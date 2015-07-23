#!/usr/bin/env python

# Copyright 2015 SAS Institute Inc.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
# 
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License. 

############################################################
#
#   hadooptracer.py
#
#   A script to help enumerate client side jars for common
#   hadoop services.
#   * hadoop
#   * hbase
#   * hcatalog
#   * hcatapi
#   * webhcat
#   * hive
#   * beeline
#   * mapreduce
#   * pig
#   * oozie
#
#   Example Usage:
#
#   $ ./hadooptracer.py -f /tmp/test.json
#
#   Example JSON Output:
#
#   cat /tmp/hadooptrace.json  | fgrep -A1 jarfiles
#    "jarfiles": [
#      "/opt/.../hadoop-hdfs-2.3.0-cdh5.0.1.jar",
#    --
#    "jarfiles": [
#      "/opt/.../hadoop-hdfs-2.3.0-cdh5.0.1.jar",
#    --
#    "jarfiles": [
#      "/opt/.../hadoop-hdfs-2.3.0-cdh5.0.1.jar",
#
############################################################

import ast
import copy
import json
import getpass
import glob
import logging
import os
import shlex
import shutil
import socket
import stat
import sys
import tempfile
import time
import traceback
from optparse import OptionParser
from pprint import pprint
from string import Template
import subprocess
from subprocess import PIPE
from subprocess import Popen
from multiprocessing import Process, Queue

############################################################
#   GLOBALS
############################################################

# store intermediate work files here
WORKDIR = "$WORKDIR"

# wait this long for a command to finish
TIMEOUT = "180s"

# strace these commands
SERVICES = {'hadoop': 'hadoop fs -ls /',
            'hadoop-put': {'pre': 'dd if=/dev/urandom of=%s/dd.out bs=1K count=1' % (WORKDIR),
                           'cmd': 'hadoop fs -put -f %s/dd.out /tmp/%s-dd.out' % (WORKDIR, getpass.getuser()),
                           'post': 'hadoop fs -rm -f -skipTrash /tmp/%s-dd.out' % (getpass.getuser())},
            'pig': {'class': 'PigTrace'},
            'thrift': {'class': 'ThriftTrace'},
            'hbase': {'pre': 'echo "whoami\nexit" > %s/test.hbase' % WORKDIR,
                      'cmd': 'hbase shell %s/test.hbase' % WORKDIR},
            'yarn-node': 'yarn node -list',
            'yarn-apps': 'yarn application -list',
            'mapreduce': {'class': 'MapReduceTrace'},
            'hcatalog': {'class': 'HcatalogTrace'},
            'hcatapi': {'class': 'HcatAPITrace'},
            'hivejdbc': {'class': 'HiveJdbcTrace'},
            'beeline': {'class': 'BeelineJdbcTrace'},
            'oozie': {'class': 'OozieTrace'}
           }

# temporary cache for reruns
DATACACHE = {}


# global cache of jar contents
JCCACHE = {}
JCEXCLUSIONS = []

# create logging object
LOG = logging.getLogger()
LOG.setLevel(logging.DEBUG)
ch = logging.StreamHandler(sys.stdout)
ch.setLevel(logging.DEBUG)
formatter = logging.Formatter('%(asctime)s hadooptracer [%(levelname)s] %(message)s')
ch.setFormatter(formatter)
LOG.addHandler(ch)


############################################################
#   FUTURE COMMANDS
############################################################

'''
yarn \
    org.apache.hadoop.yarn.applications.distributedshell.Client \
    -jar /opt/cloudera/.../hadoop-yarn-applications-distributedshell-2.3.0-cdh5.0.1.jar \
    -shell_command echo \
    -shell_args "foo"
'''

'''
hive -e 'set -v'
    * hive.server2.authentication=NONE
    * hive.server2.enable.doAs=true
    * hive.metastore.sasl.enabled=false
    * hive.server2.thrift.sasl.qop=auth
    * system:java.class.path=/etc/gphd/hadoop/conf:...
    * system:sun.java.command=org.apache.hadoop.util.RunJar \
        /usr/lib/gphd/hive/lib/hive-cli-0.12.0-gphd-3.0.0.0.jar \
        org.apache.hadoop.hive.cli.CliDriver -p 10000 -e set -v
    * env:SERVICE_LIST=beeline cli help hiveserver2 hiveserver hwi \
       jar lineage metastore metatool orcfiledump rcfilecat schemaTool
'''

'''
# https://cwiki.apache.org/confluence/display/Hive/HCatalog+UsingHCat
usage: hcat { -e "<query>" | -f "<filepath>" } [ -g "<group>" ] [ -p "<perms>" ] [ -D"<name>=<value>" ]
 -D <property=value>   use hadoop value for given property
 -e <exec>             hcat command given from command line
 -f <file>             hcat commands in file
 -g <group>            group for the db/table specified in CREATE statement
 -h,--help             Print help information
 -p <perms>            permissions for the db/table specified in CREATE statement
'''

'''
# finds the libthrift jar ...
./hadooptracer.py --nothreads --command="pig -useHCatalog -d DEBUG -f /root/test.pig"
[root@quickstart hadoop-tracer]# cat ~/test.pig
A = LOAD 'TracerHcatTest' USING org.apache.hcatalog.pig.HCatLoader();
dump A;
'''

############################################################
#   TRACER CLASS
############################################################

class Tracer(object):
    """ A stub class for other tracer classes """

    def __init__(self):
        # internal data
        self.options = None
        if not os.path.isdir(WORKDIR):
            os.makedirs(WORKDIR)

        # return data
        self.rc_strace = None
        self.rc_verbose = None
        self.rawdata = None
        self.jre = None
        self.classpath = None  #!verbose
        self.classpaths = None #verbose
        self.fqns = None
        self.javacmd = None
        self.javaenv = None
        self.jars = None
        self.jarfiles = None
        self.sitexmls = None
        self.version = None
        self.metadata = {}

    def strace(self, cmd, svckey=None, piping=True, shorten=False):
        LOG.info("%s - strace'ing" % svckey)

        rc, so, se = strace(cmd, options=self.options)
        rawdata = str(so) + str(se)
        #rc, so, se = strace(cmd)

        LOG.info("%s - parsing java info" % svckey)
        JRE, CLASSPATH, JAVACMD, JAVAENV = parse_strace_output(rawdata)
        if not JRE or not CLASSPATH or not JAVACMD or not JAVAENV:
            LOG.error("%s - no jre/classpath/javacmd/javaenv" % svckey)
            return False

        if shorten:
            #import epdb; epdb.st()
            cpr = javaClasspathReducer(CLASSPATH)
            if cpr.shortenedclasspath:
                CLASSPATH = cpr.shortenedclasspath
                CLASSPATH = ':'.join(CLASSPATH)

        # Remove excluded packages (DL+derby workaround)
        if self.options.excludepackage:
            CLASSPATH = exclude_packages(CLASSPATH, self.options.excludepackage)

        LOG.info("%s - parsing sitexmls" % svckey)
        sitexmls = parse_strace_open_file(rawdata, "site.xml", list=True)
        LOG.info("%s - rerunning with -verbose:class" % svckey)
        vrc, rawdataj = javaverbose(self.options, CLASSPATH, JAVACMD, 
                                    JAVAENV, piping=piping, svckey=svckey)
        LOG.info("%s - parsing -verbose:class output" % svckey)
        ECLASSPATH = parseverboseoutput(rawdataj)
        EJARS = classpathstojars(ECLASSPATH)
        EJARS = jrejarfilter(JRE, EJARS)

        self.javacmd = JAVACMD
        self.javaenv = JAVACMD
        self.classpaths = ECLASSPATH
        self.jars = EJARS
        self.sitexmls = sitexmls
        self.rc_strace = rc
        self.rc_verbose = vrc


############################################################
#   HIVE HELPER CODE
############################################################

HIVEJDBCCODE = '''
import java.sql.SQLException;
import java.sql.Connection;
import java.sql.ResultSet;
import java.sql.Statement;
import java.sql.DriverManager;

public class HiveJdbcClient {
  private static String driverName = "org.apache.hive.jdbc.HiveDriver";

  /**
   * @param args
   * @throws SQLException
   */
  public static void main(String[] args) throws SQLException {
    try {
      Class.forName(driverName);
    } catch (ClassNotFoundException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
      System.exit(1);
    }
    Connection con = DriverManager.getConnection(%s);
    Statement stmt = con.createStatement();
    stmt.execute("show databases");
    stmt.execute("show tables");
    stmt.execute("create table hadooptracertest(a INT)");
    stmt.execute("drop table hadooptracertest");
  }
}
'''

HIVEBUILDSCRIPT = '''#!/bin/bash

#cd /tmp

# write out the java code
cat > HiveJdbcClient.java << EOF
%s
EOF

# export the CLASSPATH
export CLASSPATH="%s:."

# cleanup old binaries
#rm -f /tmp/HiveJdbcClient.class
rm -f HiveJdbcClient.class

# compile the java code
%s HiveJdbcClient.java

# find the timeout command
TIMEOUT=$(command -v timeout)

# run the code with -verbose:class
BASECMD="%s -cp $CLASSPATH -verbose:class HiveJdbcClient"
rm -rf hivejava.debug
if [ $TIMEOUT != '' ]; then
    echo "Running with with timeout"
    $TIMEOUT -s SIGKILL 360s $BASECMD 2>&1 | tee -a hivejava.debug
else
    echo "Running hive without timeout"
    $BASECMD 2>&1 | tee -a hivejava.debug
fi

# check the exit code
RC=$?
if [ $RC != 0 ]; then
    exit $RC
fi

# check for any errors
egrep ^Error hivejava.debug
RC=$?
if [ $RC == 0 ]; then
    exit 1
fi
'''


class HiveJdbcTrace(object):
    """ Find Hive jdbc client jars """

    def __init__(self):
        # internal data
        self.options = None
        if not os.path.isdir(WORKDIR):
            os.makedirs(WORKDIR)
        self.workdir = tempfile.mkdtemp(prefix='hivejdbc.', dir=WORKDIR)
        self.jdkbasedir = locatejdkbasedir()
        self.jdk = None
        if self.jdkbasedir:
            self.jdk = os.path.join(self.jdkbasedir, 'javac')
        self.hivesitexml = None
        self.krb_principal = None
        self.hiveinfo = {}
        self.jdbcparams = None

        # return data
        self.rc_strace = None
        self.rc_verbose = None
        self.rawdata = None
        self.jre = None
        self.classpath = None  #!verbose
        self.classpaths = None #verbose
        self.fqns = None
        self.javacmd = None
        self.javaenv = None
        self.jars = []
        self.jarfiles = None
        self.sitexmls = None
        self.version = None
        self.metadata = {}

    def Run(self):

        LOG.info("hivejdbc - get hive info")
        self.hiveinfo = collecthiveinfo()

        # Run this first to get the sitexmls
        LOG.info("hivejdbc - trace hive cli")
        self.hive_show_databases()

        LOG.info("hivejdbc - set jdbc principal")
        self.set_principal()

        LOG.info("hivejdbc - set jdbc params")
        self.set_jdbc_params()

        LOG.info("hivejdbc - trace jdbc")
        self.hive_jdbc_trace()

        LOG.info("hivejdbc - finished")

    def hive_show_databases(self):
        hivecmd = getcmdpath('hive')
        cmd = "%s -e 'show databases'" % hivecmd
        (rc, so, se) = strace(cmd, options=self.options)
        LOG.info("hivejdbc - strace default hive finished: %s" % rc)
        self.rc_strace = rc
        if self.rc_strace == 137:
            LOG.error('hivejdbc - (show databases) strace timed out [>%s]' % TIMEOUT)

        # Do not shorten the classpath (DL+derby workaround)
        self.jre, self.classpath, self.javacmd, self.javaenv = \
            parse_strace_output(str(so) + str(so), shorten=False)

        if not self.jre or not self.javacmd:
            LOG.error('hivejdbc - (show databases) found no jre or javacmd in strace')
            return False

        self.sitexmls = parse_strace_open_file(str(so) + str(so), "site.xml", list=True)
        LOG.info("hivejdbc - site.xmls %s" % (self.sitexmls))
        if self.sitexmls:
            for sx in self.sitexmls:
                if sx.endswith('hive-site.xml'):
                    self.hivesitexml = sx

        # If we don't have a hive-site.xml, write out debug logs
        if not self.hivesitexml or self.options.noclean:
            fn = os.path.join(self.workdir, "hive.strace")
            f = open(fn, "wb")
            f.write('rc:%s\n' % self.rc_strace)
            f.write(str(so) + str(so))
            f.close()

        if self.javacmd:
            LOG.info("hivejdbc (show databases) - [-verbose:class]")
            vrc, rawdataj = javaverbose(self.options, self.classpath, self.javacmd, self.javaenv, svckey='hivejdbc')
            #self.rc_verbose = vrc

            LOG.info("hivejdbc (show databases) - parse jars paths")
            self.classpaths = parseverboseoutput(rawdataj)
            """
            # reduce the cp size
            cpr = javaClasspathReducer(self.classpaths):
            if cpr.shortenedclasspath:
                self.classpaths = cpr.shortenedclasspath
            """
            self.jars = classpathstojars(self.classpaths)
            self.jars = jrejarfilter(self.jre, self.jars)

    def set_jdbc_params(self):
        # https://cwiki.apache.org/confluence/display/Hive/Setting+Up+HiveServer2
        # Options are NONE, NOSASL, KERBEROS, LDAP, PAM and CUSTOM.
        # http://www-01.ibm.com/support/knowledgecenter/SSPT3X_3.0.0/com.ibm.swg.im.infosphere.biginsights.admin.doc/doc/bi_admin_enable_hive_authorization.html
        # "jdbc:hive2://%s:10000/default%s", "hive", ""
        # hive.server2.authentication=NONE
        # hive.server2.authentication=CUSTOM
        # hive.server2.custom.authentication.class=org.apache.hive.service.auth.WebConsoleAuthenticationProviderIm
        # hive.server2.ssl=false
        # hive.server2.enable.doAs=true
        # hive.server2.enable.impersonation=true
        # hive.server2.thrift.port=10000
        # hive.server2.thrift.bind.host=greysky1.unx.sas.com

        authtype = False
        thriftport = 10000
        thrifthost = 'localhost'
        usessl = False

        if 'hive.server2.authentication' in self.hiveinfo:
            atype = self.hiveinfo['hive.server2.authentication']
            if atype == 'NONE':
                authtype = 'NONE'
            elif atype == 'CUSTOM':
                if 'hive.server2.custom.authentication.class' in self.hiveinfo:
                    # settings for ibm biginsight
                    tt = self.hiveinfo['hive.server2.custom.authentication.class']
                    if tt == 'org.apache.hive.service.auth.WebConsoleAuthenticationProviderIm':
                        authtype = 'PLAIN'
                    elif tt == 'org.apache.hive.service.auth.WebConsoleAuthenticationProviderImpl':
                        authtype = 'PLAIN'

        if 'hive.server2.ssl' in self.hiveinfo:
            usessl = self.hiveinfo['hive.server2.ssl']

        if usessl:
            LOG.info("hivejdbc - usessl: %s" % usessl)

        if 'hive.metastore.uris' in self.hiveinfo:
            # fgrep dmmlax15 hivesettings.txt
            #   hive.metastore.uris=thrift://dmmlax15.unx.sas.com:9083
            pass

        if 'hive.server2.thrift.port' in self.hiveinfo:
            thriftport = int(self.hiveinfo['hive.server2.thrift.port'])

        if 'hive.server2.thrift.bind.host' in self.hiveinfo:
            thrifthost = self.hiveinfo['hive.server2.thrift.bind.host']

        """
        self.hiveinfo['hive.server2.enable.doAs']
        self.hiveinfo['hive.server2.enable.impersonation']
        """

        # "jdbc:hive2://%s:10000/default%s", "hive", ""
        LOG.info('hivejdbc - authtype: %s' % authtype)
        if self.options.hivehost:
            params = ['jdbc:hive2://%s:%s/default' % (self.options.hivehost, thriftport)]
        else:
            params = ['jdbc:hive2://%s:%s/default' % (thrifthost, thriftport)]
        if authtype == 'KERBEROS':
            params[0] += ';' + self.krb_principal
        elif authtype == 'PLAIN':
            params.append('%s' % self.options.hiveusername)
            #FIXME ... password
            if not self.options.hivepassword:
                LOG.error("hivejdbc - hive password was set to null but is required")
            params.append("%s" % self.options.hivepassword)
        elif authtype == 'NONE':
            # mapr sandbox
            params.append('%s' % self.options.hiveusername)
            params.append('%s' % self.options.hivepassword)

        LOG.info("hivejdbc - jdbc parameters: %s" % params)
        self.metadata['connection_params'] = params
        self.jdbcparams = ''
        plen = len(params) - 1
        for idx, val in enumerate(params):
            self.jdbcparams += '"%s"' % val
            if idx != plen:
                self.jdbcparams += ", "

    def set_principal(self):
        if self.options:
            if hasattr(self.options, "hivehost"):
                if not self.options.hivehost and not 'hive.server2.thrift.bind.host' in self.hiveinfo:
                    LOG.warning("hivejdbc - Hive hostname was set to Null")

        if not self.hivesitexml:
            LOG.info('hivejdbc - no hive sitexml found')
        elif self.hivesitexml:
            # get the authenication details
            f = open(self.hivesitexml)
            rawxml = f.read()
            f.close()

            # auth enabled?
            self.auth_enabled = xmlnametovalue(rawxml, "hive.security.authorization.enabled")
            self.krb_principal = xmlnametovalue(rawxml, "hive.server2.authentication.kerberos.principal")

            # use kerberos or not?
            if not self.auth_enabled:
                LOG.info('hivejdbc - auth not enabled')
            elif self.auth_enabled:
                LOG.info('hivejdbc - auth enabled')
                if ast.literal_eval(self.auth_enabled.title()):
                    # fix the url
                    if self.krb_principal:
                        if "_HOST" in self.krb_principal:
                            hname = socket.getfqdn()
                            self.krb_principal = self.krb_principal.replace('_HOST', hname)
                            self.hostname = hname
                            LOG.info("hive - principal set to %s" % (self.krb_principal))

        #   hive/_HOST@UNX.SAS.COM
        #   jdbc:hive2://$FQDN:10000/default;principal=hive/$FQDN@UNX.SAS.COM

        # Fix the principal string
        if not self.krb_principal:
            self.krb_principal = ''
        else:
            if not self.krb_principal.startswith(';principal='):
                self.krb_principal = ';principal=' + self.krb_principal

        LOG.info('hivejdbc - krb principal: %s' % self.krb_principal)


    def hive_jdbc_trace(self):

        '''
        # must have a libdir
        if not self.hivelibdir:
            LOG.error("hivejdbc - no libdir found, skipping jdbc test" % makefile)
            return False
        '''

        # Remove excluded packages (DL+derby workaround)
        if self.options.excludepackage:
            self.jdbc_classpath = exclude_packages(self.classpath, self.options.excludepackage)
        else:
            self.jdbc_classpath = self.classpath

        #import epdb; epdb.st()

        # compile the buildscript FIXME?
        """
        if self.options:
            if hasattr(self.options, 'hivehost'):
                hostname = self.options.hivehost
                HIVEJDBCPGM = HIVEJDBCCODE % (hostname, self.krb_principal)
            else:
                HIVEJDBCPGM = HIVEJDBCCODE % ("localhost", self.krb_principal)
        """

        HIVEJDBCPGM = HIVEJDBCCODE % (self.jdbcparams)
        bs = HIVEBUILDSCRIPT % (HIVEJDBCPGM, self.jdbc_classpath, self.jdk, self.jre)

        # write out buildscript
        makefile = os.path.join(self.workdir, "makefile")
        LOG.info("hivejdbc - makefile: %s" % makefile)
        fh = open(makefile, "wb")
        fh.write(bs)
        fh.close()

        # run buildscript
        args = "/bin/bash %s" % makefile
        p = Popen(args, cwd=self.workdir, stdout=PIPE, stderr=PIPE, shell=True)
        so, se = p.communicate()
        rc = p.returncode
        self.rc_verbose = rc
        self.rc_strace = rc

        if rc != 0:
            LOG.error("hivejdbc - %s" % so + se)

        # The classloader output is in the hivejava.debug file
        debugfile = os.path.join(self.workdir, "hivejava.debug")
        if not os.path.isfile(debugfile):
            return None, None
        else:
            LOG.info("hivejdbc - %s" % debugfile)

        LOG.info('hivejdbc - parsing verbose log')

        f = open(debugfile, "rb")
        data = f.read()
        f.close()

        classpaths = parseverboseoutput(data)
        if classpaths:
            for cp in classpaths:
                if cp not in self.classpaths:
                    self.classpaths.append(cp)

            self.jars = classpathstojars(classpaths)
            '''
            if jarfiles:
                jarfiles = jrejarfilter(self.jre, jarfiles)
                for jf in jarfiles:
                    if jf not in self.jars:
                        self.jars.append(jf)
            '''
        #import epdb; epdb.st()
        LOG.info('hivejdbc - total jars: %s' % len(self.jars))

    def guesshivelibdir(self):
        hivelibdir = None

        if self.hiveinfo:
            if 'system' in self.hiveinfo:
                if 'java.class.path' in self.hiveinfo['system']:
                    # FIXME
                    pass

        if not hivelibdir:
            if self.jars:
                for jf in self.jars:
                    jar = os.path.basename(jf)
                    if 'hive' in jar:
                        hivelibdir = os.path.dirname(jf)

        self.hivelibdir = hivelibdir


############################################################
#   MAPREDUCE HELPER CODE
############################################################

WC = """/**
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

/* http://svn.apache.org/viewvc/hadoop/common/trunk/hadoop-mapreduce-project/hadoop-mapreduce-examples/
        src/main/java/org/apache/hadoop/examples/WordCount.java?view=co */

package org.apache.hadoop.examples;

import java.io.IOException;
import java.util.StringTokenizer;

import org.apache.hadoop.conf.Configuration;
import org.apache.hadoop.fs.Path;
import org.apache.hadoop.io.IntWritable;
import org.apache.hadoop.io.Text;
import org.apache.hadoop.mapreduce.Job;
import org.apache.hadoop.mapreduce.Mapper;
import org.apache.hadoop.mapreduce.Reducer;
import org.apache.hadoop.mapreduce.lib.input.FileInputFormat;
import org.apache.hadoop.mapreduce.lib.output.FileOutputFormat;
import org.apache.hadoop.util.GenericOptionsParser;

public class WordCount {

  public static class TokenizerMapper
       extends Mapper<Object, Text, Text, IntWritable>{

    private final static IntWritable one = new IntWritable(1);
    private Text word = new Text();

    public void map(Object key, Text value, Context context
                    ) throws IOException, InterruptedException {
      StringTokenizer itr = new StringTokenizer(value.toString());
      while (itr.hasMoreTokens()) {
        word.set(itr.nextToken());
        context.write(word, one);
      }
    }
  }

  public static class IntSumReducer
       extends Reducer<Text,IntWritable,Text,IntWritable> {
    private IntWritable result = new IntWritable();

    public void reduce(Text key, Iterable<IntWritable> values,
                       Context context
                       ) throws IOException, InterruptedException {
      int sum = 0;
      for (IntWritable val : values) {
        sum += val.get();
      }
      result.set(sum);
      context.write(key, result);
    }
  }

  public static void main(String[] args) throws Exception {
    Configuration conf = new Configuration();
    String[] otherArgs = new GenericOptionsParser(conf, args).getRemainingArgs();
    if (otherArgs.length < 2) {
      System.err.println("Usage: wordcount <in> [<in>...] <out>");
      System.exit(2);
    }
    Job job = new Job(conf, "word count");
    job.setJarByClass(WordCount.class);
    job.setMapperClass(TokenizerMapper.class);
    job.setCombinerClass(IntSumReducer.class);
    job.setReducerClass(IntSumReducer.class);
    job.setOutputKeyClass(Text.class);
    job.setOutputValueClass(IntWritable.class);
    for (int i = 0; i < otherArgs.length - 1; ++i) {
      FileInputFormat.addInputPath(job, new Path(otherArgs[i]));
    }
    FileOutputFormat.setOutputPath(job,
      new Path(otherArgs[otherArgs.length - 1]));
    System.exit(job.waitForCompletion(true) ? 0 : 1);
  }
}
"""


class MapReduceTrace(object):
    """ Create and strace a mapreduce job. """

    def __init__(self):
        # internal data
        self.options = None
        if not os.path.isdir(WORKDIR):
            os.makedirs(WORKDIR)
        self.workdir = tempfile.mkdtemp(prefix='mapreduce.', dir=WORKDIR)
        self.jdkbasedir = None
        self.jdk = None
        self.jarcmd = None
        self.jarfile = None

        # return data
        self.rc_strace = None
        self.rc_verbose = None
        self.rawdata = None
        self.jre = None
        self.classpath = None
        self.classpaths = None
        self.javacmd = None
        self.javaenv = None
        self.jars = None
        self.sitexmls = None
        self.version = None
        self.fqns = None
        self.jarfiles = None
        self.metadata = {}

    def Run(self):
        self.wc_code = WC

        # setup necessary java tools
        self.jdkbasedir = locatejdkbasedir()
        if self.jdkbasedir:
            self.jdk = os.path.join(self.jdkbasedir, 'javac')
            self.jarcmd = os.path.join(self.jdkbasedir, 'jar')

        # build the code
        self.compilejava()

        # run the code with strace
        self.runmapreduce()

        # cleanup
        #pass
        LOG.info("mapreduce - finished")

    def compilejava(self):
        # compile the wordcount code

        # write out the java file
        jfile = os.path.join(self.workdir, "WordCount.java")
        f = open(jfile, "wb")
        f.write(self.wc_code)
        f.close()

        # compile the code
        classdir = os.path.join(self.workdir, "wordcount_classes")
        os.makedirs(classdir)
        makefile = os.path.join(self.workdir, 'build.sh')
        f = open(makefile, "wb")
        f.write("#!/bin/bash\n")
        f.write("CLASSPATH=$(hadoop classpath)\n")
        f.write("%s -cp $CLASSPATH -d wordcount_classes WordCount.java\n" % self.jdk)
        f.write("%s -cvf wordcount.jar -C wordcount_classes/ .\n" % self.jarcmd)
        f.close()

        LOG.info("mapreduce - compile wordcount.jar")
        cmd = "bash -x build.sh"
        (rc, so, se) = run_command(cmd, cwd=self.workdir, checkrc=False)

    def runmapreduce(self):
        # run the jar with hadoop|hdfs jar command

        # the user needs a writeable homedir
        #   Caused by: org.apache.hadoop.ipc.RemoteException
        #    (org.apache.hadoop.security.AccessControlException):
        #    Permission denied: user=root, access=WRITE,
        #       inode="/user":hdfs:supergroup:drwxr-xr-x

        # make two unique tmpdirs in hdfs
        tdir1 = tempfile.mkdtemp(prefix='%s-wordcount1' % getpass.getuser(), dir='/tmp')
        shutil.rmtree(tdir1)
        tdir2 = tempfile.mkdtemp(prefix='%s-wordcount2' % getpass.getuser(), dir='/tmp')
        shutil.rmtree(tdir2)

        tlog = open("%s/test.log" % self.workdir, "wb")

        # Assemble fake data
        f = open("%s/file0" % self.workdir, "wb")
        f.write('Hello World Bye World\n')
        f.close()
        f = open("%s/file1" % self.workdir, "wb")
        f.write('Hello Hadoop Goodbye Hadoop\n')
        f.close()

        cmd = 'hadoop fs -mkdir %s\n' % tdir1
        (rc, so, se) = run_command(cmd, cwd=self.workdir, checkrc=False)
        tlog.write('%s\n' % rc)
        cmd = 'hadoop fs -mkdir %s\n' % tdir2
        (rc, so, se) = run_command(cmd, cwd=self.workdir, checkrc=False)
        tlog.write('%s\n' % rc)

        cmd = 'hadoop fs -mkdir %s/input\n' % tdir1
        (rc, so, se) = run_command(cmd, cwd=self.workdir, checkrc=False)
        tlog.write('%s\n' % rc)
        cmd = 'hadoop fs -mkdir %s/input\n' % tdir2
        (rc, so, se) = run_command(cmd, cwd=self.workdir, checkrc=False)
        tlog.write('%s\n' % rc)

        # Put fake data into hdfs
        cmd = 'hadoop fs -put %s/file* %s/input\n' % (self.workdir, tdir1)
        (rc, so, se) = run_command(cmd, cwd=self.workdir, checkrc=False)
        tlog.write('%s\n' % rc)
        cmd = 'hadoop fs -put %s/file* %s/input\n' % (self.workdir, tdir2)
        (rc, so, se) = run_command(cmd, cwd=self.workdir, checkrc=False)
        tlog.write('%s\n' % rc)
        tlog.close()

        # wait for src2 to get created [prone to race conditions]
        rc = 1
        retries = 5
        while rc != 0 and retries > 0:
            LOG.info("mapreduce - waiting for %s/input creation" % tdir2)
            time.sleep(2)
            cmd = 'hadoop fs -ls %s/input\n' % tdir2
            (rc, so, se) = run_command(cmd, cwd=self.workdir, checkrc=False)
            retries -= 1

        # run it once to get the full java command
        LOG.info("mapreduce - hadoop jar wordcount.jar")
        cmd = 'hadoop jar %s/wordcount.jar org.apache.hadoop.examples.WordCount' % self.workdir
        cmd += ' %s/input %s/output' % (tdir1, tdir1)
        (rc2, so2, se2) = strace(cmd, options=self.options)
        self.rc_strace = rc2

        JRE, CLASSPATH, JAVACMD, JAVAENV = parse_strace_output(str(so2) + str(so2))
        self.classpath = CLASSPATH
        self.sitexmls = parse_strace_open_file(str(so2) + str(so2), "site.xml", list=True)

        if JAVACMD:

            # alter the destination to avoid delays / race conditions
            s1 = "%s/input" % tdir1
            s2 = "%s/input" % tdir2
            d1 = "%s/output" % tdir1
            d2 = "%s/output" % tdir2
            for idx, val in enumerate(JAVACMD):
                if val == s1:
                    JAVACMD[idx] = s2
                if val == d1:
                    JAVACMD[idx] = d2

            # run it again to get the verbose classloader output
            LOG.info("mapreduce [-verbose:class]")
            vrc, rawdataj = javaverbose(self.options, CLASSPATH, JAVACMD, JAVAENV, svckey='mapreduce')
            self.rc_verbose = vrc

            if vrc != 0:
                lines = [x.strip().replace('\t', '') for x in rawdataj.split('\n') if x]
                #import pdb; pdb.set_trace()
                for line in lines:
                    if line.startswith('Exception'):
                        LOG.error("mapreduce - %s" % line)

            LOG.info("mapreduce - parse jars paths")
            self.classpaths = parseverboseoutput(rawdataj)
            jars = classpathstojars(self.classpaths)
            self.jars = jrejarfilter(JRE, jars)

        # Cleanup
        cmd = "hadoop fs -rm -f -R -skipTrash %s" % tdir1
        run_command(cmd, cwd=self.workdir, checkrc=False)
        cmd = "hadoop fs -rm -f -R -skipTrash %s" % tdir2
        run_command(cmd, cwd=self.workdir, checkrc=False)


############################################################
#   HCATALOG HELPER CODE
############################################################

'''
HDP 2.1
hive-hcatalog-core-0.13.0.2.1.5.0-695.jar
hive-webhcat-java-client-0.13.0.2.1.5.0-695.jar
jdo-api-3.0.1.jar
jersey-client-1.9.jar
libthrift-0.9.0.jar

For CDH 5.1:
hive-hcatalog-core-0.12.0-cdh5.1.2.jar
hive-webhcat-java-client-0.12.0-cdh5.1.2.jar
jdo-api-3.0.1.jar
libthrift-0.9.0.cloudera.2.jar
parquet-hadoop-bundle.jar
'''
# https://github.com/apache/hcatalog/blob/trunk/src/test/e2e/hcatalog/tests/hcat.conf
HC = """
drop table if exists TracerHcatTest;
create table TracerHcatTest (name string,id int) row format delimited fields terminated by ':' stored as textfile;
describe TracerHcatTest;
drop table TracerHcatTest;
"""


class HcatalogTrace(object):
    """ Create and strace an hcatalog job. """

    # http://hortonworks.com/kb/working-with-files-in-hcatalog-tables/

    def __init__(self):
        # internal data
        self.options = None
        if not os.path.isdir(WORKDIR):
            os.makedirs(WORKDIR)
        self.workdir = tempfile.mkdtemp(prefix='hcatalog.', dir=WORKDIR)

        # return data
        self.rc_strace = None
        self.rc_verbose = None
        self.rawdata = None
        self.jre = None
        self.classpath = None   # !verbose
        self.classpaths = None  # verbose
        self.javacmd = None
        self.javaenv = None
        self.jars = []
        self.sitexmls = None
        self.version = None
        self.fqns = None
        self.jarfiles = None
        self.metadata = {}

    def Run(self):
        self.TraceHcatCLI()
        LOG.info("hcatalog - total jars: %s" % len(self.jars))
        LOG.info("hcatalog - finished")

    def TraceHcatCLI(self):
        # org.apache.hive.hcatalog.cli.HCatCli

        self.hc_code = HC

        # write test ddl code to a file
        fdest = os.path.join(self.workdir, "test.hcatalog")
        f = open(fdest, "wb")
        f.write(self.hc_code)
        f.close()

        cmd = "hcat -f %s" % fdest
        (rc, so, se) = strace(cmd, options=self.options)

        if rc != 0:
            data = str(so) + str(se)
            data = data.split('\n')
            for line in [x for x in data if x]:
                if "error" in line.lower() \
                    or "failed:" in line.lower() \
                    or "exception" in line.lower() \
                    or "refused" in line.lower():

                    if not "loaded " in line.lower():
                        LOG.error("thrift - %s" % line.strip())

        self.rc_strace = rc
        self.jre, self.classpath, self.javacmd, self.javaenv = \
                                parse_strace_output(str(so) + str(so))

        self.sitexmls = parse_strace_open_file(str(so) + str(so), "site.xml", list=True)

        if self.javacmd:

            # Remove excluded packages (DL+derby workaround)
            if self.options.excludepackage:
                self.classpath = exclude_packages(self.classpath, 
                                            self.options.excludepackage)
            else:
                self.classpath = self.classpath

            LOG.info("hcatalog [-verbose:class]")
            vrc, rawdataj = javaverbose(self.options, self.classpath, self.javacmd, self.javaenv, svckey='hcatalog')
            self.rc_verbose = vrc

            LOG.info("hcatalog - parse jars paths")
            self.classpaths = parseverboseoutput(rawdataj)
            self.jars = classpathstojars(self.classpaths)
            self.jars = jrejarfilter(self.jre, self.jars)



############################################################
#   HCAT API HELPER CODE
############################################################

HCAPI = """/*
* HCAT API script
*/
package org.hts.hcat;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import org.apache.hadoop.conf.Configuration;
import org.apache.hadoop.hive.conf.HiveConf;
import org.apache.hadoop.hive.metastore.HiveMetaStore;
import org.apache.hadoop.hive.metastore.api.PartitionEventType;
//import org.apache.hadoop.hive.ql.WindowsPathUtil;
import org.apache.hadoop.hive.ql.io.HiveIgnoreKeyTextOutputFormat;
import org.apache.hadoop.hive.ql.io.RCFileInputFormat;
import org.apache.hadoop.hive.ql.io.RCFileOutputFormat;
import org.apache.hadoop.hive.ql.io.orc.OrcInputFormat;
import org.apache.hadoop.hive.ql.io.orc.OrcOutputFormat;
import org.apache.hadoop.hive.ql.io.orc.OrcSerde;
import org.apache.hadoop.hive.ql.metadata.Table;
import org.apache.hadoop.hive.serde.serdeConstants;
import org.apache.hadoop.hive.serde2.columnar.LazyBinaryColumnarSerDe;
import org.apache.hadoop.mapred.TextInputFormat;
import org.apache.hive.hcatalog.cli.SemanticAnalysis.HCatSemanticAnalyzer;
import org.apache.hive.hcatalog.common.HCatConstants;
import org.apache.hive.hcatalog.common.HCatException;
import org.apache.hive.hcatalog.data.schema.HCatFieldSchema;
import org.apache.hive.hcatalog.data.schema.HCatFieldSchema.Type;
//import org.apache.hive.hcatalog.NoExitSecurityManager;

//import org.junit.AfterClass;
//import org.junit.BeforeClass;
//import org.junit.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

//import static org.junit.Assert.assertNotNull;
//import static org.junit.Assert.fail;
//import static org.junit.Assert.assertEquals;
//import static org.junit.Assert.assertFalse;
//import static org.junit.Assert.assertTrue;
//import static org.junit.Assert.assertArrayEquals;

import org.apache.hadoop.util.Shell;

//import org.apache.hcatalog.api.HCatClient;
import org.apache.hive.hcatalog.api.HCatClient;
import org.apache.hive.hcatalog.api.HCatTable;
import org.apache.hive.hcatalog.api.HCatCreateTableDesc;

public class TestHCatClient {
  private static final Logger LOG = LoggerFactory.getLogger(TestHCatClient.class);
  //private static final String msPort = "20101";
  private static final String msPort = "9083";
  private static HiveConf hcatConf;
  private static boolean isReplicationTargetHCatRunning = false;
  //private static final String replicationTargetHCatPort = "20102";
  private static final String replicationTargetHCatPort = "9083";
  private static HiveConf replicationTargetHCatConf;
  private static SecurityManager securityManager;

  public static void main(String[] args) throws Exception {

    // Create the config
    hcatConf = new HiveConf(TestHCatClient.class);
    //hcatConf.setVar(HiveConf.ConfVars.METASTOREURIS, "thrift://localhost:"
    //  + msPort);
    hcatConf.setVar(HiveConf.ConfVars.METASTOREURIS, "$thrift_uri");
    hcatConf.setIntVar(HiveConf.ConfVars.METASTORETHRIFTCONNECTIONRETRIES, 3);
    hcatConf.setIntVar(HiveConf.ConfVars.METASTORETHRIFTFAILURERETRIES, 3);
    System.out.println(hcatConf);

    Boolean connected = false;
    HCatClient client = null;

    try {
        // Create the client object
        client = HCatClient.create(new Configuration(hcatConf));
        connected = true;
    } catch (Exception e) {
        //System.out.println(e.getMessage());
        e.printStackTrace();
        connected = false;
    }

    if ( connected ) {
        // Show databases
        List<String> dbNames = client.listDatabaseNamesByPattern("*");
        System.out.println(dbNames);

        // Show tables
        String dbName = "default";
        List<String> tbNames = client.listTableNamesByPattern(dbName, "*");
        System.out.println(tbNames);

        // Kill client and forcefully exit
        client.close();

        System.exit(0);

    } else {
        System.exit(1);
    }

  }

}
"""


class HcatAPITrace(object):
    """ Create and strace an hcatalog API job. """

    # Primary target:
    #   * hive-webhcat-java-client-0.13.0.2.1.5.0-695.jar

    def __init__(self):
        # internal data
        self.options = None
        if not os.path.isdir(WORKDIR):
            os.makedirs(WORKDIR)
        self.workdir = tempfile.mkdtemp(prefix='hcatapi.', dir=WORKDIR)

        # return data
        self.rc_strace = None
        self.rc_verbose = None
        self.rawdata = None
        self.jre = None
        self.classpath = None   # !verbose
        self.classpaths = None  # verbose
        self.javacmd = None
        self.javaenv = None
        self.jars = None
        self.sitexmls = None
        self.version = None
        self.fqns = None
        self.jarfiles = None
        self.metadata = {}

    def Run(self):

        # get hive config data
        #self.hiveclass = HiveJdbcTrace()
        #self.hiveclass.collecthiveinfo()
        LOG.info("hcatapi - fetching hive config")
        self.hiveinfo = collecthiveinfo()
        #LOG.info("hcatapi - hiveinfo: %s" % self.hiveinfo)

        # What is the thrift URI ?
        self.thrifturi = None
        if self.hiveinfo:
            if "hive.metastore.uris" in self.hiveinfo:
                if type(self.hiveinfo['hive.metastore.uris']) == list:
                    self.thrifturi = self.hiveinfo['hive.metastore.uris'][0]
                else:
                    self.thrifturi = self.hiveinfo['hive.metastore.uris']

            else:
                # EMR
                if checkthriftport():
                    self.thrifturi = "thrift://localhost:9083"
                else:
                    LOG.error("hcatapi - no hive.metastore.uris in hiveinfo")
                    LOG.error("hcatapi - hiveinfo: %s" % self.hiveinfo)

        if self.thrifturi:
            LOG.info("hcatapi - thrifturi: %s" % self.thrifturi)
        else:
            LOG.error("hcatapi - thrifturi: %s" % self.thrifturi)

        # What is the jre/jdk path?
        # system:sun.boot.class.path=/usr/java/jdk1.7.0_67-cloudera/...:...:
        self.jre, self.jdk, self.jar = self.locateJREandJDK()
        #import pdb; pdb.set_trace()

        # What is the hive classpath?
        # system:java.class.path=/etc/hadoop/conf
        self.hclasspath = None
        if self.hiveinfo:
            if 'system' in self.hiveinfo:
                if 'java.class.path' in self.hiveinfo['system']:
                    self.hclasspath = self.hiveinfo['system']['java.class.path']

        # Assemble a classpath with hive and hcat jars
        self.ajars = self.findAllJars()
        self.aclasspath = self.jarsToClassPath(self.ajars)
        #import pdb; pdb.set_trace()

        if self.hclasspath:
            self.aclasspath = self.hclasspath + ":" + self.aclasspath
        self.classpath = self.aclasspath

        # clean up the classpath        
        cpr = javaClasspathReducer(self.classpath)
        if cpr.shortenedclasspath:
            # get rid of /usr/share/java/* to work around log4j method errors
            cpr.shortenedclasspath = [x for x in cpr.shortenedclasspath if not x.startswith("/usr/share/java") ]

            self.aclasspath = ':'.join(cpr.shortenedclasspath)
            self.classpath = ':'.join(cpr.shortenedclasspath)

        # Remove excluded packages (DL+derby workaround)
        if self.options.excludepackage:
            self.aclasspath = exclude_packages(self.classpath, self.options.excludepackage)
            self.classpath = self.aclasspath

        #self.TraceHcatCLI()
        #import pdb; pdb.set_trace()
        #print "Running"
        if self.jre and self.jdk and self.jar:
            if self.compileJar():
                LOG.info("hcatapi - compiling test jar successful")
                if self.runJar():
                    LOG.info("hcatapi - running test jar successful")
                    self.rc_strace = 0
                    self.rc_verbose = 0

                else:
                    LOG.error("hcatapi - running test jar failed")
                    return False
            else:
                LOG.error("hcatapi - compiling test jar failed")
                return False
        else:
            LOG.error("hcatapi - jre/jdk/jar not found")
            return False

        # Read test log and parse out the jars
        self.parsejars()
        #import pdb; pdb.set_trace()
        LOG.info("hcatapi - total jars: %s" % len(self.jars))
        LOG.info("hcatapi - finished")

    ############################
    #   Helpers
    ############################

    def locateJREandJDK(self):

        jre = None
        jdk = None
        jar = None

        # If hive doesn't know, then use the process table
        if self.hiveinfo:
            if not 'system' in self.hiveinfo:
                x = [locatejdkbasedir()]
            elif not 'sun.boot.class.path' in self.hiveinfo['system']:
                x = [locatejdkbasedir()]
            else:
                if 'system' in self.hiveinfo:
                    if 'sun.boot.class.path' in self.hiveinfo['system']:
                        x = self.hiveinfo['system']['sun.boot.class.path'].split(':')
        else:
            x = [locatejdkbasedir()]

        x = sorted(set([os.path.dirname(y) for y in x if y]))

        for y in x:
            yparts = y.split("/")
            ylen = len(yparts)
            indexes = range(0, ylen + 1)
            indexes = reversed(indexes)
            for i in indexes:
                thisdir = "/".join(yparts[:i])

                if not jre:
                    cmd = "find %s -type f -name 'java'" % thisdir
                    (rc, so, se) = run_command(cmd)
                    if rc == 0:
                        jre = so.strip().split('\n')[0]
                    #import pdb; pdb.set_trace()

                if not jdk:
                    cmd = "find %s -type f -name 'javac'" % thisdir
                    (rc, so, se) = run_command(cmd)
                    if rc == 0:
                        jdk = so.strip()

                if not jar:
                    cmd = "find %s -type f -name 'jar'" % thisdir
                    (rc, so, se) = run_command(cmd)
                    if rc == 0:
                        jar = so.strip()

                if jre and jdk and jar:
                    break

        LOG.info("hcatapi - jres: %s" % jre)
        LOG.info("hcatapi - jdks: %s" % jdk)
        LOG.info("hcatapi - jars: %s" % jar)
        return jre, jdk, jar


    def findAllJars(self):

        """ Current revisions of hcatalog are a subproject of hive and the relevant
            jars can be found in $hivehome/hcatalog """

        # The hive-webhcat-java-client jar is an elusive file. It's not usually
        # part of any known service or command line's classpath, so we have to
        # do a lot of "fuzzing" on existing classpaths to find it.

        # Start by interrogating the hive classpath for directories/jars with
        # hive or hbase in the path or filename. Have to be careful here because
        # including too many jars in the final classpath will result in a java
        # exception for "too many open files". That is why this filters just the
        # hive|hcatalog jars and HOPES to get enough to compile the java client code
        cmd = 'hive -e "set -v" | fgrep -i classpath | cut -d\= -f2'
        (rc, so, se) = run_command(cmd, checkrc=False, cwd=None)
        paths = [x.strip() for x in so.split(':') if x.strip()]
        paths = [x for x in paths if 'hive' in x or 'hbase' in x]
        cpr = javaClasspathReducer(':'.join(paths))
        #import epdb; epdb.st()

        globdirs = [os.path.dirname(x) for x in cpr.shortenedclasspath if x.endswith('*')]
        singlejars = [x for x in cpr.shortenedclasspath if x.endswith('.jar')]

        # now replace "lib" with "hcatalog" and check if it exists to find the hcatalog home(s)
        hcatalogdirs = []
        for dirpath in globdirs:

            thisparent = os.path.dirname(dirpath)
            thisgrandparent = os.path.dirname(thisparent)

            # workaround for newer cdh 5.3.2.x layouts
            if thisparent not in hcatalogdirs and thisparent:
                hcatalogdirs.append(thisparent)

            candidates = []
            candidates.append(os.path.join(thisparent, "hcatalog"))
            candidates.append(os.path.join(thisparent, "hive-hcatalog"))
            candidates.append(os.path.join(thisgrandparent, "hcatalog"))
            candidates.append(os.path.join(thisgrandparent, "hive-hcatalog"))

            for cp in candidates:
                if os.path.isdir(cp) and not cp in hcatalogdirs:
                    hcatalogdirs.append(cp)

        # now find all the jars in the hcatalog paths
        jars = []
        parcel_dirs = []
        for dirpath in hcatalogdirs:
            cmd = "find %s -type f -name \"*.jar\"" % dirpath
            (rc, so, se) = run_command(cmd, checkrc=False, cwd=None)
            for line in so.split('\n'):
                line = line.strip()
                if line.endswith('.jar'):
                    if line not in jars:
                        jars.append(line)

            # Find the CDH parcel dir
            if 'cloudera/parcels' in dirpath:
                parts = dirpath.split('/')
                pindex = None
                for idx,x in enumerate(parts):
                    if x == 'parcels':
                        pindex = idx
                        break
                if pindex:
                    parcel_path = "/".join(parts[0:(pindex+2)])
                    if parcel_path not in parcel_dirs:
                        parcel_dirs.append(parcel_path)
                        LOG.info("hcatapi - CDH parcel path: %s" % parcel_path)

        # CDH doesn't like to put ALL of their jars in the right place,
        # so we have to locate a path to the parcels for this install
        # and then look for a "jars" directory where hopefully the
        # webhcat client can be found
        if parcel_dirs:
            # Use the longest path
            longest = None
            for x in parcel_dirs:
                if not longest:
                    longest = x
                elif len(x) > len(longest):
                    longest = x
            # Add jars in this path to the CP
            jpath = os.path.join(longest, "jars")
            if os.path.isdir(jpath):
                parcel_jars = glob.glob("%s/*.jar" % jpath)
                for pjar in parcel_jars:
                    if pjar not in jars:
                        jars.append(pjar)
                #import pdb; pdb.set_trace()

        # Check the process table for the hcatapi service and locate it's client jar dir
        # This only works if the webhcat services is running on the current machine.
        ps_client_cps = self.findWebHcatProcessCP()
        if ps_client_cps:
            psjars = []
            for pscp in ps_client_cps:
                tjars = glob.glob(pscp)
                for tjar in tjars:
                    jars.append(os.path.abspath(tjar))

        # recombine with the single jars
        jars += singlejars
        jars = sorted(set(jars))

        #import epdb; epdb.st()
        #import pdb; pdb.set_trace()
        return jars


    def findWebHcatProcessCP(self):
        # [etlguest@bdedev147 jamtan]$ ps aux | fgrep -i webhcat
        # hive     27473  0.0  1.1 836980 185256 ?       Sl   Jun24  15:15 /usr/../java -Xmx1000m
        # -Dwebhcat.log.dir=/var/log/hcatalog -Dlog4j.configuration=file:/.../webhcat-log4j.properties
        # -Dhadoop.log.dir=/opt/cloudera/parcels/CDH-5.2.0-1.cdh5.2.0.p0.36/lib/hadoop/logs
        # -Dhadoop.log.file=hadoop.log
        # -Dhadoop.home.dir=/opt/cloudera/parcels/CDH-5.2.0-1.cdh5.2.0.p0.36/lib/hadoop
        # -Dhadoop.id.str=
        # -Dhadoop.root.logger=INFO,console
        # -Djava.library.path=/opt/cloudera/parcels/CDH-5.2.0-1.cdh5.2.0.p0.36/lib/hadoop/lib/native
        # -Dhadoop.policy.file=hadoop-policy.xml
        # -Djava.net.preferIPv4Stack=true
        # -Djava.net.preferIPv4Stack=true
        # -Djava.net.preferIPv4Stack=true
        # -Xms268435456 -Xmx268435456 -XX:+UseParNewGC -XX:+UseConcMarkSweepGC
        # -XX:-CMSConcurrentMTEnabled -XX:CMSInitiatingOccupancyFraction=70
        # -XX:+CMSParallelRemarkEnabled -XX:OnOutOfMemoryError=/usr/lib64/cmf/service/common/killparent.sh
        # -Dhadoop.security.logger=INFO,NullAppender org.apache.hadoop.util.RunJar
        # /opt/.../hive-webhcat-0.13.1-cdh5.2.0.jar org.apache.hive.hcatalog.templeton.Main

        jarpaths = []
        cmd = "ps aux | fgrep -i webhcat"
        (rc, so, se) = run_command(cmd, checkrc=False, cwd=None)
        if rc != 0:
            return None

        lines = [x for x in so.split('\n') if 'java' in x]
        for line in lines:
            parts = line.split()
            thisjar = None
            user = parts[0]
            pid = parts[1]

            ''' FIXME ... needs more validation/testing
            # Can we look at the environ file (probably has the CP set)?
            fdata = None
            try:
                f = open("/proc/%s/environ" % pid, "rb")
                fdata = f.read()
                f.close()
            except Exception as e:
                pass

            if fdata:
                import epdb; epdb.st()
            '''

            runjar_idx = None
            for idx,x in enumerate(parts):
                if x == 'org.apache.hadoop.util.RunJar':
                    runjar_idx = idx
                    break
            if runjar_idx:
                thisjar = parts[runjar_idx + 1]
                LOG.info("hcatapi - service jar located at %s" % thisjar)
                if 'webhcat' in thisjar:
                    jarpaths.append(os.path.abspath(thisjar))
                else:
                    break


        # seek higher dirs for the client jars
        clientdirs = []
        for jarpath in jarpaths:

            thisdir = os.path.dirname(jarpath)
            thisparent = os.path.dirname(thisdir)
            thisgrandparent = os.path.dirname(thisparent)

            candidates = []
            candidates.append(os.path.join(thisparent, "java-client"))
            candidates.append(os.path.join(thisgrandparent, "java-client"))

            for cp in candidates:
                if os.path.isdir(cp):
                    LOG.info("hcatapi - client dir at %s" % cp)
                    clientdirs.append(os.path.join(cp, '*'))

        #import pdb; pdb.set_trace()
        return clientdirs


    def findAllJars_deprecated(self):
        cmd =  "find / -path /tmp -prune -path /mnt -prune -path *filecache* -prune"
        cmd += " -path /mapr -prune"
        cmd += " -path /net -prune"
        cmd += " -o -type f -name '*.jar'"
        (rc, so, se) = run_command(cmd, checkrc=False, cwd=None)
        jars = [x for x in so.split('\n') if x.endswith(".jar")]

        # get rid of netbeans jars ...
        #   warning: Supported source version 'RELEASE_6' from
        #   annotation processor 'org.netbeans.modules.openide.util.ServiceProviderProcessor'
        #   less than -source '1.7'
        jars = [x for x in jars if 'visualvm' not in x]

        # exclude other builds of hts-hcat.jar
        jars = [x for x in jars if not x.endswith('hts-hcat.jar')]

        # exclude work and tmp dirs
        jars = [x for x in jars if WORKDIR not in x]

        # Java can't handle a LARGE classpath, so attempt to cut it down ...
        #   Caused by: java.io.FileNotFoundException:
        #   /usr/java/jdk1.7.0_67-cloudera/jre/lib/resources.jar
        #   (Too many open files)
        #jars = [x for x in jars if 'hcat' in x or 'hive' in x]
        jars = [x for x in jars if 'webhcat' in x or "hcat" in x]

        # FIXME ... cdh4 and cdh5 jars are in use

        # ignore cached yarn jars
        jars = [x for x in jars if 'cache/yarn' not in x]
        # ignore cached jars
        jars = [x for x in jars if 'filecache' not in x]
        # ignore mounted jars
        jars = [x for x in jars if not x.startswith('/mnt')]

        # ignore /root and /home, execpt for /home/hadoop on EMR
        jars1 = [x for x in jars if not x.startswith('/root') and not x.startswith('/home')]
        jars2 = [x for x in jars if x.startswith('/home/hadoop')]
        jars = jars1 + jars2

        return jars

    def jarsToClassPath(self, jars):
        dirnames = []
        for x in jars:
            dirname = os.path.dirname(x)
            if dirname not in dirnames:
                dirnames.append(dirname)
        dirnames = "/*:".join(dirnames) + '/*'
        return dirnames

    def compileJar(self):
        LOG.info("hcatapi - compiling test jar")

        s = Template(HCAPI)
        tdata = s.substitute(thrift_uri=self.thrifturi)

        fname = os.path.join(self.workdir, "TestHCatClient.java")
        f = open(fname, "wb")
        f.write(tdata)
        f.close()

        bscript = "#!/bin/bash\n"
        bscript += "CP=\"%s\"\n" % self.aclasspath
        bscript += "rm -rf htest_classes\n"
        bscript += "mkdir htest_classes\n"
        bscript += "%s -Xlint:deprecation -d htest_classes -g" % self.jdk
        bscript += " -cp \"$CP\" TestHCatClient.java\n"
        bscript += "RC=$?\n"
        bscript += "if [ $RC != 0 ];then\n"
        bscript += "    exit 1\n"
        bscript += "fi\n"
        bscript += "RC=$?\n"
        bscript += "rm -f hts-hcat.jar\n"
        bscript += "%s -cvf hts-hcat.jar -C htest_classes .\n" % self.jar
        bscript += "if [ $RC != 0 ];then\n"
        bscript += "    exit 1\n"
        bscript += "fi\n"

        bname = os.path.join(self.workdir, "make.sh")
        f = open(bname, "wb")
        f.write(bscript)
        f.close()
        st = os.stat(bname)
        os.chmod(bname, st.st_mode | stat.S_IEXEC)

        cmd = "./make.sh"
        (rc, so, se) = run_command(cmd, cwd=self.workdir)

        jarf = os.path.join(self.workdir, "hts-hcat.jar")

        if os.path.isfile(jarf) and rc == 0:
            return True
        else:
            data = str(so) + str(se)
            data = data.split('\n')
            for line in data:
                if 'error: ' in line:
                    LOG.error("hcatapi [compilejar] - %s" % line)

            return False

    def runJar(self):
        LOG.info("hcatapi - running test jar")

        testscr = "#!/bin/bash\n"
        testscr += "CP=\"$(pwd)/*:%s\"\n" % self.aclasspath
        testscr += "%s -verbose:class -cp $CP org.hts.hcat.TestHCatClient" % self.jre
        testscr += " > test.log 2>&1\n"
        testscr += "RC=$?\n"
        testscr += "if [ $RC != 0 ];then\n"
        testscr += "    exit 1\n"
        testscr += "fi\n"

        fname = os.path.join(self.workdir, "test.sh")
        f = open(fname, "wb")
        f.write(testscr)
        f.close()
        st = os.stat(fname)
        os.chmod(fname, st.st_mode | stat.S_IEXEC)

        cmd = "./test.sh"
        (rc, so, se) = run_command(cmd, cwd=self.workdir)

        tlog = os.path.join(self.workdir, "test.log")

        if os.path.isfile(tlog):
            f = open(tlog, "rb")
            data = f.readlines()
            f.close()

        # Show what failed
        if rc != 0:
            if rc == 9:
                LOG.error("hcatapi - exceeded timeout")
            for line in [x for x in data if x]:
                if "error" in line.lower() or "exception" in line.lower() or "refused" in line.lower():
                    if not "loaded " in line.lower():
                        LOG.error("hcatapi - %s" % line.strip())

        #import pdb; pdb.set_trace()
        if (os.path.isfile(tlog) and rc == 0) or (not self.options.stoponerror):
            return True
        else:
            return False

    def parsejars(self):
        fname = os.path.join(self.workdir, "test.log")
        f = open(fname, "rb")
        data = f.read()
        f.close()
        self.classpaths = parseverboseoutput(data)
        self.jars = classpathstojars(self.classpaths)
        self.jars = [x for x in self.jars if 'hts-hcat.jar' not in x]
        self.jars = jrejarfilter(self.jre, self.jars)


############################################################
#   THRIFT HELPER CODE
############################################################

HC1 = """drop table if exists TracerHcatPIGTest;
create table TracerHcatPIGTest (name string,id int) row format delimited fields terminated by ':' stored as textfile;
"""

# old hcat fqn ...
PC = """A = LOAD 'TracerHcatPIGTest' USING org.apache.hcatalog.pig.HCatLoader();
dump A;
"""

# new hcat fqn
PC2 = """A = LOAD 'TracerHcatPIGTest' USING org.apache.hive.hcatalog.pig.HCatLoader();
dump A;
"""

HC2 = """drop table TracerHcatPIGTest;
"""


class ThriftTrace(object):
    """ Create and strace a PIG job to find the libthrift jar"""

    # Primary target(s):
    #   * libthrift-0.9.0-cdh5-2.jar
    #       - import org.apache.thrift.TException;

    def __init__(self):
        # internal data
        self.options = None
        if not os.path.isdir(WORKDIR):
            os.makedirs(WORKDIR)
        self.workdir = tempfile.mkdtemp(prefix='thrift.', dir=WORKDIR)

        # return data
        self.rc_strace = None
        self.rc_verbose = None
        self.rawdata = None
        self.jre = None
        self.classpath = None   # !verbose
        self.classpaths = None  # verbose
        self.javacmd = None
        self.javaenv = None
        self.jars = None
        self.sitexmls = None
        self.version = None
        self.fqns = None
        self.jarfiles = None
        self.metadata = {}

    def Run(self):

        # Is the hcatalog fqn prefixed by hive?
        self.get_hcat_prefix()
    
        # PREPARE
        fdest = os.path.join(self.workdir, "hcat1")
        f = open(fdest, "wb")
        f.write(HC1)
        f.close()
        cmd = "hcat -f %s" % fdest
        (rc, so, se) = run_command(cmd)

        if rc != 0:
            data = str(so) + str(se)
            data = data.split('\n')
            for line in [x for x in data if x]:
                if "error" in line.lower() \
                    or "failed:" in line.lower() \
                    or "exception" in line.lower() \
                    or "refused" in line.lower():

                    if not "loaded " in line.lower():
                        LOG.error("thrift - %s" % line.strip())

        # TRACE
        fdest = os.path.join(self.workdir, "test.pig")
        f = open(fdest, "wb")
        if self.hcat_prefix == "org/apache/hive/hcatalog":
            f.write(PC2)
        else:
            # use older pre hive merge path
            f.write(PC)
        f.close()
        cmd = "pig -useHCatalog -d DEBUG -f %s" % fdest
        self.strace(cmd)

        # CLEANUP
        fdest = os.path.join(self.workdir, "hcat2")
        f = open(fdest, "wb")
        f.write(HC2)
        f.close()
        cmd = "hcat -f %s" % fdest
        (rc, so, se) = run_command(cmd)

    def strace(self, cmd):
        LOG.info("thrift - strace'ing")
        rc, so, se = strace(cmd, options=self.options)
        rawdata = str(so) + str(se)

        if rc != 0:
            lines = rawdata.split('\n')
            for line in [x for x in lines if x]:
                if 'ERROR' in line \
                    or 'Caused by' in line:

                    if not "loaded " in line.lower():
                        LOG.error("thrift - %s" % line.strip())


        LOG.info("thrift - parsing java info")
        JRE, CLASSPATH, JAVACMD, JAVAENV = parse_strace_output(rawdata)
        if not JRE or not CLASSPATH or not JAVACMD or not JAVAENV:
            LOG.error("thrift - no jre/classpath/javacmd/javaenv")
            return False

        LOG.info("thrift - parsing sitexmls")
        sitexmls = parse_strace_open_file(rawdata, "site.xml", list=True)
        vrc, rawdataj = javaverbose(options, CLASSPATH, JAVACMD, JAVAENV, svckey='thrift')
        ECLASSPATH = parseverboseoutput(rawdataj)
        EJARS = classpathstojars(ECLASSPATH)
        EJARS = jrejarfilter(JRE, EJARS)

        if vrc != 0:
            data = rawdataj.split('\n')
            for line in [x for x in data if x]:
                if "error" in line.lower() \
                    or "failed:" in line.lower() \
                    or "exception" in line.lower() \
                    or "refused" in line.lower():

                    if not "loaded " in line.lower():
                        LOG.error("thrift - %s" % line.strip())

        self.classpaths = ECLASSPATH
        self.jars = EJARS
        self.sitexmls = sitexmls
        self.rc_strace = rc
        self.rc_verbose = vrc


    def get_hcat_prefix(self):
        """ Use the jars in the hcat classpath to determine
            the fqn of hcatalog on this system """

        LOG.info('thrift - finding hcat fqn prefix')

        # use the hcat command to get the classpath
        cmd = 'hcat -classpath'
        (rc, so, se) = run_command(cmd)
        jcpr = javaClasspathReducer(so)
        jars = [x for x in jcpr.jars if 'hcat' in x.lower()]

        LOG.info('thrift - inspecting hcat jar contents')
        allpaths = []

        # find all the fqns in each jar
        unzip = getcmdpath('unzip')
        jarcmd = getcmdpath('jar')
        if jarcmd:                
            LOG.info('thrift - using jar cmd to inspect jar files')
            for jar in jars:
                cmd = "jar -tf %s" % jar
                (rc, so, se) = run_command(cmd)
                paths = [x for x in so.split('\n') if x and x.endswith('.class')]
                for y in paths:
                    if y not in allpaths:
                        allpaths.append(y)
        elif unzip:
            LOG.info('thrift - using unzip cmd to inspect jar files')
            for jar in jars:
                cmd = "unzip -l %s" % jar
                (rc, so, se) = run_command(cmd)
                rawlines = [x for x in so.split('\n') if x.endswith('.class')]
                for rl in rawlines:
                    rl_parts = rl.split(None)
                    if rl_parts[-1] and rl_parts[-1] not in allpaths:
                        allpaths.append(rl_parts[-1])

        # Is it org/apache/hive/hcatalog or org/apache/hcatalog ?
        prefix = None
        for x in allpaths:
            if x.startswith('org/apache/hive/hcatalog'):
                prefix = 'org/apache/hive/hcatalog'
            elif x.startswith('org/apache/hcatalog'):
                prefix = 'org/apache/hcatalog'
        LOG.info('thrift - hcatalog prefix is %s' % prefix)    
        self.hcat_prefix = prefix
        #import pdb; pdb.set_trace()



############################################################
#   OOZIE 
############################################################

class OozieTrace(Tracer):

    """ Find the oozie metadata from the process table """

    def Run(self):
        self.findOozieProcess()
        self.findOozieSiteXML()

        # [ignored - oozie.rc.cmd_strace oozie.rc.java_verbose ]
        self.rc_strace = 0
        self.rc_verbose = 0
        

    def findOozieProcess(self):
        cmd = "ps aux"
        (rc, so, se) = run_command(cmd)
        lines = [x for x in so.split('\n') if x]
        lines = [x for x in lines if 'oozie.config.dir' in x]
        if len(lines) >= 1:
            parts = shlex.split(lines[0])
            for part in parts:
                if part.startswith('-D') and '=' in part:
                    part = part.replace('-D', '', 1)
                    plist = part.split('=', 1)                
                    k = plist[0]
                    v = plist[1]
                    self.metadata[k] = v


    def findOozieSiteXML(self):
        configfile = None
        configdir = None
        configfilepath = None
        if 'oozie.config.file' in self.metadata:
            configfile = self.metadata['oozie.config.file']
        if 'oozie.config.dir' in self.metadata:
            configdir = self.metadata['oozie.config.dir']

        if configdir and configfile:
            configfilepath = os.path.join(configdir, configfile)
            if os.path.isfile(configfilepath):
                self.sitexmls=[configfilepath]

############################################################
#   BEELINE
############################################################

class BeelineJdbcTrace(Tracer):

    """ Get the jars for beeline """

    def Run(self):
        self.beeline = getcmdpath('beeline')
        self.hiveinfo = collecthiveinfo()
        self.hivetracer = HiveJdbcTrace()
        self.hivetracer.options = self.options
        self.hivetracer.hiveinfo = self.hiveinfo
        self.hivetracer.set_principal()
        self.hivetracer.set_jdbc_params()
        LOG.info("beeline - jdbcparams: %s" % self.hivetracer.jdbcparams)
        self.metadata['connection_params'] = self.hivetracer.metadata['connection_params']

        # Use the hive hostname the user specified
        if self.options.hivehost:
            if self.options.hivehost not in self.metadata['connection_params'][0]:
                # split the host and port ...
                slash_parts = self.metadata['connection_params'][0].split('/')
                hostport = slash_parts[2].split(':')
                hostport[0] = self.options.hivehost

                # rejoin and save
                slash_parts[2] = ':'.join(hostport)
                self.metadata['connection_params'][0] = '/'.join(slash_parts)

        #if not checkcmdinpath("beeline"):
        if not self.beeline:

            # Is beeline next to hive? (mapr)
            hive = getcmdpath('hive')
            if hive:
                if os.path.islink(hive):
                    hive = os.path.realpath(hive)

                bindir = os.path.dirname(hive)
                beelinecmd = os.path.join(bindir, "beeline")
                if os.path.isfile(beelinecmd):
                    LOG.info('beeline found at %s' % beelinecmd)
                    self.beeline = beelinecmd

            if not self.beeline:
                LOG.error("beeline is not in this users path")
                return False

        # write out the sql cmds
        sqlfile = os.path.join(WORKDIR, "beeline-query.sql")
        f = open(sqlfile, "wb")
        f.write("show tables;\n")
        f.close()

        #beeline -u jdbc:hive2://localhost:10000/default -e "show tables"
        if len(self.metadata['connection_params']) == 1:
            cmd = "%s --color=false -u %s -f %s" % (self.beeline,
                                                    self.metadata['connection_params'][0],
                                                    sqlfile)
        else:
            # Beeline doesn't like empty password strings ...
            if not self.metadata['connection_params'][2]:
                self.metadata['connection_params'][2] = "NULL"

            cmd = "%s --color=false -u %s -n %s -p \"%s\" -f %s" % (self.beeline,
                                                    self.metadata['connection_params'][0],
                                                    self.metadata['connection_params'][1],
                                                    self.metadata['connection_params'][2],
                                                    sqlfile)

        LOG.info("beeline - cmd to strace: %s" % cmd)
        self.strace(cmd, svckey="beeline", piping=False, shorten=False)

        LOG.info("beeline - finished")


############################################################
#   PIG
############################################################

class PigTrace(Tracer):

    """ Get the jars for pig """

    DATA = """customer_number,account_number,status
1,1,foo
2,2,foo
3,3,bar
4,4,foo
5,5,baz
6,6,foo
"""

    CODE = """rmf /tmp/pigtracer/output
A = LOAD '/tmp/pigtracer/indata' USING PigStorage(',')
    AS (customer_number,account_number,status);
B = FILTER A BY status == 'foo';
store B into '/tmp/pigtracer/output' USING PigStorage(',');
"""

    def Run(self):
        self.workdir = tempfile.mkdtemp(prefix='pig.', dir=WORKDIR)
        self.pig = getcmdpath('pig')

        """
        # OLD        
        cmd = "%s -x mapreduce -e 'pwd'" % (self.pig)
        LOG.info("pig - cmd to strace: %s" % cmd)
        self.strace(cmd, svckey="pig", piping=True)
        """

        # Create the dataset csv in the workdir
        fname = os.path.join(self.workdir, "test.csv")
        f = open(fname, "wb")
        f.write(self.DATA)
        f.close()

        # Clean and create other hdfs tmpdir
        cmd = "hadoop fs -rm -r -f -skipTrash /tmp/pigtracer"
        (rc, so, se) = run_command(cmd)
        cmd = "hadoop fs -mkdir -p /tmp/pigtracer/indata"
        (rc, so, se) = run_command(cmd)
        #cmd = "hadoop fs -mkdir -p /tmp/pigtracer/output"
        #(rc, so, se) = run_command(cmd)

        # Copy the dataset to hdfs
        cmd = "hadoop fs -copyFromLocal %s /tmp/pigtracer/indata/test.csv" % (fname)
        (rc, so, se) = run_command(cmd)

        # Write out the example code
        fname = os.path.join(self.workdir, "test.pig")
        f = open(fname, "wb")
        f.write(self.CODE)
        f.close()

        # Strace the pig command
        cmd = "%s -x mapreduce -f %s" % (self.pig, fname)
        self.strace(cmd, svckey='pig', piping=True)
 

############################################################
#   CLASSPATH REDUCER
############################################################

class javaClasspathReducer(object):

    def __init__(self, classpath):

        self.classpath = classpath

        # make a unique list of cp's
        self.classpaths = self.classpathunique(self.classpath)

        # flatten the list to real files
        self.classdirs, self.flatfiles = self.flattenclasspathtofiles(self.classpaths)

        # reduce the flattened list
        self.reducedpaths = self.filepathreducer(self.flatfiles)

        # retain the dirs and combine with paths
        self.shortenedclasspath = sorted(set(self.classdirs + self.reducedpaths))
        #import epdb; epdb.st()

        # Make a flat list of jars for optional use
        self.jarfiles = self.flattenjars()


    def __exit__(self, *args, **kwargs):
        pass

    def __enter__(self):
        return self


    def flattenclasspathtofiles(self, classpaths):

            """Flatten a java classpath to a list of
               absolute file paths based on java's
               classloader behavior """

            dirs = []
            files = []

            # break out multi-line filenames: S1152653
            for idx,x in enumerate(classpaths):
                if '\n' in x:
                    parts = x.split('\n')
                    classpaths += parts
                    del classpaths[idx]

            for cp in classpaths:

                # directory
                if cp.endswith('/'):
                    #print "directory ..."
                    # get jars AND classes
                    jarfiles = glob.glob("%s/*.jar" % cp)
                    classfiles = glob.glob("%s/*.class" % cp)
                    testfiles = jarfiles + classfiles
                    for tf in testfiles:
                        if os.path.isfile(tf):
                            tf = os.path.abspath(tf)
                            files.append(tf)

                # single jar
                elif cp.endswith('.jar'):
                    #print "jar ..."
                    cp = os.path.abspath(cp)
                    files.append(cp)

                # glob
                elif cp.endswith('/*'):

                    cp = "%s.jar" % cp
                    #print "glob ...", cp

                    dirglob = glob.glob(cp)
                    for dirfile in dirglob:
                        if os.path.isfile(dirfile):
                            # make sure it's an absolute path
                            dirfile = os.path.abspath(dirfile)
                            files.append(dirfile)
                            #import epdb; epdb.st()    
                        elif os.path.islink(dirfile):
                            sl = os.path.abspath(dirfile)
                            if os.path.isfile(sl):
                                files.append(sl)

                        else:
                            #print "What is this?",dirfile
                            #import epdb; epdb.st()
                            pass

                # other (must discover)
                else:
                    if os.path.isdir(cp):
                        #print "pydir ..."

                        # keep track of this dir for confs
                        if os.path.abspath(cp) not in dirs:
                            dirs.append(os.path.abspath(cp))

                        jarfiles = glob.glob("%s/*.jar" % cp)
                        classfiles = glob.glob("%s/*.class" % cp)
                        testfiles = jarfiles + classfiles
                        for tf in testfiles:
                            if os.path.isfile(tf):
                                tf = os.path.abspath(tf)
                                files.append(tf)

                    elif os.path.isfile(cp):
                        #print "pyfile ..."
                        #import epdb; epdb.st()
                        tf = os.path.abspath(cp)
                        files.append(tf)
                    else:
                        #print "unknown ..."
                        #import epdb; epdb.st()
                        pass

            return dirs, files
        

    def classpathunique(self, classpath):

        """Split a string of classpaths and unique the list"""

        classpaths = classpath.split(':')
        classpaths = [x for x in classpaths if x]
        classpaths = sorted(set(classpaths))
        return classpaths


    def filepathreducer(self, files):

        """Given a list of files, shorten the list
           for each path to a glob if all files in the
           basedir are defined """

        # save copy
        ofiles = files

        # max # of unused jars before not globbing a dir
        threshold = 2 

        # make a list of dirpaths
        dirs = []
        for f in files:
            dir = os.path.dirname(f)
            #print dir 
            #if dir.endswith('.'):
            #    import epdb; epdb.st()
            if dir not in dirs:
                dirs.append(dir)
        
        # get the list of files in the dir
        for dir in dirs:
            alldefined = True
            dirjars = glob.glob("%s/*.jar" % dir)
            dirjars += glob.glob("%s/*.class" % dir)
            undefined = []
            for dj in dirjars:
                if dj not in files:
                    #print "UNDEFINED:",dj
                    undefined.append(dj)
                    #import epdb; epdb.st()
                    #alldefined = False

            if len(undefined) > threshold:
                #print undefined
                #print "### %s could not be consolidated" % dir 
                pass
            else:
                #print "### %s can be consolidated" % dir 
                for idx,x in enumerate(files):
                    if dir  == os.path.dirname(x):
                        files[idx] = "%s/*" % dir 

        files = sorted(set(files))
        #import epdb; epdb.st()
        #import epdb; epdb.st()
        return files


    def flattenjars(self):

        """ Make a flat list of absolute jars from the shortened CP """

        self.jars = []
        #print self.shortenedclasspath
        for cp in self.shortenedclasspath:
            if cp.endswith('.jar'):
                if cp not in self.jars:
                    self.jars.append(cp)                
                continue
            if cp.endswith('/*'):
                gjars = glob.glob(cp + '.jar')
                for gjar in gjars:
                    if gjar not in self.jars:
                        self.jars.append(gjar)
        #import pdb; pdb.set_trace()            


############################################################
#   FUNCTIONS
############################################################

def list_jar_contents(jarfile):
    global JCCACHE 

    if jarfile in JCCACHE:
        return JCCACHE[jarfile]

    jarcontent = []
    ecmd = None
    candidates = ['unzip', 'zip', 'jar']
    for can in candidates:
        if checkcmdinpath(can):
            ecmd = can
            break
    if ecmd == "unzip":
        cmd = "unzip -l %s" % jarfile
        (rc, so, se) = run_command(cmd, checkrc=False)
        lines = [x for x in so.split('\n') if x]
        for x in lines:
            parts = x.split()
            if not len(parts) == 4:
                continue
            jarcontent.append(parts[-1])

    elif ecmd == "jar":
        #[root@jt-cdh5-0 ~]# jar -tf /tmp/jars/derby-10.11.1.1.jar | head
        #META-INF/MANIFEST.MF
        #org/apache/derby/agg/Aggregator.class

        cmd = "jar -tf %s" % jarfile
        (rc, so, se) = run_command(cmd, checkrc=False)
        jarcontent = [x for x in so.split('\n') if x]


    # save to cache            
    JCCACHE[jarfile] = jarcontent

    return jarcontent

def exclude_packages(classpath, excludepackages, shorten=False):
    # take a classpath, break it down to jars, inspect jars,
    # exclude any jars that have blacklisted packages

    # FIXME -- make sure the ordering is not altered
    # FIXME -- make sure the directories are saved
    
    jarmap = {}
    global JCEXCLUSIONS

    if not classpath or not excludepackages:
        return classpath

    jcpr = javaClasspathReducer(classpath)

    # figure out if any jars have exclusions in them
    for jar in jcpr.jars:
        if jar in JCEXCLUSIONS:
            continue
        jarmap[jar] = {}
        flagged = False
        files = list_jar_contents(jar)
        jarmap[jar]['files'] = files
        for file in files:
            for exp in excludepackages:
                if file.startswith(exp):
                    flagged = True
        jarmap[jar]['flagged'] = flagged
        #if flagged and os.path.basename(jar) != 'hive-jdbc.jar':
        if flagged:
            LOG.info("exclusion -- %s" % jar)
            JCEXCLUSIONS.append(jar)
            #import epdb; epdb.st()

    # make a new classpath without the exclusions
    if shorten:
        newcp = [x for x in jcpr.jars if x not in JCEXCLUSIONS]
        jcpr2 = javaClasspathReducer(':'.join(newcp))
        newclasspath = jcpr2.shortenedclasspath
    else:
        # preserve the original classpath ordering
        newcp = []
        for path in classpath.split(':'):
            # do away with the /../ style paths
            path = os.path.abspath(path)
            if path.endswith('.jar') and path not in JCEXCLUSIONS:
                newcp.append(path)
            elif os.path.isdir(path):
                newcp.append(path)
            elif path.endswith('/*'):
                # Need to get the list of jars and remove exclusions
                jars = glob.glob(path)
                jars2 = [x for x in jars if x not in JCEXCLUSIONS]
                if jars2 == jars:
                    newcp.append(path)
                else:
                    newcp = newcp + jars2
                #import epdb; epdb.st()
        newclasspath = newcp

    #import pdb; pdb.set_trace()
    #import epdb; epdb.st()
    return ':'.join(newclasspath)


def checkprereqs():
    if not checkcmdinpath("strace"):
        print "Please install strace (yum install strace) before using this script"
        sys.exit(1)


def locatejdkbasedir():
    # use the process table to find a valid JDK path
    jres = []
    jdks = []

    cmd = "ps aux | fgrep -i java"
    (rc, so, se) = run_command(cmd, checkrc=False)
    if rc != 0:
        return None

    # split apart the lines and find running jres
    lines = so.split('\n')
    for line in lines:
        parts = shlex.split(line)
        if len(parts) < 10:
            continue
        if not parts[10].endswith('bin/java'):
            continue
        if os.path.isfile(parts[10]) and not parts[10] in jres:
            jres.append(parts[10])

    # append a 'c' to the jre and see if it's a real file
    for jre in jres:
        basedir = os.path.dirname(jre)
        jdk = os.path.join(basedir, 'javac')
        jarcmd = os.path.join(basedir, 'jar')
        if os.path.isfile(jdk) and os.path.isfile(jarcmd):
            jdks.append(basedir)

    if len(jdks) == 0:
        return None
    elif len(jdks) == 1:
        return jdks[0]
    else:
        return jdks[0]


def hadoopclasspathcmd():

    """ Find all jars listed by the hadoop classpath command """

    LOG.info("hadoop-classpath - locating all jars")

    jars = []
    cmd = "hadoop classpath"
    rc, so, se = run_command(cmd, checkrc=False)

    if rc != 0:
        return jars

    # Split and iterate each path
    paths = so.split(':')
    for path in paths:
        files = glob.glob(path)
        for file in files:
            if file.endswith(".jar"):
                jars.append(file)

    return jars


def sitexmlcombiner(confdir, outfile="combined-site.xml"):

    # Verify the system has xml libs
    hasxml = False
    try:
        import xml.etree.ElementTree as ET
        hasxml = True
    except:
        pass

    if not hasxml:
        return False

    # Each property is stored here
    xdata = []
    ydata = []

    # clear out old copies
    outfile = os.path.join(confdir, outfile)
    merge = os.path.join(confdir, 'core-hdfs-merged.xml')

    if os.path.isfile(outfile):
        os.remove(outfile)

    # Read all site.xml files and parse them
    for file in os.listdir(confdir):
        fpath = os.path.join(confdir, file)
        if os.path.isfile(fpath) and fpath.endswith('.xml'):

                tree = ET.parse(fpath)
                root = tree.getroot()

                for child in root:
                    # create a dict for each propery
                    # and append to the overall list
                    xdict = {}
                    for x in child.getchildren():
                        xdict[x.tag] = x.text
                    xdata.append(xdict)
                    if 'core-site.xml' in fpath or 'hdfs-site.xml' in fpath:
                        ydata.append(xdict)

    # Write out properties to a combined xml file
    f = open(outfile, "wb")
    h = open(merge,   "wb")

    f.write("<configuration>\n")
    h.write("<configuration>\n")

    for x in xdata:
        f.write("\t<property>\n")
        for k in sorted(x.keys()):
            if k == "description":
                continue
            f.write("\t\t<%s>%s</%s>\n" % (k, x[k], k))
        f.write("\t</property>\n")
    f.write("</configuration>\n")

    for x in ydata:
        h.write("\t<property>\n")
        for k in sorted(x.keys()):
            if k == "description":
                continue
            h.write("\t\t<%s>%s</%s>\n" % (k, x[k], k))
        h.write("\t</property>\n")
    h.write("</configuration>\n")

    return True


def xmlnametovalue(rawxml, name):

    """ Grab the value for a given xml node by name """

    # <name>hive.enforce.sorting</name>
    # <value>true</value>

    # clean up empty lines
    tl = [x.strip() for x in rawxml.split("\n") if x.strip()]
    this_idx = None
    # find line number for matching name
    for idx, val in enumerate(tl):
        if val == '<name>' + name + "</name>":
            this_idx = idx
    # get the value
    if this_idx:
        data = tl[this_idx + 1]
        if data.startswith('<value>'):
            data = data.replace('<value>', '')
        if data.endswith('</value>'):
            data = data.replace('</value>', '')
        return data
    return None


def striplast(line, delimiter):

    """ Reverse a string, strip up to delimiter """

    backwards = line[::-1]
    parts = backwards.split(delimiter, 1)
    forwards = parts[1][::-1]
    #import pdb; pdb.set_trace()
    return forwards


def splitoutterarray(line):

    """ Get the outtermost array defined by [] in a string """

    result = None

    # strip to the first [
    parts1 = line.split('[', 1)

    # strip after the last ]
    strlist = striplast(parts1[1], ']')

    # cast to a real list
    try:
        result = ast.literal_eval('[' + strlist + ']')
    except Exception:
        # move on if not a good list
        result = None

    return result


def splitexecve(line):
    '''
    [pid 31338] 21:16:03 execve("/usr/java/latest/bin/java",
        ["/usr/java/latest/bin/java", "-Xmx256m", "-server",
            "-Dhadoop.log.dir=/home/hadoop/logs", "-Dhadoop.log.file=hadoop.log",
            "-Dhadoop.home.dir=/home/hadoop", "-Dhadoop.id.str=",
            "-Dhadoop.root.logger=INFO,console",
            "-Djava.library.path=/home/hadoop/lib/native",
            "-Dhadoop.policy.file=hadoop-policy.xml",
            "-Djava.net.preferIPv4Stack=true", "-XX:MaxPermSize=128m",
            "-Dhadoop.security.logger=INFO,NullAppender",
            "-Dsun.net.inetaddr.ttl=30", "org.apache.hadoop.util.VersionInfo" ],
        [ ENVIRONMENT ]
    '''

    if 'execve' not in line:
        return None, None

    # drop everything before the command
    parts1 = line.split('(', 1)

    # get everything after the first [
    parts2 = parts1[1].split('[', 1)

    # get everything before the first ]
    parts3 = parts2[1].split(']', 1)

    ## ARGLIST
    # try to convert the string to a list
    arglist = '[' + parts3[0] + ']'
    try:
        arglist = ast.literal_eval(arglist)
    except Exception:
        arglist = None

    ## ENVIRONMENT
    envlist = splitoutterarray(parts3[1])

    #return JAVACMD, JAVAENV
    return arglist, envlist


def getcmdpath(cmd):

    """ Get the path for a command """

    if len(shlex.split(cmd)) > 1:
        cmd = shlex.split(cmd)[0]
    args = "which %s" % cmd

    p = Popen(args, stdout=PIPE, stderr=PIPE, shell=True)
    so, se = p.communicate()

    return so.strip()


def checkcmdinpath(cmd):

    """ Verify a command is in the user's path """

    if len(shlex.split(cmd)) > 1:
        cmd = shlex.split(cmd)[0]
    args = "which %s" % cmd

    p = Popen(args, stdout=PIPE, stderr=PIPE, shell=True)
    so, se = p.communicate()

    if p.returncode == 0:
        return True
    else:
        return False


def bashtimeout(timeout=TIMEOUT):

    # SLES 11sp1 does not provide the timeout command
    # with it's coreutils package. This bash script can
    # simulate the timeout command's functionality

    # http://stackoverflow.com/a/11056286
    code = '''
    #!/bin/bash
    TIMEOUT=%s
    ( $@ ) & pid=$!
    ( sleep $TIMEOUT && kill -HUP $pid ) 2>/dev/null & watcher=$!
    wait $pid 2>/dev/null && pkill -HUP -P $watcher
    ''' % timeout.replace('s', '')

    codelines = [x.lstrip() for x in code.split('\n') if x]

    # create the file if not already created
    fname = os.path.join(WORKDIR, 'timeout')
    if not os.path.isfile(fname):
        f = open(fname, "wb")
        for line in codelines:
            f.write(line + '\n')
        f.close()

    st = os.stat(fname)
    os.chmod(fname, st.st_mode | stat.S_IEXEC)

    return fname


def run_command(cmd, checkrc=False, cwd=None, timeout=TIMEOUT):

    """ Run a shell command """

    timeoutcmd = None
    if checkcmdinpath('timeout'):
        timeoutcmd = getcmdpath('timeout')
        cmd = "%s -s SIGKILL %s %s" % (timeoutcmd, timeout, cmd)
    else:
        btimeoutcmd = bashtimeout()
        cmd = "%s %s" % (btimeoutcmd, cmd)

    p = Popen(cmd, cwd=cwd, stdout=PIPE, stderr=PIPE, shell=True)
    so, se = p.communicate()
    rc = p.returncode
    if rc != 0 and checkrc:
        LOG.error("cmd: %s\n#\trc: %s" % (cmd, rc))
        LOG.error("cmd: %s\tso|se: %s" % (cmd, str(so) + str(se)))
        #sys.exit(1)
    return rc, so, se

def run_command_live(args, cwd=None, shell=True, checkrc=False):
    p = subprocess.Popen(args,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            cwd=cwd,
            shell=shell)
    so = ""
    se = ""
    while p.poll() is None:
        lo = p.stdout.readline() # This blocks until it receives a newline.
        sys.stdout.write(lo)
        so += lo
    print p.stdout.read()
    
    return (p.returncode, so, "")    


def strace(cmd, cwd=None, follow_threads=True, timeout=TIMEOUT, usetimeout=False, options=None):

    """ Wrap input command with strace and store output """

    # Forcefully kill the command if it runs too long
    timeoutcmd = None
    if checkcmdinpath('timeout'):
        timeoutcmd = getcmdpath('timeout')
        timeoutcmd = "%s -s SIGKILL %s" % (timeoutcmd, timeout)
    else:
        timeoutcmd = bashtimeout()

    if follow_threads:
        #args = "%s strace -s 100000 -fftv -e trace=execve,open %s 2>&1" % (timeoutcmd, cmd)
        #args = "%s strace -s 100000 -fftv -e trace=execve,open %s" % (timeoutcmd, cmd)

        #args = "strace -s 100000 -fftv -e trace=execve,open %s" % (cmd)
        args = "strace -s 100000 -fftv -e trace=execve,open %s 2>&1" % (cmd)
    else:
        args = "strace -s 100000 -tv -e trace=execve,open %s 2>&1" % (cmd)

    if usetimeout:
        args = "%s %s" % (timeoutcmd, args)

    #import pdb; pdb.set_trace()

    if not options.verbose:
        p = Popen(args, cwd=cwd, stdout=PIPE, stderr=PIPE, shell=True)
        p = Popen(args, cwd=cwd, stdout=PIPE, stderr=subprocess.STDOUT, shell=True)
        so, se = p.communicate()
        rc = p.returncode
    else:
        (rc, so, se) = run_command_live(args)

    return rc, so, se


def parse_strace_output(rawtext, shorten=False):

    """ Pull java related information from raw strace output """

    CLASSPATH = None
    JRE = None
    JAVACMD = None
    JAVAENV = None

    # look for execve
    for x in (rawtext).split("\n"):
        if 'bin/java' in x \
            and 'execve(' in x \
            and x.strip().endswith('= 0') \
            and not '<unfinished ...>' in x:

            # pick apart this line into a java command and an env
            tmpcmd, tmpenv = splitexecve(x)
            if tmpcmd is not None and tmpenv is not None:
                # skip weird non-java execves
                if not tmpcmd[0].endswith('java'):
                    continue
                else:
                    JAVACMD = tmpcmd
                    JAVAENV = tmpenv

                # workaround to re-quote -e strings for hive/beeline
                if JAVACMD[-2] == "-e":
                    JAVACMD[-1] = '"' + JAVACMD[-1] + '"'
                    #print JAVACMD
                    #import pdb; pdb.set_trace()

    if type(JAVACMD) != list:
        return None, None, None, None

    CPS = [x for x in JAVAENV if x.startswith('CLASSPATH=')]
    if CPS:
        CLASSPATH = CPS[0]
        CLASSPATH = CLASSPATH.replace('CLASSPATH=', '')

    if not CLASSPATH:
        # did any positional args have a classpath?
        cp_idx = None
        for idx, val in enumerate(JAVACMD):
            if val == '-classpath' or val == '-cp':
                cp_idx = idx + 1
        if cp_idx:
            CLASSPATH = JAVACMD[cp_idx]

    # clean up the classpath
    if shorten:
        prevcp = CLASSPATH
        with javaClasspathReducer(CLASSPATH) as cpr:
            #cpr = javaClasspathReducer(CLASSPATH)
            if cpr.shortenedclasspath:
                CLASSPATH = ':'.join(cpr.shortenedclasspath)
    #import epdb; epdb.st()

    if JAVACMD[0].endswith('/java'):
        JRE = JAVACMD[0]

    #import pdb; pdb.set_trace()
    #types STR  STRING     LIST     LIST
    return JRE, CLASSPATH, JAVACMD, JAVAENV


def parse_strace_open_file(rawtext, filename, list=False):

    """ Return the last path a filename was opened from """

    #17:02:29 open("/etc/issues", O_RDONLY)  = -1 ENOENT (No such file or directory)
    #17:02:36 open("/etc/issue", O_RDONLY)   = 3
    results = []
    for x in rawtext.split("\n"):
        if not ' open(' in x:
            continue
        if "ENOENT" in x:
            continue
        parts = [y for y in shlex.split(x)]
        if len(parts) == 0:
            continue
        if parts[-2] != '=':
            continue
        open_idx = None
        for idx, part in enumerate(parts):
            if part.startswith('open'):
                open_idx = idx
                break
        if open_idx:
            # open("/etc/issue",
            data = parts[open_idx]
            data = data.replace('open(', '')
            data = data.replace('"', '')
            data = data.replace(',', '')
            if data.endswith(filename):
                results.append(data)
        else:
            continue

    # return the last found
    if results:
        if not list:
            return results[-1]
        else:
            # we want all files in some cases
            return sorted(set(results))
    else:
        return None


def safequote(javacmd):

    """ Some JRE args need to be quoted """

    '''
    (Pdb) pp JAVACMD[0:10]
    ['/usr/lib/jvm/java-1.7.0-openjdk-1.7.0.51.x86_64/bin/java',
     '-Dproc_/root/test.hbase',
     '-XX:OnOutOfMemoryError=kill -9 %p',
     '-Xmx1000m',
     '-XX:+UseConcMarkSweepGC',
     '-XX:+UseParNewGC',
     '-XX:NewRatio=16',
     '-XX:CMSInitiatingOccupancyFraction=70',
     '-XX:+UseCMSInitiatingOccupancyOnly',
     '-XX:MaxGCPauseMillis=100']
    '''

    if type(javacmd) != list:
        return javacmd

    for idx, val in enumerate(javacmd):
        # '-XX:OnOutOfMemoryError=kill -9 %p'
        if ' ' in val and val.startswith('-X') and '=' in val and not val.endswith('"'):
            newval = val.split('=', 1)
            newval[1] = '"' + newval[1] + '"'
            newval = '='.join(newval)
            javacmd[idx] = newval

    #import pdb; pdb.set_trace()
    return javacmd


def javaverbose(options, CLASSPATH, JAVACMD, JAVAENV, piping=True, svckey=None):

    """ Re-run a java cmd with -verbose:class """

    # Fix quoting around jvm options
    # http://gitlab.sas.com/prd-ctf/hadoop-integration-test/issues/16
    JAVACMD1 = JAVACMD
    JAVACMD = safequote(JAVACMD)

    # inject -verbose:class
    JAVACMD.insert(1, "-verbose:class")

    if checkcmdinpath('timeout') and piping:
        timeoutcmd = getcmdpath('timeout')
        # Set timeout on the command
        JAVACMD.insert(0, TIMEOUT)
        JAVACMD.insert(0, "-s SIGKILL")
        JAVACMD.insert(0, timeoutcmd)
    else:
        JAVACMD.insert(0, bashtimeout())

    NEWCMD = "#!/bin/bash\n"

    # if the original trace exported a CLASSPATH, do that too
    if CLASSPATH:
        NEWCMD += "export CLASSPATH=\"%s\"\n%s" % (CLASSPATH, " ".join(JAVACMD))
    else:
        NEWCMD += "%s" % " ".join(JAVACMD)

    # fix -e string quoting for hive commands
    if " -e " in NEWCMD:
        TMPCMD = NEWCMD.split(' -e ')
        if not TMPCMD[1].startswith('"') and not TMPCMD[1].endswith('"'):
            TMPCMD[1] = '"%s"' % TMPCMD[1]
            NEWCMD = ' -e '.join(TMPCMD)

    # capture the rc
    NEWCMD += "\nRC=$?\nexit $RC\n"

    # Create the wrapper script
    fh = tempfile.NamedTemporaryFile(dir=WORKDIR, prefix='%s-verbose-' % svckey,  delete=False)
    fname = fh.name
    fh.write(NEWCMD)
    fh.close()


    if not options.verbose and piping:
        cmd = "bash -x %s" % fname
        p = Popen(cmd, cwd=WORKDIR, stdout=PIPE, stderr=PIPE, shell=True)
        so, se = p.communicate()
        rc = p.returncode
    elif not options.verbose and not piping:
        cmd = "bash %s" % fname

        # Define a filename to hold stdout+stderr
        outfile = fname + ".out"

        # Redirect the script to the filename
        cmd += " 2>&1 > %s" % outfile
        p = Popen(cmd, cwd=WORKDIR, shell=True)
        so, se = p.communicate()
        rc = p.returncode

        # Read the outfile
        f = open(outfile, "rb")
        fdata = f.read()
        f.close()
        so = fdata
        se = ""

    else:
        cmd = "bash -x %s" % fname
        (rc, so, se) = run_command_live(cmd) 

    if options.noclean or options.stoponerror:
        logfile = fname + '.log'
        f = open(logfile, "wb")
        f.write(str(so) + str(se))
        f.close()

    if rc != 0:
        LOG.error("%s - %s script failed, exit code %s" % (svckey, fname, p.returncode))

        # if in verbose mode, display the error(s)
        if options.verbose:
            lines = str(so) + str(se)
            lines = lines.split('\n')
            lines = [x for x in lines if not '[load' in x.lower()]
            for line in lines:
                LOG.error("%s - %s" % (svckey, line))

        #if options.stoponerror:
        #    sys.exit(p.returncode)

    rawdata = so + se
    return (rc, rawdata)


def parseverboseoutput(rawdata):

    """ parse classpaths and jarfiles from -verbose:class output """
    classpaths = []

    for rl in rawdata.split("\n"):
        if rl.startswith("[Loaded") or rl.startswith('class load:'):
            # [Loaded java.. from /../rt.jar]
            # class load: org.ap.. from: file:../foo.jar
            parts = shlex.split(rl)
            if parts[1].lower() == 'load:':
                jfqn = parts[2]
            else:
                jfqn = parts[1]
            jarf = parts[-1].replace(']', '')

            if jarf.startswith('file:'):
                jarf = jarf.replace('file:', '')
            if not jarf.startswith('/'):
                continue

            if jarf.endswith('.jar'):
                classpaths.append((jfqn, jarf))

    # list of tuples
    #   [ (fqn, jarfile) ]
    return classpaths


def classpathstojars(classpaths):
    # convert a (cp,jar) tuple to a list of jars
    jars = []
    for fqn, jar in classpaths:
        if jar not in jars:
            jars.append(jar)
    jars = sorted(jars)
    return jars


def getversion(cmd, jarfiles):

    """ Find --version for a cli """

    version = _getversionstring(cmd)

    if version == None:
        jversions = []
        jardir = None
        jarname = None
        # resort to jarfilename chopping
        cjars = [x for x in jarfiles if cmd in x]
        for j in cjars:
            jf = os.path.basename(j)
            if jf.startswith(cmd):
                jardir = os.path.dirname(j)
                jarname = jf.replace('.jar', '')
                jv = jarname.split('-')
                ptr = None
                # find the index for the first numeric character
                for idx, val in enumerate(jv):
                    if hasattr(val, 'isdigit'):
                        if val.isdigit():
                            ptr = idx
                            break
                    if hasattr(val[0], 'isdigit'):
                        if val[0].isdigit():
                            ptr = idx
                            break
                    if type(val) == int:
                        ptr = idx
                        break
                if ptr:
                    thisv = '-'.join([str(x) for x in jv[ptr:]])
                    jversions.append(thisv)

        jversions = sorted(set(jversions))

        # check the release notes
        rver = None
        if jardir:
            if jardir.endswith('/lib'):
                cdir = jardir.replace('/lib', '')
                rn = os.path.join(cdir, "RELEASE_NOTES.txt")
                if os.path.isfile(rn):
                    f = open(rn, "rb")
                    data = f.readlines()
                    f.close()
                    parts = shlex.split(data[0])

                    if 'version' in data[0].lower():
                        parts = shlex.split(data[0])
                        if parts[5].lower() == 'version':
                            rver = parts[6]
                        elif parts[6].lower() == 'release.':
                            rver = parts[5]

        if len(jversions) == 1:
            if rver:
                if rver in jversions[0]:
                    version = jversions[0]
                else:
                    version = rver
            else:
                version = jversions[0]
        elif len(jversions) > 1:
            if rver:
                candidates = [x for x in jversions if rver in x]
                if len(candidates) == 1:
                    version = candidates[0]
        elif rver:
            version = rver

    return version


def _getversionstring(cmd):
    '''
    $ hadoop version
    Hadoop 2.3.0-cdh5.0.1

    $ hive --version
    Hive 0.13.0.2.1.2.1-471

    $ pig --version
    Apache Pig version 0.12.1.2.1.2.1-471 (rexported)
    '''
    version = None
    for v in ['--version', 'version']:
        vcmd = "%s %s" % (cmd, v)
        if cmd == "hive" and v == "version":
            # this would open an interactive shell
            continue
        LOG.info("%s" % vcmd)
        p = Popen(vcmd, cwd=WORKDIR, stdout=PIPE, stderr=PIPE, shell=True)
        so, se = p.communicate()
        rc = p.returncode

        if rc != 0:
            #continue
            pass
        else:
            lines = so.split('\n')
            l0 = shlex.split(lines[0].lower())
            if not l0:
                continue
            if l0[0] == cmd:
                #print "version = %s" % l0[1]
                version = l0[1]
                break
            elif l0[1] == cmd:
                #print "version = %s" % l0[3]
                version = l0[3]
                break
            break

    return version


def collecthiveinfo():

    # Use hive's 'set -v' output to create a dict of active settings.
    #   runs as a singleton to reduce overall runtime

    """
    env:USER=tdatuser
    env:WINDOWMANAGER=/usr/bin/icewm
    env:XCURSOR_THEME=
    env:XDG_CONFIG_DIRS=/etc/xdg
    env:XDG_DATA_DIRS=/usr/share:/etc/opt/kde3/share:/opt/kde3/share
    env:XFILESEARCHPATH=/usr/dt/app-defaults/%L/Dt
    env:XKEYSYMDB=/usr/share/X11/XKeysymDB
    env:XNLSPATH=/usr/share/X11/nls
    system:awt.toolkit=sun.awt.X11.XToolkit
    system:file.encoding=UTF-8
    system:file.encoding.pkg=sun.io
    system:file.separator=/
    system:hadoop.home.dir=/usr/lib/hadoop
    system:hadoop.id.str=tdatuser
    """

    hiveinfo = {}

    # Make this a singleton (except on re-run?)
    datafile = os.path.join(WORKDIR, "hiveinfo")
    if not os.path.isfile(datafile):
        f = open(datafile, "wb")
        f.write("##RUNNING\n")
        f.close()
    else:
        # poll until file is finished
        status = "##RUNNING"
        data = []
        count = 0   # polling count
        stime = 10  # polling interval
        while status == "##RUNNING":
            if count > 0 and stime < 30:
                stime = stime * 2
            time.sleep(stime)
            f = open(datafile, "rb")
            data = f.readlines()
            LOG.info("collecthiveinfo - [%s] status: %s" % (os.getpid(), data[0].strip()))
            f.close()
            if data[0].strip() == "##RUNNING":
                status = "##RUNNING"
            elif data[0].strip() == "##FINISHED":
                status = "##FINISHED"
            else:
                #FIXME ?
                status = "Other"
            count += 1

        # convert raw json data to a dict
        try:
            hiveinfo = json.loads(''.join(data[1:]))
        except Exception as e:
            LOG.error("collecthiveinfo - EXCEPTION: %s" % e)
        LOG.info("collecthiveinfo  - keys: %s" % hiveinfo.keys()[0:10])
        if hiveinfo:
            return hiveinfo

    # Proceed with calling hive 'set -v' ...
    hivecmd = getcmdpath("hive")
    if not hivecmd:
        LOG.error("collecthiveinfo - hive command not found in path")
        f = open(datafile, "wb")
        f.write("##FINISHED\n")
        f.write(json.dumps(hiveinfo))
        f.close()
        return hiveinfo
    else:
        LOG.info("collecthiveinfo - [%s] hive path: %s" % (os.getpid(), hivecmd))

    # wait for all hive cli processes to stop
    while commandinpstable(hivecmd):
        LOG.info("collecthiveinfo - waiting for other hive pids to quit")
        time.sleep(2)

    cmd = "%s -e 'set -v'" % hivecmd
    # allow for 3 failures
    for i in range(0, 4):
        LOG.info("collecthiveinfo - [%s] running (%s of 3): %s -e 'set -v'" % \
            (os.getpid(), i, hivecmd))
        (rc, so, se) = run_command(cmd, cwd=WORKDIR)
        if rc == 9:
            LOG.error("collecthiveinfo - [%s] hive command timed out" % os.getpid())
        if rc != 0:
            LOG.error("collecthiveinfo - [%s] unable to get hive settings" % os.getpid())
            LOG.error("collecthiveinfo - %s" % str(so) + str(se))
            #return hiveinfo
        else:
            LOG.info("collecthiveinfo - %s -e 'set -v' finished" % hivecmd)
            break

    lines = so.split('\n')
    lines = [x.strip() for x in lines if x.strip()]
    for idx, line in enumerate(lines):
        if not '=' in line and not ':' in line:
            continue

        section = None
        subkey = None
        value = None

        if '=' in line:
            parts = line.split('=', 1)
            if len(parts) == 2:
                if ':' in parts[0]:
                    hparts = parts[0].split(':', 1)
                    section = hparts[0]
                    subkey = hparts[1]
                    value = parts[1]
                else:
                    section = parts[0]
                    value = parts[1]

                if subkey:
                    if section not in hiveinfo:
                        hiveinfo[section] = {}
                    hiveinfo[section][subkey] = value
                else:
                    hiveinfo[section] = value

    f = open(datafile, "wb")
    f.write("##FINISHED\n")
    f.write(json.dumps(hiveinfo))
    f.close()
    LOG.info("collecthiveinfo - [%s] returning data", os.getpid())
    return hiveinfo


def checkthriftport(port=9083):

    """ Verify thrift metastore is functional on a specific port """

    cmd = 'hive --hiveconf hive.metastore.uris="thrift://localhost:%s"' % port
    cmd += ' --hiveconf hive.metastore.local=false -e "show tables"'
    (rc, so, se) = run_command(cmd)
    if rc == 0:
        LOG.info("hive metastore listening on port %s" % port)
        return True
    else:
        LOG.error("hive metastore not listening on port %s" % port)
        return False


def commandinpstable(cmd):
    checkcmd = "ps aux | awk '{print $11}' | fgrep %s" % cmd
    (rc, so, se) = run_command(checkcmd)
    if rc == 0:
        return True
    else:
        return False


def jrejarfilter(jre, jars):

    # abort if no JRE provided
    if not jre:
        return jars

    # create jre base path
    jrepath = jre.replace('/bin/java', '')

    # filter out jars that contain the path
    tmpjars = []
    for jf in jars:
        if not jrepath in jf and not '/jre/lib/' in jf:
            tmpjars.append(jf)
    return tmpjars


def copyjars(options, datadict):
    jarfiles = []
    dest = options.dir
    for k, v in datadict.iteritems():
        if 'jarfiles' in v:
            if v['jarfiles']:
                for jf in v['jarfiles']:
                    if jf not in jarfiles and not '/sas.' in jf:
                        jarfiles.append(jf)

    assert not os.path.isfile(dest), \
        "%s is a file and jars cannot be copied here" % dest

    if not os.path.isdir(dest) and not os.path.isfile(dest):
        os.makedirs(dest)
    else:
        if not options.nooverwrite:
            LOG.info("emptying contents of %s" % (dest))
            shutil.rmtree(dest)
            os.makedirs(dest)

    for jf in sorted(jarfiles):
        thisf = os.path.basename(jf)
        thisp = os.path.join(dest, thisf)
        if not os.path.isfile(thisp) and os.path.isfile(jf):
            LOG.info("copy %s to %s" % (jf, dest))
            try:
                shutil.copy(jf, thisp)
            except Exception as e:
                LOG.error("%s" % e)


def dedupejars(options):
    # delete duplicate jars by md5sum
    md5cmd = getcmdpath('md5sum')
    cmd = "%s *.jar" % md5cmd
    jardict = {}
    (rc, so, se) = run_command(cmd, checkrc=False, cwd=options.dir)

    if rc != 0:
        return False

    lines = so.split('\n')
    lines = [x for x in lines if x and x.endswith('.jar')]
    for line in lines:
        parts = shlex.split(line)
        md5 = parts[0]
        jar = parts[1]
        if md5 not in jardict:
            jardict[md5] = []
        jardict[md5].append(jar)

    for k, v in jardict.iteritems():
        if len(v) == 1:
            continue

        # keep the longest filename
        longest = v[0]
        for jf in v:
            if len(jf) > longest:
                longest = jf
        for jf in v:
            if jf != longest:
                delpath = os.path.join(options.dir, jf)
                LOG.info('%s duplicates %s, removed' % (jf, longest))
                os.remove(delpath)


def copyconfig(options, datadict):
    confiles = []
    dest = options.conf
    for k, v in datadict.iteritems():
        if 'sitexmls' in v:
            if v['sitexmls']:
                for sx in v['sitexmls']:
                    if sx not in confiles:
                        confiles.append(sx)

    assert not os.path.isfile(dest), \
        "%s is a file and site xmls cannot be copied here" % dest

    if not os.path.isdir(dest) and not os.path.isfile(dest):
        os.makedirs(dest)
    else:
        if not options.nooverwrite:
            LOG.info("emptying contents of %s" % (dest))
            shutil.rmtree(dest)
            os.makedirs(dest)

    for sx in sorted(confiles):

        # ignore None types
        if not sx:
            continue

        thisf = os.path.basename(sx)
        thisp = os.path.join(dest, thisf)
        if not os.path.isfile(thisp):
            LOG.info("copy %s to %s" % (sx, dest))
            try:
                shutil.copy(sx, thisp)
            except Exception as e:
                LOG.error("%s" % e)

def threaded_worker(input, output, options):
    for svckey in iter(input.get, 'STOP'):

        svc = SERVICES[svckey]
        cmd = None
        cmdclass = None
        if 'cmd' in svc:
            cmd = svc['cmd']
        if 'class' in svc:
            cmdclass = svc['class']
        JRE = None
        CLASSPATH = None
        JAVACMD = None
        JAVAENV = None
        ECLASSPATH = None
        EJARS = None
        version = None
        sitexmls = None
        vrc = None
        stracerc = None
        metadata = {}

        if cmdclass:
            LOG.info("%s - calling class %s" % (svckey, cmdclass))
            XC = None
            try:
                XC = eval(cmdclass + '()')
            except NameError as e:
                LOG.info("%s - %s" % (svckey, e))

            if XC:
                try:
                    XC.options = options
                    XC.Run()

                    stracerc = XC.rc_strace
                    vrc = XC.rc_verbose
                    version = XC.version
                    JRE = XC.jre
                    CLASSPATH = XC.classpath
                    JAVACMD = XC.javacmd
                    JAVAENV = XC.javaenv
                    ECLASSPATH = XC.classpaths
                    EJARS = XC.jars
                    sitexmls = XC.sitexmls
                    metadata = XC.metadata
                except Exception as e:
                    exc_type, exc_value, exc_traceback = sys.exc_info()
                    tbtext = ''.join(traceback.format_exception(exc_type,
                                        exc_value, exc_traceback, 10))
                    LOG.info("%s - Exception: %s %s" % (svckey, e, tbtext))

        elif not checkcmdinpath(cmd):
            LOG.info("%s - %s not in path, skipping" % (svckey, shlex.split(cmd)[0]))
        else:
            try:
                # Handle pre-commands
                if 'pre' in svc:
                    LOG.info("%s - running pre-command" % svckey)
                    run_command(svc['pre'])

                LOG.info("%s - strace %s" % (svckey, cmd))
                rc, so, se = strace(cmd, usetimeout=True, options=options)
                stracerc = rc
                rawdata = str(so) + str(se)
                JRE, CLASSPATH, JAVACMD, JAVAENV = parse_strace_output(rawdata)
                if not JRE or not CLASSPATH or not JAVACMD or not JAVAENV:
                    LOG.error("No java info found in %s strace" % svckey)
                    output.put((svckey, version, JRE, CLASSPATH, JAVACMD,
                                JAVAENV, None, None, None, None, None))
                    return False

                sitexmls = parse_strace_open_file(rawdata, "site.xml", list=True)
                if sitexmls:
                    LOG.info("%s site.xmls %s" % (svckey, sorted(set(sitexmls))))
                else:
                    LOG.info("%s site.xmls --> None" % (svckey))

                LOG.info("%s [-verbose:class]" % (svckey))
                vrc, rawdataj = javaverbose(options, CLASSPATH, JAVACMD, JAVAENV, svckey=svckey)

                LOG.info("%s parse jars paths" % (svckey))
                ECLASSPATH = parseverboseoutput(rawdataj)
                EJARS = classpathstojars(ECLASSPATH)

                # filter out JRE provided jars
                EJARS = jrejarfilter(JRE, EJARS)

                # enumerate command version
                cparts = shlex.split(cmd)
                version = getversion(cparts[0], EJARS)
                LOG.info("%s version: %s" % (svckey, version))

                if svckey == 'hadoop':
                    # get the mapr.login.conf if defined
                    maprlogin = parse_strace_open_file(rawdata, "login.conf")
                    if maprlogin:
                        LOG.info("%s login.conf  %s" % (svckey, maprlogin))
                        sitexmls.append(maprlogin)

                    maprclusters = parse_strace_open_file(rawdata, "mapr-clusters.conf")
                    if maprclusters:
                        LOG.info("%s mapr-clusters.conf %s" % (svc, maprclusters))
                        sitexmls.append(maprclusters)

                # Handle post-commands
                if 'post' in svc:
                    LOG.info("%s - running post-command" % svckey)
                    run_command(svc['post'])

            except Exception as e:
                exc_type, exc_value, exc_traceback = sys.exc_info()
                tbtext = ''.join(traceback.format_exception(exc_type,
                                    exc_value, exc_traceback, 10))
                LOG.info("%s - Exception: %s %s" % (svckey, e, exc_traceback))

        # ~return
        output.put((svckey, version, JRE, CLASSPATH, JAVACMD,
                    JAVAENV, ECLASSPATH, EJARS, sitexmls, stracerc, vrc, metadata))


def threaded_tracer(options):

    datadict = {}
    NUMBER_OF_PROCESSES = len(SERVICES.keys())

    # Create queues
    task_queue = Queue()
    done_queue = Queue()

    # Submit tasks
    for k in SERVICES.keys():
        task_queue.put(k)

    # Start workers
    for i in range(NUMBER_OF_PROCESSES):
        Process(target=threaded_worker, args=(task_queue, done_queue, options)).start()

    # Collect results
    results = []
    for i in range(NUMBER_OF_PROCESSES):
        results.append(done_queue.get())

    for i in range(NUMBER_OF_PROCESSES):
        task_queue.put('STOP')

    for r in results:
        try:
            svc = r[0]
            datadict[svc] = {}
            datadict[svc]['version'] = r[1]
            datadict[svc]['jre'] = r[2]
            datadict[svc]['classpath'] = r[3]
            datadict[svc]['javacmd'] = r[4]
            datadict[svc]['javaenv'] = r[5]
            datadict[svc]['fqns'] = r[6]
            datadict[svc]['jarfiles'] = r[7]
            datadict[svc]['sitexmls'] = r[8]
            datadict[svc]['rc.cmd_strace'] = r[9]
            datadict[svc]['rc.java_verbose'] = r[10]
            datadict[svc]['metadata'] = r[11]
        except Exception as e:
            exc_type, exc_value, exc_traceback = sys.exc_info()
            LOG.info("Traceback: %s, %s" % (e, exc_traceback))

    return datadict


def converge_services():
    """ Make all values in SERVICES dicts """

    for k in SERVICES.keys():
        if type(SERVICES[k]) == str:
            cmd = SERVICES[k]
            SERVICES[k] = {}
            SERVICES[k]['cmd'] = cmd


def nothread_tracer(options, rerun=False, timeout=TIMEOUT):

    global SERVICES
    global DATACACHE
    datadict = {}

    for svc, cmd in SERVICES.iteritems():

        LOG.info("%s - tracer started" % svc)
        precmd = None
        postcmd = None
        cmdclass = None
        configlocs = []
        if svc not in datadict:
            datadict[svc] = {}

        # get the real command out of the cmd dict
        if type(cmd) == dict:
            if 'class' in cmd:
                cmdclass = cmd['class']
            if 'pre' in cmd:
                precmd = cmd['pre']
            if 'post' in cmd:
                postcmd = cmd['post']
            if 'cmd' in cmd:
                cmd = cmd['cmd']

        if cmdclass:
            # Instantiate the class
            # Run the class
            XC = None
            try:
                XC = eval(cmdclass + '()')
            except NameError as e:
                LOG.info("%s - %s" % (svc, e))

            if XC:
                try:
                    XC.options = options
                    XC.Run()

                    datadict[svc]['rc.cmd_strace'] = XC.rc_strace
                    datadict[svc]['rc.java_verbose'] = XC.rc_verbose
                    datadict[svc]['version'] = XC.version
                    datadict[svc]['jre'] = XC.jre
                    datadict[svc]['classpath'] = XC.classpath
                    datadict[svc]['javacmd'] = XC.javacmd
                    datadict[svc]['javaenv'] = XC.javaenv
                    datadict[svc]['fqns'] = XC.classpaths
                    datadict[svc]['jarfiles'] = XC.jars
                    datadict[svc]['sitexmls'] = XC.sitexmls
                    datadict[svc]['metadata'] = XC.metadata
                except Exception as e:
                    exc_type, exc_value, exc_traceback = sys.exc_info()
                    tbtext = ''.join(traceback.format_exception(exc_type,
                                        exc_value, exc_traceback, 10))
                    LOG.info("%s - Exception: %s %s" % (svc, e, tbtext))
                LOG.info("%s - tracer finished" % svc)

        else:
            try:
                # ignore missing commands
                if cmd and not cmdclass:
                    if not checkcmdinpath(cmd):
                        LOG.info("%s - %s not in path, skipping" % (svc, shlex.split(cmd)[0]))
                        continue

                # run any pre commands
                if precmd:
                    LOG.info("%s - running pre-command" % svc)
                    run_command(precmd)

                # Use strace if this command wasn't already traced
                if not rerun:
                    LOG.info("%s - strace %s" % (svc, cmd))
                    rc, so, se = strace(cmd, usetimeout=True, options=options)
                    rawdata = str(so) + str(se)
                    JRE, CLASSPATH, JAVACMD, JAVAENV = parse_strace_output(rawdata)
                    datadict[svc]['jre'] = JRE
                    datadict[svc]['classpath'] = CLASSPATH
                    datadict[svc]['javacmd'] = JAVACMD
                    datadict[svc]['javaenv'] = JAVAENV
                    datadict[svc]['rc.cmd_strace'] = rc

                    sitexmls = parse_strace_open_file(rawdata, "site.xml", list=True)
                    if sitexmls:
                        configlocs.extend(sitexmls)
                        configlocs = sorted(set(configlocs))
                        LOG.info("%s site.xmls %s" % (svc, sitexmls))
                    else:
                        LOG.warning("%s site.xmls --> None" % (svc))
                    datadict[svc]['sitexmls'] = configlocs

                else:
                    LOG.info("%s - using previous strace info for %s" % (svc, cmd))
                    JRE = DATACACHE[svc]['jre']
                    CLASSPATH = DATACACHE[svc]['classpath']
                    JAVACMD = DATACACHE[svc]['javacmd']
                    JAVAENV = DATACACHE[svc]['javaenv']
                    configlocs = DATACACHE[svc]['sitexmls']
                    datadict[svc]['rc.cmd_strace'] = DATACACHE[svc]['rc.cmd_strace']
                    #import pdb; pdb.set_trace()

                if not JAVACMD:
                    LOG.error("%s java command could not be parsed" % svc)
                    continue

                else:
                    if JAVACMD:
                        LOG.info("%s [-verbose:class]" % (svc))
                        vrc, rawdataj = javaverbose(options, CLASSPATH, JAVACMD, JAVAENV, svckey=svc)

                        LOG.info("%s parse jars paths" % (svc))
                        classpaths = parseverboseoutput(rawdataj)
                        jars = classpathstojars(classpaths)

                        if svc == 'hadoop':
                            # get the mapr.login.conf if defined
                            maprlogin = parse_strace_open_file(rawdata, "login.conf")
                            if maprlogin:
                                LOG.info("%s login.conf  %s" % (svc, maprlogin))
                                configlocs.append(maprlogin)

                            maprclusters = parse_strace_open_file(rawdata, "mapr-clusters.conf")
                            if maprclusters:
                                LOG.info("%s mapr-clusters.conf %s" % (svc, maprclusters))
                                configlocs.append(maprclusters)

                        # filter out JRE provided jars
                        jars = jrejarfilter(JRE, jars)
                        LOG.info("%s total jars: %s" % (svc, len(jars)))

                        # enumerate command version
                        version = getversion(svc, jars)
                        LOG.info("%s version: %s" % (svc, version))

                        datadict[svc]['rc.java_verbose'] = vrc
                        datadict[svc]['version'] = version
                        datadict[svc]['jre'] = JRE
                        datadict[svc]['classpath'] = CLASSPATH
                        datadict[svc]['javacmd'] = JAVACMD
                        datadict[svc]['javaenv'] = JAVAENV
                        datadict[svc]['fqns'] = classpaths
                        datadict[svc]['jarfiles'] = jars
                        datadict[svc]['sitexmls'] = configlocs

                # run any post commands
                if postcmd:
                    LOG.info("%s - running post-command" % svc)
                    run_command(postcmd)

            except Exception as e:
                # TRACEBACK
                exc_type, exc_value, exc_traceback = sys.exc_info()
                tbtext = ''.join(traceback.format_exception(exc_type,
                                    exc_value, exc_traceback, 10))
                LOG.info("%s - Exception: %s %s" % (svc, e, tbtext))

            LOG.info("%s - tracer finished" % svc)

    return datadict


def main(options=None):

    # do not run if things are missing
    checkprereqs()

    global SERVICES
    global DATACACHE
    global TIMEOUT
    global WORKDIR
    global LOG

    # Override the base directory if specified
    WORKDIR_BAK = WORKDIR
    if options.tmpdir:
        options.logfile = os.path.join(options.tmpdir, os.path.basename(options.logfile))
        options.conf = os.path.join(options.tmpdir, os.path.basename(options.conf))
        options.dir = os.path.join(options.tmpdir, os.path.basename(options.dir))
        options.filename = os.path.join(options.tmpdir, os.path.basename(options.filename))

        if not os.path.isdir(options.tmpdir):
            os.makedirs(options.tmpdir)
        WORKDIR_BAK = WORKDIR
        WORKDIR = tempfile.mkdtemp(prefix="hadooptracer.", dir=options.tmpdir)
    else:
        WORKDIR = tempfile.mkdtemp(prefix="hadooptracer.")

    # Fixup the tmp file locations in some of the older tracers
    for k,v in SERVICES.iteritems():
        if 'pre' in v:
            SERVICES[k]['pre'] = v['pre'].replace(WORKDIR_BAK, WORKDIR)
        if 'cmd' in v:
            SERVICES[k]['cmd'] = v['cmd'].replace(WORKDIR_BAK, WORKDIR)
        if 'post' in v:
            SERVICES[k]['post'] = v['post'].replace(WORKDIR_BAK, WORKDIR)
    
    if not os.path.isdir(WORKDIR):
        os.makedirs(WORKDIR)

    # Create a file appender for the logger
    fhdlr = logging.FileHandler(options.logfile)
    formatter = logging.Formatter('%(asctime)s hadooptracer [%(levelname)s] %(message)s')
    fhdlr.setFormatter(formatter)
    LOG.addHandler(fhdlr) 

    LOG.info("Hadoop Tracer started")
    LOG.info("Temporary File Directory: %s" % WORKDIR)

    # Log details about the environment
    localinfo = get_local_environment()
    for k,v in localinfo.iteritems():
        LOG.info("%s - %s" % (k,v))

    if options.listsvckeys:
        pprint(SERVICES)
        return 0
    elif options.svckey:
        #import pdb; pdb.set_trace()
        tmpsvcs = {}
        for k in options.svckey:
            tmpsvcs[k] = SERVICES[k]
        
        #SERVICES = {options.svckey: SERVICES[options.svckey]}
        SERVICES = tmpsvcs
        #import pdb; pdb.set_trace()

    elif options.excludesvckey:
        for k in options.excludesvckey:
            if k in SERVICES:
                SERVICES.pop(k, None)

    if options.command:
        key = shlex.split(options.command)[0]
        SERVICES = {key: options.command}

    converge_services()

    # Wait till all other tracers are finished before running mapreduce
    # it seems as though a single MR job can cause all other tracers
    # to hang up on the backend calls (especially on a mapr sandbox)
    MRSERVICES = None
    if not options.nothreads and 'mapreduce' in SERVICES and len(SERVICES.keys()) > 1:
        #import epdb; epdb.st()
        MRSERVICES = copy.deepcopy(SERVICES)
        SERVICES.pop('mapreduce', None)

    # trace defined commands threaded or not threaded
    if not options.nothreads:
        LOG.info("Starting parallel tracing")
        datadict = threaded_tracer(options)
        LOG.info("Finished with parallel tracing")
    else:
        LOG.info("Starting serialized tracing")
        datadict = nothread_tracer(options)

    # Run mapreduce now
    if not options.nothreads and MRSERVICES:
        LOG.info("Running just the mapreduce tracer now in serial mode ...")
        SERVICES = {}
        SERVICES['mapreduce'] = MRSERVICES['mapreduce']
        mrdict = nothread_tracer(options)
        # copy the results back to the main dict
        datadict['mapreduce'] = copy.deepcopy(mrdict['mapreduce'])
        # fix the services dict
        SERVICES = copy.deepcopy(MRSERVICES)

    # Only use hadoop classpath if tracing hadoop
    if not options.nohadoopclasspath:
        if (not options.svckey and not options.command) \
            or ("hadoop" in SERVICES) or ("hadoop-put" in SERVICES):

            LOG.info("Check 'hadoop classpath' command output")
            hcpjars = hadoopclasspathcmd()
            datadict['hadoop-classpath'] = {}
            datadict['hadoop-classpath']['rc.cmd_strace'] = 0
            datadict['hadoop-classpath']['rc.java_verbose'] = 0
            datadict['hadoop-classpath']['jarfiles'] = hcpjars

    # Some poorly provisioned clusters (such as sandboxes)
    # have issues with concurrency, so various tracers will
    # fail for no good reason. Due to that "problem", attempt 
    # to rerun those tracers in serialized mode.
    if not options.skipretry:
        LOG.info("looking for failures to re-run those tracers")
        keys = datadict.keys()
        failed_keys = []
        for k,v in datadict.iteritems():
            if v['rc.cmd_strace'] != 0 or v['rc.java_verbose'] != 0:
                failed_keys.append(k)
            #import pdb; pdb.set_trace()
        LOG.info("retracing: %s" % failed_keys)

        # save the traced data to avoid re-running strace
        DATACACHE = copy.deepcopy(datadict)

        # save the global services dict
        for key in keys:
            if key not in failed_keys:
                SERVICES.pop(key, None)

        retry_dict = nothread_tracer(options, rerun=True)

        # merge the new data back into the datadict
        for key in failed_keys:
            if key in retry_dict:
                datadict[key] = copy.deepcopy(retry_dict[key])
            else:
                datadict[key] = {}
                datadict[key]['rc.cmd_strace'] = -1
                datadict[key]['rc.java_verbose'] = -1

    #####################################
    #   JSON WRITER ...
    #####################################
    thisfile = "/tmp/hadooptrace.json"
    if options:
        if hasattr(options, 'filename'):
            thisfile = options.filename
    LOG.info("Writing results to %s" % thisfile)

    # strip out the dirname
    dirpath = os.path.dirname(thisfile)
    if not os.path.isdir(dirpath):
        os.makedirs(dirpath)

    # add local data
    if not 'metadata' in datadict:
        datadict['tracer_metadata'] = {}
    for k,v in localinfo.iteritems():
        datadict['tracer_metadata'][k] = v

    f = open(thisfile, "wb")
    f.write(json.dumps(datadict, sort_keys=True, indent=2))
    f.close()
    #####################################

    LOG.info("Copy jars to %s" % options.dir)
    copyjars(options, datadict)

    LOG.info("Deduplicating jars")
    dedupejars(options)

    LOG.info("Copy site.xml files to %s" % options.conf)
    copyconfig(options, datadict)

    LOG.info("Combine site.xml files into combined-site.xml")
    sitexmlcombiner(options.conf)

    if options.noclean:
        LOG.info("Tempfiles stored in %s" % WORKDIR)
    else:
        LOG.info("Cleaning up temporary directory %s" % WORKDIR)
        shutil.rmtree(WORKDIR)

    # create the returncode
    rc = 0
    failed = ''
    for k, v in datadict.iteritems():
        if k == "tracer_metadata":
            continue
        if 'rc.cmd_strace' in v:
            if v['rc.cmd_strace'] != 0:
                fk = k + '.rc.cmd_strace '
                failed += fk
                rc += 1
        else:
            fk = k + '.rc.cmd_strace '
            failed += fk
            rc += 1
        if 'rc.java_verbose' in v:
            if v['rc.java_verbose'] != 0:
                fk = k + '.rc.java_verbose '
                failed += fk
                rc += 1
        else:
            fk = k + '.rc.java_verbose '
            failed += fk
            rc += 1

    if options.stoponerror:
        LOG.info("Hadoop Tracer finished - failures: %s [%s]" % (rc, str(failed)))
        return rc
    else:
        if rc == 0:
            LOG.info("Hadoop Tracer finished - failures: %s" % rc)
        else:
            LOG.info("Hadoop Tracer finished - failures: %s [ignored - %s]" % (rc, str(failed)))
        return 0

def get_local_environment():

    info = {}

    # hostname
    info['hostname'] = socket.gethostname()

    # username
    info['username'] = getpass.getuser()

    # cwd
    info['pwd'] = os.getcwd()

    return info


if __name__ == "__main__":

    parser = OptionParser()

    # Results Storage
    parser.add_option("-b", "--basedir",
                      help="Use this directory instead of /tmp for storing all results",
                      action="store", dest="tmpdir")
    parser.add_option("-f", "--file",
                      dest="filename",
                      help="write results to FILE",
                      default="/tmp/hadooptracer.json",
                      metavar="FILE")
    parser.add_option("-d", "--directory", "--jars",
                      help="copy jars to this directory",
                      default="/tmp/jars",
                      action="store", dest="dir")
    parser.add_option("--conf", "--confdirectory", "--sitexmls",
                      help="copy config files to this directory",
                      default="/tmp/sitexmls",
                      action="store", dest="conf")
    parser.add_option("--logfile",
                      help="Store the log output here",
                      default="/tmp/hadooptracer.log",
                      action="store", dest="logfile")

    # Hive settings
    parser.add_option("-s", "--hivehostname",
                      help="specify the hive host name if its not namenode.",
                      default="localhost",
                      action="store", dest="hivehost")
    parser.add_option("--hiveusername",
                      help="specify the hive username if necessary.",
                      default="%s" % getpass.getuser(),
                      action="store", dest="hiveusername")
    parser.add_option("--hivepassword",
                      help="specify the hive username if necessary.",
                      default="",
                      action="store", dest="hivepassword")

    # Limit traced commands
    parser.add_option("--listsvckeys",
                      help="list services that will be traced",
                      default=False,
                      action="store_true", dest="listsvckeys")

    parser.add_option("--svckey",
                      help="trace only this service key [see list keys]",
                      action="append", dest="svckey")

    parser.add_option("--excludesvckey",
                      help="trace only this service key [see list keys]",
                      action="append", dest="excludesvckey")


    parser.add_option("--command",
                      help="trace this arbitrary command",
                      action="store", dest="command")

    parser.add_option("--nohadoopclasspath", action="store_true",
                      default=False,
                      help="do not fetch all the jars in the hadoop classpath")

    # General behavior controls
    parser.add_option("--nooverwrite", action="store_true",
                      default=False,
                      dest="nooverwrite",
                      help="do not clean out pre-existing jar/conf dirs")

    parser.add_option("--noclean", action="store_true",
                      help="do not clean up temp files")

    parser.add_option("--stoponerror", action="store_true",
                      help="If a command fails, change the file exit code to non-zero [default: False]")

    parser.add_option("--nothreads", action="store_true",
                      help="Do not multi-thread the tracing actions")

    parser.add_option("--verbose", action="store_true",
                      default=False,
                      help="Show extended information in the log output")

    parser.add_option("--skipretry",
                      action="store_true",
                      default=False,
                      help="Do not retry tracers that failed (serialized) [default:false]")

    # Dataloader+derby workaround: 
    #   https://rndjira.sas.com/browse/VAPPEN-1775 
    #   http://sww.sas.com/ds/DefectsSearch/S1186/S1186811.html
    #   http://sww.sas.com/cgi-bin/quick_browse?defectid=S1186807
    parser.add_option("--excludepackage",
                      help="exclude any jars that contain these packages [should be a / delimited classpath]",
                      default=['org/apache/derby'],
                      action="append", dest="excludepackage")


    (options, args) = parser.parse_args()
    sys.exit(main(options=options))
