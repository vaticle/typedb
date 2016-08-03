#!/bin/bash

# MindmapsDB - A Distributed Semantic Database
# Copyright (C) 2016  Mindmaps Research Ltd
#
# MindmapsDB is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# MindmapsDB is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with MindmapsDB. If not, see <http://www.gnu.org/licenses/gpl.txt>.

[[ $(readlink $0) ]] && path=$(readlink $0) || path=$0

ENGINE_STARTUP_TIMEOUT_S=30
CASSANDRA_STARTUP_TIMEOUT_S=60
SLEEP_INTERVAL_S=2

# from titan
wait_for_cassandra() {
    local now_s=`date '+%s'`
    local stop_s=$(( $now_s + $CASSANDRA_STARTUP_TIMEOUT_S ))
    local status_thrift=

    while [ $now_s -le $stop_s ]; do
        echo -n .
        # The \r\n deletion bit is necessary for Cygwin compatibility
        status_thrift="`nodetool statusthrift 2>/dev/null | tr -d '\n\r'`"
        if [ $? -eq 0 -a 'running' = "$status_thrift" ]; then
            echo
            return 0
        fi
        sleep $SLEEP_INTERVAL_S
        now_s=`date '+%s'`
    done

    echo " timeout exceeded ($CASSANDRA_STARTUP_TIMEOUT_S seconds)" >&2
    return 1
}

wait_for_engine() {
    local now_s=`date '+%s'`
    local stop_s=$(( $now_s + $ENGINE_STARTUP_TIMEOUT_S ))
    local status_thrift=

    while [ $now_s -le $stop_s ]; do
        echo -n .
        # get everything listening on port 4567
        num_listeners=`lsof -i :4567 -t | wc -l`
        if [ "$num_listeners" -ne "0" ]; then
            echo
            return 0
        fi
        sleep $SLEEP_INTERVAL_S
        now_s=`date '+%s'`
    done

    echo " timeout exceeded ($ENGINE_STARTUP_TIMEOUT_S seconds)" >&2
    return 1
}

case "$1" in

start)


    if [ -e /tmp/mindmaps-cassandra.pid ] && ps -p `cat /tmp/mindmaps-cassandra.pid` > /dev/null ; then
        echo "Cassandra already running"
    else
        # cassandra has not already started
        echo -n "Starting cassandra"
        # we hide errors because of a java bug that prints "Cass JavaLaunchHelper is implemented in both..."
        `dirname $path`/cassandra -p /tmp/mindmaps-cassandra.pid > /dev/null 2> /dev/null

        if ! wait_for_cassandra ; then exit 1 ; fi
    fi

    if [ -e /tmp/mindmaps-engine.pid ] && ps -p `cat /tmp/mindmaps-engine.pid` > /dev/null ; then
        echo "Engine already running"
    else
        # engine has not already started
        echo -n "Starting engine"
        java -cp "`dirname $path`/../lib/*" MindmapsEngineServer > /dev/null &
        echo $!>/tmp/mindmaps-engine.pid
        wait_for_engine
    fi
    ;;

stop)

    echo "Stopping engine"
    if [[ -e /tmp/mindmaps-engine.pid ]]; then
        kill `cat /tmp/mindmaps-engine.pid`
        rm /tmp/mindmaps-engine.pid
    fi

    echo "Stopping casasndra"
    if [[ -e /tmp/mindmaps-cassandra.pid ]]; then
        kill `cat /tmp/mindmaps-cassandra.pid`
        rm /tmp/mindmaps-cassandra.pid
    fi
    ;;

*)
    echo "Usage: $0 {start|stop}"
    ;;

esac