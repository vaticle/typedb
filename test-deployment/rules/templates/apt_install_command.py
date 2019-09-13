#!/usr/bin/env python

#
# GRAKN.AI - THE KNOWLEDGE GRAPH
# Copyright (C) 2019 Grakn Labs Ltd
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU Affero General Public License as
# published by the Free Software Foundation, either version 3 of the
# License, or (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU Affero General Public License for more details.
#
# You should have received a copy of the GNU Affero General Public License
# along with this program.  If not, see <https://www.gnu.org/licenses/>.
#

import os
import json
import subprocess as sp

refs = {
    'commits': {},
    'tags': {},
}

with open("workspace_refs.json") as f:
    refs = json.load(f)


def get_commit():
    return sp.check_output([
        'git', 'rev-parse', 'HEAD'
    ], cwd=os.getenv('BUILD_WORKSPACE_DIRECTORY')).decode().strip()


def get_dep_version(ws):
    if ws in refs['commits']:
        return '0.0.0-' + refs['commits'][ws]
    elif ws in refs['tags']:
        return refs['tags'][ws]
    else:
        raise Exception('no reference of workspace @{}'.format(ws))


core_version = '0.0.0-' + get_commit()
console_version = get_dep_version("graknlabs_console")
bin_version = get_dep_version("graknlabs_common")

command = [
    'sudo',
    'apt',
    'install',
    'grakn-core-all={}'.format(core_version),
    'grakn-core-server={}'.format(core_version),
    'grakn-core-console={}'.format(console_version),
    'grakn-core-bin={}'.format(bin_version),
]

print('Executing command: {}'.format(' '.join(command)))
sp.check_call(command)
