#
# GRAKN.AI - THE KNOWLEDGE GRAPH
# Copyright (C) 2018 Grakn Labs Ltd
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

#!/usr/bin/env bash


ARTIFACT="$ARTIFACT"
COORDINATES="$COORDINATES"
VERSION="{pom_version}"

GROUP_ID="$(echo $COORDINATES | cut -d / -f 1,2 | sed -e 's@/@.@g')"

if [[ $# -ne 3 ]]; then
    echo "Should pass <snapshot|release> <maven-username> <maven-password> as arguments"
    exit 1
fi


MAVEN_REPO_TYPE="$1"
MAVEN_USERNAME="$2"
MAVEN_PASSWORD="$3"


if [[ "$MAVEN_REPO_TYPE" != "snapshot" ]] && [[ "$MAVEN_REPO_TYPE" != "release" ]]; then
    echo "Error: first argument should be 'snapshot' or 'release', not '$MAVEN_REPO_TYPE'"
    exit 1
fi


MAVEN_URL=$(grep "maven.repository-url.$MAVEN_REPO_TYPE" deployment.properties | cut -d '=' -f 2)

platform=$(uname)

MD5_BINARY=""
SHA1_BINARY=""

if [[ "$platform" == "Darwin" ]]; then
    MD5_BINARY="md5 -q"
    SHA1_BINARY="shasum -a 1"
elif [[ "$platform" == "Linux" ]]; then
    MD5_BINARY="md5sum"
    SHA1_BINARY="sha1sum"
else
    echo "Error: there are no md5 and sha1 binaries for your platform: $platform"
    exit 1
fi

# Update the JAR contents to simulate Maven structure
DIRECTORY_INSIDE_JAR=META-INF/maven/$GROUP_ID/$ARTIFACT/
cp lib.jar lib-with-maven-metadata.jar # un-symlink it and add the maven metadata to the new copy afterwards
mkdir -p $DIRECTORY_INSIDE_JAR/

install -m 755 pom.xml $DIRECTORY_INSIDE_JAR/pom.xml

echo "#Generated by Bazel" > $DIRECTORY_INSIDE_JAR/pom.properties
echo "#$(LANG=C date)" >> $DIRECTORY_INSIDE_JAR/pom.properties
echo "version=$VERSION" >> $DIRECTORY_INSIDE_JAR/pom.properties
echo "groupId=$GROUP_ID" >> $DIRECTORY_INSIDE_JAR/pom.properties
echo "artifactId=$ARTIFACT" >> $DIRECTORY_INSIDE_JAR/pom.properties

jar -fu lib-with-maven-metadata.jar META-INF/

$MD5_BINARY pom.xml | awk '{print $1}' > pom.md5
$MD5_BINARY lib-with-maven-metadata.jar | awk '{print $1}' > lib.jar.md5
curl -X PUT -u $MAVEN_USERNAME:$MAVEN_PASSWORD --upload-file pom.md5 $MAVEN_URL/$COORDINATES/$VERSION/$ARTIFACT-$VERSION.pom.md5
curl -X PUT -u $MAVEN_USERNAME:$MAVEN_PASSWORD --upload-file lib.jar.md5 $MAVEN_URL/$COORDINATES/$VERSION/$ARTIFACT-$VERSION.jar.md5

$SHA1_BINARY pom.xml | awk '{print $1}' > pom.sha1
$SHA1_BINARY lib-with-maven-metadata.jar | awk '{print $1}' > lib.jar.sha1
curl -X PUT -u $MAVEN_USERNAME:$MAVEN_PASSWORD --upload-file pom.sha1 $MAVEN_URL/$COORDINATES/$VERSION/$ARTIFACT-$VERSION.pom.sha1
curl -X PUT -u $MAVEN_USERNAME:$MAVEN_PASSWORD --upload-file lib.jar.sha1 $MAVEN_URL/$COORDINATES/$VERSION/$ARTIFACT-$VERSION.jar.sha1

curl -X PUT -u $MAVEN_USERNAME:$MAVEN_PASSWORD --upload-file pom.xml $MAVEN_URL/$COORDINATES/$VERSION/$ARTIFACT-$VERSION.pom
curl -X PUT -u $MAVEN_USERNAME:$MAVEN_PASSWORD --upload-file lib-with-maven-metadata.jar $MAVEN_URL/$COORDINATES/$VERSION/$ARTIFACT-$VERSION.jar
