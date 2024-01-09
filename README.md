[![TypeDB](./docs/banner.png)](https://typedb.com/introduction)

[![Factory](https://factory.vaticle.com/api/status/vaticle/typedb/badge.svg)](https://factory.vaticle.com/vaticle/typedb)
[![CircleCI](https://circleci.com/gh/vaticle/typedb/tree/master.svg?style=shield)](https://circleci.com/gh/vaticle/typedb/tree/master)
[![GitHub release](https://img.shields.io/github/release/vaticle/typedb.svg)](https://github.com/vaticle/typedb/releases/latest)
[![Discord](https://img.shields.io/discord/665254494820368395?color=7389D8&label=chat&logo=discord&logoColor=ffffff)](https://typedb.com/discord)
[![Discussion Forum](https://img.shields.io/badge/discourse-forum-blue.svg)](https://forum.typedb.com)
[![Stack Overflow](https://img.shields.io/badge/stackoverflow-typedb-796de3.svg)](https://stackoverflow.com/questions/tagged/typedb)
[![Stack Overflow](https://img.shields.io/badge/stackoverflow-typeql-3dce8c.svg)](https://stackoverflow.com/questions/tagged/typeql)
[![Hosted By: Cloudsmith](https://img.shields.io/badge/OSS%20hosting%20by-cloudsmith-blue?logo=cloudsmith&style=flat)](https://cloudsmith.com)

# Introducing TypeDB

TypeDB is a [polymorphic](https://typedb.com/features#polymorphic-queries) database with a [conceptual](https://typedb.com/features#conceptual-modeling) data model, a strong [subtyping](https://typedb.com/features#strong-type-system) system, a symbolic [reasoning](https://typedb.com/features#symbolic-reasoning) engine, and a beautiful and elegant [type-theoretic](https://typedb.com/features#modern-language) language [TypeQL](https://github.com/vaticle/typeql).

> **IMPORTANT NOTE:** TypeDB & TypeQL are in the process of being ported over and rewritten in [Rust](https://www.rust-lang.org). There will be changes that won't be backwards compatible, as we refine the the language further to extend its expressivity, as well as changes to the byte storage data structure to further boost performance significantly. We're aiming to complete this by February/March 2024, released as TypeDB 3.0, along with preliminary benchmarks of TypeDB.

## Polymorphic databases

###  Why TypeDB was built

Data frequently exhibits polymorphic features in the form of inheritance hierarchies and interface dependencies. TypeDB was crafted to solve the inability of current database paradigms to natively express these polymorphic features.

- Relational schemas have [no native capability for modeling polymorphic data](https://typedb.com/philosophy#why-do-we-need-a-polymorphic-database).
- Unstructured databases eliminate the schemas entirely, but this [prevents declarative data retrieval](https://typedb.com/philosophy#why-do-we-need-a-polymorphic-database).
- [ORMs work around the fundamental problem](https://typedb.com/philosophy#why-do-we-need-a-polymorphic-database) by trading off performance.


### Providing full support for polymorphism

<!-- Polymorphism in programming languages and data modeling comes in the form of [interface](https://typedb.com/philosophy#what-defines-a-polymorphic-database), [inheritance](https://typedb.com/philosophy#what-defines-a-polymorphic-database), and [parametric polymorphism](https://typedb.com/philosophy#what-defines-a-polymorphic-database).  -->

In order to fully support polymorphism, a database needs to implement three key components:

- Support for [**polymorphic** **schemas**](https://typedb.com/features#conceptual-modeling) that can express inheritance hierarchies and interface implementations.
- Implementation of a fully [**variablizable** **query language**](https://typedb.com/features#polymorphic-queries) to support powerful [parametric](https://typedb.com/philosophy#what-defines-a-polymorphic-database) database operations.
- Integration of an [**inference engine**](https://typedb.com/features#strong-type-system) to interpret variables in the semantic context given by the schema.



## The TypeDB database

### The schema

TypeDB schemas are based on a modern type system that natively supports inheritance and interfaces, and follows a [conceptual data modeling](https://typedb.com/features#conceptual-modeling) approach, in which user-defined types subtype (based on their function) three root types: [entities](https://typedb.com/features#conceptual-modeling), [relations](https://typedb.com/features#expressive-relations), and [attributes](https://typedb.com/features#intuitive-attributes).

- *Entities* are independent objects,
- *Relations* depend on their *role* interfaces played by either entities or relations,
- *Attributes* are properties with a value that can be *owned* by entities or relations.

Interface and inheritance for these types can be combined in many ways, resulting in highly expressive ways of modeling data.

```php
define

full-name sub attribute, value string;
id sub attribute, value string;
email sub id;
employee-id sub id;

user sub entity,
    owns full-name,
    owns email @unique,
    plays mentorship:trainee;
employee sub user,
    owns employee-id @key,
    plays mentorship:mentor;

mentorship sub relation,
    relates mentor,
    relates trainee;
```


### The query language

The query language of TypeDB is [TypeQL](https://typedb.com/docs/typeql/overview). The syntax of TypeQL is fully variablizable and provides native support for polymorphic queries. The language is based on [fully declarative and composable](https://typedb.com/features#modern-language) patterns, mirroring the structure of natural language.

```php
match $user isa user,
    has full-name $name,
    has email $email;
# This returns all users of any type

match $user isa employee,
    has full-name $name,
    has email $email,
    has employee-id $id;
# This returns only users who are employees

match $user-type sub user;
$user isa $user-type,
    has full-name $name,
    has email $email;
# This returns all users and their type
```


### The inference engine

Any query in TypeDB is [semantically validated](https://typedb.com/features#strong-type-system) by TypeDB’s inference engine for consistency with the database schema. This prevents invalid schema updates and data inserts before they can affect the integrity of the database.

TypeDB can also work with data that is not physically stored in the database, but instead logically inferred based on user-specified [rules](https://typedb.com/features#symbolic-reasoning). This enables developers to cleanly separate their source data from their application logic, often allowing for complex systems to be described by combinations of simple rules.

```php
define
rule transitive-team-membership:
    when {
        (team: $team-1, member: $team-2) isa team-membership;
        (team: $team-2, member: $member) isa team-membership;
    } then {
        (team: $team-1, member: $member) isa team-membership;
    };

insert
$john isa user, has email "john@vaticle.com";
$eng isa team, has name "Engineering ";
$cloud isa team, has name "Cloud";
(team: $eng, member: $cloud) isa team-membership;
(team: $cloud, member: $john) isa team-membership;

match
$john isa user, has email "john@vaticle.com";
(team: $team, member: $john) isa team-membership;
# This will return both Cloud and Engineering for $team due to the defined rule
```
 

## Effective database engineering

TypeDB breaks down the patchwork of existing database paradigms into three fundamental ingredients: [types](https://typedb.com/features#strong-type-system), [inheritance](https://typedb.com/features#conceptual-modeling), and [interfaces](https://typedb.com/features#polymorphic-queries). This provides a unified way of working with data across all database applications, that directly impacts development:

- Make use of full [object model parity](https://typedb.com/#solve-object-relational-mismatch-entirely-within-the-database) when working with OOP
- Ensure [continuous extensibility](https://typedb.com/features#conceptual-modeling) of your data model
- Work with high-level [logical abstractions](https://typedb.com/features#conceptual-modeling) eliminating the need for physical data modeling
- Let TypeDB's inference engine guarantee [data-consistency](https://typedb.com/#avoid-data-redundancy-and-ensure-data-consistency-in-real-time) at all times
- Write high-clarity code with TypeQL's [near-natural](https://typedb.com/features#modern-language) queries even for the most complex databases
- Unleash the power of [fully declarative and composable](https://typedb.com/features#modern-language) patterns onto your data


## Installation and editions

### TypeDB editions

* [TypeDB Cloud](https://cloud.typedb.com) — multi-cloud DBaaS
* [TypeDB Enterprise](mailto://sales@vaticle.com) — Enterprise edition of TypeDB
* **TypeDB Core** — Open-source edition of TypeDB ← _This repository_

For a comparison of all three editions, see the [Deploy](https://typedb.com/deploy) page on our website.


### Download and run TypeDB Core

You can download TypeDB from the [GitHub Releases](https://github.com/vaticle/typedb/releases). 

Check our [Installation guide](https://typedb.com/docs/typedb/2.x/installation) to get started.


### Compiling TypeDB Core from source

> Note: You DO NOT NEED to compile TypeDB from the source if you just want to use TypeDB. See the _"Download and Run 
> TypeDB Core"_ section above.

1. Make sure you have the following dependencies installed on your machine:
   - Java JDK 11 or higher
   - [Bazel 6 or higher](https://bazel.build/install).

2. You can build TypeDB with either one of the following commands, depending on the targeted architecture and 
   Operation system: 

   ```sh
   $ bazel build //:assemble-linux-x86_64-targz
   $ bazel build //:assemble-linux-arm64-targz
   $ bazel build //:assemble-mac-x86_64-zip
   $ bazel build //:assemble-mac-arm64-zip
   $ bazel build //:assemble-windows-x86_64-zip
   ```

   Outputs to: `bazel-bin/`.

3. If you're on a Mac and would like to run any `bazel test` commands, you will need to install:
   - snappy: `brew install snappy`
   - jemalloc: `brew install jemalloc`


## Resources

### Developer resources

- Documentation: https://typedb.com/docs
- Discussion Forum: https://forum.typedb.com/
- Discord Chat Server: https://typedb.com/discord
- Community Projects: https://github.com/typedb-osi


### Useful links

If you want to begin your journey with TypeDB, you can explore the following resources:

* More on TypeDB's [features](https://typedb.com/features)
* In-depth dive into TypeDB's [philosophy](https://typedb.com/philosophy)
* Our [TypeDB quickstart](https://typedb.com/docs/home/quickstart)
* [TypeDB in 25 queries](https://typedb.com/docs/home/25-queries)
* **[TypeQL](https://github.com/vaticle/typeql)**
* **[TypeDB Studio](https://github.com/vaticle/typedb-studio)**


## Contributions

TypeDB and TypeQL are built using various open-source frameworks and technologies throughout its evolution. 
Today TypeDB and TypeQL use
[Speedb](https://www.speedb.io/),
[pest](https://pest.rs/),
[SCIP](https://www.scipopt.org),
[Bazel](https://bazel.build),
[gRPC](https://grpc.io),
[ZeroMQ](https://zeromq.org), 
and [Caffeine](https://github.com/ben-manes/caffeine). 

Thank you!

In the past, TypeDB was enabled by various open-source products and communities that we are hugely thankful to:
[RocksDB](https://rocksdb.org),
[ANTLR](https://www.antlr.org),
[Apache Cassandra](http://cassandra.apache.org), 
[Apache Hadoop](https://hadoop.apache.org), 
[Apache Spark](http://spark.apache.org), 
[Apache TinkerPop](http://tinkerpop.apache.org), 
and [JanusGraph](http://janusgraph.org). 

### Package hosting
Package repository hosting is graciously provided by  [Cloudsmith](https://cloudsmith.com).
Cloudsmith is the only fully hosted, cloud-native, universal package management solution, that
enables your organization to create, store and share packages in any format, to any place, with total
confidence.

## Licensing

This software is developed by [Vaticle](https://vaticle.com/).  
It's released under the GNU Affero GENERAL PUBLIC LICENSE version 3 (AGPL v.3.0).
For license information, please see [LICENSE](https://github.com/vaticle/typedb/blob/master/LICENSE). 

Vaticle also provides a commercial license for TypeDB Enterprise - get in touch with our team at 
[commercial@vaticle.com](emailto://sales@vaticle.com).

Copyright (C) 2023 Vaticle.
