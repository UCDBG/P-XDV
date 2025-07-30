# P-XDV Overview

**P-XDV** is a framework that allows users to estimate the price of data shared between buyers and sellers based on provenance and generate explanations of the estimated price. Provenance is information about how a query's result was produced based on the given input data and a query containing several database operations. Various provenance types provide different level of information. P-XDV captures where and how provenance to computed the value of shared data at a fine-grained level. The system follows the capabilities of other systems such as GProM that relay on query instrumentation techniques for capturing provenance. P-XDV also provides meaningful top-*k* patterns as an explanation that are extracted based on various metrics determining the pattern's contribution to the estimated price. 
<!-- That is, for a row in a table returned by a query we capture from which rows it was derived from the input table and by which operations.  -->
<!-- through annotations and their respective columns along with calculating a distance metric between two tuples during integration of data.  -->
<!-- PEDS builds on the capabilities of GProM to rewrite input queries into rewritten queries for more complex actions.  -->
<!--For information about the research behind PEDS have a look at the link : https://scholar.google.com/citationsview_op=view_citation&hl=en&user=RzClsh8AAAAJ&citation_for_view=RzClsh8AAAAJ:roLk4NBRz8UC-->


# Simple Demo
You will also need to create 2 new functions namely hammingxor and hammingxorvalue in postgres. The code for those functions are porvided in createTable.sql file.
To run a simple P-XDV sinerio, you can write a command in the following format:
+ to estimate the price
  + ./scripts/eig_run.sh ${log_level} "IG OF (${query});"
  + Example: ./scripts/eig_run.sh 3 "IG OF (select * from owned o FULL OUTER JOIN shared s ON(o.county = s.county AND o.year = s.year));"
+ to compute explanations
  + ./scripts/eig_run.sh ${log_level} "IGEXPL TOP ${k} OF (${query});"
  + Example: ./scripts/eig_run.sh 3 "IGEXPL TOP 10 OF (select * from owned o FULL OUTER JOIN shared s ON(o.county = s.county AND o.year = s.year));"

Below, we show sample data from a real-world Air Quality Index dataset(AQI) for the example queries above.
This demo shows a simple sinerio to familiarize the users with two of P-XDV functionality. 
+ (i)  That computed the degree of new information and
+ (ii) That shows meaningful patterns found after integration step.

```
sample data for owned 

 year | county    | dayswaqi | maqi | 
-------------------------------------
 2021 | Colbert   | 274      | 200  |
 2021 | Jackson   | 366      | 200  |
 2022 | Jefferson | 348      | 271  |
 2022 | Autauga   | 179      | 177  |

sample data for shared

 year | county    | gdays | maqi | 
----------------------------------
 2021 | Jackson   | 85   | 156  |
 2022 | Colbert   | 66   | 200  |
 2022 | Jefferson | 66   | 221  |
 2021 | Colbert   | 66   | 168  |
 2022 | Autauga   | 122  | 177  |

output for first command. Shows IG only

 year | county    | dayswaqi | maqi | gdays | IG_year | IG_county | IG_dayswaqi | IG_maqi | IG_gdays | Total_IG |
-----------------------------------------------------------------------------------------------------------------
 2021 | Colbert   | 274      | 168  | 66    | 0       | 0         | 0           | 2       | 2        | 4        |
 2021 | Jackson   | 366      | 156  | 85    | 0       | 0         | 0           | 3       | 4        | 7        |
 2022 | Jefferson | 348      | 221  | 66    | 0       | 0         | 0           | 5       | 2        | 7        |
 2022 | Autauga   | 179      | 177  | 122   | 0       | 0         | 0           | 0       | 5        | 5        |
 2022 | Colbert   | null     | 200  | 66    | 0       | 0         | 0           | 3       | 2        | 5        |

output for second command. Shows the best patterns and the f_score based on which they are ranked on

 year | county    | dayswaqi | maqi | gdays | imp | info | cov | f_score |
-------------------------------------------------------------------------- 
 2022 | *         | *       | *     | 66    | 12  | 2    | 2   | 11.29   |
 *    | Colbert   | *       | *     | 66    | 9   | 2    | 2   | 10.29   |
 *    | *         | *       | *     | 66    | 16  | 1    | 3   | 9.14    |
 2021 | *         | *       | *     | *     | 17  | 1    | 3   | 5.87    |
 2022 | *         | *       | *     | *     | 11  | 1    | 2   | 4.25    |

```

<!--
# Documentation (Wiki Links)

* [Installation Instructions](https://github.com/IITDBGroup/gprom/wiki/installation)
* [Tutorial](https://github.com/IITDBGroup/gprom/wiki/tutorial)
* [GProM Commandline Shell Manual](https://github.com/IITDBGroup/gprom/blob/master/doc/gprom_man.md)
* Provenance Language Features
  * [SQL](https://github.com/IITDBGroup/gprom/wiki/sql_extensions)
  * [Datalog](https://github.com/IITDBGroup/gprom/wiki/lang_datalog)
* [Docker containers](https://github.com/IITDBGroup/gprom/wiki/docker)
* [Optimization](https://github.com/IITDBGroup/gprom/wiki/research_optimization)
* [Reenactment](https://github.com/IITDBGroup/gprom/wiki/research_reenactment)
* [Provenance Graphs for Datalog](https://github.com/IITDBGroup/gprom/wiki/datalog_prov)

# Features

+ Annotation and capture of where and how provenance
+ Calculation of degree of new information i.e Information Gain (IG)
+ Computation of quality patterns
+ Analysis of patterns
+ Flexible on-demand provenance capture and querying for SQL queries using language-level instrumentation, i.e., by running SQL queries.
+ Retroactive provenance capture for transactions using reenactment. Notably, our approach requires no changes to the transactional workload and underlying DBMS
+ Produce provenance graphs for Datalog queries that explain why (provenance) or why-not (missing answers) a tuple is in the result of a Datalog query
+ Heuristic and cost-based optimization for queries instrumented for provenance capture
+ Export of database provenance into the WWW PROV standard format

# Usage #

To use **P-XDV**, you will just need to install gprom, the interactive shell of GProM, you will need to have one of the supported backend databases installed. For casual use cases, you can stick to SQLite. However, to fully exploit the features of GProM, you should use Oracle. We also provide several docker containers with gprom preinstalled (see [here](https://github.com/IITDBGroup/gprom/wiki/docker)) When starting gprom, you have to specify connection parameters to the database. For example, using one of the convenience wrapper scripts that ship with GProM, you can connected to a test SQLite database included in the repository by running the following command in the main source folder after installation:

```
gprom -backend sqlite -db ./examples/test.db
```

will start the shell connecting to an SQLite database `./examples/test.db`. If GProM is able to connect to the database, then this will spawn a shell like this:

```
GProM Commandline Client
Please input a SQL command, '\q' to exit the program, or '\h' for help
======================================================================

Oracle SQL - SQLite:./examples/test.db$
```

In this shell you can enter SQL and utility commands. The shell in turn will show you query results (just like your favorite DB shell). However, the main use of GProM is on-demand capture of provenance for database operations. You can access this functionality through several new SQL language constructs supported by GProM. Importantly, these language constructs behave like queries and, thus, can be used as part of more complex queries. Assume you have a table `R(A,B)`, let us ask our first provenance query.

```
Oracle SQL - SQLite:./examples/test.db$ SELECT * FROM R;
 A | B |
--------
 1 | 1 |
 2 | 3 |

Oracle SQL - SQLite:./examples/test.db$ PROVENANCE OF (SELECT A FROM r);

 A | PROV_R_A | PROV_R_B |
--------------------------
 1 | 1        | 1        |
 2 | 2        | 3        |
```

As you can see, `PROVENANCE OF (q)` returns the same answer as query `q`, but adds additional *provenance* attributes. These attributes store for each result row of the query the input row(s) which where used to compute the output row. For example, the query result `(1)` was derived from row `(1,1)` in table `R`. For now let us close the current session using the `\q` utility command:

```
Oracle SQL - SQLite:./examples/test.db$ \q
```

Provenance for SQL queries is only one of the features supported by GProM. A full list of SQL language extensions supported by GProM can be found in the [wiki](https://github.com/IITDBGroup/gprom/wiki/). See the [man page](https://github.com/IITDBGroup/gprom/blob/master/doc/gprom_man.md) of gprom for further information how to use the CLI of the system. 
--> 

# Installation

P-XDV installation follows the installation of GProM. The [wiki](https://github.com/IITDBGroup/gprom/wiki/installation) has detailed installation instructions. <!--In a nutshell, GProM can be compiled with support for different database backends and is linked against the C client libraries of these database backends.--> The installation follows the standard procedure using GNU build tools. Checkout the git repository, install all dependencies and run:

```
./autogen.sh
./configure
make
sudo make install
```

<!--
# Research and Background

P-XDV builds on GProM and the functionality of GProM is based on a long term research effort by the [IIT DBGroup](http://www.cs.iit.edu/~dbgroup/) studying how to capture provenance on-demand using instrumentation. Links to [publications](http://www.cs.iit.edu/~dbgroup/publications) and more research oriented descriptions of the techniques implemented in GProM can be found at [http://www.cs.iit.edu/~dbgroup/research](http://www.cs.iit.edu/~dbgroup/research).
-->
