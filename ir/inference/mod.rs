/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

/*
Affect of clause statements on inferred types from parent variables:

1. Conjunction: intersection over types
2. Disjunction: union over types
3. Optional: no effect (consider match $x isa person; try { $x has dob $dob; };)
4. Negation: no effect (advanced: subtraction over types when unspecialised: match $x isa person; not { $x isa child; }. However, unsafe in: match $x isa person; not { $x isa child, has name "bob"; }



---> can we come up with a general, nestable algorithm for handling negations being nested? Eg. effect of  a Disjunction(Negation(Disjunction(Conjunction(negation)))))....
Or even:
conjunction(disjunction(conjunction or conjunction))



match
$x isa person;
{ $x has name "john"; } or { $x has bday bill;}

=> actually, disjunctions compute a possibility space via unions across branches, then intersect that with parent.
=> it's a "contextual" operation - have to compute within a pattern, then apply it


Execution idea:
Add all variables to frontier, and add all types in category to its set.
Pick a variable.
For each constraint attached, addOrIntersect types possible for the neighbor variable, add var to frontier
Repeat for each variable in frontier.


Want: good error messages when impossibility arises:

match
$x isa person;
$y isa company;
($x, $y) isa friendship;

Error:
Given:
$x is any of [person, child, adult]
($x, $y) is any of [friendship, child-friendship]
Then $y is not satisfiable


Algorithm:
when we find an empty answer for a variable, we go back through its neighbors and build the stack
in reverse, through named variables.

We should assign a search order over variables, based on connectedness.
On error, show the inferred types for variables (in minimal original query format, either named or ($x, $y))
In the order that are connected to the variable.
 */

mod pattern_type_inference;
mod seed_types;
mod type_inference;
mod value_type_inference;
