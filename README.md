### Background
Boolean functions can written as an boolean expression like e.g. _A and B or B and C and not A_. Here the variables are boolean. Methods to _minimize_ these _expressions_ are [Quine-McCluskey](https://en.wikipedia.org/wiki/Quine%E2%80%93McCluskey_algorithm) and [Petrick's Method](https://en.wikipedia.org/wiki/Petrick%27s_method)
As expression become large the _complexity_ of these algorithms growth rapidly, in fact one step of the method is equivalent to _NP-hard_ set covering problem.


Also "A<3 and B>=1 or A=1 and C>=2" is a _logical expression_, but the variables are now _multivalued_ and we need to define their range. 

### This algorithm
_extends_ the Quine-McCluskey method to also _minimize_ expression of _multivalued logic_ as _A<3 and B>=1 or A=1 and C>=2_.
To this end the multivalued variables are _represented_ by several _boolean variables_ and their _interdependecies_. When the minimization on these boolean cases are carried out, the interdependencies need to be handled. This happens in the _creation of prime implicants_. The _reduction of prime implicants_ to minimal cover stays the same. A devide and conquer approach is used to improve runtime for reducing prime cover.

Apart from Quine-McClusky extension and implementation, Logicfun class has helper methods to read, write, random generate multivalued expressions.