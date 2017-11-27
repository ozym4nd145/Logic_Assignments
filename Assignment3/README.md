# Assingment 3 - First Order Resolution

In this assignment I have implemented the resolution method as follows:
* The algorithm first converts the given formula to PCNF form and then skolemizes it.
* After that it converts the formula to the set notation (where the formula is a set of clauses)
* Then it tries to find two clause such that it is possible to unify a positive and negative predicate on them
* Then it find such an m.g.u and applies it to the resolvent and adds this clause to the clause set and removes the selected clauses.
* This is continued till we can't proceed or we derive an empty clause.
