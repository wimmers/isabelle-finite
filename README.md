Intro
-----
This project provides two **Eisbach** proof methods for better automated reasoning about finiteness
of sets in **Isabelle/HOL**. Code and examples are contained in the single theory file `Finiteness.thy`.
Moreover, generalizations of the theorem `setcompr_eq_image` are provided.

The file `Tutorial.thy` contains a number of general hints on reasoning about finiteness in Isabelle/HOL.

The file `Reordering_Quantifiers.thy` attempts to provide a number of fine-grained reasoning
tactics that can help to solve complex finiteness goals with manual support.
Moreover, generalizations of the theorem `finite_Collect_bounded_ex` are provided.

Usage
------
On Isabelle 2020, simply import the file to use any of the methods. The attribute
`finite` can be used to declare more intro methods.

License
-------
This work is released under the BSD license. See `LICENSE.md`.

More detailed description of the provided methods
-------------------------------------------------
The first method is intended to act more conservatively (think *safe*), leaving subgoals
for the user where it couldn't proceed any further.
The second method is more powerful, acting more in a succeed-or-die manner,
similarly to *force* and friends.
The examples in the second section should give a good impression of where these methods
can help.

TODO
----
* Extend scope to finiteness of sets of functions like in the last example