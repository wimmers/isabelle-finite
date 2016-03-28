-----
Intro
-----
This project provides two Eisbach proof methods for better automated reasoning about finiteness
of sets. Code and examples are contained in the single theory file Finiteness.thy.

------
Usage
------
On Isabelle 2016, simply import the file to use any of the methods. The attribute
finite can be used to declare more intro methods.

-------------------------------------------------
More detailed description of the provided methods
-------------------------------------------------
The first method is intended to act more conservatively (think \<open>safe\<close>), leaving subgoals
for the user where it couldn't proceed any further.
The second method is more powerful, acting more in a succeed-or-die manner,
similarly to \<open>force\<close> and friends.
The examples in the second section should give a good impression of where these methods
can help.