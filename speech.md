# Finite sets using lists

In the functional programming language provided to describe algorithms in Coq, there is a data structure to represent ordered collections of objects.  It is known as lists.  This data structure is not loaded by default, to use it, we need to start the development with the following directive:
`Require Import List.`
## A discussion of the syntax for lists
The list that contains the elements `1` `2` and `3` in that order will be represented by the following code.
`1 :: 2 :: 3 :: nil`
This notation makes use of the infix operation `::`, which separates the first element from the rest of the list.  In turn, the rest of the list also uses `::` to separate its own first element from its rest, and so on.  In effect, the list with three elements has the following structure.
`1 :: (2 :: (3 :: nil))`
So `1` is the first sub-component, and `2 :: 3 :: nil` is the second sub-component of the main list.
The expression `3 :: nil` represents a list with only one element, and `nil` represents the empty list.
## Representing sets using lists
If we need to represent finite sets in a program, we can do so by relying on lists.  The empty list, `nil`, represents the empty set.  If `l` represents a set `s`, then `a :: l` represents the union of `s` and `{a}`.

This representation is not perfect, because several different lists can represent the same set.  For instance, `1 :: 2 :: 1 :: nil` and `2 :: 1 :: nil` represent the set that contains exactly `1` and `2`.  Depending of the programming context, this may or may not be an important issue.
For instance, it may be that we only need to detect when some value has already been seen.  In that case, a membership function can be written, which traverses the list representing the set of seen values and returns true as soon as the value is detected.  In that case, a naive implementation of sets using lists may be practical.
In other instances, one may need objects representing finite sets and an operation to compare two such objects for equality or inclusion.  In this case, it may be useful to maintain invariant properties that guarantee that one only one list can be used to represent each set.
In a first experiment, we will only look at a naive implementation where only basic operations are provided, with no attention to the speed of operations.
## Checking if an element is in a set
For this initial experiment, we will assume that we are interested in sets of integers.  These numbers are available in Coq if we start our development with the following lines:
`Require Import ZArith.`
`Open Scope Z_scope.`
Integers are positive or negative and unbounded.  They come with a comparison function `_ =? _`, which we can illustrate in the following way:
`Compute 12345678 =? 2345678`.

The answer of the Coq system is `false`, for obvious reasons.
To check whether a given integer is element of the set represented by a list, we can simply compare this number with all the elements of the list one after the other.  This is done with the following definition.
<pre>
Fixpoint mem (x : Z) (l : list Z) : bool :=
  match l with
    nil => false
  | y :: tl => if x =? y then true else mem x tl
  end.
</pre>