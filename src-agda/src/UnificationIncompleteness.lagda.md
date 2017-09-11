```agda
{-# OPTIONS --allow-unsolved-metas #-}
```

failure to solve b/c undecidable? custom meta solvers?

The below code type-checks if the hole is filled with `x1`. I believe that this is the unique solution (which Agda fails to solve).

```agda
postulate
  A : Set
  f : (B : A → Set) (x : A) → B x → B x
  x0 : A

test : (B : A → Set) (x : A) → B x → B x
test B1 x1 bx1 = f (λ x2 → B1 {!x1!}) x0 bx1
```

`show-constraints` reports:

    ?0 := _10 x1 x2
    _13 := λ B1 x1 bx1 → f (λ x2 → B1 (_10 x1 x2)) x0 (_12 B1 x1 bx1) [blocked by problem 19]
    [19,20] (_10 x1 x0) = x1 : A
    _11 := λ B1 x1 bx1 → bx1 [blocked by problem 17]
    [17,18] x1 = (_10 x1 x0) : A

I'm surprised that the constraint `_10 x1 x0 = x1` does not lead to the unique solution `_10 := λ x1 x0 → x1`. Taking a look at the debug output, I gather that Agda's failure to solve has something to do with metas being "frozen" and/or a failure to "prune" (though I don't know what that all means).

* Am I right that there is a unique solution which Agda is failing to find?

* I'm guessing that problems like this are the inevitable result of undecidability. Is that right? And so it's not a bug? And so I shouldn't bother reporting such things?

* Is the constraint-solver written-up somewhere separately from the code? With explanations of "pruning" and "freezing", etc.?

* Barring a fix, I'm hunting for possible workarounds. The notion of a "custom meta solver" is mentioned in Agda issue #2513. I take it that that refers to a possible enhancement somewhere down the road for Agda. Roughly speaking, how would that work? Would that allow an Agda programmer to "hook-in" to the built-in solver and then nudge it towards finding the unique solution to the above? Or is the idea instead to allow only for solvers that are implemented completely separately from the existing machinery?

UPDATE

Ulf replies:

> I'm surprised that the constraint `_10 x1 x0 = x1` does not lead to the unique solution `_10 := λ x1 x0 → x1`.

The reason for this is that x0 is not a variable but a postulate. You get the expected solution if you change the code to

{- ```agda -}
postulate
  A : Set
  f : (B : A → Set) (x : A) → B x → B x

module _ (x0 : A) where

  test : (B : A → Set) (x : A) → B x → B x
  test B1 x1 bx1 = f (λ x2 → B1 {!x1!}) x0 bx1
{- ``` -}

The idea for custom solvers would be to let you program them with the reflection machinery. Currently it doesn't let you access unsolved constraints, but that would be a reasonable extension to add.
