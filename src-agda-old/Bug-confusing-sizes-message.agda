{-

--{-# OPTIONS --allow-unsolved-metas #-}
--{-# OPTIONS -v 100 #-}

{- Yellow highlighting should be accompanied by an error message -}

{- By default, command-line agda reports "unsolved metas" and gives a source-code location, but no information about the nature of the unsolved metas. (Emacs agda gives only yellow-highlighting.). With  Without increasing verbosity (via "-v 100")  -}
postulate
  yellow-highlighting-but-no-error-message : Set _

{- --allow-unsolved-metas -}
{-
Running from the command-line, agda reports that there are unsolved metas but doesn't say anything about what they are. Is there a way to increase verbosity about the unsolved metas?
-}

postulate
  error-message-but-no-link-to-source-code-location : _ _
-}
postulate
  Σ : (A : Set) (B : A → Set) → Set
  X : Set

confusing-message--not-empty-type-of-sizes : Σ _ λ x → X
confusing-message--not-empty-type-of-sizes = {!!}
