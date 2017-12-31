
```agda
{-# OPTIONS --allow-unsolved-metas #-}
```

```agda
module Type.Term.Layer-1 where

open import Type.Prelude
```

## Generalised DeBruijn-indexed terms and contexts

```agda
-- open import Type.Term.Layer-1.Kernel public
import Type.Term.Layer-1.Kernel
```


```agda
private

  module Test where

    pattern ,_ s = _ ,, s

    myMeta : Vec (∃ Vec Nat) _
    myMeta =
      -- Π
      , (0 ∷ 1 ∷ []) ∷
      , (0 ∷ 1 ∷ []) ∷
      , (0 ∷ 0 ∷ []) ∷
      -- Σ
      , (0 ∷ 1 ∷ []) ∷
      , (0 ∷ 0 ∷ []) ∷
      , (1 ∷ 2 ∷ 0 ∷ []) ∷
      -- +
      []

    module _ where
      open import Type.Term.Layer-1.Kernel myMeta

      testExpression₁ : Expression 0
      testExpression₁ = 𝓉 0 (𝒰 0 ∷ 𝓋 0 ∷ [])

    module _ where
      open import Type.Term.Layer-1.Kernel

      -- pattern z = zero

      pattern ΠF x = 𝓉 zero x
      pattern ΠI x = 𝓉 (suc zero) x
      pattern ΠE f x = 𝓉 (suc (suc zero)) (f ∷ x ∷ [])
      pattern ΣF A B = 𝓉 3 (A ∷ B ∷ []) -- there's a problem with Agda assuming this 3 is a Nat (and not possibly a Fin)

      testExpression₁' : Expression myMeta 0
      testExpression₁' = ΠF (𝒰 0 ∷ 𝓋 0 ∷ [])

      testExpression₂ : Expression myMeta 0
      testExpression₂ = ΠI (𝒰 0 ∷ 𝓋 0 ∷ [])

      test₃ : Expression myMeta 2
      test₃ = ΠE (𝓋 0) (𝒰 17)

      test-fail-pattern : Expression myMeta 1
      test-fail-pattern = {!ΣF!}

      test-for-weakening : Expression myMeta 2
      test-for-weakening = ΠI ((𝓋 0) ∷ ((ΠE (𝓋 0) (𝓋 2)) ∷ []))

      test-weakening-0 : Expression myMeta 3
      test-weakening-0 = weakenExpressionFrom myMeta 0 test-for-weakening
```

## A particular implementation (for HoTT)

```agda
alphabet : Vec (∃ Vec Nat) _
alphabet =

  {- ΠF  -} (_ ,, (0 ∷ 1 ∷ [])             ) ∷
  {- ΠI  -} (_ ,, (0 ∷ 1 ∷ [])             ) ∷
  {- ΠE  -} (_ ,, (0 ∷ 0 ∷ [])             ) ∷

  {- ΣF  -} (_ ,, (0 ∷ 1 ∷ [])             ) ∷
  {- ΣI  -} (_ ,, (0 ∷ 0 ∷ [])             ) ∷
  {- ΣE  -} (_ ,, (1 ∷ 2 ∷ 0 ∷ [])         ) ∷

  {- +F  -} (_ ,, (0 ∷ 0 ∷ [])             ) ∷
  {- +Iˡ -} (_ ,, (0 ∷ [])                 ) ∷
  {- +Iʳ -} (_ ,, (0 ∷ [])                 ) ∷
  {- +E  -} (_ ,, (1 ∷ 1 ∷ 1 ∷ 0 ∷ [])     ) ∷

  {- 𝟘F  -} (_ ,, []                       ) ∷
  {- 𝟘E  -} (_ ,, (1 ∷ 0 ∷ [])             ) ∷

  {- 𝟙F  -} (_ ,, []                       ) ∷
  {- 𝟙I  -} (_ ,, []                       ) ∷
  {- 𝟙E  -} (_ ,, (1 ∷ 0 ∷ 0 ∷ [])         ) ∷

  {- ℕF  -} (_ ,, []                       ) ∷
  {- ℕIᶻ -} (_ ,, []                       ) ∷
  {- ℕIˢ -} (_ ,, (0 ∷ [])                 ) ∷
  {- ℕE  -} (_ ,, (1 ∷ 0 ∷ 2 ∷ 0 ∷ [])     ) ∷

  {- =F  -} (_ ,, (0 ∷ 0 ∷ 0 ∷ [])         ) ∷
  {- =I  -} (_ ,, (0 ∷ [])                 ) ∷
  {- =E  -} (_ ,, (3 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ []) ) ∷

  []

open import Type.Term.Layer-1.Kernel alphabet public
module K = Type.Term.Layer-1.Kernel

pattern #ΠF  = zero
pattern #ΠI  = suc #ΠF
pattern #ΠE  = suc #ΠI

pattern #ΣF  = suc #ΠE
pattern #ΣI  = suc #ΣF
pattern #ΣE  = suc #ΣI

pattern #+F  = suc #ΣE
pattern #+Iˡ = suc #+F
pattern #+Iʳ = suc #+Iˡ
pattern #+E  = suc #+Iʳ

pattern #𝟘F  = suc #+E
pattern #𝟘E  = suc #𝟘F

pattern #𝟙F  = suc #𝟘E
pattern #𝟙I  = suc #𝟙F
pattern #𝟙E  = suc #𝟙I

pattern #ℕF  = suc #𝟙E
pattern #ℕIᶻ = suc #ℕF
pattern #ℕIˢ = suc #ℕIᶻ
pattern #ℕE  = suc #ℕIˢ

pattern #=F  = suc #ℕE
pattern #=I  = suc #=F
pattern #=E  = suc #=I

pattern Πf A B       = K.𝓉 #ΠF  (A ∷ B ∷ [])
pattern Πi A b       = K.𝓉 #ΠI  (A ∷ b ∷ [])
pattern Πe f x       = K.𝓉 #ΠE  (f ∷ x ∷ [])

pattern Σf A B       = K.𝓉 #ΣF  (A ∷ B ∷ [])
pattern Σi a b       = K.𝓉 #ΣI  (a ∷ b ∷ [])
pattern Σe C g x     = K.𝓉 #ΣE  (C ∷ g ∷ x ∷ [])

pattern +f A B       = K.𝓉 #+F  (A ∷ B ∷ [])
pattern +iˡ a        = K.𝓉 #+Iˡ (a ∷ [])
pattern +iʳ b        = K.𝓉 #+Iʳ (b ∷ [])
pattern +e C l r x   = K.𝓉 #+E  (C ∷ l ∷ r ∷ x ∷ [])

pattern 𝟘f           = K.𝓉 #𝟘F  []
pattern 𝟘e C x       = K.𝓉 #𝟘E  (C ∷ x ∷ [])

pattern 𝟙f           = K.𝓉 #𝟙F  []
pattern 𝟙i           = K.𝓉 #𝟙I  []
pattern 𝟙e C g x     = K.𝓉 #𝟙E  (C ∷ g ∷ x ∷ [])

pattern ℕf           = K.𝓉 #ℕF  []
pattern ℕiᶻ          = K.𝓉 #ℕIᶻ []
pattern ℕiˢ n        = K.𝓉 #ℕIˢ (n ∷ [])
pattern ℕe C cᶻ cˢ x = K.𝓉 #ℕE  (C ∷ cᶻ ∷ cˢ ∷ x ∷ [])

pattern =f A a b     = K.𝓉 #=F (A ∷ a ∷ b ∷ [])
pattern =i a         = K.𝓉 #=I (a ∷ [])
pattern =e C c a b p = K.𝓉 #=E (C ∷ c ∷ a ∷ b ∷ p ∷ [])
```

## Historical reference

Here are some other attempts.

```agda
import Type.Term.Layer-1.SCTerm
```

```agda
import Type.Term.Layer-1.Formulaturez
import Type.Term.Layer-1.Formulaturenz
```
