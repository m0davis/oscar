
```agda
module Type.DeBruijnA2 where

open import Type.Prelude
```

```agda
open import Type.A2
open import Type.DeBruijnExpression

pattern Πf A B       = 𝓉 ΠF  (A ∷ B ∷ [])
pattern Πi A b       = 𝓉 ΠI  (A ∷ b ∷ [])
pattern Πe f x       = 𝓉 ΠE  (f ∷ x ∷ [])

pattern Σf A B       = 𝓉 ΣF  (A ∷ B ∷ [])
pattern Σi a b       = 𝓉 ΣI  (a ∷ b ∷ [])
pattern Σe C g x     = 𝓉 ΣE  (C ∷ g ∷ x ∷ [])

pattern +f A B       = 𝓉 +F  (A ∷ B ∷ [])
pattern +iˡ a        = 𝓉 +Iˡ (a ∷ [])
pattern +iʳ b        = 𝓉 +Iʳ (b ∷ [])
pattern +e C l r x   = 𝓉 +E  (C ∷ l ∷ r ∷ x ∷ [])

pattern 𝟘f           = 𝓉 𝟘F  []
pattern 𝟘e C x       = 𝓉 𝟘E  (C ∷ x ∷ [])

pattern 𝟙f           = 𝓉 𝟙F  []
pattern 𝟙i           = 𝓉 𝟙I  []
pattern 𝟙e C g x     = 𝓉 𝟙E  (C ∷ g ∷ x ∷ [])

pattern ℕf           = 𝓉 ℕF  []
pattern ℕiᶻ          = 𝓉 ℕIᶻ []
pattern ℕiˢ n        = 𝓉 ℕIˢ (n ∷ [])
pattern ℕe C cᶻ cˢ x = 𝓉 ℕE  (C ∷ cᶻ ∷ cˢ ∷ x ∷ [])

pattern =f A a b     = 𝓉 =F (A ∷ a ∷ b ∷ [])
pattern =i a         = 𝓉 =I (a ∷ [])
pattern =e C c a b p = 𝓉 =E (C ∷ c ∷ a ∷ b ∷ p ∷ [])
```
