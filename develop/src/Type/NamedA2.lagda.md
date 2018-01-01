
```agda
module Type.NamedA2 where

open import Type.Prelude
```

```agda
open import Type.A2
open import Type.NamedExpression

private

  _ = Set
  pattern [[_]] A = [ [] ↦ A ]
  pattern [[_//_]] x A = [ x ∷ [] ↦ A ]
  pattern [[_,_//_]] x y A = [ x ∷ y ∷ [] ↦ A ]
  pattern [[_,_,_//_]] x y z A = [ x ∷ y ∷ z ∷ [] ↦ A ]

pattern Πf A x B         = 𝓉 #ΠF  ([[ A ]] ∷ [[ x // B ]] ∷ [])
pattern Πi A x b         = 𝓉 #ΠI  ([[ A ]] ∷ [[ x // b ]] ∷ [])
pattern Πe f x           = 𝓉 #ΠE  ([[ f ]] ∷ [[ x ]] ∷ [])

pattern Σf A x B         = 𝓉 #ΣF  ([[ A ]] ∷ [[ x // B ]] ∷ [])
pattern Σi a b           = 𝓉 #ΣI  ([[ a ]] ∷ [[ b ]] ∷ [])
pattern Σe z C x y g e   = 𝓉 #ΣE  ([[ z // C ]] ∷ [[ x , y // g ]] ∷ [[ e ]] ∷ [])

pattern +f A B           = 𝓉 #+F  ([[ A ]] ∷ [[ B ]] ∷ [])
pattern +iˡ a            = 𝓉 #+Iˡ ([[ a ]] ∷ [])
pattern +iʳ b            = 𝓉 #+Iʳ ([[ b ]] ∷ [])
pattern +e z C x a y b e = 𝓉 #+E  ([[ z // C ]] ∷ [[ x // a ]] ∷ [[ y // b ]] ∷ [[ e ]] ∷ [])

pattern 𝟘f               = 𝓉 #𝟘F  []
pattern 𝟘e z C e         = 𝓉 #𝟘E  ([[ z // C ]] ∷ [[ e ]] ∷ [])

pattern 𝟙f               = 𝓉 #𝟙F  []
pattern 𝟙i               = 𝓉 #𝟙I  []
pattern 𝟙e z C c x       = 𝓉 #𝟙E  ([[ z // C ]] ∷ [[ c ]] ∷ [[ x ]] ∷ [])

pattern ℕf                 = 𝓉 #ℕF  []
pattern ℕiᶻ                = 𝓉 #ℕIᶻ []
pattern ℕiˢ n              = 𝓉 #ℕIˢ ([[ n ]] ∷ [])
pattern ℕe z C cᶻ x y cˢ n = 𝓉 #ℕE  ([[ z // C ]] ∷ [[ cᶻ ]] ∷ [[ x , y // cˢ ]] ∷ [[ n ]] ∷ [])

pattern =f A a b     = 𝓉 #=F ([[ A ]] ∷ [[ a ]] ∷ [[ b ]] ∷ [])
pattern =i a         = 𝓉 #=I ([[ a ]] ∷ [])
pattern =e x y p C z c⁼ v₁ v₂ v⁼ = 𝓉 #=E ([[ x , y , p // C ]] ∷ [[ z // c⁼ ]] ∷ [[ v₁ ]] ∷ [[ v₂ ]] ∷ [[ v⁼ ]] ∷ [])
```
