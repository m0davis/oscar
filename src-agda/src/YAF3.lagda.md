
```agda

open import Prelude

∃_ : ∀ {a b} {A : Set a} (B : A → Set b) → Set (a ⊔ b)
∃_ = Σ _

data IsYes {a} {P : Set a} : Dec P → Set a where
  yes : (p : P) → IsYes (yes p)

getProof : ∀ {a} {P : Set a} → {d : Dec P} → IsYes d → P
getProof (yes p) = p

record I {A B : Set} (F : A → B → Set) : Set where
  field
    listen : (x : A) → ∃ F x
    speak : (y : B) → ∃ λ x → ∃ λ (f : F x y) → listen x ≡ (y , f)
  paraphrase : A → A
  paraphrase x = fst (speak (fst (listen x)))
  paraphrase-is-fixed-point : (x : A) → paraphrase (paraphrase x) ≡ paraphrase x
  paraphrase-is-fixed-point x with
                                listen x | speak (fst (listen x)) | listen (fst (speak (fst (listen x)))) | speak (fst (listen (fst (speak (fst (listen x))))))
  paraphrase-is-fixed-point x | y , fxy  | x' , fx'y , x'=>y,fx'y | y' , fx'y'                            | x'' , fx''y' , x''=>y',fx''y' = {!!}

record J {A B : Set} : Set where
  field
    listen : A → B
    speak : (y : B) → ∃ λ x → listen x ≡ y
  paraphrase : A → A
  paraphrase x = fst (speak (listen x))
  paraphrase-is-fixed-point : (x : A) → paraphrase (paraphrase x) ≡ paraphrase x
  paraphrase-is-fixed-point x with
      listen x | speak (listen x) | graphAt speak (listen x)
  … | y        | x' , refl        | ingraph eq2 =
    cong fst eq2

  paraphrase-is-fixed-point' : (x : A) → paraphrase (paraphrase x) ≡ paraphrase x
  paraphrase-is-fixed-point' x with
      speak (listen x) | graphAt speak (listen x)
  … | x' , refl'       | ingraph eq2 =
    transport (λ v → fst (speak v) ≡ x') (sym refl') (cong fst eq2)

{-
  listen x = y
  speak y = x' , (_ : listen x' = y)
  listen x' = y'


  -- speak y = x' , _
  listen x' = y
  listen x' = y'
  speak y' = x'' , _
-}

record Interpreter {source : Set} {target : Set} (translation : source → target → Set) : Set where

  field
    interpret : (s : source) → Dec $ ∃ translation s -- possibly generate a translation into the target language (or show that no translation is possible)
    restate : (t : target) → ∃ λ s → ∃ λ (r : translation s t) → interpret s ≡ yes (t , r) -- for any statement from the target language, there's a statement in the source that is interpreted as the original statement in the target language.

    translation-is-functional : ∀ s t1 t2 → translation s t1 → translation s t2 → t1 ≡ t2 -- no ambiguities: multiple interpretations are not possible -- we could say that translation is "functional". Maybe this somehow calls for a separate record type. Alternatively, we could allow for ambiguity and place this into the definition of `interpret`
    translation-is-parsimonious : ∀ s t (r1 r2 : translation s t) → r1 ≡ r2 -- parsimony: there is but one way of translating a given source into a given target -- maybe this isn't something we want?

  paraphrase : (s : source) → IsYes (interpret s) → source
  paraphrase s i = fst ∘ restate ∘ fst $ getProof i

  -- paraphrase is a fixed-point if there is an interpretation
  field paraphrase-is-fixed-point : (s : source) → (i : IsYes (interpret s)) → ∃ λ i' → paraphrase (paraphrase s i) i' ≡ paraphrase s i

  paraphrase-is-fixed-point' : (s : source) → (i : IsYes (interpret s)) → ∃ λ i' → paraphrase (paraphrase s i) i' ≡ paraphrase s i
  paraphrase-is-fixed-point' s i with interpret s
  paraphrase-is-fixed-point' s (yes (t , r)) | _ with restate t | interpret (fst (restate t))
  paraphrase-is-fixed-point' s (yes (t , r)) | .(yes (t , r)) | fst₁ , fst₂ , snd₁ | yes (fst₃ , snd₂) = {!!}
  paraphrase-is-fixed-point' s (yes (t , r)) | .(yes (t , r)) | fst₁ , fst₂ , snd₁ | no x = {!!}
  {-
  paraphrase-is-fixed-point' s i with interpret s
  paraphrase-is-fixed-point' s (yes (t , r)) | _   with restate t    | getProof (fst (snd (restate t))) | graphAt getProof (fst (snd (restate t))) | interpret (fst (restate t))
  paraphrase-is-fixed-point' s (yes (t , r)) | .(yes (t , r)) | s' , i' , r' , pi' | .(getProof i') | ingraph refl | yes (t' , r'') = {!!} -- yes _ , {!!}
  paraphrase-is-fixed-point' s (yes (t , r)) | _ | s' , i' , r' , pi' | gp | g | no _ = {!!}
  -}
  {-
  paraphrase-is-fixed-point' s (yes (t , r)) | _ with restate t | graphAt restate t | interpret (fst (restate t)) | graphAt interpret (fst (restate t))
  paraphrase-is-fixed-point' s (yes (t , r)) | .(yes (t , r)) | s' , i' , r' , gp | ingraph eq1 | yes (fst₁ , snd₁) | ingraph eq2 = yes _ , {!!}
  paraphrase-is-fixed-point' s (yes (t , r)) | .(yes (t , r)) | s' , i' , r' , gp | ingraph eq1 | no x | ingraph eq2 = {!!}
  -}


  {-
  paraphrase-is-fixed-point' s i with interpret s | graphAt interpret s | paraphrase s i | graphAt (paraphrase s) i
  … | is | ga | pp | gap = ?
  -}
  {-
  paraphrase-is-fixed-point' s i with interpret s | paraphrase s i | graphAt (paraphrase s) i
  paraphrase-is-fixed-point' s i | i' | pp | ingraph x with interpret pp
  paraphrase-is-fixed-point' s i | i' | pp | ingraph x | yes (t , r) = {!!}
  paraphrase-is-fixed-point' s i | i' | pp | ingraph x | no x₁ = {!!}
  -}
  {-
  paraphrase-is-fixed-point' s i               with interpret s
  paraphrase-is-fixed-point' s (yes (t , r)) | _   with restate t | graphAt restate t | interpret (fst (restate t))
  paraphrase-is-fixed-point' s (yes (t , r)) | .(yes (t , r)) | s' , i , r' , gp | ingraph eq | yes x = {!x!}
  paraphrase-is-fixed-point' s (yes (t , r)) | .(yes (t , r)) | s' , i , r' , gp | ingraph eq | no x = {!!}
  -}
  -- … | ii | rr = ?
  {-
  paraphrase-is-fixed-point' s (yes (t , r)) | _ | s' , yes .(t , r') , r' , refl | ingraph eq | .(yes (t , r')) | s'' , i'' , r'' , gp'' with interpret s'' | restate t -- | paraphrase-is-fixed-point' s' ?
  paraphrase-is-fixed-point' s (yes (t , r)) | _ | s' , yes .(t , r') , r' , refl | ingraph eq | .(yes (t , r')) | s'' , yes .(t , r'') , r'' , refl | yes .(t , r'') | fst₁ , fst₂ , fst₃ , snd₁ = yes _ , {!!}
  -}
```
