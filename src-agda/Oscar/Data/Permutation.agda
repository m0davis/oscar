
module Oscar.Data.Permutation where

--open import Data.Permutation public
import Data.Permutation as P
open import Data.Permutation renaming (delete to deleteP; _∘_ to _∘P_; enum to allInj)

open import Oscar.Data.Vec renaming (delete to deleteV; map to mapV)


open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Fin

open ≡-Reasoning

open import Data.Permutation.Properties

open import Oscar.Data.Vec.Properties
open import Function

open import Data.Sum
open import Agda.Builtin.Nat

<>-inv : ∀ {n} (ps : Permutation n) i → i ≡ < ps > (< ps ⁻¹ > i)
<>-inv ps i =
  trans
    (sym (id-is-id i))
    (subst (< P.id > _ ≡_)
           (inj-correct (ps ⁻¹) ps i)
           (cong (flip <_> _)
                 (sym (inv-left ps))))

_≞_÷_ : ∀ {a n} {A : Set a} → Vec A n → Vec A n → Permutation n → Set a
x ≞ px ÷ p = ∀ i → lookup i px ≡ lookup (< p > i) x

lookup-ext : ∀ {a n} {A : Set a} {pv₁ pv₂ : Vec A n} → (∀ i → lookup i pv₁ ≡ lookup i pv₂) → pv₁ ≡ pv₂
lookup-ext {pv₁ = []} {[]} x = refl
lookup-ext {pv₁ = x₁ ∷ pv₁} {x₂ ∷ pv₂} x with lookup-ext {pv₁ = pv₁} {pv₂} (x ∘ suc) | x zero
… | refl | refl = refl

permuted-inj : ∀ {a n} {A : Set a} {v : Vec A n} {pv₁ pv₂ : Vec A n} {p : Permutation n} → v ≞ pv₁ ÷ p → v ≞ pv₂ ÷ p → pv₁ ≡ pv₂
permuted-inj {pv₁ = pv₁} {pv₂} v≞pv₁÷p v≞pv₂÷p = lookup-ext foo where
  foo : (i : Fin _) → lookup i pv₁ ≡ lookup i pv₂
  foo i = trans (v≞pv₁÷p i) (sym (v≞pv₂÷p i))

permutedLookup : ∀ {a n} {A : Set a} → Permutation n → Vec A n → Fin n → A
permutedLookup p v = flip lookup v ∘ < p >

permute : ∀ {a n} {A : Set a} → (p : Permutation n) → (v : Vec A n) → Vec A n
permute p v = tabulate (flip lookup v ∘ < p >)

permute-correct : ∀ {a n} {A : Set a} → (p : Permutation n) → (v : Vec A n) →
                  v ≞ permute p v ÷ p
permute-correct p v = lookup∘tabulate (flip lookup v ∘ < p >)

Permute : ∀ {a n} {A : Set a} → (p : Permutation n) → (v : Vec A n) →
          ∃ (v ≞_÷ p)
Permute p v = permute p v , permute-correct p v

_≞_÷? : ∀ {a n} {A : Set a} → Vec A n → Vec A n → Set a
_≞_÷? x px = ∃ (x ≞ px ÷_)

∈-allInj : ∀ {n m} (i : Inj n m) → i ∈ allInj n m
∈-allInj {zero} [] = here
∈-allInj {suc n} (i ∷ is) = ∈-map₂ _∷_ (∈-allFin i) (∈-allInj is)

tabulate₂ : ∀ {n m a} {A : Set a} → (Inj n m → A) → Vec A (size n m)
tabulate₂ f = mapV f (allInj _ _)

∈-tabulate₂ : ∀ {n m a} {A : Set a} (f : Inj n m → A) i → f i ∈ tabulate₂ f
∈-tabulate₂ f i = ∈-map f (∈-allInj i)

ENUM₂ : ∀ {a n} {A : Set a} → (v : Vec A n) → Vec (∃ (v ≞_÷?)) (size n n)
ENUM₂ v = tabulate₂ (λ p → permute p v , p , permute-correct p v)

enum₂ : ∀ {a n} {A : Set a} → Vec A n → Vec (Vec A n) (size n n)
enum₂ v = tabulate₂ (flip permute v)

enum₂-sound : ∀ {a} {A : Set a} {n} (x px : Vec A n) → px ∈ enum₂ x → x ≞ px ÷?
enum₂-sound x _ px∈enum₂x with map-∈ px∈enum₂x
enum₂-sound x _ _ | p , refl = p , permute-correct p x

remove-÷-zero : ∀ {n a} {A : Set a} {x : A} {xs : Vec A n} {px : A}
                  {pxs : Vec A n} {ps : Inj n n} →
                (x ∷ xs) ≞ px ∷ pxs ÷ (zero ∷ ps) →
                xs ≞ pxs ÷ ps
remove-÷-zero f i = f (suc i)

enum₂-complete : ∀ {a} {A : Set a} {n} (x px : Vec A n) → x ≞ px ÷? → px ∈ enum₂ x
enum₂-complete x px (p , x≞px÷p) = proof where
  p∈allInj : p ∈ allInj _ _
  p∈allInj = ∈-allInj p
  permutepx∈enum₂x : permute p x ∈ enum₂ x
  permutepx∈enum₂x = ∈-map (flip permute x) p∈allInj
  x≞permutepx÷p : x ≞ permute p x ÷ p
  x≞permutepx÷p = permute-correct p x
  proof : px ∈ enum₂ x
  proof = subst (_∈ _) (permuted-inj {p = p} x≞permutepx÷p x≞px÷p) permutepx∈enum₂x

Enum₂ : ∀ {a n} {A : Set a} → (x : Vec A n) → Σ[ pxs ∈ Vec (Vec A n) (size n n) ] (∀ px → (px ∈ pxs → x ≞ px ÷?) × (x ≞ px ÷? → px ∈ pxs))
Enum₂ x = enum₂ x , (λ px → enum₂-sound x px , enum₂-complete x px)

_∃⊎∀_ : ∀ {a} {A : Set a} {l r} (L : A → Set l) (R : A → Set r) {p} (P : A → Set p) → Set _
(L ∃⊎∀ R) P = (∃ λ x → P x × L x) ⊎ (∀ x → P x → R x)

open import Agda.Primitive

stepDecide∃⊎∀ : ∀ {a} {A : Set a} {l r} {L : A → Set l} {R : A → Set r} → (∀ y → L y ⊎ R y) → ∀ {p} (P : A → Set p) →
                ∀ {d} (done : Vec A d) {nd} (not-done : Vec A nd) →
                (∀ y → y ∈ done ⊎ y ∈ not-done → P y) →
                (∀ y → P y → y ∈ done ⊎ y ∈ not-done) →
                (∀ y → y ∈ done → R y) →
                (L ∃⊎∀ R) P
stepDecide∃⊎∀ dec P done {zero} not-done dnd-sound dnd-complete done-R = inj₂ (λ y Py → done-R y (dnd-done y Py)) where
  dnd-done : ∀ y → P y → y ∈ done
  dnd-done y Py with dnd-complete y Py
  dnd-done y Py | inj₁ y∈done = y∈done
  dnd-done y Py | inj₂ ()
stepDecide∃⊎∀ dec P done {suc nd} (step ∷ not-dones) dnd-sound dnd-complete done-R with dec step
… | inj₁ l = inj₁ (step , (dnd-sound step (inj₂ here)) , l)
… | inj₂ r = stepDecide∃⊎∀ dec P (step ∷ done) not-dones stepdnd-sound stepdnd-complete (stepdone-R r) where
  stepdnd-sound : ∀ y → y ∈ step ∷ done ⊎ y ∈ not-dones → P y
  stepdnd-sound _ (inj₁ here) = dnd-sound step (inj₂ here)
  stepdnd-sound y (inj₁ (there y∈done)) = dnd-sound y (inj₁ y∈done)
  stepdnd-sound y (inj₂ y∈not-dones) = dnd-sound y (inj₂ (there y∈not-dones))

  stepdnd-complete : ∀ y → P y → y ∈ step ∷ done ⊎ y ∈ not-dones
  stepdnd-complete y Py with dnd-complete y Py
  stepdnd-complete y Py | inj₁ y∈done = inj₁ (there y∈done)
  stepdnd-complete y Py | inj₂ here = inj₁ here
  stepdnd-complete y Py | inj₂ (there y∈not-dones) = inj₂ y∈not-dones

  stepdone-R : _ → ∀ y → y ∈ step ∷ done → _
  stepdone-R Rstep _ here = Rstep
  stepdone-R Rstep y (there y∈done) = done-R y y∈done

decide∃⊎∀ : ∀ {a} {A : Set a} {l r} {L : A → Set l} {R : A → Set r} → (∀ y → L y ⊎ R y) → ∀ {p} (P : A → Set p) →
            ∀ {nd} (not-done : Vec A nd) →
            (∀ y → y ∈ not-done → P y) →
            (∀ y → P y → y ∈ not-done) →
            (L ∃⊎∀ R) P
decide∃⊎∀ dec P not-done nd-sound nd-complete = stepDecide∃⊎∀ dec P [] not-done []nd-sound []nd-complete (λ {_ ()}) where
  []nd-sound : ∀ y → y ∈ [] ⊎ y ∈ not-done → P y
  []nd-sound y (inj₁ ())
  []nd-sound y (inj₂ y∈not-done) = nd-sound y y∈not-done

  []nd-complete : ∀ y → P y → y ∈ [] ⊎ y ∈ not-done
  []nd-complete y Py = inj₂ (nd-complete y Py)

decidePermutations : ∀ {a n} {A : Set a} {l r} {L : Vec A n → Set l} {R : Vec A n → Set r} → ∀ x → (∀ y → L y ⊎ R y) →
                     (L ∃⊎∀ R) (x ≞_÷?)
decidePermutations x f = decide∃⊎∀ f _ (enum₂ x) (enum₂-sound x) (enum₂-complete x)

-- -- sym-≞∣ : ∀ {a n} {A : Set a} → (y x : Vec A n) → (p : Permutation n) →
-- --          y ≞ x ∣ p → x ≞ y ∣ (p ⁻¹)
-- -- sym-≞∣ y x ps y≞x∣p i =
-- --   trans (cong (flip lookup x) {x = i} {y = < ps > (< ps ⁻¹ > i)} (<>-inv ps i)) (sym (y≞x∣p (< ps ⁻¹ > i)))

-- -- open import Oscar.Data.Vec.Properties

-- -- Permute : ∀ {a n} {A : Set a} → (p : Permutation n) → (v : Vec A n) →
-- --           ∃ λ w → w ≞ v ∥ p
-- -- Permute [] v = v , λ ()
-- -- Permute p@(p' ∷ ps) v@(v' ∷ vs) =
-- --   let ws , [vs≡ws]ps = Permute ps (deleteV p' v)
-- --       w = lookup p' v ∷ ws
-- --       [v≡w]p : w ≞ v ∥ p
-- --       [v≡w]p = {!!}
-- --       {-
-- --       [v≡w]p = λ
-- --         { zero → here
-- --         ; (suc f) → there (subst (ws [ f ]=_)
-- --                                  (lookup-delete-thin p' (< ps > f) v)
-- --                                  ([vs≡ws]ps f)) }
-- --       -}
-- --   in
-- --   w , [v≡w]p

-- -- -- permute : ∀ {a n} {A : Set a} → Permutation n → Vec A n → Vec A n
-- -- -- permute p v = proj₁ (Permute p v)

-- -- -- permute-correct : ∀ {a n} {A : Set a} → (p : Permutation n) → (v : Vec A n) → v ≞ permute p v ∥ p
-- -- -- permute-correct p v = proj₂ (Permute p v)

-- -- -- open import Function

-- -- -- --∈-map-proj₁ : mapV proj₁ (mapV (λ p → F p , G p) xs) ≡ mapV F xs
-- -- -- open import Data.Nat

-- -- -- ∈-enum : ∀ {n m} (i : Inj n m) → i ∈ enum n m
-- -- -- ∈-enum {zero} [] = here
-- -- -- ∈-enum {suc n} (i ∷ is) = ∈-map₂ _∷_ (∈-allFin i) (∈-enum is)

-- -- -- open import Data.Permutation.Properties

-- -- -- [thin]=→delete[]= : ∀ {a n} {A : Set a} {i j} {v : Vec A (suc n)} {x} → v [ thin i j ]= x → deleteV i v [ j ]= x
-- -- -- [thin]=→delete[]= {i = zero} {v = x ∷ v} (there x₂) = x₂
-- -- -- [thin]=→delete[]= {n = zero} {i = suc ()} x₁
-- -- -- [thin]=→delete[]= {n = suc n} {i = suc i} {zero} {x ∷ v} here = here
-- -- -- [thin]=→delete[]= {n = suc n} {i = suc i} {suc j} {x ∷ v} (there v[thinij]=?) = there ([thin]=→delete[]= {i = i} v[thinij]=?)

-- -- -- delete≡Permutation : ∀ {a n} {A : Set a} {v₀ : A} {v₊ : Vec A n} {w : Vec A (suc n)} {p : Permutation (suc n)} →
-- -- --                      (v₀ ∷ v₊) ≞ w ∥ p →
-- -- --                      v₊ ≞ deleteV (annihilator p) w ∥ delete (annihilator p) p
-- -- -- delete≡Permutation {v₀ = v₀} {v₊} {w} {p} [v₀∷v₊≡w]p f = [thin]=→delete[]= {i = annihilator p} {j = f} qux where
-- -- --   foo : thin (< p > (annihilator p)) (< delete (annihilator p) p > f) ≡ < p > (thin (annihilator p) f)
-- -- --   foo = inj-thin p (annihilator p) f

-- -- --   foo2 : suc (< delete (annihilator p) p > f) ≡ < p > (thin (annihilator p) f)
-- -- --   foo2 = subst (λ y → thin y (< delete (annihilator p) p > f) ≡ < p > (thin (annihilator p) f)) (ann-correct p) foo

-- -- --   bar : w [ thin (annihilator p) f ]= lookup (< p > (thin (annihilator p) f)) (v₀ ∷ v₊)
-- -- --   bar = [v₀∷v₊≡w]p (thin (annihilator p) f)

-- -- --   qux : w [ thin (annihilator p) f ]= lookup (< delete (annihilator p) p > f) v₊
-- -- --   qux = subst (λ y → w [ thin (annihilator p) f ]= lookup y (v₀ ∷ v₊)) (sym foo2) bar

-- -- -- permute-complete-step : ∀ {a n} {A : Set a} {v₀ : A} {w : Vec A (suc n)} {v₊ : Vec A n} (x : Fin (suc n)) →
-- -- --   w [ x ]= v₀ →
-- -- --   deleteV x w ∈ mapV (flip permute v₊) (enum n n) →
-- -- --   w ∈ mapV (flip permute (v₀ ∷ v₊)) (enum (suc n) (suc n))
-- -- -- permute-complete-step {n = zero} {w = x₃ ∷ []} {[]} zero here here = here
-- -- -- permute-complete-step {n = zero} {w = x₃ ∷ []} {[]} zero x₁ (there ())
-- -- -- permute-complete-step {n = zero} {w = x₃ ∷ []} {[]} (suc ()) x₁ x₂
-- -- -- permute-complete-step {n = suc n} {w = w ∷ ws} x w∷ws[x]=v₀ x₂ = {!!}

-- -- -- permute-lemma : ∀ {a n} {A : Set a} (v w : Vec A n) (p : Permutation n) →
-- -- --   v ≞ w ∥ p →
-- -- --   w ≡ permute (p ⁻¹) v
-- -- -- permute-lemma v w p x = {!permute-correct p w!}

-- -- -- {-
-- -- -- permute-complete' : ∀ {a n} {A : Set a} (v w : Vec A n) (p : Permutation n) →
-- -- --   v ≞ w ∥ p →
-- -- --   ∀ {m} {ps : Vec (Permutation n) m} → p ∈ ps →
-- -- --   w ≡ permute p v
-- -- --   w ∈ mapV (flip
-- -- -- -}

-- -- -- permute-complete : ∀ {a n} {A : Set a} (v w : Vec A n) →
-- -- --            v ∃≡Permutation w →
-- -- --            w ∈ mapV (flip permute v) (enum n n)
-- -- -- permute-complete [] [] (p , [v≡w]p) = here
-- -- -- permute-complete {n = suc n} v@(v₀ ∷ v₊) w (p , [v≡w]p) = permute-complete-step (annihilator p) w[ap]=v₀ pc' where
-- -- --   w[ap]=v₀ : w [ annihilator p ]= v₀
-- -- --   w[ap]=v₀ = {![v≡w]p (annihilator p)!}
-- -- --   pc' : deleteV (annihilator p) w ∈ mapV (flip permute v₊) (enum n n)
-- -- --   pc' = permute-complete v₊ (deleteV (annihilator p) w) (delete (annihilator p) p , delete≡Permutation {p = p} [v≡w]p)

-- -- -- EnumPermutations : ∀ {a n} {A : Set a} → (v : Vec A n) →
-- -- --                    Σ (Vec (∃ (v ∃≡Permutation_)) (size n n)) λ ws
-- -- --                    → ∀ w → (v ∃≡Permutation w → w ∈ mapV proj₁ ws)
-- -- -- EnumPermutations {n = n} v = mapV (λ p → permute p v , p , permute-correct p v) (enum n n) , (λ w v∃≡Pw → subst (w ∈_) (map-∘ proj₁ (λ p → permute p v , p , permute-correct p v) (enum n n)) (permute-complete v w v∃≡Pw))

-- -- -- enumPermutations : ∀ {a n} {A : Set a} → Vec A n → Vec (Vec A n) (size n n)
-- -- -- enumPermutations {n = n} xs = mapV (λ p → permute p xs) (enum n n)

-- -- -- tryPermutations : ∀ {a n} {A : Set a} {l r} {L : Vec A n → Set l} {R : Vec A n → Set r} → ∀ x → (f : ∀ y → L y ⊎ R y) → Vec (∃ λ y → x ∃≡Permutation y × L y ⊎ R y) (size n n)
-- -- -- tryPermutations x f = mapV (λ x₁ → x₁ , {!!}) (enumPermutations x)
