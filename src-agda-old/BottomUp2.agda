
record R (A : Set) : Set where field giveA : A
open R ⦃ … ⦄

record WrapR (A : Set) : Set where field instance ⦃ wrappedR ⦄ : R A
open WrapR ⦃ … ⦄

postulate
  instance R-instance : ∀ {X} → WrapR X

data D : Set where

works : D
works = giveA ⦃ WrapR.wrappedR (R-instance {D}) ⦄

fails : D
fails = giveA ⦃ {!!} ⦄
-- No instance of type R D was found in scope.


-- open import Agda.Primitive


-- {-
-- record IsBottom₀ (⊥ : Set) : Set (lsuc lzero) where
--   field
--     ⊥₀-elim : ⊥ → {A : Set lzero} → A

-- open IsBottom₀ ⦃ … ⦄ public

-- record Bottom₀ : Set (lsuc lzero) where
--   field
--     ⊥₀ : Set
--     ⦃ isBottom ⦄ : IsBottom₀ ⊥₀

-- open Bottom₀ ⦃ … ⦄ public

-- test : ⦃ bottom : ∀ {l : Set} → Bottom₀ ⦄ {fake : ⊥₀ ⦃ bottom {Level} ⦄} {real : Set} → real
-- test ⦃ bottom ⦄ {fake} {real} = ⊥₀-elim {⊥₀ ⦃ bottom ⦄} ⦃ Bottom₀.isBottom (bottom {Level}) ⦄ fake
-- -}

-- record IsBottom₀ (⊥ : Set) a : Set (lsuc a) where
--   field
--     ⊥₀-elim : ⊥ → {A : Set a} → A

-- open IsBottom₀ ⦃ … ⦄ public

-- record Bottom₀ a : Set (lsuc a) where
--   field
--     ⊥₀ : Set
--     ⦃ isBottom ⦄ : IsBottom₀ ⊥₀ a

-- open Bottom₀ ⦃ … ⦄ public

-- postulate
--   instance Bi : ∀ {a} → Bottom₀ a

-- --test : ⦃ bottom : ∀ {a} → Bottom₀ a ⦄ {fake : ⊥₀ {lzero}} {real : Set} → real
-- --test ⦃ bottom ⦄ {fake} {real} = let instance b = Bottom₀.isBottom (bottom {lzero}) in ⊥₀-elim {⊥₀ {lzero} ⦃ bottom ⦄} {lzero} ⦃ {!Bottom₀.isBottom bottom!} ⦄ fake

-- test : {fake : ⊥₀ {lzero}} {real : Set} → real
-- test {fake} {real} = ⊥₀-elim {⊥₀ {lzero} ⦃ Bi ⦄} {lzero} ⦃ Bottom₀.isBottom Bi ⦄ fake



-- -- record Bottom₀ a : Set (lsuc a) where
-- --   field
-- --     ⊥₀ : Set
-- --     ⊥₀-elim : ⊥₀ → {A : Set a} → A

-- -- open Bottom₀ ⦃ … ⦄ public

-- -- test : ⦃ bottom : ∀ {a} → Bottom₀ a ⦄ {fake : ⊥₀ {lzero}} {real : Set} → real
-- -- test ⦃ bottom ⦄ {fake} {real} = ⊥₀-elim fake -- ⊥₀-elim {⊥₀ {lzero} ⦃ bottom ⦄} {lzero} ⦃ bottom ⦄ fake

-- -- postulate
-- --   B : Set

-- -- record IsB (r : Set) a : Set (lsuc a) where
-- --   field
-- --     gotB : B
-- --     xx : r

-- -- open IsB ⦃ … ⦄ public

-- -- record RB a : Set (lsuc a) where
-- --   field
-- --     r : Set
-- --     ⦃ isB ⦄ : IsB r a

-- -- open RB ⦃ … ⦄ public

-- -- testB : ⦃ bottom : ∀ {a} → RB a ⦄ → B
-- -- testB ⦃ bottom ⦄ = gotB ⦃ {!isB bottom {lzero}!} ⦄
