{- In the below, I define an OrderedList and attempt to prove a lemma: that if every element in such a list is also in the empty list, then the list in question must be the empty list. I don't succeed, but I do come up with a number of QUESTIONs and COMPLAINTs. I hope my story will help inspire someone to write-up a comprehensive explanation of error messages in Agda. Or (better) to modify Agda so that error messages don't require so much explanation! :) I suspect that Issue 771 [https://github.com/agda/agda/issues/771] might pertain to some of my complaints. -}

open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

module Enagda05-need-more-help-from-agda
  {𝑼⟨Key⟩ 𝑼⟨Value⟩ 𝑼⟨<⟩}
  {Key : Set 𝑼⟨Key⟩} (Value : Key → Set 𝑼⟨Value⟩)
  {_<_ : Rel Key 𝑼⟨<⟩}
  (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_)
  where

open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Level using (_⊔_; Lift)

data Key⁺ : Set 𝑼⟨Key⟩ where
  ⊥⁺ ⊤⁺ : Key⁺
  [_]   : (k : Key) → Key⁺
  
infix 4 _<⁺_

_<⁺_ : Key⁺ → Key⁺ → Set 𝑼⟨<⟩
⊥⁺    <⁺ [ _ ] = Lift ⊤
⊥⁺    <⁺ ⊤⁺    = Lift ⊤
[ x ] <⁺ [ y ] = x < y
[ _ ] <⁺ ⊤⁺    = Lift ⊤
_     <⁺ _     = Lift ⊥
  
infixr 6 _∷_
data OrderedList (l u : Key⁺) : Set (𝑼⟨Key⟩ ⊔ 𝑼⟨<⟩) where
  [] : {{l<u : l <⁺ u}} → OrderedList l u
  _∷_ : ∀
         (k : Key)
         {{_ : l <⁺ [ k ]}}
         (ku : OrderedList [ k ] u) →
         OrderedList l u

data _∈_ {l u} (k : Key) : OrderedList l u → Set (𝑼⟨<⟩ ⊔ 𝑼⟨Key⟩) where
  here : ∀ {ks : OrderedList [ k ] u} {{p : l <⁺ [ k ] }} → k ∈ (k ∷ ks)
  succ : ∀ {k' : Key} {ks : OrderedList [ k' ] u} {{p : l <⁺ [ k' ] }} → k ∈ ks → k ∈ (k' ∷ ks)


{- The first of three attempts at the lemma. -}
lem1 : ∀ {l u} (y : OrderedList l u) (l<u : l <⁺ u) → (x : ∀ (k : Key) → (k ∈ y → _∈_ k [])) → [] ≡ y
{- 
The yellow highlights in the above type specification are associated with error messages like this:

  _l_70 : Key⁺  [ at Enagda05-need-more-help-from-agda.agda:41,83-86 ]
  _u_71 : Key⁺  [ at Enagda05-need-more-help-from-agda.agda:41,83-86 ]
  _l<u_72 : _l_70 Value isStrictTotalOrder y l<u k <⁺
  _u_71 Value isStrictTotalOrder y l<u k  [ at Enagda05-need-more-help-from-agda.agda:41,89-91 ]

QUESTION: What exactly do these errors mean?
-}
lem1 {l} {u} [] l<u ∀k→k∈y→k∈[] = {!!}
lem1 (k ∷ y) l<u ∀k→k∈y→k∈[] = {!!}

{- 
Moving on, in lem2, I avoid the errors mentioned in lem1 by adding a specification of just one of the implicit arguments, {l}. Somehow this works to remove the yellow highlighting, but I'm not clear on why. 
-}
lem2 : ∀ {l u} (y : OrderedList l u) (l<u : l <⁺ u) → (x : ∀ (k : Key) → (k ∈ y → _∈_ {l} {u} k [])) → [] ≡ y
lem2 {l} {u} [] l<u ∀k→k∈y→k∈[] = {!refl!}
{- 
Executing C-c C-. on the hole shows:

  Goal: [] ≡ []
  Have: _x_106 Value isStrictTotalOrder l<u ∀k→k∈y→k∈[] ≡
        _x_106 Value isStrictTotalOrder l<u ∀k→k∈y→k∈[]
  ————————————————————————————————————————————————————————————
  ∀k→k∈y→k∈[]
           : (k : Key) → k ∈ [] → k ∈ []
  l<u      : l <⁺ u
  .l<u     : l <⁺ u
  u        : Key⁺
  l        : Key⁺
  isStrictTotalOrder
           : IsStrictTotalOrder _≡_ _<_
  _<_      : Rel Key 𝑼⟨<⟩
  Value    : Key → Set 𝑼⟨Value⟩
  Key      : Set 𝑼⟨Key⟩
  𝑼⟨<⟩     : Level.Level
  𝑼⟨Value⟩ : Level.Level
  𝑼⟨Key⟩   : Level.Level

I'm unable to refine by typing C-c C-r, but I have no explanation (yet) for why it won't refine. Agda simply says "cannot refine". QUESTION: Should I be able to tell why it won't refine given the information above?

Here's the error message if I (by brute force) replace the hole with refl:
 
  l<u != .l<u of type l <⁺ u
  when checking that the expression refl has type [] ≡ []

It looks to me like Agda has now given me some more clues as to why it had refused to refine. COMPLAINT: Please correct me if I'm wrong, but couldn't (shouldn't?) Agda have divulged this business about l<u when I hit C-c C-. ?

It turns out that .l<u is an implicit argument to the first explicit argument ([] or y). COMPLAINT: It isn't always obvious where dotted variables are coming from, so I wish Agda would tell me this. It may be asking too much to have a semi-automated way of bringing these hidden variables into scope. I'm just saying that there needs to be more clues given as to how the programmer might bring the given variable into scope.

Furthermore, I'm confused about the meaning of this error message. It sounds like Agda is saying that, while l<u and .l<u are both of the same type, they aren't (somehow) "the same". Okay, but so what? Why should that have something to do with checking that refl has type [] ≡ [] ? QUESTION: How am I to interpret the error message?
-}
lem2 (k ∷ y) l<u ∀k→k∈y→k∈[] = {!!}


{- I'm still not ready to give up the fight. Inspired by the meager clue in the previous error message, I come up with a reformulatation the lemma. As it turns out, I need to define a function that gives a proof of the bounds for an OrderedList. -}

-- This one fails comically.
l<⁺u' : ∀ {l u} (y : OrderedList l u) → l <⁺ u
l<⁺u' [] = {!!} -- COMPLAINT: C-c C-a yields the syntactically incorrect .l<u
l<⁺u' (k ∷ y) = {!!}

l<⁺u : ∀ {l u} (y : OrderedList l u) → l <⁺ u
l<⁺u ([] {{l<u}}) = l<u
l<⁺u (_∷_ k {{l<⁺[k]}} y) = {!!} -- exercise for the reader

trans⁺ : ∀ l {m u} → l <⁺ m → m <⁺ u → l <⁺ u
trans⁺ = {!!} -- exercise for the reader

{- Here's my last try at the lemma. -}
lem3 : ∀ {l u} (y : OrderedList l u) → (x : ∀ (k : Key) (l' u' : Key⁺) (l'<u' : l' <⁺ u') → (k ∈ y → _∈_ {l'} {u'} k ([] {{l'<u'}}))) → [] {{l<⁺u y}} ≡ y
lem3 {l} {u} ([] {{l<u}}) ∀k→k∈y→k∈[] = refl
{-
Here's the result of C-c C-. this time:

  Goal: [] ≡ []
  Have: _x_150 Value isStrictTotalOrder ∀k→k∈y→k∈[] ≡
        _x_150 Value isStrictTotalOrder ∀k→k∈y→k∈[]
  ————————————————————————————————————————————————————————————
  ∀k→k∈y→k∈[]
           : (k : Key) (l' u' : Key⁺) (l'<u' : l' <⁺ u') → k ∈ [] → k ∈ []
  l<u      : l <⁺ u
  u        : Key⁺
  l        : Key⁺
  isStrictTotalOrder
           : IsStrictTotalOrder _≡_ _<_
  _<_      : Rel Key 𝑼⟨<⟩
  Value    : Key → Set 𝑼⟨Value⟩
  Key      : Set 𝑼⟨Key⟩
  𝑼⟨<⟩     : Level.Level
  𝑼⟨Value⟩ : Level.Level
  𝑼⟨Key⟩   : Level.Level

This looks pretty similar to what we saw in lem2. It turns out that the refl in the hole will refine, but, weirdly, the result is a yellow-highlighted error:

_139 : [] ≡ []  [ at Enagda05-need-more-help-from-agda.agda:114,42-46 ]
_140 : [] ≡ []  [ at Enagda05-need-more-help-from-agda.agda:114,42-46 ]

I suspect the meaning of the above error is that there's some unification problem, but I feel like Agda could be telling me more. QUESTION: What does it mean?
-}
lem3 (k ∷ y) ∀k→k∈y→k∈[] = {!!}
