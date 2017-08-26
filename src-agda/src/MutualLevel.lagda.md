The order of definitions in a mutual block is not supposed to matter, but the below demonstrates that it does (at least with respect to levels).

```agda
open import Agda.Primitive

it : ∀ {a} {A : Set a} {{x : A}} -> A
it {{x}} = x

postulate
  F : Set → Set
  A : Set
  instance iFoo : F A

mutual -- works

  a1 : Level
  a1 = _

  A1 : Set a1
  A1 = _

  FA1 : F A
  FA1 = it {a1} {A1} {{it}}

mutual -- works

  a2 : Level
  a2 = _ -- yellow

  FA2 : F A
  FA2 = it {a2} {A2} {{it}} -- no instance of type A2

  A2 : Set a2
  A2 = _

mutual -- fails

  A3 : Set {!a3!} -- a3 is not in scope
  A3 = _

  a3 : Level
  a3 = _

  FA3 : F A
  FA3 = it {a3} {A3} {{it}}
```
