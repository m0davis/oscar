#### Non-unique solutions

Agda finds non-unique solutions of constraints involving `eta-equality` record types when there are other solutions involving hidden arguments. My understanding is that

###### a superclass and its _magic_ method

```agda
record Super : Set₁ where
  -- no-eta-equality
  constructor #_
  field
    type : Set

postulate
  magic-method : (c : Super) → Super.type c
```

###### particulars

```agda
postulate
  I : Set
  A : I → Set
  i : I
```

###### demonstrating non-uniqueness

In the below, Agda solves the hole term as `# A i`. (If record `Super` is changed to `no-eta-equality`, Agda (correctly) fails to find a solution.)

```agda
test-magic-open : A i
test-magic-open = magic-method {!!} -- ?0 := # A i

test-magic-closed-1 : A i
test-magic-closed-1 = magic-method (# A i)
```

But a different solution was possible!

```agda
test-magic-closed-2 : A i
test-magic-closed-2 = magic-method (# ∀ {j : I} → A j)
```

#### Is instance search negligent?

The upshot is that instance search can appear to be negligent, failing with "no instance found" when an appropriate named instance is in scope. Really, it's just (improperly?) constrained.

###### subclass and its _real_ method

```agda
record Sub (c : Super) : Set where
  field value : Super.type c

real-method : (c : Super) → Sub c → Super.type c
real-method _ I = Sub.value I
```

###### instance search

```agda
it : ∀ {a} {A : Set a} {{x : A}} → A
it {{x}} = x
```

###### an instance

```agda
postulate instance I-sub-tricky : Sub (# ∀ {j} → A j)
```

###### demonstrating instance search negligence

`it` doesn't find anything (of a certain type).

```agda
test-real-fails : A i
test-real-fails = real-method _ {!it!} -- No instance of type (Sub (# A i))
```

But _I_ do.

```agda
test-real-works : A i
test-real-works = real-method _ I-sub-tricky
```

A workaround (if we really want to use instance search) is to specify the superclass.

```agda
test-real-workaround : A i
test-real-workaround = real-method (# ∀ {j} → A j) it
```

From issue #2099:

```agda
the : (A : Set) (x : A) -> A
the _ x = x

data It {X : Set}(x : X) : Set where ! : It x

data Wrap (x : Set) : Set where wrap : (a : x) -> Wrap x

prf : {X Y : Set} -> Wrap ({a : X} (y : X) -> It a)
prf {X} {Y} = wrap (the {!{a : X} (y : X) -> It a!} (\y -> !))
```

Also possibly related to issue #1079.
