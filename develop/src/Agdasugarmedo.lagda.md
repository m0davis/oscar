
```agda
{-# OPTIONS --allow-unsolved-metas #-}
```

# failure to unify absurd lambdas when function declared mutually with datatype

```agda
module Agdasugarmedo where
```

Should Agda drop datatype parameters from an absurd lambda? I'm not sure if this behaviour of Agda's is intended or a bug. It seems related to #2256 in that Agda is not dropping datatype parameters from an absurd lambda. Or anyway, it's not unifying those absurd lambdas with each other while inside a function mutually-defined with the datatype.

This program type-checks if `foo`'s type-declaration is moved below `PBot`'s definition:

```agda
data Bot : Set where
data NotBot : Set where
  alice bobby : NotBot

postulate
  P : (Bot → Bot) → Set

data PBot (d : NotBot) : Set

foo : (x y : NotBot) → PBot x → PBot y

data PBot (d : NotBot) where
  con : P (λ()) → PBot d

foo alice alice (con p) = con p
foo alice bobby (con p) = con {!p!}
                           -- ^ error here (after give and reload)
foo bobby alice (con p) = con {!!}
foo bobby bobby (con p) = con p
```

The error is

    alice != bobby of type NotBot
    when checking that the expression p has type P ((λ ()) bobby)

So, `p` has type `P ((λ ()) alice)` but the goal there is `P ((λ ()) bobby)`. Hmm... The lambda seems to be inheriting the parameter from the datatype. From a user's perspective, the problem gets worse if pattern lambdas are used: {-
    data PBot (d : NotBot) where
      con : P (λ{()}) → PBot d

    ...
    foo alice bobby (con p) = con {!p!}
    ...
-}
In that case, `Goal` and `p` look identical, there are no unsolved metas or constraints, Agda accepts `p` via `agda2-give`, but complains on reload. It gives me the sugar-me-do!

Fwiw, a slightly simpler (but less motivated) example of the problem is as follows:

```agda
data QBot (d : Bot) : Set

bar : (x y : Bot) → QBot x → QBot y

data QBot (d : Bot) where
  con : P (λ()) → QBot d

bar x y (con p) = con {!p!}
                   -- ^ error here (after give and reload)
```

A workaround is to define the absurd lamba outside the parameterised data definition so that the lamda doesn't inherit the parameter:

```agda
data RBot (d : NotBot) : Set

qux : (x y : NotBot) → PBot x → PBot y

bot2bot : Bot → Bot
bot2bot = λ ()

data RBot (d : NotBot) where
  con : P bot2bot → RBot d

qux x y (con p) = con p
```
