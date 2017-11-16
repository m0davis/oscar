In the code below, an internal error occurs at `src/full/Agda/Syntax/Translation/ConcreteToAbstract.hs:721` when trying to refine (`C-c C-r`) the goal.

```agda
foo : Set
foo = {!foo λ {x y → foo}!}
```
