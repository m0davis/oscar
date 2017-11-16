Mixfix operators can generate a parsing error when using the short-hand module application syntax.

```agda
module AgdaModuleEqualsSyntaxProblem where

module M (F : Set → Set) where

module works-with-parens (mix_fix : Set → Set) = M (mix_fix)

module works-without-= (mix_fix : Set → Set) where open M mix_fix public

-- module fails (mix_fix : Set → Set) = M mix_fix
```
