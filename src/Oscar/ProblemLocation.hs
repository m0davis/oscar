{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}
module Oscar.ProblemLocation where

class ƇPlace place where

-- | For use in 'Tagged' (or '`⁞`') annotations. `⁞`
data ƇPlace place ⇒ ƮAfter place
