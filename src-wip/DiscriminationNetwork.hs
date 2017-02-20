module DiscriminationNetwork where



data DiscriminationNode = DiscriminationNode
    { _dnNumber ∷ Int
    , _dnDescription ∷ [Discriminator] -- nil)
    , _dnDiscriminationTests ∷ [(Discriminator, DiscriminationNode)] -- nil)
    , _dnCLists ∷ () -- nil)
    , _dnILists ∷ () -- nil)
    , _dnParent ∷ Maybe DiscriminationNode -- nil)
    , _dnForwardsReasons ∷ () -- nil)  -- a list of partially-instantiated-premises
    , _dnBackwardsReasons ∷ () -- nil)  -- a list of non-degenerate backwards-reasons
    , _dnInterestSchemes ∷ () -- nil)  -- a list of partially-instantiated-premises
    , _dnDegenerateBackwardsReasons ∷ () -- nil)
    }

pursueDNodeFor
