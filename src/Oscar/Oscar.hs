{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE UnicodeSyntax #-}

module Oscar.Oscar where

import Oscar.Main.Prelude

import Oscar.FormulaCode
import Oscar.Problem

testOscar ∷ Problem → IO ()
testOscar problem@(Problem {..}) = do
    print "TEST: STARTING"
    print "Problem:"
    ppPrint problem
    print "TEST: ENDING"
    return ()

data Reason = Reason
    { _reasonName ∷ Text
    , _reasonFunction ∷ Oscar → Oscar
    , _reasonConclusions ∷ ()
    , _reasonConclusionsFunction ∷ ()
    , _reasonForwardsPremises ∷ ()
    , _reasonBackwardsPremises ∷ ()
    , _reasonVariables ∷ ()
    , _reasonDefeasibleRule ∷ ()
    , _reasonStrength ∷ Double
    , _reasonDiscountFactor ∷ Double
    , _reasonDescription ∷ ()
    , _reasonInstantiatedPremise ∷ ()
    , _reasonBackwardsPremisesFunction ∷ ()
    , _reasonTemporal ∷ Bool
    , _reasonUndercuttingDefeaters ∷ ()
    , _reasonDefeatees ∷ ()
    }

data Oscar = Oscar
    { _oscarDiscriminationNet ∷ DiscriminationNet -- TODO we might only need the top node; consider replacing with a DiscriminationNode
    , _oscarDiscriminationNodeNumber ∷ Int
    , _oscarDiscriminationNodeTop ∷ DiscriminationNode
    , _oscarTemporalCycle ∷ Int
    }

data DiscriminationNode = DiscriminationNode
  { _discriminationNodeNumber ∷ Int -- historical/descriptive
  , _discriminationNodeDescription ∷ [Discriminator] -- historical/descriptive
  , _discriminationNodeTests ∷ [(Discriminator, DiscriminationNode)]
  , _discriminationNodeParent ∷ Maybe DiscriminationNode
  }

type DiscriminationNet = [DiscriminationNode]

data Interest

storeInterestAtNewDNode ∷ Interest → FormulaTerm → DiscriminationNode → Discriminator → Oscar → Oscar
storeInterestAtNewDNode = undefined

-- initializeOscarState ∷ State Oscar ()
-- initializeOscarState = put $ Oscar [top] 1
--   where
--     top = DiscriminationNode 1 [] [] Nothing

-- insertDiscriminationNode ∷ Text -> [(DiscriminationTest, DiscriminationNode)] -> DiscriminationNode -> DiscriminationNet -> DiscriminationNet
-- insertDiscriminationNode description tests parent dn =
--   dn { _osDiscriminationNet = dn : _osDiscriminationNet dn
--      , _osDiscriminationNodeNumber = 1 + _osDiscriminationNodeNumber dn
--      }

-- simpleDiscriminationNet ∷ State OscarState ()
-- simpleDiscriminationNet = top <> conditional <> undercutter <> conjunctiveUndercutter
--   where
--     top = Discrimination

-- oscar ∷ [DiscriminationNode] -> IO ()
-- oscar [] = oscar oscar conditional

