{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE UnicodeSyntax #-}

module Oscar.Oscar where

import Oscar.Main.Prelude

import qualified Oscar.Formula as F
import qualified Oscar.FormulaCode as FC
import qualified Oscar.Problem as P

import Oscar.Problem (Problem(Problem))
import Oscar.Formula (Symbol(Symbol))
import Oscar.FormulaCode (Formula)

type FormulaTerm = FC.FormulaTerm
type Discriminator = FC.Discriminator

testOscar ∷ Problem → IO ()
testOscar problem@(Problem {..}) = do
    print "TEST: STARTING"
    print "Problem:"
    ppPrint problem
    print "TEST: ENDING"
    return ()

-- TODO for efficiency, use TemplateHaskell to convert strings into Formulas (or UFormulas)
compileFormulaFromText ∷ Text → Formula
compileFormulaFromText = undefined

simpReason ∷ ForwardsReason
simpReason = ForwardsReason Reason
    { _rName = "simp"
    , _rForwardsPremises = [cfp (compileFormulaFromText "(P & Q)") ((Symbol . pack) <$> ["P", "Q"]) undefined]
    , _rVariables = ((Symbol ) <$> ["P", "Q"])
    , _rFunction = simpReasonFunction
    }
  where
    simpReasonFunction ∷ Oscar -> (Oscar, IO ())
    simpReasonFunction o = undefined

cfp ∷ Formula → SET Variable → BindingFunction → ForwardsPremise
cfp f vs bf = constructForwardsPremise f undefined vs bf

constructForwardsPremise ∷ Formula → Condition → SET Variable → BindingFunction → ForwardsPremise
constructForwardsPremise f c vs bf =
    ForwardsPremise
        { _fpFormula = f
        , _fpKind = PremiseKindInference
        , _fpCondition = c
        , _fpVariables = vs
        , _fpBindingFunction = bf
        , _fpInstantiator = reasonInstantiator f vs
        }

-- reason-instantiator
reasonInstantiator ∷ Formula → SET Variable → Instantiator
reasonInstantiator f vs = undefined

-- def-instantiator
definitionInstantiator ∷ TODO → SET Variable → Instantiator
definitionInstantiator = undefined

type SET a = [a]

type Variable = Symbol

type TODO = ()
type BindingFunction = TODO
type Condition = TODO
type Instantiator = TODO

newtype ForwardsReason = ForwardsReason { _frReason ∷ Reason }

data Reason = Reason
    { _rName ∷ Text
    , _rFunction ∷ Oscar → (Oscar, IO ())
    , _rConclusions ∷ ()
    , _rConclusionsFunction ∷ ()
    , _rForwardsPremises ∷ [ForwardsPremise]
    , _rBackwardsPremises ∷ ()
    , _rVariables ∷ SET Variable
    , _rDefeasibleRule ∷ ()
    , _rStrength ∷ Double
    , _rDiscountFactor ∷ Double
    , _rDescription ∷ ()
    , _rInstantiatedPremise ∷ ()
    , _rBackwardsPremisesFunction ∷ ()
    , _rTemporal ∷ Bool
    , _rUndercuttingDefeaters ∷ ()
    , _rDefeatees ∷ ()
    }

data PremiseKind = PremiseKindInference
                 | PremiseKindPercept

data ForwardsPremise = ForwardsPremise
    { _fpFormula ∷ Formula
    , _fpKind ∷ PremiseKind
    , _fpCondition ∷ Condition
    , _fpBindingFunction ∷ ()
    , _fpVariables ∷ SET Variable
    , _fpInstantiator ∷ ()
    , _fpIsClue ∷ ()
    , _fpHypernodeSpecifier ∷ () -- bound to the node instantiating the premise in a link
    }

defaultForwardsPremise ∷ ForwardsPremise
defaultForwardsPremise = ForwardsPremise { _fpKind = PremiseKindInference }


data HyperLink = HyperLink
    { _hlNumber ∷ () -- 0)
    , _hlTarget ∷ () -- nil)   -- the node supported by the link
    , _hlBasis ∷ () -- nil)   -- a list of hypernodes
    , _hlRule ∷ () -- nil)  -- a substantive reason or a string describing an inference rule
    , _hlIsDefeasible ∷ Bool -- nil)  -- t if the inference is a defeasible one
    , _hlDefeaters ∷ () -- nil)  -- a list of hyper-defeat-links
    , _hlDegreeOfJustification ∷ () -- nil)
    , _hlDiscountFactor ∷ () -- 1.0)  -- This is the discount-factor provided by the link-rule.
    , _hlNearestDefeasibleAncestors ∷ () -- nil)
    , _hlReasonStrength ∷ () -- 1.0)  -- the strength of the reason
    , _hlBinding ∷ () -- nil)
    , _hlConclusiveDefeatStatus ∷ () -- nil)
    , _hlTemporal ∷ () -- nil)
    , _hlGeneratingInterestLink ∷ () -- nil)
    , _hlClues ∷ () -- nil)
    , _hlIsUnsecured ∷ Bool -- nil) -- list of sigmas
    , _hlDefeatLoops ∷ () -- T) -- defeat-loops from link to link
    , _hlJustifications ∷ () -- nil)  -- list of pairs (sigma.val) used by justification
    , _hlIn ∷ () -- (list nil))  -- list of sigmas
    , _hlDependencies ∷ () -- nil)  -- list of sigmas
    }
data HyperDefeatLink = HyperDefeatLink
    { _hdlNumber ∷ () -- 0)
    , _hdlTarget ∷ () -- nil)   -- the hyperlink defeated by the link
    , _hdlRoot ∷ () -- nil)   -- an hypernode
    , _hdlIsCritical ∷ Bool -- nil)  -- list of (X.t) or (sigma.nil)
    , _hdlJustifications ∷ () -- nil)  -- list of pairs (sigma.val).
    , _hdlIn ∷ () -- (list nil))  -- list of  lists of links
    }
data HyperNode = HyperNode
    { _hnNumber ∷ () -- 0)
    , _hnSequent ∷ () -- nil)
    , _hnFormula ∷ () -- nil)
    , _hnSupposition ∷ () -- nil)
    , _hnKind ∷ () -- nil)   --:percept, :desire, or :inference
    , _hnHyperlinks ∷ () -- nil)
    , _hnJustification ∷ () -- nil)  -- a keyword if the node is given or a supposition
    , _hnConsequentLinks ∷ () -- nil)
    , _hnOldDegreeOfJustification ∷ () -- nil) -- the degree prior to the last computation of defeat statuses
    , _hnReductioAncestors ∷ () -- nil)
    , _hnNonReductioSupposition ∷ () -- nil)
    , _hnSupportedHyperDefeatLinks ∷ () -- nil)  -- hyper-defeat-links for which the node is the root
    , _hnDegreeOfJustification ∷ () -- nil)
    , _hnMaximalDegreeOfJustification ∷ () -- 0)  -- maximal possible dj, ignoring defeat
    , _hnAncestors ∷ () -- nil)
    , _hnNearestDefeasibleAncestors ∷ () -- nil)
    , _hnAnsweredQueries ∷ () -- nil)
    , _hnDeductiveOnly ∷ () -- nil)   -- If conclusion is for deductive purposes only, this is t.
    , _hnGeneratedInterests ∷ () -- nil)
    , _hnGeneratingInterests ∷ () -- nil)-- interest generating sup
    , _hnCancelledNode ∷ () -- nil)
    , _hnDiscountedNodeStrength ∷ () -- nil)
    , _hnIsProcessed ∷ Bool -- nil)  --  T if node has been processed.
    , _hnVariables ∷ () -- nil)
    , _hnDischargedInterests ∷ () -- nil)  -- triples (interest unifier unifiers) where unifiers is produced by appropriately-related-suppositions.  unifier and unifiers are left nil in cases where they will not be used.
    , _hnSuppositionVariables ∷ () -- nil)
    , _hnAreInterestsDischarged ∷ Bool -- nil)   -- records whether interests have been discharged
    , _hnReductiosDischarged ∷ () -- (not *use-reductio*))  -- records whether reductio-interests have been discharged
    , _hnReadoptedSupposition ∷ () -- 0)  -- number of times the node has been readopted as a supposition
    , _hnDiscountFactor ∷ () -- 1.0)  -- This is the discount-factor provided by the hypernode-rule.  it's only use is in ei.
    , _hnCList ∷ () -- nil)
    , _hnQueueNode ∷ () -- nil)
    , _hnEnablingInterests ∷ () -- nil)  -- if the node is obtained by discharging inference-links, this is the list of resultant-interests of the links.
    , _hnMotivatingNodes ∷ () -- nil)  -- nodes motivating the inference, not included in the basis.
    , _hnGeneratedDirectReductioInterests ∷ () -- nil)
    , _hnGeneratedDefeatInterests ∷ () -- nil)
    , _hnGeneratingDefeatInterests ∷ () -- nil)  -- interest in defeaters discharged by this node
    , _hnTemporalNode ∷ () -- nil)  -- nil or the cycle on which the node was constructed
    , _hnBackgroundKnowledge ∷ () -- nil)
    , _hnIsNonReductioSupposition ∷ Bool -- nil)
    , _hnAnchoringInterests ∷ () -- nil)
    , _hnJustifications ∷ () -- nil)  -- list of pairs (sigma.val) used by justification
    , _hnIn ∷ () -- (list nil))  -- list of  lists of links
    , _hnDependencies ∷ () -- nil)   -- list of sigmas
    }
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
data CList = CList
    { _clFormula ∷ () -- nil)
    , _clCorrespondingILists ∷ () -- nil)
    , _clNodes ∷ () -- nil)
    , _clProcessedNodes ∷ () -- nil)
    , _clLinkDefeatees ∷ () -- nil)
    , _clReductioInterests ∷ () -- nil)
    , _clVariables ∷ () -- nil)
    , _clContradictors ∷ () -- nil)
    , _clTermList ∷ () -- nil)
    , _clDNode ∷ () -- nil)
    , _clGeneratedInstantiatedPremises ∷ () -- nil)
    , _clSupportedInterestSchemes ∷ () -- nil))
    }
data Query = Query
    { _qNumber ∷ () -- 0)
    , _qFormula ∷ () -- nil)
    , _qStrength ∷ () -- 0)
    , _qQueueNode ∷ () -- nil)
    , _qDeductive ∷ () -- nil)  -- t if the query is whether the query formula is deductively provable
    , _qPositiveInstructions ∷ () -- nil) -- a list of functions applicable to an hypernode
    , _qNegativeInstructions ∷ () -- nil) -- a list of functions applicable to an hypernode
    , _qAnswers ∷ () -- nil)  --a list of hypernodes
    , _qIsAnswered ∷ Bool -- nil)  -- t if some answer is justified to degree greater than or equal to the degree of interest, nil otherwise
    , _qInterest ∷ () -- nil)   -- the interest recording the query
    , _qNegativeInterest ∷ () -- nil)  -- the negative-interest for a whether-query
    , _qQConstraint ∷ () -- nil))  -- a function which when applied to the ?-vars yields a discharge-condition for the query-interest, constraining the instantiating terms.
    }
data InstantiatedPremise = InstantiatedPremise
    { _ipReason ∷ () -- nil)
    , _ipBinding ∷ () -- nil)  -- cumulative binding prior to this premise
    , _ipBasis ∷ () -- nil)
    , _ipPremise ∷ () -- nil)
    , _ipRemainingPremises ∷ () -- nil)  -- premises left to be instantiated
    , _ipInstantiations ∷ () -- nil)  -- instantiations of hypernode-variables in previous premises
    , _ipUsedPremiseVariables ∷ () -- nil)  -- premise-variables bound in earlier premises
    , _ipUsedVariables ∷ () -- nil)  -- conclusion-variables occurring in basis
    , _ipDerivedPremises ∷ () -- nil)  -- instantiated-premises immediately following this one
    , _ipDNode ∷ () -- nil)
    , _ipNumber ∷ () -- 0)
    , _ipClues ∷ () -- nil)
    , _ipIsInitial ∷ Bool --  nil))   -- records whether the premise is the initial premise of the reason
    }
data InterestScheme = InterestScheme
    { _nsInstantiatedPremise ∷ InstantiatedPremise
    , _nsTargetInterest ∷ () -- nil)
    , _nsSupposition ∷ () -- nil)
    , _nsSuppositionVariables ∷ () -- nil)
    , _nsInstanceFunction ∷ () -- nil)
    , _nsGeneratingNode ∷ () -- nil))
    }
-- "An interest-graph-link"
data InterestLink = InterestLink
    { _nlNumber ∷ () -- 0)
    , _nlResultantInterest ∷ () -- nil)
    , _nlInterest ∷ () -- nil)
    , _nlInterestFormula ∷ () -- nil)
    , _nlInterestCondition ∷ () -- nil)
    , _nlBinding ∷ () -- nil)
    , _nlRule ∷ () -- nil)
    , _nlRemainingPremises ∷ () -- nil)
    , _nlSupportingNodes ∷ () -- nil)
    , _nlInstantiations ∷ () -- nil)
    , _nlSupposition ∷ () -- nil)
    , _nlDefeaters ∷ () -- nil)
    , _nlDefeatStatus ∷ () -- nil)
    , _nlStrength ∷ () -- 0)  -- maximum-degree-of-interest conveyed
    , _nlGeneratingNode ∷ () -- nil)
    , _nlDischarged ∷ () -- nil)
    , _nlInterestMatch ∷ () -- nil)
    , _nlInterestReverseMatch ∷ () -- nil)
    , _nlGenerating ∷ () -- nil)
    , _nlPremise ∷ () -- nil)
    , _nlClues ∷ () -- nil)
    }
-- "An interest-graph-node"
data Interest = Interest
    { _nNumber ∷ () -- 0)
    , _nSequent ∷ () -- nil)
    , _nFormula ∷ () -- nil)
    , _nSupposition ∷ () -- nil)
    , _nRightLinks ∷ () -- nil)
    , _nLeftLinks ∷ () -- nil)
    , _nDegreeOfInterest ∷ () -- *base-priority*)
    , _nLastProcessedDegreeOfInterest ∷ () -- nil)
    , _nDefeatStatus ∷ () -- nil)
    , _nDischargedDegree ∷ () -- nil)  -- used in computing priorities
    , _nDeductive ∷ () -- nil)
    , _nCancelled ∷ () -- nil)
    , _nQueueNode ∷ () -- nil)
    , _nIList ∷ () -- nil)
    , _nMaximumDegreeOfInterest ∷ () -- 0)
    , _nDefeatees ∷ () -- nil)
    , _nReductio ∷ () -- nil)
    , _nDirectReductio ∷ () -- nil)
    , _nGeneratedSuppositions ∷ () -- nil)
    , _nGeneratingNodes ∷ () -- nil)
    , _nPriority ∷ () -- 0)
    , _nVariables ∷ () -- nil)
    , _nDischargeCondition ∷ () -- nil)  --a function of node, unifier, and interest-link
    , _nSuppositionVariables ∷ () -- nil)
    , _nCancellingNode ∷ () -- nil)
    , _nDischargingNodes ∷ () -- nil)
    , _nSuppositionNodes ∷ () -- nil)
    , _nGeneratedInterestSchemes ∷ () -- nil)
    , _nDefeaterBinding ∷ () -- nil)
    , _nGeneratingDefeatNodes ∷ () -- nil)
    , _nCancelledLeftLinks ∷ () -- nil)
    , _nIsNonReductio ∷ Bool -- t)
    , _nAnchoredNodes ∷ () -- nil)
    , _nTextDischargeCondition ∷ () -- nil)  -- a text statement of the discharge condition
    , _nEnabledNodes ∷ () -- nil)  -- the nodes for which this is an enabling-interest
    , _nDecisionPlans ∷ () -- nil)  -- the nodes this interest is relevant to deciding on
    }
data IList = IList
    { _ilFormula ∷ () -- nil)
    , _ilCorrespondingCLists ∷ () -- nil)
    , _ilInterests ∷ () -- nil)
    , _ilQueries ∷ () -- nil)
    , _ilReductioTrigger ∷ () -- nil)
    , _ilReductioSupposition ∷ () -- nil)
    , _ilVariables ∷ () --
    , _ilTermList ∷ () -- nil)
    , _ilDNode ∷ () -- nil))
    }
data BackwardsPremise = BackwardsPremise
    { _bpFormula ∷ () -- nil)
    , _bpCondition1 ∷ () -- nil)
    , _bpCondition2 ∷ () -- nil)
    , _bpInstantiator ∷ () -- nil)
    , _bpIsClue ∷ Bool -- nil)
    , _bpTextCondition ∷ () -- nil)  -- text specification of the discharge condition
    , _bpHypernodeSpecifier ∷ () -- nil)  -- bound to the node instantiating the premise in a link
    }
data BackwardsReason = BackwardsReason
    { _brReason ∷ Reason
    , _brCondition ∷ () -- nil)  -- this is a predicate applied to the binding
    , _brDischarge ∷ () -- nil)
    , _brLength ∷ () -- 1)  -- this is the number of backwards-premises
    , _brConclusionsBindingFunction ∷ () -- nil)
    , _brConclusionVariables ∷ () -- nil)
    , _brImmediate ∷ () -- nil))
    }
data InferenceQueueNode = InferenceQueueNode
    { _iqnNumber ∷ () -- 0)
    , _iqnItem ∷ () -- nil)  -- either an interest or a conclusion or a query
    , _iqnItemKind ∷ () -- nil)   -- this will be :conclusion, :interest, or :query
    , _iqnItemComplexity ∷ () -- 0)
    , _iqnDiscountedStrength ∷ () -- 0)
    , _iqnDegreeOfPreference ∷ () -- 0))
    }
data Goal = Goal
    { _gNumber ∷ () -- 0)
    , _gFormula ∷ () -- nil)
    , _gStrength ∷ () -- 1)
    , _gSupportingNode ∷ () -- nil)  -- the node supporting this as a suitable goal
    , _gGeneratingDesire ∷ () -- nil)  -- the desire, if there is on, that generates the goal
  -- (plans-for nil)  -- the list of candidate plans that aim at the satisfaction of this goal
  -- (user-question-asked? nil)
    }
data Desire = Desire
    { _dNumber ∷ () -- 0)
    , _dContent ∷ () -- nil)
    , _dObject ∷ () -- nil)  -- the object of a desire will be a goal
    , _dStrength ∷ () -- 0)
    , _dGeneratedPlans ∷ () -- nil)
    , _dGeneratingInterest ∷ () -- nil)  -- for epistemic-desires
    , _dHypernode ∷ () -- nil))  -- the hypernode recording the desire
    }
data Percept = Percept
    { _pNumber ∷ () -- 0)
    , _pContent ∷ () -- nil)
    , _pClarity ∷ () -- 0)
    , _pDate ∷ () -- 0))
    }


data Oscar = Oscar
    { _oscarDiscriminationNet ∷ DiscriminationNet -- TODO we might only need the top node; consider replacing with a DiscriminationNode
    , _oscarDiscriminationNodeNumber ∷ Int
    , _oscarDiscriminationNodeTop ∷ DiscriminationNode
    , _oscarTemporalCycle ∷ Int
    }

type DiscriminationNet = [DiscriminationNode]

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

