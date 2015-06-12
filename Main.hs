{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main (
    main,
    ) where

import Oscar.Main.Prelude

import Oscar.Main                       (combinedProblemsPath)

import Oscar.ProblemParser              (readFileProblems)

import Oscar.Formula                    (Symbol(Symbol))
import Oscar.FormulaParser              (formulaFromText)
import Oscar.FormulaCode                (uFormula)
import Oscar.FormulaCode                (formulaCode)
import Oscar.FormulaCode                (reasonCode)

import Oscar.Oscar                      (testOscar)

{- | At the moment, the executable simply reads from a file called
     "combined-probems", parses the problems, and prints a structured
     representation. Reading and parsing the file is done with
     'readFileProblems'. The file itself is denoted by 'combinedProblemsPath'.
     Printing is done by 'ppPrint'.

__Example__

* Sample input file

    @
    Problem #1
    This is a case of collective rebutting defeat
    Given premises:
         P    justification = 1.0
         A    justification = 1.0
    Ultimate epistemic interests:
         R    interest = 1.0

             FORWARDS PRIMA FACIE REASONS
               pf-reason_1:   {P} ||=> Q   strength = 1.0
               pf-reason_2:   {Q} ||=> R   strength = 1.0
               pf-reason_3:   {C} ||=> ~R   strength = 1.0
               pf-reason_4:   {B} ||=> C   strength = 1.0
               pf-reason_5:   {A} ||=> B   strength = 1.0
    @

* Sample printed output

    @
    Problem
      { _problemNumber = ProblemNumber 1
      , _problemDescription =
          ProblemDescription "This is a case of collective rebutting defeat"
      , _problemPremises =
          [ ( FormulaPredication
                { _formulaPredication = Predication (Symbol "P") [] }
            , ProblemJustificationDegree (Degree 1.0)
            )
          , ( FormulaPredication
                { _formulaPredication = Predication (Symbol "A") [] }
            , ProblemJustificationDegree (Degree 1.0)
            )
          ]
      , _problemInterests =
          [ ( FormulaPredication
                { _formulaPredication = Predication (Symbol "R") [] }
            , ProblemInterestDegree (Degree 1.0)
            )
          ]
      , _problemForwardsPrimaFacieReasons =
          [ ( ProblemReasonName "pf-reason_1"
            , ForwardsReason
                { _frForwardsPremises =
                    [ FormulaPredication
                        { _formulaPredication = Predication (Symbol "P") [] }
                    ]
                , _frConclusion =
                    FormulaPredication
                      { _formulaPredication = Predication (Symbol "Q") [] }
                }
            , ProblemStrengthDegree (Degree 1.0)
            )
          , ( ProblemReasonName "pf-reason_2"
            , ForwardsReason
                { _frForwardsPremises =
                    [ FormulaPredication
                        { _formulaPredication = Predication (Symbol "Q") [] }
                    ]
                , _frConclusion =
                    FormulaPredication
                      { _formulaPredication = Predication (Symbol "R") [] }
                }
            , ProblemStrengthDegree (Degree 1.0)
            )
          , ( ProblemReasonName "pf-reason_3"
            , ForwardsReason
                { _frForwardsPremises =
                    [ FormulaPredication
                        { _formulaPredication = Predication (Symbol "C") [] }
                    ]
                , _frConclusion =
                    FormulaUnary
                      { _formulaUnaryOp = Negation
                      , _formulaUnaryFormula =
                          FormulaPredication
                            { _formulaPredication = Predication (Symbol "R") [] }
                      }
                }
            , ProblemStrengthDegree (Degree 1.0)
            )
          , ( ProblemReasonName "pf-reason_4"
            , ForwardsReason
                { _frForwardsPremises =
                    [ FormulaPredication
                        { _formulaPredication = Predication (Symbol "B") [] }
                    ]
                , _frConclusion =
                    FormulaPredication
                      { _formulaPredication = Predication (Symbol "C") [] }
                }
            , ProblemStrengthDegree (Degree 1.0)
            )
          , ( ProblemReasonName "pf-reason_5"
            , ForwardsReason
                { _frForwardsPremises =
                    [ FormulaPredication
                        { _formulaPredication = Predication (Symbol "A") [] }
                    ]
                , _frConclusion =
                    FormulaPredication
                      { _formulaPredication = Predication (Symbol "B") [] }
                }
            , ProblemStrengthDegree (Degree 1.0)
            )
          ]
      , _problemForwardsConclusiveReasons = []
      , _problemBackwardsPrimaFacieReasons = []
      , _problemBackwardsConclusiveReasons = []
      }
    @

TODO implement the rest of Oscar
-}
main ∷ IO ()
main = do
    problems ← readFileProblems combinedProblemsPath
    -- sequence_ $ ppPrint <$> problems
    let f = formulaFromText $ pack "(all x)((some z)(Q (g x) y) v ((some y)(~(H x y z) & (Q (g x) z)) v (J a b)))" in
      let u = uFormula f in do
        ppPrint f
        ppPrint u
        ppPrint $ formulaCode u
        ppPrint $ reasonCode u [Symbol $ pack "H"]

    sequence_ $ testOscar <$> problems
