{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE UnicodeSyntax #-}
module Oscar.Problem.Parser (
    -- * primitive API, in order of intended usage
    readProblemsTextFile,
    problemFromText,
    partitionProblemsText,
    statefulParseProblemNumber,
    statefulParseProblemDescription,
    problemSectionText,
    decodeGivenPremisesSection,
    decodeUltimateEpistemicInterestsSection,
    decodeForwardsPrimaFacieReasonSection,
    decodeForwardsConclusiveReasonSection,
    decodeBackwardsPrimaFacieReasonSection,
    decodeBackwardsConclusiveReasonSection,
    ) where

import Oscar.Problem.Internal.Internal
