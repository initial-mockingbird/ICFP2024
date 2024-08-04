-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Singletons.TH
-- Copyright   :  (C) 2013 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Ryan Scott
-- Stability   :  experimental
-- Portability :  non-portable
--
-- This module contains basic functionality for deriving your own singletons
-- via Template Haskell. Note that this module does not define any singled
-- definitions on its own. For a version of this module that comes pre-equipped
-- with several singled definitions based on the "Prelude", see
-- @Data.Singletons.Base.TH@ from the @singletons-base@ library.
--
----------------------------------------------------------------------------

module Data.Singletons.TH (


  -- * Basic singleton definitions
  module Data.Singletons,

  -- * Auxiliary definitions
  SDecide(..), (:~:)(..), Void, Refuted, Decision(..),

  SuppressUnusedWarnings(..)

 ) where


import Data.Singletons
import Data.Singletons.Decide
import Data.Singletons.TH.SuppressUnusedWarnings

