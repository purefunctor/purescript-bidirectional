module Bidirectional.Algorithm where

import Prelude

import Bidirectional.Types
  ( Context
  , Incomplete
  , PolyType
  , Type(..)
  , TypeCheck
  , TypeCheckError(..)
  , TypeVar
  , applyContext
  , assertWellFormedType
  , cExists
  , cForall
  , cMarker
  , cSolved
  , contextExists
  , dropMarker
  , fail
  , freeTypeVariables
  , freshTypeVar
  , insertAt
  , mkContext
  , monotype
  , orderedContext
  , snoc
  , solveContext
  , tExists
  , tFun
  , tVar
  , typeSubstitute
  )
import Data.List as List
import Data.Set as Set
import Data.Maybe (Maybe(..))

subtype ∷ Context Incomplete → PolyType → PolyType → TypeCheck (Context Incomplete)
subtype gamma a b = do
  assertWellFormedType gamma a
  assertWellFormedType gamma b
  case a, b of

    (TUnit _), (TUnit _) →
      pure gamma

    (TVar m _), (TVar n _)
      | m == n →
          pure gamma

    (TExists m _), (TExists n _)
      | m == n →
          pure gamma

    (TForall n t _), u → do
      n' ← freshTypeVar n

      let
        gamma' ∷ Context Incomplete
        gamma' = gamma <> mkContext [ cMarker n', cExists n' ]

        t' ∷ PolyType
        t' = typeSubstitute (tExists n') n t

      theta ← subtype gamma' t' u

      case dropMarker (cMarker n') theta of
        Just delta →
          pure delta
        Nothing →
          fail $ TypeCheckPanic "Could not drop marker!"

    t, (TForall n u _) → do
      n' ← freshTypeVar n

      let
        gamma' ∷ Context Incomplete
        gamma' = snoc gamma (cForall n')

        u' ∷ PolyType
        u' = typeSubstitute (tExists n') n u

      theta ← subtype gamma' t u'

      case dropMarker (cForall n') theta of
        Just delta →
          pure delta
        Nothing →
          fail $ TypeCheckPanic "Failed to drop marker!"

    (TFun x x' _), (TFun y y' _) → do
      theta ← subtype gamma y x
      subtype theta (applyContext theta x') (applyContext theta y')

    (TExists n _), t
      | List.elem n (contextExists gamma)
      , not $ Set.member n (freeTypeVariables t) ->
          instantiateLeft gamma n t

    t, (TExists n _)
      | List.elem n (contextExists gamma)
      , not $ Set.member n (freeTypeVariables t) ->
          instantiateRight gamma t n

    _, _ →
      fail $ TypeCheckPanic "Unimplemented case!"

instantiateLeft ∷ Context Incomplete → TypeVar → PolyType → TypeCheck (Context Incomplete)
instantiateLeft gamma alpha a = do
  assertWellFormedType gamma a
  case monotype a >>= solveContext gamma alpha of
    Just gamma' → pure gamma'
    Nothing → case a of
      (TExists beta _)
        | orderedContext gamma alpha beta →
            case solveContext gamma beta (tExists alpha) of
              Just gamma' →
                pure gamma'
              Nothing →
                fail $ TypeCheckPanic "Failed to solve existential."
        | otherwise →
            case solveContext gamma alpha (tExists beta) of
              Just gamma' →
                pure gamma'
              Nothing →
                fail $ TypeCheckPanic "Failed to solve existential."

      (TFun x y _) → do
        a' ← freshTypeVar alpha
        b' ← freshTypeVar alpha

        let
          gamma' ∷ Context Incomplete
          gamma' = insertAt gamma (cExists alpha)
            $ mkContext [ cExists b', cExists a', cSolved alpha (tFun (tVar a') (tVar b')) ]

        theta ← instantiateRight gamma' x a'
        instantiateLeft theta b' (applyContext theta y)

      (TForall beta b _) → do
        beta' ← freshTypeVar beta

        let
          gamma' ∷ Context Incomplete
          gamma' = gamma <> mkContext [ cForall beta' ]

          b' ∷ PolyType
          b' = typeSubstitute (tVar beta') beta b

        delta' ← instantiateLeft gamma' alpha b'
        case dropMarker (cForall beta') delta' of
          Just delta →
            pure delta
          Nothing →
            fail $ TypeCheckPanic "Failed to drop marker!"

      _ →
        fail $ TypeCheckPanic "Impossible case."

instantiateRight ∷ Context Incomplete → PolyType → TypeVar → TypeCheck (Context Incomplete)
instantiateRight gamma a alpha = do
  assertWellFormedType gamma a
  case monotype a >>= solveContext gamma alpha of
    Just gamma' → pure gamma'
    Nothing → case a of
      (TExists beta _)
        | orderedContext gamma alpha beta →
            case solveContext gamma beta (tExists alpha) of
              Just gamma' →
                pure gamma'
              Nothing →
                fail $ TypeCheckPanic "Failed to solve existential."
        | otherwise →
            case solveContext gamma alpha (tExists beta) of
              Just gamma' →
                pure gamma'
              Nothing →
                fail $ TypeCheckPanic "Failed to solve existential."

      (TFun x y _) → do
        a' ← freshTypeVar alpha
        b' ← freshTypeVar alpha

        let
          gamma' ∷ Context Incomplete
          gamma' = insertAt gamma (cExists alpha)
            $ mkContext [ cExists b', cExists a', cSolved alpha (tFun (tVar a') (tVar b')) ]

        theta ← instantiateLeft gamma' a' x
        instantiateRight theta (applyContext theta y) b'

      (TForall beta b _) → do
        beta' ← freshTypeVar beta

        let
          gamma' ∷ Context Incomplete
          gamma' = gamma <> mkContext [ cMarker beta', cExists beta' ]

          b' ∷ PolyType
          b' = typeSubstitute (tExists beta') beta b

        delta' ← instantiateRight gamma' b' alpha
        case dropMarker (cMarker beta') delta' of
          Just delta →
            pure delta
          Nothing →
            fail $ TypeCheckPanic "Failed to drop marker!"

      _ →
        fail $ TypeCheckPanic "Impossible case."
