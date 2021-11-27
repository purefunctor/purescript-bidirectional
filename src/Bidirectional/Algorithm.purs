module Bidirectional.Algorithm where

import Prelude

import Bidirectional.Types
  ( Context(..)
  , ContextElement(..)
  , Expr(..)
  , Incomplete
  , PolyType
  , TermVar(..)
  , Type(..)
  , TypeCheck
  , TypeCheckError(..)
  , TypeVar(..)
  , applyContext
  , assertWellFormedContext
  , assertWellFormedType
  , breakMarker
  , cExists
  , cForall
  , cMarker
  , cSolved
  , cVar
  , contextExists
  , contextUnsolved
  , dropMarker
  , exprSubstitute
  , fail
  , freeTypeVariables
  , freshTermVar
  , freshTypeVar
  , insertAt
  , mkContext
  , monotype
  , orderedContext
  , snoc
  , solveContext
  , tExists
  , tForall
  , tFun
  , tUnit
  , tVar
  , typeSubstitute
  )
import Data.List as List
import Data.List.Lazy as Lazy
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Tuple (uncurry)

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
      | m == n
      , List.elem m (contextExists gamma) →
          pure gamma

    (TFun x x' _), (TFun y y' _) → do
      theta ← subtype gamma y x
      subtype theta (applyContext theta x') (applyContext theta y')

    t, (TForall n u _) → do
      n' ← freshTypeVar n

      let
        gamma' ∷ Context Incomplete
        gamma' = snoc gamma (cForall n')

        u' ∷ PolyType
        u' = typeSubstitute (tVar n') n u

      theta ← subtype gamma' t u'

      case dropMarker (cForall n') theta of
        Just delta →
          pure delta
        Nothing →
          fail $ TypeCheckPanic "Failed to drop marker!"

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

    (TExists n _), t
      | List.elem n (contextExists gamma)
      , not $ Set.member n (freeTypeVariables t) →
          instantiateLeft gamma n t

    t, (TExists n _)
      | List.elem n (contextExists gamma)
      , not $ Set.member n (freeTypeVariables t) →
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
            $ mkContext
                [ cExists b'
                , cExists a'
                , cSolved alpha
                    ( tFun (tExists a')
                        (tExists b')
                    )
                ]

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
    Just gamma' → do
      pure gamma'
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
            $ mkContext
                [ cExists b'
                , cExists a'
                , cSolved alpha (tFun (tExists a') (tExists b'))
                ]

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

check ∷ Context Incomplete → Expr → PolyType → TypeCheck (Context Incomplete)
check gamma e t = do
  assertWellFormedType gamma t
  case e, t of
    EUnit, (TUnit _) → do
      pure gamma

    e', (TForall n u _) → do
      n' ← freshTypeVar n

      let
        gamma' ∷ Context Incomplete
        gamma' = snoc gamma (cForall n')

        u' ∷ PolyType
        u' = typeSubstitute (tVar n') n u

      theta ← check gamma' e' u'
      case dropMarker (cForall n') theta of
        Just delta →
          pure delta
        Nothing →
          fail $ TypeCheckPanic "Failed to drop marker!"

    (EAbs n c), (TFun a b _) → do
      n' ← freshTermVar n

      let
        gamma' ∷ Context Incomplete
        gamma' = snoc gamma (cVar n' a)

        c' ∷ Expr
        c' = exprSubstitute (EVar n') n c

      theta ← check gamma' c' b
      case dropMarker (cVar n' a) theta of
        Just delta →
          pure delta
        Nothing →
          fail $ TypeCheckPanic "Failed to drop marker!"

    e', t' → do
      { context: theta, polytype } ← synth gamma e'
      subtype theta (applyContext theta polytype) (applyContext theta t')

synth
  ∷ Context Incomplete → Expr → TypeCheck ({ context ∷ Context Incomplete, polytype ∷ PolyType })
synth gamma@(Context c) e = do
  assertWellFormedContext gamma
  case e of
    EUnit →
      pure
        { context: gamma
        , polytype: tUnit
        }
    EVar n → do
      let
        findVar ∷ ContextElement Incomplete → Maybe PolyType
        findVar (CVar m t _) | n == m = Just t
        findVar _ = Nothing

      case List.findMap findVar c of
        Just t →
          pure
            { context: gamma
            , polytype: t
            }
        Nothing →
          fail $ TypeCheckPanic "Could not synthesize type."

    EAbs n@(TermVar v) b → do
      n' ← freshTermVar n
      alpha ← freshTypeVar (TypeVar v)
      beta ← freshTypeVar (TypeVar v)

      let
        gamma' ∷ Context Incomplete
        gamma' = gamma <> mkContext
          [ cMarker alpha, cExists alpha, cExists beta, cVar n' (tExists alpha) ]

        b' ∷ Expr
        b' = exprSubstitute (EVar n') n b

      theta ← check gamma' b' (tExists beta)
      case breakMarker (cMarker alpha) theta of
        { init, rest } → do
          let
            tau = applyContext rest (tFun (tExists alpha) (tExists beta))
            uns = Lazy.fromFoldable $ contextUnsolved rest
          uvr ← Lazy.replicateM (Lazy.length uns) (freshTypeVar (TypeVar v))
          let typeSubts = flip $ Lazy.foldr $ uncurry typeSubstitute
          pure
            { context: init
            , polytype: Lazy.foldr tForall (typeSubts (Lazy.zip (map tVar uvr) uns) tau) uvr
            }
    EApp f x → do
      { context: theta, polytype } ← synth gamma f
      synthApp theta (applyContext theta polytype) x

    _ →
      fail $ TypeCheckPanic "Impossible case."

synthApp
  ∷ Context Incomplete
  → PolyType
  → Expr
  → TypeCheck ({ context ∷ Context Incomplete, polytype ∷ PolyType })
synthApp gamma t e = do
  assertWellFormedType gamma t
  case t of
    TForall alpha a _ → do
      alpha' ← freshTypeVar alpha

      let
        gamma' = snoc gamma (cExists alpha')

        a' = typeSubstitute (tExists alpha') alpha a

      synthApp gamma' a' e

    TExists a _ → do
      a' ← freshTypeVar a
      b' ← freshTypeVar a

      let
        gamma' ∷ Context Incomplete
        gamma' = insertAt gamma (cExists a)
          $ mkContext [ cExists b', cExists a', cSolved a (tFun (tExists a') (tExists b')) ]

      delta ← check gamma' e (tExists a')
      pure
        { context: delta
        , polytype: tExists b'
        }

    TFun a b _ → do
      delta ← check gamma e a
      pure
        { context: delta
        , polytype: b
        }
    _ →
      fail $ TypeCheckPanic "Impossible case."
