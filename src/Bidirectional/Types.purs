-- | Types for implementing bidirectional typechecking.
module Bidirectional.Types where

import Prelude
import Prim hiding (Type)

import Bidirectional.Leibniz (type (~), refl)
import Data.Either (Either)
import Data.Foldable (class Foldable)
import Data.Generic.Rep (class Generic)
import Data.List (List(..))
import Data.List as List
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.Traversable (traverse)
import Effect (Effect)
import Effect.Console as Console
import Prim as Prim
import Run (EFFECT, Run, liftEffect, runBaseEffect)
import Run.Except (EXCEPT, runExcept, throw)
import Run.State (STATE, evalState, get, put)
import Safe.Coerce (coerce)
import Type.Row (type (+))
import Unsafe.Coerce (unsafeCoerce)

-- | The expressions in our language.
-- |
-- | * EVar - a term variable
-- |
-- | * EUnit - single inhabitant
-- |
-- | * EAbs - lambda abstraction
-- |
-- | * EApp - lambda application
-- |
-- | * EAnn - expression annotation
data Expr
  = EVar TermVar
  | EUnit
  | EAbs TermVar Expr
  | EApp Expr Expr
  | EAnn Expr PolyType

derive instance Eq Expr
derive instance Generic Expr _
instance Show Expr where
  show e = genericShow e

newtype TermVar = TermVar String

derive instance Newtype TermVar _
derive newtype instance Eq TermVar
derive newtype instance Ord TermVar
derive newtype instance Show TermVar

exprSubstitute ∷ Expr → TermVar → Expr → Expr
exprSubstitute e n = case _ of
  EVar m
    | n == m → e
    | otherwise → EVar m
  EUnit → EUnit
  EAbs m b
    | n == m → EAbs m b
    | otherwise → EAbs m (exprSubstitute e n b)
  EApp x y → EApp (exprSubstitute e n x) (exprSubstitute e n y)
  EAnn x t → EAnn (exprSubstitute e n x) t

-- | Monomorphic types
foreign import data Mono ∷ Prim.Type

-- | Polymorphic types
foreign import data Poly ∷ Prim.Type

-- | The types of our language's expressions.
-- |
-- | * TUnit - the unit type
-- |
-- | * TVar - a universally quantifiable type variable
-- |
-- | * TExists - an existentially quantified type variable
-- |
-- | * TForall - introduces a universally quantified type variable
-- | :
-- | : This is the only constructor that can make a polymorphic type.
-- |
-- | * TFun - the function arrow type
data Type a
  = TUnit (a ~ a)
  | TVar TypeVar (a ~ a)
  | TExists TypeVar (a ~ a)
  | TForall TypeVar (Type Poly) (a ~ Poly)
  | TFun (Type a) (Type a) (a ~ a)

derive instance Eq (Type a)
derive instance Generic (Type a) _
instance Show (Type a) where
  show t = genericShow t

newtype TypeVar = TypeVar String

derive instance Newtype TypeVar _
derive newtype instance Eq TypeVar
derive newtype instance Ord TypeVar
derive newtype instance Show TypeVar

-- | Monomorphic types
type MonoType = Type Mono

-- | Polymorphic types
type PolyType = Type Poly

tUnit ∷ ∀ a. Type a
tUnit = TUnit refl

tVar ∷ ∀ a. TypeVar → Type a
tVar n = TVar n refl

tExists ∷ ∀ a. TypeVar → Type a
tExists n = TExists n refl

tForall ∷ TypeVar → Type Poly → Type Poly
tForall n t = TForall n t refl

tFun ∷ ∀ a. Type a → Type a → Type a
tFun a b = TFun a b refl

-- | Determine whether a type is a monotype.
monotype ∷ ∀ a. Type a → Maybe MonoType
monotype = case _ of
  TUnit _ → Just tUnit
  TVar n _ → Just $ tVar n
  TExists n _ → Just $ tExists n
  TForall _ _ _ → Nothing
  TFun n e _ → tFun <$> monotype n <*> monotype e

-- | Determine whether a type is a polytype.
polytype ∷ ∀ a. Type a → PolyType
polytype = case _ of
  TUnit _ → tUnit
  TVar n _ → tVar n
  TExists n _ → tExists n
  TForall n t _ → tForall n t
  TFun n e _ → tFun (polytype n) (polytype e)

-- | Type substitutions
typeSubstitute ∷ ∀ a. Type a → TypeVar → Type a → Type a
typeSubstitute t m = case _ of
  TUnit _ → tUnit

  TVar n _
    | m == n → t
    | otherwise → tVar n

  TExists n _
    | m == n → t
    | otherwise → tExists n

  TForall n u _
    | m == n →
        unsafeCoerce $ tForall n u
    | otherwise →
        unsafeCoerce $ tForall n (unsafeCoerce (typeSubstitute t m (unsafeCoerce u)))

  TFun u v _ → tFun (typeSubstitute t m u) (typeSubstitute t m v)

-- | Find all free type variables
freeTypeVariables ∷ ∀ a. Type a → Set TypeVar
freeTypeVariables = case _ of
  TUnit _ → Set.empty
  TVar v _ → Set.singleton v
  TForall v t _ → Set.delete v $ freeTypeVariables t
  TExists v _ → Set.singleton v
  TFun a b _ → freeTypeVariables a <> freeTypeVariables b

-- | Elements that inhabit the context type consumsed by the algorithm.
-- |
-- | * CVar - a term variable whose type is known
-- |
-- | * CForall - a universally quantifiable type variable
-- |
-- | * CExists - an existentially quantified type variable
-- | :
-- | : This is used in the context as a "placeholder" for unknown types.
-- | : If the compiler is able to synthesize a type for this existential,
-- | : it is then marked with CSolved. If present within a context, it's
-- | : considered incomplete.
-- |
-- | * CSolved - a solved existential variable
-- |
-- | * CMarker - a placeholder element for deconstructing the context
data ContextElement a
  = CVar TermVar PolyType (a ~ a)
  | CForall TypeVar (a ~ a)
  | CExists TypeVar (a ~ Incomplete)
  | CSolved TypeVar MonoType (a ~ a)
  | CMarker TypeVar (a ~ a)

derive instance Eq (ContextElement a)
derive instance Generic (ContextElement a) _
instance Show (ContextElement a) where
  show e = genericShow e

-- | Complete contexts and elements
foreign import data Complete ∷ Prim.Type

-- | Incomplete contexts and elements
foreign import data Incomplete ∷ Prim.Type

cForall ∷ ∀ a. TypeVar → ContextElement a
cForall n = CForall n refl

cVar ∷ ∀ a. TermVar → PolyType → ContextElement a
cVar n t = CVar n t refl

cExists ∷ TypeVar → ContextElement Incomplete
cExists n = CExists n refl

cSolved ∷ ∀ a. TypeVar → MonoType → ContextElement a
cSolved n t = CSolved n t refl

cMarker ∷ ∀ a. TypeVar → ContextElement a
cMarker n = CMarker n refl

-- | The context consumed by our bidirectional typechecking algorithm.
-- |
-- | A context is a stack of context elements that sort of represent
-- | the current state of the typechecking machine. It's passed around
-- | as inputs for and outputs from typing judgments.
newtype Context a = Context (List (ContextElement a))

derive instance Newtype (Context a) _
derive newtype instance Show (Context a)
derive newtype instance Eq (Context a)

instance Semigroup (Context a) where
  append (Context a) (Context b) = Context (b <> a)

instance Monoid (Context a) where
  mempty = Context Nil

-- | Create a context from a list
mkContext ∷ ∀ f a. Foldable f ⇒ f (ContextElement a) → Context a
mkContext = Context <<< List.reverse <<< List.fromFoldable

-- | Push an element to the context
snoc ∷ ∀ a. Context a → ContextElement a → Context a
snoc (Context c) e = Context $ Cons e c

-- | Keep all elements to the right of a provided marker element,
-- | removing all previous elements and itself.
dropMarker ∷ ∀ a. ContextElement a → Context a → Maybe (Context a)
dropMarker m (Context c) = Context <$> (List.tail $ List.dropWhile (_ /= m) c)

-- | Break apart a context into two parts using a marker. `init`
-- | contains all elements to the left while `rest` contains the
-- | items to the right of it.
breakMarker ∷ ∀ a. ContextElement a → Context a → { init ∷ Context a, rest ∷ Context a }
breakMarker m (Context c) =
  let
    { init, rest } = List.span (_ /= m) c
  in
    { init: Context (List.drop 1 rest)
    , rest: Context init
    }

-- | Assert whether a context is free from unsolved existentials.
purifyContext ∷ ∀ a. Context a → Maybe (Context Complete)
purifyContext (Context c) = Context <$> traverse purifyElement c
  where
  purifyElement ∷ ContextElement a → Maybe (ContextElement Complete)
  purifyElement = case _ of
    CExists _ _ → Nothing
    e → Just (unsafeCoerce e)

-- | Collect all type variables inside annotations.
contextVars ∷ ∀ a. Context a → List TermVar
contextVars (Context c) = List.foldl isVar Nil c
  where
  isVar xs (CVar x _ _) = Cons x xs
  isVar xs _ = xs

-- | Collect all type variables inside foralls.
contextForalls ∷ ∀ a. Context a → List TypeVar
contextForalls (Context c) = List.foldl isForall Nil c
  where
  isForall xs (CForall x _) = Cons x xs
  isForall xs _ = xs

-- | Collect all type variables inside existentials.
contextExists ∷ ∀ a. Context a → List TypeVar
contextExists (Context c) = List.foldl isExists Nil c
  where
  isExists xs (CExists x _) = Cons x xs
  isExists xs (CSolved x _ _) = Cons x xs
  isExists xs _ = xs

-- | Collect all unsolved existentials
contextUnsolved ∷ ∀ a. Context a → List TypeVar
contextUnsolved (Context c) = List.foldl isExists Nil c
  where
  isExists xs (CExists x _) = Cons x xs
  isExists xs _ = xs

-- | Collect all type variables inside markers.
contextMarkers ∷ ∀ a. Context a → List TypeVar
contextMarkers (Context c) = List.foldl isMarker Nil c
  where
  isMarker xs (CMarker x _) = Cons x xs
  isMarker xs _ = xs

-- | Determine whether a type is well-formed under some context.
wellFormedType ∷ ∀ a. Context Incomplete → Type a → Boolean
wellFormedType gamma = case _ of
  TUnit _ →
    true
  TVar n _ →
    List.elem n (contextForalls gamma)
  TExists n _ →
    List.elem n (contextExists gamma)
  TForall n t _ →
    wellFormedType (snoc gamma (cForall n)) t
  TFun a b _ →
    wellFormedType gamma a && wellFormedType gamma b

-- | Determine whether a context is well-formed.
wellFormedContext ∷ Context Incomplete → Boolean
wellFormedContext (Context c) = case c of
  Nil → true
  (Cons e es) →
    let
      gamma ∷ Context Incomplete
      gamma = Context es

      head ∷ Boolean
      head =
        case e of
          CVar n t _ →
            List.notElem n (contextVars gamma) && wellFormedType gamma t
          CForall n _ →
            List.notElem n (contextForalls gamma)
          CExists n _ →
            List.notElem n (contextExists gamma)
          CSolved n t _ →
            List.notElem n (contextExists gamma) && wellFormedType gamma t
          CMarker n _ →
            List.notElem n (contextMarkers gamma)
    in
      head && wellFormedContext gamma

-- | Performs context application over some type. When encountering an
-- | existential variable, try to find its solution inside of the
-- | context. After which the solved type is further applied.
applyContext ∷ ∀ a. Context a → PolyType → PolyType
applyContext gamma@(Context c) = case _ of

  TUnit _ → tUnit

  TVar n _ → tVar n

  TExists n _ →
    let
      findSolved ∷ ContextElement a → Maybe PolyType
      findSolved (CSolved m t _)
        | n == m = Just (polytype t)
      findSolved _ = Nothing
    in
      case List.findMap findSolved c of
        Just solved → applyContext gamma solved
        Nothing → tExists n

  TForall n t _ →
    tForall n (applyContext gamma t)

  TFun a b _ →
    tFun (applyContext gamma a) (applyContext gamma b)

-- | Attempt to solve an existential variable inside of a context.
solveContext ∷ Context Incomplete → TypeVar → MonoType → Maybe (Context Incomplete)
solveContext gamma alpha tau =
  let
    { init: gammaL, rest: gammaR } = breakMarker (cExists alpha) gamma
  in
    if wellFormedType gammaL tau then
      Just $ gammaL <> mkContext [ cSolved alpha tau ] <> gammaR
    else
      Nothing

-- | Determine whether two type variables appear in order in the context.
orderedContext ∷ Context Incomplete → TypeVar → TypeVar → Boolean
orderedContext gamma alpha beta =
  case dropMarker (cExists beta) gamma of
    Just gammaL →
      List.elem alpha (contextExists gammaL)
    Nothing →
      false

-- | Take some marker and add more elements into it.
insertAt ∷ Context Incomplete → ContextElement Incomplete → Context Incomplete → Context Incomplete
insertAt gamma m theta =
  let
    { init: gammaL, rest: gammaR } = breakMarker m gamma
  in
    gammaL <> theta <> gammaR

data TypeCheckError
  = TypeCheckPanic String

derive instance Generic TypeCheckError _
instance Show TypeCheckError where
  show e = genericShow e

type TypeCheck = Run
  ( STATE Int
      + EXCEPT TypeCheckError
      + EFFECT
      + ()
  )

runTypeCheck ∷ ∀ a. TypeCheck a → Effect (Either TypeCheckError a)
runTypeCheck = runBaseEffect <<< runExcept <<< evalState 0

fresh ∷ TypeCheck Int
fresh = do
  n ← get
  put (n + 1)
  pure n

freshName ∷ String → TypeCheck String
freshName n = append n <<< show <$> fresh

freshTypeVar ∷ TypeVar → TypeCheck TypeVar
freshTypeVar = coerce freshName

freshTermVar ∷ TermVar → TypeCheck TermVar
freshTermVar = coerce freshName

peek ∷ TypeCheck Int
peek = get

fail ∷ ∀ a. TypeCheckError → TypeCheck a
fail = throw

log ∷ String → TypeCheck Unit
log = liftEffect <<< Console.log

logShow ∷ ∀ a. Show a ⇒ a → TypeCheck Unit
logShow = liftEffect <<< Console.logShow

assertWellFormedType ∷ ∀ a. Context Incomplete → Type a → TypeCheck Unit
assertWellFormedType c t =
  if wellFormedType c t then
    pure unit
  else
    fail $ TypeCheckPanic "Types are not well formed!"

assertWellFormedContext ∷ Context Incomplete → TypeCheck Unit
assertWellFormedContext c =
  if wellFormedContext c then
    pure unit
  else
    fail $ TypeCheckPanic "Context is not well formed!"
