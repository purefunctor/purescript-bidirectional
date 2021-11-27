module Main where

import Bidirectional.Algorithm
import Bidirectional.Types
import Effect
import Prelude
import Data.Either (Either(..))

expr ∷ Expr
expr =
  ( EAbs (TermVar "g")
      ( EAbs (TermVar "f")
          ( EAbs (TermVar "x")
              ( EApp
                  (EVar (TermVar "g"))
                  ( EApp
                      (EVar (TermVar "f"))
                      (EVar (TermVar "x"))
                  )
              )
          )
      )
  )

type' ∷ PolyType
type' =
  ( tForall (TypeVar "a")
      ( tForall (TypeVar "b")
          ( tForall (TypeVar "c")
              ( tFun (tFun (tVar (TypeVar "b")) (tVar (TypeVar "c")))
                  ( tFun (tFun (tVar (TypeVar "a")) (tVar (TypeVar "b")))
                      (tFun (tVar (TypeVar "a")) (tVar (TypeVar "c")))
                  )
              )
          )
      )
  )

main ∷ Effect Unit
main = void $ runTypeCheck do
  synth mempty expr >>= case _ of
    { polytype } → logShow polytype

  check mempty expr type' >>= case _ of
    _ → log "Type checks."
