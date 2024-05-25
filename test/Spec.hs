{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NegativeLiterals #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Move brackets to avoid $" #-}

import ADT
import Action
import Interpreter


stdLib :: 
  ( ADTContext   m Env
  , ShowMContext m Env
  ) 
  => [A Env m ()]
stdLib = 
  [ "negate" := (Lambda @(Value Int) "x" $ Val 0 `Minus` Var @(Value Int) "x")
  , "add"    := 
    ( Lambda @(Value Int) "x" 
    $ Lambda @(Value Int) "y" 
    $ Var @(Value Int) "x" 
    `Minus` (Var @(Value Int ~> Value Int) "negate" `App` Var @(Value Int) "y")
    )
  , "eq"  := 
    ( Lambda @(Value Int) "x" 
    $ Lambda @(Value Int) "y" 
    $ If (Var @(Value Int) "x" `Less` Var @(Value Int) "y")
      cFalse
    $ If (Var @(Value Int) "y" `Less` Var @(Value Int) "x")
      cFalse
      cTrue
    )
  , "gt" :=
    ( Lambda @(Value Int) "x" 
    $ Lambda @(Value Int) "y" 
    $ If (Var @(Value Int) "x" `Less` Var @(Value Int) "y")
      cFalse
    $ If (Var @(Value Int ~> Value Int ~> Value Int) "eq" `App` Var @(Value Int) "y" `App` Var @(Value Int) "x")
      cFalse
      cTrue
    )
  , "lt" :=
    ( Lambda @(Value Int) "x" 
    $ Lambda @(Value Int) "y" 
    $ Less (Var @(Value Int) "x") (Var @(Value Int) "y")
    )
  , "lte" := 
    ( Lambda @(Value Int) "x" 
    $ Lambda @(Value Int) "y" 
    $ If (Var @(Value Int) "x" `Less` Var @(Value Int) "y")
      cTrue
    $ If (Var @(Value Int ~> Value Int ~> Value Int) "eq" `App` Var @(Value Int) "x" `App` Var @(Value Int) "y")
      cTrue
      cFalse
    )
  , "gte" := 
    ( Lambda @(Value Int) "x" 
    $ Lambda @(Value Int) "y" 
    $ If (Var @(Value Int ~> Value Int ~> Value Int) "eq" `App` Var @(Value Int) "x" `App` Var @(Value Int) "y")
      cTrue
    $ If (Var @(Value Int ~> Value Int ~> Value Int) "gt" `App` Var @(Value Int) "x" `App` Var @(Value Int) "y")
      cTrue
      cFalse
    )
  , "not" :=
    ( Lambda @(Value Int) "x" 
    $ If (Var @(Value Int ~> Value Int ~> Value Int) "eq" `App` Var @(Value Int) "x" `App` Val 0)
      cTrue
      (If (Var @(Value Int) "x" `Less` Val 0)
        cTrue
        cFalse
      )
      )
  , "sum"    := Lambda @(Value Int) "x" 
      ( If (Var @(Value Int) "x" `Less` Val 0)
        (Val 0)
        (  Var @(Value Int) "x" 
          `Minus` 
          ( Minus (Val 0)
            $ Var @(Value Int ~> Value Int) "sum" `App`  (Var @(Value Int) "x" `Minus` Val 1)
          ) 
        )

      )
  ]

ax4 :: 
  ( ADTContext   m Env
  , ShowMContext m Env
  ) 
  => [A Env m ()]
ax4 = stdLib ++
  [ Print (Var @(Value Int ~> Value Int) "sum")
  , "z0" := Var @(Value Int ~> Value Int) "sum" `App` Val -1
  , Print (Var @(Value Int) "z0") -- should be 0
  , "z1" := Var @(Value Int ~> Value Int) "sum" `App` Val 0
  , Print (Var @(Value Int) "z1") -- should be 0
  , "z2" := Var @(Value Int ~> Value Int) "sum" `App` Val 1
  , Print (Var @(Value Int) "z2") -- should be 1
  , "z3" := Var @(Value Int ~> Value Int) "sum" `App` Val 2
  , Print (Var @(Value Int) "z3") -- should be 3
  , "z4" := Var @(Value Int ~> Value Int) "sum" `App` Val 3
  , Print (Var @(Value Int) "z4") -- should be 6
  

  ]

ax5 :: 
  ( ADTContext   m Env
  , ShowMContext m Env
  ) 
  => [A Env m ()]
ax5 = stdLib ++
  [  "f" := 
      ( Lambda @(Lazy (Value Int)) "y" 
      $ Defer (Val 20 `Minus` Var @(Lazy (Value Int)) "y")
      )
  , "z0" := Var @(Lazy (Value Int) ~> Value Int) "f" `App` (Defer $ Defer $ Val 9)
  , Print (Var @(Value Int) "z0") -- should be 11
  , "y" :=  Val 99999
  , "z1" := Var @(Lazy (Value Int) ~> Value Int) "f" `App` (Defer $ Defer $ Val 9)
  , Print (Var @(Value Int) "z1") -- should be 11
  ]

ax6 :: 
  ( ADTContext   m Env
  , ShowMContext m Env
  ) 
  => [A Env m ()]
ax6 = stdLib ++
  [ "x" := Val 5
  , "f" := 
      ( Lambda @(Lazy (Value Int)) "y" 
      $ Defer (Var @(Value Int) "x" `Minus` Var @(Lazy (Value Int)) "y")
      )
  , "z0" := Var @(Lazy (Value Int) ~> Value Int) "f" `App` (Defer $ Defer $ Val 9)
  , Print (Var @(Value Int) "z0") -- should be -4
  , "x" :=. Val 100
  , "y" :=  Val 99999
  , "z1" := Var @(Lazy (Value Int) ~> Value Int) "f" `App` (Defer $ Defer $ Val 9)
  
  , Print (Var @(Value Int) "z1") -- should be 91
  ]

ax7 :: 
  ( ADTContext   m Env
  , ShowMContext m Env
  ) 
  => [A Env m ()]
ax7 = stdLib ++
  [ "x" := Val 5
  , "f" := 
      ( Lambda @(Lazy (Value Int)) "y" 
      $ Defer (Var @(Value Int) "x" `Minus` Var @(Lazy (Value Int)) "y")
      )
  , "z0" := Var @(Lazy (Value Int) ~> Value Int) "f" `App` (Defer $ Defer $ Var @(Value Int) "x")
  , Print (Var @(Value Int) "z0") -- should be 0
  , "x" :=. Val 100
  , "y" :=  Val -10000
  , "z1" := Var @(Lazy (Value Int) ~> Value Int) "f" `App` (Defer $ Defer $ Var @(Value Int) "x")
  , Print (Var @(Value Int) "z1") -- should be 0
  , "z2" := Var @(Lazy (Value Int) ~> Value Int) "f" `App` (Defer $ Defer $ Var @(Value Int) "y")
  , Print (Var @(Value Int) "z2") -- should be 10100
  ]



main :: IO ()
main = printAndExec ax7
