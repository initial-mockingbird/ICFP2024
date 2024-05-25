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


module Examples where

import ADT
import Action
import Interpreter
import Lensy
import TypedMap
import Data.String (IsString(..))
import ShowM


ex1 :: 
  ( ADTContext   m Env
  , ShowMContext m Env
  ) 
  => E Env m (Value Int)
ex1 = If
  (Val 5 `Less` Val 4)
  (Val 1 `Minus` Var @(Value Int) "x")
  (Val 2 `Minus` Val 9)

ex2 :: 
  ( ADTContext   m Env
  , ShowMContext m Env
  ) 
  => E Env m (Value (Value Int -> Value Int))
ex2 = Lambda
  "x" 
  (Var @(Value Int) "x" `Minus` Val 1)

ex3 :: 
  ( ADTContext   m Env
  , ShowMContext m Env
  ) 
  => E Env m (Value Int)
ex3 = ex2 `App` (Val 1 `Minus` Var @(Value Int) "x")

ex4 :: 
  ( ADTContext   m Env
  , ShowMContext m Env
  ) 
  => E Env m (Value Int)
ex4 = ex2 `App` Val 1


ex5 :: 
  ( ADTContext   m Env
  , ShowMContext m Env
  ) 
  => E Env  m   (Value      (Value Int       -> Value (Value Int -> Value Int)))
ex5
  = Lambda "x" 
  $ Lambda "y"
  $ Var @(Value Int) "x" `Minus` Var @(Value Int)  "y"

ex6 :: 
  ( ADTContext   m Env
  , ShowMContext m Env
  ) 
  => E Env m (Value Int)
ex6 = App (App ex5 (Val 5)) (Val 3)

ex7 :: 
  ( ADTContext   m Env
  , ShowMContext m Env
  ) 
  => E Env m (Value Int)
ex7 = App (App ex5 (Val 5 `Minus` Val 10)) (Val 3)

ex8 :: 
  ( ADTContext   m Env
  , ShowMContext m Env
  ) 
  => E Env m (Value Int)
ex8 = App (App ex5 (Val 5)) (Val 3 `Minus` Val 10)

ex9 :: 
  ( ADTContext   m Env
  , ShowMContext m Env
  ) 
  => E Env m (Value Int)
ex9 = App (App ex5 (Val 5 `Minus` Val 10)) (Val 3 `Minus` Val 10)

ax1 :: 
  ( ADTContext   m Env
  , ShowMContext m Env
  ) 
  => [A Env m ()]
ax1 =
  [ "x"  := Val 5
  , "y" := Val 5
  -- , x := Val 9
  , Print (Val 5)
  ]

ax2 :: 
  ( ADTContext   m Env
  , ShowMContext m Env
  ) 
  => [A Env m ()]
ax2 =
  [ "x"  := Val 5
  , "y"  := Defer (Var @(Value Int) "x" )
  , "z0" := Var @(Value Int) "y"
  , "x"  :=. Val 9
  , "z1" := Var @(Value Int) "y"
  , Print (Var @(Value Int)  "z0") -- should be 5
  , Print (Var @(Value Int)  "z1") -- shoulb be 9
  ]

negate' ::
  ( ADTContext   m Env
  , ShowMContext m Env
  ) 
  => E Env m (Value (Value Int -> Value Int))
negate' = Lambda "x" $ Val 0 `Minus` Var @(Value Int) "x"


add :: forall m.
  ( ADTContext   m Env
  , ShowMContext m Env
  ) 
  => E Env m (Value
  (Value Int -> Value (Value Int -> Value Int)))
add = Lambda "x" $ Lambda "y" $ Minus
  (Var @(Value Int) "x")
  negatedY
  where
    negatedY :: E Env m (Value Int)
    negatedY = App (negate' @m) (Var @(Value Int) "y")



ax3 :: 
  ( ADTContext   m Env
  , ShowMContext m Env
  ) 
  => [A Env m ()]
ax3 =
  [ "x"      := Val 5
  , "y"      := Val 15
  , "negate" := negate'
  , "add"    := add
  , "z0"     := add `App` Val 5 `App` Val 15
  , "z1"     := add `App` Var @(Value Int) "x" `App` Val 15
  , "z2"     := add `App` Val 5 `App` Var @(Value Int) "y"
  , "z3"     := add `App` Var @(Value Int) "x" `App` Var @(Value Int) "y"
  , "z4"     := 
    Var @(Value (Value Int -> Value (Value Int -> Value Int))) "add" 
    `App` Var @(Value Int) "x" 
    `App` Var @(Value Int) "y"
  , "z5"     := 
    Var @(Value Int ~> (Value Int ~> Value Int)) "add" 
    `App` Var @(Value Int) "x" 
    `App` Var @(Value Int) "y"
  , "x+"     := 
    Var @(Value Int ~> (Value Int ~> Value Int)) "add" 
    `App` Var @(Value Int) "x"
  , "+y"     := Lambda @(Value Int) "z" 
    (Var @(Value Int ~> (Value Int ~> Value Int)) "add" 
    `App` Var @(Value Int) "z" 
    `App` Var @(Value Int) "y") 
  , Print (Var @(Value Int)  "z0") -- should be 20
  , Print (Var @(Value Int)  "z1") -- should be 20
  , Print (Var @(Value Int)  "z2") -- should be 20
  , Print (Var @(Value Int)  "z3") -- should be 20
  , Print (Var @(Value Int)  "z4") -- should be 20
  , Print (Var @(Value Int)  "z5") -- should be 20
  , Print (Var @(Value Int ~> Value Int) "x+") -- should be  \y -> add x y
  , Print (Var @(Value Int ~> Value Int) "+y") -- should be  \x -> add x y
  ]

ax4 :: 
  ( ADTContext   m Env
  , ShowMContext m Env
  ) 
  => [A Env m ()]
ax4 =
  [ "add" := add
  , "sum" := Lambda @(Value Int) "x" 
      ( If (Var @(Value Int) "x" `Less` Val 0)
        (Val 0)
        ( Var @(Value Int ~> Value Int ~> Value Int) "add"
          `App` Var @(Value Int) "x" 
          `App` 
          (Var @(Value Int ~> Value Int) "sum" `App`  (Var @(Value Int) "x" `Minus` Val 1)) 
        )

      )
  , Print (Var @(Value Int ~> Value Int) "sum")
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
ax5 =
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
ax6 =
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
ax7 =
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