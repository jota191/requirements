{-|
Module      : Data.Type.Require
Description : A small framework to manage user defined type errors.
Copyright   : (c) Juan García-Garland, Marcos Viera, 2019, 2020
License     : GPLv3
Maintainer  : jpgarcia@fing.edu.uy
Stability   : experimental
Portability : POSIX

This module implements a simple framework to manage Type Errors when
doing type-level progamming in Haskell.

* General Description:

This was originally developed for the AspectAG library (attribute
grammars in the form of an EDSL).
Both in AspectAG and in our Record library (which is again, an abstraction
synthesized from the AspectAG) are examples of how to use
'Require'.
Some simpler examples are presented in Example modules in this package.

Let us inline one in this documentation file:

Firstly, we define size-indexed vectors, the stapple example of a
dependent Haskell type.

> data Vec (n :: Nat) (a :: Type) :: Type where
>   VNil :: Vec 0 a
>   (:<) :: a -> Vec n a -> Vec (1 + n) a

And singletons for natutals:

> data SNat (n :: Nat) where
>   SZ :: SNat 0
>   SS :: SNat n -> SNat (1 + n)

With this we can implement a get function, that takes the element in a
given index of the vector. There are many ways to do that in a safe
way:

 * use a value of type 'Fin n' as the input for the index.

> get :: Fin n -> Vec n a -> a

 * use 'SNat' but also define a GADT 'Lt :: Nat -> Nat -> Type' that
   encodes a proof that the index is smaller than the vector size.

> get :: SNat n -> Lt n m -> Vec m a -> a

 * use a 'SNat', with no proof argument, and let index overflows to be
   ill-typed. Since this is Haskell all type information is static,
   meaning that we will know at compile time if the index is out of
   bound.

> get :: SNat n -> Vec m a -> a

In the latter approach is where |Require| fits. The require
infrastructure allows us to have nice type errors when an out of bound
lookup occurs, instead of something like 'no instance for ..'

We introduce an /operation/ for the vector, the get operation. This
is a product datatype having all information we need: an index and
vector:

> data OpGet (n :: Nat) (k :: Nat) (a :: Type) :: Type  where
>    OpGet :: SNat n -> Vec k a -> OpGet n k a

This operation /requires/ some properties about its arguments, in this
case, that the index given is less than vector's length. A well-typed
lookup will satisfy the constraint 'Require (OpGet n k a)'

We will decide according on the result of '(<=? (n + 1) k)' . Since
typeclass resolution does not backtrack we need to have all
informartion on the head of the instance. This is a well known
trick. We build a wrapper where the first Boolean argument will
contain the result of the comparisson:

> data OpGet' (cmp :: Bool) (n :: Nat) (k :: Nat) (a :: Type) :: Type where
>    OpGet' :: Proxy cmp -> SNat n -> Vec k a -> OpGet' cmp n k a

Then, the wrapper instance:

> instance
>   Require (OpGet' ((n + 1) <=? k) n k a) ctx
>   =>
>   Require (OpGet n k a) ctx where
>   type ReqR (OpGet n k a) =
>     ReqR (OpGet' (n + 1 <=? k) n k a)
>   req proxy (OpGet (n :: SNat n) (v :: Vec k a)) =
>     req proxy (OpGet' (Proxy @ (n + 1 <=? k)) n v)

Now we program the good cases, we show only the base case, the
recursive case is an excercise for the reader:

> instance
>   Require (OpGet' 'True 0 k a) ctx where
>   type ReqR (OpGet' 'True 0 k a) = a
>   req _ (OpGet' _ SZ (a :< _)) = a

Finally, when (n + 1 <=? k ~ 'False) we have an ill-typed get
operation.  We build a |Require| instance for the |OpError|
operation. When defining it, we have in scope 'n', 'k', and 'a',
everything needed to write a good type error using 'GHC.TypeLits'
infraestructure.


> instance
>   Require (OpError (Text "Type error!" index out of bound")) ctx
>   =>
>   Require (OpGet' False n k a) ctx where
>   type ReqR (OpGet' False n k a) = OpError (Text "lala")
>   req = error "unreachable"



-}

{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE ScopedTypeVariables   #-}

module Data.Type.Require
 
 where

import Data.Kind
import Data.Proxy
import GHC.TypeLits
import Data.Type.Bool
import Data.Type.Equality

-- | Require class. Use this when a /dependent type/ (/a la/ Haskell)
-- /requires/ some type level property for a function to be defined to
-- program nice type errors.
class
  Require (op :: Type) (ctx :: [ErrorMessage]) where
  type ReqR op :: Type
  req :: Proxy ctx -> op -> ReqR op


-- | OpError operation. A 'Require' call to this operation produces a
-- type error showing the argument message.
data OpError (m :: ErrorMessage) :: Type where {}


-- | Failing and printing of an |OpError| requirement.
instance (TypeError
          (Text "Error: " :<>: m :$$:
           If (IsEmptyCtx ctx)
              (Text "")
              (Text "trace: " :<>: ShowCTX ctx)))
  =>
  Require (OpError m) ctx where
  type ReqR (OpError m) = ()
  req _ _ = error "unreachable"

type family IsEmptyCtx (ms :: [ErrorMessage]) :: Bool where
  IsEmptyCtx '[] = True
  IsEmptyCtx (m ': ms) = IsEmptyMsg m && IsEmptyCtx ms

type family IsEmptyMsg (m :: ErrorMessage) :: Bool where
  IsEmptyMsg (Text "") = True
  IsEmptyMsg (l :<>: r) = IsEmptyMsg l && IsEmptyMsg r
  IsEmptyMsg other = False

-- -- | Formatting of context printing.
type family ShowCTX (ctx :: [ErrorMessage]) :: ErrorMessage where
  ShowCTX '[] = Text ""
  ShowCTX (m ': ms) = m :$$: ShowCTX ms
  
  
type family FromText (t :: ErrorMessage) :: Symbol where
  FromText (Text t) = t

-- | Show for types
type family ShowTE (t :: k) :: ErrorMessage
type instance ShowTE (t :: Type) = ShowType t
type instance ShowTE (t :: Symbol) = Text t



-- | A common constraint is to have a |Requirement| to be fullfilled,
-- and something to unify with the result of the operation.  
type RequireR (op :: Type) (ctx:: [ErrorMessage]) (res :: Type)
     = (Require op ctx, ReqR op ~ res)

-- | 
type RequireEq (t1 :: k )(t2 :: k) (ctx:: [ErrorMessage])
    = (Require (OpEq t1 t2) ctx, t1 ~ t2)


-- Exported operators.

-- | Equality operator.
data OpEq t1 t2

-- | implementation of Require instance for equality (the type family
-- in the context implements the logic)
instance RequireEqRes t1 t2 ctx
  => Require (OpEq t1 t2) ctx where
  type ReqR (OpEq t1 t2) = ()
  req = undefined

-- | comparisson of types, given a trivially satisfying constraint if
-- they are equal, or requiring an |OpError| otherwise.
type family RequireEqRes (t1 :: k) (t2 :: k)
                     (ctx :: [ErrorMessage]) ::  Constraint where
  RequireEqRes t1 t2 ctx = If (t1 `Equal` t2) (() :: Constraint)
    (Require (OpError (Text "\n   " :<>: ShowTE t1
                       :<>: Text "\n/= " :<>: ShowTE t2)) ctx)

type family Equal (a :: k) (b :: k') :: Bool where
  Equal a a = True
  Equal a b = False


-- | overloaded type equality
type family Equ (a :: k) (b :: k) :: Bool


emptyCtx = Proxy :: Proxy '[ Text ""]


type Lala = ShowCTX
               '[ ((('GHC.TypeLits.Text "syndef("
                     'GHC.TypeLits.:<>: ((('GHC.TypeLits.Text "Attribute "
                                           'GHC.TypeLits.:<>: 'GHC.TypeLits.Text "cst")
                                          'GHC.TypeLits.:<>: 'GHC.TypeLits.Text ":")
                                         'GHC.TypeLits.:<>: 'GHC.TypeLits.ShowType String))
                    'GHC.TypeLits.:<>: 'GHC.TypeLits.Text ", ")
                   'GHC.TypeLits.:<>: ((('GHC.TypeLits.Text "Non-Terminal "
                                         'GHC.TypeLits.:<>: 'GHC.TypeLits.Text "Rose")
                                        'GHC.TypeLits.:<>: 'GHC.TypeLits.Text "::Production ")
                                       'GHC.TypeLits.:<>: 'GHC.TypeLits.Text "Node"))
                  'GHC.TypeLits.:<>: 'GHC.TypeLits.Text ")" ]
