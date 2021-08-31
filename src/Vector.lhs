
> {-# LANGUAGE UndecidableInstances  #-}
> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE FlexibleContexts      #-}
> {-# LANGUAGE ConstraintKinds       #-}
> {-# LANGUAGE FlexibleInstances     #-}
> {-# LANGUAGE TypeOperators         #-}
> {-# LANGUAGE TypeFamilies          #-}
> {-# LANGUAGE DataKinds             #-}
> {-# LANGUAGE PolyKinds             #-}
> {-# LANGUAGE KindSignatures        #-}
> {-# LANGUAGE GADTs                 #-}
> {-# LANGUAGE TypeApplications      #-}
> {-# LANGUAGE ScopedTypeVariables   #-}

> module Vector where

> import Data.Kind
> import Data.Proxy
> import GHC.TypeLits (Symbol, ErrorMessage(..))

> import Data.Type.Bool
> import Data.Type.Equality
> import Data.Type.Require

Firstly, we define size-indexed vectors, the stapple example of a
dependent Haskell type.

> data Nat = Z | S Nat
> type family Lt (m :: Nat) (n :: Nat) :: Bool where
>   Lt Z     (S n) = True
>   Lt _      Z    = False
>   Lt (S m) (S n) = Lt m n

> infixr 3 :< 

> data Vec (n :: Nat) (a :: Type) :: Type where
>   VNil :: Vec Z a
>   (:<) :: a -> Vec n a -> Vec (S n) a

And singletons for natutals:

> data SNat (n :: Nat) where
>   SZ :: SNat Z
>   SS :: SNat n -> SNat (S n)

With this we can implement a get function, that takes the element in a
given index of the vector. There are many ways to do that in a safe
way:

 * use a value of type 'Fin n' as the input for the index.

< get :: Fin n -> Vec n a -> a

 * use 'SNat' but also define a GADT 'Lt :: Nat -> Nat -> Type' that
   encodes a proof that the index is smaller than the vector size.

< get :: SNat n -> Lt n m -> Vec m a -> a

 * use a 'SNat', with no proof argument, and let index overflows to be
   ill-typed. Since this is Haskell all type information is static,
   meaning that we will know at compile time if the index is out of
   bound.

< get :: SNat n -> Vec m a -> a

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

We will decide according on the result of '(Lt n k)' . Since
typeclass resolution does not backtrack we need to have all
informartion on the head of the instance. This is a well known
trick. We build a wrapper where the first Boolean argument will
contain the result of the comparisson:

> data OpGet' (cmp :: Bool) (n :: Nat) (k :: Nat) (a :: Type) :: Type where
>    OpGet' :: Proxy cmp -> SNat n -> Vec k a -> OpGet' cmp n k a

Then, the wrapper instance:

> instance
>   Require (OpGet' (Lt n k) n k a) ctx
>   =>
>   Require (OpGet n k a) ctx where
>   type ReqR (OpGet n k a) =
>     ReqR (OpGet' (Lt n k) n k a)
>   req proxy (OpGet (n :: SNat n) (v :: Vec k a)) =
>     req proxy (OpGet' (Proxy @ (Lt n k)) n v)

Now we program the good cases:

> instance
>   Require (OpGet' 'True Z k a) ctx where
>   type ReqR (OpGet' 'True Z k a) = a
>   req _ (OpGet' _ SZ (a :< _)) = a

> instance
>   Require (OpGet n k a) ctx
>   => 
>   Require (OpGet' 'True (S n) (S k) a) ctx where
>   type ReqR (OpGet' 'True (S n) (S k) a) =
>     ReqR (OpGet n k a)
>   req ctx (OpGet' _ (SS n) (_ :< as)) = req ctx (OpGet n as)
 

Finally, when (Lt n k ~ 'False) we have an ill-typed get
operation.  We build a |Require| instance for the |OpError|
operation. When defining it, we have in scope 'n', 'k', and 'a',
everything needed to write a good type error using 'GHC.TypeLits'
infraestructure.


> instance
>   Require (OpError
>     (Text "Type error!, index out of bound:" :$$:
>     Text "Trying to lookup the " :<>: ShowTE n :<>: Text "th index" :$$:
>     Text "in a vector of size " :<>: ShowTE k
>     )
>           ) ctx
>   =>
>   Require (OpGet' False n k a) ctx where
>   type ReqR (OpGet' False n k a) = OpError (Text "lala")
>   req = error "unreachable"

> get n v = req (Proxy @ '[Text "getting"]) (OpGet n v)


> vecEx = 'a' :< 'b' :< 'c' :< 'd' :< VNil
> a = get SZ vecEx
> c = get (SS $ SS SZ) vecEx

< e = get (SS $ SS $ SS $ SS SZ) vecEx

--> 
  • Error: Type error!, index out of bound:
           Trying to lookup the ShowTE ('S ('S ('S ('S 'Z))))th index
           in a vector of size ShowTE ('S ('S ('S ('S 'Z))))
    trace: getting
