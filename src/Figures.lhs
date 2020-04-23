> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE UndecidableInstances #-}
> {-# LANGUAGE TypeFamilies #-}
> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE TypeApplications #-}

> module Figures where

> import Data.Type.Require
> import GHC.TypeLits
> import Data.Type.Bool
> import Data.Type.Equality
> import Data.Proxy

> data Color = RGB Nat Nat Nat

> type instance Equ (RGB r g b) (RGB r' g' b')
>   = r == r' && g == g' && b == b'

> data Dim = R2 | R3

> data family Figure (d :: Dim) (c :: Color)


> data instance Figure R2 c
>   = Circle Double Double Double -- center, radius? not important

> data instance Figure R3 c
>   = Sphere Double Double Double Double


> combine :: Figure d c -> Figure d c -> Figure d c
> combine f g = undefined

combine (Circle 1 1 1) (Sphere 1 1 1 1) ->

• Couldn't match type ‘'R3’ with ‘'R2’
  Expected type: Figure 'R2 c
  Actual type: Figure 'R3 c


> data OpEqDim  (d :: Dim)  (d' :: Dim)
> data OpEqDim' (b :: Bool) (d :: Dim)   (d' :: Dim)
> data OpEqCol  (c :: Color) (c' :: Color)
> data OpEqCol' (b :: Bool) (c :: Color) (c' :: Color)

> data OpCombine d d' c c' where
>   OpCombine :: Figure d c -> Figure d' c' -> OpCombine d d' c c'

> instance
>   ( Require (OpEqDim d d') ctx
>   , Require (OpEqCol c c') ctx
>   )
>   =>
>   Require (OpCombine d d' c c') ctx where
>   type ReqR (OpCombine d d' c c') =
>     Figure d c
>   req ctx (OpCombine f g) =
>     undefined

> instance
>   Require (OpEqDim d d') ctx where
>   type ReqR (OpEqDim d d') = ReqR (OpEqDim' (d == d') d d')

> instance Require (OpEqDim' 'True  d d') ctx where {}
>
> instance Require (OpEqCol c c') ctx where {}
> instance Require (OpEqCol' 'True  c c') ctx where {}
> instance Require (OpEqCol' 'False c c') ctx where {}

> instance
>   Require (OpError (Text "Dimensional error: cannot combine figure of dimension "
>   :<>: ShowT d :<>: Text " and dimension " :<>: ShowT d')) ctx
>   => Require (OpEqDim' 'False d d') ctx


> combine' f f' = req (Proxy @( '[ Text "combining.." ] )) (OpCombine f f')
