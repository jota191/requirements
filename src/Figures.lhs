> {-# LANGUAGE FlexibleContexts #-}
> {-# LANGUAGE DataKinds #-}
> {-# LANGUAGE TypeOperators #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE UndecidableInstances #-}
> {-# LANGUAGE TypeFamilies #-}
> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE TypeApplications #-}
> {-# LANGUAGE ScopedTypeVariables #-}
> {-# LANGUAGE AllowAmbiguousTypes #-}
> {-# OPTIONS -Wno-missing-methods #-}

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
> type instance ShowTE R2 = Text "R2"
> type instance ShowTE R3 = Text "R3"

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
>   (Require (OpEqDim' (d == d') d d')) ctx
>   =>
>   Require (OpEqDim d d') ctx where
>   type ReqR (OpEqDim d d') = ReqR (OpEqDim' (d == d') d d')

> instance Require (OpEqDim' 'True  d d') ctx where {}

> instance
>   Require (OpError
>   (Text "Dimensional error:" :$$: Text "cannot combine figure of dimension "
>   :<>: ShowTE d :<>: Text " and dimension " :<>: ShowTE d')) ctx
>   => Require (OpEqDim' 'False d d') ctx


> instance
>   (Require (OpEqCol' (Equ c c') c c')) ctx
>   =>
>   Require (OpEqCol c c') ctx where
>   type ReqR (OpEqCol c c') = ReqR (OpEqCol' (Equ c c') c c')

> instance Require (OpEqCol' 'True  c c') ctx where {}


an sloppy error:

> instance
>   Require (OpError
>   (Text "Error, combined images must be of the same color")) ctx
>   => Require (OpEqCol' 'False c c') ctx


> combine' f f' = req (Proxy @( '[ Text "combining"] )) (OpCombine f f')

combine' (Circle 1 1 1) (Sphere 1 1 1 1) ->

• Error: Dimensional error:
         cannot combine figure of dimension R2 and dimension R3
  trace: combining..



combine' (Circle 1 1 1 :: Figure R2 (RGB 1 1 1))
         (Circle 1 1 1 :: Figure R2 (RGB 1 1 2)) ->

• Error: Error, combined images must be of the same color
  trace: combining..

> f1 = (Circle 2 2 2 :: Figure R2 (RGB 1 1 1))
> f2 = (Sphere 2 2 2 2:: Figure R3 (RGB 1 1 1))

> f = (CFigure $ \Proxy  -> f1) :: CFigure 'R2 ('RGB 1 1 1) '[]
> f' = CFigure $ \Proxy -> f2

> f'' = traceFig
>    (\(_ :: Proxy (Text "tracefig!!!!!" : ctx)) -> Proxy :: Proxy ctx ) $ f'

> tr = traceFig
>    (\(_ :: Proxy (ctx)) -> Proxy :: Proxy (Text "tracefig!!!!!" : ctx) )

> data CFigure d c (ctx :: [ErrorMessage])
>  = CFigure {mkCFig :: Proxy ctx -> Figure d c}


> combine''
>   :: (Require (OpEqDim' (d == d') d d') (Text "combine''" :ctx),
>       Require (OpEqCol' (Equ c c') c c') (Text "combine''" : ctx)) =>
>      CFigure d c ctx -> CFigure d' c' ctx' -> CFigure d c ctx
> combine'' (CFigure f1) (CFigure f2)
>   = CFigure $ \(a :: Proxy ctx) ->
>           req (Proxy :: Proxy (Text "combine''" : ctx))
>               (OpCombine (f1 a) (f2 Proxy))


> traceFig :: (Proxy ctx' -> Proxy ctx) -> CFigure d c ctx -> CFigure d c ctx'
> traceFig fctx (CFigure f) = CFigure $ f . fctx



Error:

 > g = combine'' (tr $ tr f) (tr $ tr f'') -- (tr $ tr $ tr $ combine'' f f) f''


Adding traces:

> addMsg :: Proxy msg -> Proxy (msg ': ctx) -> Proxy ctx 
> addMsg Proxy Proxy = Proxy

> f11 = traceFig (addMsg (Proxy @(Text "11"))) f
> f22 = traceFig (addMsg (Proxy @(Text "22"))) f


> fcomb = traceFig (addMsg (Proxy @(Text "comb"))) $ combine'' f11 f22

 > ferr = traceFig (addMsg (Proxy @(Text "err"))) $ combine'' fcomb f'
