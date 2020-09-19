-- {-# OPTIONS --cubical --prop --no-import-sorts #-}
module Stream where
-- open import Cubical.Core
-- open import Eq
-- import Iso
-- open import Iso using (_≃_)

-- private
--   variable
--     ℓ : Level
--     A B : Type ℓ

-- record Stream (A : Type) : Type where
--     coinductive
--     constructor _∷_
--     field
--         hd : A
--         tl : Stream A
-- open Stream
-- record _≈_ (xs ys : Stream A) : Type where
--     coinductive
--     constructor _∷_
--     field
--         hd≈ : hd xs ≡ hd ys
--         tl≈ : tl xs ≈ tl ys
-- open _≈_

-- bisim : {xs ys : Stream A} → xs ≈ ys → xs ≡ ys
-- hd (bisim xs≈ys i) = hd≈ xs≈ys i
-- tl (bisim xs≈ys i) =  bisim (tl≈ xs≈ys) i

-- bisim⁻¹ : {xs ys : Stream A} → xs ≡ ys → xs ≈ ys
-- hd≈ (bisim⁻¹ xs≡ys) i = hd (xs≡ys i)
-- tl≈ (bisim⁻¹ xs≡ys) = bisim⁻¹ (cong tl xs≡ys)

-- bisimIsoL : {xs ys : Stream A} (p : xs ≡ ys) → bisim (bisim⁻¹ p) ≡ p
-- hd (bisimIsoL {xs = xs} {ys = ys} xs≡ys i j) = hd (xs≡ys j)
-- tl (bisimIsoL {xs = xs} {ys = ys} xs≡ys i j) = bisimIsoL (λ k →  tl (xs≡ys k)) i j
-- bisimIsoR : {xs ys : Stream A} (p : xs ≈ ys) → bisim⁻¹ (bisim p) ≡ p
-- hd≈ (bisimIsoR xs≈ys i) j =  hd≈ xs≈ys j 
-- tl≈ (bisimIsoR xs≈ys i) = bisimIsoR (tl≈  xs≈ys) i

-- bisim≃equiv : {xs ys : Stream A} → (xs ≈ ys) ≃ (xs ≡ ys)
-- hd (Iso.to bisim≃equiv xs≈ys i) = hd≈ xs≈ys i
-- tl (Iso.to bisim≃equiv xs≈ys i) = Iso.to bisim≃equiv (tl≈ xs≈ys) i
-- hd≈ (Iso.from bisim≃equiv xs≡ys) i =  hd (xs≡ys i)
-- tl≈ (Iso.from bisim≃equiv xs≡ys) = Iso.from bisim≃equiv (cong tl xs≡ys)
-- hd (Iso.to∘from≡id bisim≃equiv xs≡ys i j) = hd (xs≡ys j)
-- tl (Iso.to∘from≡id bisim≃equiv xs≡ys i j) = {! tl (xs≡ys (i ∨ j))!}
-- Iso.from∘to≡id bisim≃equiv x i = {!!}
