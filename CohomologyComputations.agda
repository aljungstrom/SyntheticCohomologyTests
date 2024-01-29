{-# OPTIONS --safe --cubical #-}
module CohomologyComputations where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Int
open import Cubical.Data.Fin

open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Torus
open import Cubical.HITs.Wedge
open import Cubical.HITs.RPn
open import Cubical.HITs.KleinBottle renaming (KleinBottle to K² ; rec to K²Fun)
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.EilenbergMacLane1 as EM1

open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.EilenbergMacLane.Properties

open import Cubical.Cohomology.EilenbergMacLane.Base
open import Cubical.Cohomology.EilenbergMacLane.CupProduct
open import Cubical.Cohomology.EilenbergMacLane.Groups.Sn
open import Cubical.Cohomology.EilenbergMacLane.Groups.RP2
open import Cubical.Cohomology.EilenbergMacLane.Rings.RP2
open import Cubical.Cohomology.EilenbergMacLane.Groups.Torus
open import Cubical.Cohomology.EilenbergMacLane.Groups.Wedge
open import Cubical.Cohomology.EilenbergMacLane.Groups.KleinBottle
open import Cubical.Cohomology.EilenbergMacLane.Groups.RPinf
open import Cubical.Cohomology.EilenbergMacLane.Rings.RPinf



open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.IntMod
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.IntMod

open import Cubical.Algebra.Ring




open import Cubical.HITs.Susp
open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.Pushout

open import Cubical.Data.Fin.Arithmetic
open import Cubical.Data.Nat.Order
open import Cubical.Data.Int renaming (_+_ to _+ℤ_ ; _-_ to _-ℤ_ ;  _·_ to _·ℤ_)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)



private
  T² = S¹ × S¹
  S²∨S¹∨S¹ = S₊∙ 2 ⋁ (S₊∙ 1 ⋁ S₊∙ 1 , inl base)
  RP∞ = EM ℤ/2 1

  open import Cubical.Data.Int as Int
    renaming ( ℤ to ℤ ; _+_ to _+ℤ_; _·_ to _·ℤ_ ; -_ to -ℤ_)

  module _ where
    open CommRingStr using (0r ; 1r ; _+_ ; _·_ ; -_; isCommRing)

    ℤCommRing : CommRing ℓ-zero
    fst ℤCommRing = ℤ
    0r (snd ℤCommRing) = 0
    1r (snd ℤCommRing) = 1
    CommRingStr._+_ (snd ℤCommRing) = _+ℤ_
    CommRingStr._·_ (snd ℤCommRing) = _·ℤ_
    CommRingStr.- snd ℤCommRing = -ℤ_
    isCommRing (snd ℤCommRing) = isCommRingℤ
      where
      isCommRingℤ : _ --_ IsCommRing 0 1 _+ℤ_ _·ℤ_ -ℤ_
      isCommRingℤ = makeIsCommRing isSetℤ Int.+Assoc (λ _ → refl)
                                   -Cancel Int.+Comm Int.·Assoc
                                   Int.·IdR ·DistR+ Int.·Comm

    ℤRing = CommRing→Ring ℤCommRing
    ℤAbGroup = Ring→AbGroup ℤRing

  -- HⁿSⁿ-gen-raw : ∀ {ℓ} (G : AbGroup ℓ) (gen : fst G) (n : ℕ) → S₊ n → EM G n
  -- HⁿSⁿ-gen-raw G gen zero _ = gen
  -- HⁿSⁿ-gen-raw G gen (suc zero) base = embase
  -- HⁿSⁿ-gen-raw G gen (suc zero) (loop i) = emloop gen i
  -- HⁿSⁿ-gen-raw G gen (suc (suc n)) north = 0ₖ (suc (suc n))
  -- HⁿSⁿ-gen-raw G gen (suc (suc n)) south = 0ₖ (suc (suc n))
  -- HⁿSⁿ-gen-raw G gen (suc (suc n)) (merid a i) =
  --   EM→ΩEM+1 (suc n) (HⁿSⁿ-gen-raw G gen (suc n) a) i

  -- HⁿSⁿ-gen-raw : ∀ {ℓ} (G : AbGroup ℓ) (gen : fst G) (n : ℕ) → S₊ n → EM G n
  -- HⁿSⁿ-gen-raw G gen zero _ = gen
  -- HⁿSⁿ-gen-raw G gen (suc zero) base = embase
  -- HⁿSⁿ-gen-raw G gen (suc zero) (loop i) = emloop gen i
  -- HⁿSⁿ-gen-raw G gen (suc (suc n)) north = 0ₖ (suc (suc n))
  -- HⁿSⁿ-gen-raw G gen (suc (suc n)) south = ∣ south ∣
  -- HⁿSⁿ-gen-raw G gen (suc (suc zero)) (merid a i) =
  --   ∣ merid (HⁿSⁿ-gen-raw G gen (suc zero) a) i ∣ₕ
  -- HⁿSⁿ-gen-raw G gen (suc (suc (suc n))) (merid a i) =
  --   TR.rec {B = Path (EM G (suc (suc (suc n)))) ∣ north ∣ ∣ south ∣}
  --     (isOfHLevelTrunc (5 +ℕ n) _ _)
  --     (λ x i → ∣ merid x i ∣ )
  --     (HⁿSⁿ-gen-raw G gen (suc (suc n)) a) i

  HⁿSⁿ-gen-raw : ∀ {ℓ} (G : AbGroup ℓ) (gen : fst G) (n : ℕ) → S₊ n → EM G n
  HⁿSⁿ-gen-raw G gen zero _ = gen
  HⁿSⁿ-gen-raw G gen (suc zero) base = embase
  HⁿSⁿ-gen-raw G gen (suc zero) (loop i) = emloop gen i
  HⁿSⁿ-gen-raw G gen (suc (suc n)) north = 0ₖ (suc (suc n))
  HⁿSⁿ-gen-raw G gen (suc (suc n)) south = ∣ north ∣
  HⁿSⁿ-gen-raw G gen (suc (suc zero)) (merid a i) =
    ∣ (merid (HⁿSⁿ-gen-raw G gen (suc zero) a) ∙ sym (merid embase)) i ∣ₕ
  HⁿSⁿ-gen-raw G gen (suc (suc (suc n))) (merid a i) =
    TR.rec {B = Path (EM G (suc (suc (suc n)))) ∣ north ∣ ∣ north ∣}
      (isOfHLevelTrunc (5 +ℕ n) _ _)
      (λ x i → ∣ (merid x ∙ sym (merid north)) i ∣ )
      (HⁿSⁿ-gen-raw G gen (suc (suc n)) a) i



  ℤ/^2→ℤ/2 : (x : (ℤAbGroup /^ 2) .fst) → ℤ/2 .fst
  ℤ/^2→ℤ/2 = SQ.rec isSetFin underl
    λ a b → PT.rec (isSetFin _ _)
      λ {(c , p) → lem a b c p}
    where
    underlℕ : ℕ → ℤ/2 .fst
    underlℕ zero = fzero
    underlℕ (suc zero) = fone
    underlℕ (suc (suc n)) = underlℕ n

    underl : ℤ → ℤ/2 .fst
    underl (pos n) = underlℕ n
    underl (negsuc n) = underlℕ (suc n)

    underl+ℕ : (x y : ℕ) → ((underlℕ x) +ₘ (underlℕ y)) ≡ underlℕ (x +ℕ y)
    underl+ℕ zero y = +ₘ-lUnit (underlℕ y)
    underl+ℕ (suc zero) zero = refl
    underl+ℕ (suc zero) (suc zero) = refl
    underl+ℕ (suc zero) (suc (suc y)) = underl+ℕ (suc zero) y
    underl+ℕ (suc (suc x)) y = underl+ℕ x y

    underl+2 : (x : ℤ) → underl (sucℤ (sucℤ x)) ≡ underl x
    underl+2 (pos n) = refl
    underl+2 (negsuc zero) = refl
    underl+2 (negsuc (suc zero)) = refl
    underl+2 (negsuc (suc (suc n))) = refl
      where
      help : predℤ (predℤ (pos 2 +negsuc n)) ≡ negsuc n
      help = cong predℤ (predℤ+negsuc n (pos 2))
           ∙ predℤ+negsuc n (pos 1) ∙ +Comm (pos 0) (negsuc n)

    underl-2 : (x : ℤ) → underl (predℤ (predℤ x)) ≡ underl x
    underl-2 (pos zero) = refl
    underl-2 (pos (suc zero)) = refl
    underl-2 (pos (suc (suc n))) = refl
    underl-2 (negsuc n) = refl

    underl×2 : (x : ℤ) → underl (x +ℤ x) ≡ fzero
    underl×2 (pos zero) = refl
    underl×2 (pos (suc n)) =
        cong underl (sym (sucℤ+pos (suc n) (pos n)))
      ∙ underl+2 (pos n +pos n) ∙ underl×2 (pos n)
    underl×2 (negsuc zero) = refl
    underl×2 (negsuc (suc n)) =
      cong underl (sym (predℤ+negsuc (suc n) (negsuc n)))
      ∙ underl-2 (negsuc n +negsuc n) ∙ underl×2 (negsuc n)

    underl+ : (x y : ℤ) → (underl x +ₘ underl y) ≡ underl (x +ℤ y)
    underl+ (pos n) (pos m) = underl+ℕ n m ∙ cong underl (pos+ n m)
    underl+ (pos n) (negsuc m) = underl+ℕ n (suc m) ∙ help n m
      where
      help : (n m : ℕ) → underlℕ (n +ℕ suc m) ≡ underl (pos n +negsuc m)
      help zero m = cong underl (+Comm (negsuc m) (pos zero))
      help (suc zero) zero = refl
      help (suc zero) (suc m) =
        cong underl (+Comm (negsuc m) (pos 0) ∙ sym (predℤ+negsuc m (pos 1)))
      help (suc (suc n)) zero = cong underlℕ (+-comm n 1)
      help (suc (suc n)) (suc zero) = cong underlℕ (+-comm n 2)
      help (suc (suc n)) (suc (suc m)) =
        cong underlℕ (+-suc n (suc (suc m)) ∙ cong suc (+-suc n (suc m)))
        ∙ help n m
        ∙ cong underl
           (sym (predℤ+negsuc m (pos (suc n)))
          ∙ sym (cong predℤ (predℤ+negsuc m (pos (suc (suc n))))))
    underl+ (negsuc n) (pos m) =
       +ₘ-comm (underl (pos (suc n))) (underl (pos m))
      ∙ underl+ (pos m) (negsuc n)
      ∙ cong underl (+Comm (pos m) (negsuc n))
    underl+ (negsuc n) (negsuc m) = underl+ℕ (suc n) (suc m)
      ∙ cong underl (neg+ (suc n) (suc m))

    lem : (a b : ℤ) (c : ℤ) → (c +ℤ c) ≡ (a -ℤ b) → underl a ≡ underl b
    lem a b c p =
      cong underl
        (cong (a +ℤ_) (sym (-Cancel' b))
      ∙ +Assoc a (- b) b)
      ∙ sym (underl+ (a -ℤ b) b)
      ∙ cong (_+ₘ (underl b)) help
      ∙ +ₘ-lUnit (underl b)
      where
      help : underl (a -ℤ b) ≡ fzero
      help = sym (cong underl p) ∙ underl×2 c


module S¹-comps-ℤ where
  H¹[S¹,ℤ] = coHomGr 1 ℤAbGroup S¹
  _+H_ = _+ₕ_ {n = 1} {ℤAbGroup} {S¹}
  -H_ = -ₕ_ {n = 1} {ℤAbGroup} {S¹}

  ϕ₁ : H¹[S¹,ℤ] .fst → ℤ
  ϕ₁ = H¹[S¹,G]≅G ℤAbGroup .fst .fst

  g : H¹[S¹,ℤ] .fst
  g = ∣ HⁿSⁿ-gen-raw ℤAbGroup 1 1 ∣₂

  test₁ : ϕ₁ g ≡ 1
  test₁ = refl

  test₂ : ϕ₁ (g +H g) ≡ 2
  test₂ = refl

  test₃ : ϕ₁ (-H g) ≡ -1
  test₃ = refl

module S¹-comps-ℤ/2 where
  H¹[S¹,ℤ/2] = coHomGr 1 ℤ/2 S¹
  _+H_ = _+ₕ_ {n = 1} {ℤ/2} {S¹}
  -H_ = -ₕ_ {n = 1} {ℤ/2} {S¹}

  ϕ₂ : H¹[S¹,ℤ/2] .fst → ℕ -- ⊃ ℤ/2
  ϕ₂ x = H¹[S¹,G]≅G ℤ/2 .fst .fst x .fst

  g : H¹[S¹,ℤ/2] .fst
  g = ∣ HⁿSⁿ-gen-raw ℤ/2 fone 1 ∣₂

  test₁ : ϕ₂ g ≡ 1
  test₁ = refl

  test₂ : ϕ₂ (g +H g) ≡ 0
  test₂ = refl

  test₃ : ϕ₂ (-H g) ≡ 1
  test₃ = refl

module S²-comps-ℤ where
  H²[S²,ℤ] = coHomGr 2 ℤAbGroup (S₊ 2)
  _+H_ = _+ₕ_ {n = 2} {ℤAbGroup} {S₊ 2}
  -H_ = -ₕ_ {n = 2} {ℤAbGroup} {S₊ 2}

  ϕ₂ : H²[S²,ℤ] .fst → ℤ
  ϕ₂ = Hⁿ[Sⁿ,G]≅G ℤAbGroup 1 .fst .fst

  g : H²[S²,ℤ] .fst
  g = ∣ HⁿSⁿ-gen-raw ℤAbGroup 1 2 ∣₂

  test₁ : ϕ₂ g ≡ 1
  test₁ = refl

  -- test₂ : ϕ₂ (g +H g) ≡ 2
  -- test₂ = refl

  -- test₃ : ϕ₂ (-H g) ≡ -1
  -- test₃ = refl

module S²-comps-ℤ/2 where
  H²[S²,ℤ/2] = coHomGr 2 ℤ/2 (S₊ 2)
  _+H_ = _+ₕ_ {n = 2} {ℤ/2} {(S₊ 2)}
  -H_ = -ₕ_ {n = 2} {ℤ/2} {(S₊ 2)}

  ϕ₂ : H²[S²,ℤ/2] .fst → ℕ -- ⊃ ℤ/2
  ϕ₂ x = Hⁿ[Sⁿ,G]≅G ℤ/2 1 .fst .fst x .fst

  g : H²[S²,ℤ/2] .fst
  g = ∣ HⁿSⁿ-gen-raw ℤ/2 fone 2 ∣₂

  test₁ : ϕ₂ g ≡ 1
  test₁ = refl

  -- test₂ : ϕ₂ (g +H g) ≡ 0
  -- test₂ = refl

  -- test₃ : ϕ₂ (-H g) ≡ 1
  -- test₃ = refl

module S³-comps-ℤ where
  H³[S³,ℤ] = coHomGr 3 ℤAbGroup (S₊ 3)
  _+H_ = _+ₕ_ {n = 3} {ℤAbGroup} {S₊ 3}
  -H_ = -ₕ_ {n = 3} {ℤAbGroup} {S₊ 3}

  ϕ₃ : H³[S³,ℤ] .fst → ℤ
  ϕ₃ = Hⁿ[Sⁿ,G]≅G ℤAbGroup 2 .fst .fst

  g : H³[S³,ℤ] .fst
  g = ∣ HⁿSⁿ-gen-raw ℤAbGroup 1 3 ∣₂

  -- test₁ : ϕ₃ g ≡ 1
  -- test₁ = refl

  -- test₂ : ϕ₃ (g +H g) ≡ 2
  -- test₂ = refl

  -- test₃ : ϕ₃ (-H g) ≡ -1
  -- test₃ = refl

module S³-comps-ℤ/2 where
  H³[S³,ℤ/2] = coHomGr 3 ℤ/2 (S₊ 3)
  _+H_ = _+ₕ_ {n = 3} {ℤ/2} {S₊ 3}
  -H_ = -ₕ_ {n = 3} {ℤ/2} {S₊ 3}

  ϕ₃ : H³[S³,ℤ/2] .fst → ℕ -- ⊃ ℤ/2
  ϕ₃ x = Hⁿ[Sⁿ,G]≅G ℤ/2 2 .fst .fst x .fst

  g : H³[S³,ℤ/2] .fst
  g = ∣ HⁿSⁿ-gen-raw ℤ/2 fone 3 ∣₂

  -- test₁ : ϕ₃ g ≡ 1
  -- test₁ = refl

  -- test₂ : ϕ₃ (g +H g) ≡ 2
  -- test₂ = refl

  -- test₃ : ϕ₃ (-H g) ≡ -1
  -- test₃ = refl

module T²-comps-ℤ where
  H¹[T²,ℤ] = coHomGr 1 ℤAbGroup T²
  H²[T²,ℤ] = coHomGr 2 ℤAbGroup T²

  _+H¹_ = _+ₕ_ {n = 1} {ℤAbGroup} {T²}
  _-H¹_ = _-ₕ_ {n = 1} {ℤAbGroup} {T²}

  _+H²_ = _+ₕ_ {n = 2} {ℤAbGroup} {T²}
  -H²_ = -ₕ_ {n = 2} {ℤAbGroup} {T²}

  _⌣T²_ = _⌣_ {G'' = CommRing→Ring ℤCommRing} {T²} {1} {1}

  ϕ₁ : H¹[T²,ℤ] .fst → ℤ × ℤ -- ⊃ ℤ/2
  ϕ₁ = H¹[T²,G]≅G×G ℤAbGroup .fst .fst

  ϕ₂ : H²[T²,ℤ] .fst → ℤ
  ϕ₂ = H²[T²,G]≅G ℤAbGroup .fst .fst

  g¹₁ g¹₂ : H¹[T²,ℤ] .fst
  g¹₁ = ∣ (λ {(x , y) → HⁿSⁿ-gen-raw ℤAbGroup 1 1 x}) ∣₂
  g¹₂ = ∣ (λ {(x , y) → HⁿSⁿ-gen-raw ℤAbGroup 1 1 y}) ∣₂

  g² : H²[T²,ℤ] .fst
  g² = ∣ (λ { (base , y) → ∣ north ∣
            ; (loop i , y) → HⁿSⁿ-gen-raw ℤAbGroup 1 2 (merid y i)}) ∣₂

  test¹₁ : ϕ₁ (g¹₁ +H¹ g¹₂) ≡ (1 , 1)
  test¹₁ = refl

  test¹₂ : ϕ₁ (g¹₁ -H¹ g¹₂) ≡ (1 , -1)
  test¹₂ = refl 

  -- test²₁ : ϕ₂ g² ≡ 1
  -- test²₁ = refl

  -- test²₂ : ϕ₂ (g¹₁ ⌣T² g¹₂) ≡ 1 
  -- test²₂ = refl

  -- test²₃ : ϕ₂ ((g¹₁ +H¹ g¹₁) ⌣T² g¹₂) ≡ 2
  -- test²₃ = refl

module T²-comps-ℤ/2 where
  H¹[T²,ℤ/2] = coHomGr 1 ℤ/2 T²
  H²[T²,ℤ/2] = coHomGr 2 ℤ/2 T²

  _+H¹_ = _+ₕ_ {n = 1} {ℤ/2} {T²}
  _-H¹_ = _-ₕ_ {n = 1} {ℤ/2} {T²}

  _+H²_ = _+ₕ_ {n = 2} {ℤ/2} {T²}
  -H²_ = -ₕ_ {n = 2} {ℤ/2} {T²}

  _⌣T²_ = _⌣_ {G'' = ℤ/2Ring} {T²} {1} {1}

  ϕ₁ : H¹[T²,ℤ/2] .fst → ℕ × ℕ -- ⊃ ℤ/2 ×⊃ ℤ/2
  ϕ₁ x = H¹[T²,G]≅G×G ℤ/2 .fst .fst x .fst .fst
       , H¹[T²,G]≅G×G ℤ/2 .fst .fst x .snd .fst 

  ϕ₂ : H²[T²,ℤ/2] .fst → ℕ
  ϕ₂ x = H²[T²,G]≅G ℤ/2 .fst .fst x .fst

  g¹₁ g¹₂ : H¹[T²,ℤ/2] .fst
  g¹₁ = ∣ (λ {(x , y) → HⁿSⁿ-gen-raw ℤ/2 fone 1 x}) ∣₂
  g¹₂ = ∣ (λ {(x , y) → HⁿSⁿ-gen-raw ℤ/2 fone 1 y}) ∣₂

  g² : H²[T²,ℤ/2] .fst
  g² = ∣ (λ { (base , y) → ∣ north ∣
            ; (loop i , y) → HⁿSⁿ-gen-raw ℤ/2 fone 2 (merid y i)}) ∣₂

  test¹₁ : ϕ₁ (g¹₁ +H¹ g¹₂) ≡ (1 , 1)
  test¹₁ = refl

  test¹₂ : ϕ₁ (g¹₁ -H¹ g¹₂) ≡ (1 , 1)
  test¹₂ = refl 

  -- test²₁ : ϕ₂ g² ≡ 1
  -- test²₁ = refl

  -- test²₂ : ϕ₂ (g¹₁ ⌣T² g¹₂) ≡ 1 
  -- test²₂ = refl

  -- test²₃ : ϕ₂ ((g¹₁ +H¹ g¹₁) ⌣T² g¹₂) ≡ 2
  -- test²₃ = refl

module S²∨S¹∨S¹-comps-ℤ where
  H¹[S²∨S¹∨S¹,ℤ] = coHomGr 1 ℤAbGroup S²∨S¹∨S¹
  H²[S²∨S¹∨S¹,ℤ] = coHomGr 2 ℤAbGroup S²∨S¹∨S¹

  _+H¹_ = _+ₕ_ {n = 1} {ℤAbGroup} {S²∨S¹∨S¹}
  _-H¹_ = _-ₕ_ {n = 1} {ℤAbGroup} {S²∨S¹∨S¹}

  _+H²_ = _+ₕ_ {n = 2} {ℤAbGroup} {S²∨S¹∨S¹}
  _-H²_ = _-ₕ_ {n = 2} {ℤAbGroup} {S²∨S¹∨S¹}

  _⌣T²_ = _⌣_ {G'' = CommRing→Ring ℤCommRing} {S²∨S¹∨S¹} {1} {1}

  ϕ₁ : H¹[S²∨S¹∨S¹,ℤ] .fst → ℤ × ℤ
  ϕ₁ x = Hⁿ[Sⁿ,G]≅G ℤAbGroup 0 .fst .fst (t .fst)
        , Hⁿ[Sⁿ,G]≅G ℤAbGroup 0 .fst .fst (t .snd)
    where
    t = fst (Hⁿ-⋁≅Hⁿ×Hⁿ ℤAbGroup 0 .fst) ((fst (Hⁿ-⋁≅Hⁿ×Hⁿ ℤAbGroup zero .fst) x .snd))

  ϕ₂ : H²[S²∨S¹∨S¹,ℤ] .fst → ℤ
  ϕ₂ x = Hⁿ[Sⁿ,G]≅G ℤAbGroup 1 .fst .fst (fst (Hⁿ-⋁≅Hⁿ×Hⁿ ℤAbGroup (suc zero) .fst) x .fst)

  g¹₁ : H¹[S²∨S¹∨S¹,ℤ] .fst
  g¹₁ = ∣ (λ { (inl x) → embase ;
              (inr (inl x)) → HⁿSⁿ-gen-raw ℤAbGroup 1 1 x
              ; (inr (inr x)) → embase
              ; (inr (push a i)) → embase
              ; (push a i) → embase}) ∣₂

  g¹₂ : H¹[S²∨S¹∨S¹,ℤ] .fst
  g¹₂ = ∣ (λ { (inl x) → embase ;
               (inr (inl x)) → embase
               ; (inr (inr x)) → HⁿSⁿ-gen-raw ℤAbGroup 1 1 x
               ; (inr (push a i)) → embase
               ; (push a i) → embase}) ∣₂


  g² : H²[S²∨S¹∨S¹,ℤ] .fst
  g² = ∣ (λ { (inl x) → HⁿSⁿ-gen-raw ℤAbGroup 1 2 x ;
             (inr x) → ∣ north ∣ ; 
             (push a i) → ∣ north ∣}) ∣₂


  test¹₁ : ϕ₁ (g¹₁ +H¹ g¹₂) ≡ (1 , 1)
  test¹₁ = refl

  test¹₂ : ϕ₁ (g¹₁ -H¹ g¹₂) ≡ (1 , -1)
  test¹₂ = refl 

  test²₁ : ϕ₂ g² ≡ 1
  test²₁ = refl

  test²₂ : ϕ₂ (g¹₁ ⌣T² g¹₂) ≡ 0
  test²₂ = refl

  test²₃ : ϕ₂ ((g¹₁ +H¹ g¹₁) ⌣T² g¹₂) ≡ 0
  test²₃ = refl

module S²∨S¹∨S¹-comps-ℤ/2 where
  H¹[S²∨S¹∨S¹,ℤ/2] = coHomGr 1 ℤ/2 S²∨S¹∨S¹
  H²[S²∨S¹∨S¹,ℤ/2] = coHomGr 2 ℤ/2 S²∨S¹∨S¹

  _+H¹_ = _+ₕ_ {n = 1} {ℤ/2} {S²∨S¹∨S¹}
  _-H¹_ = _-ₕ_ {n = 1} {ℤ/2} {S²∨S¹∨S¹}

  _+H²_ = _+ₕ_ {n = 2} {ℤ/2} {S²∨S¹∨S¹}
  _-H²_ = _-ₕ_ {n = 2} {ℤ/2} {S²∨S¹∨S¹}

  _⌣∨_ = _⌣_ {G'' = ℤ/2Ring} {S²∨S¹∨S¹} {1} {1}

  ϕ₁ : H¹[S²∨S¹∨S¹,ℤ/2] .fst → ℕ × ℕ -- ⊃ ℤ/2 × ℤ/2
  ϕ₁ x = Hⁿ[Sⁿ,G]≅G ℤ/2 0 .fst .fst (t .fst) .fst
        , Hⁿ[Sⁿ,G]≅G ℤ/2 0 .fst .fst (t .snd) .fst
    where
    t = fst (Hⁿ-⋁≅Hⁿ×Hⁿ ℤ/2 0 .fst) ((fst (Hⁿ-⋁≅Hⁿ×Hⁿ ℤ/2 zero .fst) x .snd))

  ϕ₂ : H²[S²∨S¹∨S¹,ℤ/2] .fst → ℕ -- ⊃ ℤ/2
  ϕ₂ x = Hⁿ[Sⁿ,G]≅G ℤ/2 1 .fst .fst (fst (Hⁿ-⋁≅Hⁿ×Hⁿ ℤ/2 (suc zero) .fst) x .fst) .fst

  g¹₁ : H¹[S²∨S¹∨S¹,ℤ/2] .fst
  g¹₁ = ∣ (λ { (inl x) → embase ;
              (inr (inl x)) → HⁿSⁿ-gen-raw ℤ/2 fone 1 x
              ; (inr (inr x)) → embase
              ; (inr (push a i)) → embase
              ; (push a i) → embase}) ∣₂

  g¹₂ : H¹[S²∨S¹∨S¹,ℤ/2] .fst
  g¹₂ = ∣ (λ { (inl x) → embase ;
               (inr (inl x)) → embase
               ; (inr (inr x)) → HⁿSⁿ-gen-raw ℤ/2 fone 1 x
               ; (inr (push a i)) → embase
               ; (push a i) → embase}) ∣₂


  g² : H²[S²∨S¹∨S¹,ℤ/2] .fst
  g² = ∣ (λ { (inl x) → HⁿSⁿ-gen-raw ℤ/2 fone 2 x ;
             (inr x) → ∣ north ∣ ; 
             (push a i) → ∣ north ∣}) ∣₂


  test¹₁ : ϕ₁ (g¹₁ +H¹ g¹₂) ≡ (1 , 1)
  test¹₁ = refl

  test¹₂ : ϕ₁ (g¹₁ -H¹ g¹₂) ≡ (1 , 1)
  test¹₂ = refl 

  test²₁ : ϕ₂ g² ≡ 1
  test²₁ = refl

  test²₂ : ϕ₂ (g¹₁ ⌣∨ g¹₂) ≡ 0
  test²₂ = refl

  test²₃ : ϕ₂ ((g¹₁ +H¹ g¹₁) ⌣∨ g¹₂) ≡ 0
  test²₃ = refl


module RP²-comps-ℤ where
  H²[RP²,ℤ] = coHomGr 2 ℤAbGroup RP²

  _+H²_ = _+ₕ_ {n = 2} {ℤAbGroup} {RP²}
  -H²_ = -ₕ_ {n = 2} {ℤAbGroup} {RP²}

  ϕ₂ : H²[RP²,ℤ] .fst → ℕ -- ⊃ ℤ/2
  ϕ₂ x = ℤ/^2→ℤ/2 (H²[RP²,G]≅G/2 ℤAbGroup .fst .fst x) .fst

  g² : H²[RP²,ℤ] .fst
  g² = ∣ RP²Fun ∣ north ∣ₕ refl
      (sym (EM→ΩEM+1-0ₖ {G = ℤAbGroup} 1)
    ∙∙ cong (EM→ΩEM+1 {G = ℤAbGroup} 1) (EM→ΩEM+1 {G = ℤAbGroup} 0 1)
    ∙∙ EM→ΩEM+1-0ₖ {G = ℤAbGroup} 1) ∣₂

  -- test₁ : ϕ₂ g² ≡ 1
  -- test₁ = refl

  -- test₂ : ϕ₂ (g¹ +H² g²) ≡ 0
  -- test₂ = refl

  -- test₃ : ϕ₂ (-H² g²) ≡ 1
  -- test₃ = refl


module RP²-comps-ℤ/2 where
  H¹[RP²,ℤ/2] = coHomGr 1 ℤ/2 RP²
  H²[RP²,ℤ/2] = coHomGr 2 ℤ/2 RP²

  _+H¹_ = _+ₕ_ {n = 1} {ℤ/2} {RP²}
  -H¹_ = -ₕ_ {n = 1} {ℤ/2} {RP²}

  _+H²_ = _+ₕ_ {n = 2} {ℤ/2} {RP²}
  -H²_ = -ₕ_ {n = 2} {ℤ/2} {RP²}

  _⌣RP²_ = _⌣_ {G'' = ℤ/2Ring} {RP²} {1} {1}

  ϕ₁ : H¹[RP²,ℤ/2] .fst → ℕ -- ⊃ ℤ/2
  ϕ₁ x = H¹[RP²,G]≅G[2] ℤ/2 .fst .fst x .fst .fst

  ϕ₂ : H²[RP²,ℤ/2] .fst → ℕ -- ⊃ ℤ/2
  ϕ₂ x = Iso.fun (ℤ/2/2≅ℤ/2 .fst) (H²[RP²,G]≅G/2 ℤ/2 .fst .fst x) .fst

  g¹ : H¹[RP²,ℤ/2] .fst
  g¹ = ∣ RP²Fun embase (emloop fone) (emloop-inv (AbGroup→Group ℤ/2) fone) ∣₂

  g² : H²[RP²,ℤ/2] .fst
  g² = ∣ RP²Fun ∣ north ∣ₕ refl
      (sym (EM→ΩEM+1-0ₖ {G = ℤ/2} 1)
    ∙∙ cong (EM→ΩEM+1 {G = ℤ/2} 1) (EM→ΩEM+1 {G = ℤ/2} 0 fone)
    ∙∙ EM→ΩEM+1-0ₖ {G = ℤ/2} 1) ∣₂

  test¹₁ : ϕ₁ g¹ ≡ 1
  test¹₁ = refl

  test¹₂ : ϕ₁ (g¹ +H¹ g¹) ≡ 0
  test¹₂ = refl

  test¹₃ : ϕ₁ (-H¹ g¹) ≡ 1
  test¹₃ = refl

  -- test²₁ : ϕ₂ g² ≡ 1
  -- test²₁ = refl

  -- test²₂ : ϕ₂ (g² +H² g²) ≡ 0
  -- test²₂ = refl

  -- test²₃ : ϕ₂ (-H² g²) ≡ 1
  -- test²₃ = refl

  -- test²₄ : ϕ₂ (g¹ ⌣ g¹) ≡ 1
  -- test²₄ = refl


-- KleinBottle (ℤ coefficients)
module K²-comps-ℤ where
  H¹[K²,ℤ] = coHomGr 1 ℤAbGroup K²
  H²[K²,ℤ] = coHomGr 2 ℤAbGroup K²

  _+H¹_ = _+ₕ_ {n = 1} {ℤAbGroup} {K²}
  -H¹_ = -ₕ_ {n = 1} {ℤAbGroup} {K²}

  _+H²_ = _+ₕ_ {n = 2} {ℤAbGroup} {K²}
  -H²_ = -ₕ_ {n = 2} {ℤAbGroup} {K²}

  _⌣K²_ = _⌣_ {G'' = CommRing→Ring ℤCommRing} {K²} {1} {1}

  ϕ₁ : H¹[K²,ℤ] .fst → ℤ
  ϕ₁ x = H¹[K²,G]≅G×G[2] ℤAbGroup .fst .fst x .fst

  ϕ₂ : H²[K²,ℤ] .fst → ℕ -- ⊃ ℤ/2
  ϕ₂ x = ℤ/^2→ℤ/2 (H²[K²,G]≅G/2 ℤAbGroup .fst .fst x) .fst

  g¹ : H¹[K²,ℤ] .fst
  g¹ = ∣ K²Fun embase refl (emloop 1) refl ∣₂

  g² : H²[K²,ℤ] .fst
  g² = ∣ K²Fun ∣ north ∣ₕ refl refl
      ((sym (EM→ΩEM+1-0ₖ {G = ℤAbGroup} 1)
      ∙∙ cong (EM→ΩEM+1 {G = ℤAbGroup} 1) (EM→ΩEM+1 {G = ℤAbGroup} 0 1)
      ∙∙ EM→ΩEM+1-0ₖ {G = ℤAbGroup} 1) ) ∣₂

  test¹₁ : ϕ₁ g¹ ≡ 1
  test¹₁ = refl

  test¹₂ : ϕ₁ (g¹ +H¹ g¹) ≡ 2
  test¹₂ = refl

  test¹₃ : ϕ₁ (-H¹ g¹) ≡ -1
  test¹₃ = refl

  -- test²₁ : ϕ₂ g² ≡ 1
  -- test²₁ = refl

  -- test²₂ : ϕ₂ (g² +H² g²) ≡ 0
  -- test²₂ = refl

  -- test²₃ : ϕ₂ (-H² g²) ≡ 1
  -- test²₃ = refl

  -- test²₄ : ϕ₂ (g¹ ⌣K² g¹) ≡ 1
  -- test²₄ = refl

-- KleinBottle (ℤ/2 coefficients)
module K²-comps-ℤ/2 where
  H¹[K²,ℤ/2] = coHomGr 1 ℤ/2 K²
  H²[K²,ℤ/2] = coHomGr 2 ℤ/2 K²

  _+H¹_ = _+ₕ_ {n = 1} {ℤ/2} {K²}
  _-H¹_ = _-ₕ_ {n = 1} {ℤ/2} {K²}

  _+H²_ = _+ₕ_ {n = 2} {ℤ/2} {K²}
  _-H²_ = _-ₕ_ {n = 2} {ℤ/2} {K²}

  _⌣K²_ = _⌣_ {G'' = CommRing→Ring ℤ/2CommRing} {K²} {1} {1}

  ϕ₁ : H¹[K²,ℤ/2] .fst → ℕ × ℕ -- ⊃ ℤ/2 × ℤ/2
  ϕ₁ x = (H¹[K²,G]≅G×G[2] ℤ/2 .fst .fst x .fst .fst)
        , (Iso.fun (ℤ/2[2]≅ℤ/2 .fst)
            (H¹[K²,G]≅G×G[2] ℤ/2 .fst .fst x .snd) .fst)

  ϕ₂ : H²[K²,ℤ/2] .fst → ℕ -- ⊃ ℤ/2
  ϕ₂ x = Iso.fun (ℤ/2/2≅ℤ/2 .fst) (H²[K²,G]≅G/2 ℤ/2 .fst .fst x) .fst

  g¹₁ : H¹[K²,ℤ/2] .fst
  g¹₁ = ∣ K²Fun embase refl (emloop fone) refl ∣₂

  g¹₂ : H¹[K²,ℤ/2] .fst
  g¹₂ = ∣ K²Fun embase (emloop fone) refl
    (λ i j → emloop-inv (AbGroup→Group ℤ/2) fone (~ j) i ) ∣₂

  g² : H²[K²,ℤ/2] .fst
  g² = ∣ K²Fun ∣ north ∣ₕ refl refl
      ((sym (EM→ΩEM+1-0ₖ {G = ℤ/2} 1)
      ∙∙ cong (EM→ΩEM+1 {G = ℤ/2} 1) (EM→ΩEM+1 {G = ℤ/2} 0 fone)
      ∙∙ EM→ΩEM+1-0ₖ {G = ℤ/2} 1) ) ∣₂

  test¹₁ : ϕ₁ (g¹₁ +H¹ g¹₂) ≡ (1 , 1)
  test¹₁ = refl

  test¹₂ : ϕ₁ (g¹₁ -H¹ g¹₂) ≡ (1 , 1)
  test¹₂ = refl

  -- test²₁ : ϕ₂ g² ≡ 1
  -- test²₁ = refl

  -- test²₂ : ϕ₂ (g¹₁ ⌣K² g¹₂) ≡ 1
  -- test²₂ = refl

  -- test²₃ : ϕ₂ (g¹₁ ⌣K² (g¹₂ +H¹ g¹₂)) ≡ 0
  -- test²₃ = refl

-- HⁿRP∞≅ℤ/2
-- KleinBottle (ℤ/2 coefficients)
module RP∞-comps-ℤ/2 where
  H¹[RP∞,ℤ/2] = coHomGr 1 ℤ/2 RP∞
  H²[RP∞,ℤ/2] = coHomGr 2 ℤ/2 RP∞

  _+H¹_ = _+ₕ_ {n = 1} {ℤ/2} {RP∞}
  -H¹_ = -ₕ_ {n = 1} {ℤ/2} {RP∞}

  ϕ₁ : H¹[RP∞,ℤ/2] .fst → ℕ -- ⊃ ℤ/2
  ϕ₁ x = Iso.fun (HⁿRP∞≅ℤ/2 1 .fst) x .fst

  g¹ : H¹[RP∞,ℤ/2] .fst
  g¹ = ∣ (λ x → x) ∣₂

  -- obs: to test, you need to remove the abstract flag from ⌣RP∞'IsEq
  -- in Cohomology.EilenbergMacLane.Groups.RPinf and isEquiv-g in
  -- Cohomology.EilenbergMacLane.Gysin.

  -- test¹₁ : ϕ₁ g¹ ≡ 1
  -- test¹₁ = {!refl!} -- refl

  -- test¹₂ : ϕ₁ (g¹ +H¹ g¹) ≡ 0
  -- test¹₂ = refl

  -- test¹₃ : ϕ₁ (-H¹ g¹) ≡ 1
  -- test¹₃ = refl
