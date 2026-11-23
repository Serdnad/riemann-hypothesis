module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle422
public import Mathlib.RingTheory.PiTensorProduct
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PiTensorLiftCompSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle426
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

noncomputable section

namespace GlobalTheory.EtC.GmStep.LevelIso

theorem T_eq_unit_zpow (B : Type) [CommRing B] (m : ℤ) :
    (LaurentPolynomial.T m : LaurentPolynomial B) =
      ((laurentVarUnit B ^ m : (LaurentPolynomial B)ˣ) : LaurentPolynomial B) := by
  have h := laurentMap_T (RingHom.id B) m
  rw [laurentMap, LaurentPolynomial.eval₂_T] at h
  exact h.symm

theorem laurent_ringHom_ext {B R : Type} [CommRing B] [CommRing R] {φ ψ : LaurentPolynomial B →+* R}
    (hC : φ.comp LaurentPolynomial.C = ψ.comp LaurentPolynomial.C)
    (hT : φ (LaurentPolynomial.T 1) = ψ (LaurentPolynomial.T 1)) : φ = ψ := by
  have hu : Units.map φ.toMonoidHom (laurentVarUnit B) = Units.map ψ.toMonoidHom (laurentVarUnit B) :=
    Units.ext hT
  have e : ∀ (χ : LaurentPolynomial B →+* R) (m : ℤ),
      χ ((laurentVarUnit B ^ m : (LaurentPolynomial B)ˣ) : LaurentPolynomial B) =
        ((Units.map χ.toMonoidHom (laurentVarUnit B) ^ m : Rˣ) : R) := by
    intro χ m
    rw [← map_zpow]
    rfl
  have hTm : ∀ m : ℤ, φ (LaurentPolynomial.T m) = ψ (LaurentPolynomial.T m) := fun m => by
    rw [T_eq_unit_zpow, e φ, e ψ, hu]
  refine RingHom.ext fun p => ?_
  induction p using LaurentPolynomial.induction_on' with
  | add p r hp hr => rw [map_add (f := _), map_add (f := _), hp, hr]
  | C_mul_T n b => rw [map_mul, map_mul, hTm n, ← RingHom.comp_apply, hC, RingHom.comp_apply]

theorem laurentMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    (laurentMap g).comp (laurentMap f) = laurentMap (g.comp f) :=
  laurent_ringHom_ext (RingHom.ext fun a => by simp [laurentMap_C])
    (by rw [RingHom.comp_apply, laurentMap_T, laurentMap_T, laurentMap_T])

theorem tensorPow_univ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (k : ℕ) (R : Type) [CommRing R]
    (g : Fin (k + 1) → (B →+* R)) (hg : ∀ j, (g j).comp (algebraMap A B) = (g 0).comp (algebraMap A B)) :
    ∃! φ : PiTensorProduct A (fun _ : Fin (k + 1) => B) →+* R,
      ∀ j, φ.comp (PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin (k + 1) => B) j).toRingHom = g j := by
  classical
  letI : Algebra A R := ((g 0).comp (algebraMap A B)).toAlgebra
  let g' : Fin (k + 1) → (B →ₐ[A] R) := fun j => ⟨g j, fun r => RingHom.congr_fun (hg j) r⟩
  refine ⟨(GlobalTheory.piTensorLift g').toRingHom, fun j => ?_, fun ψ hψ => ?_⟩
  · ext x
    exact GlobalTheory.piTensorLift_single g' j x
  · have hc : ∀ r : A, ψ (algebraMap A (PiTensorProduct A fun _ : Fin (k + 1) => B) r) = algebraMap A R r := by
      intro r
      have h1 : algebraMap A (PiTensorProduct A fun _ : Fin (k + 1) => B) r =
          PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin (k + 1) => B) 0 (algebraMap A B r) :=
        ((PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin (k + 1) => B) 0).commutes r).symm
      rw [h1]
      exact RingHom.congr_fun (hψ 0) (algebraMap A B r)
    let ψ' : PiTensorProduct A (fun _ : Fin (k + 1) => B) →ₐ[A] R := ⟨ψ, hc⟩
    have : ψ' = GlobalTheory.piTensorLift g' := PiTensorProduct.algHom_ext fun j => by
      ext x
      change ψ _ = _
      rw [AlgHom.comp_apply, GlobalTheory.piTensorLift_single]
      exact RingHom.congr_fun (hψ j) x
    exact congrArg AlgHom.toRingHom this

theorem laurent_univ (A B T : Type) [CommRing A] [CommRing B] [CommRing T] (a : A →+* B) (k : ℕ)
    (ι : Fin (k + 1) → (B →+* T))
    (hu : ∀ (R : Type) [CommRing R] (g : Fin (k + 1) → (B →+* R)), (∀ j, (g j).comp a = (g 0).comp a) →
      ∃! φ : T →+* R, ∀ j, φ.comp (ι j) = g j)
    (R : Type) [CommRing R] (g : Fin (k + 1) → (LaurentPolynomial B →+* R))
    (hg : ∀ j, (g j).comp (laurentMap a) = (g 0).comp (laurentMap a)) :
    ∃! φ : LaurentPolynomial T →+* R, ∀ j, φ.comp (laurentMap (ι j)) = g j := by
  have hT : ∀ j, g j (LaurentPolynomial.T 1) = g 0 (LaurentPolynomial.T 1) := fun j => by
    have := RingHom.congr_fun (hg j) (LaurentPolynomial.T 1)
    rwa [RingHom.comp_apply, RingHom.comp_apply, laurentMap_T] at this
  obtain ⟨ψ, hψ, hψu⟩ := hu R (fun j => (g j).comp LaurentPolynomial.C) (fun j => by
    refine RingHom.ext fun x => ?_
    have := RingHom.congr_fun (hg j) (LaurentPolynomial.C x)
    simpa [laurentMap_C] using this)
  let u : Rˣ := Units.map (g 0).toMonoidHom (laurentVarUnit B)
  refine ⟨LaurentPolynomial.eval₂ ψ u, fun j => ?_, fun φ hφ => ?_⟩
  · apply laurent_ringHom_ext
    · refine RingHom.ext fun b => ?_
      rw [RingHom.comp_apply, RingHom.comp_apply, laurentMap_C, LaurentPolynomial.eval₂_C]
      exact RingHom.congr_fun (hψ j) b
    · rw [RingHom.comp_apply, laurentMap_T, LaurentPolynomial.eval₂_T, zpow_one, hT j]
      rfl
  · have hC : φ.comp LaurentPolynomial.C = ψ := hψu _ (fun j => by
      refine RingHom.ext fun b => ?_
      have := RingHom.congr_fun (hφ j) (LaurentPolynomial.C b)
      simpa [laurentMap_C] using this)
    apply laurent_ringHom_ext
    · refine RingHom.ext fun t => ?_
      rw [RingHom.comp_apply, RingHom.comp_apply, LaurentPolynomial.eval₂_C, ← hC]
      rfl
    · rw [LaurentPolynomial.eval₂_T, zpow_one]
      have := RingHom.congr_fun (hφ 0) (LaurentPolynomial.T 1)
      rw [RingHom.comp_apply, laurentMap_T] at this
      rw [this]
      rfl

end GlobalTheory.EtC.GmStep.LevelIso

namespace GlobalTheory.EtC.GmStep.LevelIso

theorem level_iso : ∀ (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (k : ℕ),
  ∃ (e0 : yoneda.obj (Spec (CommRingCat.of (PiTensorProduct A (fun _ : Fin (k + 1) => A')))) ≅ (cech (baseHom A A')).obj (op ⦋k⦌))
    (e : yoneda.obj (Spec (CommRingCat.of (LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A'))))) ≅
      (cech (laurentHom A A')).obj (op ⦋k⦌)),
    e.hom ≫ (cechC A A').app (op ⦋k⦌) =
      yoneda.map (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : PiTensorProduct A (fun _ : Fin (k + 1) => A') →+*
        LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A'))))) ≫ e0.hom ∧
    e.hom ≫ (cechAug (laurentHom A A')).app (op ⦋k⦌) =
      yoneda.map (Spec.map (CommRingCat.ofHom (laurentMap (algebraMap A (PiTensorProduct A (fun _ : Fin (k + 1) => A')))))) := by
  intro A A' _ _ _ k
  let ι : Fin (k + 1) → (A' →+* PiTensorProduct A (fun _ : Fin (k + 1) => A')) := fun j =>
    (PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin (k + 1) => A') j).toRingHom
  have hιA : ∀ j, (ι j).comp (algebraMap A A') = algebraMap A (PiTensorProduct A (fun _ : Fin (k + 1) => A')) :=
    fun j => RingHom.ext fun x => (PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin (k + 1) => A') j).commutes x
  have hι : ∀ j, (ι j).comp (algebraMap A A') = (ι 0).comp (algebraMap A A') := fun j => by rw [hιA, hιA]
  have hu := tensorPow_univ A A' k
  obtain ⟨e0, he0⟩ := GlobalTheory.SpecWidePullback.yoneda_spec_isoWidePullback A A' _ (algebraMap A A') k ι hι hu
  have hι' : ∀ j, (laurentMap (ι j)).comp (laurentMap (algebraMap A A')) =
      (laurentMap (ι 0)).comp (laurentMap (algebraMap A A')) := by
    intro j; rw [laurentMap_comp, laurentMap_comp, hι j]
  obtain ⟨e, he⟩ := GlobalTheory.SpecWidePullback.yoneda_spec_isoWidePullback (LaurentPolynomial A) (LaurentPolynomial A')
    (LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A'))) (laurentMap (algebraMap A A')) k
    (fun j => laurentMap (ι j)) hι' (laurent_univ A A' _ (algebraMap A A') k ι (fun R _ g hg => hu R g hg))
  refine ⟨e0, e, ?_, ?_⟩
  · change e.hom ≫ WidePullback.lift _ _ _ = _
    apply WidePullback.hom_ext
    · intro j
      simp only [Category.assoc, WidePullback.lift_π, Arrow.mk_hom, laurentHom, baseHom]
      refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (he j)).trans ?_)
      refine Eq.trans ?_ (congrArg (_ ≫ ·) (he0 j)).symm
      simp only [constSq, Arrow.homMk_left, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        laurentMap_comp_C]
    · simp only [Category.assoc, WidePullback.lift_base, Arrow.mk_hom, laurentHom, baseHom]
      rw [← WidePullback.π_arrow _ 0]
      simp only [Category.assoc]
      refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (he 0)).trans ?_)
      refine Eq.trans ?_ ((congrArg (_ ≫ ·) (((congrArg (· ≫ yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A A')))) (he0 0)).symm.trans (Category.assoc _ _ _)).trans (congrArg (e0.hom ≫ ·) (WidePullback.π_arrow _ 0)))).trans (Category.assoc _ _ _).symm)
      simp only [constSq, Arrow.homMk_right, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        laurentMap_comp_C]
      congr 3
      exact RingHom.ext fun x => by simp [laurentMap_C]
  · change e.hom ≫ WidePullback.base _ = _
    rw [← WidePullback.π_arrow _ 0, ← Category.assoc, he 0]
    simp only [laurentHom, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, laurentMap_comp, hιA 0]

end GlobalTheory.EtC.GmStep.LevelIso
end
end

section

open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v

noncomputable section
namespace GlobalTheory.EZ.AWChain

theorem bop_comp {n m p q r s : ℕ} (α : SimplexCategory.mk p ⟶ SimplexCategory.mk n)
    (β : SimplexCategory.mk q ⟶ SimplexCategory.mk m) (α' : SimplexCategory.mk r ⟶ SimplexCategory.mk p)
    (β' : SimplexCategory.mk s ⟶ SimplexCategory.mk q) :
    bop α β ≫ bop α' β' = bop (α' ≫ α) (β' ≫ β) := by
  have := Free.single_comp_single (R := ℤ) (C := SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ)
    (X := (op (SimplexCategory.mk n), op (SimplexCategory.mk m)))
    (Y := (op (SimplexCategory.mk p), op (SimplexCategory.mk q)))
    (Z := (op (SimplexCategory.mk r), op (SimplexCategory.mk s))) (α.op, β.op) (α'.op, β'.op) 1 1
  simp only [mul_one] at this
  exact this

theorem comp_apply' {a b c : ℕ} (f : SimplexCategory.mk a ⟶ SimplexCategory.mk b)
    (g : SimplexCategory.mk b ⟶ SimplexCategory.mk c) (j : Fin (a+1)) :
    ((f ≫ g).toOrderHom j : ℕ) = (g.toOrderHom (f.toOrderHom j) : ℕ) := rfl

theorem hom_ext' {a b : ℕ} (f g : SimplexCategory.mk a ⟶ SimplexCategory.mk b)
    (h : ∀ j : Fin (a+1), (f.toOrderHom j : ℕ) = (g.toOrderHom j : ℕ)) : f = g := by
  apply SimplexCategory.Hom.ext
  ext j
  exact h j

theorem faceFun_lt {i j : ℕ} (h : j < i) : faceFun i j = j := if_pos h
theorem faceFun_ge {i j : ℕ} (h : i ≤ j) : faceFun i j = j + 1 := if_neg (by omega)

theorem backc_apply (n a b : ℕ) (j : Fin (b+1)) : ((backc n a b).toOrderHom j : ℕ) = min n (a + j) := rfl
theorem idc_apply (n m : ℕ) (j : Fin (m+1)) : ((idc n m).toOrderHom j : ℕ) = min n j := rfl
theorem fc_apply (n m i : ℕ) (j : Fin (m+1)) : ((fc n m i).toOrderHom j : ℕ) = min n (faceFun i j) := rfl

section
variable (a b : ℕ)

theorem front_face_low (i : ℕ) (hi : i ≤ a) :
    idc (a+b) a ≫ fc (a+b+1) (a+b) i = fc (a+1) a i ≫ idc (a+b+1) (a+1) := by
  apply hom_ext'; intro j; have hj := j.isLt
  simp only [comp_apply', fc_apply, idc_apply, backc_apply]
  rcases lt_or_ge (j:ℕ) i with h | h
  · rw [faceFun_lt (by omega), faceFun_lt h]; omega
  · rw [faceFun_ge (by omega), faceFun_ge h]; omega

theorem back_face_low (i : ℕ) (hi : i ≤ a) :
    backc (a+b) a b ≫ fc (a+b+1) (a+b) i = idc b b ≫ backc (a+b+1) (a+1) b := by
  apply hom_ext'; intro j; have hj := j.isLt
  simp only [comp_apply', fc_apply, idc_apply, backc_apply]
  rw [faceFun_ge (by omega)]; omega

theorem front_face_high (i : ℕ) (hi : a < i) :
    idc (a+b) a ≫ fc (a+b+1) (a+b) i = idc a a ≫ idc (a+b+1) a := by
  apply hom_ext'; intro j; have hj := j.isLt
  simp only [comp_apply', fc_apply, idc_apply, backc_apply]
  rw [faceFun_lt (by omega)]; omega

theorem back_face_high (j : ℕ) (hj : j ≤ b) :
    backc (a+b) a b ≫ fc (a+b+1) (a+b) (a+1+j) = fc (b+1) b (j+1) ≫ backc (a+b+1) a (b+1) := by
  apply hom_ext'; intro k; have hk := k.isLt
  simp only [comp_apply', fc_apply, idc_apply, backc_apply]
  rcases lt_or_ge (k:ℕ) (j+1) with h | h
  · rw [faceFun_lt (by omega), faceFun_lt h]; omega
  · rw [faceFun_ge (by omega), faceFun_ge h]; omega

theorem front_face_cancel : fc (a+1) a (a+1) ≫ idc (a+b+1) (a+1) = idc a a ≫ idc (a+b+1) a := by
  apply hom_ext'; intro j; have hj := j.isLt
  simp only [comp_apply', fc_apply, idc_apply, backc_apply]
  rw [faceFun_lt (by omega)]; omega

theorem back_face_cancel : idc b b ≫ backc (a+b+1) (a+1) b = fc (b+1) b 0 ≫ backc (a+b+1) a (b+1) := by
  apply hom_ext'; intro j; have hj := j.isLt
  simp only [comp_apply', fc_apply, idc_apply, backc_apply]
  rw [faceFun_ge (by omega)]; omega

end

theorem dT_h (a b : ℕ) : dT (a+1) b a b = ∑ i ∈ Finset.range (a+1+1), ((-1 : ℤ) ^ i) • bop (fc (a+1) a i) (idc b b) := by
  simp [dT, dH, dV]

theorem dT_v (a b : ℕ) : dT a (b+1) a b = ((-1 : ℤ) ^ a) • ∑ j ∈ Finset.range (b+1+1), ((-1 : ℤ) ^ j) • bop (idc a a) (fc (b+1) b j) := by
  simp [dT, dH, dV]

theorem dT_zero (x y a b : ℕ) (h1 : ¬ (x = a + 1 ∧ y = b)) (h2 : ¬ (x = a ∧ y = b + 1)) : dT x y a b = 0 := by
  simp [dT, dH, dV, h1, h2]

end GlobalTheory.EZ.AWChain

namespace GlobalTheory.EZ
open GlobalTheory.EZ.AWChain

theorem awO_comm_d : ∀ (n a b : ℕ), a + b = n → dD (n + 1) n ≫ awO n a b =
    ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), awO (n + 1) x.1 x.2 ≫ dT x.1 x.2 a b := by
  intro n a b hab
  subst hab
  rw [Finset.sum_eq_add (a + 1, b) (a, b + 1) (by simp)]
  rotate_left
  · rintro c hc ⟨h1, h2⟩
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hc
    rw [dT_zero, Limits.comp_zero]
    · rintro ⟨e1, e2⟩; exact h1 (Prod.ext e1 e2)
    · rintro ⟨e1, e2⟩; exact h2 (Prod.ext e1 e2)
  · intro h; exact absurd (by rw [Finset.HasAntidiagonal.mem_antidiagonal]; omega) h
  · intro h; exact absurd (by rw [Finset.HasAntidiagonal.mem_antidiagonal]; omega) h
  simp only [dT_h, dT_v]
  have e1 : awO (a + b + 1) (a + 1) b = bop (idc (a+b+1) (a+1)) (backc (a+b+1) (a+1) b) := if_pos (by omega)
  have e2 : awO (a + b + 1) a (b + 1) = bop (idc (a+b+1) a) (backc (a+b+1) a (b+1)) := if_pos (by omega)
  have e3 : awO (a + b) a b = bop (idc (a+b) a) (backc (a+b) a b) := if_pos rfl
  have e4 : dD (a + b + 1) (a + b) = ∑ i ∈ Finset.range (a+b+1+1),
      ((-1 : ℤ) ^ i) • bop (fc (a+b+1) (a+b) i) (fc (a+b+1) (a+b) i) := if_pos rfl
  rw [e1, e2, e3, e4]
  simp only [Preadditive.sum_comp, Preadditive.comp_sum, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
    bop_comp]
  rw [show a + b + 1 + 1 = (a + 1) + (b + 1) by omega, Finset.sum_range_add]
  conv_rhs => rw [Finset.sum_range_succ _ (a + 1), Finset.sum_range_succ' _ (b + 1), smul_add]
  have hA : ∑ i ∈ Finset.range (a + 1), ((-1 : ℤ) ^ i) •
      bop (idc (a+b) a ≫ fc (a+b+1) (a+b) i) (backc (a+b) a b ≫ fc (a+b+1) (a+b) i) =
      ∑ i ∈ Finset.range (a + 1), ((-1 : ℤ) ^ i) •
      bop (fc (a+1) a i ≫ idc (a+b+1) (a+1)) (idc b b ≫ backc (a+b+1) (a+1) b) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [front_face_low a b i (by omega), back_face_low a b i (by omega)]
  have hB : ∑ j ∈ Finset.range (b + 1), ((-1 : ℤ) ^ (a + 1 + j)) •
      bop (idc (a+b) a ≫ fc (a+b+1) (a+b) (a + 1 + j)) (backc (a+b) a b ≫ fc (a+b+1) (a+b) (a + 1 + j)) =
      ((-1 : ℤ) ^ a) • ∑ j ∈ Finset.range (b + 1), ((-1 : ℤ) ^ (j + 1)) •
      bop (idc a a ≫ idc (a+b+1) a) (fc (b+1) b (j + 1) ≫ backc (a+b+1) a (b+1)) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [front_face_high a b (a + 1 + j) (by omega), back_face_high a b j (by omega), smul_smul, ← pow_add, show a + (j + 1) = a + 1 + j by omega]
  have hC : ((-1 : ℤ) ^ (a + 1)) • bop (fc (a+1) a (a + 1) ≫ idc (a+b+1) (a+1)) (idc b b ≫ backc (a+b+1) (a+1) b)
      + ((-1 : ℤ) ^ a) • (((-1 : ℤ) ^ 0) • bop (idc a a ≫ idc (a+b+1) a) (fc (b+1) b 0 ≫ backc (a+b+1) a (b+1))) = 0 := by
    rw [front_face_cancel, back_face_cancel, smul_smul, pow_zero, mul_one, pow_succ, mul_neg_one, neg_smul, neg_add_cancel]
  rw [hA, hB, add_add_add_comm, hC, add_zero]

end GlobalTheory.EZ
end
end

section

open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ

noncomputable section

namespace GlobalTheory.EZ.TotSq

theorem bop_comp {n m p q r s : ℕ} (α : SimplexCategory.mk p ⟶ SimplexCategory.mk n)
    (β : SimplexCategory.mk q ⟶ SimplexCategory.mk m) (α' : SimplexCategory.mk r ⟶ SimplexCategory.mk p)
    (β' : SimplexCategory.mk s ⟶ SimplexCategory.mk q) :
    bop α β ≫ bop α' β' = bop (α' ≫ α) (β' ≫ β) := by
  have := Free.single_comp_single (R := ℤ) (C := SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ)
    (show (op (SimplexCategory.mk n), op (SimplexCategory.mk m)) ⟶
      (op (SimplexCategory.mk p), op (SimplexCategory.mk q)) from (α.op, β.op))
    (show (op (SimplexCategory.mk p), op (SimplexCategory.mk q)) ⟶
      (op (SimplexCategory.mk r), op (SimplexCategory.mk s)) from (α'.op, β'.op)) 1 1
  simp only [mul_one] at this
  exact this

theorem idc_self (n : ℕ) : idc n n = 𝟙 _ := by
  ext j
  have hj : (j : ℕ) < n + 1 := j.isLt
  simp only [idc, clampHom, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk]
  change min n (j : ℕ) = ((j : Fin (n + 1)) : ℕ)
  omega

theorem fc_comp_fc (n i j : ℕ) (hji : j < i) (hi : i ≤ n + 2) :
    fc (n + 1) n j ≫ fc (n + 2) (n + 1) i = fc (n + 1) n (i - 1) ≫ fc (n + 2) (n + 1) j := by
  ext k
  have hk : (k : ℕ) < n + 1 := k.isLt
  simp only [fc, clampHom, faceFun, SimplexCategory.mkHom, SimplexCategory.comp_toOrderHom,
    SimplexCategory.Hom.toOrderHom_mk, OrderHom.comp_coe, Function.comp_apply, OrderHom.coe_mk]
  split_ifs <;> omega

theorem alt_double_sum {M : Type*} [AddCommGroup M] (n : ℕ)
    (F : (SimplexCategory.mk n ⟶ SimplexCategory.mk (n + 2)) → M) :
    ∑ i ∈ Finset.range (n + 3), ∑ j ∈ Finset.range (n + 2),
      ((-1 : ℤ) ^ i * (-1) ^ j) • F (fc (n + 1) n j ≫ fc (n + 2) (n + 1) i) = 0 := by
  rw [← Finset.sum_product']
  refine Finset.sum_involution (fun x _ => if x.2 < x.1 then (x.2, x.1 - 1) else (x.2 + 1, x.1)) ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ h
    simp only [Finset.mem_product, Finset.mem_range] at h
    dsimp only
    split_ifs with hji
    · dsimp only
      rw [fc_comp_fc n i j hji (by omega), ← add_smul]
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rw [show i' + 1 - 1 = i' by omega, pow_succ]
      ring_nf
      simp
    · dsimp only
      rw [fc_comp_fc n (j + 1) i (by omega) (by omega), show j + 1 - 1 = j by omega, ← add_smul, pow_succ]
      ring_nf
      simp
  · rintro ⟨i, j⟩ _ _
    dsimp only
    split_ifs <;> simp only [ne_eq, Prod.mk.injEq] <;> omega
  · rintro ⟨i, j⟩ h
    simp only [Finset.mem_product, Finset.mem_range] at h ⊢
    split_ifs <;> simp only <;> omega
  · rintro ⟨i, j⟩ _
    by_cases h : j < i
    · simp only [h, if_true]
      rw [if_neg (by omega)]
      simp only [Prod.mk.injEq, and_true, true_and]
      omega
    · simp only [h, if_false]
      rw [if_pos (by omega)]
      simp only [Prod.mk.injEq, and_true, true_and]
      omega

theorem dH_comp_dH (a b x y c d : ℕ) : dH a b x y ≫ dH x y c d = 0 := by
  unfold dH
  by_cases h1 : a = x + 1 ∧ b = y
  · by_cases h2 : x = c + 1 ∧ y = d
    · obtain ⟨rfl, rfl⟩ := h1
      obtain ⟨rfl, rfl⟩ := h2
      rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, Preadditive.sum_comp]
      simp only [Preadditive.comp_sum, Preadditive.zsmul_comp, Preadditive.comp_zsmul, bop_comp, smul_smul]
      have := alt_double_sum c (fun α => bop α (idc b b ≫ idc b b))
      simpa only [mul_comm] using this
    · rw [if_neg h2, comp_zero]
  · rw [if_neg h1, zero_comp]

theorem dV_comp_dV (a b x y c d : ℕ) : dV a b x y ≫ dV x y c d = 0 := by
  unfold dV
  by_cases h1 : a = x ∧ b = y + 1
  · by_cases h2 : x = c ∧ y = d + 1
    · obtain ⟨rfl, rfl⟩ := h1
      obtain ⟨rfl, rfl⟩ := h2
      rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, Preadditive.sum_comp]
      simp only [Preadditive.comp_sum, Preadditive.zsmul_comp, Preadditive.comp_zsmul, bop_comp, smul_smul]
      have := alt_double_sum d (fun β => bop (idc a a ≫ idc a a) β)
      simpa only [mul_comm] using this
    · rw [if_neg h2, comp_zero]
  · rw [if_neg h1, zero_comp]

theorem dH_comp_dV (c d : ℕ) :
    dH (c + 1) (d + 1) c (d + 1) ≫ dV c (d + 1) c d = dV (c + 1) (d + 1) (c + 1) d ≫ dH (c + 1) d c d := by
  unfold dH dV
  rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩,
    Preadditive.sum_comp, Preadditive.sum_comp]
  simp only [Preadditive.comp_sum, Preadditive.zsmul_comp, Preadditive.comp_zsmul, bop_comp, smul_smul,
    idc_self, Category.id_comp, Category.comp_id]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

theorem dT_comp_dT (a b c d k : ℕ) (hk : c + d = k) :
    ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (k + 1), dT a b x.1 x.2 ≫ dT x.1 x.2 c d = 0 := by
  subst hk
  have hsplit : ∀ x : ℕ × ℕ, dT a b x.1 x.2 ≫ dT x.1 x.2 c d =
      ((-1 : ℤ) ^ x.1) • (dH a b x.1 x.2 ≫ dV x.1 x.2 c d) +
        ((-1 : ℤ) ^ a) • (dV a b x.1 x.2 ≫ dH x.1 x.2 c d) := by
    intro x
    simp only [dT, Preadditive.add_comp, Preadditive.comp_add, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
      dH_comp_dH, dV_comp_dV, smul_zero, zero_add, add_zero]
    rw [add_comm]
  simp_rw [hsplit, Finset.sum_add_distrib]
  have hm1 : (c, d + 1) ∈ Finset.HasAntidiagonal.antidiagonal (c + d + 1) := by
    rw [Finset.HasAntidiagonal.mem_antidiagonal]; omega
  have hm2 : (c + 1, d) ∈ Finset.HasAntidiagonal.antidiagonal (c + d + 1) := by
    rw [Finset.HasAntidiagonal.mem_antidiagonal]; omega
  rw [Finset.sum_eq_single_of_mem (c, d + 1) hm1 ?_, Finset.sum_eq_single_of_mem (c + 1, d) hm2 ?_]
  · dsimp only
    by_cases h : a = c + 1 ∧ b = d + 1
    · obtain ⟨rfl, rfl⟩ := h
      rw [dH_comp_dV c d, ← add_smul, pow_succ]
      simp
    · have e1 : dH a b c (d + 1) = 0 := by unfold dH; rw [if_neg h]
      have e2 : dV a b (c + 1) d = 0 := by unfold dV; rw [if_neg h]
      rw [e1, e2, zero_comp, zero_comp, smul_zero, smul_zero, add_zero]
  · rintro ⟨x1, x2⟩ _ hx
    have : dH x1 x2 c d = 0 := by
      unfold dH; rw [if_neg]; rintro ⟨rfl, rfl⟩; exact hx rfl
    dsimp only
    rw [this, comp_zero, smul_zero]
  · rintro ⟨x1, x2⟩ _ hx
    have : dV x1 x2 c d = 0 := by
      unfold dV; rw [if_neg]; rintro ⟨rfl, rfl⟩; exact hx rfl
    dsimp only
    rw [this, comp_zero, smul_zero]

theorem dT_sq (a b c d : ℕ) (_h : c + d + 2 = a + b) :
    ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (c + d + 1), dT a b x.1 x.2 ≫ dT x.1 x.2 c d = 0 :=
  dT_comp_dT a b c d (c + d) rfl

end GlobalTheory.EZ.TotSq
end
end
