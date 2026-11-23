module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.AdjointDiagonalRepPreservesWeightPiece
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle003
public import Mathlib.Algebra.GradedMonoid
public import Mathlib.RingTheory.GradedAlgebra.Basic
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

@[expose] public section

section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

namespace UpperTheory.V.UnitaryThreeInertia

private theorem lu_unit {O : Type} [CommRing O] (t : Oˣ) (ht : IsUnit ((t : O) ^ 2 - 1)) (a b : Fin 3)
    (hab : a ≠ b) : IsUnit (((t ^ wt1 a : Oˣ) : O) - ((t ^ wt1 b : Oˣ) : O)) := by
  have e : (t : O) * ((t⁻¹ : Oˣ) : O) = 1 := Units.mul_inv t
  have h1 : IsUnit ((t : O) - 1) := by
    rw [show (t : O) ^ 2 - 1 = ((t : O) - 1) * (t + 1) by ring] at ht
    exact isUnit_of_mul_isUnit_left ht
  have h2 : IsUnit ((t : O) - ((t⁻¹ : Oˣ) : O)) := by
    have := ht.mul (t⁻¹).isUnit
    convert this using 1
    linear_combination (-(t : O)) * e
  have h3 : IsUnit (1 - ((t⁻¹ : Oˣ) : O)) := by
    have := h1.mul (t⁻¹).isUnit
    convert this using 1
    linear_combination (-1 : O) * e
  have h1' := h1.neg
  have h2' := h2.neg
  have h3' := h3.neg
  rw [neg_sub] at h1' h2' h3'
  have w0 : wt1 0 = 1 := rfl
  have w1 : wt1 1 = 0 := rfl
  have w2 : wt1 2 = -1 := rfl
  fin_cases a <;> fin_cases b <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, w0, w1, w2, zpow_one, zpow_zero, _root_.zpow_neg,
      Units.val_one, ne_eq, not_true_eq_false] at hab ⊢ <;> assumption

private theorem lu_up {R : Type} [CommRing R] (U k T : Matrix (Fin 3) (Fin 3) R) (e : U * k = k * T)
    (hU : ∀ a b, wt a b < 0 → U a b = 0) (hT : ∀ a b, wt a b < 0 → T a b = 0)
    (hu : ∀ a b, a ≠ b → IsUnit (U a a - T b b)) :
    ∀ a b, wt a b < 0 → k a b = 0 := by
  have e10 := congrFun (congrFun e 1) 0
  have e20 := congrFun (congrFun e 2) 0
  have e21 := congrFun (congrFun e 2) 1
  have u10 := hU 1 0 (by decide)
  have u20 := hU 2 0 (by decide)
  have u21 := hU 2 1 (by decide)
  have t10 := hT 1 0 (by decide)
  have t20 := hT 2 0 (by decide)
  have t21 := hT 2 1 (by decide)
  simp only [Matrix.mul_apply, Fin.sum_univ_three, u10, u20, u21, t10, t20, t21] at e10 e20 e21
  have k20 : k 2 0 = 0 := (hu 2 0 (by decide)).mul_right_eq_zero.1 (by linear_combination e20)
  have k10 : k 1 0 = 0 := (hu 1 0 (by decide)).mul_right_eq_zero.1 (by
    rw [k20] at e10; linear_combination e10)
  have k21 : k 2 1 = 0 := (hu 2 1 (by decide)).mul_right_eq_zero.1 (by
    rw [k20] at e21; linear_combination e21)
  intro a b hab
  fin_cases a <;> fin_cases b <;> first | assumption | exact absurd hab (by decide)

private theorem lu_J {R : Type} [CommRing R] (X : Matrix (Fin 3) (Fin 3) R) (a b : Fin 3) :
    (Jmat R 3 * Xᵀ * Jmat R 3) a b = X b.rev a.rev := by
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev]

end UpperTheory.V.UnitaryThreeInertia

theorem UpperTheory.V.UnitaryThreeInertia.lt_upper :
    ∀ {O R D : Type} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R] [Group D]
      (η : D →* ℤˣ) (Ψ : D →* Oˣ) (r : D →* GG (m := 3) (R := R)) (x : D),
      Red η Ψ r → η x = 1 → IsUnit ((Ψ x : O) ^ 2 - 1) → Upper η r → ∀ g a b, wt a b < 0 → (r g).mat a b = 0 := by
  intro O R D _ _ _ _ _ _ η Ψ r x hr hx hΨ hU g
  rcases Int.units_eq_one_or (η g) with hg | hg
  · exact hU g hg
  have hX : ∀ x a, residue R ((r x).mat a a) = residue R (algebraMap O R ((Ψ x ^ wt1 a : Oˣ) : O)) := by
    intro x a
    have := (residue_eq_zero_iff _).2 (hr.red x a a)
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
    rw [this]
    simp only [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.map_apply, Matrix.diagonal_apply_eq]
  obtain ⟨y, hy⟩ : ∃ y, y = g⁻¹ * x⁻¹ * g := ⟨_, rfl⟩
  have hηy : η y = 1 := by simp [hy, hx]
  have hΨy : Ψ y = (Ψ x)⁻¹ := by simp [hy]
  have rx : (r x).right = 1 := (hr.mult x).trans hx
  have ry : (r y).right = 1 := (hr.mult y).trans hηy
  have rg : (r g).right = -1 := (hr.mult g).trans hg
  have e0 : r x * r g = r g * (r y)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, hy]; congr 1; group
  have e1 : (r x).left * (r g).left = (r g).left * theta ((r y).left⁻¹) := by
    have := congrArg SemidirectProduct.left e0
    simpa [rx, ry, rg] using this
  have e2 : (r x).mat * (r g).mat = (r g).mat * (Jmat R 3 * (r y).matᵀ * Jmat R 3) := by
    have := congrArg Units.val e1
    rwa [Units.val_mul, Units.val_mul, theta_val, inv_inv] at this
  refine lu_up _ _ _ e2 (hU x hx) (fun a b hab => ?_) (fun a b hab => ?_)
  · rw [lu_J]
    refine hU y hηy _ _ ?_
    have : wt b.rev a.rev = wt a b := by fin_cases a <;> fin_cases b <;> rfl
    rwa [this]
  · have w : wt1 b.rev = -wt1 b := by fin_cases b <;> rfl
    rw [lu_J, ← residue_ne_zero_iff_isUnit, map_sub, hX, hX, ← map_sub,
      ← map_sub, residue_ne_zero_iff_isUnit, hΨy, w, _root_.inv_zpow', neg_neg]
    exact (lu_unit (Ψ x) hΨ a b hab).map _
end

section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem entIn_sub_iff {C : Type} [CommRing C] (I : Ideal C) (X Y : Matrix (Fin 3) (Fin 3) C) :
    EntIn I (X - Y) ↔ X.map (Ideal.Quotient.mk I) = Y.map (Ideal.Quotient.mk I) := by
  constructor
  · intro h
    ext a b
    simp only [Matrix.map_apply]
    exact Ideal.Quotient.eq.mpr (by simpa [Matrix.sub_apply] using h a b)
  · intro h a b
    have hab := congrFun (congrFun h a) b
    simp only [Matrix.map_apply] at hab
    simpa [Matrix.sub_apply] using Ideal.Quotient.eq.mp hab

private theorem congOne_iff {C : Type} [CommRing C] (I : Ideal C) (h : GL (Fin 3) C) :
    CongOne I h ↔ GeneralLinearGroup.map (Ideal.Quotient.mk I) h = 1 := by
  unfold CongOne
  rw [entIn_sub_iff, Matrix.map_one _ (map_zero _) (map_one _)]
  constructor
  · intro e
    exact Units.ext e
  · intro e
    exact congrArg Units.val e

private theorem map_conjBy {C D : Type} [CommRing C] [Group D] (I : Ideal C) (h : GL (Fin 3) C)
    (hh : CongOne I h) (r : D →* GG (m := 3) (R := C)) (g : D) :
    GG.map (Ideal.Quotient.mk I) (conjBy h r g) = GG.map (Ideal.Quotient.mk I) (r g) := by
  have e : GG.map (Ideal.Quotient.mk I) (GG.ofGL h) = 1 := by
    unfold GG.map
    rw [SemidirectProduct.map_inl, (congOne_iff I h).1 hh, map_one]
  simp only [conjBy, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, e,
    one_mul, inv_one, mul_one]

private theorem mats_conjBy {C D : Type} [CommRing C] [Group D] (h : GL (Fin 3) C)
    (r : D →* GG (m := 3) (R := C)) (g : D) :
    mats (conjBy h r) g =
      (h : Matrix (Fin 3) (Fin 3) C) * mats r g *
        ((sgnAct 3 C (r g).right h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
  simp [mats, GG.mat, conjBy, GG.ofGL, SemidirectProduct.mul_left, Units.val_mul]

theorem UpperTheory.V.UnitaryThreeInertia.lt_red_conj :
    ∀ {O R D : Type} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R]
      [Group D] [TopologicalSpace D] (η : D →* ℤˣ) (Ψ : D →* Oˣ)
      (r : D →* GG (m := 3) (R := R)) (h : GL (Fin 3) R),
      InHat h → Red η Ψ r → InHat h⁻¹ ∧ Red η Ψ (conjBy h r) ∧ (IsLocallyConstant η → IsLocallyConstant (mats r) → IsLocallyConstant (mats (conjBy h r))) := by
  intro O R D _ _ _ _ _ _ _ η Ψ r h hh hr
  have hinv : InHat h⁻¹ := by
    show CongOne (maximalIdeal R) h⁻¹
    rw [congOne_iff, map_inv, (congOne_iff _ h).mp hh, inv_one]
  have hright : ∀ g, (conjBy h r g).right = (r g).right := by
    intro g
    simp [conjBy, GG.ofGL]
  refine ⟨hinv, ⟨fun g => (hright g).trans (hr.mult g), fun g => ?_⟩, fun hη hm => ?_⟩
  · rw [entIn_sub_iff]
    have h0 := (entIn_sub_iff _ _ _).mp (hr.red g)
    rw [← h0, ← GG.map_mat, ← GG.map_mat, map_conjBy _ h hh]
  · have hfun : mats (conjBy h r) = fun g =>
        (h : Matrix (Fin 3) (Fin 3) R) * mats r g *
          ((sgnAct 3 R (η g) h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
      funext g
      rw [mats_conjBy, hr.mult g]
    rw [hfun]
    exact IsLocallyConstant.comp₂ hm hη fun M s =>
      (h : Matrix (Fin 3) (Fin 3) R) * M * ((sgnAct 3 R s h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)
end

section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

section SlopeTestRemainingChoices

variable {O R D : Type} [CommRing O] [CommRing R] [Algebra O R] [Group D]

private theorem conj_app (h : GL (Fin 3) R) (r : D →* GG (m := 3) (R := R)) (g : D) :
    conjBy h r g = GG.ofGL h * r g * (GG.ofGL h)⁻¹ := rfl

private theorem conj_comp {D' : Type} [Group D'] (h : GL (Fin 3) R) (r : D →* GG (m := 3) (R := R)) (f : D' →* D) :
    (conjBy h r).comp f = conjBy h (r.comp f) := rfl

private theorem conj_swap (T h : GL (Fin 3) R) (r : D →* GG (m := 3) (R := R)) :
    conjBy (T * h * T⁻¹)⁻¹ (conjBy T r) = conjBy T (conjBy h⁻¹ r) := by
  ext1 g
  simp only [conj_app, map_mul, map_inv, _root_.mul_inv_rev, inv_inv]
  group

private theorem wt_self (a : Fin 3) : wt a a = 0 := sub_self _

private theorem tor_conj_apply (t : Rˣ) (h : GL (Fin 3) R) (a b : Fin 3) :
    ((tor R t * h * (tor R t)⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) a b =
      ((t ^ wt a b : Rˣ) : R) * (h : Matrix (Fin 3) (Fin 3) R) a b := by
  rw [← map_inv, Units.val_mul, Units.val_mul, tor_val, tor_val, Matrix.mul_diagonal,
    Matrix.diagonal_mul, wt, _root_.zpow_sub, Units.val_mul, _root_.inv_zpow]
  ring

private theorem weighted_entry_sub_mem_ideal (I : Ideal R) (t : Rˣ) (X Y : Matrix (Fin 3) (Fin 3) R)
    (hY : ∀ a b, a ≠ b → Y a b = 0) (h : EntIn I (X - Y)) (a b : Fin 3) :
    ((t ^ wt a b : Rˣ) : R) * X a b - Y a b ∈ I := by
  by_cases hab : a = b
  · subst hab
    rw [wt_self, zpow_zero, Units.val_one, one_mul]
    have := h a a
    rwa [Matrix.sub_apply] at this
  · rw [hY a b hab, sub_zero]
    apply Ideal.mul_mem_left
    have := h a b
    rwa [Matrix.sub_apply, hY a b hab, sub_zero] at this

private theorem inHat_tor [IsLocalRing R] (t : Rˣ) (h : GL (Fin 3) R) (hh : InHat h) :
    InHat (tor R t * h * (tor R t)⁻¹) := by
  intro a b
  rw [Matrix.sub_apply, tor_conj_apply]
  exact weighted_entry_sub_mem_ideal _ t _ 1 (fun a b hab => Matrix.one_apply_ne hab) hh a b

private theorem triIn_tor {η : D →* ℤˣ} {Ψ : D →* Oˣ} {I : Subgroup D} {r : D →* GG (m := 3) (R := R)} {h : GL (Fin 3) R}
    (t : Rˣ) (H : TriIn η Ψ I r h) : TriIn η Ψ I (conjBy (tor R t) r) (tor R t * h * (tor R t)⁻¹) := by
  obtain ⟨htri, hine⟩ := H
  refine ⟨?_, ?_⟩
  · rw [conj_swap]
    unfold Upper at htri ⊢
    intro g hg a b hab
    rw [(conjBy_tor _ t).1 g a b, htri g hg a b hab, mul_zero]
  · intro s hs hη a
    rw [conj_swap, (conjBy_tor _ t).1 s a a, wt_self, zpow_zero, Units.val_one, one_mul]
    exact hine s hs hη a

private theorem diagIn_tor {η : D →* ℤˣ} {Ψ : D →* Oˣ} {I : Subgroup D} {r : D →* GG (m := 3) (R := R)} {h : GL (Fin 3) R}
    (t : Rˣ) (H : DiagIn η Ψ I r h) : DiagIn η Ψ I (conjBy (tor R t) r) (tor R t * h * (tor R t)⁻¹) := by
  obtain ⟨H1, hlow⟩ := H
  refine ⟨triIn_tor t H1, ?_⟩
  rw [conj_swap]
  unfold Lower at hlow ⊢
  intro g hg a b hab
  rw [(conjBy_tor _ t).1 g a b, hlow g hg a b hab, mul_zero]

end SlopeTestRemainingChoices

theorem UpperTheory.V.UnitaryThreeInertia.isPt_tor :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] {G Γ ι : Type} [Group G] [Group Γ] [TopologicalSpace Γ] (F : Frame O G Γ ι) {R : Type} [CommRing R] [IsLocalRing R] [Algebra O R] (g₁ : Γ) (r : Γ →* GG (m := 3) (R := R)) (t : Rˣ), F.IsPt g₁ r → F.IsPt g₁ (conjBy (tor R t) r) := by
  intro O _ _ G Γ ι _ _ _ F R _ _ _ g₁ r t H
  obtain ⟨k1, k2, k3, -⟩ := conjBy_tor r t
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, k3 _ _ H.norm⟩, ?_⟩
  · intro g
    rw [k2, H.mult g]
  · intro g a b
    rw [Matrix.sub_apply, k1]
    refine weighted_entry_sub_mem_ideal _ t _ _ ?_ (H.red g) a b
    intro a b hab
    rw [Matrix.map_apply, GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_apply_ne _ hab, map_zero]
  · intro v
    obtain ⟨h1, h2, h3⟩ := H.loc v
    rw [conj_comp]
    refine ⟨fun hv => ?_, fun hv => ?_, fun hv s hs => ?_⟩
    · obtain ⟨h, hh, ht⟩ := h1 hv
      exact ⟨_, inHat_tor t h hh, triIn_tor t ht⟩
    · obtain ⟨h, hh, ht⟩ := h2 hv
      exact ⟨_, inHat_tor t h hh, diagIn_tor t ht⟩
    · rw [conj_app, h3 hv s hs, mul_one, mul_inv_cancel]
  · intro n
    have e : (fun g => (conjBy (tor R t) r g).mat.map (Ideal.Quotient.mk (maximalIdeal R ^ n))) =
        (fun X : Matrix (Fin 3) (Fin 3) (R ⧸ maximalIdeal R ^ n) =>
          Matrix.of fun a b => Ideal.Quotient.mk (maximalIdeal R ^ n) ((t ^ wt a b : Rˣ) : R) * X a b) ∘
        fun g => (r g).mat.map (Ideal.Quotient.mk (maximalIdeal R ^ n)) := by
      funext g
      ext a b
      simp only [Function.comp_apply, Matrix.map_apply, Matrix.of_apply, k1, map_mul]
    rw [e]
    exact (H.cont n).comp _
end

section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem ltgs_inv_mem {M : Type} [Group M] [Finite M] (S : Submonoid M) {x : M} (hx : x ∈ S) : x⁻¹ ∈ S := by
  have hk : 0 < orderOf x := orderOf_pos x
  have e : x⁻¹ = x ^ (orderOf x - 1) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', Nat.sub_add_cancel hk, pow_orderOf_eq_one]
  rw [e]
  exact S.pow_mem hx _

theorem UpperTheory.V.UnitaryThreeInertia.lt_grSub :
    ∀ {O R : Type} [CommRing O] [CommRing R] [Algebra O R] [Finite R] (ℬ : ℤ → Submodule O R) [SetLike.GradedMonoid ℬ],
      ∃ S : Subgroup (GG (m := 3) (R := R)), ∀ x, x ∈ S ↔ GrMat ℬ x.mat := by
  intro O R _ _ _ _ ℬ _
  classical
  have hwt : ∀ a c b : Fin 3, wt a c + wt c b = wt a b := by
    intro a c b; simp only [wt]; ring
  have hwrev : ∀ a b : Fin 3, wt b.rev a.rev = wt a b := by
    intro a b; fin_cases a <;> fin_cases b <;> rfl
  have hone : GrMat ℬ (1 : Matrix (Fin 3) (Fin 3) R) := by
    intro a b
    by_cases h : a = b
    · subst h
      rw [Matrix.one_apply_eq]
      have h0 : wt a a = 0 := by simp [wt]
      rw [h0]
      exact SetLike.GradedOne.one_mem
    · rw [Matrix.one_apply_ne h]
      exact Submodule.zero_mem _
  have hmul : ∀ X Y : Matrix (Fin 3) (Fin 3) R, GrMat ℬ X → GrMat ℬ Y → GrMat ℬ (X * Y) := by
    intro X Y hX hY a b
    rw [Matrix.mul_apply]
    refine Submodule.sum_mem _ fun c _ => ?_
    rw [← hwt a c b]
    exact SetLike.GradedMul.mul_mem (hX a c) (hY c b)
  let T : Submonoid (GL (Fin 3) R) :=
    { carrier := {g | GrMat ℬ (g : Matrix (Fin 3) (Fin 3) R)}
      mul_mem' := fun {g h} hg hh => by
        show GrMat ℬ ((g * h : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)
        rw [Units.val_mul]
        exact hmul _ _ hg hh
      one_mem' := by
        show GrMat ℬ ((1 : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)
        rw [Units.val_one]
        exact hone }
  have hinv : ∀ g : GL (Fin 3) R, GrMat ℬ (g : Matrix (Fin 3) (Fin 3) R) →
      GrMat ℬ ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) :=
    fun g hg => ltgs_inv_mem T (x := g) hg
  have hJ : ∀ (M : Matrix (Fin 3) (Fin 3) R) (a b : Fin 3),
      (Jmat R 3 * M * Jmat R 3) a b = M a.rev b.rev := by
    intro M a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat] <;> rfl
  have htheta : ∀ g : GL (Fin 3) R, GrMat ℬ (g : Matrix (Fin 3) (Fin 3) R) →
      GrMat ℬ ((theta g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
    intro g hg a b
    rw [theta_val, hJ, Matrix.transpose_apply, ← hwrev a b]
    exact hinv g hg b.rev a.rev
  have hact : ∀ (s : ℤˣ) (g : GL (Fin 3) R), GrMat ℬ (g : Matrix (Fin 3) (Fin 3) R) →
      GrMat ℬ ((sgnAct 3 R s g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
    intro s g hg
    rcases Int.units_eq_one_or s with rfl | rfl
    · rw [sgnAct_one]; exact hg
    · rw [sgnAct_neg_one]; exact htheta g hg
  haveI : Finite (GG (m := 3) (R := R)) :=
    Finite.of_injective (fun x : GG (m := 3) (R := R) => (x.left, x.right))
    (fun x y h => SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  let S0 : Submonoid (GG (m := 3) (R := R)) :=
    { carrier := {x | GrMat ℬ x.mat}
      mul_mem' := fun {x y} hx hy => by
        show GrMat ℬ ((x * y).left : Matrix (Fin 3) (Fin 3) R)
        rw [SemidirectProduct.mul_left, Units.val_mul]
        exact hmul _ _ hx (hact _ _ hy)
      one_mem' := by
        show GrMat ℬ ((1 : GG (m := 3) (R := R)).left : Matrix (Fin 3) (Fin 3) R)
        rw [SemidirectProduct.one_left, Units.val_one]
        exact hone }
  exact ⟨{ S0 with inv_mem' := fun {x} hx => ltgs_inv_mem S0 hx }, fun x => Iff.rfl⟩
end

section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

section
variable {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜]

private theorem gr_mul {X Y : Matrix (Fin 3) (Fin 3) R} (hX : GrMat 𝒜 X) (hY : GrMat 𝒜 Y) :
    GrMat 𝒜 (X * Y) := by
  intro a b
  simp only [Matrix.mul_apply]
  refine Submodule.sum_mem _ fun c _ => ?_
  have h := SetLike.GradedMul.mul_mem (hX a c) (hY c b)
  have e : wt a c + wt c b = wt a b := by simp only [wt]; ring
  rwa [e] at h

private theorem gr_one : GrMat 𝒜 (1 : Matrix (Fin 3) (Fin 3) R) := by
  intro a b
  by_cases h : a = b
  · subst h
    rw [Matrix.one_apply_eq]
    have e : wt a a = 0 := by simp [wt]
    rw [e]
    exact SetLike.GradedOne.one_mem
  · rw [Matrix.one_apply_ne h]
    exact zero_mem _

private theorem gr_pow {g : GL (Fin 3) R} (hg : GrMat 𝒜 (g : Matrix (Fin 3) (Fin 3) R)) (n : ℕ) :
    GrMat 𝒜 ((g ^ n : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  induction n with
  | zero => rw [pow_zero]; exact gr_one 𝒜
  | succ n ih => rw [pow_succ, Units.val_mul]; exact gr_mul 𝒜 ih hg

private theorem gr_inv [Finite R] {g : GL (Fin 3) R} (hg : GrMat 𝒜 (g : Matrix (Fin 3) (Fin 3) R)) :
    GrMat 𝒜 ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  have hn := orderOf_pos g
  have e : g⁻¹ = g ^ (orderOf g - 1) := by
    symm
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel hn, pow_orderOf_eq_one]
  rw [e]
  exact gr_pow 𝒜 hg _

private theorem gr_theta [Finite R] {g : GL (Fin 3) R} (hg : GrMat 𝒜 (g : Matrix (Fin 3) (Fin 3) R)) :
    GrMat 𝒜 ((theta g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  rw [theta_val]
  have hi := gr_inv 𝒜 hg
  have key : ∀ (M : Matrix (Fin 3) (Fin 3) R) (a b : Fin 3),
      (Jmat R 3 * Mᵀ * Jmat R 3) a b = M b.rev a.rev := by
    intro M a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Jmat, Fin.sum_univ_three, Fin.rev]
  intro a b
  rw [key]
  have e : wt b.rev a.rev = wt a b := by fin_cases a <;> fin_cases b <;> rfl
  rw [← e]
  exact hi _ _

private theorem gr_act [Finite R] (s : ℤˣ) {g : GL (Fin 3) R} (hg : GrMat 𝒜 (g : Matrix (Fin 3) (Fin 3) R)) :
    GrMat 𝒜 ((sgnAct 3 R s g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · rw [sgnAct_one]; exact hg
  · rw [sgnAct_neg_one]; exact gr_theta 𝒜 hg

end

theorem UpperTheory.graded_matrix_mul_inv :
    ∀ {O R : Type} [CommRing O] [CommRing R] [Algebra O R] [Finite R]
      (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜] (x y : GG (m := 3) (R := R)),
      GrMat 𝒜 x.mat → GrMat 𝒜 y.mat → GrMat 𝒜 (x * y).mat ∧ GrMat 𝒜 (x⁻¹).mat := by
  intro O R _ _ _ _ 𝒜 _ x y hx hy
  unfold GG.mat at *
  constructor
  · rw [SemidirectProduct.mul_left, Units.val_mul]
    exact gr_mul 𝒜 hx (gr_act 𝒜 _ hy)
  · rw [SemidirectProduct.inv_left]
    exact gr_act 𝒜 _ (gr_inv 𝒜 hx)
end
