module

import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LieLiftsTangentReduction
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.PiTensorProduct
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.CancelSecAct
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.SpanXLeKerAevalZero
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle003

@[expose] public section

section

noncomputable section

namespace GlobalTheory.ArcLieCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.LieLiftsTangentReduction
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)
open scoped CategoryTheory.Obj

section General

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

theorem prod_Oφ_zero {T : Over (Sp R)} (b : T ⟶ D.P.A) {Z : Scheme.{0}} (π : Z ⟶ T.left) (σ : Z ⟶ Sp R)
    (hb : π ≫ b.left = σ ≫ eSec D.P.A) (χ : D.X) {U : Type} [CommGroup U] (h : (Z ⟶ D.P.A.left) → U) :
    ∏ k, h (π ≫ D.Oφ b χ k) ^ Oinvε k = 1 := by
  have hσ : σ = π ≫ T.hom := by
    have e : eSec D.P.A ≫ D.P.A.hom = 𝟙 (Sp R) := Over.w η[D.P.A]
    rw [← Over.w b, ← Category.assoc, hb, Category.assoc]
    exact ((congrArg (σ ≫ ·) e).trans (Category.comp_id _)).symm
  let FinalForm : Over (Sp R) := Over.mk (π ≫ T.hom)
  let π' : FinalForm ⟶ T := Over.homMk π rfl
  have h1 : π' ≫ b = 1 := Over.OverMorphism.ext (hb.trans (by
    rw [hσ]
    show _ = (toUnit FinalForm ≫ η[D.P.A]).left
    simp [eSec, FinalForm]))
  have e : ∀ k, π ≫ D.Oφ b χ k = D.Oφ (1 : FinalForm ⟶ D.P.A) χ k := fun k =>
    (WeightPf.Oφ_comp π' b χ k).trans (by rw [h1])
  simp only [e]
  rw [Fin.prod_univ_four]
  show h ((1 : FinalForm ⟶ D.P.A) * (toUnit FinalForm ≫ D.c χ)).left ^ (-1 : ℤ) * h (toUnit FinalForm ≫ D.c χ).left ^ (1 : ℤ) *
    h (1 : FinalForm ⟶ D.P.A).left ^ (1 : ℤ) * h (1 : FinalForm ⟶ D.P.A).left ^ (-1 : ℤ) = 1
  simp

theorem exists_isZero (T : Over (Sp R)) : ∃ g : GtPt D T, g.IsZero := by
  apply GlobalTheory.FormalValue.exists_isZero <;> assumption


variable {I : Ideal R} {e : ℕ} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)


omit [IsDomain R] in
theorem epsRed_hom : epsRed R ≫ (epsR R).hom = 𝟙 _ := by
  show Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have h3 : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R :=
    RingHom.ext fun r => (TrivSqZeroExt.fstHom R R R).commutes r
  rw [h3]
  exact Spec.map_id _

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section ThetaShiftProofs

variable {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {K₁ : Type} [Field K₁] {b : O →+* K₁}
  {a : ArcIn Dw l β K₁ b} {χ : Sp (PowerSeries K₁) ⟶ Y.X}

end ThetaShiftProofs


end GlobalTheory.ArcLieCompare
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.UnitaryLieComplexification

open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies

variable {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ}

noncomputable def cj (J Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := -(J⁻¹ * Zᴴ * J)

theorem cj_add (Z W : Matrix (Fin n) (Fin n) ℂ) : cj J (Z + W) = cj J Z + cj J W := by
  simp only [cj, conjTranspose_add, mul_add, add_mul, neg_add]

theorem cj_sub (Z W : Matrix (Fin n) (Fin n) ℂ) : cj J (Z - W) = cj J Z - cj J W := by
  simp only [cj, conjTranspose_sub, mul_sub, sub_mul]
  abel

theorem cj_smul (c : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) : cj J (c • Z) = star c • cj J Z := by
  simp only [cj, conjTranspose_smul, mul_smul_comm, smul_mul_assoc, smul_neg]

theorem cj_cj (hJ : Jᴴ = J) (hu : IsUnit J.det) (Z : Matrix (Fin n) (Fin n) ℂ) : cj J (cj J Z) = Z := by
  simp only [cj, conjTranspose_neg, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hJ,
    mul_neg, neg_mul, neg_neg, Matrix.mul_assoc, Matrix.nonsing_inv_mul J hu, Matrix.mul_one]
  rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul J hu, Matrix.one_mul]

theorem mem_iff_cj (hu : IsUnit J.det) (X : Matrix (Fin n) (Fin n) ℂ) : X ∈ lieU J ↔ cj J X = X := by
  change Xᴴ * J + J * X = 0 ↔ _
  constructor
  · intro h
    rw [cj, Matrix.mul_assoc, eq_neg_of_add_eq_zero_left h, mul_neg, neg_neg, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul J hu, Matrix.one_mul]
  · intro h
    have : J * X = -(Xᴴ * J) := by
      conv_lhs => rw [← h]
      rw [cj, mul_neg, Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv J hu, Matrix.one_mul]
    rw [this, add_neg_cancel]

noncomputable def rePart (hJ : Jᴴ = J) (hu : IsUnit J.det) (Z : Matrix (Fin n) (Fin n) ℂ) : lieU J :=
  ⟨(1 / 2 : ℂ) • (Z + cj J Z), by
    rw [mem_iff_cj hu, cj_smul, cj_add, cj_cj hJ hu, add_comm]
    simp⟩

noncomputable def imPart (hJ : Jᴴ = J) (hu : IsUnit J.det) (Z : Matrix (Fin n) (Fin n) ℂ) : lieU J :=
  ⟨(1 / (2 * Complex.I) : ℂ) • (Z - cj J Z), by
    rw [mem_iff_cj hu, cj_smul, cj_sub, cj_cj hJ hu, ← neg_sub Z, smul_neg, ← neg_smul]
    congr 1
    simp⟩

theorem re_add_im (hJ : Jᴴ = J) (hu : IsUnit J.det) (Z : Matrix (Fin n) (Fin n) ℂ) :
    (rePart hJ hu Z).1 + Complex.I • (imPart hJ hu Z).1 = Z := by
  have h : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by field_simp
  simp only [rePart, imPart, smul_smul, h]
  module

theorem cj_mk (hu : IsUnit J.det) (X Y : lieU J) :
    cj J (X.1 + Complex.I • Y.1) = X.1 - Complex.I • Y.1 := by
  rw [cj_add, cj_smul, (mem_iff_cj hu _).1 X.2, (mem_iff_cj hu _).1 Y.2]
  simp [sub_eq_add_neg]

theorem rePart_mk (hJ : Jᴴ = J) (hu : IsUnit J.det) (X Y : lieU J) :
    rePart hJ hu (X.1 + Complex.I • Y.1) = X := by
  apply Subtype.ext
  simp only [rePart, cj_mk hu]
  module

theorem imPart_mk (hJ : Jᴴ = J) (hu : IsUnit J.det) (X Y : lieU J) :
    imPart hJ hu (X.1 + Complex.I • Y.1) = Y := by
  apply Subtype.ext
  simp only [imPart, cj_mk hu]
  have h : (1 / (2 * Complex.I)) * (2 * Complex.I) = 1 := by field_simp
  have h2 : X.1 + Complex.I • Y.1 - (X.1 - Complex.I • Y.1) = (2 * Complex.I) • Y.1 := by module
  rw [h2, smul_smul, h, one_smul]

theorem exists_mk (hJ : Jᴴ = J) (hu : IsUnit J.det) (Z : Matrix (Fin n) (Fin n) ℂ) :
    ∃ X Y : lieU J, Z = X.1 + Complex.I • Y.1 := ⟨_, _, (re_add_im hJ hu Z).symm⟩

theorem exists_extension (hJ : Jᴴ = J) (hu : IsUnit J.det) {A : Type} [Ring A] [Algebra ℂ A] (ρ : lieU J → A)
    (hadd : ∀ X Y, ρ (X + Y) = ρ X + ρ Y) (hsm : ∀ (c : ℝ) X, ρ (c • X) = (c : ℂ) • ρ X)
    (hlie : ∀ X Y Z : lieU J, Z.1 = X.1 * Y.1 - Y.1 * X.1 → ρ Z = ρ X * ρ Y - ρ Y * ρ X) :
    ∃ R : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A,
      (∀ Z, R Z = ρ (rePart hJ hu Z) + Complex.I • ρ (imPart hJ hu Z)) ∧ (∀ X : lieU J, R X.1 = ρ X) ∧
      ∀ Z W, R (Z * W - W * Z) = R Z * R W - R W * R Z := by
  have hsub : ∀ X Y, ρ (X - Y) = ρ X - ρ Y := by
    intro X Y
    have := hadd (X - Y) Y
    rw [sub_add_cancel] at this
    rw [this, add_sub_cancel_right]
  have h0 : ρ 0 = 0 := by
    have := hsub 0 0
    rwa [sub_self, sub_self] at this
  let r : Matrix (Fin n) (Fin n) ℂ → A := fun Z => ρ (rePart hJ hu Z) + Complex.I • ρ (imPart hJ hu Z)
  have key : ∀ X Y : lieU J, r (X.1 + Complex.I • Y.1) = ρ X + Complex.I • ρ Y := by
    intro X Y
    simp only [r, rePart_mk, imPart_mk]
  have hII : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (m : M), Complex.I • Complex.I • m = -m := by
    intro M _ _ m
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  have hbr : ∀ X Y : lieU J, ρ ⁅X, Y⁆ = ρ X * ρ Y - ρ Y * ρ X := fun X Y => hlie X Y _ rfl
  have hbc : ∀ X Y : lieU J, (⁅X, Y⁆ : lieU J).1 = X.1 * Y.1 - Y.1 * X.1 := fun X Y => rfl
  refine ⟨{ toFun := r, map_add' := ?_, map_smul' := ?_ }, fun Z => rfl, ?_, ?_⟩
  · intro Z W
    obtain ⟨X, Y, rfl⟩ := exists_mk hJ hu Z
    obtain ⟨X', Y', rfl⟩ := exists_mk hJ hu W
    have : X.1 + Complex.I • Y.1 + (X'.1 + Complex.I • Y'.1) = (X + X').1 + Complex.I • (Y + Y').1 := by
      change _ = (X.1 + X'.1) + Complex.I • (Y.1 + Y'.1)
      module
    rw [this, key, key, key, hadd, hadd]
    module
  · intro c Z
    obtain ⟨X, Y, rfl⟩ := exists_mk hJ hu Z
    have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
    generalize c.re = a at hc
    generalize c.im = b at hc
    subst hc
    have : ((a : ℂ) + (b : ℂ) * Complex.I) • (X.1 + Complex.I • Y.1) =
        (a • X - b • Y).1 + Complex.I • (b • X + a • Y).1 := by
      change _ = ((a : ℂ) • X.1 - (b : ℂ) • Y.1) + Complex.I • ((b : ℂ) • X.1 + (a : ℂ) • Y.1)
      simp only [add_smul, smul_add, mul_smul, hII]
      module
    rw [this, key, key, hsub, hadd, hsm, hsm, hsm, hsm]
    simp only [RingHom.id_apply, add_smul, smul_add, mul_smul, hII]
    module
  · intro X
    have := key X 0
    simpa [h0] using this
  · intro Z W
    obtain ⟨X, Y, rfl⟩ := exists_mk hJ hu Z
    obtain ⟨X', Y', rfl⟩ := exists_mk hJ hu W
    have : (X.1 + Complex.I • Y.1) * (X'.1 + Complex.I • Y'.1) - (X'.1 + Complex.I • Y'.1) * (X.1 + Complex.I • Y.1) =
        (⁅X, X'⁆ - ⁅Y, Y'⁆ : lieU J).1 + Complex.I • (⁅X, Y'⁆ + ⁅Y, X'⁆ : lieU J).1 := by
      change _ = ((X.1 * X'.1 - X'.1 * X.1) - (Y.1 * Y'.1 - Y'.1 * Y.1)) +
        Complex.I • ((X.1 * Y'.1 - Y'.1 * X.1) + (Y.1 * X'.1 - X'.1 * Y.1))
      simp only [add_mul, mul_add, mul_smul_comm, smul_mul_assoc, smul_add, hII]
      module
    change r _ = r _ * r _ - r _ * r _
    rw [this, key, key, key, hsub, hadd, hbr, hbr, hbr, hbr]
    simp only [add_mul, mul_add, mul_smul_comm, smul_mul_assoc, smul_add, hII]
    module

theorem glRel_and_span : ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) ℂ), Jᴴ = J → IsUnit J.det → ∃ P Q : Fin n → Fin n → GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, (∀ a b, (P a b).1 = (1 / 2 : ℂ) • (Matrix.single a b 1 + -(J⁻¹ * (Matrix.single a b (1 : ℂ))ᴴ * J)) ∧ (Q a b).1 = (1 / (2 * Complex.I)) • (Matrix.single a b 1 - -(J⁻¹ * (Matrix.single a b (1 : ℂ))ᴴ * J))) ∧ ∀ (A : Type) [Ring A] [Algebra ℂ A] (ρ : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J → A), (∀ X Y, ρ (X + Y) = ρ X + ρ Y) → (∀ (c : ℝ) X, ρ (c • X) = (c : ℂ) • ρ X) → (∀ X Y Z : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, Z.1 = X.1 * Y.1 - Y.1 * X.1 → ρ Z = ρ X * ρ Y - ρ Y * ρ X) → Formalism.REAL.GlRel (fun a b => ρ (P a b) + Complex.I • ρ (Q a b)) ∧ ∀ X, ρ X ∈ Submodule.span ℂ (Set.range fun p : Fin n × Fin n => ρ (P p.1 p.2) + Complex.I • ρ (Q p.1 p.2)) := by
  intro n J hJ hu
  refine ⟨fun a b => rePart hJ hu (Matrix.single a b 1), fun a b => imPart hJ hu (Matrix.single a b 1),
    fun a b => ⟨rfl, rfl⟩, ?_⟩
  intro A _ _ ρ hadd hsm hlie
  obtain ⟨R, hR, hX, hc⟩ := exists_extension hJ hu ρ hadd hsm hlie
  simp only [← hR]
  constructor
  · intro a b c d
    simp only
    rw [← hc, map_sub]
    congr 1
    · split_ifs with h
      · subst h; rw [Matrix.single_mul_single_same, one_mul]
      · rw [Matrix.single_mul_single_of_ne (h := h), map_zero]
    · split_ifs with h
      · subst h; rw [Matrix.single_mul_single_same, one_mul]
      · rw [Matrix.single_mul_single_of_ne (h := h), map_zero]
  · intro X

    rw [← hX, Matrix.matrix_eq_sum_single X.1, map_sum]
    refine Submodule.sum_mem _ fun a _ => ?_

    rw [map_sum]
    refine Submodule.sum_mem _ fun b _ => ?_
    have : Matrix.single a b (X.1 a b) = X.1 a b • Matrix.single a b (1 : ℂ) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [this, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(a, b), rfl⟩)

end GlobalTheory.UnitaryLieComplexification
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.EnvWords

theorem mem_span_words (L : Type) [LieRing L] [LieAlgebra ℝ L] (u : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L)) :
    u ∈ Submodule.span ℂ (Set.range fun l : List L =>
      (l.map fun X => UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)).prod) := by
  have hs : Function.Surjective (UniversalEnvelopingAlgebra.mkAlgHom ℂ (ℂ ⊗[ℝ] L)) :=
    fun u => Quotient.exists_rep u
  obtain ⟨t, rfl⟩ := hs u
  induction t using TensorAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[], rfl⟩)
  | ι x =>
    change UniversalEnvelopingAlgebra.ι ℂ x ∈ _
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul z X =>
      have h : z ⊗ₜ[ℝ] X = z • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h, map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[X], by simp⟩)
    | add x y hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | mul a b ha hb =>
    rw [map_mul]
    have h := Submodule.mul_mem_mul ha hb
    rw [Submodule.span_mul_span] at h
    refine Submodule.span_mono ?_ h
    rintro _ ⟨_, ⟨l, rfl⟩, _, ⟨m, rfl⟩, rfl⟩
    exact ⟨l ++ m, by simp only [List.map_append, List.prod_append]⟩
  | add a b ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb

theorem envOf_surjective : ∀ (D : D7) (V : HSp D) (τ : D.what₂.Tau),
    Function.Surjective (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.envOf V τ) := by
  intro D V τ u
  exact (Finsupp.mem_span_range_iff_exists_finsupp).1 (mem_span_words (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ) u)

end GlobalTheory.EnvWords
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

namespace GlobalTheory.EnvelopingExtension

theorem exists_algHom_of_real (L : Type) [LieRing L] [LieAlgebra ℝ L] (A : Type) [Ring A] [Algebra ℂ A] (ρ : L → A)
    (hadd : ∀ X Y, ρ (X + Y) = ρ X + ρ Y) (hsmul : ∀ (c : ℝ) X, ρ (c • X) = (c : ℂ) • ρ X)
    (hbr : ∀ X Y, ρ ⁅X, Y⁆ = ρ X * ρ Y - ρ Y * ρ X) :
    ∃ π : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L) →ₐ[ℂ] A,
      ∀ X, π (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) = ρ X := by
  let f : L →ₗ[ℝ] A :=
    { toFun := ρ
      map_add' := hadd
      map_smul' := fun c X => by
        rw [hsmul]
        exact Complex.coe_smul c (ρ X) }
  let F : ℂ ⊗[ℝ] L →ₗ[ℂ] A := f.liftBaseChange ℂ
  have hF : ∀ (a : ℂ) (x : L), F (a ⊗ₜ x) = a • ρ x := fun a x => by
    simp [F, f, LinearMap.liftBaseChange_tmul]
  have hlie : ∀ u v : ℂ ⊗[ℝ] L, F ⁅u, v⁆ = ⁅F u, F v⁆ := by
    intro u v
    induction u using TensorProduct.induction_on with
    | zero => simp
    | add u₁ u₂ h₁ h₂ => rw [add_lie, map_add (f := _), h₁, h₂, map_add (f := _), add_lie]
    | tmul a x =>
      induction v using TensorProduct.induction_on with
      | zero => simp
      | add v₁ v₂ h₁ h₂ => rw [lie_add, map_add (f := _), h₁, h₂, map_add (f := _), lie_add]
      | tmul b y =>
        rw [LieAlgebra.ExtendScalars.bracket_tmul, hF, hF, hF, hbr, Ring.lie_def,
          smul_mul_smul_comm, smul_mul_smul_comm, mul_comm b a, smul_sub]
  let G : ℂ ⊗[ℝ] L →ₗ⁅ℂ⁆ A := { F with map_lie' := fun {u v} => hlie u v }
  refine ⟨UniversalEnvelopingAlgebra.lift ℂ G, fun X => ?_⟩
  rw [UniversalEnvelopingAlgebra.lift_ι_apply]
  change F ((1 : ℂ) ⊗ₜ X) = ρ X
  rw [hF, one_smul]

theorem exists_algHom_unitary : ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) ℂ) (A : Type) [Ring A] [Algebra ℂ A] (ρ : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J → A), (∀ X Y, ρ (X + Y) = ρ X + ρ Y) → (∀ (c : ℝ) X, ρ (c • X) = (c : ℂ) • ρ X) → (∀ X Y Z : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, Z.1 = X.1 * Y.1 - Y.1 * X.1 → ρ Z = ρ X * ρ Y - ρ Y * ρ X) → ∃ π : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J) →ₐ[ℂ] A, ∀ X, π (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) = ρ X := by
  intro n J A _ _ ρ hadd hsmul hbr
  exact exists_algHom_of_real _ A ρ hadd hsmul fun X Y => hbr X Y ⁅X, Y⁆ (by
    rw [LieSubalgebra.coe_bracket, Ring.lie_def])

end GlobalTheory.EnvelopingExtension

end
end
