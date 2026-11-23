module

public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.Bundle001
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.CategoryTheory.Category.Basic
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle004
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.LocalToGlobal.ProjectiveLattices.CrudeMin
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.Valuation.Integers
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle052
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001

@[expose] public section

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.MomentParseval

lemma sum_norm_sq_eq {ι : Type} [Fintype ι] (v : ι → ℂ) :
    ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) = v ⬝ᵥ star v := by
  push_cast
  unfold dotProduct
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.star_apply, Complex.star_def, Complex.mul_conj']

lemma sum_vecMul {ι : Type} [Fintype ι] [DecidableEq ι] (V : Matrix ι ι ℂ) (hV : V * Vᴴ = 1) (y : ι → ℂ) :
    ∑ e, ‖(star y ᵥ* V) e‖ ^ 2 = ∑ i, ‖y i‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [sum_norm_sq_eq, sum_norm_sq_eq, Matrix.star_vecMul, star_star, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, hV, Matrix.one_mulVec, dotProduct_comm]

lemma inv_mem {k r : ℕ} {g : Mx k r} (hg : g ∈ GG k r) : g⁻¹ ∈ GG k r := by
  have e : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  have h1 : g * g⁻¹ = 1 := PI.QuotSetU.UnitaryGroupMassFormula.SW.mul_inv_UH (k := k) (r := r) hg
  have h2 : (g⁻¹)ᴴ * gᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  show (g⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r * g⁻¹ = Formalism.QuantumDeterminants.Hpk k r
  calc (g⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Formalism.QuantumDeterminants.Hpk k r * g) * g⁻¹ := by rw [e]
    _ = ((g⁻¹)ᴴ * gᴴ) * Formalism.QuantumDeterminants.Hpk k r * (g * g⁻¹) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem sum_herm_sq : ∀ (k r : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (ρ : Mx k r → Matrix ι ι ℂ) (Γ U : Matrix ι ι ℂ) (d : ℕ) (om : ι → ℂ), IsFRep ρ Γ d → U ∈ Matrix.unitaryGroup ι ℂ → ∀ g ∈ GG k r, ∑ e, ‖Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ (fun c => U e c)) om‖ ^ 2 = ∑ i, ‖(ρ g⁻¹ *ᵥ om) i‖ ^ 2 := by
  intro k r ι _ _ ρ Γ U d om hρ hU g hg
  obtain ⟨hΓ, hΓ2, h1, hmul, hinv, -⟩ := hρ
  have hg' := inv_mem hg
  have hgg : g * g⁻¹ = 1 := PI.QuotSetU.UnitaryGroupMassFormula.SW.mul_inv_UH (k := k) (r := r) hg
  have hAB : ρ g * ρ g⁻¹ = 1 := by rw [← hmul g hg _ hg', hgg, h1]
  have hBA : (ρ g⁻¹)ᴴ * (ρ g)ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hAB, Matrix.conjTranspose_one]
  have key : Γ * ρ g = (ρ g⁻¹)ᴴ * Γ := by
    calc Γ * ρ g = ((ρ g⁻¹)ᴴ * (ρ g)ᴴ) * Γ * ρ g := by rw [hBA, Matrix.one_mul]
      _ = (ρ g⁻¹)ᴴ * ((ρ g)ᴴ * Γ * ρ g) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hinv g hg]
  have hUU : Uᵀ * (Uᵀ)ᴴ = 1 := by
    have h0 : Uᴴ * U = 1 := (Matrix.mem_unitaryGroup_iff').1 hU
    have h3 := congrArg Matrix.transpose h0
    rw [Matrix.transpose_mul, Matrix.transpose_one] at h3
    exact h3
  have hV : (Γ * Uᵀ) * (Γ * Uᵀ)ᴴ = 1 := by
    rw [Matrix.conjTranspose_mul, hΓ, Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hUU, Matrix.one_mul, hΓ2]
  rw [← sum_vecMul (Γ * Uᵀ) hV (ρ g⁻¹ *ᵥ om)]
  refine Finset.sum_congr rfl fun e _ => ?_
  congr 2
  unfold Formalism.QuantumDeterminants.herm
  rw [Matrix.mulVec_mulVec, key, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec,
    Matrix.dotProduct_mulVec, ← Matrix.vecMul_vecMul]
  rfl

end GlobalTheory.MomentParseval
end

section

open Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal ContDiff

noncomputable section

namespace BranchingSupport.TensInh

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem lenA_eq_lA (z : Fin (2 * r + k + 1) → ℂ) (g : Mx k r) (a : Fin (r + 1)) :
    lenA k r z g a = Formalism.MainNotions.S.lA k r z g a := by
  classical
  let Lm : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin (2 * r + k + 1)) :=
    { toFun := fun v => WithLp.toLp 2 (g⁻¹ *ᵥ v)
      map_add' := fun v w => by simp [Matrix.mulVec_add]
      map_smul' := fun c v => by simp [Matrix.mulVec_smul] }
  let S : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) := Submodule.span ℂ
    (Set.range fun b : {b : Fin r // b.val < a.val} => Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r b.1))
  have hlt : ∀ b : Fin (r + 1), b < a → b.val < r :=
    fun b hb => Nat.lt_of_lt_of_le hb (Nat.le_of_lt_succ a.2)
  have hfv : ∀ (b : Fin (r + 1)) (hb : b < a),
      Formalism.QuantumDeterminants.fvec k r z b = Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r ⟨b.val, hlt b hb⟩) := by
    intro b hb
    have hbr : b.val < r := hlt b hb
    simp [Formalism.QuantumDeterminants.fvec, hbr]
  have hspan : Submodule.span ℂ ((fun b => (WithLp.toLp 2 (g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z b) :
      EuclideanSpace ℂ (Fin (2 * r + k + 1)))) '' {b | b < a}) = S.map Lm := by
    rw [Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨_, ⟨⟨⟨b.val, hlt b hb⟩, hb⟩, rfl⟩, ?_⟩
      exact (congrArg (fun v => (WithLp.toLp 2 (g⁻¹ *ᵥ v) : EuclideanSpace ℂ (Fin (2 * r + k + 1))))
        (hfv b hb)).symm
    · rintro ⟨_, ⟨⟨b, hb⟩, rfl⟩, rfl⟩
      refine ⟨⟨b.val, by have := b.2; omega⟩, hb, ?_⟩
      show WithLp.toLp 2 (g⁻¹ *ᵥ _) = _
      rw [hfv _ hb]
      rfl
  have hd : ∀ y, dist (WithLp.toLp 2 (g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z a) : EuclideanSpace ℂ (Fin (2 * r + k + 1)))
      (WithLp.toLp 2 (g⁻¹ *ᵥ y)) = Formalism.MainNotions.S.eucl (g⁻¹ *ᵥ (Formalism.QuantumDeterminants.fvec k r z a - y)) := by
    intro y
    rw [EuclideanSpace.dist_eq]
    simp [Formalism.MainNotions.S.eucl, Matrix.mulVec_sub, Complex.normSq_eq_norm_sq, dist_eq_norm]
  unfold lenA Formalism.MainNotions.S.lA
  rw [hspan, Metric.infDist_eq_iInf, ← sInf_range]
  congr 1
  ext t
  constructor
  · rintro ⟨⟨_, y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, hd y⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨Lm y, y, hy, rfl⟩, hd y⟩

end BranchingSupport.TensInh
end
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.LengthCont

variable {n ι : Type} [Fintype n] [DecidableEq n]

def dst (x : n → ℂ) (f : ι → n → ℂ) (s : Set ι) (A : Matrix n n ℂ) : ℝ :=
  Metric.infDist (WithLp.toLp 2 (A *ᵥ x) : EuclideanSpace ℂ n)
    (Submodule.span ℂ ((fun b => (WithLp.toLp 2 (A *ᵥ f b) : EuclideanSpace ℂ n)) '' s) : Set _)

def opn (M : Matrix n n ℂ) : ℝ := ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) M‖

lemma opn_cont : Continuous (opn (n := n)) := by

  let L : Matrix n n ℂ →ₗ[ℂ] (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :=
    { toFun := fun M => Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) M
      map_add' := fun M N => map_add _ M N
      map_smul' := fun c M => map_smul _ c M }
  exact continuous_norm.comp (LinearMap.continuous_of_finiteDimensional L)

lemma opn_one [Nonempty n] : opn (1 : Matrix n n ℂ) = 1 := by
  unfold opn
  rw [map_one]
  exact norm_one

private lemma infDist_image_le_opNorm_mul {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →L[ℂ] E) (y : E) (K : Set E) (hK : K.Nonempty) :
    Metric.infDist (T y) (T '' K) ≤ ‖T‖ * Metric.infDist y K := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hδ : 0 < ε / (‖T‖ + 1) := by positivity
  obtain ⟨p, hp, hd⟩ := (Metric.infDist_lt_iff hK).1 (lt_add_of_pos_right (Metric.infDist y K) hδ)
  have hTε : ‖T‖ * (ε / (‖T‖ + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg T]
  calc Metric.infDist (T y) (T '' K) ≤ dist (T y) (T p) :=
        Metric.infDist_le_dist_of_mem (Set.mem_image_of_mem T hp)
    _ ≤ ‖T‖ * dist y p := by
        rw [dist_eq_norm, dist_eq_norm, ← map_sub]; exact T.le_opNorm _
    _ ≤ ‖T‖ * (Metric.infDist y K + ε / (‖T‖ + 1)) := by gcongr
    _ ≤ ‖T‖ * Metric.infDist y K + ε := by rw [mul_add]; linarith

lemma dst_mul_le (x : n → ℂ) (f : ι → n → ℂ) (s : Set ι) (M A : Matrix n n ℂ) :
    dst x f s (M * A) ≤ opn M * dst x f s A := by
  unfold dst
  set T := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) M
  have key : ∀ v : n → ℂ, (WithLp.toLp 2 ((M * A) *ᵥ v) : EuclideanSpace ℂ n) =
      T (WithLp.toLp 2 (A *ᵥ v)) := fun v => by
    rw [← Matrix.mulVec_mulVec]; rfl
  simp only [key]
  set S : Set (EuclideanSpace ℂ n) := (fun b => (WithLp.toLp 2 (A *ᵥ f b) : EuclideanSpace ℂ n)) '' s
  have himg : (fun b => T (WithLp.toLp 2 (A *ᵥ f b))) '' s = T '' S := (Set.image_image _ _ _).symm
  rw [himg]

  have hsub : T '' (Submodule.span ℂ S : Set _) ⊆ (Submodule.span ℂ (T '' S) : Set _) := by
    rintro _ ⟨p, hp, rfl⟩
    exact Submodule.apply_mem_span_image_of_mem_span (T : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n) hp
  calc Metric.infDist (T (WithLp.toLp 2 (A *ᵥ x))) (Submodule.span ℂ (T '' S) : Set _)
      ≤ Metric.infDist (T (WithLp.toLp 2 (A *ᵥ x))) (T '' (Submodule.span ℂ S : Set _)) :=
        Metric.infDist_le_infDist_of_subset hsub ⟨T 0, 0, Submodule.zero_mem _, rfl⟩
    _ ≤ ‖T‖ * Metric.infDist (WithLp.toLp 2 (A *ᵥ x)) (Submodule.span ℂ S : Set _) :=
        infDist_image_le_opNorm_mul T _ _ ⟨0, Submodule.zero_mem _⟩
    _ = opn M * Metric.infDist (WithLp.toLp 2 (A *ᵥ x)) (Submodule.span ℂ S : Set _) := rfl

lemma dst_inv_continuousOn [Nonempty n] (x : n → ℂ) (f : ι → n → ℂ) (s : Set ι) :
    ContinuousOn (fun g : Matrix n n ℂ => dst x f s g⁻¹) {g | IsUnit g.det} := by
  set U : Set (Matrix n n ℂ) := {g | IsUnit g.det}

  have hinv : ContinuousOn (fun g : Matrix n n ℂ => g⁻¹) U := by
    have h : (fun g : Matrix n n ℂ => g⁻¹) = fun g => (g.det)⁻¹ • g.adjugate := by
      funext g; rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [h]
    exact (continuous_id.matrix_det.continuousOn.inv₀ fun (g : Matrix n n ℂ) (hg : g ∈ U) => (show IsUnit g.det from hg).ne_zero).smul
      continuous_id.matrix_adjugate.continuousOn
  intro g0 hg0
  have hg0' : IsUnit g0.det := hg0
  set a0 := dst x f s g0⁻¹

  have hu : Filter.Tendsto (fun g => opn (g⁻¹ * g0)) (nhdsWithin g0 U) (nhds 1) := by
    have hc : ContinuousWithinAt (fun g => opn (g⁻¹ * g0)) U g0 :=
      opn_cont.continuousAt.comp_continuousWithinAt ((hinv g0 hg0).mul continuousWithinAt_const)
    have h1 : opn (g0⁻¹ * g0) = 1 := by rw [Matrix.nonsing_inv_mul _ hg0', opn_one]
    have := hc.tendsto
    rwa [h1] at this
  have hv : Filter.Tendsto (fun g => opn (g0⁻¹ * g)) (nhdsWithin g0 U) (nhds 1) := by
    have hc : Continuous fun g => opn (g0⁻¹ * g) := opn_cont.comp (continuous_const.mul continuous_id)
    have h1 : opn (g0⁻¹ * g0) = 1 := by rw [Matrix.nonsing_inv_mul _ hg0', opn_one]
    have := hc.continuousWithinAt (s := U) (x := g0) |>.tendsto
    rwa [h1] at this
  have hup : ∀ g ∈ U, dst x f s g⁻¹ ≤ opn (g⁻¹ * g0) * a0 := by
    intro g _
    have h := dst_mul_le x f s (g⁻¹ * g0) g0⁻¹
    rwa [mul_assoc, Matrix.mul_nonsing_inv _ hg0', mul_one] at h
  have hlow : ∀ g ∈ U, a0 ≤ opn (g0⁻¹ * g) * dst x f s g⁻¹ := by
    intro g hg
    have h := dst_mul_le x f s (g0⁻¹ * g) g⁻¹
    rwa [mul_assoc, Matrix.mul_nonsing_inv _ (show IsUnit g.det from hg), mul_one] at h
  have hpos : ∀ᶠ g in nhdsWithin g0 U, 0 < opn (g0⁻¹ * g) := hv.eventually (lt_mem_nhds one_pos)
  have hL : Filter.Tendsto (fun g => a0 / opn (g0⁻¹ * g)) (nhdsWithin g0 U) (nhds a0) := by
    have := (tendsto_const_nhds (x := a0)).div hv one_ne_zero
    rwa [div_one] at this
  have hR : Filter.Tendsto (fun g => opn (g⁻¹ * g0) * a0) (nhdsWithin g0 U) (nhds a0) := by
    have := hu.mul_const a0
    rwa [one_mul] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hR ?_ (eventually_nhdsWithin_of_forall hup)
  filter_upwards [hpos, eventually_nhdsWithin_of_forall hlow] with g hg1 hg2
  rw [div_le_iff₀ hg1, mul_comm]
  exact hg2

theorem lenA_continuousOn : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z →
    0 < Formalism.QuantumDeterminants.Tz k r z → ∀ a, ContinuousOn (fun g => lenA k r z g a) (GG k r) := by
  intro k r z _ _ a

  have hsub : GG k r ⊆ {g : Mx k r | IsUnit g.det} := by
    intro g hg
    have h1 : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
    have hdet : (Formalism.QuantumDeterminants.Hpk k r).det * (Formalism.QuantumDeterminants.Hpk k r).det = 1 := by
      rw [← Matrix.det_mul, Formalism.QuantumDeterminants.GBasic.Hpk_sq, Matrix.det_one]
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_mul] at h2
    show IsUnit g.det
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, mul_zero] at h2
    rw [← h2, mul_zero] at hdet
    exact zero_ne_one hdet
  exact (dst_inv_continuousOn (Formalism.QuantumDeterminants.fvec k r z a) (Formalism.QuantumDeterminants.fvec k r z) {b | b < a}).mono hsub

end GlobalTheory.LengthCont
end
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory.MonomialDense
open GlobalTheory.MultiMahler

variable {p : ℕ} [Fact p.Prime]

noncomputable def incl (p : ℕ) [Fact p.Prime] : ℤ_[p] →+* ℂ_[p] :=
  (algebraMap ℚ_[p] ℂ_[p]).comp PadicInt.Coe.ringHom

theorem continuous_incl : Continuous (incl p) :=
  (continuous_algebraMap ℚ_[p] ℂ_[p]).comp continuous_subtype_val

theorem factorial_mul_binomC (k : ℕ) (x : ℤ_[p]) :
    (k.factorial : ℂ_[p]) * binomC k x
      = incl p (Polynomial.aeval x (descPochhammer ℤ k)) := by
  have h1 : binomC k x = incl p (Ring.choose x k) := rfl
  have h2 := Ring.descPochhammer_eq_factorial_smul_choose x k
  rw [← Polynomial.aeval_eq_smeval] at h2
  rw [h1, h2, nsmul_eq_mul, map_mul, map_natCast]

theorem exists_mahler_expansion {E : Type*} [NormedAddCommGroup E] [NormedSpace ℚ_[p] E]
    [IsUltrametricDist E] [CompleteSpace E] (f : C(ℤ_[p], E)) :
    ∃ t : ℕ → C(ℤ_[p], E), HasSum t f ∧
      ∀ n, ∃ a : E, ∀ x, t n x = ((mahler n x : ℤ_[p]) : ℚ_[p]) • a := by
  letI : Module ℤ_[p] E := Module.compHom E (algebraMap ℤ_[p] ℚ_[p])
  haveI : IsBoundedSMul ℤ_[p] E := IsBoundedSMul.of_norm_smul_le fun r x =>
    norm_smul_le (r : ℚ_[p]) x
  exact ⟨_, PadicInt.hasSum_mahler f, fun n => ⟨_, fun _ => rfl⟩⟩

variable {Z : Type} [TopologicalSpace Z] [CompactSpace Z]

omit [CompactSpace Z] in
theorem binomC_comp_mem (S : Subalgebra ℂ_[p] C(Z, ℂ_[p])) (φ : C(Z, ℤ_[p]))
    (X : C(Z, ℂ_[p])) (hX : ∀ z, X z = incl p (φ z)) (hS : X ∈ S) (k : ℕ) :
    (binomC k).comp φ ∈ S := by
  have hmem : ∀ P : Polynomial ℤ, ∃ G ∈ S, ∀ z, G z = incl p (Polynomial.aeval (φ z) P) := by
    intro P
    induction P using Polynomial.induction_on' with
    | add P Q hP hQ =>
      obtain ⟨G, hG, hG'⟩ := hP
      obtain ⟨G₂, hG₂, hG₂'⟩ := hQ
      exact ⟨G + G₂, S.add_mem hG hG₂, fun z => by simp [hG', hG₂']⟩
    | monomial n a =>
      refine ⟨(a : ℂ_[p]) • X ^ n, S.smul_mem (S.pow_mem hS n) _, fun z => ?_⟩
      simp [hX, Polynomial.aeval_monomial]
  obtain ⟨G, hG, hG'⟩ := hmem (descPochhammer ℤ k)
  have hk : (k.factorial : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have : (binomC k).comp φ = (k.factorial : ℂ_[p])⁻¹ • G := by
    ext z
    change binomC k (φ z) = (k.factorial : ℂ_[p])⁻¹ * G z
    rw [hG', ← factorial_mul_binomC, inv_mul_cancel_left₀ hk]
  rw [this]
  exact S.smul_mem hG _

noncomputable def evalAlong {Y : Type} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (φ : C(Z, ℤ_[p])) (ψ : C(Z, Y)) :
    C(ℤ_[p], C(Y, ℂ_[p])) →L[ℂ_[p]] C(Z, ℂ_[p]) :=
  LinearMap.mkContinuous
    { toFun := fun G => ⟨fun z => G (φ z) (ψ z), by fun_prop⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1 (fun G => by
      rw [one_mul, ContinuousMap.norm_le _ (norm_nonneg _)]
      intro z
      exact ((G (φ z)).norm_coe_le_norm _).trans (G.norm_coe_le_norm _))

theorem comp_mem (S : Subalgebra ℂ_[p] C(Z, ℂ_[p])) (hS : IsClosed (S : Set C(Z, ℂ_[p])))
    (g : ℕ) : ∀ (φ : C(Z, Fin g → ℤ_[p])),
      (∀ i, ∃ X ∈ S, ∀ z, X z = incl p (φ z i)) →
      ∀ F : C(Fin g → ℤ_[p], ℂ_[p]), F.comp φ ∈ S := by
  induction g with
  | zero =>
    intro φ _ F
    have : F.comp φ = algebraMap ℂ_[p] C(Z, ℂ_[p]) (F 0) := by
      ext z
      simp [Subsingleton.elim (φ z) 0]
    rw [this]
    exact S.algebraMap_mem _
  | succ g ih =>
    intro φ hφ F
    obtain ⟨t, ht, ht'⟩ := exists_mahler_expansion (curryFirst F)
    let φ0 : C(Z, ℤ_[p]) := ⟨fun z => φ z 0, by fun_prop⟩
    let ψ : C(Z, Fin g → ℤ_[p]) := ⟨fun z i => φ z i.succ, by fun_prop⟩
    have h := (evalAlong φ0 ψ).hasSum ht
    have e : evalAlong φ0 ψ (curryFirst F) = F.comp φ := by
      ext z
      exact congrArg F (Fin.cons_self_tail (φ z))
    rw [e] at h
    refine hS.mem_of_tendsto h (Filter.Eventually.of_forall fun s => S.sum_mem fun n _ => ?_)
    obtain ⟨a, ha⟩ := ht' n
    have e2 : evalAlong φ0 ψ (t n) = (binomC n).comp φ0 * a.comp ψ := by
      ext z
      change t n (φ0 z) (ψ z) = _
      rw [ha]
      change ((mahler n (φ0 z) : ℤ_[p]) : ℚ_[p]) • a (ψ z) = _
      rw [Algebra.smul_def]
      rfl
    rw [e2]
    obtain ⟨X, hX, hX'⟩ := hφ 0
    exact S.mul_mem (binomC_comp_mem S φ0 X hX' hX n) (ih ψ (fun i => hφ i.succ) a)

theorem eq_zero_of_monomials : ∀ (p r : ℕ) [Fact p.Prime] (μ : C(Fin r → ℤ_[p], ℂ_[p]) →L[ℂ_[p]] ℂ_[p]), (∀ (m : ℕ) (k : Fin m → Fin r) (g : C(Fin r → ℤ_[p], ℂ_[p])), (∀ a, g a = ∏ j, zc (a (k j))) → μ g = 0) → μ = 0 := by
  intro p r _ μ hμ
  let X : Fin r → C(Fin r → ℤ_[p], ℂ_[p]) := fun i =>
    ⟨fun a => incl p (a i), continuous_incl.comp (continuous_apply i)⟩
  let A : Subalgebra ℂ_[p] C(Fin r → ℤ_[p], ℂ_[p]) := Algebra.adjoin ℂ_[p] (Set.range X)
  have hA : ∀ f ∈ A, μ f = 0 := by
    intro f hf
    have hf' : f ∈ Submodule.span ℂ_[p] (Submonoid.closure (Set.range X) : Set _) := by
      rw [← Algebra.adjoin_eq_span]; exact hf
    refine (Submodule.span_le (p := LinearMap.ker μ.toLinearMap)).mpr ?_ hf'
    intro g hg
    have : ∃ (m : ℕ) (k : Fin m → Fin r), ∀ a, g a = ∏ j, zc (a (k j)) := by
      induction hg using Submonoid.closure_induction_left with
      | one => exact ⟨0, Fin.elim0, fun a => by simp⟩
      | mul_left x hx y _ ih =>
        obtain ⟨i, rfl⟩ := hx
        obtain ⟨m, k, hk⟩ := ih
        refine ⟨m + 1, Fin.cons i k, fun a => ?_⟩
        rw [Fin.prod_univ_succ, ContinuousMap.mul_apply, hk]
        rfl
    obtain ⟨m, k, hk⟩ := this
    exact hμ m k g hk
  ext F
  have hF := comp_mem A.topologicalClosure A.isClosed_topologicalClosure r (ContinuousMap.id _)
    (fun i => ⟨X i, A.le_topologicalClosure (Algebra.subset_adjoin ⟨i, rfl⟩), fun _ => rfl⟩) F
  have hcl : closure (A : Set C(Fin r → ℤ_[p], ℂ_[p])) ⊆ {f | μ f = 0} :=
    closure_minimal hA (isClosed_eq μ.continuous continuous_const)
  exact hcl hF

end GlobalTheory.MonomialDense
end

section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.valuation_blockPolynomial_ge_prod : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (Ty : Type) [Fintype Ty] [DecidableEq Ty] (r : Ty → ℕ) (n : ℕ) (β : (Σ τ : Ty, Fin (r τ)) → Fin n), Function.Injective β → ∀ (a : Ty → ℕ → ℕ), Crude.Dom r a → ∀ (yv : Letter Ty r n → O) (x : Ty → NNReal), (∀ τ, x τ ≤ 1) → (∀ τ (i : Fin (r τ)), x τ ≤ v (algebraMap O C (Matrix.of fun a b : Fin (i.val + 1) => yv ⟨τ, Fin.castLE i.isLt a, β ⟨τ, Fin.castLE i.isLt b⟩⟩).det)) → (∏ τ, x τ ^ (a τ 0) ≤ v (algebraMap O C (MvPolynomial.eval yv (Crude.crP r n O β a)))) ∧ ∀ mo ∈ (Crude.crP r n O β a).support, ∀ ℓ, mo ℓ ≠ 0 → ∃ i, β ⟨ℓ.1, i⟩ = ℓ.2.2 := by
  first | exact @GlobalTheory.CharDepth.valuation_blockPoly_ge | exact GlobalTheory.CharDepth.valuation_blockPoly_ge | (intros; apply GlobalTheory.CharDepth.valuation_blockPoly_ge <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.groupExpansion_bijective_of_completeDVR : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → (∀ σ' : U.SecGF F k, ∃! s : Fam D.toPre F k, U.ExpandsG F k σ' s) ∧ ∀ s : Fam D.toPre F k, ∃! σ' : U.SecGF F k, U.ExpandsG F k σ' s := by
  first | exact @GlobalTheory.expandsG_bijective_of_dvr | exact GlobalTheory.expandsG_bijective_of_dvr | (intros; apply GlobalTheory.expandsG_bijective_of_dvr <;> assumption)
end
