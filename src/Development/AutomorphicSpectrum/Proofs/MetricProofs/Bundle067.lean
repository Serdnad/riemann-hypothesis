module

import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusHolomorphicPotentialChange
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle043
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.EmbEquivSymmApply
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle062
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle021
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle059
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle012
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.PshLogGrowthBounded
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.ReduceModChar
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusMatrix
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements

@[expose] public section

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ.MemBall

theorem exists_sqLen {m : Type} [Fintype m] (x : m → ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧ star x ⬝ᵥ x = (r : ℂ) ∧ (x ≠ 0 → 0 < r) := by
  have h0 : 0 ≤ star x ⬝ᵥ x := dotProduct_star_self_nonneg x
  have hz := Complex.nonneg_iff.1 h0
  have heq : star x ⬝ᵥ x = (((star x ⬝ᵥ x).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hz.2.symm
  refine ⟨(star x ⬝ᵥ x).re, hz.1, heq, fun hx => ?_⟩
  have hp : 0 < star x ⬝ᵥ x := dotProduct_star_self_pos_iff.2 hx
  exact (Complex.pos_iff.1 hp).1

theorem qf_one_sub {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n ℂ) (w : n → ℂ) :
    star w ⬝ᵥ ((1 - Aᴴ * A) *ᵥ w) = star w ⬝ᵥ w - star (A *ᵥ w) ⬝ᵥ (A *ᵥ w) := by
  rw [sub_mulVec, one_mulVec, dotProduct_sub, ← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose, star_star]

theorem posDef_adjoint {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (A : Matrix m n ℂ)
    (h : (1 - Aᴴ * A).PosDef) : (1 - A * Aᴴ).PosDef := by
  apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Moeb.posDef_one_sub_swap <;> assumption

theorem posDef_adjoint_iff {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (A : Matrix m n ℂ) :
    (1 - Aᴴ * A).PosDef ↔ (1 - A * Aᴴ).PosDef :=
  ⟨posDef_adjoint A, fun h => by simpa using posDef_adjoint Aᴴ (by simpa using h)⟩

theorem posDef_blockDiagonal_iff {m o : Type} [Fintype m] [Fintype o] [DecidableEq m] [DecidableEq o]
    (M : o → Matrix m m ℂ) : (blockDiagonal M).PosDef ↔ ∀ k, (M k).PosDef := by
  constructor
  · intro h k
    have hinj : Function.Injective (fun i : m => (i, k)) := fun a b hab => (Prod.ext_iff.1 hab).1
    have := h.submatrix hinj
    convert this using 1
    ext a b
    simp [blockDiagonal_apply]
  · intro h
    refine posDef_iff_dotProduct_mulVec.2 ⟨?_, fun x hx => ?_⟩
    · rw [IsHermitian, blockDiagonal_conjTranspose]
      congr 1
      funext k
      exact (h k).1
    have hmv : ∀ i k, (blockDiagonal M *ᵥ x) (i, k) = (M k *ᵥ fun i => x (i, k)) i := by
      intro i k
      simp only [mulVec, dotProduct, Fintype.sum_prod_type_right, blockDiagonal_apply]
      rw [Finset.sum_eq_single k]
      · simp
      · intro c _ hc
        simp [Ne.symm hc]
      · simp
    have hsum : star x ⬝ᵥ (blockDiagonal M *ᵥ x) =
        ∑ k, star (fun i => x (i, k)) ⬝ᵥ (M k *ᵥ fun i => x (i, k)) := by
      simp only [dotProduct, Fintype.sum_prod_type_right, hmv]
      rfl
    rw [hsum]
    obtain ⟨⟨i, k⟩, hp⟩ := Function.ne_iff.1 hx
    refine Finset.sum_pos' (fun k _ => (h k).posSemidef.dotProduct_mulVec_nonneg _) ⟨k, Finset.mem_univ _, ?_⟩
    refine (posDef_iff_dotProduct_mulVec.1 (h k)).2 (Function.ne_iff.2 ⟨i, ?_⟩)
    simpa using hp

theorem posDef_fromBlocks_diag_iff {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (D : Matrix n n ℂ) : (fromBlocks A 0 0 D).PosDef ↔ A.PosDef ∧ D.PosDef := by
  constructor
  · intro h
    constructor
    · have h1 : (fromBlocks A 0 0 D).submatrix (Sum.inl : m → m ⊕ n) Sum.inl = A := by
        ext a c; simp
      exact h1 ▸ h.submatrix Sum.inl_injective
    · have h1 : (fromBlocks A 0 0 D).submatrix (Sum.inr : n → m ⊕ n) Sum.inr = D := by
        ext a c; simp
      exact h1 ▸ h.submatrix Sum.inr_injective
  · rintro ⟨hA, hD⟩
    refine posDef_iff_dotProduct_mulVec.2 ⟨?_, fun x hx => ?_⟩
    · rw [IsHermitian, fromBlocks_conjTranspose, hA.1, hD.1]
      simp
    have hsum : star x ⬝ᵥ (fromBlocks A 0 0 D *ᵥ x) =
        star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) + star (x ∘ Sum.inr) ⬝ᵥ (D *ᵥ (x ∘ Sum.inr)) := by
      rw [fromBlocks_mulVec]
      simp [dotProduct, Fintype.sum_sum_type]
    rw [hsum]
    have h1 := hA.posSemidef.dotProduct_mulVec_nonneg (x ∘ Sum.inl)
    have h2 := hD.posSemidef.dotProduct_mulVec_nonneg (x ∘ Sum.inr)
    obtain ⟨p, hp⟩ := Function.ne_iff.1 hx
    rcases p with i | i
    · refine add_pos_of_pos_of_nonneg ((posDef_iff_dotProduct_mulVec.1 hA).2 (Function.ne_iff.2 ⟨i, ?_⟩)) h2
      simpa using hp
    · refine add_pos_of_nonneg_of_pos h1 ((posDef_iff_dotProduct_mulVec.1 hD).2 (Function.ne_iff.2 ⟨i, ?_⟩))
      simpa using hp

theorem posDef_transpose_block {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (Z : Matrix m n ℂ) :
    (1 - Zᵀᴴ * Zᵀ).PosDef ↔ (1 - Zᴴ * Z).PosDef := by
  rw [posDef_adjoint_iff Z, ← PosDef.transpose_iff (M := 1 - Z * Zᴴ)]
  have : (1 - Z * Zᴴ)ᵀ = 1 - Zᵀᴴ * Zᵀ := by
    rw [transpose_sub, transpose_one, transpose_mul]
    congr 2
  rw [this]

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ.MemBall

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ


open MemBall in
theorem mem_ballDom_iff_posDef_bigZe {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n g : ℕ} (e : Ix Ψ j j' ≃ Fin g)
    (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) :
    t ∈ ballDom q ↔ (1 - (bigZe e q t)ᴴ * bigZe e q t).PosDef := by
  have hblk : (1 : Matrix (Ix Ψ j j') (Ix Ψ j j') ℂ) - (bigZ q t)ᴴ * bigZ q t =
      blockDiagonal fun τ => fromBlocks (1 - (ballMat q t τ)ᴴ * ballMat q t τ) 0 0
        (1 - (ballMat q t τ)ᵀᴴ * (ballMat q t τ)ᵀ) := by
    rw [bigZ, blockDiagonal_conjTranspose, ← blockDiagonal_mul, ← blockDiagonal_one, ← blockDiagonal_sub]
    congr 1
    funext τ
    simp only [Pi.sub_apply, Pi.one_apply]
    rw [fromBlocks_conjTranspose, fromBlocks_multiply]
    simp only [conjTranspose_zero, mul_zero, add_zero, zero_add, ← fromBlocks_one]
    ext (a | a) (c | c) <;> simp [Matrix.one_apply]
  have hsub : (1 : Matrix (Fin g) (Fin g) ℂ) - (bigZe e q t)ᴴ * bigZe e q t =
      ((1 : Matrix (Ix Ψ j j') (Ix Ψ j j') ℂ) - (bigZ q t)ᴴ * bigZ q t).submatrix e.symm e.symm := by
    rw [bigZe, conjTranspose_submatrix, submatrix_mul_equiv]
    ext a c
    simp [Matrix.one_apply]
  have hequiv : ((1 - (bigZ q t)ᴴ * bigZ q t).submatrix e.symm e.symm).PosDef ↔
      (1 - (bigZ q t)ᴴ * bigZ q t).PosDef :=
    ⟨fun h => by simpa using h.submatrix e.injective, fun h => h.submatrix e.symm.injective⟩
  rw [hsub, hequiv, hblk, MemBall.posDef_blockDiagonal_iff]
  simp only [MemBall.posDef_fromBlocks_diag_iff, MemBall.posDef_transpose_block, and_self]
  rfl

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ
end
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FirstMin

theorem sInf_range_le_mul {S : Type} [Nonempty S] (f h : S → ℝ) (hf : ∀ s, 0 ≤ f s) (c : ℝ) (hc : 0 < c)
    (hle : ∀ s, f s ≤ c * h s) : sInf (Set.range f) ≤ c * sInf (Set.range h) := by
  have hb : BddBelow (Set.range f) := ⟨0, by rintro _ ⟨s, rfl⟩; exact hf s⟩
  have key : sInf (Set.range f) / c ≤ sInf (Set.range h) := by
    apply le_csInf (Set.range_nonempty h)
    rintro _ ⟨s, rfl⟩
    rw [div_le_iff₀' hc]
    exact (csInf_le hb ⟨s, rfl⟩).trans (hle s)
  rwa [div_le_iff₀' hc] at key

theorem eventually_form_comparison {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (Q : X → (ι → ℝ) → ℝ) (hQ : Continuous fun p : X × (ι → ℝ) => Q p.1 p.2)
    (hhom : ∀ x (r : ℝ) a, Q x (r • a) = r ^ 2 * Q x a)
    (hpos : ∀ x a, a ≠ 0 → 0 < Q x a) (x₀ : X) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∀ᶠ x in 𝓝 x₀, ∀ a, a ≠ 0 → (1 - δ) ^ 2 * Q x₀ a ≤ Q x a ∧ Q x a ≤ (1 + δ) ^ 2 * Q x₀ a := by
  have hK : IsCompact (Metric.sphere (0 : ι → ℝ) 1) := isCompact_sphere _ _
  have hQ0 : Continuous fun p : X × (ι → ℝ) => Q x₀ p.2 :=
    hQ.comp (continuous_const.prodMk continuous_snd)
  have hev : ∀ᶠ x in 𝓝 x₀, ∀ a ∈ Metric.sphere (0 : ι → ℝ) 1,
      (1 - δ) ^ 2 * Q x₀ a < Q x a ∧ Q x a < (1 + δ) ^ 2 * Q x₀ a := by
    apply hK.eventually_forall_of_forall_eventually
    intro a ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at ha
    have hp := hpos x₀ a ha0
    have hl : (1 - δ) ^ 2 < 1 := by nlinarith
    have hu : 1 < (1 + δ) ^ 2 := by nlinarith
    have h1 : (1 - δ) ^ 2 * Q x₀ a < Q x₀ a := by nlinarith
    have h2 : Q x₀ a < (1 + δ) ^ 2 * Q x₀ a := by nlinarith
    exact ((isOpen_lt (continuous_const.mul hQ0) hQ).inter
      (isOpen_lt hQ (continuous_const.mul hQ0))).mem_nhds ⟨h1, h2⟩
  filter_upwards [hev] with x hx a ha
  have hn : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hu : ‖a‖⁻¹ • a ∈ Metric.sphere (0 : ι → ℝ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have hau : a = ‖a‖ • (‖a‖⁻¹ • a) := by
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  obtain ⟨h1, h2⟩ := hx _ hu
  have hn2 : 0 < ‖a‖ ^ 2 := by positivity
  rw [hau, hhom x, hhom x₀]
  generalize ‖a‖⁻¹ • a = u at h1 h2
  constructor
  · nlinarith [mul_lt_mul_of_pos_left h1 hn2]
  · nlinarith [mul_lt_mul_of_pos_left h2 hn2]

theorem continuous_sInf_sqrt_form {X ι S : Type} [TopologicalSpace X] [Fintype ι]
    (Q : X → (ι → ℝ) → ℝ) (hQ : Continuous fun p : X × (ι → ℝ) => Q p.1 p.2)
    (hhom : ∀ x (r : ℝ) a, Q x (r • a) = r ^ 2 * Q x a)
    (hpos : ∀ x a, a ≠ 0 → 0 < Q x a) (c : S → ι → ℝ) (hc : ∀ s, c s ≠ 0) :
    Continuous fun x => sInf (Set.range fun s => Real.sqrt (Q x (c s))) := by
  rcases isEmpty_or_nonempty S with hS | hS
  · simp only [Set.range_eq_empty]
    exact continuous_const
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [Metric.continuousAt_iff']
  intro ε hε
  set m := sInf (Set.range fun s => Real.sqrt (Q x₀ (c s))) with hm
  have hm0 : 0 ≤ m := Real.sInf_nonneg (by rintro _ ⟨s, rfl⟩; exact Real.sqrt_nonneg _)
  obtain ⟨δ, hδ, hδ1, hδm⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ δ * m < ε := by
    refine ⟨min (1 / 2) (ε / (2 * (m + 1))), by positivity, ?_, ?_⟩
    · exact (min_le_left _ _).trans_lt (by norm_num)
    · have h1 : min (1 / 2) (ε / (2 * (m + 1))) ≤ ε / (2 * (m + 1)) := min_le_right _ _
      have h2 : ε / (2 * (m + 1)) * m < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
      exact (mul_le_mul_of_nonneg_right h1 hm0).trans_lt h2
  filter_upwards [eventually_form_comparison Q hQ hhom hpos x₀ δ hδ hδ1] with x hx
  have hlow : ∀ s, Real.sqrt (Q x₀ (c s)) ≤ (1 - δ)⁻¹ * Real.sqrt (Q x (c s)) := by
    intro s
    have h1 : 0 < 1 - δ := by linarith
    rw [inv_mul_eq_div, le_div_iff₀' h1]
    have := Real.sqrt_le_sqrt (hx _ (hc s)).1
    rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq h1.le] at this
  have hup : ∀ s, Real.sqrt (Q x (c s)) ≤ (1 + δ) * Real.sqrt (Q x₀ (c s)) := by
    intro s
    have h1 : 0 < 1 + δ := by linarith
    have := Real.sqrt_le_sqrt (hx _ (hc s)).2
    rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq h1.le] at this
  have hA := sInf_range_le_mul _ _ (fun s => Real.sqrt_nonneg _) _
    (inv_pos.mpr (by linarith : 0 < 1 - δ)) hlow
  have hB := sInf_range_le_mul _ _ (fun s => Real.sqrt_nonneg _) _ (by linarith : 0 < 1 + δ) hup
  rw [← hm] at hA hB
  set l := sInf (Set.range fun s => Real.sqrt (Q x (c s))) with hl
  have hA' : (1 - δ) * m ≤ l := by
    have h1 : 0 < 1 - δ := by linarith
    rw [inv_mul_eq_div, le_div_iff₀' h1] at hA
    exact hA
  rw [Real.dist_eq, abs_lt]
  constructor <;> nlinarith

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

theorem linearIndependent_periods (R : RiemLat E g Λ) {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ Λ) :
    LinearIndependent ℝ fun i => R.P (b i) := by
  apply LevelTowerAlt.basis_indep <;> assumption

def comb (R : RiemLat E g Λ) {ι : Type} [Fintype ι] (b : ι → Λ) (a : ι → ℝ) : Fin g → ℂ :=
  ∑ i, ((a i : ℝ) : ℂ) • R.P (b i)

theorem comb_repr (R : RiemLat E g Λ) {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ Λ) (v : Λ) :
    comb R b (fun i => ((b.repr v i : ℤ) : ℝ)) = R.P v := by

  conv_rhs => rw [← b.sum_repr v, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ]
  simp

theorem comb_ne_zero (R : RiemLat E g Λ) {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ Λ) (a : ι → ℝ)
    (ha : a ≠ 0) : comb R b a ≠ 0 := by
  intro h0
  apply ha
  have hli := linearIndependent_periods R b
  have h1 : ∑ i, a i • R.P (b i) = 0 := by
    rw [← h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    ext j
    simp
  funext i
  exact Fintype.linearIndependent_iff.mp hli a h1 i

end GlobalTheory.CompanionTheory.Ar.Cusp.FirstMin


open GlobalTheory.CompanionTheory.Ar.Cusp.FirstMin in
theorem GlobalTheory.CompanionTheory.Ar.Cusp.continuous_first_minimum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (X : Type) [TopologicalSpace X] (R : X → RiemLat E g Λ), (∀ v, Continuous fun x => (R x).P v) → (Continuous fun x => (R x).Hm) → Continuous fun x => (R x).lam1 := by
  intro E _ _ _ g Λ _ _ X _ R hP hH
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · exact continuous_of_const fun x => hX.elim x
  haveI := (R x₀).free
  haveI := (R x₀).fin
  let b := Module.Free.chooseBasis ℤ Λ
  let Q : X → (Module.Free.ChooseBasisIndex ℤ Λ → ℝ) → ℝ := fun x a =>
    ((R x).ip (FirstMin.comb (R x) b a) (FirstMin.comb (R x) b a)).re
  have hL : Continuous fun p : X × (Module.Free.ChooseBasisIndex ℤ Λ → ℝ) => FirstMin.comb (R p.1) b p.2 := by
    unfold FirstMin.comb
    refine continuous_finsetSum _ fun i _ => ?_
    exact (Complex.continuous_ofReal.comp ((continuous_apply i).comp continuous_snd)).smul
      ((hP (b i)).comp continuous_fst)
  have hQ : Continuous fun p : X × (Module.Free.ChooseBasisIndex ℤ Λ → ℝ) => Q p.1 p.2 := by
    refine Complex.continuous_re.comp ?_
    exact hL.dotProduct ((hH.comp continuous_fst).matrix_mulVec hL.star)
  have hhom : ∀ x (r : ℝ) a, Q x (r • a) = r ^ 2 * Q x a := by
    intro x r a
    have hc : FirstMin.comb (R x) b (r • a) = (r : ℂ) • FirstMin.comb (R x) b a := by
      unfold FirstMin.comb
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul]
      simp
    simp only [Q, RiemLat.ip, hc, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
    simp [pow_two, mul_assoc]
  have hpos : ∀ x a, a ≠ 0 → 0 < Q x a := fun x a ha => (R x).pos _ (FirstMin.comb_ne_zero (R x) b a ha)
  have hmain := FirstMin.continuous_sInf_sqrt_form Q hQ hhom hpos
    (fun (s : {v : Λ // v ≠ 0}) i => ((b.repr s.1 i : ℤ) : ℝ)) (by
      intro s h0
      apply s.2
      apply b.repr.injective
      ext i
      have := congrFun h0 i
      simpa using this)
  convert hmain using 2 with x
  unfold RiemLat.lam1
  congr 1
  ext y
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨⟨v, hv⟩, ?_⟩
    simp only [Q, FirstMin.comb_repr, RiemLat.normSq]
  · rintro ⟨⟨v, hv⟩, rfl⟩
    refine ⟨v, hv, ?_⟩
    simp only [Q, FirstMin.comb_repr, RiemLat.normSq]
end
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

theorem _root_.GlobalTheory.T.common_resolution_potential_comparison : PullbackStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (D : ℕ) (R : AnLogRes P J D) (Amp : HermLine ι) (β : MRing ι) (b : K → ℕ) (σ : Type) [Fintype σ] (S₁ S₂ : AnSys D σ) (π₁ : R.X → S₁.X) (π₂ : R.X → S₂.X) (h₁ : HoloMap R.A S₁.A π₁) (h₂ : HoloMap R.A S₂.A π₂), IsPotential R.A (potOf R Amp) → IsPosPot R.A (potOf R Amp) → IsMultiHomog β b → β ∉ P → (∀ z ∈ mcPts P, evC z β = 0 → z ∈ mcPts J) → (∀ x, π₁ x ∈ bdry S₁.s → evC (R.lift x x) β = 0) → (∀ x, π₂ x ∈ bdry S₂.s → evC (R.lift x x) β = 0) → ∃ (L : LocPot R.X) (s : R.X → R.X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set R.X) (C₅ C t₀ : ℝ), IsPotential R.A L ∧ IsSection R.A L s ∧ IsSNC R.A L s m W ∧ (∀ y, logNormSec L s y ≤ 0) ∧ (∀ x, x ∈ bdry s ↔ evC (R.lift x x) β = 0) ∧ t₀ ≤ S₁.t₀ ∧ t₀ ≤ S₂.t₀ ∧ (∀ a, IsSingWeight R.A L s ((S₁.th a).pullback π₁ h₁.1) (S₁.ph a ∘ π₁) C₅ ∧ IsRegFamily R.A (potOf R Amp) L s ((S₁.th a).pullback π₁ h₁.1) (S₁.ph a ∘ π₁) (fun t => S₁.phT a t ∘ π₁) C t₀ ∧ IsRegFamilyC2 R.A s (S₁.ph a ∘ π₁) (fun t => S₁.phT a t ∘ π₁)) ∧ ∀ a, IsSingWeight R.A L s ((S₂.th a).pullback π₂ h₂.1) (S₂.ph a ∘ π₂) C₅ ∧ IsRegFamily R.A (potOf R Amp) L s ((S₂.th a).pullback π₂ h₂.1) (S₂.ph a ∘ π₂) (fun t => S₂.phT a t ∘ π₂) C t₀ ∧ IsRegFamilyC2 R.A s (S₂.ph a ∘ π₂) (fun t => S₂.phT a t ∘ π₂) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.r_combine | exact GlobalTheory.CompanionTheory.Ar.Cmp.r_combine | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.r_combine <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

theorem _root_.GlobalTheory.T.algebraic_realisation_holomorphic_map : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (κ₁ : K₁ → K) (v₁ : (Σ k, ι₁ k) → Σ k, ι k) (P J : Ideal (MRing ι)) (D : ℕ) (σ : Type) (S : AnSys D σ) (Re : Realis S (imageZ v₁ P)) (R : AnLogRes P J D), IsBlockMap κ₁ v₁ → IsArithVar P (D + 1) → AlgOver Re → ∃ (π : R.X → S.X) (hπ : HoloMap R.A S.A π), (∀ (x : R.X) (x₁ : Re.R.X), SameOrbit (Re.R.lift x₁ x₁) (fun p => R.lift x x (v₁ p)) → π x = Re.π x₁) ∧ (∀ a (ref' : HermLine ι), IsPullHerm κ₁ v₁ (Re.ref a) ref' → SamePot R.A Set.univ (potOf R ref') ((S.th a).pullback π hπ.1)) ∧ (∀ a t, 0 < t → t ≤ S.t₀ → ∀ x, Real.log ((Re.line a t).h fun p => R.lift x x (v₁ p)) = Real.log ((Re.ref a).h fun p => R.lift x x (v₁ p)) + S.phT a t (π x)) ∧ ∃ (β : MRing ι) (b : K → ℕ), IsMultiHomog β b ∧ β ∉ P ∧ ∀ x, π x ∈ bdry S.s → evC (R.lift x x) β = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pull.realis_pullback | exact GlobalTheory.CompanionTheory.Ar.Pull.realis_pullback | (intros; apply GlobalTheory.CompanionTheory.Ar.Pull.realis_pullback <;> assumption)
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund


theorem _root_.GlobalTheory.T.root_origin_multiplicity_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (nu : Wt (CMType H) (D.p + D.q)) (n₀ m : Option (RootIx D) → ℤ), (∀ r, (Fx.n r : ℝ) = (Fx.kA * Fx.q' : ℕ) * nu r.1 r.2) → (∀ r, n₀ (some r) = -Fx.n r) → n₀ none = -(Fx.q' : ℤ) → (∀ r : RootIx D, (m (some r) : ℝ) = (Fx.kA * Fx.q' : ℕ) * fundCo (nu r.1) r.2) → m none = -(Fx.q' : ℤ) → (combLine Or.Re.ref m).a = (combLine (RM.line 1) n₀).a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.Fund.combLine_ref_a_eq_line_a | exact GlobalTheory.CompanionTheory.Ar.Small.Fund.combLine_ref_a_eq_line_a | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.Fund.combLine_ref_a_eq_line_a <;> assumption)
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund


theorem _root_.GlobalTheory.T.root_origin_weight_comparison : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (lam nu : Wt (CMType H) (D.p + D.q)) (n' : Option (RootIx D) → ℤ) (s : ℝ) (x : Or.Re.R.X), (∀ j, (n' j : ℝ) = RM.coef lam 0 j) → scale s ≤ Sys.t₀ → Or.Re.π x ∈ Sys.open' → RM.weight (scale s) (lam - s • nu) s (Or.Re.R.lift x x) - Real.log (∏ r, (Or.sing r).h (Or.Re.R.lift x x) ^ n' (some r)) = s / RM.kA * Real.log (RM.A.h (Or.Re.R.lift x x)) - s * ∑ r : RootIx D, fundCo (nu r.1) r.2 * Real.log ((Or.Re.ref (some r)).h (Or.Re.R.lift x x)) + ∑ r : RootIx D, fundCo ((lam - s • nu) r.1) r.2 * Sys.phT (some r) (scale s) (Or.Re.π x) - ∑ r : RootIx D, fundCo (lam r.1) r.2 * Sys.ph (some r) (Or.Re.π x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.Fund.weight_sub_log_sing | exact GlobalTheory.CompanionTheory.Ar.Small.Fund.weight_sub_log_sing | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.Fund.weight_sub_log_sing <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem _root_.GlobalTheory.CompanionTheory.Relay.psh_log_growth_bounded_near_puncture : ∀ (n a : ℕ) (ρ C : ℝ) (u : (Fin n → ℂ) → ℝ), 0 < ρ → ρ ≤ 1 → ReciprocityTheory.AnForm.A.IsPsh (Flat.punct n a ρ) u → (∀ t ∈ Flat.punct n a ρ, u t ≤ C * (1 + Real.log (Flat.logSize a t))) → ∃ C' : ℝ, ∀ t ∈ Flat.punct n a (ρ / 2), u t ≤ C' := by
  first | exact @LevelTowerAlt.psh_log_growth_bounded | exact LevelTowerAlt.psh_log_growth_bounded
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem AnSys.eventually_mInt_potT {e : ℕ} {σ : Type} (S : AnSys e σ) (w : Fin e → σ) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      mInt S.A (fun i => S.potT (w i) t) (fun _ => 1) = S.degNum w := by
  have hsm : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ i, S.A.Smooth (S.phT (w i) t) := by
    refine Filter.eventually_all.2 fun i => ?_
    obtain ⟨h0, -, hreg⟩ := S.reg (w i)
    filter_upwards [Ioc_mem_nhdsGT h0] with t ht
    exact (hreg t ht.1 ht.2).1
  filter_upwards [hsm] with t ht
  exact massIndep S.A (fun i => S.th (w i)) (fun i => S.phT (w i) t)
    (fun i => (S.sing (w i)).1) ht

theorem AnSys.abs_one_le_log_rW {e : ℕ} {σ : Type} (S : AnSys e σ) (y : S.X) :
    |(1 : ℝ)| ≤ 1 * Real.log (rW S.L S.s y) := by
  have h : Real.exp 1 ≤ rW S.L S.s y := by
    have := S.norm_le y
    unfold rW
    linarith
  have h1 : (1 : ℝ) ≤ Real.log (rW S.L S.s y) :=
    (Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos 1) h)).2 h
  simpa using h1

theorem AnSys.mIntegrable_potH_and_mInt_eq_degNum :
    ConvergenceSignedStatement → ∀ (e : ℕ) (σ : Type) (S : AnSys e σ) (w : Fin e → σ),
      MIntegrable S.A (fun i => S.potH (w i)) (fun _ => 1) ∧
        mInt S.A (fun i => S.potH (w i)) (fun _ => 1) = S.degNum w := by
  intro hC e σ S w
  letI : MeasurableSpace S.X := borel S.X
  haveI : BorelSpace S.X := ⟨rfl⟩
  have hlim := hC S.A S.Θ S.L S.s S.m S.W S.potΘ S.posΘ S.potL S.sec S.snc S.norm_le
    (fun i => S.th (w i)) (fun i => S.ph (w i)) (fun i => S.phT (w i)) S.C₅ S.C S.t₀
    (fun i => S.sing (w i)) (fun i => S.reg (w i)) (fun i => S.c2 (w i))
    (fun _ => 1) (fun _ _ => 1) 1 (fun _ => continuousOn_const)
    (fun _ y _ => S.abs_one_le_log_rW y)
    (TendstoUniformlyOn.tendstoLocallyUniformlyOn (by
      refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
      exact Filter.Eventually.of_forall fun _ _ _ => by simpa using hε))
  refine ⟨hlim.1, ?_⟩
  have hT : Tendsto (fun t => mInt S.A (fun i => S.potT (w i) t) (fun _ => 1))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (mInt S.A (fun i => S.potH (w i)) (fun _ => 1))) :=
    hlim.2
  have hc : Tendsto (fun t => mInt S.A (fun i => S.potT (w i) t) (fun _ => 1))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (S.degNum w)) :=
    tendsto_const_nhds.congr' ((S.eventually_mInt_potT w).mono fun _ h => h.symm)
  exact tendsto_nhds_unique hT hc

end GlobalTheory.CompanionTheory.Ar.PB
end
