module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.PsiDatumStatement
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IntegrableComplexContinuousBoundedSupport
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.TmDSingleMulVec
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Bundle001
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.ContinuousSecondMatrix
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.IntOfBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.TmAContDiffMulLeft
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.TransportGeo

@[expose] public section

section

noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.QuotA

open ReciprocityTheory.ChartRestriction.DS

section Group

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

theorem uh_mul {H A B : Mat k r} (hA : A ∈ Formalism.QuantumDeterminants.UH H) (hB : B ∈ Formalism.QuantumDeterminants.UH H) :
    A * B ∈ Formalism.QuantumDeterminants.UH H := by
  show (A * B)ᴴ * H * (A * B) = H
  have hA' : Aᴴ * H * A = H := hA
  have hB' : Bᴴ * H * B = H := hB
  calc (A * B)ᴴ * H * (A * B) = Bᴴ * (Aᴴ * H * A) * B := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = H := by rw [hA', hB']

theorem cay_inv {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P) : P * P⁻¹ = 1 ∧ P⁻¹ * P = 1 ∧ (P⁻¹)ᴴ * Pᴴ = 1 := by
  have hPu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPu
  refine ⟨h1, Matrix.nonsing_inv_mul P hPu, ?_⟩
  rw [← conjTranspose_mul, h1, conjTranspose_one]

theorem ujset_conj {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P) {M : Mat k r}
    (hM : M ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : P * M * P⁻¹ ∈ UJset ε := by
  obtain ⟨h1, -, h2⟩ := cay_inv hP
  have hC : Pᴴ * Jm ε * P = Formalism.QuantumDeterminants.Hpk k r := hP.2
  have hM' : Mᴴ * Formalism.QuantumDeterminants.Hpk k r * M = Formalism.QuantumDeterminants.Hpk k r := hM
  show (P * M * P⁻¹)ᴴ * Jm ε * (P * M * P⁻¹) = Jm ε
  calc (P * M * P⁻¹)ᴴ * Jm ε * (P * M * P⁻¹) = (P⁻¹)ᴴ * (Mᴴ * (Pᴴ * Jm ε * P) * M) * P⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = ((P⁻¹)ᴴ * Pᴴ) * Jm ε * (P * P⁻¹) := by rw [hC, hM', ← hC]; simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem uh_conj {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P) {u : Mat k r} (hu : u ∈ UJset ε) :
    P⁻¹ * u * P ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  obtain ⟨h1, -, h2⟩ := cay_inv hP
  have hC : Pᴴ * Jm ε * P = Formalism.QuantumDeterminants.Hpk k r := hP.2
  have hu' : uᴴ * Jm ε * u = Jm ε := hu
  show (P⁻¹ * u * P)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (P⁻¹ * u * P) = Formalism.QuantumDeterminants.Hpk k r
  rw [← hC]
  calc (P⁻¹ * u * P)ᴴ * (Pᴴ * Jm ε * P) * (P⁻¹ * u * P)
      = Pᴴ * (uᴴ * (((P⁻¹)ᴴ * Pᴴ) * Jm ε * (P * P⁻¹)) * u) * P := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Pᴴ * Jm ε * P := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one, hu']

end Group

section Per

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {Vp : Type*} [NormedAddCommGroup Vp]
  [InnerProductSpace ℂ Vp] [CompleteSpace Vp]

theorem ae_bdata {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} {u : Fin k → ℝ} {π : Mat k r → (Vp →L[ℂ] Vp)}
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} (hB : IsBData z c u π μW μN) :
    ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r := by
  have hW := hB.2.2.2.2.1
  have hN := hB.2.2.2.2.2
  have := hW.1
  have := hN.1
  have h1 : (μW.prod μN) ({x | Matrix.of x ∉ Formalism.QuantumDeterminants.UWset k r z} ×ˢ Set.univ) = 0 := by
    rw [Measure.prod_prod, hW.2.2.1, zero_mul]
  have h2 : (μW.prod μN) (Set.univ ×ˢ {x | Matrix.of x ∉ Formalism.QuantumDeterminants.Nset k r}) = 0 := by
    rw [Measure.prod_prod, hN.2.2.1, mul_zero]
  rw [ae_iff]
  refine measure_mono_null (fun p hp => ?_) (measure_union_null h1 h2)
  simp only [Set.mem_ofPred_eq, not_and_or] at hp
  rcases hp with hp | hp
  · exact Or.inl ⟨hp, trivial⟩
  · exact Or.inr ⟨trivial, hp⟩

theorem per_congr {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} {u : Fin k → ℝ} {π : Mat k r → (Vp →L[ℂ] Vp)}
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P)
    (hB : IsBData z c u π μW μN) (ψ : Mat k r → ℂ) {F G : Mat k r → ℂ} (hFG : ∀ g ∈ UJset ε, F g = G g)
    (ξ : Vp) {x : Mat k r} (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    per P μW μN ψ π F ξ x = per P μW μN ψ π G ξ x := by
  unfold per sInt
  apply integral_congr_ae
  filter_upwards [ae_bdata hB] with p hp
  have hm : Matrix.of p.1 * Matrix.of p.2 * x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
    uh_mul (uh_mul hp.1.1 hp.2.1) hx
  rw [hFG _ (ujset_conj hP hm)]

theorem eabB_zero {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P) {f : Mat k r → Vp}
    (hf : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), f y = 0) (a b : Fin (2 * r + k + 1)) {x : Mat k r}
    (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : eabB ε P a b f x = 0 := by
  obtain ⟨-, h2, -⟩ := cay_inv hP
  have key : ∀ X, inG ε X → (fun t : ℝ => f (P⁻¹ * (P * x * P⁻¹ * NormedSpace.exp ((t : ℂ) • X)) * P)) =
      fun _ => 0 := by
    intro X hX
    funext t
    apply hf
    have : P⁻¹ * (P * x * P⁻¹ * NormedSpace.exp ((t : ℂ) • X)) * P =
        x * (P⁻¹ * NormedSpace.exp ((t : ℂ) • X) * P) := by
      simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]
    rw [this]
    exact uh_mul hx (uh_conj hP (exp_smul_mem_UJset hX t))
  unfold eabB S7.EabV S7.EcV S7.RdV
  simp only
  rw [key _ (SmDerA.inG_cpart1 ε _), key _ (SmDerA.inG_cpart2 ε _)]
  simp

theorem per_add {u : Fin k → ℝ} {h : ℝ} {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ}
    {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp] {π : Mat k r → (Vp →L[ℂ] Vp)}
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P)
    (hB : IsBData z c u π μW μN) (hp : pOf ε = k + r) (hq : qOf ε = r + 1) (hgap : StepGap ε r h)
    {F G : Mat k r → ℂ} (hFc : ContinuousOn F (UJset ε))
    (hFb : ∃ C : ℝ, ∀ g ∈ UJset ε, ‖F g‖ ≤ C * frob g ^ (1 - aExp ε h)) (hGc : ContinuousOn G (UJset ε))
    (hGb : ∃ C : ℝ, ∀ g ∈ UJset ε, ‖G g‖ ≤ C * frob g ^ (1 - aExp ε h)) (ξ : Vp) {x : Mat k r}
    (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π (F + G) ξ x =
      per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π F ξ x + per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π G ξ x := by
  have hi := (per_spec k r ε u h z c Vp π μW μN P hP hB hp hq hgap).1
  obtain ⟨CF, hCF⟩ := hFb
  obtain ⟨CG, hCG⟩ := hGb
  have iF := hi F CF hFc hCF x hx ξ
  have iG := hi G CG hGc hCG x hx ξ
  unfold per sInt
  rw [← integral_add iF iG]
  congr 1
  funext p
  simp [add_smul]

theorem per_smul (P : Mat k r) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (ψ : Mat k r → ℂ)
    (π : Mat k r → (Vp →L[ℂ] Vp)) (a : ℂ) (F : Mat k r → ℂ) (ξ : Vp) (x : Mat k r) :
    per P μW μN ψ π (a • F) ξ x = a • per P μW μN ψ π F ξ x := by
  unfold per sInt
  rw [← integral_smul]
  congr 1
  funext p
  exact (smul_smul a _ _).symm

end Per

section Fun

variable {n : ℕ} {ε : Fin n → Bool}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem contOn_of_smooth {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : Formalism.REAL.SmoothOnG ε F) :
    ContinuousOn F (UJset ε) := by
  intro g₀ hg₀
  obtain ⟨U, F', hU, hg, hF', hEq⟩ := hF g₀ hg₀
  have hc : ContinuousAt F' g₀ := hF'.continuousOn.continuousAt (hU.mem_nhds hg)
  refine hc.continuousWithinAt.congr_of_eventuallyEq ?_ (hEq g₀ hg hg₀)
  filter_upwards [inter_mem_nhdsWithin (UJset ε) (hU.mem_nhds hg)] with g hg'
  exact hEq g hg'.2 hg'.1

theorem eqOn_unitary_of_toL2_eq {F G : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : IsSmoothL2 ε F) (hG : IsSmoothL2 ε G)
    (h : toL2 ε F = toL2 ε G) : ∀ g ∈ UJset ε, F g = G g := by
  have hF2 : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := hF.2 []
  have hG2 : MemLp (fun g : Formalism.REAL.UJ ε => G (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := hG.2 []
  unfold toL2 at h
  rw [dite_eq_left hF2, dite_eq_left hG2] at h
  have hae := (MemLp.toLp_eq_toLp_iff hF2 hG2).1 h
  have hcF : Continuous (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) := Formalism.REAL.continuous_smooth_on_group_eval hF.1
  have hcG : Continuous (fun g : Formalism.REAL.UJ ε => G (Formalism.MainNotions.S.umat g)) := Formalism.REAL.continuous_smooth_on_group_eval hG.1
  have heq := (hcF.ae_eq_iff_eq (Formalism.REAL.muG ε) hcG).1 hae
  intro g hg
  obtain ⟨y, rfl⟩ := exists_unitary_preimage ε hg
  exact congrFun heq y

end Fun

end ReciprocityTheory.ChartRestriction.DS.Lap.QuotA
end
end

section

noncomputable section

open Matrix MeasureTheory Filter

namespace ReciprocityTheory.ChartRestriction.DS.Lap.EvaluationEquivalence

open Formalism.QuantumDeterminants ReciprocityTheory.ChartRestriction.DS

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {H : Type} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] {σ : Mat k r → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ D}
  {u : Fin k → ℝ} {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} {Vp : Type}
  [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp] {π : Mat k r → (Vp →L[ℂ] Vp)}
  {μW μN : Measure (Mt k r)} {P x₀ g : Mat k r} {w : H} {a : ℝ}

theorem good_bound {m : H} (hm : TmGood ε σ x₀ w a m) :
    ∃ C : ℝ, ∀ y ∈ UJset ε, ‖coefX σ x₀ w m y‖ ≤ C * frob y ^ (1 - a) := by
  obtain ⟨C, hC⟩ := hm.2 []
  refine ⟨|C|, fun y hy => (hC y hy).trans ?_⟩
  have h1 := tmA_one_le_frob hy (0 : Fin (2 * r + k + 1))
  exact mul_le_mul (le_abs_self C) (Real.rpow_le_rpow_of_exponent_le h1 (by linarith))
    (Real.rpow_nonneg (by linarith) _) (abs_nonneg C)

theorem per_lin (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hB : IsBData z c u π μW μN) (hg : g ∈ UH (Hpk k r))
    (hb : S0.bS k r < a - 1) (ξ : Vp) {m m' : H} (hm : TmGood ε σ x₀ w a m)
    (hm' : TmGood ε σ x₀ w a m') (t : ℂ) :
    per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π (coefX σ x₀ w (m + t • m')) ξ g =
      per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π (coefX σ x₀ w m) ξ g +
        t • per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π (coefX σ x₀ w m') ξ g := by
  obtain ⟨C, hC⟩ := good_bound hm
  obtain ⟨C', hC'⟩ := good_bound hm'
  have i1 := CurveContinuity.int_of_bound hP hB hg ξ a hb _ (CurveContinuity.smooth_contOn hm.1) C hC
  have i2 := CurveContinuity.int_of_bound hP hB hg ξ a hb _ (CurveContinuity.smooth_contOn hm'.1) C' hC'
  unfold per sInt
  rw [← integral_smul]
  refine Eq.trans ?_ (integral_add i1 (i2.smul t))
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [coefX, map_add (f := _), map_smul, inner_add_right, inner_smul_right, add_smul, smul_smul,
    Pi.smul_apply]

theorem frame_form (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hg : g ∈ UH (Hpk k r)) :
    IsUnit (g * P⁻¹).det ∧ (g * P⁻¹)ᴴ * Hpk k r * (g * P⁻¹) = Jm ε := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  have h2 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  refine ⟨by rw [Matrix.det_mul]; exact (TransportGeo.uh_det hg).mul (Matrix.isUnit_nonsing_inv_det P hd),
    ?_⟩
  calc (g * P⁻¹)ᴴ * Hpk k r * (g * P⁻¹) = (P⁻¹)ᴴ * (gᴴ * Hpk k r * g) * P⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (P⁻¹)ᴴ * Pᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by rw [hg', ← hP.2]; simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]; rfl

theorem mul_inUJ (hP : Formalism.MainNotions.S.IsCayley k r ε P) {y : Mat k r} (hy : y ∈ UH (Hpk k r)) :
    P * y * P⁻¹ ∈ UJset ε := by
  show (P * y * P⁻¹)ᴴ * Jm ε * (P * y * P⁻¹) = Jm ε
  have h := (frame_form hP hy).2
  rw [← hP.2] at h
  refine Eq.trans ?_ h
  show (P * y * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * y * P⁻¹) = _
  simp only [conjTranspose_mul, Matrix.mul_assoc]

theorem per_deriv (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hx₀ : x₀ ∈ UJset ε)
    (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hB : IsBData z c u π μW μN) (hg : g ∈ UH (Hpk k r))
    (hb : S0.bS k r < a - 1) (ξ : Vp) {Y : Mat k r} (hY : Yᴴ * Hpk k r + Hpk k r * Y = 0) (m : D)
    (hm : TmGood ε σ x₀ w a (m : H))
    (hm' : TmGood ε σ x₀ w a ((actM E ((g * P⁻¹)⁻¹ * Y * (g * P⁻¹)) m : D) : H)) :
    HasDerivAt (fun t : ℝ => per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π (coefX σ x₀ w (m : H)) ξ
        (NormedSpace.exp ((t : ℂ) • Y) * g))
      (per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π
        (coefX σ x₀ w ((actM E ((g * P⁻¹)⁻¹ * Y * (g * P⁻¹)) m : D) : H)) ξ g) 0 := by
  obtain ⟨hR, hJ⟩ := frame_form hP hg
  set R := g * P⁻¹ with hRd
  have hX : inG ε (R⁻¹ * Y * R) := by
    have e1 : Jm ε * (R⁻¹ * Y * R) = Rᴴ * (Hpk k r * Y) * R := by
      rw [← hJ]; simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hR]
    have e2 : (R⁻¹ * Y * R)ᴴ * Jm ε = Rᴴ * (Yᴴ * Hpk k r) * R := by
      have h2 : (R⁻¹)ᴴ * Rᴴ = 1 := by
        rw [← conjTranspose_mul, Matrix.mul_nonsing_inv _ hR, conjTranspose_one]
      rw [← hJ]
      simp only [conjTranspose_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (R⁻¹)ᴴ, h2, Matrix.one_mul]
    show (R⁻¹ * Y * R)ᴴ * Jm ε + Jm ε * (R⁻¹ * Y * R) = 0
    rw [e1, e2, ← Matrix.add_mul, ← Matrix.mul_add, hY, Matrix.mul_zero, Matrix.zero_mul]
  have hRd' : ∀ y ∈ UJset ε, Formalism.REAL.Rd (R⁻¹ * Y * R) (coefX σ x₀ w (m : H)) y =
      coefX σ x₀ w ((actM E (R⁻¹ * Y * R) m : D) : H) y := fun y hy =>
    tmB_rd_coef hσ hD (tmA_inUJ_mul (tmA_inUJ_inv hx₀) hy) hX w m
  obtain ⟨C, hC⟩ := good_bound hm
  obtain ⟨C', hC'⟩ := good_bound hm'
  have h := (CurveContinuity.deriv_int hP hB hg ξ a hb _ hm.1 C hC _ hX C'
    (fun y hy => by rw [hRd' y hy]; exact hC' y hy)).2
  refine HasDerivAt.congr_deriv (h.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)) ?_
  · have e : NormedSpace.exp ((t : ℂ) • (R⁻¹ * Y * R)) = R⁻¹ * NormedSpace.exp ((t : ℂ) • Y) * R := by
      rw [← Matrix.exp_conj' _ _ ((Matrix.isUnit_iff_isUnit_det R).mpr hR), Matrix.mul_smul,
        Matrix.smul_mul]
    simp only [per, sInt, e]
    congr 1
    funext p
    congr 2
    calc _ = P * (Matrix.of p.1 * Matrix.of p.2) * (NormedSpace.exp ((t : ℂ) • Y) * R) := by
          rw [hRd]; simp only [Matrix.mul_assoc]
      _ = P * (Matrix.of p.1 * Matrix.of p.2) * (R * (R⁻¹ * (NormedSpace.exp ((t : ℂ) • Y) * R))) := by
          rw [Matrix.mul_nonsing_inv_cancel_left _ _ hR]
      _ = _ := by
          rw [← Matrix.mul_assoc R⁻¹]
          generalize R⁻¹ * NormedSpace.exp ((t : ℂ) • Y) * R = A
          rw [hRd]; simp only [Matrix.mul_assoc]
  · unfold per sInt
    refine integral_congr_ae ?_
    filter_upwards [CurveContinuity.ae_supp hB.2.2.2.2.1 hB.2.2.2.2.2] with p hp
    rw [hRd' _ (mul_inUJ hP (TransportGeo.uh_mul (TransportGeo.uh_mul hp.1.1 hp.2.1) hg))]

end ReciprocityTheory.ChartRestriction.DS.Lap.EvaluationEquivalence
end
end
