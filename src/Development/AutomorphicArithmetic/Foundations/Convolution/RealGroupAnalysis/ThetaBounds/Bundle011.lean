module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle004
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.EmbPiInjective
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle010
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle008
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.WtLeOfNorm
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Bundle002
import GroundTheory.HeightsAndTheta.Theta.AdelicFourierCoord
import GroundTheory.HeightsAndTheta.Theta.Weil.PartialFourierAdelicPi
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem wt_nonneg' {F : Type} [Field F] [NumberField F]
    (S : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F)) (N : ℕ) (v : V4 F) : 0 ≤ wt S N v := by
  unfold wt
  split_ifs
  · positivity
  · exact le_rfl

private theorem wt_mono'' {F : Type} [Field F] [NumberField F]
    {S S' : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F)} (h : S ⊆ S') (N : ℕ) (v : V4 F) :
    wt S N v ≤ wt S' N v := by
  unfold wt
  by_cases hv : finPartPi v ∈ S
  · rw [if_pos hv, if_pos (h hv)]
  · rw [if_neg hv]
    split_ifs
    · positivity
    · exact le_rfl

private noncomputable def sc4 {F : Type} [Field F] [NumberField F] : (A F)ˣ →* GL (Fin 4) (A F) :=
  Units.map (Matrix.scalar (Fin 4) : A F →+* Matrix (Fin 4) (Fin 4) (A F)).toMonoidHom

private theorem continuous_scalarFour {F : Type} [Field F] [NumberField F] :
    Continuous (sc4 (F := F)) := by
  refine Continuous.units_map _ ?_
  change Continuous fun a : A F => Matrix.scalar (Fin 4) a
  simp only [Matrix.scalar_apply]
  exact Continuous.matrix_diagonal (continuous_pi fun _ => continuous_id)

private theorem scalarFour_mulVec {F : Type} [Field F] [NumberField F] (a : (A F)ˣ) (v : V4 F) :
    (sc4 a).val *ᵥ v = fun i => (a : A F) * v i := by
  funext i
  change (Matrix.scalar (Fin 4) (a : A F) *ᵥ v) i = _
  rw [Matrix.scalar_apply, Matrix.mulVec_diagonal]

theorem UpperTheory.ConvolutionTheory.R2.Ff.omCpt :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D), OmCpt W := by
  intro F E _ _ _ _ _ _ _ D W φ hφ C hC
  obtain ⟨-, hIw⟩ := iwa F
  obtain ⟨U, hUc, hU⟩ := hIw C hC
  obtain ⟨n, e, he⟩ := omFin F E D W φ hφ
  have hdom : ∀ i, Dom (Set.univ : Set Unit) fun _ => (e i).1 := fun i => (wtBound F (e i)).2
  choose Ki hKi hB using hdom
  have hK : IsCompact (⋃ i, Ki i) := isCompact_iUnion hKi
  obtain ⟨K', hK', hlin⟩ := wtLin F (sc4 '' U) (hUc.image continuous_scalarFour) _ hK
  obtain ⟨m, hm⟩ := (hUc.image (M.continuous_ab (F := F))).bddAbove
  refine ⟨K', hK', fun N => ?_⟩
  obtain ⟨B, hBl⟩ := hlin N
  choose Bi hBi using fun i => hB i N
  refine ⟨max m 0 ^ 2 * ((∑ i, |Bi i|) * |B|), fun g hg v => ?_⟩
  obtain ⟨b, a, ha, k, hk, rfl⟩ := hU g hg
  obtain ⟨c, hc, hsum⟩ := he k hk
  have hη : ‖((W.η.1 a : ℂˣ) : ℂ)‖ = 1 := by
    have h2 : ((W.η.1 a : ℂˣ) : ℂ) ^ 2 = 1 := by
      rw [← Units.val_pow_eq_pow_val, W.η_sq a, Units.val_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp (by rw [← norm_pow, h2, norm_one])
  set w : V4 F := fun i => (a : A F) * v i with hw
  have hψ : ∀ x : A F, ‖ψ x‖ = 1 := fun x => Circle.norm_coe _
  have h1 : ‖(W.Om (nU b * mD a * k) φ).1 v‖ = ab a ^ 2 * ‖(W.Om k φ).1 w‖ := by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, W.Om_n, W.Om_m, norm_mul,
      hψ, one_mul, norm_mul, norm_mul, hη, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  have h2 : (W.Om k φ).1 w = ∑ i, c i * (e i).1 w := by
    rw [hsum]
    simp [Finset.sum_apply]
  have hlinw : wt (⋃ i, Ki i) N w ≤ |B| * wt K' N v := by
    have := hBl (sc4 a) ⟨a, ha, rfl⟩ v
    rw [scalarFour_mulVec] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self B) (wt_nonneg' _ _ _))
  have h3 : ‖(W.Om k φ).1 w‖ ≤ (∑ i, |Bi i|) * (|B| * wt K' N v) := by
    rw [h2, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul]
    calc ‖c i‖ * ‖(e i).1 w‖ ≤ 1 * ‖(e i).1 w‖ :=
          mul_le_mul_of_nonneg_right (hc i) (norm_nonneg _)
      _ = ‖(e i).1 w‖ := one_mul _
      _ ≤ Bi i * wt (Ki i) N w := hBi i () (Set.mem_univ _) w
      _ ≤ |Bi i| * wt (Ki i) N w :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (wt_nonneg' _ _ _)
      _ ≤ |Bi i| * wt (⋃ i, Ki i) N w :=
          mul_le_mul_of_nonneg_left (wt_mono'' (Set.subset_iUnion Ki i) N w) (abs_nonneg _)
      _ ≤ |Bi i| * (|B| * wt K' N v) := mul_le_mul_of_nonneg_left hlinw (abs_nonneg _)
  have h4 : ab a ^ 2 ≤ max m 0 ^ 2 :=
    pow_le_pow_left₀ (M.ab_pos a).le ((hm ⟨a, ha, rfl⟩).trans (le_max_left _ _)) 2
  rw [h1]
  calc ab a ^ 2 * ‖(W.Om k φ).1 w‖
      ≤ max m 0 ^ 2 * ((∑ i, |Bi i|) * (|B| * wt K' N v)) :=
        mul_le_mul h4 h3 (norm_nonneg _) (by positivity)
    _ = max m 0 ^ 2 * ((∑ i, |Bi i|) * |B|) * wt K' N v := by ring
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

noncomputable section

namespace UpperTheory.ConvolutionTheory.R2.Ff.HM

variable {F : Type} [Field F] [NumberField F]

private theorem comp_signed_mem {ι κ : Type} [Fintype ι] [Fintype κ] (e : κ ≃ ι) (ε : κ → F)
    (hε : ∀ k, ε k * ε k = 1) {G : (κ → A F) → ℂ} (hG : G ∈ schwartzBruhatPi (K := F) (ι := κ)) :
    (fun x : ι → A F => G fun k => rt (ε k) * x (e k)) ∈ schwartzBruhatPi (K := F) (ι := ι) := by
  have hD : Matrix.diagonal ε * Matrix.diagonal ε = (1 : Matrix κ κ F) := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    exact hε k
  let M : Matrix κ ι F := (Matrix.diagonal ε).submatrix id e.symm
  let N : Matrix ι κ F := (Matrix.diagonal ε).submatrix e.symm id
  have hNM : N * M = 1 := by
    have h := Matrix.submatrix_mul (Matrix.diagonal ε) (Matrix.diagonal ε) e.symm id e.symm
      Function.bijective_id
    rw [hD, Matrix.submatrix_one_equiv] at h
    exact h.symm
  have hMN : M * N = 1 := by
    have h := Matrix.submatrix_mul (Matrix.diagonal ε) (Matrix.diagonal ε) id e.symm id
      e.symm.bijective
    rw [hD, Matrix.submatrix_id_id] at h
    exact h.symm
  have h := GroundTheory.Heights₂.Theta.comp_mulVec_mem_schwartzBruhatPi M N hNM hMN hG
  have hx : ∀ x : ι → A F, (M.map (algebraMap F (A F)) *ᵥ x) = fun k => rt (ε k) * x (e k) := by
    intro x
    funext k
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, M, Matrix.submatrix_apply, id]
    rw [← e.sum_comp]
    simp only [Matrix.diagonal_apply]
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  simpa only [hx] using h

private def eS : Fin 3 ⊕ Unit ≃ Fin 4 where
  toFun := Sum.elim ![0, 2, 3] fun _ => 1
  invFun := ![.inl 0, .inr (), .inl 1, .inl 2]
  left_inv := by
    rintro (i | ⟨⟩)
    · fin_cases i <;> rfl
    · rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

private def FF (φ : V4 F → ℂ) (z : Fin 3 ⊕ Unit → A F) : ℂ := φ fun i => z (eS.symm i)

private theorem FF_mem {φ : V4 F → ℂ} (hφ : φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) :
    FF φ ∈ schwartzBruhatPi (K := F) (ι := Fin 3 ⊕ Unit) := by
  have h := comp_signed_mem (F := F) eS.symm (fun _ => 1) (fun _ => by simp) hφ
  have he : FF φ = fun x => φ fun k => rt ((fun _ => 1 : Fin 4 → F) k) * x (eS.symm k) := by
    funext x
    simp [FF]
  rw [he]
  exact h

private theorem slice_integrable {φ : V4 F → ℂ} (hφ : φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) (x : V4 F) :
    Integrable (fun s => φ (Function.update x 1 s)) (adeleMeasure F) := by
  have h := GroundTheory.Heights₂.Theta.integrable_partialFourierPi_slice (FF_mem hφ) (fun i => x (eS (Sum.inl i)))
  have hmp := measurePreserving_funUnique (adeleMeasure F) Unit
  refine (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).1 ?_
  have e : (fun s => φ (Function.update x 1 s)) ∘ (MeasurableEquiv.funUnique Unit (A F)) =
      fun y => FF φ (Sum.elim (fun i => x (eS (Sum.inl i))) y) := by
    funext y
    simp only [Function.comp, FF]
    congr 1
    funext i
    fin_cases i <;> simp [eS]
  rw [e]
  exact h

private theorem slice_mul_integrable {φ : V4 F → ℂ} (hφ : φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) (x : V4 F) :
    Integrable (fun s => φ (Function.update x 1 s) * ψ (-(s * x 1))) (adeleMeasure F) := by
  refine (slice_integrable hφ x).mul_bdd (c := 1) ?_ ?_
  · exact (continuous_ψ.comp (continuous_id.mul continuous_const).neg).aestronglyMeasurable
  · exact Eventually.of_forall fun s => by simp

private theorem hat_add {a b : V4 F → ℂ} (ha : a ∈ schwartzBruhatPi (K := F) (ι := Fin 4))
    (hb : b ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) (x : V4 F) : hat (a + b) x = hat a x + hat b x := by
  unfold hat
  rw [← integral_add (slice_mul_integrable ha x) (slice_mul_integrable hb x)]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp [add_mul]

private theorem hat_smul (c : ℂ) (a : V4 F → ℂ) (x : V4 F) : hat (c • a) x = c * hat a x := by
  unfold hat
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp [mul_assoc]

private theorem hat_sum {ι : Type} (s : Finset ι) (f : ι → S4 F) (x : V4 F) :
    hat (∑ i ∈ s, f i).1 x = ∑ i ∈ s, hat (f i).1 x := by
  induction s using Finset.induction_on with
  | empty =>
    have : ((0 : S4 F)).1 = (0 : ℂ) • (0 : V4 F → ℂ) := by simp
    simp only [Finset.sum_empty]
    rw [this, hat_smul, zero_mul]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    exact hat_add (f i).2 (∑ i ∈ s, f i).2 x

private theorem wt_mono {K K' : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F)} (h : K ⊆ K') (N : ℕ) (v : V4 F) :
    wt K N v ≤ wt K' N v := by
  unfold wt
  by_cases hv : finPartPi v ∈ K
  · rw [if_pos hv, if_pos (h hv)]
  · rw [if_neg hv]
    split_ifs
    · positivity
    · exact le_rfl

private theorem wt_nonneg (K : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F)) (N : ℕ) (v : V4 F) : 0 ≤ wt K N v := by
  unfold wt
  split_ifs
  · positivity
  · exact le_rfl

end UpperTheory.ConvolutionTheory.R2.Ff.HM

end

open UpperTheory.ConvolutionTheory.R2.Ff.HM

theorem UpperTheory.ConvolutionTheory.R2.Ff.hatMaj :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D), HatMaj W := by
  intro F E _ _ _ _ _ _ _ D W φ hφ y hy
  have hS := hatSt F E D W
  obtain ⟨n, e, he⟩ := omFin F E D W φ hφ
  have hb : ∀ i, ∃ K, IsCompact K ∧ ∀ N, ∃ B : ℝ, ∀ v,
      ‖hat (W.L (infGL E 2 y) (e i)).1 v‖ ≤ B * wt K N v := fun i => by
    obtain ⟨_, K, hK, h⟩ := wtBound F ⟨_, hS.mem (W.L (infGL E 2 y) (e i))⟩
    exact ⟨K, hK, fun N => by
      obtain ⟨B, hB⟩ := h N
      exact ⟨B, fun v => hB () trivial v⟩⟩
  choose K hK hB using hb
  refine ⟨⋃ i, K i, isCompact_iUnion hK, fun N => ?_⟩
  choose B hB' using fun i => hB i N
  refine ⟨∑ i, |B i|, fun b a k hk x u t => ?_⟩
  obtain ⟨c, hc, hk'⟩ := he k hk
  have hcomm : W.Om k (W.L (infGL E 2 y) φ) = W.L (infGL E 2 y) (W.Om k φ) := by
    have h := W.comm (infGL E 2 y) k
    rw [show nu F (infGL E 2 y) = 1 from hy, cD_one_left] at h
    exact (LinearMap.congr_fun h φ).symm
  have hΨ : W.Om k (W.L (infGL E 2 y) φ) = ∑ i, c i • W.L (infGL E 2 y) (e i) := by

    rw [hcomm, hk', map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
  have hsplit : W.Om (nU b * mD a * k) (W.L (infGL E 2 y) φ) =
      W.Om (nU b) (W.Om (mD a) (∑ i, c i • W.L (infGL E 2 y) (e i))) := by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hΨ]
  have hv : Function.update ![(0 : A F), x, u, t] 1 (![(0 : A F), x, u, t] 1 + b * ![(0 : A F), x, u, t] 0) = ![0, x, u, t] := by
    funext i
    fin_cases i <;> simp
  have hη : ‖((W.η.1 a : ℂˣ) : ℂ)‖ = 1 := by
    have h0 := W.η_sq a
    have h : ((W.η.1 a : ℂˣ) : ℂ) ^ 2 = 1 := by
      first
        | exact h0
        | (rw [← Units.val_pow_eq_pow_val, h0]; rfl)
        | simpa using congrArg Units.val h0
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 (by rw [← norm_pow, h, norm_one])
  set v' : V4 F := ![0, ((a⁻¹ : (A F)ˣ) : A F) * x, a * u, a * t] with hv'
  have hm : hat (W.Om (mD a) (∑ i, c i • W.L (infGL E 2 y) (e i))).1 ![0, x, u, t] =
      ((W.η.1 a : ℂˣ) : ℂ) * ((ab a : ℝ) : ℂ) * hat (∑ i, c i • W.L (infGL E 2 y) (e i)).1 v' := by
    rw [hS.m]
    simp [hv']
  have hsum : ‖hat (∑ i, c i • W.L (infGL E 2 y) (e i)).1 v'‖ ≤ (∑ i, |B i|) * wt (⋃ i, K i) N v' := by
    rw [hat_sum, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    have h1 : hat (c i • W.L (infGL E 2 y) (e i)).1 v' = c i * hat (W.L (infGL E 2 y) (e i)).1 v' :=
      hat_smul _ _ _
    rw [h1, norm_mul]
    calc ‖c i‖ * ‖hat (W.L (infGL E 2 y) (e i)).1 v'‖
        ≤ 1 * (B i * wt (K i) N v') := mul_le_mul (hc i) (hB' i v') (norm_nonneg _) zero_le_one
      _ ≤ |B i| * wt (⋃ i, K i) N v' := by
        rw [one_mul]
        exact (mul_le_mul_of_nonneg_right (le_abs_self _) (wt_nonneg _ _ _)).trans
          (mul_le_mul_of_nonneg_left (wt_mono (Set.subset_iUnion K i) N v') (abs_nonneg _))
  rw [hsplit, hS.n, hv, norm_mul, norm_ψ, one_mul, hm, norm_mul, norm_mul, hη, one_mul,
    Complex.norm_real, Real.norm_of_nonneg (ab_pos a).le]
  calc ab a * ‖hat (∑ i, c i • W.L (infGL E 2 y) (e i)).1 v'‖
      ≤ ab a * ((∑ i, |B i|) * wt (⋃ i, K i) N v') := mul_le_mul_of_nonneg_left hsum (ab_pos a).le
    _ = (∑ i, |B i|) * ab a * wt (⋃ i, K i) N v' := by ring
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem wt_nonneg {F : Type} [Field F] [NumberField F]
    (K : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F)) (N : ℕ) (v : V4 F) : 0 ≤ wt K N v := by
  unfold wt
  split_ifs <;> positivity

private theorem wt_mono {F : Type} [Field F] [NumberField F]
    {K K' : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F)} (h : K ⊆ K') (N : ℕ) (v : V4 F) :
    wt K N v ≤ wt K' N v := by
  unfold wt
  by_cases hv : finPartPi v ∈ K
  · rw [if_pos hv, if_pos (h hv)]
  · rw [if_neg hv]
    split_ifs
    · positivity
    · exact le_rfl

private theorem common_majorant {F : Type} [Field F] [NumberField F] {n : ℕ} (e : Fin n → S4 F) (N : ℕ) :
    ∃ K : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F), IsCompact K ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ i v, ‖(e i).1 v‖ ≤ B * wt K N v := by
  have h : ∀ i, ∃ K : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F), IsCompact K ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ v, ‖(e i).1 v‖ ≤ B * wt K N v := by
    intro i
    obtain ⟨K, hK, hb⟩ := (wtBound F (e i)).2
    obtain ⟨B, hB⟩ := hb N
    refine ⟨K, hK, |B|, abs_nonneg B, fun v => ?_⟩
    exact (hB () (Set.mem_univ _) v).trans
      (mul_le_mul_of_nonneg_right (le_abs_self B) (wt_nonneg K N v))
  choose K hK B hB hb using h
  refine ⟨⋃ i, K i, isCompact_iUnion hK, ∑ i, B i, Finset.sum_nonneg fun i _ => hB i, fun i v => ?_⟩
  calc ‖(e i).1 v‖ ≤ B i * wt (K i) N v := hb i v
    _ ≤ B i * wt (⋃ i, K i) N v :=
        mul_le_mul_of_nonneg_left (wt_mono (Set.subset_iUnion K i) N v) (hB i)
    _ ≤ (∑ i, B i) * wt (⋃ i, K i) N v :=
        mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _ => hB i) (Finset.mem_univ i))
          (wt_nonneg _ N v)

section Pointwise

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] {D : Dat F E}

private theorem norm_eta (W : Weil D) (a : (A F)ˣ) : ‖((W.η.1 a : ℂˣ) : ℂ)‖ = 1 := by
  have h : ((W.η.1 a : ℂˣ) : ℂ) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, W.η_sq a, Units.val_one]
  have h' : ‖((W.η.1 a : ℂˣ) : ℂ)‖ ^ 2 = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h'

private theorem om_L_comm (W : Weil D) {y : GL (Fin 2) (Cinf E)} (hy : One F y) (k : G1 F) (φ : S4 F) :
    W.Om k (W.L (infGL E 2 y) φ) = W.L (infGL E 2 y) (W.Om k φ) := by
  have h := LinearMap.congr_fun (W.comm (infGL E 2 y) k) φ
  have hy' : nu F (infGL E 2 y) = 1 := hy
  rw [hy', cD_one_left] at h
  exact h.symm

private theorem norm_term (W : Weil D) {y : GL (Fin 2) (Cinf E)} (hy : One F y) (b : A F) (a : (A F)ˣ)
    (k : G1 F) (φ : S4 F) (ξ : Fin 4 → F) :
    ‖(W.Om (nU b * mD a * k) (W.L (infGL E 2 y) φ)).1 fun i => rt (ξ i)‖ =
      ab a ^ 2 * ‖(W.Om k φ).1 (D.act (infGL E 2 y)⁻¹ (sc a ξ))‖ := by
  have hy' : nu F (infGL E 2 y) = 1 := hy
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, om_L_comm W hy, W.Om_n, W.Om_m,
    W.L_apply, hy', ab_one]
  simp only [norm_mul, norm_ψ, one_mul, norm_eta, inv_one, Complex.ofReal_one, norm_one]
  rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rfl

end Pointwise

theorem UpperTheory.ConvolutionTheory.R2.Ff.thMaj :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D), ThMaj W := by
  intro F E _ _ _ _ _ _ _ D W φ hφ c hc
  obtain ⟨n, e, he⟩ := omFin F E D W φ hφ
  obtain ⟨N, hN⟩ := wtSum F
  obtain ⟨K, hK, B, hB, hBe⟩ := common_majorant e N
  obtain ⟨C, hC⟩ := hN K hK c hc
  obtain ⟨C₀, hC₀⟩ := wtAct F E D
  refine ⟨n * B * |C₀| ^ N * C, 2 * N, fun y hy b a k hk hca => ?_⟩
  obtain ⟨hsum, htsum⟩ := hC a hca
  obtain ⟨cf, hcf, hk'⟩ := he k hk
  have hHt : 0 ≤ Ht y := by unfold Ht; positivity

  set T : ℝ := |C₀| ^ N * Ht y ^ (2 * N) with hT
  have hT0 : 0 ≤ T := by positivity
  have hTact : ∀ v, wt K N (D.act (infGL E 2 y)⁻¹ v) ≤ T * wt K N v := by
    intro v
    refine (hC₀ K N y v).trans (mul_le_mul_of_nonneg_right ?_ (wt_nonneg K N v))
    calc (C₀ * Ht y ^ 2) ^ N ≤ |(C₀ * Ht y ^ 2) ^ N| := le_abs_self _
      _ = T := by rw [abs_pow, abs_mul, abs_of_nonneg (pow_nonneg hHt 2), mul_pow, ← pow_mul, hT]
  have hM : 0 ≤ ab a ^ 2 * (n * B * T) :=
    mul_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hB) hT0)
  have hterm : ∀ ξ : Fin 4 → F, ‖(W.Om (nU b * mD a * k) (W.L (infGL E 2 y) φ)).1 fun i => rt (ξ i)‖ ≤
      (ab a ^ 2 * (n * B * T)) * wt K N (sc a ξ) := by
    intro ξ
    rw [norm_term W hy, hk']
    set u := D.act (infGL E 2 y)⁻¹ (sc a ξ) with hu
    have hval : (∑ i, cf i • e i : S4 F).1 u = ∑ i, cf i * (e i).1 u := by
      simp [Submodule.coe_sum, Finset.sum_apply]
    have hb : ‖(∑ i, cf i • e i : S4 F).1 u‖ ≤ n * B * wt K N u := by
      rw [hval]
      calc ‖∑ i, cf i * (e i).1 u‖ ≤ ∑ i, ‖cf i * (e i).1 u‖ := norm_sum_le _ _
        _ ≤ ∑ _i : Fin n, B * wt K N u := Finset.sum_le_sum fun i _ => by
            rw [norm_mul]
            calc ‖cf i‖ * ‖(e i).1 u‖ ≤ 1 * (B * wt K N u) :=
                  mul_le_mul (hcf i) (hBe i u) (norm_nonneg _) zero_le_one
              _ = B * wt K N u := one_mul _
        _ = n * B * wt K N u := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
    have hnB : 0 ≤ (n : ℝ) * B := mul_nonneg (Nat.cast_nonneg _) hB
    calc ab a ^ 2 * ‖(∑ i, cf i • e i : S4 F).1 u‖
        ≤ ab a ^ 2 * (n * B * (T * wt K N (sc a ξ))) :=
          mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_left (hTact _) hnB)) (sq_nonneg _)
      _ = (ab a ^ 2 * (n * B * T)) * wt K N (sc a ξ) := by ring
  have hs := hsum.hasSum.mul_left (ab a ^ 2 * (n * B * T))
  calc ‖Th (W.Om (nU b * mD a * k) (W.L (infGL E 2 y) φ)).1‖
      ≤ (ab a ^ 2 * (n * B * T)) * ∑' ξ, wt K N (sc a ξ) := tsum_of_norm_bounded hs hterm
    _ ≤ (ab a ^ 2 * (n * B * T)) * C := mul_le_mul_of_nonneg_left htsum hM
    _ = n * B * |C₀| ^ N * C * Ht y ^ (2 * N) * ab a ^ 2 := by rw [hT]; ring
end
