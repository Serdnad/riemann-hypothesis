module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle007
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle009
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.InGOne
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle012
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle005
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SingToDiff
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle015
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle012
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.DetSecondCayleyBlockNe
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.MultiplicityOneTestOperators
public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.ContinuousOnIteratedFDerivTranslate
import Mathlib.Topology.UniformSpace.Uniformizable
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DefsPlus
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle003

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.CrxMa

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem continuous_matrix_lower_left_block : Continuous (fun M : M2 n => M.toBlocks₂₁) := by
  have : (fun M : M2 n => M.toBlocks₂₁) = fun M => M.submatrix Sum.inr Sum.inl := by funext M; rfl
  rw [this]; exact continuous_id.matrix_submatrix _ _

theorem continuous_matrix_lower_right_block : Continuous (fun M : M2 n => M.toBlocks₂₂) := by
  have : (fun M : M2 n => M.toBlocks₂₂) = fun M => M.submatrix Sum.inr Sum.inr := by funext M; rfl
  rw [this]; exact continuous_id.matrix_submatrix _ _

theorem continuous_cayley_first_block : Continuous (fun M : M2 n => u1 M) := by
  unfold u1
  exact ((continuous_const : Continuous fun _ : M2 n => Complex.I).smul continuous_matrix_lower_left_block).add continuous_matrix_lower_right_block

theorem continuous_cayley_second_block : Continuous (fun M : M2 n => u2 M) := by
  unfold u2
  exact ((continuous_const : Continuous fun _ : M2 n => Complex.I).smul continuous_matrix_lower_left_block).neg.add continuous_matrix_lower_right_block

theorem isOpen_OmZ (hFz : FzHol) (Kg : Type) [TopologicalSpace Kg] [CompactSpace Kg] (ι : Kg → M2 n)
    (hι : Continuous ι) : IsOpen {x : M2 n | ∀ k, ι k * x ∈ DomZ n} :=
  isOpen_setK (hFz n 0 0).1 Kg ι hι

theorem gset_sub_OmZ (hFz : FzHol) {Kg : Type} (ι : Kg → M2 n) (hιG : ∀ k, InG (ι k)) :
    GSet n ⊆ {x : M2 n | ∀ k, ι k * x ∈ DomZ n} :=
  fun _g hg k => (hFz n 0 0).2.1 (inG_mul (hιG k) hg)

theorem continuousOn_vacuum_at_zero (hFz : FzHol) (m : ℕ) : ContinuousOn (fun x : M2 n => fz m 0 0 x) (DomZ n) := by
  intro x hx
  have hA := (hFz n m 0).2.2 ((0 : ℂ), x) ⟨Set.mem_univ _, hx⟩
  have hmk : Continuous fun y : M2 n => ((0 : ℂ), y) := by fun_prop
  exact (hA.continuousAt.comp hmk.continuousAt).continuousWithinAt

theorem continuous_rhoP (hFz : FzHol) (m : ℕ) {Kg : Type} [TopologicalSpace Kg] (ι : Kg → M2 n)
    (hι : Continuous ι) (hιG : ∀ k, InG (ι k)) (Y : Matrix (Fin n) (Fin n) ℂ) : Continuous (rhoP ι m 0 Y) := by
  unfold rhoP
  have hfz : Continuous fun k => fz m 0 0 (ι k) :=
    (continuousOn_vacuum_at_zero hFz m).comp_continuous hι (fun k => (hFz n m 0).2.1 (hιG k))
  have hinv : Continuous fun k => (u2 (ι k))⁻¹ := by
    have e : (fun k => (u2 (ι k))⁻¹) = fun k => (u2 (ι k)).det⁻¹ • (u2 (ι k)).adjugate := by
      funext k; rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [e]
    have hd := (continuous_cayley_second_block.comp hι).matrix_det
    exact (hd.inv₀ (fun k => det_second_cayley_block_ne_zero (hιG k))).smul ((continuous_cayley_second_block.comp hι).matrix_adjugate)
  exact (hfz.mul (((hinv.matrix_mul continuous_const).matrix_mul (continuous_cayley_first_block.comp hι)).matrix_trace)).star

theorem contDiffOn_PhiZ (hFd : FdProps) (hFz : FzHol) (m : ℕ) (Kg : Type) [TopologicalSpace Kg] [CompactSpace Kg]
    [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [IsFiniteMeasure μ] (ι : Kg → M2 n) (hι : Continuous ι)
    (c : Kg → ℂ) (hc : Continuous c) :
    ContDiffOn ℂ ∞ (fun x => ∫ k, Fd m (ι k * x) * c k ∂μ) {x : M2 n | ∀ k, ι k * x ∈ DomZ n} := by
  have hF : ContDiffOn ℂ ∞ (Fd (n := n) m) (DomZ n) := (hFd n m).1.of_le le_top
  exact (PositivityTheory.Rg.Sw.LVs.holInt n Kg μ _ (fun k x => Fd m (ι k * x) * c k) (isOpen_OmZ hFz Kg ι hι)
    (fun N => continuousOn_iteratedFDeriv_translate (Fd m) (DomZ n) (hFz n 0 0).1 hF Kg ι hι c hc N)
    (fun k => (hF.comp (contDiff_mulLeft (ι k)).contDiffOn
      (fun x (hx : x ∈ {x : M2 n | ∀ k, ι k * x ∈ DomZ n}) => hx k)).mul contDiffOn_const)).1

theorem fubini_gen (F : M2 n → ℂ) (U : Set (M2 n)) (hF : ContinuousOn F U) (hGU : GSet n ⊆ U)
    (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg]
    [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hι : Continuous ι)
    (hιG : ∀ k, InG (ι k)) (ρ : Kg → ℂ) (hρ : Continuous ρ) (a b : M2 n) (ha : InG a) (hb : InG b)
    (ψ : (Fin n → Fin n → ℝ) → ℂ) (hψ : IsSingTest ψ) :
    ∫ t, (∫ k, F (ι k * (a * nU (herm t) * b)) * ρ k ∂μ) * ψ t =
      ∫ k, ρ k * (∫ t, F (1 * ι k * a * nU (herm t) * b) * ψ t) ∂μ := by
  have hherm : Continuous (herm (n := n)) := by
    unfold herm; fun_prop
  have hnU : Continuous fun x : Fin n → Fin n → ℝ => nU (herm x) := by
    unfold nU; exact Continuous.matrix_fromBlocks continuous_const hherm continuous_const continuous_const
  have hmap : Continuous fun z : Kg × (Fin n → Fin n → ℝ) => ι z.1 * a * nU (herm z.2) * b :=
    (((hι.comp continuous_fst).mul continuous_const).mul (hnU.comp continuous_snd)).mul continuous_const
  set Fp : Kg × (Fin n → Fin n → ℝ) → ℂ := fun z => F (ι z.1 * a * nU (herm z.2) * b) * ψ z.2 * ρ z.1 with hFpdef
  have hFc : Continuous Fp :=
    ((hF.comp_continuous hmap (fun z => hGU (inG_mul (inG_mul (inG_mul (hιG z.1) ha) (inG_nU_herm z.2)) hb))).mul
      (hψ.1.comp continuous_snd)).mul (hρ.comp continuous_fst)
  have hFs : HasCompactSupport Fp := by
    refine IsCompact.of_isClosed_subset (isCompact_univ.prod hψ.2.1) (isClosed_tsupport Fp) ?_
    refine closure_minimal (fun z hz => ⟨Set.mem_univ _, subset_tsupport ψ ?_⟩)
      (isClosed_univ.prod (isClosed_tsupport ψ))
    intro h0; apply hz; simp [hFpdef, h0]
  have hFi : Integrable Fp (μ.prod volume) := hFc.integrable_of_hasCompactSupport hFs
  have e1 : ∀ k, ρ k * (∫ t, F (1 * ι k * a * nU (herm t) * b) * ψ t) = ∫ t, Fp (k, t) := by
    intro k; rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hFpdef, Matrix.one_mul]; ring
  have e2 : ∀ t, (∫ k, F (ι k * (a * nU (herm t) * b)) * ρ k ∂μ) * ψ t = ∫ k, Fp (k, t) ∂μ := by
    intro t; rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [hFpdef, Matrix.mul_assoc]; ring
  simp_rw [e1, e2]
  exact (integral_integral_swap (f := fun k x => Fp (k, x)) hFi).symm

theorem stepA_Z (hFd : FdProps) (hFz : FzHol) (m : ℕ) (Kg : Type) [Group Kg] [TopologicalSpace Kg]
    [IsTopologicalGroup Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg)
    [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hι : Continuous ι) (hK : ∀ g, InK g ↔ ∃ k, ι k = g)
    (hneg : ∀ (P : Matrix (Fin n) (Fin n) ℂ) (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b x : M2 n), IsSingTest ψ → InG a →
      InG b → InG x → deriv (fun z => tOp μ ι (rhoP ι m 0 P) ψ a b (fz m 0 z) x) 0 = 0)
    (Y : Matrix (Fin n) (Fin n) ℂ) (a b : M2 n) (ha : InG a) (hb : InG b) :
    detD (fun H => ∫ k, Fd m (ι k * (a * nU H * b)) * rhoP ι m 0 Y k ∂μ) = 0 := by
  have hιG : ∀ k, InG (ι k) := fun k => ((hK (ι k)).2 ⟨k, rfl⟩).1
  have hΩo := isOpen_OmZ hFz Kg ι hι
  have hGΩ := gset_sub_OmZ hFz ι hιG
  have hρ := continuous_rhoP hFz m ι hι hιG Y
  have hΦ := contDiffOn_PhiZ hFd hFz m Kg μ ι hι _ hρ
  have hpre : IsOpen {H : Matrix (Fin n) (Fin n) ℂ | a * nU H * b ∈ {x : M2 n | ∀ k, ι k * x ∈ DomZ n}} :=
    hΩo.preimage (contDiff_nU_sandwich a b).continuous
  have h0 : (0 : Matrix (Fin n) (Fin n) ℂ) ∈
      {H : Matrix (Fin n) (Fin n) ℂ | a * nU H * b ∈ {x : M2 n | ∀ k, ι k * x ∈ DomZ n}} := by
    show a * nU 0 * b ∈ {x : M2 n | ∀ k, ι k * x ∈ DomZ n}
    have : nU (0 : Matrix (Fin n) (Fin n) ℂ) = 1 := by simp [nU, Matrix.fromBlocks_one]
    rw [this, mul_one]; exact hGΩ (inG_mul ha hb)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hpre 0 h0
  refine singToDiff n (fun H => ∫ k, Fd m (ι k * (a * nU H * b)) * rhoP ι m 0 Y k ∂μ) r hr
    (hΦ.comp (contDiff_nU_sandwich a b).contDiffOn (fun H hH => hball hH)) ?_
  intro ψ hψ
  have h1 := hneg Y ψ a b 1 hψ ha hb inG_one
  rw [(hFd n m).2 Kg μ ι hι hK (rhoP ι m 0 Y) ψ a b 1 hρ hψ.1 hψ.2.1 ha hb inG_one] at h1
  rw [← h1]
  have hFc : ContinuousOn (Fd (n := n) m) (DomZ n) := (hFd n m).1.continuousOn
  exact fubini_gen (Fd m) (DomZ n) hFc (hFz n 0 0).2.1 Kg μ ι hι hιG _ hρ a b ha hb ψ hψ

end PositivityTheory.Rg.Sw.HSt.CrxMa
end
end

section

noncomputable section

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.LoweringDerivative

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem rhoP_add {Kg : Type} (ι : Kg → M2 n) (m : ℕ) (e : ℤ) (X Y : Matrix (Fin n) (Fin n) ℂ) (k : Kg) :
    rhoP ι m e (X + Y) k = rhoP ι m e X k + rhoP ι m e Y k := by
  simp only [rhoP, Matrix.mul_add, Matrix.add_mul, trace_add, mul_add, star_add]

theorem rhoP_smul {Kg : Type} (ι : Kg → M2 n) (m : ℕ) (e : ℤ) (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (k : Kg) :
    rhoP ι m e (c • X) k = star c * rhoP ι m e X k := by
  simp only [rhoP, Matrix.mul_smul, Matrix.smul_mul, trace_smul, smul_eq_mul, star_mul']; ring

section Main

variable {Kg : Type} [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg] [MeasurableSpace Kg]
  [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hι : Continuous ι)
  (hK : ∀ g, InK g ↔ ∃ k, ι k = g) (m : ℕ) (e : ℤ) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : Continuous ψ)
  (hψc : HasCompactSupport ψ) {a b : M2 n} (ha : InG a) (hb : InG b)

def abelian₂ (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b : M2 n) (z : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  tOp μ ι (rhoP ι m e X) ψ a b (fz m e z) 1

theorem Lam_eq (z : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    abelian₂ μ ι m e ψ a b z X = ∫ k, rhoP ι m e X k * Hf m e ψ a b z (ι k) ∂μ := by
  simp only [abelian₂, tOp, Hf, one_mul]

include hι hK hψ hψc ha hb in
theorem continuous_integrand (z : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun k => rhoP ι m e X k * Hf m e ψ a b z (ι k) := by
  have hG : ∀ k, InG (ι k) := fun k => LoweringDerivative.inG_of_inK ((hK (ι k)).2 ⟨k, rfl⟩)
  have h1 : Continuous (rhoP (⇑ι) m e X) := LoweringDerivative.continuous_rhoP (⇑ι) hι hG m e X
  have h2 := continuous_Hf m e hψ hψc ha hb
  have h3 : Continuous fun k : Kg => ((⟨ι k, hG k⟩ : Gs n), z) :=
    (Continuous.subtype_mk hι (fun k => hG k)).prodMk continuous_const
  have h4 : Continuous fun k : Kg => Hf m e ψ a b z (ι k) := by
    have h5 := h2.comp h3
    simp only [Function.comp_def] at h5
    exact h5
  exact h1.mul h4

include hι hK hψ hψc ha hb in
theorem integrable_integrand (z : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    Integrable (fun k => rhoP ι m e X k * Hf m e ψ a b z (ι k)) μ := by
  exact (continuous_integrand ι hι hK m e hψ hψc ha hb z X).integrable_of_hasCompactSupport
    (isClosed_tsupport _).isCompact

include hι hK hψ hψc ha hb in
theorem Lam_add (z : ℂ) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    abelian₂ μ ι m e ψ a b z (X + Y) = abelian₂ μ ι m e ψ a b z X + abelian₂ μ ι m e ψ a b z Y := by
  simp only [Lam_eq, rhoP_add, add_mul]
  exact integral_add (integrable_integrand μ ι hι hK m e hψ hψc ha hb z X)
    (integrable_integrand μ ι hι hK m e hψ hψc ha hb z Y)

theorem Lam_smul (z c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    abelian₂ μ ι m e ψ a b z (c • X) = star c * abelian₂ μ ι m e ψ a b z X := by
  simp only [Lam_eq, rhoP_smul, mul_assoc, integral_const_mul]

private theorem inK_fromBlocks_unitary_diag (U : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1) :
    InK (Matrix.fromBlocks U 0 0 U : M2 n) := by
  refine ⟨?_, ?_⟩
  · simp [InG, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hU]
  · simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hU]

private theorem u1_fromBlocks_diag_mul (U : Matrix (Fin n) (Fin n) ℂ) (y : M2 n) :
    u1 (Matrix.fromBlocks U 0 0 U * y) = U * u1 y := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks y]
  simp [u1, Matrix.fromBlocks_multiply, Matrix.mul_add, Matrix.mul_smul]

private theorem u2_fromBlocks_diag_mul (U : Matrix (Fin n) (Fin n) ℂ) (y : M2 n) :
    u2 (Matrix.fromBlocks U 0 0 U * y) = U * u2 y := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks y]
  simp [u2, Matrix.fromBlocks_multiply, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_neg]

include hK ha hb in
theorem Lam_inv (z : ℂ) {U X : Matrix (Fin n) (Fin n) ℂ} (hU : Uᴴ * U = 1) (hX : Xᴴ * X = 1) :
    abelian₂ μ ι m e ψ a b z (U * X * Uᴴ) = abelian₂ μ ι m e ψ a b z X := by
  obtain ⟨k0, hk0⟩ := (hK _).1 (inK_fromBlocks_unitary_diag U hU)
  have hG : ∀ k, InG (ι k) := fun k => LoweringDerivative.inG_of_inK ((hK (ι k)).2 ⟨k, rfl⟩)
  have hpG : InG (Matrix.fromBlocks U 0 0 U : M2 n) := LoweringDerivative.inG_of_inK (inK_fromBlocks_unitary_diag U hU)
  have hp21 : Matrix.toBlocks₂₁ (Matrix.fromBlocks U 0 0 U : M2 n) = 0 :=
    Matrix.toBlocks_fromBlocks₂₁ _ _ _ _
  have hUi : U⁻¹ = Uᴴ := Matrix.inv_eq_left_inv hU
  have hd : star U.det * U.det = 1 := by
    rw [← Matrix.det_conjTranspose, ← Matrix.det_mul, hU, Matrix.det_one]
  have hn : Complex.normSq U.det = 1 := by
    have h : (Complex.normSq U.det : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self]
      exact hd
    exact_mod_cast h
  have hl : ∀ w : ℂ, lam m e w (Matrix.fromBlocks U 0 0 U : M2 n) =
      (U.det * U.det) ^ e * U.det ^ (-(m : ℤ)) := by
    intro w
    simp only [lam, Matrix.toBlocks_fromBlocks₂₂, Matrix.det_fromBlocks_zero₂₁, hn, Complex.ofReal_one,
      Complex.one_cpow, mul_one]
  have h1 : star ((U.det * U.det) ^ e) * (U.det * U.det) ^ e = 1 := by
    rw [star_zpow₀, ← mul_zpow, star_mul',
      show star U.det * star U.det * (U.det * U.det) = (star U.det * U.det) * (star U.det * U.det) by ring,
      hd, one_mul, _root_.one_zpow]
  have h2 : star (U.det ^ (-(m : ℤ))) * U.det ^ (-(m : ℤ)) = 1 := by
    rw [star_zpow₀, ← mul_zpow, hd, _root_.one_zpow]
  have hlam : star (lam m e 0 (Matrix.fromBlocks U 0 0 U : M2 n)) *
      lam m e z (Matrix.fromBlocks U 0 0 U : M2 n) = 1 := by
    rw [hl, hl]
    calc star ((U.det * U.det) ^ e * U.det ^ (-(m : ℤ))) * ((U.det * U.det) ^ e * U.det ^ (-(m : ℤ)))
        = (star ((U.det * U.det) ^ e) * (U.det * U.det) ^ e) *
          (star (U.det ^ (-(m : ℤ))) * U.det ^ (-(m : ℤ))) := by
          rw [star_mul']
          ring
      _ = 1 := by rw [h1, h2, one_mul]
  have aux : ∀ A B C : ℂ, star (lam m e 0 (Matrix.fromBlocks U 0 0 U : M2 n)) * A * B *
      (lam m e z (Matrix.fromBlocks U 0 0 U : M2 n) * C) = A * B * C := by
    intro A B C
    linear_combination (A * B * C) * hlam
  have key : ∀ k, rhoP ι m e (U * X * Uᴴ) (k0 * k) * Hf m e ψ a b z (ι (k0 * k)) =
      rhoP ι m e X k * Hf m e ψ a b z (ι k) := by
    intro k
    have hm : (u2 (ι k))⁻¹ * Uᴴ * (U * X * Uᴴ) * (U * u1 (ι k)) = (u2 (ι k))⁻¹ * X * u1 (ι k) := by
      calc (u2 (ι k))⁻¹ * Uᴴ * (U * X * Uᴴ) * (U * u1 (ι k))
          = (u2 (ι k))⁻¹ * (Uᴴ * U) * X * (Uᴴ * U) * u1 (ι k) := by
            simp only [Matrix.mul_assoc]
        _ = (u2 (ι k))⁻¹ * X * u1 (ι k) := by
            rw [hU]
            simp only [Matrix.mul_one]
    simp only [rhoP]
    rw [map_mul, hk0, Hf_up m e ψ ha hb hpG hp21 (hG k) z, fz_up hpG hp21 (hG k) m e 0,
      u1_fromBlocks_diag_mul, u2_fromBlocks_diag_mul, Matrix.mul_inv_rev, hUi, hm]
    simp only [star_mul']
    exact aux _ _ _
  have hinv := integral_mul_left_eq_self (μ := μ)
    (fun k => rhoP ι m e (U * X * Uᴴ) k * Hf m e ψ a b z (ι k)) k0
  simp only [key] at hinv
  rw [Lam_eq, Lam_eq]
  exact hinv.symm

end Main

end PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks
end
end

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.HSt.Conv

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt.GRH

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem continuous_kR : Continuous (fun k : KR n => mR (k : GR n)) := PositivityTheory.Rg.Sw.AbsSt.continuous_mR.comp continuous_subtype_val

def kSet (S : Set (M2 n)) : Set (M2 n) := (fun p : KR n × M2 n => mR (p.1 : GR n) * p.2) '' (univ ×ˢ S)

theorem isCompact_kSet {S : Set (M2 n)} (hS : IsCompact S) : IsCompact (kSet S) :=
  (isCompact_univ.prod hS).image ((continuous_kR.comp continuous_fst).mul continuous_snd)

theorem tw_eq_zero (m : ℕ) (e : ℤ) (μK : Measure (KR n)) (β : M2 n → ℝ) {X : M2 n} (hX : X ∉ kSet (tsupport β)) :
    tw m e μK β X = 0 := by
  unfold tw
  have hz : ∀ k : KR n, β ((mR (k : GR n))ᴴ * X) = 0 := by
    intro k
    by_contra h
    apply hX
    have hk : InK (mR (k : GR n)) := k.2
    have hkk : mR (k : GR n) * (mR (k : GR n))ᴴ = 1 := mul_eq_one_comm.mp hk.2
    refine ⟨(k, (mR (k : GR n))ᴴ * X), ⟨mem_univ _, subset_tsupport _ h⟩, ?_⟩
    simp only
    rw [← Matrix.mul_assoc, hkk, Matrix.one_mul]
  simp [hz]

theorem tw_support (m : ℕ) (e : ℤ) (μK : Measure (KR n)) {β : M2 n → ℝ} (hβ : HasCompactSupport β) :
    HasCompactSupport (tw m e μK β) := by
  refine HasCompactSupport.intro (isCompact_kSet hβ) fun X hX => tw_eq_zero m e μK β hX

end PositivityTheory.Rg.Sw.HSt.Conv
end
end

section

noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.HSt.HolTPf

open PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

def Dom (n : ℕ) : Set (Fin n → Fin n → ℂ) :=
  {Z | ((-(Complex.I / 2)) • (Matrix.of Z - (Matrix.of Z)ᴴ)).PosDef}

end PositivityTheory.Rg.Sw.HSt.HolTPf
end
end
