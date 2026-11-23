module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SfDefs
public import Mathlib.RepresentationTheory.Irreducible
public import Development.AutomorphicArithmetic.TwistedTraces.Bundle007
import Development.AutomorphicArithmetic.TwistedTraces.Bundle005
public import Development.AutomorphicArithmetic.TwistedTraces.Bundle008
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.CuspDecayHeights.CuspDecay
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SiegelCount
import GroundTheory.AutomorphicForms.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.CuspDecayHeights.HeightLe
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsMeasure
public import GroundTheory.AutomorphicForms.L2LocalComponents.ArchBump
import GroundTheory.AutomorphicForms.Bundle016
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle004
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle003
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableCartan

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

private theorem comm_adj {A : Type} [Ring A] [Algebra ℂ A] {s t : Set A} (h : ∀ a ∈ s, ∀ b ∈ t, Commute a b) {a b : A}
    (ha : a ∈ Algebra.adjoin ℂ s) (hb : b ∈ Algebra.adjoin ℂ t) : Commute a b :=
  Algebra.commute_of_mem_adjoin_of_forall_mem_commute hb fun y hy =>
    (Algebra.commute_of_mem_adjoin_of_forall_mem_commute ha fun x hx => (h x hx y hy).symm).symm


theorem UpperTheory.isotypic_component_product_of_smooth_reps :
    ∀ (r : ℕ) (G : Fin r → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, T2Space (G i)] [∀ i, TotallyDisconnectedSpace (G i)] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : Fin r → Type) [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)] (π : ∀ i, UnitaryRep (G i) H) (τ : ∀ i, Representation ℂ (G i) (S i)) (V Z : Submodule ℂ H), (∀ i, GroundTheory.Automorphic.IsSmooth (τ i)) → (∀ i, (τ i).IsIrreducible) → (∀ i j, i ≠ j → ∀ g h v, π i g (π j h v) = π j h (π i g v)) → IsClosed (Z : Set H) → Z ≤ V → (∀ i, (π i).IsInvariant Z) → (∀ i, V ≤ (spanAll (τ i) (π i) V).topologicalClosure) → ∀ U : ∀ i, Subgroup (G i), (∀ i, IsCompact (U i : Set (G i)) ∧ IsOpen (U i : Set (G i))) → FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (U i)) → (Z ⊓ ⨅ i, fixU (π i) (U i)) ≠ ⊥ → (∀ i, FiniteDimensional ℂ (fixedVectors (τ i) (U i)) ∧ fixedVectors (τ i) (U i) ≠ ⊥) ∧ ∃ c : ∀ i, Module.End ℂ (fixedVectors (τ i) (U i)) →ₐ[ℂ] Module.End ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (U i)), (∀ i j, i ≠ j → ∀ a b, Commute (c i a) (c j b)) ∧ (∀ i t f, Eqv (τ i) (π i) (Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (U j)) f → ∀ (x : fixedVectors (τ i) (U i)) (y : ↥(Z ⊓ ⨅ i, fixU (π i) (U i))), (y : H) = f x → ((c i t y : ↥(Z ⊓ ⨅ i, fixU (π i) (U i))) : H) = f (t x)) ∧ ∀ i, (Z ⊓ ⨅ i, fixU (π i) (U i)) ≤ spanFix (τ i) (π i) (Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (U j)) (U i) := by
  intro r G _ _ _ _ _ _ H _ _ _ S _ _ π τ V Z hsm hirr hcm hZc hZV hZi hV U hU hfd hne
  set X := Z ⊓ ⨅ i, fixU (π i) (U i) with hX
  let D : Fin r → Submodule ℂ H := fun i => Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (U j)
  have hD : ∀ i v, v ∈ D i ↔ v ∈ Z ∧ ∀ j, j ≠ i → v ∈ fixU (π j) (U j) := fun i v => by
    simp only [D, Submodule.mem_inf, Submodule.mem_iInf]
  have hDc : ∀ i, IsClosed (D i : Set H) := fun i => by
    have : (D i : Set H) = (Z : Set H) ∩ ⋂ j, ⋂ _ : j ≠ i, (fixU (π j) (U j) : Set H) := by
      ext v; rw [SetLike.mem_coe, hD]; simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_iInter]
    rw [this]
    exact hZc.inter (isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_fixU _ _)
  have hDi : ∀ i, (π i).IsInvariant (D i) := fun i g v hv => (hD i _).2 ⟨hZi i g v ((hD i v).1 hv).1, fun j hj u hu => by
    rw [hcm j i hj, ((hD i v).1 hv).2 j hj u hu]⟩
  have hXD : ∀ i, X = D i ⊓ fixU (π i) (U i) := fun i => by
    ext v
    simp only [hX, Submodule.mem_inf, Submodule.mem_iInf, hD]
    refine ⟨fun h => ⟨⟨h.1, fun j _ => h.2 j⟩, h.2 i⟩, fun h => ⟨h.1.1, fun j => ?_⟩⟩
    by_cases e : j = i
    · exact e ▸ h.2
    · exact h.1.2 j e
  have hle : ∀ i, X ≤ spanFix (τ i) (π i) (D i) (U i) := fun i => (hXD i).le.trans
    (UpperTheory.inf_fixed_le_spanFix_of_dense_spanAll (G i) H (S i) (τ i) (hsm i) (π i) (U i) (hU i).1 (hU i).2 V (D i) (hDc i) (hDi i) (inf_le_left.trans hZV) (hV i)
      (hXD i ▸ hfd))
  have hm : ∀ i f, Eqv (τ i) (π i) (D i) f → ∀ x : fixedVectors (τ i) (U i), f x ∈ X := fun i f hf x => by
    rw [hXD i]
    exact ⟨hf.mem _, fun u hu => by rw [← hf.map, mem_fixedVectors.1 x.2 u hu]⟩
  have h1 : ∀ i, FiniteDimensional ℂ (fixedVectors (τ i) (U i)) ∧ fixedVectors (τ i) (U i) ≠ ⊥ := fun i => by
    obtain ⟨f, hf, x, hx, h0⟩ : ∃ f, Eqv (τ i) (π i) (D i) f ∧ ∃ x ∈ fixedVectors (τ i) (U i), f x ≠ 0 := by
      by_contra hno
      push Not at hno
      refine hne (le_bot_iff.1 ((hle i).trans (Submodule.span_le.2 ?_)))
      rintro _ ⟨f, hf, x, hx, rfl⟩
      exact hno f hf x hx
    have := hirr i
    have hinj : Function.Injective f := by
      rcases eq_bot_or_eq_top (⟨LinearMap.ker f, fun g v hv => by
        rw [LinearMap.mem_ker] at hv ⊢; rw [hf.map, hv, map_zero]⟩ : Subrepresentation (τ i)) with e | e
      · exact LinearMap.ker_eq_bot.1 (congrArg Subrepresentation.toSubmodule e)
      · exact (h0 (by rw [LinearMap.ker_eq_top.1 (congrArg Subrepresentation.toSubmodule e)]; rfl)).elim
    refine ⟨Module.Finite.of_injective ((f ∘ₗ (fixedVectors (τ i) (U i)).subtype).codRestrict X (hm i f hf)) fun a b e =>
      Subtype.ext (hinj (congrArg Subtype.val e)), fun e => h0 ?_⟩
    rw [e] at hx
    rw [(Submodule.mem_bot ℂ).1 hx, map_zero]
  refine ⟨h1, ?_⟩
  have := fun i => (h1 i).1
  have := fun i => Submodule.nontrivial_iff_ne_bot.2 (h1 i).2
  choose c hc1 hc2 using fun i => UpperTheory.exists_algHom_end_fixedVectors_to_fixed_subspace (G i) H (S i) (τ i) (hsm i) (hirr i) (π i) (U i) (hU i).1 (hU i).2 (D i) X
    (hDc i) (hDi i) (hXD i) (hle i)
  refine ⟨c, fun i j hij s t => ?_, fun i t f hf x y hy => hc1 i t f hf x y hy, hle⟩
  refine comm_adj ?_ (hc2 i s) (hc2 j t)
  rintro a ⟨g, ha⟩ b ⟨h, hb⟩
  obtain ⟨q1, q2⟩ := (UpperTheory.fixedProjection_invariant_and_commuting_reps (G i) (G j) H (π i) (π j) (U i) (U j)).2.2.2 (hcm i j hij)
  obtain ⟨q3, -⟩ := (UpperTheory.fixedProjection_invariant_and_commuting_reps (G j) (G i) H (π j) (π i) (U j) (U i)).2.2.2 (hcm j i hij.symm)
  refine LinearMap.ext fun v => Subtype.ext ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, ha, hb, hb, ha, ← q3, ← q1, q2, hcm i j hij]
end

section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped ContDiff

private theorem rconv_add_fun {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n))
    [μ.IsHaarMeasure] (a b : CC K n) (φ : L2 μ) (x : G1 K n) :
    rconv (Gam K n) μ (a + b : CC K n) φ x =
      rconv (Gam K n) μ a φ x + rconv (Gam K n) μ b φ x := by
  unfold rconv
  rw [← integral_add (integrable_rconv (Gam K n) μ a φ x) (integrable_rconv (Gam K n) μ b φ x)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [CompactlySupportedContinuousMap.coe_add, Pi.add_apply, add_mul]

private theorem cuspDecay_zero {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n))
    [μ.IsHaarMeasure] : CuspDecay μ (0 : CC K n) := fun _ =>
  ⟨0, fun φ _ x => by simp [rconv]⟩

private theorem cuspDecay_add {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n))
    [μ.IsHaarMeasure] {a b : CC K n} (ha : CuspDecay μ a) (hb : CuspDecay μ b) :
    CuspDecay μ (a + b) := fun N' => by
  obtain ⟨C₁, h₁⟩ := ha N'
  obtain ⟨C₂, h₂⟩ := hb N'
  refine ⟨C₁ + C₂, fun φ hφ x => ?_⟩
  rw [rconv_add_fun, add_mul, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (h₁ φ hφ x) (h₂ φ hφ x))

theorem UpperTheory.cuspDecay_finset_sum :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
        (ι : Type) [Fintype ι] (f : ι → CC K n), (∀ i, CuspDecay μ (f i)) → CuspDecay μ (∑ i, f i) := by
  intro K _ _ n μ _ ι _ f hf
  exact Finset.sum_induction f (CuspDecay μ) (fun _ _ => cuspDecay_add μ) (cuspDecay_zero μ)
    (fun i _ => hf i)
end

section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped ContDiff

theorem UpperTheory.cuspDecay_of_rank_zero :
    ∀ (K : Type) [Field K] [NumberField K] (μ : Measure (G1 K 0)) [μ.IsHaarMeasure] (a : CC K 0), CuspDecay μ a := by
  intro K _ _ μ _ a N'
  haveI : Subsingleton (AdelicGLn.AdelicGL K 0) :=
    ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩
  haveI : Subsingleton (G1 K 0) := ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩
  obtain ⟨Ω₀, hΩ₁, hΩ₁B, t, ht, hsieg⟩ := exists_siegelSet (K := K) 0
  have hbasic : ∃ (C : ℝ) (N : ℕ), ∀ φ : Lp ℂ 2 (quotientMeasure (Gam K 0) μ), ∀ b ∈ Ω₀,
      ∀ (ρ : Fin 0 → ℝ) (hρ : ∀ i, 0 < ρ i),
      (∀ i j : Fin 0, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) →
      ∀ kk ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K 0)), ∀ x : G1 K 0,
      (x : AdelicGLn.AdelicGL K 0) = b * diagUnits 0 (fun i => posIdele (K := K) (ρ i) (hρ i)) * kk →
      ∀ R : ℝ, 1 ≤ R → (∀ i j : Fin 0, i < j → ρ i / ρ j ≤ R) →
      ‖rconv (Gam K 0) μ a φ x‖ ≤ C * Real.sqrt (R ^ N) * ‖φ‖ := by
    obtain ⟨Cc, N, hCc⟩ := exists_encard_le_siegel hΩ₁ ht a.hasCompactSupport
    have hf2 : ∫⁻ y, ‖a y‖ₑ ^ 2 ∂μ ≠ ⊤ := by
      have h := a.continuous.memLp_of_hasCompactSupport (μ := μ) (p := 2) a.hasCompactSupport
      rw [← L2Kernel.eLpNorm_two_sq]
      have hnorm := h.eLpNorm_lt_top
      rw [eLpNorm_eq_eLpNorm' (by norm_num) (by simp) h.aestronglyMeasurable,
        ENNReal.toReal_ofNat] at hnorm
      exact (ENNReal.pow_lt_top hnorm).ne
    let A := (∫⁻ y, ‖a y‖ₑ ^ 2 ∂μ).toReal
    have hA : 0 ≤ A := ENNReal.toReal_nonneg
    refine ⟨Real.sqrt (A * max Cc 0), N, ?_⟩
    intro φ b hb ρ hρ hsieg kk hkk x hx R hR1 hR
    obtain ⟨m, hmC, hm⟩ := hCc b hb ρ hρ hsieg kk hkk x hx R hR1 hR
    have hS : MeasurableSet ((fun y => x * y) '' tsupport (a : G1 K 0 → ℂ)) :=
      (a.hasCompactSupport.image (continuous_const_mul x)).measurableSet
    have h1 := enorm_rconv_sq_le (Gam K 0) μ a φ x hS (fun y hy => image_eq_zero_of_notMem_tsupport
      fun h' => hy ⟨x⁻¹ * y, h', by simp⟩) hm
    rw [← mul_assoc] at h1
    have h2 := norm_le_of_enorm_sq_le (ENNReal.mul_ne_top hf2 (by simp)) h1
    refine h2.trans ?_
    gcongr
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ← Real.sqrt_mul (mul_nonneg hA
      (le_max_right _ _))]
    refine Real.sqrt_le_sqrt ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hmC.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (pow_nonneg (by linarith) _))) hA
  obtain ⟨C₀, N, hC₀⟩ := hbasic
  have hq : 1 ≤ qht (1 : G1 K 0) := le_ciInf fun _ => AutomorphicForm.one_le_height _
  have hqN : qht (1 : G1 K 0) ^ N' ≠ 0 := (pow_pos (by linarith) N').ne'
  refine ⟨max C₀ 0 * qht (1 : G1 K 0) ^ N', fun φ _ x => ?_⟩
  obtain ⟨γ, hγ⟩ := hsieg (x : AdelicGLn.AdelicGL K 0)
  obtain ⟨b, hb, a', ⟨ρ, hρ, hs, rfl⟩, kk, hkk, -⟩ := hγ
  have h := hC₀ φ b hb ρ hρ hs kk hkk x (Subsingleton.elim _ _) 1 le_rfl (fun i => i.elim0)
  rw [one_pow, Real.sqrt_one, mul_one] at h
  rw [Subsingleton.elim x 1] at h ⊢
  rw [mul_inv_cancel_right₀ hqN]
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
end

section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped ContDiff

private theorem frob_diag {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (M : Matrix (Fin n) (Fin n) 𝕜) (e : 𝕜) (r : ℝ)
    (he : ‖e‖ = r) : frobSq (M * Matrix.diagonal fun _ => e) = r ^ 2 * frobSq M := by
  simp only [frobSq, Matrix.mul_diagonal, norm_mul, mul_pow, he, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

private noncomputable def lam (K : Type) [Field K] [NumberField K] (n : ℕ) (s : {r : ℝ // 0 < r}) : ℝ :=
  ((rpowHom ((n * Module.finrank ℚ K : ℝ))⁻¹ s : {r : ℝ // 0 < r}) : ℝ)

private theorem lam_pos (K : Type) [Field K] [NumberField K] (n : ℕ) (s : {r : ℝ // 0 < r}) : 0 < lam K n s :=
  (rpowHom ((n * Module.finrank ℚ K : ℝ))⁻¹ s).2

private theorem infAt_zInf (K : Type) [Field K] [NumberField K] (n : ℕ) (s : {r : ℝ // 0 < r})
    (w : InfinitePlace K) : ∃ u : w.Completion, ‖u‖ = lam K n s ∧ ∀ a b : Fin n,
      Reduction.infAt w (infEmb K n (zInf K n s)) a b = if a = b then u else 0 := by
  refine ⟨(GroundTheory.Global.IdeleGroup.infiniteProj w (posIdele (K := K) (lam K n s) (lam_pos K n s)) : (w.Completion)ˣ), ?_, fun a b => ?_⟩
  · rw [GroundTheory.Global.IdeleGroup.coe_infiniteProj]
    exact norm_posIdele_infinite _ _ w
  · have e : centralSection K n s = diagUnits n fun _ => posIdele (K := K) (lam K n s) (lam_pos K n s) := rfl
    rw [infEmb_zInf, e, infAt_diagUnits, coe_diagUnits, Matrix.diagonal_apply]

private theorem quad_mul_zInf (K : Type) [Field K] [NumberField K] (n : ℕ) (A : ArchMatrix K n)
    (s : {r : ℝ // 0 < r}) : archQuad (A * archVal (zInf K n s)) = lam K n s ^ 2 * archQuad A := by
  have hr : ∀ v : {w : InfinitePlace K // InfinitePlace.IsReal w}, ∃ e : ℝ, ‖e‖ = lam K n s ∧
      realCompM v (archVal (zInf K n s)) = Matrix.diagonal fun _ => e := by
    rintro ⟨w, hw⟩
    obtain ⟨u, hu, hab⟩ := infAt_zInf K n s w
    refine ⟨InfinitePlace.Completion.extensionEmbeddingOfIsReal hw u, ?_, ?_⟩
    · rw [← hu]
      exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) u
    · ext a b
      have h1 := congrArg (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw) (hab a b)
      rw [infAt_infEmb_apply, extensionEmbeddingOfIsReal_symm] at h1
      simp only [realCompM_apply, Matrix.map_apply, realComp_apply, Matrix.diagonal_apply]
      rw [h1]
      split_ifs <;> simp
  have hc : ∀ v : {w : InfinitePlace K // InfinitePlace.IsComplex w}, ∃ e : ℂ, ‖e‖ = lam K n s ∧
      complexCompM v (archVal (zInf K n s)) = Matrix.diagonal fun _ => e := by
    rintro ⟨w, hw⟩
    obtain ⟨u, hu, hab⟩ := infAt_zInf K n s w
    refine ⟨InfinitePlace.Completion.extensionEmbedding w u, ?_, ?_⟩
    · rw [← hu]
      exact (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) u
    · ext a b
      have h1 := congrArg (InfinitePlace.Completion.extensionEmbedding w) (hab a b)
      rw [infAt_infEmb_apply, extensionEmbedding_symm _ hw] at h1
      simp only [complexCompM_apply, Matrix.map_apply, complexComp_apply, Matrix.diagonal_apply]
      rw [h1]
      split_ifs <;> simp
  simp only [archQuad, mul_add, Finset.mul_sum, map_mul]
  congr 1
  · refine Finset.sum_congr rfl fun v _ => ?_
    obtain ⟨e, he, hv⟩ := hr v
    rw [hv, frob_diag _ e _ he]
  · refine Finset.sum_congr rfl fun v _ => ?_
    obtain ⟨e, he, hv⟩ := hc v
    rw [hv, frob_diag _ e _ he]

private theorem quad_ne (K : Type) [Field K] [NumberField K] (n : ℕ) (hn : 0 < n) (a : archGroup K n) :
    archQuad (archVal a) ≠ 0 := by
  intro h
  have h0 := archQuad_eq_zero h
  have h1 : archVal a * archVal a⁻¹ = 1 := by
    rw [archVal, archVal, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
  rw [h0, zero_mul] at h1
  have h2 : (0 : mixedEmbedding.mixedSpace K) = 1 := by
    have h3 := congrFun (congrFun (congrArg mat h1) ⟨0, hn⟩) ⟨0, hn⟩
    rw [mat_zero, mat_one, Matrix.one_apply_eq] at h3
    exact h3
  obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
  by_cases hw : InfinitePlace.IsReal w
  · have h3 := congrArg (fun p : mixedEmbedding.mixedSpace K => p.1 ⟨w, hw⟩) h2
    exact zero_ne_one (α := ℝ) h3
  · have hw' := InfinitePlace.not_isReal_iff_isComplex.1 hw
    have h3 := congrArg (fun p : mixedEmbedding.mixedSpace K => p.2 ⟨w, hw'⟩) h2
    exact zero_ne_one (α := ℂ) h3

private theorem lam_exp (K : Type) [Field K] [NumberField K] (n : ℕ) (t : ℝ) :
    lam K n (GroundTheory.Global.expPos t) = Real.exp (t * (n * Module.finrank ℚ K : ℝ)⁻¹) := by
  change (Real.exp t) ^ ((n * Module.finrank ℚ K : ℝ))⁻¹ = _
  rw [← Real.exp_mul]

private noncomputable def lq (K : Type) [Field K] [NumberField K] (n : ℕ) (a : archGroup K n) : ℝ :=
  Real.log (archQuad (archVal a))

private theorem lq_mul (K : Type) [Field K] [NumberField K] (n : ℕ) (hn : 0 < n) (a : archGroup K n) (t : ℝ) :
    lq K n (a * zInf K n (GroundTheory.Global.expPos t)) = lq K n a + 2 * (n * Module.finrank ℚ K : ℝ)⁻¹ * t := by
  have e : archVal (a * zInf K n (GroundTheory.Global.expPos t)) = archVal a * archVal (zInf K n (GroundTheory.Global.expPos t)) := rfl
  rw [lq, e, quad_mul_zInf, lam_exp, Real.log_mul (by positivity) (quad_ne K n hn a), Real.log_pow, Real.log_exp, lq]
  push_cast
  ring

private theorem continuous_lq (K : Type) [Field K] [NumberField K] (n : ℕ) (hn : 0 < n) :
    Continuous (lq K n) :=
  Continuous.log ((contDiff_archQuad (K := K) (n := n)).continuous.comp continuous_archVal) (quad_ne K n hn)

theorem UpperTheory.exists_smooth_archCutoff_kbar_eq_one :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n →
        ∃ χ : archGroup K n → ℝ, (isExpLieAlgebra K n).IsSmoothFun (fun A => (χ A : ℂ)) ∧
          (∀ A, kbar (fun g => (χ g : ℂ)) A = 1) ∧
          ∀ C : Set (G1 K n), IsCompact C → ∃ D : Set (archGroup K n), IsCompact D ∧
            ∀ A, χ A ≠ 0 → archP K n A ∈ C → A ∈ D := by
  intro K _ _ n hn
  set d : ℝ := (n * Module.finrank ℚ K : ℝ) with hd
  have hd0 : 0 < d := by
    have : 0 < Module.finrank ℚ K := Module.finrank_pos
    have h2 : (0 : ℝ) < n := Nat.cast_pos.2 hn
    have h3 : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.2 this
    positivity
  set β : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩ with hβ
  set h : ℝ → ℝ := β.normed volume with hh
  set c : ℝ := 2 * d⁻¹ with hc
  have hc0 : 0 < c := by positivity
  refine ⟨fun A => c * h (lq K n A), ?_, fun A => ?_, fun C hC => ?_⟩
  · rw [IsExpLieAlgebra.isSmoothFun_iff]
    intro g
    have hY : ContDiff ℝ ∞ (fun Y : archLie K n => (Y : ArchMatrix K n)) :=
      (Submodule.subtypeL (archLie K n)).contDiff
    have hexp : ContDiff ℝ ∞ (NormedSpace.exp : ArchMatrix K n → ArchMatrix K n) :=
      contDiff_exp ℝ _
    have hq : ContDiff ℝ ∞ (archQuad : ArchMatrix K n → ℝ) := contDiff_archQuad.of_le le_top
    have e : (fun Y : archLie K n => lq K n (g * (isExpLieAlgebra K n).expG Y)) = fun Y : archLie K n =>
        Real.log (archQuad (archVal g * NormedSpace.exp (Y : ArchMatrix K n))) := by
      funext Y
      simp only [lq, archVal, Subgroup.coe_mul, Units.val_mul, IsExpLieAlgebra.coe_expG]
    have hl : ContDiff ℝ ∞ (fun Y : archLie K n => lq K n (g * (isExpLieAlgebra K n).expG Y)) := by
      rw [e]
      refine ContDiff.log (hq.comp (contDiff_const.mul (hexp.comp hY))) fun Y => ?_
      have := quad_ne K n hn (g * (isExpLieAlgebra K n).expG Y)
      simpa only [archVal, Subgroup.coe_mul, Units.val_mul, IsExpLieAlgebra.coe_expG] using this
    exact Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (β.contDiff_normed.comp hl))
  · have hemb : MeasurableEmbedding GroundTheory.Global.expPos :=
      GroundTheory.Global.expPosHomeomorph.measurableEmbedding
    rw [kbar, GroundTheory.Global.posRealMeasure_eq_map_expPos, hemb.integral_map]
    have e1 : ∀ t : ℝ, ((c * h (lq K n (A * zInf K n (GroundTheory.Global.expPos t))) : ℝ) : ℂ) =
        ((c * h (lq K n A + c * t) : ℝ) : ℂ) := fun t => by
      rw [lq_mul K n hn]
    simp only [e1]
    rw [integral_complex_ofReal, integral_const_mul]
    have e2 : ∫ t, h (lq K n A + c * t) = |c⁻¹| • ∫ y, h (lq K n A + y) :=
      Measure.integral_comp_mul_left (fun y => h (lq K n A + y)) c
    rw [e2, integral_add_left_eq_self h (lq K n A), hh, β.integral_normed, abs_of_pos (inv_pos.2 hc0),
      smul_eq_mul, mul_one, mul_inv_cancel₀ hc0.ne']
    simp
  · set C' : Set (archGroup K n) := (fun x : G1 K n => infPart K n (x : AdelicGLn.AdelicGL K n)) '' C with hC'
    have hC'c : IsCompact C' := hC.image (continuous_infPart.comp continuous_subtype_val)
    obtain ⟨M, hM⟩ := hC'c.exists_bound_of_continuousOn (continuous_lq K n hn).continuousOn
    set R : ℝ := (2 + M) / c with hR
    refine ⟨(fun p : archGroup K n × ℝ => p.1 * zInf K n (GroundTheory.Global.expPos p.2)) '' (C' ×ˢ Set.Icc (-R) R),
      (hC'c.prod isCompact_Icc).image
        (continuous_fst.mul (continuous_zInf.comp (GroundTheory.Global.expPosHomeomorph.continuous.comp continuous_snd))),
      fun A hA hAC => ?_⟩
    set r := detA K n A with hr
    set a := infPart K n (archP K n A : AdelicGLn.AdelicGL K n) with ha
    have haC : a ∈ C' := ⟨_, hAC, rfl⟩
    have hr' : GroundTheory.Global.expPos (Real.log r) = r := Subtype.ext (Real.exp_log r.2)
    have hAa : A = a * zInf K n (GroundTheory.Global.expPos (Real.log r)) := by
      rw [hr', ha, infPart_archP, inv_mul_cancel_right]
    have hsup : lq K n A ∈ Metric.ball (0 : ℝ) 2 := by
      have h1 : h (lq K n A) ≠ 0 := right_ne_zero_of_mul hA
      have h2 : lq K n A ∈ Function.support h := h1
      rw [hh, β.support_normed_eq] at h2
      exact h2
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hsup
    have hl := lq_mul K n hn a (Real.log r)
    rw [← hAa] at hl
    have hMa := hM a haC
    rw [Real.norm_eq_abs] at hMa
    have hct : |c * Real.log r| ≤ 2 + M := by
      have e3 : c * Real.log r = lq K n A - lq K n a := by rw [hl, hc, hd]; ring
      rw [e3]
      exact (abs_sub _ _).trans (by linarith)
    have ht : |Real.log r| ≤ R := by
      rw [hR, le_div_iff₀ hc0]
      rwa [abs_mul, abs_of_pos hc0, mul_comm] at hct
    exact ⟨(a, Real.log r), ⟨haC, abs_le.1 ht⟩, hAa.symm⟩
end
