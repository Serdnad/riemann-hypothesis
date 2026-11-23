module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle004
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableCartan
import Mathlib.Algebra.Module.StablyFree.Basic
public import GroundTheory.AutomorphicForms.DiscreteSpectrumAbstract
public import GroundTheory.AutomorphicForms.GKModules.Casimir
public import GroundTheory.AutomorphicForms.GKModules.SmoothVectors
public import GroundTheory.AutomorphicForms.Bundle004
public import GroundTheory.AutomorphicForms.TraceClass
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Complex
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SfDefs
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Archimedean
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.AltSum
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting
import GroundTheory.AutomorphicForms.QuotientMeasure
import GroundTheory.AutomorphicForms.Bundle003
import GroundTheory.AutomorphicForms.WhittakerRelevance
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Ring.Basic

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

theorem UpperTheory.trace_restrict_eq_of_hasFinTrace :
    ∀ (S : Type) [AddCommGroup S] [Module ℂ S] (Q Q' : Submodule ℂ S) [FiniteDimensional ℂ Q'] (g : S →ₗ[ℂ] S) (t : ℂ) (m : Module.End ℂ Q') (e : Q' →ₗ[ℂ] S), Q ≤ Q' → HasFinTrace g t → (∀ x, g x ∈ Q) → (∀ x : Q', ((m x : Q') : S) = g (e x)) → (∀ x : Q', (x : S) ∈ Q → e x = x) → LinearMap.trace ℂ Q' m = t := by
  intro S _ _ Q Q' _ g t m e hQ hg hgQ hm he
  obtain ⟨hfd, hr⟩ := hg
  haveI := hfd
  have hWQ : LinearMap.range g ≤ Q := by
    rintro _ ⟨x, rfl⟩
    exact hgQ x
  let p : Q' →ₗ[ℂ] LinearMap.range g :=
    (g ∘ₗ e).codRestrict (LinearMap.range g) fun x => LinearMap.mem_range_self g (e x)
  let q : LinearMap.range g →ₗ[ℂ] Q' := Submodule.inclusion (hWQ.trans hQ)
  have e1 : m = q ∘ₗ p := by
    ext x
    exact hm x
  have e2 : g.restrict (p := LinearMap.range g) (q := LinearMap.range g)
      (fun v _ => LinearMap.mem_range_self g v) = p ∘ₗ q := by
    ext x
    exact congrArg g (he (q x) (hWQ x.2)).symm
  rw [e1, LinearMap.trace_comp_comm', ← e2, hr]
end

section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

private theorem algebra_trace_pi_eq_sum_trace {R A ι : Type*} [CommRing R] [CommRing A] [Algebra R A] [Fintype ι]
    [Module.Free R A] [Module.Finite R A] (x : ι → A) :
    Algebra.trace R (ι → A) x = ∑ i, Algebra.trace R A (x i) := by
  classical
  let b := Module.Free.chooseBasis R A
  rw [Algebra.trace_eq_matrix_trace (Pi.basis fun _ : ι => b), Matrix.trace, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_repr, Pi.basis_apply]

theorem UpperTheory.trace_mixedSpace_eq_mixedTraceL_mul :
    ∀ (K : Type) [Field K] [NumberField K] (x : NumberField.mixedEmbedding.mixedSpace K),
      Algebra.trace ℝ (NumberField.mixedEmbedding.mixedSpace K) x =
        mixedTraceL (K := K) (x * ((fun _ => (1 : ℝ)), (fun _ => (2 : ℂ)))) := by
  classical
  intro K _ _ x
  rw [Algebra.trace_prod_apply, algebra_trace_pi_eq_sum_trace, algebra_trace_pi_eq_sum_trace]
  simp [mixedTraceL, Algebra.trace_complex_apply, mul_comm]
end

section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.exists_approximate_identity_integrated :
    ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [OpensMeasurableSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H) (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] (N : Set G), N ∈ 𝓝 (1 : G) → ∃ f : CompactlySupportedContinuousMap G ℂ, ∀ (v : H) (r : ℝ), (∀ g ∈ N, ‖π g v - v‖ ≤ r) → ‖π.integrated μ (UnitaryRep.ccToL1 μ f) v - v‖ ≤ r := by
  intro G H _ _ _ _ _ _ _ _ _ _ π μ _ _ N hN
  obtain ⟨U, hUsub, hUo, h1U⟩ := mem_nhds_iff.1 hN
  obtain ⟨h, h1, h0, hcs, hrange⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_singleton (x := (1 : G))) hUo.isClosed_compl
    (Set.disjoint_singleton_left.2 fun h => h h1U)
  have hnn : ∀ g, 0 ≤ h g := fun g => (hrange g).1
  set c : ℝ := ∫ g, h g ∂μ with hc
  have hcpos : 0 < c := h.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs hnn
    (by rw [h1 (Set.mem_singleton 1)]; exact one_ne_zero)
  let k : G → ℝ := fun g => c⁻¹ * h g
  have hkc : Continuous k := continuous_const.mul h.continuous
  have hkcs : HasCompactSupport k := by
    have : k = (fun _ => c⁻¹) * (h : G → ℝ) := rfl
    rw [this]
    exact hcs.mul_left
  have hknn : ∀ g, 0 ≤ k g := fun g => mul_nonneg (inv_nonneg.2 hcpos.le) (hnn g)
  have hkint : Integrable k μ := hkc.integrable_of_hasCompactSupport hkcs
  have hk1 : ∫ g, k g ∂μ = 1 := by
    simp only [k]
    rw [integral_const_mul, ← hc, inv_mul_cancel₀ hcpos.ne']
  let f : CompactlySupportedContinuousMap G ℂ :=
    ⟨⟨fun g => (k g : ℂ), by fun_prop⟩, hkcs.comp_left Complex.ofReal_zero⟩
  have hfg : ∀ g, f g = (k g : ℂ) := fun _ => rfl
  refine ⟨f, fun v r hr => ?_⟩
  have hint1 : Integrable (fun g => f g • π g v) μ :=
    (f.continuous.smul (π.continuous_orbit v)).integrable_of_hasCompactSupport
      f.hasCompactSupport.smul_right
  have hint2 : Integrable (fun g => f g • v) μ :=
    (f.continuous.smul continuous_const).integrable_of_hasCompactSupport
      f.hasCompactSupport.smul_right
  have hv : ∫ g, f g • v ∂μ = v := by
    rw [integral_smul_const]
    simp only [hfg]
    have : ∫ g, (k g : ℂ) ∂μ = ((1 : ℝ) : ℂ) := by
      rw [← hk1]; exact integral_ofReal
    rw [this]
    simp
  have key : π.integrated μ (UnitaryRep.ccToL1 μ f) v - v = ∫ g, f g • (π g v - v) ∂μ := by
    simp only [smul_sub]
    rw [integral_sub hint1 hint2, hv, UnitaryRep.integrated_ccToL1_apply]
  have hbound : ‖∫ g, f g • (π g v - v) ∂μ‖ ≤ ∫ g, k g * r ∂μ := by
    refine norm_integral_le_of_norm_le (hkint.mul_const _) (Filter.Eventually.of_forall fun g => ?_)
    rw [norm_smul, hfg, Complex.norm_real, Real.norm_of_nonneg (hknn g)]
    by_cases hg : g ∈ U
    · exact mul_le_mul_of_nonneg_left (hr g (hUsub hg)) (hknn g)
    · have : k g = 0 := by
        simp only [k]
        rw [h0 hg]
        simp
      rw [this]
      simp
  rw [key]
  rw [integral_mul_const, hk1, one_mul] at hbound
  exact hbound
end

section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.casimir_eq_of_orthonormal_bases :
    ∀ (L : Type) [LieRing L] [LieAlgebra ℝ L] (B : LinearMap.BilinForm ℝ L) (ι ι' : Type) [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] (b : Module.Basis ι ℝ L) (ε : ι → ℝ) (b' : Module.Basis ι' ℝ L) (ε' : ι' → ℝ), (∀ X Y, B X Y = B Y X) → (∀ i, ε i * ε i = 1) → (∀ i j, B (b i) (b j) = if i = j then ε i else 0) → (∀ i, ε' i * ε' i = 1) → (∀ i j, B (b' i) (b' j) = if i = j then ε' i else 0) → casimir b ε = casimir b' ε' := by
  intro L _ _ B ι ι' _ _ _ _ b ε b' ε' hs hε hb hε' hb'
  set u := UniversalEnvelopingAlgebra.ι ℝ (L := L) with hu
  have e1 : ∀ i, u (b i) = ∑ j, (ε' j * B (b' j) (b i)) • u (b' j) := by
    intro i
    conv_lhs => rw [eq_sum_of_orthogonal hε' hb' (b i)]

    simp only [map_sum, map_smul]
  have e2 : ∀ j, u (b' j) = ∑ i, (ε i * B (b i) (b' j)) • u (b i) := by
    intro j
    conv_lhs => rw [eq_sum_of_orthogonal hε hb (b' j)]

    simp only [map_sum, map_smul]
  simp only [casimir]
  calc ∑ i, ε i • (u (b i) * u (b i))
      = ∑ i, ∑ j, (ε i * (ε' j * B (b' j) (b i))) • (u (b i) * u (b' j)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have h : u (b i) * u (b i) = u (b i) * ∑ j, (ε' j * B (b' j) (b i)) • u (b' j) :=
          congrArg (fun x => u (b i) * x) (e1 i)
        rw [h, Finset.mul_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_smul_comm, smul_smul]
    _ = ∑ j, ∑ i, (ε i * (ε' j * B (b' j) (b i))) • (u (b i) * u (b' j)) := Finset.sum_comm
    _ = ∑ j, ε' j • (u (b' j) * u (b' j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have h : u (b' j) * u (b' j) = (∑ i, (ε i * B (b i) (b' j)) • u (b i)) * u (b' j) :=
          congrArg (fun x => x * u (b' j)) (e2 j)
        rw [h, Finset.sum_mul, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_mul_assoc, smul_smul, hs (b' j) (b i)]
        congr 1
        ring
end

section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.norm_exp_smul_sub_le_norm_derivOp :
    ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E) (v : E) (X : 𝔤), (∀ g w, ‖π g w‖ = ‖w‖) → h.IsSmoothVector π v → ‖π (h.expG X) v - v‖ ≤ ‖h.derivOp π X v‖ := by
  intro 𝔸 _ _ _ _ G 𝔤 h E _ _ π v X hπ hv
  have hd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => π (h.expG (s • X)) v)
      (π (h.expG (t • X)) (h.derivOp π X v)) t := by
    intro t
    have h2 := ((π (h.expG (t • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (h.hasDerivAt_derivOp π hv X)
    have h3 : HasDerivAt (fun s : ℝ => π (h.expG ((t + s) • X)) v)
        (π (h.expG (t • X)) (h.derivOp π X v)) (t - t) := by
      rw [sub_self]
      refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars']
      rw [h.expG_add_smul, BanachRep.map_mul_apply]
    have h4 := h3.comp_sub_const t t
    simpa only [add_sub_cancel] using h4
  have hm := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun s : ℝ => π (h.expG (s • X)) v)
    (f' := fun t : ℝ => π (h.expG (t • X)) (h.derivOp π X v)) (C := ‖h.derivOp π X v‖)
    (fun t _ => (hd t).hasDerivWithinAt) (fun t _ => (hπ _ _).le)
  simpa using hm
end

section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C

theorem UpperTheory.norm_trace_comp_le_mul_traceNorm :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ι : Type) (b : HilbertBasis ι ℂ H) (T D : H →L[ℂ] H) (c : ℝ), 0 ≤ c → IsTraceClass T → (∀ i, ∃ d : ℂ, ‖d‖ ≤ c ∧ T (D (b i)) = d • T (b i)) → ‖trace (D ∘L T)‖ ≤ c * (traceNorm T).toReal := by
  intro H _ _ _ ι b T D c hc hT hd
  have hs := hT.summable_norm_inner b
  have h1 := (hT.comp_right D).hasSum_trace b
  rw [trace_comp_comm hT D]
  have h2 : ‖trace (T ∘L D)‖ ≤ ∑' i, c * ‖inner ℂ (b i) (T (b i))‖ :=
    h1.norm_le_of_bounded (hs.mul_left c).hasSum fun i => by
      obtain ⟨d, hd1, hd2⟩ := hd i
      rw [ContinuousLinearMap.comp_apply, hd2, inner_smul_right, norm_mul]
      exact mul_le_mul_of_nonneg_right hd1 (norm_nonneg _)
  have h3 : ∑' i, ‖inner ℂ (b i) (T (b i))‖ ≤ (traceNorm T).toReal := by
    rw [← ENNReal.ofReal_le_iff_le_toReal (show traceNorm T < ⊤ from hT).ne,
      ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hs]
    simp only [ofReal_norm]
    exact tsum_enorm_inner_self_le b T
  rw [tsum_mul_left] at h2
  exact h2.trans (mul_le_mul_of_nonneg_left h3 hc)
end

section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.exists_bound_of_isRoot_exp_mul_forall :
    ∀ (d : ℕ) (p : ℝ → ℂ[X]), (∀ t, p t ≠ 0 ∧ (p t).natDegree ≤ d) → ∃ M : ℝ, ∀ z : ℂ, (∀ t : ℝ, (p t).IsRoot (Complex.exp (z * t))) → ‖z‖ ≤ M := by
  intro d p hp
  classical
  have hfin : Set.Finite {z : ℂ | ∀ t : ℝ, (p t).IsRoot (Complex.exp (z * t))} := by
    by_contra hinf
    obtain ⟨F, hF, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (d + 1)
    obtain ⟨R, hR⟩ := (F.finite_toSet.isBounded).exists_norm_le
    set S : ℝ := |R| + 1 with hS
    have hSpos : 0 < S := by positivity
    have hRS : ∀ z ∈ F, ‖z‖ ≤ S := fun z hz => by
      have h1 := hR z (Finset.mem_coe.mpr hz)
      have h2 := le_abs_self R
      linarith
    set t : ℝ := S⁻¹ with ht
    have htpos : 0 < t := inv_pos.mpr hSpos
    have hn : ∀ z ∈ F, ‖z * (t : ℂ)‖ ≤ 1 := fun z hz => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos, ht]
      rw [mul_inv_le_iff₀ hSpos, one_mul]
      exact hRS z hz
    have hinj : Set.InjOn (fun z : ℂ => Complex.exp (z * (t : ℂ))) F := by
      intro z hz w hw h
      obtain ⟨n, hn'⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
      have h1 := hn z hz
      have h2 := hn w hw
      have h3 : ‖(n : ℂ) * (2 * Real.pi * Complex.I)‖ ≤ 2 := by
        have : (n : ℂ) * (2 * Real.pi * Complex.I) = z * t - w * t := by rw [hn']; ring
        rw [this]
        have := norm_sub_le (z * (t : ℂ)) (w * t)
        linarith
      have hn0 : n = 0 := by
        by_contra hne
        have h4 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hne
        have h5 : ‖(n : ℂ) * (2 * Real.pi * Complex.I)‖ = |(n : ℝ)| * (2 * Real.pi) := by
          simp [abs_of_pos Real.pi_pos]
        have h6 := Real.pi_gt_three
        rw [h5] at h3
        nlinarith
      rw [hn0] at hn'
      have htne : (t : ℂ) ≠ 0 := by exact_mod_cast htpos.ne'
      have : z * (t : ℂ) = w * t := by simpa using hn'
      exact mul_right_cancel₀ htne this
    have hsub : (F.image (fun z : ℂ => Complex.exp (z * (t : ℂ)))).val ⊆ (p t).roots := by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp (Finset.mem_val.mp hx)
      exact (Polynomial.mem_roots (hp t).1).mpr (hF (Finset.mem_coe.mpr hz) t)
    have hle := Polynomial.card_le_degree_of_subset_roots hsub
    rw [Finset.card_image_of_injOn hinj, hcard] at hle
    have := (hp t).2
    omega
  obtain ⟨M, hM⟩ := hfin.isBounded.exists_norm_le
  exact ⟨M, fun z hz => hM z hz⟩
end

section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C

theorem UpperTheory.cfc_apply_of_eigenvector :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →L[ℂ] H), IsSelfAdjoint A → ∀ (φ : ℝ → ℝ), Continuous φ → ∀ (x : ℝ) (v : H), A v = (x : ℂ) • v → (cfc φ A : H →L[ℂ] H) v = (φ x : ℂ) • v := by
  intro H _ _ _ A hA φ hφ x v hv
  by_cases hv0 : v = 0
  · simp [hv0]
  have halg : ∀ r : ℝ, (algebraMap ℝ (H →L[ℂ] H) r) v = (r : ℂ) • v := by
    intro r
    rw [Algebra.algebraMap_eq_smul_one]
    simp
  have hx : x ∈ spectrum ℝ A := by
    rw [spectrum.mem_iff]
    rintro ⟨u, hu⟩
    apply hv0
    have h0 : (u : H →L[ℂ] H) v = 0 := by
      rw [hu, ContinuousLinearMap.sub_apply, halg, hv, sub_self]
    have h1 : ((↑u⁻¹ * ↑u : H →L[ℂ] H)) v = v := by
      rw [Units.inv_mul]; rfl
    rw [← h1, ContinuousLinearMap.mul_apply, h0, map_zero]
  have key : ∀ f : C(spectrum ℝ A, ℝ), (cfcHom hA f : H →L[ℂ] H) v = ((f ⟨x, hx⟩ : ℝ) : ℂ) • v := by
    intro f
    induction f using ContinuousMap.induction_on_of_compact with
    | const r =>
      have : (ContinuousMap.const (spectrum ℝ A) r) = algebraMap ℝ C(spectrum ℝ A, ℝ) r := rfl
      rw [this, AlgHomClass.commutes, halg]
      simp
    | id =>
      rw [cfcHom_id hA, hv]; rfl
    | star_id =>
      rw [star_trivial, cfcHom_id hA, hv]; rfl
    | add f g hf hg =>
      rw [map_add (f := _), ContinuousLinearMap.add_apply, hf, hg]
      simp [add_smul]
    | mul f g hf hg =>
      rw [map_mul, ContinuousLinearMap.mul_apply, hg, map_smul, hf, smul_smul]
      simp [mul_comm]
    | frequently f hf =>
      have hc : IsClosed {g : C(spectrum ℝ A, ℝ) | (cfcHom hA g : H →L[ℂ] H) v = ((g ⟨x, hx⟩ : ℝ) : ℂ) • v} := by
        apply isClosed_eq
        · exact (cfcHom_continuous hA).clm_apply continuous_const
        · exact (Complex.continuous_ofReal.comp (continuous_eval_const _)).smul continuous_const
      exact hc.closure_subset (mem_closure_iff_frequently.mpr hf)
  rw [cfc_apply φ A hA hφ.continuousOn, key]
  rfl
end

section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.re_inner_ge_of_span_eigenvectors :
    ∀ (M H : Type) [AddCommGroup M] [Module ℂ M] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (j : M →ₗ[ℂ] H) (V : Submodule ℂ M) (T : Module.End ℂ M) (c : ℝ) (s : Set M), (∀ x ∈ V, ∀ y ∈ V, inner ℂ (j (T x)) (j y) = inner ℂ (j x) (j (T y))) → (∀ x ∈ s, x ∈ V ∧ ∃ κ : ℂ, -c ≤ κ.re ∧ T x = κ • x) → ∀ v ∈ Submodule.span ℂ s, -c * ‖j v‖ ^ 2 ≤ (inner ℂ (j v) (j (T v))).re := by
  intro M H _ _ _ _ j V T c s hsym hs v hv
  classical
  have hle : Submodule.span ℂ s ≤
      ⨆ κ : {κ : ℂ // -c ≤ κ.re}, (V ⊓ Module.End.eigenspace T (κ : ℂ)) := by
    refine Submodule.span_le.2 fun x hx => ?_
    obtain ⟨hxV, κ, hκ, hT⟩ := hs x hx
    exact Submodule.mem_iSup_of_mem (⟨κ, hκ⟩ : {κ : ℂ // -c ≤ κ.re})
      ⟨hxV, Module.End.mem_eigenspace_iff.2 hT⟩
  obtain ⟨f, hf, hfv⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 (hle hv)
  have hV : ∀ κ, f κ ∈ V := fun κ => (hf κ).1
  have hT : ∀ κ, T (f κ) = (κ : ℂ) • f κ := fun κ => Module.End.mem_eigenspace_iff.1 (hf κ).2
  have hrel : ∀ a b : {κ : ℂ // -c ≤ κ.re}, (starRingEnd ℂ) (a : ℂ) * inner ℂ (j (f a)) (j (f b))
      = (b : ℂ) * inner ℂ (j (f a)) (j (f b)) := by
    intro a b
    have := hsym _ (hV a) _ (hV b)
    rwa [hT, hT, map_smul, map_smul, inner_smul_left, inner_smul_right] at this
  have horth : ∀ a b, a ≠ b → inner ℂ (j (f a)) (j (f b)) = 0 := by
    intro a b hab
    by_cases h0 : j (f a) = 0
    · rw [h0, inner_zero_left]
    · have h1 : (starRingEnd ℂ) (a : ℂ) = a :=
        mul_right_cancel₀ (fun h => h0 (inner_self_eq_zero.1 h)) (hrel a a)
      have h2 := hrel a b
      rw [h1] at h2
      by_contra h3
      exact hab (Subtype.ext (mul_right_cancel₀ h3 h2))
  have hv' : v = ∑ a ∈ f.support, f a := hfv.symm
  have e1 : inner ℂ (j v) (j v) = ∑ a ∈ f.support, inner ℂ (j (f a)) (j (f a)) := by

    rw [hv', map_sum, sum_inner]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [inner_sum, Finset.sum_eq_single_of_mem a ha]
    intro b _ hb
    exact horth a b hb.symm
  have e2 : inner ℂ (j v) (j (T v))
      = ∑ a ∈ f.support, (a : ℂ) * inner ℂ (j (f a)) (j (f a)) := by

    rw [hv', map_sum T, map_sum, map_sum, sum_inner]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [inner_sum, Finset.sum_eq_single_of_mem a ha, hT, map_smul, inner_smul_right]
    intro b _ hb
    rw [hT, map_smul, inner_smul_right, horth a b hb.symm, mul_zero]
  have hn : ∀ x : H, inner ℂ x x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have e3 : ‖j v‖ ^ 2 = ∑ a ∈ f.support, ‖j (f a)‖ ^ 2 := by
    simp only [hn] at e1
    exact_mod_cast e1
  rw [e2, e3, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [hn, Complex.re_mul_ofReal]
  exact mul_le_mul_of_nonneg_right a.2 (sq_nonneg _)
end
