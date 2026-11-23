module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle057
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle169
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle168
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle166
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle093
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib

@[expose] public section

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.SelfDualLat

theorem isLC_indicator_one {X : Type} [TopologicalSpace X] (s : Set X) (h : IsClopen s) :
    IsLocallyConstant (s.indicator (fun _ => (1 : ℂ))) := by
  classical
  intro B
  rw [Set.indicator_preimage, Set.ite]
  refine (IsOpen.inter ?_ h.isOpen).union ?_
  · rw [Set.preimage_const]; split_ifs <;> simp
  · rw [Set.diff_eq]
    refine IsOpen.inter ?_ h.isClosed.isOpen_compl
    change IsOpen ((fun _ : X => (0:ℂ)) ⁻¹' B)
    rw [Set.preimage_const]; split_ifs <;> simp

theorem topo : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V], LocallyCompactSpace V ∧ SecondCountableTopology V ∧ T2Space V ∧ IsTopologicalAddGroup V := by
  intro F E _ _ _ _ _ V _ _ _ _ _
  haveI := (inferInstance : Unram F E).lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd F V
  haveI : ContinuousNeg V := ⟨by
    have := IsModuleTopology.continuous_of_linearMap (R := F) (A := V) (B := V) (-LinearMap.id)
    exact this⟩
  let e : V ≃ₗ[F] (Fin (Module.finrank F V) → F) := (Module.finBasis F V).equivFun
  have hc : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hc' : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let h : V ≃ₜ (Fin (Module.finrank F V) → F) := ⟨e.toEquiv, hc, hc'⟩
  exact ⟨h.isOpenEmbedding.locallyCompactSpace, h.isEmbedding.secondCountableTopology, h.isEmbedding.t2Space,
    IsTopologicalAddGroup.mk⟩
theorem orth : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] [IsTopologicalAddGroup V] (β : LinearMap.BilinForm F V) (μ : Measure V), μ.IsAddHaarMeasure → ∀ M : AddSubgroup V, IsOpen (M : Set V) → IsCompact (M : Set V) → ∀ y, ∫ x in (M : Set V), ψ (β x y) ∂μ = Set.indicator {y | ∀ x ∈ M, ψ (β x y) = 1} (fun _ => ((μ M).toReal : ℂ)) y := by
  intro F E _ _ _ _ _ ψ hψ V _ _ _ _ _ _ _ _ β μ hμ M hMo hMc y
  classical
  by_cases hy : y ∈ {y | ∀ x ∈ M, ψ (β x y) = 1}
  · rw [Set.indicator_of_mem hy, setIntegral_congr_fun hMo.measurableSet (fun x hx => hy x hx)]
    simp [Measure.real]
  · rw [Set.indicator_of_notMem hy]
    simp only [Set.mem_setOf_eq, not_forall] at hy
    obtain ⟨x0, hx0, hne⟩ := hy
    have ht := integral_add_left_eq_self (μ := μ) (fun x => (M : Set V).indicator (fun x => ψ (β x y)) x) x0
    have hpt : ∀ x, (M : Set V).indicator (fun x => ψ (β x y)) (x0 + x) =
        ψ (β x0 y) * (M : Set V).indicator (fun x => ψ (β x y)) x := by
      intro x
      by_cases hx : x ∈ M
      · have : x0 + x ∈ M := M.add_mem hx0 hx
        simp [Set.indicator_of_mem (show x0 + x ∈ (M : Set V) from this),
          Set.indicator_of_mem (show x ∈ (M : Set V) from hx), map_add, AddChar.map_add_eq_mul]
      · have : x0 + x ∉ M := fun h => hx (by simpa using M.sub_mem h hx0)
        simp [Set.indicator_of_notMem (show x0 + x ∉ (M : Set V) from this),
          Set.indicator_of_notMem (show x ∉ (M : Set V) from hx)]
    simp_rw [hpt] at ht
    rw [integral_const_mul, integral_indicator hMo.measurableSet] at ht
    have h0 : (ψ (β x0 y) - 1) * ∫ x in (M : Set V), ψ (β x y) ∂μ = 0 := by rw [sub_mul, one_mul, ht, sub_self]
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · exact h
theorem planch : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [IsTopologicalAddGroup V] (β : LinearMap.BilinForm F V), β.IsSymm → β.Nondegenerate → ∀ μ : Measure V, SelfDual μ (fun x y => ψ (β x y)) → ∀ f, IsTest f → ∫ y, ‖fourB μ (fun x y => ψ (β x y)) f y‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  intro F E _ _ _ _ _ ψ hψ V _ _ _ _ _ _ _ _ _ _ _ β hβs hβn μ hsd f hf
  haveI := hsd.1
  have hψ' := (GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ
  have hI := GlobalTheory.T.selfDual_measure_exists_unique_fourier_inversion F E ψ hψ V β hβs hβn
  set B : V → V → ℂ := fun x y => ψ (β x y) with hB
  set g := fourB μ B f with hgdef
  have hg : IsTest g := hI.2 μ hsd.1 f hf
  have hψc : Continuous (fun t : F => ψ t) := hψ'.1.continuous
  have hβc : Continuous (fun p : V × V => β p.1 p.2) := IsModuleTopology.continuous_bilinear_of_finite_left β
  have hfc : Continuous f := hf.1.continuous
  have hgc : Continuous g := hg.1.continuous
  have hfi : Integrable f μ := hfc.integrable_of_hasCompactSupport hf.2
  have hgi : Integrable g μ := hgc.integrable_of_hasCompactSupport hg.2
  have key : ∀ h : V → ℂ, ((∫ y, ‖h y‖ ^ 2 ∂μ : ℝ) : ℂ) = ∫ y, h y * (starRingEnd ℂ) (h y) ∂μ := by
    intro h
    rw [← integral_complex_ofReal]
    congr 1; ext y
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hconj : ∀ t : F, (starRingEnd ℂ) (ψ t) = ψ (-t) := by
    intro t
    rw [AddChar.map_neg_eq_inv]
    have h1 : ‖ψ t‖ = 1 := hψ'.2.1 t
    have h0 : ψ t ≠ 0 := by intro h; rw [h, norm_zero] at h1; exact zero_ne_one h1
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, h1]; simp
  have hinner : ∀ x, ∫ y, ψ (β x y) * (starRingEnd ℂ) (g y) ∂μ = (starRingEnd ℂ) (f x) := by
    intro x
    have := hsd.2 f hf (-x)
    rw [neg_neg] at this
    rw [← this]
    show _ = (starRingEnd ℂ) (∫ y, g y * B y (-x) ∂μ)
    rw [← integral_conj]
    congr 1; ext y
    rw [map_mul, hconj]
    simp only [map_neg, neg_neg, hβs.eq x y]
    ring
  have hint : Integrable (Function.uncurry fun y x => f x * ψ (β x y) * (starRingEnd ℂ) (g y)) (μ.prod μ) := by
    refine Integrable.mono' ((hgi.norm).mul_prod hfi.norm) ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      exact ((hfc.comp continuous_snd).mul (hψc.comp (hβc.comp continuous_swap))).mul
        (Complex.continuous_conj.comp (hgc.comp continuous_fst))
    · refine Filter.Eventually.of_forall (fun z => ?_)
      simp only [Function.uncurry, norm_mul, hψ'.2.1, mul_one, Complex.norm_conj]
      rw [mul_comm]
  apply Complex.ofReal_injective
  rw [key, key]
  calc ∫ y, g y * (starRingEnd ℂ) (g y) ∂μ
      = ∫ y, ∫ x, f x * ψ (β x y) * (starRingEnd ℂ) (g y) ∂μ ∂μ := by
        congr 1; ext y
        rw [hgdef]; unfold fourB
        rw [← integral_mul_const]
    _ = ∫ x, ∫ y, f x * ψ (β x y) * (starRingEnd ℂ) (g y) ∂μ ∂μ := integral_integral_swap hint
    _ = ∫ x, f x * (starRingEnd ℂ) (f x) ∂μ := by
        congr 1; ext x
        simp_rw [mul_assoc]
        rw [integral_const_mul, hinner]

end GlobalTheory.JR.SelfDualLat

open GlobalTheory.JR.SelfDualLat in
theorem GlobalTheory.JR.selfDual_iff_lattice_volume_and_plancherel : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] (β : LinearMap.BilinForm F V), β.IsSymm → β.Nondegenerate → ∀ μ : Measure V, μ.IsAddHaarMeasure → (∀ M : AddSubgroup V, IsOpen (M : Set V) → IsCompact (M : Set V) → (SelfDual μ (fun x y => ψ (β x y)) ↔ μ M * μ {y | ∀ x ∈ M, ψ (β x y) = 1} = 1) ∧ ∀ y, ∫ x in (M : Set V), ψ (β x y) ∂μ = Set.indicator {y | ∀ x ∈ M, ψ (β x y) = 1} (fun _ => ((μ M).toReal : ℂ)) y) ∧ (SelfDual μ (fun x y => ψ (β x y)) → ∀ f, IsTest f → ∫ y, ‖fourB μ (fun x y => ψ (β x y)) f y‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) := by
  intro F E _ _ _ _ _ ψ hψ V _ _ _ _ _ _ _ β hβs hβn μ hμ
  obtain ⟨hLC, hSC, hT2, hTG⟩ := topo F E V
  haveI := hLC; haveI := hSC; haveI := hT2; haveI := hTG
  have hI := GlobalTheory.T.selfDual_measure_exists_unique_fourier_inversion F E ψ hψ V β hβs hβn
  have fwd : ∀ ν : Measure V, SelfDual ν (fun x y => ψ (β x y)) → ∀ M : AddSubgroup V, IsOpen (M : Set V) →
      IsCompact (M : Set V) → ν M * ν {y | ∀ x ∈ M, ψ (β x y) = 1} = 1 := by
    intro ν hν M hMo hMc
    haveI := hν.1
    set P : Set V := {y | ∀ x ∈ M, ψ (β x y) = 1} with hP
    set g : V → ℂ := (M : Set V).indicator (fun _ => 1) with hg
    have hMcl : IsClosed (M : Set V) := AddSubgroup.isClosed_of_isOpen M hMo
    have hgt : IsTest g := ⟨isLC_indicator_one _ ⟨hMcl, hMo⟩,
      HasCompactSupport.intro hMc (fun x hx => Set.indicator_of_notMem hx _)⟩
    have h1 : ∀ x, fourB ν (fun x y => ψ (β x y)) g x = P.indicator (fun _ => ((ν M).toReal : ℂ)) x := by
      intro x
      rw [← orth F E ψ hψ V β ν hν.1 M hMo hMc x]
      unfold fourB
      rw [← integral_indicator hMo.measurableSet]
      congr 1; ext t
      by_cases ht : t ∈ (M : Set V) <;> simp [hg, ht]
    have hc : ((ν M).toReal : ℂ) ≠ 0 := by
      have h0 : ν M ≠ 0 := (hMo.measure_pos ν ⟨0, M.zero_mem⟩).ne'
      have ht : ν M ≠ ⊤ := hMc.measure_lt_top.ne
      exact_mod_cast (ENNReal.toReal_pos h0 ht).ne'
    have hft := hI.2 ν hν.1 g hgt
    have hPm : MeasurableSet P := by
      have : P = (fourB ν (fun x y => ψ (β x y)) g) ⁻¹' {((ν M).toReal : ℂ)} := by
        ext y
        show y ∈ P ↔ fourB ν (fun x y => ψ (β x y)) g y = ((ν M).toReal : ℂ)
        rw [h1]
        by_cases hy : y ∈ P
        · simp [Set.indicator_of_mem hy, hy]
        · rw [Set.indicator_of_notMem hy]; exact ⟨fun h => absurd h hy, fun h => absurd h.symm hc⟩
      rw [this]; exact (hft.1.isOpen_fiber _).measurableSet
    have h2 := hν.2 g hgt 0
    rw [neg_zero, show g 0 = 1 by simp [hg, M.zero_mem]] at h2
    have h3 : fourB ν (fun x y => ψ (β x y)) (fourB ν (fun x y => ψ (β x y)) g) 0 =
        (ν P).toReal * (ν M).toReal := by
      show ∫ x, fourB ν (fun x y => ψ (β x y)) g x * ψ (β x 0) ∂ν = _
      simp_rw [h1, map_zero, AddChar.map_zero_eq_one, mul_one]
      rw [integral_indicator_const _ hPm]
      simp [Measure.real]
    rw [h3] at h2
    rw [← ENNReal.toReal_eq_one_iff, ENNReal.toReal_mul]
    have h4 : (((ν M).toReal * (ν P).toReal : ℝ) : ℂ) = 1 := by push_cast; linear_combination h2
    exact_mod_cast h4
  refine ⟨fun M hMo hMc => ⟨⟨fun hsd => fwd μ hsd M hMo hMc, fun h => ?_⟩, orth F E ψ hψ V β μ hμ M hMo hMc⟩,
    fun hsd f hf => planch F E ψ hψ V β hβs hβn μ hsd f hf⟩
  obtain ⟨⟨μ0, hμ0, -⟩, -⟩ := hI
  haveI := hμ0.1
  have hsc : μ = Measure.addHaarScalarFactor μ μ0 • μ0 := Measure.isAddLeftInvariant_eq_smul μ μ0
  set c := Measure.addHaarScalarFactor μ μ0 with hcdef
  have h0 := fwd μ0 hμ0 M hMo hMc
  rw [hsc] at h
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
  have hcc : ((c * c : NNReal) : ENNReal) = 1 := by
    calc ((c * c : NNReal) : ENNReal) = (c : ENNReal) * c * (μ0 M * μ0 {y | ∀ x ∈ M, ψ (β x y) = 1}) := by
          rw [h0, mul_one, ENNReal.coe_mul]
      _ = (c : ENNReal) * μ0 M * ((c : ENNReal) * μ0 {y | ∀ x ∈ M, ψ (β x y) = 1}) := by ring
      _ = 1 := h
  have hcc' : (c : ℝ) * c = 1 := by exact_mod_cast (ENNReal.coe_eq_one.1 hcc)
  have hc1 : c = 1 := by
    have : (c : ℝ) = 1 := by nlinarith [c.2]
    exact_mod_cast this
  have : μ = μ0 := by rw [hsc, hc1, one_smul]
  rw [this]; exact hμ0
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem dual_cinvOK_small : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ V ∈ 𝓝 (0 : A.K),
    ∀ᶠ c in 𝓝[≠] (0 : F), {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1} ⊆ V := by
  intro F E _ _ _ _ _ A ψ hψ V hV
  classical
  haveI : ContinuousSMul F A.K := IsModuleTopology.toContinuousSMul F A.K
  obtain ⟨-, -, hnd, -, -, -, -, -, -, hOpen, -, R, hR⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  have h0 : (0 : A.K) ∈ A.OK := by rw [← hR]; exact R.zero_mem
  let b := Module.finBasis F A.K
  let d := (Algebra.traceForm F A.K).dualBasis hnd b

  have hU : (⋂ i, {t : F | t • b i ∈ A.OK}) ∈ 𝓝 (0 : F) := by
    refine Filter.iInter_mem.2 fun i => ?_
    have hc : Continuous fun t : F => t • b i := continuous_id.smul continuous_const
    have : A.OK ∈ 𝓝 ((fun t : F => t • b i) 0) := by simpa using hOpen.mem_nhds h0
    exact hc.continuousAt this
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨x₀, hx₀, -⟩ := hψ.2
  have hx₀0 : x₀ ≠ 0 := by rintro rfl; exact hx₀ (AddChar.map_zero_eq_one ψ)

  have key : ∀ t : F, (∀ l : F, ‖l‖ < ε → ψ (l * t) = 1) → ‖t‖ ≤ ‖x₀‖ / ε := by
    intro t ht
    by_contra hlt
    push_neg at hlt
    have ht0 : t ≠ 0 := by
      rintro rfl; simp at hlt; linarith [div_pos (norm_pos_iff.2 hx₀0) hε]
    have hn : ‖x₀ / t‖ < ε := by
      rw [norm_div, div_lt_iff₀ (norm_pos_iff.2 ht0)]
      rw [div_lt_iff₀ hε] at hlt; linarith
    apply hx₀
    have := ht (x₀ / t) hn
    rwa [div_mul_cancel₀ x₀ ht0] at this
  set Rr := ‖x₀‖ / ε with hRr
  have hRr0 : 0 ≤ Rr := div_nonneg (norm_nonneg _) hε.le

  let g : (Fin (Module.finrank F A.K) → F) → A.K := fun t => ∑ i, t i • d i
  have hg : Continuous g := continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const
  have hg0 : g 0 = 0 := by simp [g]
  have hgV : g ⁻¹' V ∈ 𝓝 (0 : Fin (Module.finrank F A.K) → F) := by
    rw [← hg0] at hV; exact hg.continuousAt hV
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.1 hgV
  have hev : ∀ᶠ c in 𝓝 (0 : F), ‖c‖ * Rr < δ := by
    have : Tendsto (fun c : F => ‖c‖ * Rr) (𝓝 0) (𝓝 (‖(0:F)‖ * Rr)) :=
      (continuous_norm.mul continuous_const).tendsto 0
    simp only [norm_zero, zero_mul] at this
    exact this.eventually (gt_mem_nhds hδ)
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with c hc hc0
  intro y hy
  have hc0' : c ≠ 0 := hc0
  have hbound : ∀ i, ‖Algebra.trace F A.K (y * b i)‖ ≤ ‖c‖ * Rr := by
    intro i
    have h1 : ‖c⁻¹ * Algebra.trace F A.K (b i * y)‖ ≤ Rr := by
      apply key
      intro l hl
      have hmem : c • ((l * c⁻¹) • b i) ∈ A.OK := by
        rw [smul_smul, mul_comm l, ← mul_assoc, mul_inv_cancel₀ hc0', one_mul]
        have : l ∈ Metric.ball (0:F) ε := by simpa using hl
        simpa using Set.mem_iInter.1 (hεU this) i
      have := hy _ hmem
      simp only [Et.psiK, smul_mul_assoc, map_smul, smul_eq_mul] at this
      rw [← this]; congr 1; ring
    rw [norm_mul, norm_inv, inv_mul_le_iff₀ (norm_pos_iff.2 hc0')] at h1
    rwa [mul_comm y]
  have hy' : y = g (fun i => Algebra.trace F A.K (y * b i)) := by
    simp only [g]
    conv_lhs => rw [← d.sum_repr y]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply]
    rfl
  rw [hy']
  apply hδV
  rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff hδ]
  intro i
  exact lt_of_le_of_lt (hbound i) hc

end GlobalTheory
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

open scoped Pointwise NNReal ENNReal

namespace GlobalTheory.JR.Et
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] (A : Et F E)

theorem secondCountable_K : SecondCountableTopology A.K := by
  haveI : LocallyCompactSpace F := Unram.lcF (E := E)
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  let e : A.K ≃ₗ[F] (Fin (Module.finrank F A.K) → F) := (Module.finBasis F A.K).equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let h : A.K ≃ₜ (Fin (Module.finrank F A.K) → F) := ⟨e.toEquiv, h1, h2⟩
  exact h.isEmbedding.secondCountableTopology

theorem absK_unit (x : A.Kˣ) : A.absK (x : A.K) = (distribHaarChar A.K x : ℝ) := by
  unfold absK
  rw [dite_eq_left x.isUnit]
  congr 2
  ext; rfl

theorem absK_mul (s t : A.K) : A.absK (s * t) = A.absK s * A.absK t := by
  by_cases hs : IsUnit s
  · by_cases ht : IsUnit t
    · have e1 := A.absK_unit (hs.unit * ht.unit)
      have e2 := A.absK_unit hs.unit
      have e3 := A.absK_unit ht.unit
      simp only [Units.val_mul, IsUnit.unit_spec] at e1 e2 e3
      rw [e1, e2, e3, map_mul, NNReal.coe_mul]
    · have : ¬ IsUnit (s * t) := fun h => ht (IsUnit.mul_iff.1 h).2
      simp [absK, this, ht]
  · have : ¬ IsUnit (s * t) := fun h => hs (IsUnit.mul_iff.1 h).1
    simp [absK, this, hs]

theorem distribHaarChar_le_one_of_mem_OK (u : A.Kˣ) (hu : (u : A.K) ∈ A.OK) : distribHaarChar A.K u ≤ 1 := by
  haveI := A.secondCountable_K
  obtain ⟨-, -, -, -, -, -, -, -, -, hO, hC, R, hR⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  let μ : Measure A.K := Measure.addHaar
  have h0 : (0 : A.K) ∈ A.OK := by rw [← hR]; exact R.zero_mem
  have hm0 : μ A.OK ≠ 0 := hO.measure_ne_zero μ ⟨0, h0⟩
  have hmt : μ A.OK ≠ ⊤ := hC.measure_lt_top.ne
  have hsub : u • A.OK ⊆ A.OK := by
    rintro _ ⟨z, hz, rfl⟩
    rw [← hR] at hz hu ⊢
    exact R.mul_mem hu hz
  have hle : (distribHaarChar A.K u : ℝ≥0∞) * μ A.OK ≤ 1 * μ A.OK := by
    rw [distribHaarChar_mul μ u A.OK, one_mul]; exact measure_mono hsub
  have := (ENNReal.mul_le_mul_iff_left hm0 hmt).1 hle
  exact_mod_cast this

theorem absK_facts : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), ((∀ s t : A.K, A.absK (s * t) = A.absK s * A.absK t) ∧ (∀ s s' : A.K, s ∈ A.OK → s' ∈ A.OK → s * s' = 1 → A.absK s = 1) ∧ (∀ (μ : Measure A.K), μ.IsAddHaarMeasure → ∀ (x : A.Kˣ) (a : A.K) (S : Set A.K), MeasurableSet S → μ {a' : A.K | (x : A.K) * a' - a ∈ S} = ENNReal.ofReal (A.absK (x : A.K))⁻¹ * μ S)) := by
  intro F E _ _ _ _ _ A
  refine ⟨A.absK_mul, ?_, ?_⟩
  · intro s s' hs hs' h
    let u : A.Kˣ := ⟨s, s', h, by rw [mul_comm]; exact h⟩
    have h1 := A.distribHaarChar_le_one_of_mem_OK u hs
    have h2 := A.distribHaarChar_le_one_of_mem_OK u⁻¹ hs'
    have hprod : distribHaarChar A.K u * distribHaarChar A.K u⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    have : distribHaarChar A.K u = 1 := by
      refine le_antisymm h1 ?_
      calc (1 : ℝ≥0) = distribHaarChar A.K u * distribHaarChar A.K u⁻¹ := hprod.symm
        _ ≤ distribHaarChar A.K u * 1 := mul_le_mul_of_nonneg_left h2 zero_le'
        _ = distribHaarChar A.K u := mul_one _
    have e := A.absK_unit u
    change A.absK s = 1
    rw [show s = (u : A.K) from rfl, e, this, NNReal.coe_one]
  · intro μ hμ x a S _
    haveI := A.secondCountable_K
    have hset : {a' : A.K | (x : A.K) * a' - a ∈ S} = x⁻¹ • ((fun z => z + -a) ⁻¹' S) := by
      ext a'
      rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
      simp [Units.smul_def, sub_eq_add_neg]
    rw [hset, ← distribHaarChar_mul μ x⁻¹, measure_preimage_add_right, A.absK_unit, map_inv,
      ← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal]

end GlobalTheory.JR.Et
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.TildeTest

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ φ' : A.K × A.K → ℂ, IsTest φ' → IsTest (fun p : A.K × A.K => A.tilde μK ψ φ' p.1 p.2) := by
  intro F E _ _ _ _ _ A ψ hψ μK hμ φ' hφ
  set T : A.K → A.K → ℂ := fun c u => A.tilde μK ψ φ' c u with hTdef
  have hslice : ∀ c, IsTest (fun u => T c u) := by
    intro c
    have hnd := (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.2.1
    have h := (GlobalTheory.T.selfDual_measure_exists_unique_fourier_inversion F E ψ hψ A.K (Algebra.traceForm F A.K) (Algebra.traceForm_isSymm F) hnd).2 μK hμ
      (fun b => φ' (b, c)) (GlobalTheory.TestFn.slice_test φ' hφ c)
    have heq : (fun u => T c u) = fourB μK (fun x y => ψ ((Algebra.traceForm F A.K) x y)) (fun b => φ' (b, c)) := by
      funext u
      simp [hTdef, Et.tilde, fourB, Et.psiK, Algebra.traceForm_apply, mul_comm]
    rw [heq]
    exact h
  obtain ⟨V, hV, hVf⟩ := GlobalTheory.TestFn.unif_const (A.K × A.K) φ' hφ
  set V₂ : Set A.K := {v | ((0 : A.K), v) ∈ V} with hV₂def
  have hV₂ : V₂ ∈ 𝓝 (0 : A.K) := by
    have hc : Continuous (fun v : A.K => ((0 : A.K), v)) := by fun_prop
    exact hc.continuousAt.preimage_mem_nhds (by rw [show ((0 : A.K), (0 : A.K)) = (0 : A.K × A.K) from rfl]; exact hV)
  have hshift : ∀ c c', c' - c ∈ V₂ → ∀ u, T c' u = T c u := by
    intro c c' hcc u
    simp only [hTdef, Et.tilde]
    congr 1; funext b
    have := hVf (b, c) (0, c' - c) hcc
    simp only [Prod.mk_add_mk, add_zero, add_sub_cancel] at this
    rw [this]
  have hnbhd : ∀ c : A.K, {c' | c' - c ∈ V₂} ∈ 𝓝 c := by
    intro c
    have hc : Continuous (fun c' : A.K => c' - c) := by fun_prop
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hV₂)
  have hlc : IsLocallyConstant (fun p : A.K × A.K => T p.1 p.2) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨c₀, u₀⟩
    have hu : {u | T c₀ u = T c₀ u₀} ∈ 𝓝 u₀ := ((hslice c₀).1.isOpen_fiber _).mem_nhds rfl
    rw [nhds_prod_eq]
    filter_upwards [prod_mem_prod (hnbhd c₀) hu] with p hp
    rw [hshift c₀ p.1 hp.1 p.2]; exact hp.2
  refine ⟨hlc, ?_⟩
  have hC₂ : IsCompact (Prod.snd '' tsupport φ') := hφ.2.image continuous_snd
  obtain ⟨t, -, hcover⟩ := hC₂.elim_nhds_subcover (fun c => {c' | c' - c ∈ V₂}) (fun c _ => hnbhd c)
  have hK : IsCompact ((Prod.snd '' tsupport φ') ×ˢ ⋃ c ∈ t, tsupport (fun u => T c u)) :=
    hC₂.prod (t.isCompact_biUnion fun c _ => (hslice c).2)
  have hzero : ∀ c ∉ Prod.snd '' tsupport φ', ∀ u, T c u = 0 := by
    intro c hc u
    have h0 : ∀ b, φ' (b, c) = 0 := fun b => image_eq_zero_of_notMem_tsupport (fun h => hc ⟨(b, c), h, rfl⟩)
    simp [hTdef, Et.tilde, h0]
  have hsupp : Function.support (fun p : A.K × A.K => T p.1 p.2) ⊆
      (Prod.snd '' tsupport φ') ×ˢ ⋃ c ∈ t, tsupport (fun u => T c u) := by
    rintro ⟨c, u⟩ hp
    have hc : c ∈ Prod.snd '' tsupport φ' := by
      by_contra hc; exact hp (hzero c hc u)
    refine ⟨hc, ?_⟩
    obtain ⟨c', hc't, hcc'⟩ := Set.mem_iUnion₂.mp (hcover hc)
    refine Set.mem_iUnion₂.mpr ⟨c', hc't, subset_tsupport _ ?_⟩
    show T c' u ≠ 0
    rw [← hshift c' c hcc' u]; exact hp
  have hclosed : IsClosed (Function.support (fun p : A.K × A.K => T p.1 p.2)) := by
    have := (hlc.isOpen_fiber 0).isClosed_compl
    convert this using 1
    ext p; simp [Function.mem_support]
  have hts : tsupport (fun p : A.K × A.K => T p.1 p.2) = Function.support (fun p : A.K × A.K => T p.1 p.2) :=
    hclosed.closure_eq
  unfold HasCompactSupport
  rw [hts]
  exact hK.of_isClosed_subset hclosed hsupp

end GlobalTheory.JR.TildeTest
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.glOrbitalIntegral_unit_liftLastBasis_reduce : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas (r + 1) F E) (M' : Meas r F E) (Z : Gl r F) (μ l : F), ‖μ‖ = 1 → Delta (inv (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 → orbG M (unitG (r + 1) F) (GlobalTheory.JR.Step.lift Z μ l) = (if ‖l‖ ≤ 1 then 1 else 0) * orbG M' (unitG r F) Z := by
  first | exact @GlobalTheory.JR.GLift.orbG_lift | exact GlobalTheory.JR.GLift.orbG_lift | (intros; apply GlobalTheory.JR.GLift.orbG_lift <;> assumption)
end
