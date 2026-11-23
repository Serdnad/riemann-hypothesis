module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1384
public import Mathlib.Basic.Complex.Basic
public import GroundTheory.AutomorphicForms.StrongApproximationSLDense
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAutomorphicFormIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle867
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermSliceCuspForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle917
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1363
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1364
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical

noncomputable section

namespace GlobalTheory.EvAdm.CosetSum

variable {F : Type} [Field F] [NumberField F]

theorem finAdele_algebraMap_apply (x : F) (v : HeightOneSpectrum (𝓞 F)) :
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) x) v = algebraMap F (v.adicCompletion F) x := rfl

theorem algebraMap_mem_iff (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    algebraMap F (v.adicCompletion F) x ∈ v.adicCompletionIntegers F ↔ v.valuation F x ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact iff_of_eq (congrArg (· ≤ 1) (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x))

theorem int_mem (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F) :
    algebraMap F (v.adicCompletion F) (x : F) ∈ v.adicCompletionIntegers F := by
  rw [algebraMap_mem_iff]
  exact v.valuation_le_one x

variable {κ : Type}

theorem mul_int_mem {b : F} (hb : b ≠ 0) (x : κ → 𝓞 F) :
    (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (b * (x i : F))) ∈ scaledInt F κ b := by
  rw [mem_scaledInt]
  intro i v
  rw [finAdele_algebraMap_apply, map_mul, ← mul_assoc,
    inv_mul_cancel₀ ((map_ne_zero (algebraMap F (v.adicCompletion F))).2 hb), one_mul]
  exact int_mem v (x i)

theorem scaledInt_mul_le {a : F} (ha : a ≠ 0) {m : 𝓞 F} (hm : m ≠ 0) :
    scaledInt F κ (a * m) ≤ scaledInt F κ a := by
  intro z hz
  rw [mem_scaledInt] at hz ⊢
  intro i v
  have hm' : algebraMap F (v.adicCompletion F) (m : F) ≠ 0 :=
    (map_ne_zero _).2 (by exact_mod_cast hm)
  have e : (algebraMap F (v.adicCompletion F) a)⁻¹ * (z i) v =
      algebraMap F (v.adicCompletion F) (m : F) *
        ((algebraMap F (v.adicCompletion F) (a * m))⁻¹ * (z i) v) := by
    set A := algebraMap F (v.adicCompletion F) a
    set M := algebraMap F (v.adicCompletion F) (m : F)
    rw [map_mul, mul_inv, ← mul_assoc, ← mul_assoc, mul_comm M A⁻¹, mul_assoc A⁻¹ M M⁻¹,
      mul_inv_cancel₀ hm', mul_one]
  rw [e]
  exact mul_mem (int_mem v m) (hz i v)

theorem rat_mem {b : F} (hb : b ≠ 0) (ξ : κ → F)
    (h : (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ scaledInt F κ b) (i : κ) :
    ∃ x : 𝓞 F, (x : F) = ξ i / b := by
  rw [mem_scaledInt] at h
  have hv : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (ξ i / b) ≤ 1 := fun v => by
    rw [← algebraMap_mem_iff, div_eq_inv_mul, map_mul, map_inv₀]
    exact h i v
  obtain ⟨x, hx⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F (ξ i / b) hv
  exact ⟨x, hx⟩

theorem indicator_scaledInt_eq_sum : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ m : 𝓞 F, m ≠ 0 →
    ∃ R : Finset (κ → F), (GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator (fun _ => (1 : ℂ)) =
      ∑ ξ ∈ R, {y | y - (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ (a * m)}.indicator
        (fun _ => (1 : ℂ)) := by
  intro F _ _ κ _ a ha m hm
  set I : Ideal (𝓞 F) := Ideal.span {m} with hIdef
  have hI : I ≠ ⊥ := by
    rw [hIdef, Ne, Ideal.span_singleton_eq_bot]; exact hm
  haveI : Finite (𝓞 F ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  haveI : Fintype (κ → 𝓞 F ⧸ I) := Fintype.ofFinite _
  let out : 𝓞 F ⧸ I → 𝓞 F := fun q => (Ideal.Quotient.mk_surjective q).choose
  have hout : ∀ q, Ideal.Quotient.mk I (out q) = q := fun q => (Ideal.Quotient.mk_surjective q).choose_spec
  let rep : (κ → 𝓞 F ⧸ I) → (κ → F) := fun c i => a * ((out (c i) : 𝓞 F) : F)
  let ι : (κ → F) → (κ → FiniteAdeleRing (𝓞 F) F) := fun ξ i => algebraMap F _ (ξ i)
  have hrep_inj : Function.Injective rep := by
    intro c c' h
    funext i
    have h1 := congrFun h i
    simp only [rep, mul_right_inj' ha] at h1
    have h2 : out (c i) = out (c' i) := by exact_mod_cast h1
    rw [← hout (c i), ← hout (c' i), h2]
  have hrepS : ∀ c, ι (rep c) ∈ scaledInt F κ a := fun c => mul_int_mem ha (fun i => out (c i))
  have hsub := scaledInt_mul_le (κ := κ) ha hm
  have hm0 : (m : F) ≠ 0 := by exact_mod_cast hm
  have ham : a * (m : F) ≠ 0 := mul_ne_zero ha hm0
  have huniq : ∀ c c' (y : κ → FiniteAdeleRing (𝓞 F) F), y - ι (rep c) ∈ scaledInt F κ (a * m) →
      y - ι (rep c') ∈ scaledInt F κ (a * m) → c = c' := by
    intro c c' y h h'
    have hd : ι (fun i => rep c' i - rep c i) ∈ scaledInt F κ (a * m) := by
      have := sub_mem h h'
      convert this using 1
      funext i
      simp only [ι, Pi.sub_apply, map_sub]
      abel
    funext i
    obtain ⟨z, hz⟩ := rat_mem ham _ hd i
    have h3 : ((out (c' i) - out (c i) : 𝓞 F) : F) = ((z * m : 𝓞 F) : F) := by
      have hz' : (z : F) * (a * m) = rep c' i - rep c i := by rw [hz, div_mul_cancel₀ _ ham]
      simp only [rep] at hz'
      push_cast
      apply mul_left_cancel₀ ha
      linear_combination (-1 : F) * hz'
    have h4 : out (c' i) - out (c i) ∈ I := by
      rw [hIdef, Ideal.mem_span_singleton']
      exact ⟨z, by exact_mod_cast h3.symm⟩
    have h5 := (Ideal.Quotient.eq).2 h4
    rw [hout, hout] at h5
    exact h5.symm
  have hexist : ∀ y ∈ scaledInt F κ a, ∃ c, y - ι (rep c) ∈ scaledInt F κ (a * m) := by
    intro y hy
    have hd : DenseRange ι :=
      DenseRange.piMap (fun _ => GroundTheory.Automorphic.AdelicGLn.denseRange_algebraMap_finiteAdeleRing F)
    have hopen : IsOpen {z | y - z ∈ (scaledInt F κ (a * m) : Set (κ → FiniteAdeleRing (𝓞 F) F))} :=
      (isOpen_scaledInt (a * m)).preimage (continuous_const.sub continuous_id)
    obtain ⟨ξ, hξ⟩ := hd.exists_mem_open hopen ⟨y, by simp [zero_mem]⟩
    have hξ' : y - ι ξ ∈ scaledInt F κ (a * m) := hξ
    have hξa : ι ξ ∈ scaledInt F κ a := by
      have := sub_mem hy (hsub hξ')
      simpa using this
    choose x hx using fun i => rat_mem ha ξ hξa i
    have ht : ∀ i, ∃ t : 𝓞 F, t * m = out (Ideal.Quotient.mk I (x i)) - x i := fun i => by
      have := (Ideal.Quotient.eq).1 (hout (Ideal.Quotient.mk I (x i)))
      exact Ideal.mem_span_singleton'.1 this
    choose t htm using ht
    refine ⟨fun i => Ideal.Quotient.mk I (x i), ?_⟩
    have hF : ∀ i, rep (fun i => Ideal.Quotient.mk I (x i)) i = ξ i + a * m * (t i : F) := fun i => by
      have e1 : ((t i * m : 𝓞 F) : F) = ((out (Ideal.Quotient.mk I (x i)) - x i : 𝓞 F) : F) := by rw [htm i]
      push_cast at e1
      have e2 : ξ i = a * (x i : F) := by rw [hx i]; field_simp
      simp only [rep]
      rw [e2]
      linear_combination (-a) * e1
    have hw : ι (fun i => a * m * (t i : F)) ∈ scaledInt F κ (a * m) := mul_int_mem ham t
    have e : y - ι (rep (fun i => Ideal.Quotient.mk I (x i))) = (y - ι ξ) - ι (fun i => a * m * (t i : F)) := by
      funext i
      simp only [ι, Pi.sub_apply]
      rw [hF i, map_add (f := _)]
      abel
    rw [e]
    exact sub_mem hξ' hw
  refine ⟨Finset.univ.image rep, ?_⟩
  rw [Finset.sum_image (fun c _ c' _ h => hrep_inj h)]
  funext y
  rw [Finset.sum_apply]
  by_cases hy : y ∈ scaledInt F κ a
  · obtain ⟨c0, hc0⟩ := hexist y hy
    rw [Set.indicator_of_mem (by exact hy), Finset.sum_eq_single c0]
    · rw [Set.indicator_of_mem (by exact hc0)]
    · intro c _ hc
      rw [Set.indicator_of_notMem]
      intro h
      exact hc (huniq c c0 y h hc0)
    · intro h
      exact absurd (Finset.mem_univ c0) h
  · rw [Set.indicator_of_notMem (by exact hy)]
    symm
    apply Finset.sum_eq_zero
    intro c _
    rw [Set.indicator_of_notMem]
    intro h
    apply hy
    rw [show y = (y - ι (rep c)) + ι (rep c) from (sub_add_cancel _ _).symm]
    exact add_mem (hsub h) (hrepS c)

end GlobalTheory.EvAdm.CosetSum
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.EvAdm

noncomputable section

namespace GlobalTheory.EvAdm

theorem norm_natCast_lt_one_of_dvd (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (c : ℕ) (hc : Ideal.absNorm v.asIdeal ∣ c) :
    ‖(c : v.adicCompletion F)‖ < 1 := by
  have hmem : (c : 𝓞 F) ∈ v.asIdeal := by
    obtain ⟨k, hk⟩ := hc
    rw [hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
  have hval := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v (c : 𝓞 F)).2 hmem
  rw [Valued.toNormedField.norm_lt_one_iff]
  have e : (c : v.adicCompletion F) = (((algebraMap (𝓞 F) F (c : 𝓞 F)) : F) : v.adicCompletion F) := by
    rw [map_natCast]
    rw [show (((c : F)) : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (c : F) from rfl,
      map_natCast]
  rw [e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact hval

theorem exists_nat_scaled_subset (F : Type) [Field F] [NumberField F]
    (U : Set (FiniteAdeleRing (𝓞 F) F)) (hU : U ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F)) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ m : ℕ, m ≠ 0 → N ∣ m → ∀ x : FiniteAdeleRing (𝓞 F) F,
      (∀ v : HeightOneSpectrum (𝓞 F),
        (algebraMap F (v.adicCompletion F) (m : F))⁻¹ * x v ∈ v.adicCompletionIntegers F) → x ∈ U := by
  classical
  have hAopen : ∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun _ => Valued.isOpen_valuationSubring _
  have hU' : U ∈ Filter.map (RestrictedProduct.structureMap
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite)
      (𝓝 (fun v => ⟨0, zero_mem (v.adicCompletionIntegers F)⟩)) := by
    rw [← RestrictedProduct.nhds_eq_map_structureMap hAopen]
    exact hU
  have hU2 : (RestrictedProduct.structureMap
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite) ⁻¹'
      (U : Set (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
        (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite)) ∈
      𝓝 (fun v : HeightOneSpectrum (𝓞 F) => (⟨0, zero_mem (v.adicCompletionIntegers F)⟩ :
        (v.adicCompletionIntegers F : Set (v.adicCompletion F)))) := hU'
  rw [nhds_pi, Filter.mem_pi] at hU2
  obtain ⟨I, hI, t, ht, hIt⟩ := hU2
  have hε : ∀ v : HeightOneSpectrum (𝓞 F), ∃ ε > (0 : ℝ),
      ∀ y : (v.adicCompletionIntegers F : Set (v.adicCompletion F)),
        ‖(y : v.adicCompletion F)‖ < ε → y ∈ t v := by
    intro v
    obtain ⟨u, hu, hut⟩ := (mem_nhds_subtype _ _ _).1 (ht v)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hu
    refine ⟨ε, hε, fun y hy => hut (hball ?_)⟩
    simpa [Metric.mem_ball, dist_zero_right] using hy
  choose ε hεpos hεt using hε
  set c : ℕ := ∏ v ∈ hI.toFinset, Ideal.absNorm v.asIdeal with hcdef
  have hc0 : c ≠ 0 := by
    rw [hcdef, Finset.prod_ne_zero_iff]
    intro v _
    exact (lt_trans zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm v)).ne'
  have hcv : ∀ v ∈ I, ‖(c : v.adicCompletion F)‖ < 1 := fun v hv =>
    norm_natCast_lt_one_of_dvd F v c (Finset.dvd_prod_of_mem _ (hI.mem_toFinset.2 hv))
  have hev : ∀ v ∈ I, ∀ᶠ k in atTop, ‖(c : v.adicCompletion F)‖ ^ k < ε v := fun v hv =>
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (hcv v hv)).eventually
      (Iio_mem_nhds (hεpos v))
  obtain ⟨k, hk⟩ := ((Filter.eventually_all_finite hI).2 hev).exists
  refine ⟨c ^ k, pow_ne_zero _ hc0, fun m hm hdvd x hx => ?_⟩
  obtain ⟨d, hd⟩ := hdvd
  have hmv : ∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (v.adicCompletion F) (m : F) = (m : v.adicCompletion F) :=
    fun v => map_natCast _ m
  have hm0 : ∀ v : HeightOneSpectrum (𝓞 F), (m : v.adicCompletion F) ≠ 0 :=
    fun v => by rw [← hmv]; exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hm)
  have hxv : ∀ v : HeightOneSpectrum (𝓞 F),
      x v = (m : v.adicCompletion F) * ((m : v.adicCompletion F)⁻¹ * x v) := by
    intro v
    rw [← mul_assoc, mul_inv_cancel₀ (hm0 v), one_mul]
  have hmem : ∀ v : HeightOneSpectrum (𝓞 F), x v ∈
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    intro v
    have h1 := hx v
    rw [hmv] at h1
    rw [hxv v]
    exact mul_mem (natCast_mem _ _) h1
  have hxe : x = RestrictedProduct.structureMap
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite
      (fun v => ⟨_, hmem v⟩) := by
    ext v
    rfl
  rw [hxe]
  apply hIt
  intro v hv
  apply hεt
  show ‖x v‖ < ε v
  have h1 := hx v
  rw [hmv] at h1
  have hz1 : ‖(m : v.adicCompletion F)⁻¹ * x v‖ ≤ 1 := by
    rw [Valued.toNormedField.norm_le_one_iff]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h1
  have hd1 : ‖(d : v.adicCompletion F)‖ ≤ 1 := by
    rw [Valued.toNormedField.norm_le_one_iff]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (natCast_mem _ _)
  have hnm : ‖(m : v.adicCompletion F)‖ ≤ ‖(c : v.adicCompletion F)‖ ^ k := by
    rw [hd, Nat.cast_mul, norm_mul, Nat.cast_pow, norm_pow]
    calc ‖(c : v.adicCompletion F)‖ ^ k * ‖(d : v.adicCompletion F)‖
        ≤ ‖(c : v.adicCompletion F)‖ ^ k * 1 := by gcongr
      _ = _ := mul_one _
  rw [hxv v, norm_mul]
  calc ‖(m : v.adicCompletion F)‖ * ‖(m : v.adicCompletion F)⁻¹ * x v‖
      ≤ ‖(c : v.adicCompletion F)‖ ^ k * 1 := by gcongr
    _ < ε v := by rw [mul_one]; exact hk v hv

end GlobalTheory.EvAdm

namespace GlobalTheory.EvAdm

theorem exists_scaledInt_subset_of_mem_nhds : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (W : Set (κ → FiniteAdeleRing (𝓞 F) F)),
    W ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) → ∃ a : F, a ≠ 0 ∧
      (scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)) ⊆ W := by
  intro F _ _ κ _ W hW
  classical
  rw [nhds_pi, Filter.mem_pi] at hW
  obtain ⟨I, _, t, ht, hIt⟩ := hW
  have ht' : ∀ i, t i ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) := fun i => ht i
  choose N hN0 hN using fun i => exists_nat_scaled_subset F (t i) (ht' i)
  have hP : (∏ i, N i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hN0 i
  refine ⟨((∏ i, N i : ℕ) : F), Nat.cast_ne_zero.2 hP, fun z hz => hIt ?_⟩
  intro i _
  exact hN i _ hP (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) (z i) (fun v => hz i v)

end GlobalTheory.EvAdm
end
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump Metric Set
open scoped ContDiff

namespace GlobalTheory.WhitBump

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem contDiff_nu_apply (i k : Fin n) : ContDiff ℝ ∞ fun t : Vp E n => nu t i k := by
  by_cases h : i < k
  · have e : (fun t : Vp E n => nu t i k) = fun t => t ⟨(i, k), h⟩ := funext fun t => by simp [nu, h]
    rw [e]; exact contDiff_apply ℝ _ _
  · have e : (fun t : Vp E n => nu t i k) = fun _ => (if i = k then 1 else 0 : Cinf E) :=
      funext fun t => by simp [nu, h]
    rw [e]; exact contDiff_const

theorem contDiff_nu_mul : ContDiff ℝ ∞ fun q : Lie E n × Vp E n => toL (nu (-q.2) * Matrix.of q.1) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  show ContDiff ℝ ∞ fun q : Lie E n × Vp E n => ∑ k, nu (-q.2) i k * q.1 k j
  refine ContDiff.sum fun k _ => ?_
  exact ((contDiff_nu_apply i k).comp contDiff_snd.neg).mul
    ((contDiff_apply ℝ _ j).comp ((contDiff_apply ℝ _ k).comp contDiff_fst))

variable [_root_.NumberField.IsTotallyComplex E]

theorem continuous_psiInf_sdM : Continuous fun t : Vp E n => psiInf (-sdM (nu t)) := by
  have hs : Continuous (sInf E) :=
    ((continuous_infEq E).prodMk continuous_const : Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))
  have hd : Continuous fun t : Vp E n => sdM (nu t) :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => (contDiff_nu_apply i j).continuous
  exact continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar.comp (hs.comp hd.neg))

theorem bumpInf_contDiffOn_invSet : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (f : Lie E n → ℝ),
    ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ invSet E n → ContDiffOn ℝ ∞ (bumpInf f) (invSet E n) := by
  open scoped Pointwise in
  intro E _ _ _ n f hf hcs hts
  intro x₀ hx₀
  refine ContDiffAt.contDiffWithinAt ?_
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_invSet x₀ hx₀
  set r := ε / 2 with hr
  have hr0 : 0 < r := by positivity
  have hB : closedBall x₀ r ⊆ invSet E n := (closedBall_subset_ball (by linarith)).trans hball

  let Φ : Lie E n × Lie E n → Vp E n := fun q p => (Matrix.of q.1 * Matrix.of (ConstTermSmooth.invM q.2)) p.1.1 p.1.2
  have hΦ : ContinuousOn Φ (tsupport f ×ˢ closedBall x₀ r) := by
    have hinv : ContinuousOn (fun q : Lie E n × Lie E n => ConstTermSmooth.invM q.2) (tsupport f ×ˢ closedBall x₀ r) :=
      ConstTermSmooth.contDiffOn_invM.continuousOn.comp continuous_snd.continuousOn fun q hq => hB hq.2
    refine continuousOn_pi.2 fun p => ?_
    show ContinuousOn (fun q : Lie E n × Lie E n => ∑ k, q.1 p.1.1 k * ConstTermSmooth.invM q.2 k p.1.2) _
    refine continuousOn_finsetSum _ fun k _ => ?_
    have h1 : Continuous fun q : Lie E n × Lie E n => q.1 p.1.1 k :=
      (continuous_apply k).comp ((continuous_apply p.1.1).comp continuous_fst)
    have h2 : ContinuousOn (fun q : Lie E n × Lie E n => ConstTermSmooth.invM q.2 k p.1.2) (tsupport f ×ˢ closedBall x₀ r) :=
      (((continuous_apply p.1.2).comp (continuous_apply k) : Continuous fun m : Lie E n => m k p.1.2)).comp_continuousOn hinv
    exact h1.continuousOn.mul h2
  set K := Φ '' (tsupport f ×ˢ closedBall x₀ r) with hK
  have hKc : IsCompact K := (hcs.isCompact.prod (isCompact_closedBall _ _)).image_of_continuousOn hΦ

  let g : Lie E n → Vp E n → ℂ := fun x y => (f (toL (nu (-y) * Matrix.of x)) : ℂ)
  have hgs : ∀ p, ∀ y, p ∈ ball x₀ r → y ∉ -K → g p y = 0 := by
    intro p y hp hy
    by_contra hne
    have h : f (toL (nu (-y) * Matrix.of p)) ≠ 0 := fun h => hne (by simp [g, h])
    refine hy (Set.mem_neg.2 ⟨(toL (nu (-y) * Matrix.of p), p), ⟨subset_tsupport _ h, ball_subset_closedBall hp⟩, ?_⟩)
    have hu : IsUnit (Matrix.of p).det := (Matrix.isUnit_iff_isUnit_det _).1 (hB (ball_subset_closedBall hp))
    funext q
    have e : Matrix.of (toL (nu (-y) * Matrix.of p)) * Matrix.of (ConstTermSmooth.invM p) = nu (-y) :=
      Matrix.mul_nonsing_inv_cancel_right _ _ hu
    show (Matrix.of (toL (nu (-y) * Matrix.of p)) * Matrix.of (ConstTermSmooth.invM p)) q.1.1 q.1.2 = _
    rw [e]
    simp [nu, q.2]
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) (↿g) (ball x₀ r ×ˢ univ) :=
    (Complex.ofRealCLM.contDiff.comp (hf.comp contDiff_nu_mul)).contDiffOn
  have hF : LocallyIntegrable (fun t : Vp E n => psiInf (-sdM (nu t))) volume :=
    continuous_psiInf_sdM.locallyIntegrable
  have hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun _ : Lie E n => (0 : Vp E n)) (ball x₀ r) := contDiffOn_const
  have main := contDiffOn_convolution_right_with_param_comp (μ := volume)
    (ContinuousLinearMap.mul ℝ ℂ) hv isOpen_ball hKc.neg hgs hF hg
  have fin : ContDiffOn ℝ ∞ (bumpInf f) (ball x₀ r) := by
    refine main.congr fun x _ => ?_
    simp only [bumpInf, convolution_def, ContinuousLinearMap.mul_apply', zero_sub, neg_neg, g]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => mul_comm _ _)
  exact fin.contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hr0))

end GlobalTheory.WhitBump
end
end

section

open NumberField MeasureTheory GlobalTheory.CuspRep

theorem _root_.GlobalTheory.T.constant_term_slice_cusp_form : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ φ : Sm E a, IsAutForm φ → ∀ (m₁ : GA E r) (t : GL (Fin a) (Af E)) (κ : Kinf E a), GlobalTheory.SliceTwo.slice E μ 𝓕 hr φ.1 m₁ t κ ∈ Sm E (a - r) := by
  first | exact @GlobalTheory.SliceTwoSmooth.slice_mem_Sm | exact GlobalTheory.SliceTwoSmooth.slice_mem_Sm | (intros; apply GlobalTheory.SliceTwoSmooth.slice_mem_Sm <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

theorem _root_.GlobalTheory.T.archimedeanUnipotentTimesGLrSet_closed_subgroup : ∀ (E : Type) [Field E] [NumberField E] (n r : ℕ), (∀ g ∈ levSetInf E n r, ∀ h ∈ levSetInf E n r, g * h ∈ levSetInf E n r) ∧ (∀ g ∈ levSetInf E n r, g⁻¹ ∈ levSetInf E n r) ∧ (∀ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n), u ∈ levSetInf E n r) ∧ IsClosed (levSetInf E n r) := by
  first | exact @GlobalTheory.JSW.MirCinf.levSetInf_closed_subgroup | exact GlobalTheory.JSW.MirCinf.levSetInf_closed_subgroup | (intros; apply GlobalTheory.JSW.MirCinf.levSetInf_closed_subgroup; all_goals assumption)
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

theorem _root_.GlobalTheory.T.archimedeanMatrixSmoothing_moderateGrowth : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (α : (Fin n → Fin n → Cinf E) → ℂ), Continuous α → HasCompactSupport α → tsupport α ⊆ {x | IsUnit (Matrix.of x)} → ∀ W : GL (Fin n) (Cinf E) → ℂ, IsModGrowthInf W → IsModGrowthInf (smoothMatInf α W) := by
  first | (exact @GlobalTheory.JSW.MirCinf.smoothMatInf_keeps_modGrowth) | (exact GlobalTheory.JSW.MirCinf.smoothMatInf_keeps_modGrowth) | (intros; apply GlobalTheory.JSW.MirCinf.smoothMatInf_keeps_modGrowth  <;> assumption)
end
