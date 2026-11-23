module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle026
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.DedekindDomain.Factorization
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HermCoord
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

@[expose] public section

section

open ValuativeRel Matrix
open scoped Classical

theorem _root_.GlobalTheory.T.levelZeroUniformizerFrame_unipotent_and_embedGL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : GlobalTheory.SymChain.SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], (∀ n : S.P.J, n.1 ∈ GlobalTheory.RootEx.N k (Fin κ) (s + 1) (S.ρ + 1) → GlobalTheory.LevZeroGen.upZero S t n.1 ∈ GlobalTheory.RootEx.N k (GlobalTheory.StepData.XIx (Fin κ) t 0) (s + 1) (S.ρ + 1) ∧ ((S.P.lam n : ℂˣ) : ℂ) = (S.ψ (GlobalTheory.RootEx.simpleSum (GlobalTheory.LevZeroGen.upZero S t n.1)) : ℂ)) ∧ ∀ γ : GL (Fin κ) k, GlobalTheory.LevZeroGen.upZero S t (GlobalTheory.RootEx.embX (s + 1) γ) = GlobalTheory.RootEx.embX (s + 1) (GlobalTheory.StepData.reGL (GlobalTheory.LevZeroGen.xZero (Fin κ) t) γ) := by
  first | exact @GlobalTheory.LevZeroUp.upZero_N_embX | exact GlobalTheory.LevZeroUp.upZero_N_embX | (intros; apply GlobalTheory.LevZeroUp.upZero_N_embX <;> assumption)
end

section

open Formalism.BasicNotions IsDedekindDomain NumberField

namespace GlobalTheory.IdeleGen

theorem exists_nat_mem_mul_integral {E : Type} [Field E] [NumberField E]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hI : I ≠ 0) :
    ∃ N : ℕ, N ≠ 0 ∧ (N : E) ∈ I ∧ ∀ b ∈ I, ∃ o : 𝓞 E, (N : E) * b = (o : E) := by
  obtain ⟨a, ha, hint⟩ := I.isFractional
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hbot : (I : Submodule (𝓞 E) E) ≠ ⊥ := by
    intro h
    apply hI
    exact FractionalIdeal.coeToSubmodule_injective (h.trans FractionalIdeal.coe_zero.symm)
  obtain ⟨x, hxI, hx0⟩ := (Submodule.ne_bot_iff _).1 hbot
  obtain ⟨j, hj⟩ := hint x hxI
  have hj' : (j : E) = (a : E) * x := by
    simpa [Algebra.smul_def] using hj
  have haE : (a : E) ≠ 0 := by exact_mod_cast ha0
  have hj0 : j ≠ 0 := by
    intro h; rw [h] at hj'; simp at hj'
    rcases hj' with h1 | h1
    · first | exact ha0 h1 | exact ha0 h1.symm | exact haE h1 | exact haE h1.symm
    · first | exact hx0 h1 | exact hx0 h1.symm
  set Nd := Ideal.absNorm (Ideal.span {a}) with hNd
  set Nj := Ideal.absNorm (Ideal.span {j}) with hNj
  have hNd0 : Nd ≠ 0 := by
    rw [hNd, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact ha0
  have hNj0 : Nj ≠ 0 := by
    rw [hNj, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hj0
  obtain ⟨o₁, ho₁⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
  obtain ⟨o₂, ho₂⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {j}))
  have ho₁E : ((Nd : 𝓞 E) : E) = (o₁ : E) * (a : E) := by rw [← ho₁]; push_cast; ring
  have ho₂E : ((Nj : 𝓞 E) : E) = (o₂ : E) * (j : E) := by rw [← ho₂]; push_cast; ring
  refine ⟨Nd * Nj, mul_ne_zero hNd0 hNj0, ?_, ?_⟩
  · have : ((Nd * Nj : ℕ) : E) = ((Nd : 𝓞 E) * o₂ * a : 𝓞 E) • x := by
      rw [Algebra.smul_def]
      have e1 : ((Nd * Nj : ℕ) : E) = ((Nd : 𝓞 E) : E) * ((Nj : 𝓞 E) : E) := by push_cast; ring
      rw [e1, ho₂E]
      have hal : ∀ z : 𝓞 E, algebraMap (𝓞 E) E z = (z : E) := fun _ => rfl
      rw [hal]
      push_cast
      linear_combination ((Nd : E) * (o₂ : E)) * hj'
    rw [this]
    exact Submodule.smul_mem _ _ hxI
  · intro b hb
    obtain ⟨y, hy⟩ := hint b hb
    have hy' : (y : E) = (a : E) * b := by simpa [Algebra.smul_def] using hy
    refine ⟨(Nj : 𝓞 E) * o₁ * y, ?_⟩
    have e1 : ((Nd * Nj : ℕ) : E) = ((Nd : 𝓞 E) : E) * ((Nj : 𝓞 E) : E) := by push_cast; ring
    rw [e1, ho₁E]
    push_cast
    linear_combination (-((Nj : E) * (o₁ : E))) * hy'

theorem aeGen : ∀ (D : D7) (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E), I ≠ 0 →
    ∃ S : Finset (HeightOneSpectrum (𝓞 D.host.F)), ∀ v ∉ S, ∃ c : 𝓞 D.host.F, c ∉ v.asIdeal ∧
      ((c : D.host.F) : D.host.E) ∈ I ∧ ∀ b ∈ I, ∃ o : 𝓞 D.host.E, ((c : D.host.F) : D.host.E) * b = (o : D.host.E) := by
  intro D I hI
  obtain ⟨N, hN0, hNI, hNb⟩ := exists_nat_mem_mul_integral I hI
  have hc0 : Ideal.span {(N : 𝓞 D.host.F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN0
  have hfin := Ideal.finite_factors hc0
  refine ⟨hfin.toFinset, fun v hv => ⟨(N : 𝓞 D.host.F), ?_, ?_, ?_⟩⟩
  · intro hmem
    apply hv
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hmem
  · have : (((N : 𝓞 D.host.F) : D.host.F) : D.host.E) = (N : D.host.E) := by push_cast; rfl
    rw [this]; exact hNI
  · have : (((N : 𝓞 D.host.F) : D.host.F) : D.host.E) = (N : D.host.E) := by push_cast; rfl
    rw [this]; exact hNb

end GlobalTheory.IdeleGen
end

section

open Formalism.BasicNotions IsDedekindDomain NumberField

namespace GlobalTheory.LocGen

theorem exists_gen_mul_of_isIntegral {R S : Type*} [CommRing R] [CommRing S] [IsDedekindDomain S] [Algebra R S]
    [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S)) (p : Ideal R) [p.IsPrime] (hp : p ≠ ⊥)
    (J : Ideal S) (hJ : J ≠ ⊥) :
    ∃ y ∈ J, y ≠ 0 ∧ ∃ c : R, c ∉ p ∧ ∀ j ∈ J, ∃ o : S, algebraMap R S c * j = y * o := by
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp
  have hr'0 : algebraMap R S r ≠ 0 := fun h => hr0 (hinj (by rw [h, map_zero]))
  have hJ0 : J ≠ 0 := hJ
  have hIv0 : J * Ideal.span {algebraMap R S r} ≠ 0 :=
    mul_ne_zero hJ0 (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hr'0)
  obtain ⟨y, hy⟩ := exists_sup_span_eq (Ideal.mul_le_left : J * Ideal.span {algebraMap R S r} ≤ J) hIv0
  have hyJ : y ∈ J := hy ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self y)
  obtain ⟨K, hK⟩ : J ∣ Ideal.span {y} := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hyJ)
  have key : ¬ Ideal.comap (algebraMap R S) K ≤ p := by
    intro h
    obtain ⟨Q, hKQ, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p K h
    have hrQ : algebraMap R S r ∈ Q := by
      change r ∈ Ideal.under R Q
      rw [hQp]; exact hr
    have h1 : J * Ideal.span {algebraMap R S r} ≤ J * Q :=
      Ideal.mul_mono_right ((Ideal.span_singleton_le_iff_mem _).mpr hrQ)
    have h2 : Ideal.span {y} ≤ J * Q := hK ▸ Ideal.mul_mono_right hKQ
    have h3 : J ≤ J * Q := calc J = _ := hy.symm
      _ ≤ J * Q := sup_le h1 h2
    have h4 : J * Q = J * ⊤ := by
      rw [Ideal.mul_top]; exact le_antisymm Ideal.mul_le_left h3
    exact hQ.ne_top (mul_left_cancel₀ hJ0 h4)
  rw [SetLike.not_le_iff_exists] at key
  obtain ⟨c, hcK, hcp⟩ := key
  rw [Ideal.mem_comap] at hcK
  refine ⟨y, hyJ, ?_, c, hcp, ?_⟩
  · rintro rfl
    have hJK : J * K = 0 := by rw [← hK, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    have hK0 : K = 0 := (mul_eq_zero.mp hJK).resolve_left hJ0
    rw [hK0, Ideal.zero_eq_bot, Ideal.mem_bot] at hcK
    exact hcp (by rw [hinj (hcK.trans (map_zero _).symm)]; exact p.zero_mem)
  · intro j hj
    have hm : j * algebraMap R S c ∈ Ideal.span {y} := hK ▸ Ideal.mul_mem_mul hj hcK
    obtain ⟨o, ho⟩ := Ideal.mem_span_singleton'.mp hm
    exact ⟨o, by rw [mul_comm, ← ho, mul_comm]⟩

end GlobalTheory.LocGen

namespace GlobalTheory


open GlobalTheory.LocGen in
theorem fracIdeal_locGen : ∀ (D : D7) (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E), I ≠ 0 →
    ∀ v : HeightOneSpectrum (𝓞 D.host.F), ∃ a : D.host.E, a ≠ 0 ∧ ∃ c : 𝓞 D.host.F, c ∉ v.asIdeal ∧
      ((c : D.host.F) : D.host.E) * a ∈ I ∧
      ∀ b ∈ I, ∃ o : 𝓞 D.host.E, ((c : D.host.F) : D.host.E) * b = a * (o : D.host.E) := by
  intro D I hI v
  letI : Algebra (𝓞 D.host.F) (𝓞 D.host.E) := (RingOfIntegers.mapRingHom D.host.F.subtype).toAlgebra
  have hφ : ∀ c : 𝓞 D.host.F, ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c : 𝓞 D.host.E) : D.host.E) =
      ((c : D.host.F) : D.host.E) := fun c => rfl
  haveI : Algebra.IsIntegral (𝓞 D.host.F) (𝓞 D.host.E) := Algebra.IsIntegral.tower_top (R := ℤ)
  have hinj : Function.Injective (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
    intro x y h
    have h' := congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) h
    simp only [hφ] at h'
    exact RingOfIntegers.ext (Subtype.ext h')
  obtain ⟨d, J, hd, rfl⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  have hJ : J ≠ ⊥ := by
    rintro rfl
    exact hI (by rw [FractionalIdeal.coeIdeal_bot, mul_zero])
  obtain ⟨y, hyJ, hy0, c, hcv, hc⟩ := exists_gen_mul_of_isIntegral hinj v.asIdeal v.ne_bot J hJ
  have hd' : ((d : 𝓞 D.host.E) : D.host.E) ≠ 0 := by
    rwa [Ne, RingOfIntegers.coe_eq_zero_iff]
  have hy' : ((y : 𝓞 D.host.E) : D.host.E) ≠ 0 := by
    rwa [Ne, RingOfIntegers.coe_eq_zero_iff]
  refine ⟨(y : D.host.E) * (d : D.host.E)⁻¹, mul_ne_zero hy' (inv_ne_zero hd'), c, hcv, ?_, ?_⟩
  · rw [FractionalIdeal.mem_singleton_mul]
    refine ⟨algebraMap (𝓞 D.host.E) D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c * y), ?_, ?_⟩
    · exact (FractionalIdeal.mem_coeIdeal _).mpr ⟨_, J.mul_mem_left _ hyJ, rfl⟩
    · rw [map_mul]
      show _ = _ * (((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c : 𝓞 D.host.E) : D.host.E) * (y : D.host.E))
      rw [hφ]
      ring
  · intro b hb
    rw [FractionalIdeal.mem_singleton_mul] at hb
    obtain ⟨b', hb', rfl⟩ := hb
    obtain ⟨j, hj, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hb'
    obtain ⟨o, ho⟩ := hc j hj
    refine ⟨o, ?_⟩
    have h2 : ((c : D.host.F) : D.host.E) * (j : D.host.E) = (y : D.host.E) * (o : D.host.E) := by
      have h3 := congrArg (algebraMap (𝓞 D.host.E) D.host.E) ho
      rw [map_mul, map_mul] at h3
      exact h3
    calc ((c : D.host.F) : D.host.E) * (((d : 𝓞 D.host.E) : D.host.E)⁻¹ * (j : D.host.E))
        = (d : D.host.E)⁻¹ * (((c : D.host.F) : D.host.E) * (j : D.host.E)) := by ring
      _ = (d : D.host.E)⁻¹ * ((y : D.host.E) * (o : D.host.E)) := by rw [h2]
      _ = _ := by ring

end GlobalTheory
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
open GlobalTheory.SWC

noncomputable section

namespace GlobalTheory.HermSD

end GlobalTheory.HermSD

namespace GlobalTheory.HermSD

theorem eq_of_test_haar {V : Type} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [LocallyCompactSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] {κ P : Measure V} {χ : V → V → ℂ}
    (hκ : SelfDual κ χ) (hP : P.IsAddHaarMeasure) (Φ : V → ℂ) (hc : Continuous Φ)
    (hs : HasCompactSupport Φ) (hI : Integrable (fun y => ∫ x, Φ x * χ x y ∂P) P) (z : V)
    (h1 : ∫ y, (∫ x, Φ x * χ x y ∂P) * χ y z ∂P = Φ (-z)) (hz : Φ (-z) ≠ 0) : κ = P := by
  have := hκ.1
  have e : κ = Measure.addHaarScalarFactor κ P • P := Measure.isAddLeftInvariant_eq_smul κ P
  set c : NNReal := Measure.addHaarScalarFactor κ P with hcdef
  have hT : ∀ y, ∫ x, Φ x * χ x y ∂κ = (c : ℂ) * ∫ x, Φ x * χ x y ∂P := by
    intro y
    rw [e, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  have hI' : Integrable (fun y => ∫ x, Φ x * χ x y ∂κ) κ := by
    simp only [hT]
    rw [e]
    exact (hI.const_mul (c : ℂ)).smul_measure_nnreal
  have h2 := hκ.2 Φ hc hs hI' z
  simp only [hT] at h2
  rw [e, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul] at h2
  have h3 : ∫ y, ((c : ℂ) * ∫ x, Φ x * χ x y ∂P) * χ y z ∂P =
      (c : ℂ) * ∫ y, (∫ x, Φ x * χ x y ∂P) * χ y z ∂P := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun y => by ring)
  rw [h3, h1, ← mul_assoc] at h2
  have h4 : ((c : ℂ)) * (c : ℂ) = 1 := mul_right_cancel₀ hz (by rw [h2, one_mul])
  have h5 : c * c = 1 := by exact_mod_cast h4
  have h6 : c = 1 := by
    have : (c : ℝ) * c = 1 := by exact_mod_cast h5
    have h7 : (c : ℝ) = 1 := by nlinarith [c.coe_nonneg]
    exact_mod_cast h7
  rw [e, h6, one_smul]

end GlobalTheory.HermSD

namespace GlobalTheory.HermSD

end GlobalTheory.HermSD

namespace GlobalTheory.HermSD

end GlobalTheory.HermSD
end
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
open GlobalTheory.SWC

noncomputable section

namespace GlobalTheory.HermSD

def coordPair {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (n : ℕ) (x y : (Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E)) : R :=
  ∑ a, x.1 a * y.1 a + ∑ p, Algebra.trace R (R ⊗[F] E) (sigR R σ (x.2 p) * y.2 p)

end GlobalTheory.HermSD
end
end
