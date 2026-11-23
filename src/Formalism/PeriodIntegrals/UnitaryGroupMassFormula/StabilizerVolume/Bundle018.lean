module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.PosNear
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

section

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

theorem integrable_of_isOmT {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {ψ : AddChar (AF F) ℂ}
    {a : ℕ} {T : Matrix (Fin a) (Fin a) E} {hT : ∀ i j, σ (T j i) = T i j}
    {νX : Measure (Fin a → Fin M → AF F ⊗[F] E)} (hν : IsOmT F E σ M J ψ T hT νX)
    {Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ} (hΦ : IsAdm F E Φ) : Integrable Φ νX := by
  obtain ⟨d, b, Φinf, Φf, Φv, hc, hcs, hpf, hprod⟩ := hΦ
  obtain ⟨μinf, h1⟩ := hν.2.1
  have k1 := hν.2.2 μinf h1
  obtain ⟨νinf, h2⟩ := k1.1
  have k2 := k1.2 νinf h2
  obtain ⟨μv, h3⟩ := k2.1
  have k3 := k2.2 μv h3
  obtain ⟨νv, h4⟩ := k3.1
  have k4 := k3.2 νv h4
  obtain ⟨fibInf, h5⟩ := k4.1
  have k5 := k4.2 fibInf h5
  obtain ⟨fibV, h6⟩ := k5.1
  exact (k5.2 fibV h6 d b Φ Φinf Φf Φv hc hcs hpf hprod).1

theorem posTest_of (hN : TestNear) : PosTest := by
  intro F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ _hψ μ hμ νX hν μ' _hμ' hC
  obtain ⟨φ, hφ0, hadm, U, hUo, hUne, hUpos⟩ := hN F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet
  refine ⟨φ, hφ0, hadm, fun hI0 => ?_⟩
  have hint : Integrable (fun X => (φ X : ℂ)) νX := integrable_of_isOmT hν hadm.adm
  have hintR : Integrable φ νX := by simpa using hint.re
  have hI : ∫ X, φ X ∂νX = 0 := by
    rw [integral_complex_ofReal] at hI0
    exact_mod_cast hI0
  have hae : φ =ᵐ[νX] 0 := (integral_eq_zero_iff_of_nonneg (fun X => hφ0 X) hintR).1 hI
  obtain ⟨hnull, hform⟩ := hC
  classical
  let s : (Fin a → Fin M → AF F ⊗[F] E) → HA (AF F) σ J := fun y =>
    if h : ∃ g : HA (AF F) σ J, g • ratTup (AF F) X0 = y then h.choose else 1
  have hs : ∀ y, (∃ g : HA (AF F) σ J, g • ratTup (AF F) X0 = y) →
      s y • ratTup (AF F) X0 = y := by
    intro y h
    simp only [s, dif_pos h]
    exact h.choose_spec
  have hf : Measurable (U.indicator (1 : HA (AF F) σ J → ENNReal)) :=
    measurable_one.indicator hUo.measurableSet
  have e := hform _ hf s hs
  have hL : ∫⁻ g, U.indicator (1 : HA (AF F) σ J → ENNReal) g ∂μ = μ U :=
    lintegral_indicator_one hUo.measurableSet
  have : μ.IsHaarMeasure := hμ
  have hpos : 0 < μ U := hUo.measure_pos μ hUne
  have hR : ∫⁻ y, ∫⁻ h', U.indicator (1 : HA (AF F) σ J → ENNReal)
      (s y * (h' : HA (AF F) σ J)) ∂μ' ∂νX = 0 := by
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hae, ae_iff.2 hnull] with y hy0 hyo
    simp only [Pi.zero_apply] at hy0
    have hz : ∀ h' : stabT (AF F) σ J X0,
        U.indicator (1 : HA (AF F) σ J → ENNReal) (s y * (h' : HA (AF F) σ J)) = 0 := by
      intro h'
      refine Set.indicator_apply_eq_zero.2 fun hm => ?_
      exfalso
      have hh : (h' : HA (AF F) σ J) • ratTup (AF F) X0 = ratTup (AF F) X0 := h'.2
      have h0 := hUpos _ hm
      rw [mul_smul, hh, hs y hyo, hy0] at h0
      exact lt_irrefl _ h0
    simp only [hz, lintegral_zero]
  rw [hL, hR] at e
  exact hpos.ne' e

theorem posTest_holds : PosTest := posTest_of testNear_holds

end PI.VolStabS
end
end

section

noncomputable section

namespace PI.VolStabS.AdmissibleCompactSupport

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open PI.VolStabS PI.VolStabS.PositiveNearLattice Set Filter
open scoped TensorProduct RestrictedProduct

variable {F : Type} [Field F] [NumberField F]

theorem isCompact_finBox {D : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (hc : ∀ v, IsCompact (D v))
    (hf : ∀ᶠ v in cofinite, D v = (v.adicCompletionIntegers F : Set (Fv F v))) :
    IsCompact {x : Af F | ∀ v, x v ∈ D v} := by
  let S : Set (HeightOneSpectrum (𝓞 F)) := {v | D v = (v.adicCompletionIntegers F : Set (Fv F v))}
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.2 hf
  let R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F
  let A := fun v : HeightOneSpectrum (𝓞 F) =>
    (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  let K : Set (Πʳ v, [R v, A v]_[𝓟 S]) := {x | ∀ v, x v ∈ D v}
  have hK : IsCompact K := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.isCompact_iff]
    have e : ((↑) : Πʳ v, [R v, A v]_[𝓟 S] → ∀ v, R v) '' K = Set.pi univ D := by
      ext g
      constructor
      · rintro ⟨x, hx, rfl⟩ v _
        exact hx v
      · intro hg
        refine ⟨⟨g, ?_⟩, fun v => hg v (mem_univ v), rfl⟩
        rw [eventually_principal]
        intro v hv
        have h := hg v (mem_univ v)
        rwa [show D v = _ from hv] at h
    rw [e]
    exact isCompact_univ_pi hc
  have e : {x : Af F | ∀ v, x v ∈ D v} = RestrictedProduct.inclusion R A hS '' K := by
    ext x
    constructor
    · intro hx
      refine ⟨⟨x, ?_⟩, hx, rfl⟩
      rw [eventually_principal]
      intro v hv
      have h := hx v
      rwa [show D v = _ from hv] at h
    · rintro ⟨y, hy, rfl⟩ v
      exact hy v
  rw [e]
  exact hK.image (RestrictedProduct.continuous_inclusion hS)

variable {E : Type} [Field E] [Algebra F E] [FiniteDimensional F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E)

theorem crd_projV {a M : ℕ} (Y : Fin a → Fin M → Af F ⊗[F] E) (v : HeightOneSpectrum (𝓞 F))
    (i : Fin a) (j : Fin M) (k : Fin d) :
    crd b (Fv F v) (projV v Y i j) k = (crd b (Af F) (Y i j) k) v := by
  simp only [projV]
  rw [crd_map]
  rfl

theorem eventually_mem_latV {a M : ℕ} (Y : Fin a → Fin M → Af F ⊗[F] E) :
    ∀ᶠ v in cofinite, projV v Y ∈ latV b v := by
  have h : ∀ (i : Fin a) (j : Fin M) (k : Fin d), ∀ᶠ v in cofinite,
      (crd b (Af F) (Y i j) k) v ∈ v.adicCompletionIntegers F :=
    fun i j k => (crd b (Af F) (Y i j) k).2
  filter_upwards [eventually_all.2 fun i => eventually_all.2 fun j => eventually_all.2 fun k =>
    h i j k] with v hv
  intro i j k
  have := crd_projV b Y v i j k
  simp only [crd] at this
  rw [this]
  exact hv i j k

variable {a M : ℕ} (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ)

theorem mulSupport_finite
    (hae : ∀ᶠ v in cofinite, Φv v = (latV b v).indicator 1) (Y : Fin a → Fin M → Af F ⊗[F] E) :
    (Function.mulSupport fun v => Φv v (projV v Y)).Finite := by
  refine (Filter.eventually_cofinite.1 (hae.and (eventually_mem_latV b Y))).subset ?_
  intro v hv h
  apply hv
  simp only
  rw [h.1, Set.indicator_of_mem h.2]
  rfl

theorem factor_ne_zero (hae : ∀ᶠ v in cofinite, Φv v = (latV b v).indicator 1)
    (Y : Fin a → Fin M → Af F ⊗[F] E) (h : ∏ᶠ v, Φv v (projV v Y) ≠ 0)
    (v : HeightOneSpectrum (𝓞 F)) : Φv v (projV v Y) ≠ 0 := by
  have hfin := mulSupport_finite b Φv hae Y
  rw [finprod_eq_prod _ hfin] at h
  by_cases hv : v ∈ hfin.toFinset
  · exact Finset.prod_ne_zero_iff.1 h v hv
  · rw [Set.Finite.mem_toFinset, Function.mem_mulSupport, not_not] at hv
    rw [hv]
    exact one_ne_zero

end PI.VolStabS.AdmissibleCompactSupport

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW PI.VolStabS.AdmissibleCompactSupport

end PI.VolStabS
end
end
