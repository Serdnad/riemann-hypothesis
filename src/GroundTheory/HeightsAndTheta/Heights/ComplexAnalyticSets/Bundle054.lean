module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle008
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle027
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle051
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle038
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle016
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PManifoldZerosComplementConnected
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle042
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Polynomial
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle003

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial IsLocalRing

noncomputable section

theorem ringKrullDim_quotient_add_height_of_finiteType {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsJacobsonRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] (hfin : ringKrullDim A ≠ ⊤) (q : Ideal A)
    [q.IsPrime] : ringKrullDim (A ⧸ q) + (q.height : WithBot ℕ∞) = ringKrullDim A := by
  have : FiniteRingKrullDim A :=
    finiteRingKrullDim_iff_ne_bot_and_top.mpr ⟨fun h => by
      have h0 := ringKrullDim_nonneg_of_nontrivial (R := A)
      rw [h] at h0
      exact absurd h0 (by simp), hfin⟩
  obtain ⟨s, hs⟩ := ReciprocityTheory.ChartRestriction.G.Geo.DimF.exists_height_of_isMaximal_of_field ℂ A
  exact ReciprocityTheory.ChartRestriction.G.Geo.DimF.dim_quot_add_height (fun M N hM hN => (hs M hM).trans (hs N hN).symm) q

theorem isRegularLocalRing_of_height_eq_one {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (q : Ideal A) [q.IsPrime] (hq : q.height = 1) {C : Type*} [CommRing C]
    (eqv : Localization.AtPrime (maximalIdeal (Localization.AtPrime q)) ≃+* C) :
    IsRegularLocalRing C ∧ ringKrullDim C = 1 := by
  have : IsDomain (Localization.AtPrime q) :=
    IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors q)
  have : IsIntegrallyClosed (Localization.AtPrime q) :=
    isIntegrallyClosed_of_isLocalization _ q.primeCompl (Ideal.primeCompl_le_nonZeroDivisors q)
  have hdB : ringKrullDim (Localization.AtPrime q) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q, hq]
    rfl
  have : Ring.KrullDimLE 1 (Localization.AtPrime q) := Ring.krullDimLE_iff.mpr (by rw [hdB]; rfl)
  have h3 : IsIntegrallyClosed (Localization.AtPrime q) ∧
      ∀ p : Ideal (Localization.AtPrime q), p ≠ ⊥ → p.IsPrime → p = maximalIdeal (Localization.AtPrime q) :=
    ⟨inferInstance, fun p hp0 hpp => eq_maximalIdeal (hpp.isMaximal_of_ne_bot hp0)⟩
  have : IsDedekindDomain (Localization.AtPrime q) :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (Localization.AtPrime q)).out 4 3).mp h3
  refine ⟨IsRegularLocalRing.of_ringEquiv eqv, ?_⟩
  rw [← ringKrullDim_eq_of_ringEquiv eqv,
    IsLocalization.AtPrime.ringKrullDim_eq_height (maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime (maximalIdeal (Localization.AtPrime q))),
    IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hdB]

theorem NormalCodimOneCompleteIntersection.proof : NormalCodimOneCompleteIntersection.Statement := by
  classical
  intro σ _ P Q e hP hQ hPQ hint hdP hdQ
  have hdS : ringKrullDim (MvPolynomial σ ℂ) = (Fintype.card σ : ℕ) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card,
      zero_add]

  obtain ⟨hgt, hhgt⟩ : ∃ k : ℕ, Q.height = k :=
    ENat.ne_top_iff_exists.mp Ideal.height_ne_top_of_isPrime |>.imp fun _ h => h.symm
  have hQh : hgt + e = Fintype.card σ := by
    have h := ringKrullDim_quotient_add_height_of_finiteType (A := MvPolynomial σ ℂ)
      (by rw [hdS]; exact ne_of_beq_false rfl) Q
    rw [hdQ, hdS, hhgt] at h
    have h' : e + hgt = Fintype.card σ := by exact_mod_cast h
    omega

  obtain ⟨Qb, hQb_def⟩ : ∃ Qb, Qb = Q.map (Ideal.Quotient.mk P) := ⟨_, rfl⟩
  have hQbp : Qb.IsPrime := hQb_def ▸ Ideal.isPrime_map_quotientMk_of_isPrime hPQ
  have : Algebra.FiniteType ℂ (MvPolynomial σ ℂ ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ P) (Ideal.Quotient.mkₐ_surjective ℂ P)
  have : IsDomain (MvPolynomial σ ℂ ⧸ P) := Ideal.Quotient.isDomain P
  have hQb : Qb.height = 1 := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, Qb.height = k :=
      ENat.ne_top_iff_exists.mp Ideal.height_ne_top_of_isPrime |>.imp fun _ h => h.symm
    have h := ringKrullDim_quotient_add_height_of_finiteType (A := MvPolynomial σ ℂ ⧸ P)
      (by rw [hdP]; exact ne_of_beq_false rfl) Qb
    have hq : ringKrullDim ((MvPolynomial σ ℂ ⧸ P) ⧸ Qb) = ringKrullDim (MvPolynomial σ ℂ ⧸ Q) := by
      rw [hQb_def]
      exact ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPQ)
    rw [hq, hdQ, hdP, hk] at h
    have h' : e + k = e + 1 := by exact_mod_cast h
    rw [hk]
    exact_mod_cast (by omega : k = 1)

  have hdR : ringKrullDim (Localization.AtPrime Q) = (hgt : WithBot ℕ∞) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q (Localization.AtPrime Q), hhgt]
    rfl

  have hcomap : (maximalIdeal (Localization.AtPrime Qb)).comap
      ((algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime Qb)).comp (Ideal.Quotient.mk P)) = Q := by
    rw [← Ideal.comap_comap]
    change (Ideal.under _ (maximalIdeal (Localization.AtPrime Qb))).comap (Ideal.Quotient.mk P) = Q
    rw [Localization.AtPrime.under_maximalIdeal, hQb_def,
      Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, sup_eq_left.mpr hPQ]
  obtain ⟨eqv, -⟩ := LocalizationAtPrimeQuotient.proof (MvPolynomial σ ℂ) P Qb.primeCompl
    (maximalIdeal (Localization.AtPrime Qb)) Q hcomap
  obtain ⟨hregRI, hdRI⟩ := isRegularLocalRing_of_height_eq_one Qb hQb eqv
  have hgt1 : 1 ≤ hgt := by
    have h := ringKrullDim_quotient_le (P.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q)))
    rw [hdRI, hdR] at h
    exact_mod_cast h
  obtain ⟨f, hfI, hfspan⟩ := exists_span_eq_of_isRegularLocalRing_quotient (hgt - 1) (Localization.AtPrime Q)
    (P.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q))) (by
      rw [hdR, hdRI]
      have : hgt = 1 + (hgt - 1) := by omega
      exact_mod_cast this)

  have hnum : ∀ j, ∃ a ∈ P, ∃ s ∈ Q.primeCompl,
      f j * algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q) s =
        algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q) a := by
    intro j
    obtain ⟨⟨a, s⟩, h⟩ :=
      (IsLocalization.mem_map_algebraMap_iff (M := Q.primeCompl) (S := Localization.AtPrime Q)).mp (hfI j)
    exact ⟨a, a.2, s, s.2, h⟩
  choose a haP s hsQ hfa using hnum
  have hIa : P.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q)) =
      (Ideal.span (Set.range a)).map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q)) := by
    apply le_antisymm
    · rw [hfspan, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      have hu : IsUnit (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q) (s j)) :=
        IsLocalization.map_units (Localization.AtPrime Q) ⟨s j, hsQ j⟩
      have hf : f j = algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q) (a j) * ↑hu.unit⁻¹ := by
        rw [← hfa j, mul_assoc, IsUnit.mul_val_inv, mul_one]
      rw [hf]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨j, rfl⟩))
    · exact Ideal.map_mono (Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact haP j))
  obtain ⟨t, ht⟩ := (IsNoetherian.noetherian P : P.FG)
  have hgen : ∀ p ∈ t, ∃ u ∈ Q.primeCompl, u * p ∈ Ideal.span (Set.range a) := by
    intro p hp
    have hp' : algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q) p ∈
        (Ideal.span (Set.range a)).map (algebraMap _ (Localization.AtPrime Q)) :=
      hIa ▸ Ideal.mem_map_of_mem _ (ht ▸ Ideal.subset_span hp)
    exact (IsLocalization.algebraMap_mem_map_algebraMap_iff (M := Q.primeCompl) (S := Localization.AtPrime Q) _ p).mp
      hp'
  choose! u hu hup using hgen
  refine ⟨hgt - 1, a, ∏ p ∈ t, u p, by omega, haP, ?_, ?_⟩
  · intro hmem
    obtain ⟨p, hp, hpQ⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hu p hp hpQ
  · intro p hp
    refine ⟨1, ?_⟩
    rw [pow_one]
    rw [← ht] at hp
    induction hp using Submodule.span_induction with
    | mem x hx =>
      rw [← Finset.mul_prod_erase t u hx, mul_comm (u x), mul_assoc]
      exact Ideal.mul_mem_left _ _ (hup x hx)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [mul_add]
      exact Ideal.add_mem _ hx hy
    | smul r x _ hx =>
      rw [smul_eq_mul, mul_left_comm]
      exact Ideal.mul_mem_left _ _ hx

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

namespace AnalyticGermComponents

variable {σ : Type} [Fintype σ]

def vanishingIdeal (X : Set (σ → ℂ)) (w : σ → ℂ) : Ideal (holGerms w) where
  carrier := {φ | ∃ f : (σ → ℂ) → ℂ, (f : Germ (𝓝 w) ℂ) = (φ : Germ (𝓝 w) ℂ) ∧ ∀ᶠ z in 𝓝 w, z ∈ X → f z = 0}
  add_mem' := by
    rintro a b ⟨f, hf, hf0⟩ ⟨g, hg, hg0⟩
    refine ⟨f + g, ?_, ?_⟩
    · show ((f + g : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) = (a : Germ (𝓝 w) ℂ) + (b : Germ (𝓝 w) ℂ)
      rw [← hf, ← hg]
      rfl
    · filter_upwards [hf0, hg0] with z h1 h2 hz
      simp [h1 hz, h2 hz]
  zero_mem' := ⟨0, rfl, Eventually.of_forall fun _ _ => rfl⟩
  smul_mem' := by
    rintro c a ⟨f, hf, hf0⟩
    obtain ⟨h, -, hh⟩ := c.2
    refine ⟨h * f, ?_, ?_⟩
    · show ((h * f : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) = (c : Germ (𝓝 w) ℂ) * (a : Germ (𝓝 w) ℂ)
      rw [← hh, ← hf]
      rfl
    · filter_upwards [hf0] with z h1 hz
      simp [h1 hz]

theorem mem_vanishingIdeal_iff {X : Set (σ → ℂ)} {w : σ → ℂ} {f : (σ → ℂ) → ℂ} (hf : AnalyticAt ℂ f w) :
    (⟨(f : Germ (𝓝 w) ℂ), f, hf, rfl⟩ : holGerms w) ∈ vanishingIdeal X w ↔ ∀ᶠ z in 𝓝 w, z ∈ X → f z = 0 := by
  constructor
  · rintro ⟨g, hg, hg0⟩
    have he : g =ᶠ[𝓝 w] f := Germ.coe_eq.1 hg
    filter_upwards [hg0, he] with z h1 h2 hz
    rw [← h2]
    exact h1 hz
  · intro h
    exact ⟨f, rfl, h⟩

theorem vanishingIdeal_anti {X X' : Set (σ → ℂ)} {w : σ → ℂ} (hXX' : X' ⊆ X) :
    vanishingIdeal X w ≤ vanishingIdeal X' w := by
  rintro φ ⟨f, hf, hf0⟩
  refine ⟨f, hf, ?_⟩
  filter_upwards [hf0] with z h hz
  exact h (hXX' hz)

theorem isAnalyticNear_inter_zero {X : Set (σ → ℂ)} {w : σ → ℂ} {f : (σ → ℂ) → ℂ}
    (hX : IsAnalyticNear X w) (hf : AnalyticAt ℂ f w) : IsAnalyticNear (X ∩ {z | f z = 0}) w := by
  obtain ⟨N, k, F, hN, hwN, hF, hXN⟩ := hX
  refine ⟨N ∩ {z | AnalyticAt ℂ f z}, k + 1, Fin.cons f F, hN.inter (isOpen_analyticAt ℂ f), ⟨hwN, hf⟩, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro z hz
      simpa using hz.2
    · intro z hz
      simpa using hF j z hz.1
  · ext z
    have e := Set.ext_iff.1 hXN z
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at e ⊢
    simp only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
    constructor
    · rintro ⟨⟨hzX, hfz⟩, hzN, hza⟩
      exact ⟨⟨hzN, hza⟩, hfz, (e.1 ⟨hzX, hzN⟩).2⟩
    · rintro ⟨⟨hzN, hza⟩, hfz, hFz⟩
      exact ⟨⟨(e.2 ⟨hzN, hFz⟩).1, hfz⟩, hzN, hza⟩

theorem apply_eq_zero_of_not {X : Set (σ → ℂ)} {w : σ → ℂ} {f g : (σ → ℂ) → ℂ} (hf : AnalyticAt ℂ f w)
    (hfg : ∀ᶠ z in 𝓝 w, z ∈ X → f z * g z = 0) (hng : ¬ ∀ᶠ z in 𝓝 w, z ∈ X → g z = 0) : f w = 0 := by
  by_contra h0
  apply hng
  have hev : ∀ᶠ z in 𝓝 w, f z ≠ 0 := hf.continuousAt.eventually_ne h0
  filter_upwards [hfg, hev] with z h1 h2 hz
  exact (mul_eq_zero.1 (h1 hz)).resolve_left h2

theorem vanishingIdeal_lt {X : Set (σ → ℂ)} {w : σ → ℂ} {f : (σ → ℂ) → ℂ} (hf : AnalyticAt ℂ f w)
    (hnf : ¬ ∀ᶠ z in 𝓝 w, z ∈ X → f z = 0) :
    vanishingIdeal X w < vanishingIdeal (X ∩ {z | f z = 0}) w := by
  refine lt_of_le_of_ne (vanishingIdeal_anti Set.inter_subset_left) fun heq => hnf ?_
  have hm : (⟨(f : Germ (𝓝 w) ℂ), f, hf, rfl⟩ : holGerms w) ∈ vanishingIdeal (X ∩ {z | f z = 0}) w :=
    (mem_vanishingIdeal_iff hf).2 (Eventually.of_forall fun z hz => hz.2)
  rw [← heq] at hm
  exact (mem_vanishingIdeal_iff hf).1 hm

theorem exists_finset {w : σ → ℂ} (hN : IsNoetherianRing (holGerms w)) (X : Set (σ → ℂ))
    (hX : IsAnalyticNear X w) (hw : w ∈ X) :
    ∃ s : Finset (Set (σ → ℂ)), (∀ Y ∈ s, IsAnalyticNear Y w ∧ GermIrreducibleAt Y w) ∧
      ∃ W ∈ 𝓝 w, X ∩ W = (⋃ Y ∈ s, Y) ∩ W := by
  classical
  suffices H : ∀ J : Ideal (holGerms w), ∀ X : Set (σ → ℂ), vanishingIdeal X w = J → IsAnalyticNear X w →
      w ∈ X → ∃ s : Finset (Set (σ → ℂ)), (∀ Y ∈ s, IsAnalyticNear Y w ∧ GermIrreducibleAt Y w) ∧
        ∃ W ∈ 𝓝 w, X ∩ W = (⋃ Y ∈ s, Y) ∩ W from H _ X rfl hX hw
  intro J
  induction J using WellFoundedGT.induction with
  | _ J ih =>
  intro X hJ hX hw
  by_cases hirr : GermIrreducibleAt X w
  · refine ⟨{X}, ?_, Set.univ, Filter.univ_mem, ?_⟩
    · intro Y hY
      rw [Finset.mem_singleton] at hY
      exact hY ▸ ⟨hX, hirr⟩
    · simp
  obtain ⟨f, g, hf, hg, hfg, hnf, hng⟩ : ∃ f g : (σ → ℂ) → ℂ, AnalyticAt ℂ f w ∧ AnalyticAt ℂ g w ∧
      (∀ᶠ z in 𝓝 w, z ∈ X → f z * g z = 0) ∧ ¬ (∀ᶠ z in 𝓝 w, z ∈ X → f z = 0) ∧
      ¬ (∀ᶠ z in 𝓝 w, z ∈ X → g z = 0) := by
    by_contra hcon
    refine hirr ⟨hw, fun f g hf hg hfg => ?_⟩
    by_contra h
    rw [not_or] at h
    exact hcon ⟨f, g, hf, hg, hfg, h.1, h.2⟩
  have hgf : ∀ᶠ z in 𝓝 w, z ∈ X → g z * f z = 0 := by
    filter_upwards [hfg] with z h hz
    rw [mul_comm]
    exact h hz
  have hfw : f w = 0 := apply_eq_zero_of_not hf hfg hng
  have hgw : g w = 0 := apply_eq_zero_of_not hg hgf hnf
  obtain ⟨s₁, hs₁, W₁, hW₁, hX₁⟩ := ih _ (hJ ▸ vanishingIdeal_lt hf hnf) _ rfl
    (isAnalyticNear_inter_zero hX hf) ⟨hw, hfw⟩
  obtain ⟨s₂, hs₂, W₂, hW₂, hX₂⟩ := ih _ (hJ ▸ vanishingIdeal_lt hg hng) _ rfl
    (isAnalyticNear_inter_zero hX hg) ⟨hw, hgw⟩
  refine ⟨s₁ ∪ s₂, ?_, W₁ ∩ W₂ ∩ {z | z ∈ X → f z * g z = 0}, inter_mem (inter_mem hW₁ hW₂) hfg, ?_⟩
  · intro Y hY
    rcases Finset.mem_union.1 hY with h | h
    · exact hs₁ Y h
    · exact hs₂ Y h
  ext z
  have e₁ := Set.ext_iff.1 hX₁ z
  have e₂ := Set.ext_iff.1 hX₂ z
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop] at e₁ e₂
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop, Finset.mem_union]
  constructor
  · rintro ⟨hzX, ⟨hz₁, hz₂⟩, hz0⟩
    refine ⟨?_, ⟨hz₁, hz₂⟩, hz0⟩
    rcases mul_eq_zero.1 (hz0 hzX) with h | h
    · obtain ⟨Y, hY, hzY⟩ := (e₁.1 ⟨⟨hzX, h⟩, hz₁⟩).1
      exact ⟨Y, Or.inl hY, hzY⟩
    · obtain ⟨Y, hY, hzY⟩ := (e₂.1 ⟨⟨hzX, h⟩, hz₂⟩).1
      exact ⟨Y, Or.inr hY, hzY⟩
  · rintro ⟨⟨Y, hY, hzY⟩, ⟨hz₁, hz₂⟩, hz0⟩
    refine ⟨?_, ⟨hz₁, hz₂⟩, hz0⟩
    rcases hY with hY | hY
    · exact (e₁.2 ⟨⟨Y, hY, hzY⟩, hz₁⟩).1.1
    · exact (e₂.2 ⟨⟨Y, hY, hzY⟩, hz₂⟩).1.1

theorem proof (hN : AnalyticGermsNoetherian.Statement) : AnalyticGermComponents.Statement := by
  intro σ _ X w hX hw
  obtain ⟨s, hs, W, hW, hXW⟩ := exists_finset (hN σ w) X hX hw
  refine ⟨s.card, fun i => (s.equivFin.symm i : Set (σ → ℂ)), fun i => hs _ (s.equivFin.symm i).2, W, hW, ?_⟩
  rw [hXW]
  congr 1
  ext z
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨Y, hY, hz⟩
    exact ⟨s.equivFin ⟨Y, hY⟩, by simpa using hz⟩
  · rintro ⟨i, hz⟩
    exact ⟨_, (s.equivFin.symm i).2, hz⟩

end AnalyticGermComponents

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem SheetPieceReachesCentre.proof : SheetPieceReachesCentre.Statement := by
  intro σ _ X w B d A D δ N U V hpar hU hV hcover hdisj hne
  obtain ⟨-, hwXB, hD, hDc, hmaps, hprop, hcentre, hδ, ⟨y₁, hy₁D, hy₁⟩, -, hchart, -⟩ := hpar
  set T : Set (σ → ℂ) := {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ∩ U with hTdef

  have key : ∀ y ∈ D, y ∈ closure (A '' T) → ∃ x ∈ closure T, x ∈ X ∩ B ∧ A x = y := by
    intro y hyD hy
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hD y hyD
    have hKD : Metric.closedBall y (ε / 2) ⊆ D :=
      (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
    have hP := hprop _ hKD (isCompact_closedBall y (ε / 2))
    have hQsub : closure (T ∩ A ⁻¹' Metric.closedBall y (ε / 2)) ⊆
        {x | x ∈ X ∩ B ∧ A x ∈ Metric.closedBall y (ε / 2)} :=
      closure_minimal (fun x hx => ⟨hx.1.1.1, hx.2⟩) hP.isClosed
    have hQ : IsCompact (closure (T ∩ A ⁻¹' Metric.closedBall y (ε / 2))) :=
      hP.of_isClosed_subset isClosed_closure hQsub
    have hAQ : IsClosed (A '' closure (T ∩ A ⁻¹' Metric.closedBall y (ε / 2))) :=
      (hQ.image A.continuous).isClosed
    have hyK : y ∈ closure (A '' (T ∩ A ⁻¹' Metric.closedBall y (ε / 2))) := by
      rw [mem_closure_iff_nhds] at hy ⊢
      intro t ht
      obtain ⟨z, ⟨hzt, hzK⟩, x, hxT, rfl⟩ :=
        hy (t ∩ Metric.closedBall y (ε / 2)) (Filter.inter_mem ht (Metric.closedBall_mem_nhds y (half_pos hε)))
      exact ⟨A x, hzt, x, ⟨hxT, hzK⟩, rfl⟩
    obtain ⟨x, hxQ, rfl⟩ := closure_minimal (Set.image_mono subset_closure) hAQ hyK
    exact ⟨x, closure_mono Set.inter_subset_left hxQ, (hQsub hxQ).1, rfl⟩

  have hopen : IsOpen (A '' T) := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨x, ⟨⟨hxXB, hδx⟩, hxU⟩, rfl⟩
    obtain ⟨O, V', g, hO, hV', hxV', hg, hAg, hXBV⟩ := hchart x hxXB hδx
    obtain ⟨y₀, hy₀O, hgy₀⟩ : x ∈ g '' O := hXBV ▸ ⟨hxXB, hxV'⟩
    have hAx : A x = y₀ := by rw [← hgy₀, hAg y₀ hy₀O]
    subst hAx
    have h1 : g ⁻¹' (U ∩ V') ∈ 𝓝 (A x) :=
      (hg (A x) hy₀O).continuousAt.preimage_mem_nhds (by rw [hgy₀]; exact (hU.inter hV').mem_nhds ⟨hxU, hxV'⟩)
    have h2 : δ ⁻¹' {0}ᶜ ∈ 𝓝 (A x) :=
      (hδ (A x) (hmaps hxXB)).continuousAt.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hδx)
    filter_upwards [h1, h2, hO.mem_nhds hy₀O] with y hy1 hy2 hy3
    have hgy : g y ∈ X ∩ B ∩ V' := hXBV ▸ ⟨y, hy3, rfl⟩
    refine ⟨g y, ⟨⟨hgy.1, ?_⟩, hy1.1⟩, hAg y hy3⟩
    rw [hAg y hy3]
    exact hy2

  have hreg : ∀ y ∈ D, IsRegularPointOf D y := fun y hy =>
    ⟨hy, d, ContinuousLinearMap.id ℂ _, D, D, id, hD, hD, hy, fun _ _ => analyticAt_id, fun _ _ => rfl,
      by rw [Set.inter_self, Set.image_id]⟩
  have hE : IsPreconnected (D \ {z | δ z = 0}) :=
    ManifoldZerosComplementConnected.proof (Fin d) D δ hDc hreg hδ ⟨y₁, hy₁D, hy₁⟩
  have hEsub : D \ {z | δ z = 0} ⊆ A '' T := by
    refine hE.subset_of_closure_inter_subset hopen ?_ ?_
    · obtain ⟨x₀, hx₀S, hx₀U⟩ := hne
      exact ⟨A x₀, ⟨hmaps hx₀S.1, hx₀S.2⟩, x₀, ⟨hx₀S, hx₀U⟩, rfl⟩
    · rintro y ⟨hy, hyD, hyδ⟩
      obtain ⟨x, hxcl, hxXB, rfl⟩ := key y hyD hy
      have hxS : x ∈ {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} := ⟨hxXB, hyδ⟩
      rcases hcover hxS with hxU | hxV
      · exact ⟨x, ⟨hxS, hxU⟩, rfl⟩
      · exfalso
        obtain ⟨z, hzV, hzS, hzU⟩ := mem_closure_iff.mp hxcl V hV hxV
        have hz : z ∈ {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ∩ (U ∩ V) := ⟨hzS, hzU, hzV⟩
        rw [hdisj] at hz
        exact hz

  have hwD : A w ∈ D := hmaps hwXB
  have hwE : A w ∈ closure (D \ {z | δ z = 0}) := by
    by_contra hw
    rw [mem_closure_iff_nhds] at hw
    push Not at hw
    obtain ⟨t, ht, hte⟩ := hw
    have hzero : δ =ᶠ[𝓝 (A w)] 0 := by
      filter_upwards [ht, hD.mem_nhds hwD] with y hyt hyD
      by_contra hy
      exact (Set.not_nonempty_iff_eq_empty.mpr hte) ⟨y, hyt, hyD, hy⟩
    exact hy₁ (hδ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hDc hwD hzero hy₁D)
  obtain ⟨x, hxcl, hxXB, hAx⟩ := key (A w) hwD (closure_mono hEsub hwE)
  rw [← hcentre x hxXB hAx]
  exact hxcl

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

def HolGermPointIdealSpan.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ),
    holGermPointIdeal w = Ideal.span (Set.range fun i : σ => polyGerm w (X i - C (w i)))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
