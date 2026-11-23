module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle007
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFContracted
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle010
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle001
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.RingTheory.LocalRing.Length

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR PFContracted

noncomputable section

universe u

theorem FibreFinite.proof : FibreFinite.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hP'n hPn W _ hWn _
  have := hP'.isPrime
  refine (Ideal.finite_minimalPrimes_of_isNoetherianRing _
    (P' ⊔ W.map (rename (blockIncl j ι')))).subset ?_
  rintro W' ⟨hW', hPW', hc⟩
  have := hW'.isPrime
  obtain ⟨Q, hQ, hQW'⟩ := Ideal.exists_minimalPrimes_le
    (sup_le hPW' (Ideal.map_le_iff_le_comap.mpr hc.ge))
  have := hQ.1.1
  have hP'Q : P' ≤ Q := le_sup_left.trans hQ.1.2
  suffices Q = W' by rwa [← this]
  by_contra hne
  have hQc : contractPrime j Q = W := le_antisymm (hc ▸ Ideal.comap_mono hQW')
    (Ideal.le_comap_map.trans (Ideal.comap_mono (le_sup_right.trans hQ.1.2)))
  have hne' : P' ≠ Q := by
    rintro rfl
    rw [hQc, hWn] at hPn
    simp only [natCast_withBot_withTop] at hPn
    have := WithTop.coe_inj.mp (WithBot.coe_inj.mp hPn)
    omega
  obtain ⟨f, hfQ, hfP⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hP'Q hne')
  obtain ⟨g, hgW, hgQ⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hQW' hne)
  have h1 := ringKrullDim_add_one_le hP'Q hfP hfQ
  have h2 := ringKrullDim_add_one_le hQW' hgQ hgW
  obtain ⟨D, -, hD⟩ := exists_ringKrullDim_eq
    (fun T _ hq => killBlocks_mem_of_isMultiHomogIdeal hP'.multiHomog T hq) hP'.relevant
  obtain ⟨E, -, hE⟩ := exists_ringKrullDim_eq
    (fun T _ hq => killBlocks_mem_of_isMultiHomogIdeal hW'.multiHomog T hq) hW'.relevant
  have h3 := ContractRelDimLe.proof F K K' j ι' W' hW'
  rw [hc, hWn, relDim_eq_int hE, natCast_withBot_withTop] at h3
  rw [relDim_eq_int hD, natCast_withBot_withTop] at hP'n
  have h4 : ((E + 1 + 1 : ℕ) : WithBot ℕ∞) ≤ D := by
    rw [← hD]
    rw [hE] at h2
    push_cast
    exact le_trans (by gcongr) h1
  have h3' : (n : ℤ) ≤ E - Fintype.card K' := by exact_mod_cast h3
  have hP'n' : (D : ℤ) - Fintype.card K' = (n + 1 : ℕ) := by exact_mod_cast hP'n
  have h4' : E + 1 + 1 ≤ D := by exact_mod_cast h4
  omega

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR PFContracted

noncomputable section

universe u

theorem FibreRelDim.proof : FibreRelDim.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hP'n hPn W _ hWn _ W' hW'
  obtain ⟨hW'm, hPW', hcW'⟩ := hW'
  have := hP'.isPrime
  have := hW'm.isPrime

  have hge : ((n : ℕ) : WithBot (WithTop ℤ)) ≤ relDim W' := by
    rw [← hWn, ← hcW']
    exact ContractRelDimLe.proof F K K' j ι' W' hW'm

  have hne : ¬ W' ≤ P' := by
    intro hle
    have heq : W' = P' := le_antisymm hle hPW'
    rw [heq] at hcW'
    rw [hcW', hWn] at hPn
    have := congrArg (fun x : WithBot (WithTop ℤ) => x) hPn
    rw [natCast_withBot_withTop, natCast_withBot_withTop] at this
    have h2 := WithTop.coe_injective (WithBot.coe_injective this)
    omega
  obtain ⟨f, hfW', hfP'⟩ := Set.not_subset.mp hne
  have hstab : ∀ {Q : Ideal (MRing ι' F)}, IsMultiProjPrime Q →
      ∀ (T : Finset K') (q : MRing ι' F), q ∈ Q → killBlocks T q ∈ Q :=
    fun hQ T _ hq => killBlocks_mem_of_isMultiHomogIdeal hQ.multiHomog T hq
  obtain ⟨D', -, hD'⟩ := exists_ringKrullDim_eq (hstab hP') hP'.relevant
  obtain ⟨D, -, hD⟩ := exists_ringKrullDim_eq (hstab hW'm) hW'm.relevant
  have hstep := ringKrullDim_add_one_le hPW' hfP' hfW'
  rw [hD, hD'] at hstep
  have hlt : D + 1 ≤ D' := by exact_mod_cast hstep
  rw [relDim_eq_int hD', natCast_withBot_withTop] at hP'n
  have hP'z := WithTop.coe_injective (WithBot.coe_injective hP'n)
  rw [relDim_eq_int hD, natCast_withBot_withTop] at hge ⊢
  have hgez : (n : ℤ) ≤ (D : ℤ) - Fintype.card K' :=
    WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp hge)
  congr 2
  push_cast at hP'z
  omega

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

namespace MChartLocDim

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}

theorem chartMonomial_isMultiHomog (u : ∀ k, ι k) (b : K → ℕ) :
    IsMultiHomog (chartMonomial (F := F) u b) b := by
  have h := IsWeightedHomogeneous.prod (R := F) (w := blockWeight ι) Finset.univ
    (fun k => (X ⟨k, u k⟩ : MRing ι F) ^ b k) (fun k => b k • blockWeight ι ⟨k, u k⟩)
    (fun k _ => (isWeightedHomogeneous_X F (blockWeight ι) ⟨k, u k⟩).pow (b k))
  unfold IsMultiHomog chartMonomial
  convert h using 1
  funext j
  simp [blockWeight, Finset.sum_apply, Pi.single_apply]


omit [DecidableEq K] in
theorem chartMonomial_not_mem (Q : Ideal (MRing ι F)) [Q.IsPrime] (u : ∀ k, ι k)
    (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ Q) (b : K → ℕ) : chartMonomial u b ∉ Q := by
  unfold chartMonomial
  rw [Ideal.IsPrime.prod_mem_iff]
  rintro ⟨k, -, hk⟩
  exact hu k (Ideal.IsPrime.mem_of_pow_mem inferInstance _ hk)


omit [Fintype K] [DecidableEq K] in
theorem algebraMap_mk_ne_zero (Q : Ideal (MRing ι F)) [Q.IsPrime] {g : MRing ι F} (hg : g ∉ Q) :
    algebraMap (MRing ι F ⧸ Q) (FractionRing (MRing ι F ⧸ Q)) (Ideal.Quotient.mk Q g) ≠ 0 := by
  rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  exact hg


omit [DecidableEq K] in
theorem mem_chartIdeal_iff (Q : Ideal (MRing ι F)) [Q.IsPrime] (u : ∀ k, ι k)
    (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ Q) {p h : MRing ι F} {b : K → ℕ}
    (hp : chartMap Q u p = algebraMap (MRing ι F ⧸ Q) (FractionRing (MRing ι F ⧸ Q))
      (Ideal.Quotient.mk Q h) / algebraMap (MRing ι F ⧸ Q) _ (Ideal.Quotient.mk Q (chartMonomial u b))) :
    p ∈ chartIdeal Q u ↔ h ∈ Q := by
  rw [chartIdeal, RingHom.mem_ker, hp, div_eq_zero_iff,
    or_iff_left (algebraMap_mk_ne_zero Q (chartMonomial_not_mem Q u hu b)),
    IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]


omit [Fintype K] in
theorem chartMap_mem (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) (u : ∀ k, ι k)
    (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ W) (p : MRing ι F) : chartMap P u p ∈ degZeroLoc P {W} := by
  have hr : (chartMap P u).range ≤ degZeroLoc P {W} := by
    rw [chartMap, aeval_range, Algebra.adjoin_le_iff]
    rintro _ ⟨v, rfl⟩
    exact div_mem_degZeroLoc P {W} (isWeightedHomogeneous_X F (blockWeight ι) v)
      (isWeightedHomogeneous_X F (blockWeight ι) ⟨v.1, u v.1⟩)
      (fun h => hu v.1 (hPW h)) (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; exact hu v.1)
  exact hr ⟨p, rfl⟩

def toLoc (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) (u : ∀ k, ι k)
    (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ W) : (MRing ι F ⧸ chartIdeal P u) →+* degZeroLoc P {W} :=
  Ideal.Quotient.lift (chartIdeal P u)
    ((chartMap P u).toRingHom.codRestrict (degZeroLoc P {W}) (chartMap_mem P W hPW u hu))
    (fun _ ha => Subtype.ext (RingHom.mem_ker.mp ha))

end MChartLocDim


open MChartLocDim in
theorem MChartLocDim.proof (h₁ : DegZeroLocQuot.Statement.{u}) (h₂ : MChartDehomog.Statement.{u})
    (h₃ : MChartHomog.Statement.{u}) : MChartLocDim.Statement.{u} := by
  intro F _ K _ _ ι _ P W _ _ hPW u hu
  have huP : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P := fun k h => hu k (hPW h)
  have hle : chartIdeal P u ≤ chartIdeal W u := by
    intro p hp
    obtain ⟨b, h, -, hQ⟩ := h₃ F K ι u p
    exact (mem_chartIdeal_iff W u hu (hQ W hu)).2 (hPW ((mem_chartIdeal_iff P u huP (hQ P huP)).1 hp))
  set q := (chartIdeal W u).map (Ideal.Quotient.mk (chartIdeal P u))
  have : q.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact hle)
  let _ := (toLoc P W hPW u hu).toAlgebra
  have hmap : ∀ p, ((algebraMap (MRing ι F ⧸ chartIdeal P u) (degZeroLoc P {W})
      (Ideal.Quotient.mk _ p) : degZeroLoc P {W}) : FractionRing (MRing ι F ⧸ P)) = chartMap P u p :=
    fun p => rfl
  have hmemq : ∀ p, Ideal.Quotient.mk (chartIdeal P u) p ∈ q ↔ p ∈ chartIdeal W u :=
    fun p => Ideal.mem_quotient_iff_mem hle
  have : IsLocalization.AtPrime (degZeroLoc P {W}) q := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨a, ha⟩
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
      have hpW : p ∉ chartIdeal W u := fun h => ha ((hmemq p).2 h)
      obtain ⟨b, h, hh, hQ⟩ := h₃ F K ι u p
      have hhW : h ∉ W := fun h' => hpW ((mem_chartIdeal_iff W u hu (hQ W hu)).2 h')
      have hinv := div_mem_degZeroLoc P {W} (chartMonomial_isMultiHomog u b) hh (fun h' => hhW (hPW h'))
        (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; exact hhW)
      refine IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext ?_)
      rw [Subalgebra.coe_mul, hmap, hQ P huP, Subalgebra.coe_one,
        div_mul_div_comm, mul_comm, div_self]
      exact mul_ne_zero (algebraMap_mk_ne_zero P (chartMonomial_not_mem P u huP b))
        (algebraMap_mk_ne_zero P (fun h' => hhW (hPW h')))
    · rintro ⟨x, hx⟩
      obtain ⟨b, f, g, hf, hg, hgP, hgW, rfl⟩ := h₁ F K ι P {W}
        (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; infer_instance) x hx
      have hgW' : g ∉ W := hgW W rfl
      have hgq : Ideal.Quotient.mk (chartIdeal P u) g ∈ q.primeCompl := fun h' =>
        hgW' ((mem_chartIdeal_iff W u hu (h₂ F K ι W u hu g b hg)).1 ((hmemq g).1 h'))
      refine ⟨(Ideal.Quotient.mk _ f, ⟨_, hgq⟩), Subtype.ext ?_⟩
      rw [Subalgebra.coe_mul, hmap, hmap, h₂ F K ι P u huP g b hg, h₂ F K ι P u huP f b hf]
      have h1 := algebraMap_mk_ne_zero P (chartMonomial_not_mem P u huP b)
      have h2 := algebraMap_mk_ne_zero P hgP
      field_simp
    · intro a c hac
      refine ⟨1, ?_⟩
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨p', rfl⟩ := Ideal.Quotient.mk_surjective c
      have h := congrArg Subtype.val hac
      rw [hmap, hmap, ← sub_eq_zero, ← map_sub] at h
      rw [Submonoid.coe_one, one_mul, one_mul]
      exact Ideal.Quotient.eq.mpr (RingHom.mem_ker.mpr h)
  exact IsLocalization.AtPrime.ringKrullDim_eq_height q (degZeroLoc P {W})

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]


omit [DecidableEq K] in
theorem finiteType_quotient_mRing (I : Ideal (MRing ι F)) : Algebra.FiniteType F (MRing ι F ⧸ I) :=
  Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F I) (Ideal.Quotient.mkₐ_surjective F I)


omit [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem chartMonomial_not_mem (Q : Ideal (MRing ι F)) [Q.IsPrime] (u : ∀ k, ι k)
    (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ Q) (b : K → ℕ) : chartMonomial u b ∉ Q := by
  unfold chartMonomial
  intro h
  obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h
  exact hu k (Ideal.IsPrime.mem_of_pow_mem ‹_› _ hk)

theorem chart_ringKrullDim_add_card (h : MChartTrdeg.Statement.{u}) (Q : Ideal (MRing ι F)) [Q.IsPrime]
    (hQ : IsMultiHomogIdeal Q) (u : ∀ k, ι k) (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ Q) :
    ringKrullDim (MRing ι F ⧸ chartIdeal Q u) + Fintype.card K = ringKrullDim (MRing ι F ⧸ Q) := by
  have := finiteType_quotient_mRing (F := F) (chartIdeal Q u)
  have := finiteType_quotient_mRing (F := F) Q
  rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F,
    GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F (A := MRing ι F ⧸ Q), ← h F K ι Q hQ u hu,
    map_add, map_natCast]
  norm_cast

end

theorem DegZeroLocDim.proof (h₁ : MChartHomog.Statement.{u}) (h₂ : MChartTrdeg.Statement.{u})
    (h₃ : MChartLocDim.Statement.{u}) : DegZeroLocDim.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW
  have := hP.isPrime
  have := hW.isPrime
  choose u hu using hW.relevant
  have huP : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P := fun k hk => hu k (hPW hk)
  have hle : chartIdeal P u ≤ chartIdeal W u := by
    intro p hp
    obtain ⟨b, h, -, hh⟩ := h₁ F K ι u p
    simp only [chartIdeal, RingHom.mem_ker] at hp ⊢
    rw [hh P huP, div_eq_zero_iff, IsFractionRing.to_map_eq_zero_iff,
      IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.Quotient.eq_zero_iff_mem] at hp
    have hW' : h ∈ W := by
      rcases hp with hp | hp
      · exact hPW hp
      · exact absurd hp (chartMonomial_not_mem P u huP b)
    rw [hh W hu, IsFractionRing.to_map_eq_zero_iff.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr hW'), zero_div]
  have : ((chartIdeal W u).map (Ideal.Quotient.mk (chartIdeal P u))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hle)
  have := finiteType_quotient_mRing (F := F) (chartIdeal P u)
  have hform := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient (k := F)
    ((chartIdeal W u).map (Ideal.Quotient.mk (chartIdeal P u)))
  rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hle)] at hform
  show ringKrullDim (degZeroLoc P {W}) + ringKrullDim (MRing ι F ⧸ W) = ringKrullDim (MRing ι F ⧸ P)
  rw [h₃ F K ι P W hPW u hu, ← chart_ringKrullDim_add_card h₂ W hW.multiHomog u hu,
    ← chart_ringKrullDim_add_card h₂ P hP.multiHomog u huP, ← hform, add_assoc]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR IsLocalRing

noncomputable section

universe u



theorem ConeLocalLength.proof (h₁ : LocalizedQuotientLength.Statement.{u, u})
    (h₂ : ConeLocalFlat.Statement.{u}) : ConeLocalLength.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW c a h _ _ hhW α hα
  have := hP.isPrime
  have := hW.isPrime
  obtain ⟨_, _, _, hmax⟩ := h₂ F K ι P hP W hW hPW
  have : IsLocalHom (algebraMap (degZeroLoc P {W}) (coneLocal P W hPW)) :=
    ((local_hom_tfae _).out 3 1).mp hmax.le
  have hu : IsUnit (algebraMap (MRing ι F ⧸ P) (coneLocal P W hPW) (Ideal.Quotient.mk P h)) :=
    IsLocalization.map_units (coneLocal P W hPW)
      (⟨_, ⟨h, hhW, rfl⟩⟩ : W.primeCompl.map (Ideal.Quotient.mk P))
  have hne : algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
      (Ideal.Quotient.mk P h) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact fun h' => hhW (hPW h')
  have ha : algebraMap (MRing ι F ⧸ P) (coneLocal P W hPW) (Ideal.Quotient.mk P a) =
      algebraMap (degZeroLoc P {W}) (coneLocal P W hPW) α *
        algebraMap (MRing ι F ⧸ P) (coneLocal P W hPW) (Ideal.Quotient.mk P h) := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, degZeroLoc.algebraMap_cone_coe, Subalgebra.coe_algebraMap,
      Subalgebra.coe_algebraMap, hα, div_mul_cancel₀ _ hne]
  have hspan : Ideal.span {algebraMap (MRing ι F ⧸ P) (coneLocal P W hPW) (Ideal.Quotient.mk P a)} =
      (Ideal.span {α}).map (algebraMap (degZeroLoc P {W}) (coneLocal P W hPW)) := by
    rw [Ideal.map_span, Set.image_singleton, ha, Ideal.span_singleton_mul_right_unit hu]

  have key : ∀ (A R : Type u) [CommRing A] [CommRing R] [IsLocalRing A] [IsLocalRing R]
      [Algebra A R] [IsLocalHom (algebraMap A R)] [Module.Flat A R],
      (maximalIdeal A).map (algebraMap A R) = maximalIdeal R → ∀ x : A,
        Module.length R (R ⧸ (Ideal.span {x}).map (algebraMap A R)) = Ring.ord A x := by
    intro A R _ _ _ _ _ _ _ hm x
    have hs : Module.length R (R ⧸ maximalIdeal R) = 1 := Module.length_eq_one_iff.mpr
      (isSimpleModule_iff_quot_maximal.mpr ⟨_, maximalIdeal.isMaximal _, ⟨LinearEquiv.refl _ _⟩⟩)
    rw [(Algebra.TensorProduct.quotIdealMapEquivTensorQuot R (Ideal.span {x})).toLinearEquiv.length_eq,
      IsLocalRing.length_baseChange, hm, hs, mul_one]
    rfl
  unfold multAt
  rw [h₁ _ P W a (coneLocal P W hPW) inferInstance, hspan]
  exact key (degZeroLoc P {W}) (coneLocal P W hPW) hmax α

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end
