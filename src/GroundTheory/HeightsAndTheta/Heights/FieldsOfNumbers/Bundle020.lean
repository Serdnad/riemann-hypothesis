module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle018
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR IsLocalRing

noncomputable section

universe u



theorem ConePolyLocalization.proof (h₀ : DegZeroLocLocal.Statement.{u}) (h₁ : ConeVarUnit.Statement.{u})
    (h₂ : ConeVarSurj.Statement.{u}) (h₃ : ConeVarInj.Statement.{u}) :
    ConePolyLocalization.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW v hv
  have := hP.isPrime
  have := hW.isPrime
  have hA : IsLocalRing (degZeroLoc P {W}) := h₀ F K ι P hP W hW hPW
  refine ⟨hA, ?_⟩
  let _ := (coneVarMap P W hPW v).toRingHom.toAlgebra
  have := isPrime_map_C_mvPolynomial K (maximalIdeal (degZeroLoc P {W}))
  have hQ : ∀ q : MvPolynomial K (degZeroLoc P {W}),
      q ∈ ((maximalIdeal (degZeroLoc P {W})).map
        (C : degZeroLoc P {W} →+* MvPolynomial K _)).primeCompl ↔ ∃ e, IsUnit (q.coeff e) := by
    intro q
    rw [Ideal.mem_primeCompl_iff, mem_map_C_iff]
    push Not
    simp only [mem_maximalIdeal, mem_nonunits_iff, not_not]
  refine (isLocalization_iff _ _).mpr ⟨fun y => ?_, fun z => ?_, fun {x y} hxy => ?_⟩
  · obtain ⟨e, he⟩ := (hQ y).mp y.2
    exact h₁ F K ι P hP W hW hPW v hv y e he
  · obtain ⟨p, q, e, he, hz⟩ := h₂ F K ι P hP W hW hPW v hv z
    exact ⟨⟨p, ⟨q, (hQ q).mpr ⟨e, he⟩⟩⟩, hz⟩
  · refine ⟨1, ?_⟩
    rw [h₃ F K ι P hP W hW hPW v hv hxy]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem ConeVarInj.proof (hNum : ConeVarNumerator.Statement.{u}) : ConeVarInj.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW v hv
  have := hP.isPrime
  have := hW.isPrime
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro p hp
  obtain ⟨B, g, h, -, hgW, hh, hc, hφ⟩ := hNum F K ι P hP W hW hPW v hv p

  have hu : ∀ d : K →₀ ℕ, IsMultiHomog (∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ d k) ⇑d := fun d => by
    unfold IsMultiHomog
    convert IsWeightedHomogeneous.prod Finset.univ (fun k => (X ⟨k, v k⟩ : MRing ι F) ^ d k)
      (fun k => d k • blockWeight ι ⟨k, v k⟩)
      (fun k _ => (isWeightedHomogeneous_X F (blockWeight ι) ⟨k, v k⟩).pow (d k)) using 1
    ext k
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  have huW : ∀ d : K →₀ ℕ, ∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ d k ∉ W := fun d => by
    rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨k, -, hk⟩
    exact hv k (hW.isPrime.mem_of_pow_mem _ hk)
  have hN : ∑ d ∈ p.support, h d * ∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ d k ∈ P := by
    have hg0 : algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P g) ≠ 0 := by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      exact fun hg => hgW (hPW hg)
    rw [hp, ZeroMemClass.coe_zero, eq_comm, div_eq_zero_iff, or_iff_left hg0,
      IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at hφ
    exact hφ
  refine MvPolynomial.ext _ _ fun d => ?_
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  by_contra hd
  have hcomp := hP.multiHomog _ hN (B + ⇑d)

  rw [map_sum, Finset.sum_eq_single d] at hcomp
  · rw [((hh d).mul (hu d)).weightedHomogeneousComponent_same] at hcomp
    have hhd : h d ∈ P := (hP.isPrime.mem_or_mem hcomp).resolve_right fun hm => huW d (hPW hm)
    apply hd
    apply Subtype.ext
    rw [hc d, Ideal.Quotient.eq_zero_iff_mem.mpr hhd, map_zero, zero_div]
    rfl
  · intro d' _ hne
    refine ((hh d').mul (hu d')).weightedHomogeneousComponent_ne _ fun heq => hne ?_
    ext k
    have := congrFun heq k
    simp only [Pi.add_apply] at this
    omega
  · exact fun hn => absurd (mem_support_iff.mpr hd) hn

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u


set_option maxHeartbeats 400000 in
theorem ConeVarSurj.proof : ConeVarSurj.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW v hv
  have := hP.isPrime
  have := hW.isPrime
  classical
  intro z
  set L := FractionRing (MRing ι F ⧸ P)
  let π : MRing ι F → L := fun x => algebraMap (MRing ι F ⧸ P) L (Ideal.Quotient.mk P x)
  have hπ : ∀ x, x ∉ P → π x ≠ 0 := fun x hx => by
    simp only [π, Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact hx
  let U : (K → ℕ) → MRing ι F := fun d => ∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ d k
  have hUh : ∀ d, IsMultiHomog (U d) d := fun d => by
    have := IsWeightedHomogeneous.prod Finset.univ (fun k => (X ⟨k, v k⟩ : MRing ι F) ^ d k)
      (fun k => d k • blockWeight ι ⟨k, v k⟩) (fun k _ => (isWeightedHomogeneous_X _ _ _).pow _)
    have hd : ∑ k, d k • blockWeight ι ⟨k, v k⟩ = d := by
      funext j
      simp [blockWeight, Finset.sum_apply, Pi.single_apply]
    rw [hd] at this
    exact this
  have hUW : ∀ d, U d ∉ W := fun d =>
    W.primeCompl.prod_mem fun k _ => W.primeCompl.pow_mem (hv k) _
  let comp : MRing ι F → (K → ℕ) → MRing ι F := fun h d =>
    weightedHomogeneousComponent (blockWeight ι) d h
  let c : MRing ι F → (K → ℕ) → degZeroLoc P {W} := fun h d =>
    ⟨π (comp h d) / π (U d), div_mem_degZeroLoc P {W}
      (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
      (hUh d) (fun h' => hUW d (hPW h')) (by rintro _ rfl; exact hUW d)⟩
  let D : MRing ι F → Finset (K → ℕ) := fun h => h.support.image (Finsupp.weight (blockWeight ι))
  have hsum : ∀ h, ∑ d ∈ D h, comp h d = h := fun h => by
    rw [← finsum_eq_sum_of_support_subset _ (s := D h) (fun d hd => by
      by_contra hd'
      exact hd (weightedHomogeneousComponent_eq_zero_of_notMem _ h d hd'))]
    exact sum_weightedHomogeneousComponent (blockWeight ι) h
  let Q : MRing ι F → MvPolynomial K (degZeroLoc P {W}) := fun h =>
    ∑ d ∈ D h, monomial (Finsupp.equivFunOnFinite.symm d) (c h d)
  have hQ : ∀ h, coneVarMap P W hPW v (Q h) =
      algebraMap (MRing ι F ⧸ P) (coneLocal P W hPW) (Ideal.Quotient.mk P h) := fun h => by
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [← hsum h, map_sum, map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [coneVarMap, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, degZeroLoc.algebraMap_cone_coe, SubmonoidClass.coe_finsetProd,
      SubmonoidClass.coe_pow, Subalgebra.coe_algebraMap, Finsupp.coe_equivFunOnFinite_symm]
    have hU : ∏ k, algebraMap (MRing ι F ⧸ P) L (Ideal.Quotient.mk P (X ⟨k, v k⟩)) ^ d k =
        π (U d) := by
      simp [π, U, map_prod, map_pow]
    rw [hU]
    exact div_mul_cancel₀ _ (hπ _ fun h' => hUW d (hPW h'))
  obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.surj (W.primeCompl.map (Ideal.Quotient.mk P)) z
  obtain ⟨g, hg, hgs⟩ := Submonoid.mem_map.mp s.2
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨d, hdD, hdW⟩ : ∃ d ∈ D g, comp g d ∉ W := by
    by_contra hne
    push Not at hne
    exact hg (hsum g ▸ W.sum_mem hne)
  refine ⟨Q f, Q g, Finsupp.equivFunOnFinite.symm d, ?_, ?_⟩
  · have hcoeff : (Q g).coeff (Finsupp.equivFunOnFinite.symm d) = c g d := by
      simp only [Q, coeff_sum, coeff_monomial, EmbeddingLike.apply_eq_iff_eq]
      rw [Finset.sum_ite_eq', if_pos hdD]
    rw [hcoeff]
    refine isUnit_iff_exists_inv.mpr ⟨⟨π (U d) / π (comp g d), div_mem_degZeroLoc P {W} (hUh d)
      (weightedHomogeneousComponent_isWeightedHomogeneous _ _) (fun h' => hdW (hPW h'))
      (by rintro _ rfl; exact hdW)⟩, Subtype.ext ?_⟩
    simp only [c, Subalgebra.coe_mul, Subalgebra.coe_one]
    rw [div_mul_div_cancel₀ (hπ _ fun h' => hUW d (hPW h')), div_self (hπ _ fun h' => hdW (hPW h'))]
  · rw [hQ, hQ, hgs]
    exact hxs

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end
