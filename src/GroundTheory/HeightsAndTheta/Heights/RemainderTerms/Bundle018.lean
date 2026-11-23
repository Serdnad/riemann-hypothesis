module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle004
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

theorem FlagDividedDifferencePoly.proof (h1 : FlagVandermondeDvd.Statement) :
    FlagDividedDifferencePoly.Statement := by
  intro f N H
  obtain ⟨R, hR⟩ := h1 f N _ (isBlockAlternating_antisymmetrize f N H)
  refine ⟨R, hR, fun w => ?_⟩
  have h := isBlockAlternating_antisymmetrize f N H w
  rw [hR, map_mul, Flag.blockPermute_blockVandermonde, smul_mul_assoc] at h
  have hs : blockSign f N w ≠ 0 := by
    intro h0
    have := Flag.blockSign_mul_self f N w
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  exact mul_left_cancel₀ (Flag.blockVandermonde_ne_zero f N) (smul_right_injective _ hs h)

end RestTerms

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

theorem FlagIntegralVandermondePos.proof : FlagIntegralVandermondePos.Statement := by
  intro f N
  unfold flagIntegral
  have hne : (blockVandermonde f N).support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
    exact Flag.blockVandermonde_ne_zero f N
  refine Finset.sum_pos (fun α hα => ?_) hne
  have hc : AddMonoidAlgebra.coeff (blockVandermonde f N) α ≠ 0 := mem_support_iff.mp hα
  refine mul_pos (mul_self_pos.mpr hc) ?_
  unfold Finsupp.prod
  exact Finset.prod_pos fun i _ => by simp only; exact_mod_cast Nat.factorial_pos _

end RestTerms

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

noncomputable section

theorem LemmaA.proof (h1 : FlagIntegralTopDegree.Statement)
    (h2 : FlagIntegralVandermondePos.Statement) (h3 : FlagDividedDifferencePoly.Statement)
    (h4 : FlagAntisymDecomposition.Statement) (h5 : FlagVandermondeHomogeneous.Statement)
    (h6 : FlagAntisymHomogeneous.Statement) (h7 : FlagQuotientHomogeneous.Statement)
    (h8 : FlagRestrictHomogeneous.Statement) (h9 : FlagRestrictSymmetric.Statement)
    (h10 : FlagRestrictDecomposition.Statement) (h11 : FlagPowerSumPreimage.Statement)
    (h12 : FlagRestrictConstantCoeff.Statement) (h13 : FlagIntegralViaQuotient.Statement) :
    LemmaA.Statement := by
  intro f N
  refine ⟨flagIntegral f N (blockVandermonde f N) / (N.factorial : ℚ) ^ f, ?_, ?_, ?_⟩
  · exact div_ne_zero (h2 f N).ne' (pow_ne_zero _ (Nat.cast_ne_zero.mpr N.factorial_ne_zero))
  · exact fun H hH => h1 f N H hH
  intro F Q hF k hk1 hkN τ G hG
  choose R hR hRsym using fun l σ => h3 f N (G * Q l σ)
  set P : RootRing f N := ∑ l ∈ Finset.Icc 1 N, ∑ σ : Fin f, blockPowerSum f N l σ * R l σ
    with hPdef
  have hanti : antisymmetrize f N (G * F) = blockVandermonde f N * P := h4 f N F G Q R hF hR
  refine ⟨P, ?_, ?_, ?_⟩
  · have hΔ : algebraMap (RootRing f N) (FractionRing (RootRing f N)) (blockVandermonde f N) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (RootRing f N) _)).mpr
        (Flag.blockVandermonde_ne_zero f N)
    rw [dividedDifference, hanti, map_mul, mul_div_cancel_left₀ _ hΔ]
  · intro hFh
    have hGF : (G * F).IsHomogeneous (topDegree f N + k) := by
      have := hG.mul hFh
      rwa [show k - 1 + (topDegree f N + 1) = topDegree f N + k by omega] at this
    have hA := h6 f N (G * F) _ hGF
    rw [hanti] at hA
    exact h8 f N τ P k (h7 _ _ _ _ _ (Flag.blockVandermonde_ne_zero f N) (h5 f N) hA)
  · obtain ⟨S, hS, hScoeff⟩ := h11 N (fun l => restrictToBlock f N τ (R l τ))
      (fun l => h9 f N τ (R l τ) (hRsym l τ))
    refine ⟨S, ?_, ?_⟩
    · rw [hS, hPdef, h10]
    · rw [hScoeff k hk1 hkN, h12, h13 f N _ _ (hR k τ)]

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

theorem FlagIntegralTopDegree.proof (h1 : FlagAltTopDegree.Statement)
    (h2 : FlagAntisymHomogeneous.Statement) (h3 : FlagIntegralViaQuotient.Statement) :
    FlagIntegralTopDegree.Statement := by
  intro f N H hH
  obtain ⟨e, he⟩ := h1 f N (antisymmetrize f N H) (isBlockAlternating_antisymmetrize f N H)
    (h2 f N H _ hH)
  have hI := h3 f N H (C e) (by rw [he, mul_comm])
  rw [constantCoeff_C] at hI
  have hΔ : algebraMap (RootRing f N) (FractionRing (RootRing f N)) (blockVandermonde f N) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (RootRing f N) (FractionRing (RootRing f N)))).mpr
      (Flag.blockVandermonde_ne_zero f N)
  have hdd : dividedDifference f N H = algebraMap ℚ (FractionRing (RootRing f N)) e := by
    rw [dividedDifference, he, map_mul, mul_div_assoc, div_self hΔ, mul_one,
      IsScalarTower.algebraMap_apply ℚ (RootRing f N) (FractionRing (RootRing f N)),
      MvPolynomial.algebraMap_eq]
  rw [hdd, ← map_mul, hI]

end RestTerms

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

noncomputable section

theorem FlagAltTopDegree.proof (h1 : FlagCoeffBlockPermute.Statement)
    (h2 : FlagAltCoeffInjective.Statement) (h3 : FlagInjSumBound.Statement)
    (h4 : FlagStaircaseOrbit.Statement) (h5 : FlagVandermondeHomogeneous.Statement) :
    FlagAltTopDegree.Statement := by
  intro f N P hP hhom

  have key : ∀ (R : RootRing f N) (β : Fin f × Fin N →₀ ℕ), IsBlockAlternating f N R →
      R.IsHomogeneous (topDegree f N) → AddMonoidAlgebra.coeff R β ≠ 0 →
      (∀ τ, Function.Injective fun i : Fin N => β (τ, i)) ∧ ∀ τ i, β (τ, i) < N := by
    intro R β hR hRh hβ
    have hinj := h2 f N R β hR hβ
    refine ⟨hinj, ?_⟩
    have hdeg : β.degree = topDegree f N := by
      by_contra hne; exact hβ (hRh.coeff_eq_zero hne)
    rw [Finsupp.degree_eq_sum, Fintype.sum_prod_type, topDegree] at hdeg
    set K := N * (N - 1) / 2
    have hge : ∀ τ, K ≤ ∑ i, β (τ, i) := fun τ => (h3 N _ (hinj τ)).1
    have hsplit : ∑ τ : Fin f, ∑ i, β (τ, i) =
        ∑ _τ : Fin f, K + ∑ τ : Fin f, (∑ i, β (τ, i) - K) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun τ _ => (Nat.add_sub_of_le (hge τ)).symm
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hdeg] at hsplit
    have hz : ∑ τ : Fin f, (∑ i, β (τ, i) - K) = 0 := by omega
    intro τ i
    have hτ := (Finset.sum_eq_zero_iff.mp hz) τ (Finset.mem_univ _)
    exact (h3 N _ (hinj τ)).2 (le_antisymm (by omega) (hge τ)) i
  have hΔ := isBlockAlternating_blockVandermonde f N
  obtain ⟨α₁, hα₁⟩ := MvPolynomial.ne_zero_iff.mp (Flag.blockVandermonde_ne_zero f N)
  set e : ℚ := AddMonoidAlgebra.coeff P α₁ / AddMonoidAlgebra.coeff (blockVandermonde f N) α₁
  set Q := P - C e * blockVandermonde f N with hQ
  have hQalt : IsBlockAlternating f N Q := by
    intro w
    simp only [hQ, map_sub, map_mul, algHom_C, hP w, hΔ w, smul_sub, mul_smul_comm,
      MvPolynomial.algebraMap_eq]
  have hQhom : Q.IsHomogeneous (topDegree f N) := hhom.sub ((h5 f N).C_mul e)
  have hQα₁ : AddMonoidAlgebra.coeff Q α₁ = 0 := by
    simp only [hQ, MvPolynomial.coeff_sub, coeff_C_mul, e]
    field_simp
    ring
  have hQ0 : Q = 0 := by
    by_contra hne
    obtain ⟨α, hα⟩ := MvPolynomial.ne_zero_iff.mp hne
    obtain ⟨hinjα, hltα⟩ := key Q α hQalt hQhom hα
    obtain ⟨hinj₁, hlt₁⟩ := key _ α₁ hΔ (h5 f N) hα₁
    obtain ⟨w, hw⟩ := h4 f N α α₁ hltα hlt₁ hinjα hinj₁
    have hα₁eq : (Finsupp.equivFunOnFinite.symm fun p : Fin f × Fin N => α (p.1, w p.1 p.2)) = α₁ := by
      ext p; simp [hw]
    have hc := h1 f N w Q α
    rw [hα₁eq, hQα₁, hQalt w, MvPolynomial.coeff_smul, smul_eq_mul] at hc
    have hs : blockSign f N w ≠ 0 := by
      intro h0; have := Flag.blockSign_mul_self f N w; rw [h0, zero_mul] at this; exact zero_ne_one this
    exact hα ((mul_eq_zero.mp hc).resolve_left hs)
  exact ⟨e, sub_eq_zero.mp hQ0⟩

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

noncomputable section

theorem flagIntegral_sum_smul_blockPermute (f N : ℕ) (H : RootRing f N)
    (s : Finset (Fin f → Equiv.Perm (Fin N))) :
    flagIntegral f N (∑ w ∈ s, blockSign f N w • blockPermute f N w H) =
      ∑ w ∈ s, blockSign f N w * flagIntegral f N (blockPermute f N w H) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Flag.flagIntegral_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Flag.flagIntegral_add, ih, smul_eq_C_mul,
      Flag.flagIntegral_C_mul]

theorem FlagIntegralAntisymmetrize.proof (h1 : FlagIntegralPermute.Statement) :
    FlagIntegralAntisymmetrize.Statement := by
  intro f N H
  rw [antisymmetrize, flagIntegral_sum_smul_blockPermute]
  rw [Finset.sum_congr rfl fun w _ => by
    rw [h1 f N w H, ← mul_assoc, Flag.blockSign_mul_self, one_mul]]
  rw [Finset.sum_const, Finset.card_univ, Flag.card_blockPerm, nsmul_eq_mul]
  push_cast
  ring

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

theorem FlagIntegralPermute.proof (h1 : FlagCoeffBlockPermute.Statement) :
    FlagIntegralPermute.Statement := by
  classical
  intro f N w H
  let e : Fin f × Fin N ≃ Fin f × Fin N := Equiv.prodShear (Equiv.refl _) w
  have hcomp : ∀ α : Fin f × Fin N →₀ ℕ,
      (Finsupp.equivFunOnFinite.symm fun p : Fin f × Fin N => α (p.1, w p.1 p.2)) =
        Finsupp.equivMapDomain e.symm α := by
    intro α; ext p; simp [Finsupp.equivMapDomain_apply, e, Equiv.prodShear]
  have hH : ∀ α, AddMonoidAlgebra.coeff (blockPermute f N w H) α = AddMonoidAlgebra.coeff H (Finsupp.equivMapDomain e.symm α) := by
    intro α; rw [h1, hcomp]
  have hD : ∀ α, AddMonoidAlgebra.coeff (blockVandermonde f N) (Finsupp.equivMapDomain e.symm α) =
      blockSign f N w * AddMonoidAlgebra.coeff (blockVandermonde f N) α := by
    intro α
    rw [← hcomp, ← h1, Flag.blockPermute_blockVandermonde, MvPolynomial.coeff_smul, smul_eq_mul]
  have hs2 : blockSign f N w * blockSign f N w = 1 := Flag.blockSign_mul_self f N w
  have hs0 : blockSign f N w ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hs2; exact zero_ne_one hs2
  have hfac : ∀ α : Fin f × Fin N →₀ ℕ,
      (Finsupp.equivMapDomain e.symm α).prod (fun _ n => (n.factorial : ℚ)) =
        α.prod (fun _ n => (n.factorial : ℚ)) := by
    intro α; rw [Finsupp.prod_equivMapDomain]
  unfold flagIntegral
  rw [Finset.mul_sum]
  refine Finset.sum_equiv (Finsupp.domCongr e.symm).toEquiv (fun α => ?_) (fun α _ => ?_)
  · simp only [MvPolynomial.mem_support_iff, AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv,
      Finsupp.domCongr_apply, hD]
    exact ⟨fun h => mul_ne_zero hs0 h, fun h h' => h (by rw [h', mul_zero])⟩
  · simp only [AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv, Finsupp.domCongr_apply, hH, hD, hfac]
    linear_combination (-(AddMonoidAlgebra.coeff H (Finsupp.equivMapDomain e.symm α) *
      AddMonoidAlgebra.coeff (blockVandermonde f N) α * α.prod (fun _ n => (n.factorial : ℚ)))) * hs2

end RestTerms

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

noncomputable section

theorem FlagIntegralVandermondeMul.proof (h1 : FlagIntegralTopComponent.Statement)
    (h2 : FlagHomogeneousComponentMul.Statement) (h3 : FlagVandermondeHomogeneous.Statement) :
    FlagIntegralVandermondeMul.Statement := by
  intro f N R
  rw [h1 f N (blockVandermonde f N * R),
    h2 _ (blockVandermonde f N) R (topDegree f N) (topDegree f N) (h3 f N),
    if_pos le_rfl, Nat.sub_self, homogeneousComponent_zero, mul_comm,
    Flag.flagIntegral_C_mul, constantCoeff_eq]

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

noncomputable section

theorem FlagIntegralViaQuotient.proof (h1 : FlagIntegralAntisymmetrize.Statement)
    (h2 : FlagIntegralVandermondeMul.Statement) : FlagIntegralViaQuotient.Statement := by
  intro f N H R hR
  have hA := h1 f N H
  rw [hR, h2 f N R] at hA
  have hne : (N.factorial : ℚ) ^ f ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N))
  rw [div_mul_eq_mul_div, eq_div_iff hne]
  linear_combination -hA

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

noncomputable section

namespace FlagVandermondeDvd

theorem blockVandermonde_eq_prod (f N : ℕ) :
    blockVandermonde f N =
      ∏ t ∈ (univ : Finset (Fin f × Fin N × Fin N)).filter (fun t => t.2.1 < t.2.2),
        ((X (t.1, t.2.1) - X (t.1, t.2.2) : RootRing f N)) := by
  rw [Finset.prod_filter, Fintype.prod_prod_type]
  simp only [blockVandermonde, vandermondeOf]
  refine Finset.prod_congr rfl (fun τ _ => ?_)
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have : Finset.Ioi i = (univ : Finset (Fin N)).filter (fun j => i < j) := by ext; simp
  rw [this, Finset.prod_filter]

theorem rename_swap_eq (f N : ℕ) (τ : Fin f) (i j : Fin N) :
    (rename (Equiv.swap (τ, i) (τ, j)) : RootRing f N →ₐ[ℚ] RootRing f N) =
      blockPermute f N (Function.update 1 τ (Equiv.swap i j)) := by
  unfold blockPermute
  congr 1
  funext p
  obtain ⟨σ, k⟩ := p
  by_cases hσ : σ = τ
  · subst hσ
    simp only [Function.update_self, Equiv.swap_apply_def, Prod.mk.injEq, true_and]
    split_ifs <;> rfl
  · simp only [Function.update_of_ne hσ, Pi.one_apply, Equiv.Perm.coe_one, id]
    rw [Equiv.swap_apply_of_ne_of_ne] <;> simp [hσ]

theorem blockSign_update_swap (f N : ℕ) (τ : Fin f) (i j : Fin N) (hij : i ≠ j) :
    blockSign f N (Function.update 1 τ (Equiv.swap i j)) = -1 := by
  unfold blockSign
  rw [Fintype.prod_eq_single τ]
  · simp [Equiv.Perm.sign_swap hij]
  · intro σ hσ
    simp [Function.update_of_ne hσ]

end FlagVandermondeDvd


open FlagVandermondeDvd in
theorem FlagVandermondeDvd.proof (h1 : FlagSwapDivisible.Statement) (h2 : FlagDiffPrime.Statement)
    (h3 : FlagDiffNotDvd.Statement) (h4 : FlagProdPrimesDvd.Statement) :
    FlagVandermondeDvd.Statement := by
  intro f N P hP
  rw [blockVandermonde_eq_prod]
  refine h4 (RootRing f N) (Fin f × Fin N × Fin N) _ _ P ?_ ?_ ?_
  · rintro ⟨τ, i, j⟩ ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    exact h2 _ _ _ (by simp [ht.ne])
  · rintro ⟨τ, i, j⟩ ht ⟨τ', i', j'⟩ ht' hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ht'
    refine h3 _ _ _ _ _ (by simp [ht.ne]) (by simp [ht'.ne]) ?_ ?_
    · rintro ⟨ha, hb⟩
      simp only [Prod.mk.injEq] at ha hb
      exact hne (by rw [ha.1, ha.2, hb.2])
    · rintro ⟨ha, hb⟩
      simp only [Prod.mk.injEq] at ha hb
      rw [ha.2, hb.2] at ht
      exact absurd (ht.trans ht') (lt_irrefl _)
  · rintro ⟨τ, i, j⟩ ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    refine h1 _ P _ _ (by simp [ht.ne]) ?_
    rw [rename_swap_eq, hP, blockSign_update_swap f N τ i j ht.ne, neg_one_smul]

end

end RestTerms

end GroundTheory.Heights₂.Heights
end
