module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Lean.Meta.Basic
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle003
public import Mathlib.RingTheory.Ideal.Height

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

section Flag

variable {K : Type} {ι : K → Type}

end Flag

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def LocRingDimOne.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (s : MRing ι) (a : K → ℕ)
    (W : Ideal (MRing ι)),
    IsMultiProjPrime P → IsMultiHomog s a → s ∉ P → W ∈ divSupp P s →
    IsNoetherianRing (locRing P W) ∧ IsLocalRing (locRing P W) ∧ ringKrullDim (locRing P W) = 1

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem geoNum_zero_nonneg {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] (W : Ideal (MRing ι))
    (b : Fin 0 → K → ℤ) : 0 ≤ geoNum 0 W b := by
  unfold geoNum
  split_ifs <;> positivity

theorem span_singleton_eq_range_lsmul {A : Type*} [CommRing A] (x : A) :
    Ideal.span {x} = LinearMap.range (LinearMap.lsmul A A x) := by
  ext z
  simp [Ideal.mem_span_singleton', LinearMap.mem_range, mul_comm]

theorem regularityLocalCardinality_holds.proof (hD : regularityLocalDimension_holds.Statement) (hR : regularityLocalResidue_holds.Statement) : regularityLocalCardinality_holds.Statement := by
  intro K _ ι _ P s a W b y hP hs hsP hW hy hy0
  obtain ⟨hloc, hnoeth, hdim⟩ := hD K ι P s a W hP hs hsP hW
  have := hloc
  have := hnoeth
  have : P.IsPrime := hP.2.1.1
  have : IsDomain (locRing P W) := inferInstance
  have : Ring.KrullDimLE 1 (locRing P W) := ReciprocityTheory.ChartRestriction.G.AI.krullDimLE_one_of_krullDim_eq hdim
  obtain ⟨-, hcard⟩ := hR K ι P s a W b hP hs hsP hW
  have hy0' : (⟨y, hy⟩ : locRing P W) ≠ 0 := fun h => hy0 (congrArg Subtype.val h)
  have hfin : Module.length (locRing P W) (locRing P W ⧸ locIdeal P W y) ≠ ⊤ := by
    rw [locIdeal_eq_span hy, span_singleton_eq_range_lsmul]
    exact ReciprocityTheory.ChartRestriction.G.AI.length_coker_ne_top (locRing P W) hy0'
  rw [card_eq_card_residueField_pow_length _ hfin, hcard]
  have hg : (geoNum 0 W b : ℝ) = ((geoNum 0 W b).toNat : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg (geoNum_zero_nonneg W b)).symm
  rw [hg]
  push_cast
  rw [Real.log_pow, Real.log_pow]

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem regularityLocalDimension_holds.proof (hF : LocRingFrac.Statement) (hL : LocRingLocal.Statement) (hN : LocRingNoeth.Statement)
    (hPw : LocRingPow.Statement) : regularityLocalDimension_holds.Statement := by
  intro K _ ι _ P s a W hP hs hsP hW
  have hPp : P.IsPrime := hP.2.1.1
  have := hPp
  have hWp : W.IsPrime := hW.1.1.1
  have hPW : P ≤ W := le_sup_left.trans hW.1.1.2
  have hsW : s ∈ W := hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  obtain ⟨hloc, hunit⟩ := hL K ι P W hPp hWp hPW
  have hnoeth := hN K ι P W hPp hWp hPW hW.2
  have := hloc
  have := hnoeth
  refine ⟨hloc, hnoeth, ?_⟩
  choose c hc using hW.2
  have ht : IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ a k) a := AvoidRing.isMultiHomog_coordProd c a
  have htW : (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ a k) ∉ W := AvoidRing.coordProd_not_mem hWp c hc a
  have htP : Ideal.Quotient.mk P (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ a k) ∈ nonZeroDivisors (MRing ι ⧸ P) :=
    mem_nonZeroDivisors_of_ne_zero fun h => htW (hPW (Ideal.Quotient.eq_zero_iff_mem.mp h))
  set xF := IsLocalization.mk' (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s) ⟨_, htP⟩ with hxF
  have hxmem : xF ∈ locRing P W := Subring.subset_closure ⟨s, _, a, htP, htW, hs, ht, rfl⟩
  have hxt : xF * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P))
      (Ideal.Quotient.mk P (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ a k)) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s) :=
    IsLocalization.mk'_spec _ _ _
  set x : locRing P W := ⟨xF, hxmem⟩
  have hx0 : x ≠ 0 := by
    intro h
    have h' : xF = 0 := congrArg Subtype.val h
    rw [h', zero_mul, eq_comm, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at hxt
    exact hsP hxt
  have hxu : ¬ IsUnit x := fun h => (hunit x s _ a hs ht htW hxt).mp h hsW
  have hmin : IsLocalRing.maximalIdeal (locRing P W) ∈ (Ideal.span {x}).minimalPrimes := by
    refine ⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem _).mpr hxu⟩, fun q hq _ y hy => ?_⟩
    obtain ⟨u, v, b, hu, hv, hvW, hyuv⟩ := hF K ι P W hPp hWp hPW y y.2
    have huW : u ∈ W := by
      by_contra h
      exact hy ((hunit y u v b hu hv hvW hyuv).mpr h)
    obtain ⟨n, z, hz, hyz⟩ :=
      hPw K ι P s _ a W xF u v b y hPp hP.2.1.2.1 hs hsP hW ht htW hxt hu hv huW hvW hyuv
    have e : y ^ n = x * ⟨z, hz⟩ := Subtype.ext (by simpa using hyz)
    have hq1 := hq.1
    exact hq1.mem_of_pow_mem n (e ▸ q.mul_mem_right _ (hq.2 (Ideal.mem_span_singleton_self x)))
  have h1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin
  have h2 := Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hx0) hxu
  have h3 := Ideal.height_mono hmin.1.2
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, le_antisymm h1 (h2 ▸ h3)]
  rfl

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem LocRingNoeth.proof (hF : LocRingFrac.Statement) : LocRingNoeth.Statement := by
  classical
  intro K _ ι _ P W hP hW hPW hrel
  have := hP
  let L := FractionRing (MRing ι ⧸ P)
  let q : MRing ι →+* L := (algebraMap (MRing ι ⧸ P) L).comp (Ideal.Quotient.mk P)
  have hq : ∀ f, f ∉ W → q f ≠ 0 := fun f hf h => hf (hPW (by
    rwa [RingHom.comp_apply, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h))
  have hnz : ∀ v, v ∉ W → Ideal.Quotient.mk P v ∈ nonZeroDivisors (MRing ι ⧸ P) := fun v hv =>
    mem_nonZeroDivisors_of_ne_zero fun h => hv (hPW (Ideal.Quotient.eq_zero_iff_mem.mp h))

  have hfrac : ∀ u v a, IsMultiHomog u a → IsMultiHomog v a → v ∉ W → q u / q v ∈ locRing P W := by
    intro u v a hu hv hvW
    refine Subring.subset_closure ⟨u, v, a, hnz v hvW, hvW, hu, hv, ?_⟩
    rw [IsFractionRing.mk'_eq_div]
    rfl
  choose c hc using hrel

  let g : (Σ k, ι k) → L := fun p => q (X p) / q (X ⟨p.1, c p.1⟩)
  let B : Subring L := Subring.closure (Set.range g)
  have hBN : IsNoetherianRing B := is_noetherian_subring_closure _ (Set.finite_range g)
  have hBS : B ≤ locRing P W := Subring.closure_le.mpr (by
    rintro _ ⟨p, rfl⟩
    exact hfrac _ _ _ (AvoidRing.isMultiHomog_X p.1 p.2) (AvoidRing.isMultiHomog_X p.1 (c p.1)) (hc p.1))
  let θ : MRing ι →+* L := eval₂Hom (Int.castRingHom L) g
  have hθB : ∀ f, θ f ∈ B := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C r => rw [eval₂Hom_C, eq_intCast]; exact intCast_mem _ r
    | add f₁ f₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | mul_X f p hf => rw [map_mul, eval₂Hom_X']; exact mul_mem hf (Subring.subset_closure ⟨p, rfl⟩)

  have hkey : ∀ u a, IsMultiHomog u a → q u = θ u * q (∏ k, X ⟨k, c k⟩ ^ a k) := by
    intro u a hu
    conv_lhs => rw [u.as_sum]
    conv_rhs => rw [u.as_sum]

    rw [map_sum, map_sum, Finset.sum_mul, map_prod]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hT : ∏ k, q (X ⟨k, c k⟩ ^ a k) = ∏ p : Σ k, ι k, q (X ⟨p.1, c p.1⟩) ^ m p := by
      rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ => ?_
      show q (X ⟨k, c k⟩ ^ a k) = ∏ y, q (X ⟨k, c k⟩) ^ m ⟨k, y⟩
      rw [map_pow, Finset.prod_pow_eq_pow_sum, hu m hm k]
    have hθm : θ (monomial m (AddMonoidAlgebra.coeff u m)) = ((AddMonoidAlgebra.coeff u m : ℤ) : L) * ∏ p, g p ^ m p := by
      rw [show θ _ = eval₂ (Int.castRingHom L) g _ from rfl, eval₂_monomial, eq_intCast,
        Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    have hqm : q (monomial m (AddMonoidAlgebra.coeff u m)) = ((AddMonoidAlgebra.coeff u m : ℤ) : L) * ∏ p, q (X p) ^ m p := by
      rw [monomial_eq, map_mul, map_finsuppProd, Finsupp.prod_fintype _ _ (fun _ => by simp)]
      simp only [map_pow]
      congr 1
      exact eq_intCast (q.comp C) _
    rw [hT, hθm, hqm, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← mul_pow]
    congr 1
    exact (div_mul_cancel₀ _ (hq _ (hc p.1))).symm

  let _ : Algebra B (locRing P W) := (Subring.inclusion hBS).toAlgebra
  let M : Submonoid B := (IsUnit.submonoid (locRing P W)).comap (Subring.inclusion hBS)
  have hLoc : IsLocalization M (locRing P W) := by
    rw [isLocalization_iff]
    refine ⟨fun y => y.2, fun z => ?_, fun {b₁ b₂} h => ⟨1, ?_⟩⟩
    · obtain ⟨u, v, a, hu, hv, hvW, hzv⟩ := hF K ι P W hP hW hPW z z.2
      have hTW := AvoidRing.coordProd_not_mem hW c hc a
      have hu' := hkey u a hu
      have hv' := hkey v a hv
      have hinv := hfrac _ v a (AvoidRing.isMultiHomog_coordProd c a) hv hvW
      have hunit : IsUnit (Subring.inclusion hBS ⟨θ v, hθB v⟩) :=
        IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (by
          show θ v * (q _ / q v) = 1
          rw [mul_div_assoc', ← hv', div_self (hq v hvW)]))
      refine ⟨(⟨θ u, hθB u⟩, ⟨⟨θ v, hθB v⟩, hunit⟩), Subtype.ext ?_⟩
      show (z : L) * θ v = θ u
      apply mul_right_cancel₀ (hq _ hTW)
      rw [mul_assoc, ← hv', ← hu']
      exact hzv
    · rw [Subring.inclusion_injective hBS h]
  exact IsLocalization.isNoetherianRing M (locRing P W) hBN

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace LocRingLocal

set_option linter.unusedSectionVars false

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem isMultiHomog_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

end LocRingLocal

theorem LocRingLocal.proof (hF : LocRingFrac.Statement) : LocRingLocal.Statement := by
  intro K _ ι _ P W hP hW hPW
  have := hP
  set F := FractionRing (MRing ι ⧸ P)
  have hnzd : ∀ w : MRing ι, w ∉ W → Ideal.Quotient.mk P w ∈ nonZeroDivisors (MRing ι ⧸ P) := fun w hw =>
    mem_nonZeroDivisors_of_ne_zero fun h => hw (hPW (Ideal.Quotient.eq_zero_iff_mem.mp h))
  have hne : ∀ w : MRing ι, w ∉ W → algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P w) ≠ 0 := fun w hw =>
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hnzd w hw)
  have key : ∀ (y : locRing P W) (u v : MRing ι) (a : K → ℕ), IsMultiHomog u a → IsMultiHomog v a → v ∉ W →
      (y : F) * algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P v) = algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P u) →
      (IsUnit y ↔ u ∉ W) := by
    intro y u v a hu hv hvW hy
    constructor
    · rintro hunit huW
      obtain ⟨y', hyy'⟩ := hunit.exists_right_inv
      obtain ⟨u', v', a', -, -, hv'W, hy'⟩ := hF K ι P W hP hW hPW y' y'.2
      have h1 : ((y * y' : locRing P W) : F) = 1 := by rw [hyy']; rfl
      have h2 : algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P (v * v')) =
          algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P (u * u')) := by
        rw [map_mul, map_mul, map_mul, map_mul, ← hy, ← hy']
        rw [Subring.coe_mul] at h1
        linear_combination (-(algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P v) *
          algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P v'))) * h1
      have h3 := Ideal.Quotient.eq.mp (IsFractionRing.injective (MRing ι ⧸ P) F h2)
      have h4 : v * v' ∈ W := by
        have := W.add_mem (hPW h3) (W.mul_mem_right u' huW)
        simpa using this
      rcases hW.mem_or_mem h4 with h | h
      · exact hvW h
      · exact hv'W h
    · intro huW
      have hz : IsLocalization.mk' F (Ideal.Quotient.mk P v) (⟨_, hnzd u huW⟩ : nonZeroDivisors (MRing ι ⧸ P)) ∈
          locRing P W := Subring.subset_closure ⟨v, u, a, hnzd u huW, huW, hv, hu, rfl⟩
      refine IsUnit.of_mul_eq_one (a := y) ⟨_, hz⟩ (Subtype.ext ?_)
      have hspec := IsLocalization.mk'_spec F (Ideal.Quotient.mk P v)
        (⟨_, hnzd u huW⟩ : nonZeroDivisors (MRing ι ⧸ P))
      simp only [Subring.coe_mul, Subring.coe_one]
      apply mul_right_cancel₀ (hne u huW)
      rw [one_mul, mul_assoc, hspec, hy]
  refine ⟨?_, key⟩
  refine IsLocalRing.of_nonunits_add fun x y hx hy => ?_
  obtain ⟨u, v, a, hu, hv, hvW, hxe⟩ := hF K ι P W hP hW hPW x x.2
  obtain ⟨u', v', a', hu', hv', hv'W, hye⟩ := hF K ι P W hP hW hPW y y.2
  have huW : u ∈ W := by
    by_contra h
    exact hx ((key x u v a hu hv hvW hxe).mpr h)
  have hu'W : u' ∈ W := by
    by_contra h
    exact hy ((key y u' v' a' hu' hv' hv'W hye).mpr h)
  have hvv' : v * v' ∉ W := fun h => (hW.mem_or_mem h).elim hvW hv'W
  have hsum : ((x + y : locRing P W) : F) * algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P (v * v')) =
      algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P (u * v' + u' * v)) := by
    simp only [Subring.coe_add, map_mul, (algebraMap (MRing ι ⧸ P) F).map_add,
      (Ideal.Quotient.mk P).map_add]
    rw [← hxe, ← hye]
    ring
  have hnum : IsMultiHomog (u * v' + u' * v) (a + a') :=
    LocRingLocal.isMultiHomog_add (AvoidRing.isMultiHomog_mul hu hv')
      (add_comm a' a ▸ AvoidRing.isMultiHomog_mul hu' hv)
  intro hunit
  exact (key (x + y) _ _ (a + a') hnum (AvoidRing.isMultiHomog_mul hv hv') hvv' hsum).mp hunit
    (W.add_mem (W.mul_mem_right v' huW) (W.mul_mem_right v hu'W))

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def PtsMonoSemiPos.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : Ideal (MRing ι)) (e : ℕ)
    (M : Fin e → HermLine ι) (E D : HermLine ι) (t : MRing ι),
    IsArithVar Q (e + 1) → (∀ j, IsSmoothHerm (M j)) → (∀ j, IsSemiPosHerm (M j)) →
    IsSmoothHerm E → IsSectionOn Q E t → IsSmoothHerm D → D.a = 0 →
    (∀ z ∈ mcPts Q, eval z (map (Int.castRingHom ℂ) t) ≠ 0 → logNorm E t z ≤ Real.log (D.h z)) →
    ptsIntegral Q (pot M) (logNorm E t) ≤ ptsIntegral Q (pot M) (fun z => Real.log (D.h z))

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def RegCurvBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (E : HermLine ι) (t : MRing ι)
    (ht : ∃ a : K → ℕ, (∀ k, E.a k = a k) ∧ IsMultiHomog t a),
    IsSmoothHerm E → ∃ C : ℕ, ∀ ε : ℝ, 0 < ε →
      IsSemiPosHerm ((E.tensor (regLine E t ht ε)).tensor
        (HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) (fun _ => (C : ℤ))))

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped ComplexOrder

def SheetHessPSD.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (M : HermLine ι) (y : Fin e → ℂ)
    (w : ((k : K) → ι k) → ℂ) (γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ),
    IsSmoothHerm M → IsSemiPosHerm M → IsSheet P Ψ y w γ →
    (cxHessian (fun y' => Real.log (M.h (γ y'))) y).PosSemidef

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def PtsRegLimit.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : Ideal (MRing ι)) (e : ℕ)
    (M : Fin e → HermLine ι) (E : HermLine ι) (t : MRing ι)
    (ht : ∃ a : K → ℕ, (∀ k, E.a k = a k) ∧ IsMultiHomog t a),
    IsArithVar Q (e + 1) → (∀ j, IsSmoothHerm (M j)) → IsSmoothHerm E → t ∉ Q →
    Filter.Tendsto (fun ε => ptsIntegral Q (pot M) (fun z => Real.log ((regLine E t ht ε).h z)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (ptsIntegral Q (pot M) (logNorm E t)))

end GroundTheory.Heights₂.Heights.Inter
end
end
