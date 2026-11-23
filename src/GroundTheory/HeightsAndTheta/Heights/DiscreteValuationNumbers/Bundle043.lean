module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle029
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PTorsionFreeQuotientLength
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle031
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.GroupWithZero.Indicator

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

open Module Submodule
open scoped Pointwise

namespace IntermediateRingQuotLength

theorem smul_top_eq_span {A : Type*} [CommRing A] (a : A) :
    (a • ⊤ : Submodule A A) = Ideal.span {a} := by
  rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]

theorem length_quot_smul_le {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Ring.KrullDimLE 1 A] {M : Type*} [AddCommGroup M] [Module A M] (φ : A →ₗ[A] M)
    (hφ : Function.Injective φ) (htor : ∀ x : M, ∃ c : A, c ≠ 0 ∧ c • x ∈ LinearMap.range φ)
    {a : A} (ha : a ≠ 0) (hreg : Function.Injective fun x : M => a • x) :
    Module.length A (M ⧸ (a • ⊤ : Submodule A M)) ≤ Module.length A (A ⧸ Ideal.span {a}) := by
  rw [← smul_top_eq_span]
  have hLtop : Module.length A (A ⧸ (a • ⊤ : Submodule A A)) ≠ ⊤ := by
    rw [smul_top_eq_span]
    exact Module.length_ne_top_iff.mpr
      (isFiniteLength_quotient_span_singleton A (mem_nonZeroDivisors_of_ne_zero ha))
  let T : Submodule A M := a • ⊤
  have hfg : ∀ N : Submodule A M, N.FG → LinearMap.range φ ≤ N →
      Module.length A (N.map T.mkQ) ≤ Module.length A (A ⧸ (a • ⊤ : Submodule A A)) := by
    intro N hN hφN
    have : Module.Finite A N := Module.Finite.iff_fg.mpr hN
    let φN : A →ₗ[A] N := φ.codRestrict N fun y => hφN (LinearMap.mem_range_self φ y)
    have hφN' : Function.Injective φN := fun y z h => hφ (congrArg Subtype.val h)
    have hregN : Function.Injective fun x : N => a • x := fun x y h =>
      Subtype.ext (hreg (congrArg Subtype.val h))
    have hfin : IsFiniteLength A (N ⧸ LinearMap.range φN) := by
      refine GroundTheory.Heights₂.Heights.Model.TorsionFreeQuotientLength.isFiniteLength_of_torsion _
        fun q => ?_
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      obtain ⟨c, hc, y, hy⟩ := htor x
      refine ⟨c, hc, ?_⟩
      rw [← Quotient.mk_smul, Quotient.mk_eq_zero]
      exact ⟨y, Subtype.ext hy⟩
    have hle : (a • ⊤ : Submodule A N) ≤ LinearMap.ker (T.mkQ ∘ₗ N.subtype) := fun x hx => by
      obtain ⟨b, -, rfl⟩ := (mem_smul_pointwise_iff_exists _ _ _).mp hx
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, mkQ_apply,
        Quotient.mk_eq_zero, Submodule.coe_smul, Submodule.subtype_apply]
      exact smul_mem_pointwise_smul _ a ⊤ mem_top
    have hmap : N.map T.mkQ = LinearMap.range ((a • ⊤ : Submodule A N).liftQ _ hle) := by
      rw [range_liftQ, LinearMap.range_comp, range_subtype]
    rw [hmap, ← GroundTheory.Heights₂.Heights.Model.TorsionFreeQuotientLength.length_quot_smul_eq φN hφN'
      hregN hfin]
    exact Module.length_le_of_surjective _ (LinearMap.surjective_rangeRestrict _)
  let S : Set ℕ := {n | ∃ N : Submodule A M, N.FG ∧ LinearMap.range φ ≤ N ∧
    Module.length A (N.map T.mkQ) = n}
  have hSb : BddAbove S := ⟨(Module.length A (A ⧸ (a • ⊤ : Submodule A A))).toNat, by
    rintro n ⟨N, hN, hφN, hn⟩
    have := hfg N hN hφN
    rw [hn] at this
    simpa using ENat.toNat_le_toNat this hLtop⟩
  have hφfg : (LinearMap.range φ).FG := by
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map φ
  have hne0 : Module.length A ((LinearMap.range φ).map T.mkQ) ≠ ⊤ :=
    ne_top_of_le_ne_top hLtop (hfg _ hφfg le_rfl)
  have hSne : S.Nonempty := ⟨_, LinearMap.range φ, hφfg, le_rfl, (ENat.natCast_toNat hne0).symm⟩
  obtain ⟨N₀, hN₀, hφN₀, hm⟩ := Nat.sSup_mem hSne hSb
  have htop : N₀.map T.mkQ = ⊤ := by
    refine eq_top_iff.mpr fun q _ => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    by_contra hx
    have hN₁ : (N₀ ⊔ span A {x}).FG := hN₀.sup (fg_span_singleton x)
    have hx1 : Submodule.Quotient.mk x ∈ (N₀ ⊔ span A {x}).map T.mkQ :=
      mem_map_of_mem (mem_sup_right (mem_span_singleton_self x))
    have hlt : N₀.map T.mkQ < (N₀ ⊔ span A {x}).map T.mkQ :=
      lt_of_le_of_ne (map_mono le_sup_left) fun h => hx (by rw [h]; exact hx1)
    have hne : Module.length A ((N₀ ⊔ span A {x}).map T.mkQ) ≠ ⊤ :=
      ne_top_of_le_ne_top hLtop (hfg _ hN₁ (hφN₀.trans le_sup_left))
    have h1 := le_csSup hSb ⟨_, hN₁, hφN₀.trans le_sup_left, (ENat.natCast_toNat hne).symm⟩
    have h2 : Module.length A (N₀.map T.mkQ) < Module.length A ((N₀ ⊔ span A {x}).map T.mkQ) := by
      rw [Module.length_submodule, Module.length_submodule]
      refine Order.height_strictMono hlt ?_
      rw [← Module.length_submodule, hm]
      exact ENat.natCast_lt_top _
    rw [hm, ← ENat.natCast_toNat hne] at h2
    exact absurd (ENat.natCast_lt_natCast.mp h2) (not_lt.mpr h1)
  calc Module.length A (M ⧸ T) = Module.length A (N₀.map T.mkQ) := by
        rw [htop, Module.length_top]
    _ ≤ Module.length A (A ⧸ (a • ⊤ : Submodule A A)) := hfg N₀ hN₀ hφN₀

end IntermediateRingQuotLength

theorem IntermediateRingQuotLength.proof : IntermediateRingQuotLength.Statement.{u} := by
  intro A C _ _ _ _ _ _ hdim hinj hfrac a ha
  have : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.mpr (by rw [hdim]; rfl)
  have hI : (Ideal.span {algebraMap A C a}).restrictScalars A = (a • ⊤ : Submodule A C) := by
    ext x
    simp only [Submodule.restrictScalars_mem, Ideal.mem_span_singleton',
      mem_smul_pointwise_iff_exists, mem_top, true_and, Algebra.smul_def, mul_comm]
  have hreg : Function.Injective fun x : C => a • x := fun x y h => by
    simp only [Algebra.smul_def] at h
    exact mul_left_cancel₀ (by simpa using (map_ne_zero_iff _ hinj).mpr ha) h
  have htor : ∀ x : C, ∃ c : A, c ≠ 0 ∧ c • x ∈ LinearMap.range (Algebra.linearMap A C) := by
    intro x
    obtain ⟨c, hc, y, hy⟩ := hfrac x
    exact ⟨c, hc, y, by simpa using hy⟩
  rw [← (Submodule.Quotient.restrictScalarsEquiv A (Ideal.span {algebraMap A C a})).length_eq, hI]
  exact IntermediateRingQuotLength.length_quot_smul_le (Algebra.linearMap A C) hinj htor ha hreg

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem finsum_eq_finsum_mem_of_support_subset' {α : Type*} (f : α → ℤ) {s : Set α}
    (h : Function.support f ⊆ s) : ∑ᶠ i, f i = ∑ᶠ i ∈ s, f i := by
  rw [finsum_mem_def, Set.indicator_eq_self.2 h]

theorem BlowUpHorizontalCorresp.proof (hsat : BlowUpHorizontalSat.Statement.{u})
    (hmult : BlowUpHorizontalMult.Statement.{u}) (hlift : BlowUpHorizontalLift.Statement.{u})
    (hstrict : BlowUpHorizontalStrict.Statement.{u}) : BlowUpHorizontalCorresp.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hex hloc c x hx hxP
  have sat := hsat O ϖ hϖ K ι J P n hP N u hu hex hloc c x hx hxP
  have mult := hmult O ϖ hϖ K ι J P n hP N u hu hex hloc c x hx hxP
  have lift := hlift O ϖ hϖ K ι J P n hP N u hu hex hloc c x hx hxP
  have strict := hstrict O ϖ hϖ K ι J P n hP N u hu hex hloc c x hx hxP
  have hC : ∀ W : Ideal (MRing (extIdx ι J) O),
      (C ϖ : MRing ι O) ∈ W.comap (liftForm (ι := ι) (J := J) (R := O)) ↔
        (C ϖ : MRing (extIdx ι J) O) ∈ W := by
    intro W
    rw [Ideal.mem_comap]
    simp [liftForm]
  refine ⟨fun h => ?_, fun W hW hϖW => ⟨by rw [mult W hW hϖW]; exact hW, strict W hW hϖW⟩⟩
  classical
  unfold cycEval
  let s : Set (Ideal (MRing (extIdx ι J) O)) :=
    {W | divCycle (blowUpOf P u) (liftForm x) W ≠ 0 ∧ (C ϖ : MRing (extIdx ι J) O) ∉ W}
  let t : Set (Ideal (MRing ι O)) := {W | divCycle P x W ≠ 0 ∧ (C ϖ : MRing ι O) ∉ W}
  rw [finsum_eq_finsum_mem_of_support_subset' _ (s := s) ?hs,
    finsum_eq_finsum_mem_of_support_subset' _ (s := t) ?ht]
  case hs =>
    intro W hW
    rw [Function.mem_support] at hW
    exact ⟨fun h0 => hW (by rw [h0, zero_mul]), fun hc => hW (by simp only [if_pos hc, mul_zero])⟩
  case ht =>
    intro W hW
    rw [Function.mem_support] at hW
    exact ⟨fun h0 => hW (by rw [h0, zero_mul]), fun hc => hW (by simp only [if_pos hc, mul_zero])⟩
  refine finsum_mem_eq_of_bijOn (fun W => W.comap (liftForm (ι := ι) (J := J) (R := O)))
    ⟨?_, ?_, ?_⟩ ?_
  · intro W hW
    exact ⟨by rw [mult W hW.1 hW.2]; exact hW.1, fun h => hW.2 ((hC W).1 h)⟩
  · intro W₁ h₁ W₂ h₂ he
    ext F
    rw [sat W₁ h₁.1 h₁.2 F, sat W₂ h₂.1 h₂.2 F]
    simp only at he
    rw [he]
  · intro W hW
    obtain ⟨W', h1, h2, h3⟩ := lift W hW.1 hW.2
    exact ⟨W', ⟨h1, h2⟩, h3⟩
  · intro W hW
    simp only
    rw [if_neg hW.2, if_neg (fun h => hW.2 ((hC W).1 h)), mult W hW.1 hW.2]

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

open Classical in
theorem BlowUpVerticalPush.proof (hfib : BlowUpVerticalFibre.Statement.{u}) :
    BlowUpVerticalPush.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP a
  have hZ : (Function.support (divCycle (blowUpOf P u) (liftForm (J := J) x))).Finite :=
    DivCycleFiniteSupport.proof O (Option K) (extIdx ι J) _ _

  have hC : ∀ W' : Ideal (MRing (extIdx ι J) O), (C ϖ : MRing (extIdx ι J) O) ∈ W' ↔
      (C ϖ : MRing ι O) ∈ W'.comap (liftForm (ι := ι) (J := J) (R := O)) := by
    intro W'
    rw [Ideal.mem_comap]
    simp [liftForm]
  set g : Ideal (MRing (extIdx ι J) O) → ℤ := fun W' =>
    divCycle (blowUpOf P u) (liftForm x) W' *
      (if (C ϖ : MRing (extIdx ι J) O) ∈ W' then vNum W' (liftDegs a) else 0) with hg_def
  have hg : Function.support g ⊆ hZ.toFinset := fun W' hW' =>
    hZ.mem_toFinset.mpr (Function.support_mul_subset_left _ _ hW')

  have key : ∀ W : Ideal (MRing ι O),
      (∑ W' ∈ hZ.toFinset with W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W, g W') =
        divCycle P x W * (if (C ϖ : MRing ι O) ∈ W then vNum W a else 0) := by
    intro W
    by_cases hW : (C ϖ : MRing ι O) ∈ W
    · rw [if_pos hW, ← hfib O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP a W hW,
        finsum_eq_sum_of_support_subset _ (s := hZ.toFinset), Finset.sum_filter]
      · refine Finset.sum_congr rfl fun W' _ => ?_
        by_cases h1 : W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W
        · rw [if_pos h1, if_pos h1, hg_def]
          dsimp only
          rw [if_pos ((hC W').mpr (by rw [h1]; exact hW))]
        · rw [if_neg h1, if_neg h1]
      · intro W' hW'
        refine hZ.mem_toFinset.mpr ?_
        rw [Function.mem_support] at hW' ⊢
        intro h0
        apply hW'
        simp [h0]
    · rw [if_neg hW, mul_zero]
      refine Finset.sum_eq_zero fun W' hW' => ?_
      have h1 := (Finset.mem_filter.mp hW').2
      rw [hg_def]
      dsimp only
      rw [if_neg (fun h => hW (h1 ▸ (hC W').mp h)), mul_zero]
  unfold cycEval
  calc (∑ᶠ W', divCycle (blowUpOf P u) (liftForm x) W' *
          (if (C ϖ : MRing (extIdx ι J) O) ∈ W' then vNum W' (liftDegs a) else 0))
      = ∑ W' ∈ hZ.toFinset, g W' := finsum_eq_sum_of_support_subset g hg
    _ = ∑ᶠ W, ∑ W' ∈ hZ.toFinset with W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W, g W' :=
        (finsum_sum_filter _ _ _).symm
    _ = _ := finsum_congr key

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem ResidualDisjoint.proof : ResidualDisjoint.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G' hϖG' hsG' hresG'
  set P' := blowUpOf P (blowUpGens s g f m e) with hP'def
  have hPprime : P.IsPrime := hP.multiProj.isPrime
  have hP'prime : P'.IsPrime := RingHom.ker_isPrime _
  have hmul := DivCycleMul.proof O (Option K) (extIdx ι (BlowUpIdx ι)) P'
  have hlm : liftForm (J := BlowUpIdx ι) m ∉ P' := fun h => by
    rw [hP'def, blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_liftForm, Polynomial.C_eq_zero,
      Ideal.Quotient.eq_zero_iff_mem] at h
    exact hmP h
  have hY₁P' : (newVar (some none) : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ P' := fun h => by
    rw [hP'def, blowUpOf, RingHom.mem_ker] at h
    simp only [newVar, aeval_X, blowUpSubst, blowUpGens, mul_eq_zero, Polynomial.X_ne_zero, or_false,
      Polynomial.C_eq_zero, Ideal.Quotient.eq_zero_iff_mem] at h
    exact (hPprime.mem_or_mem h).elim hD.1.num_not_mem hmP
  have hnonneg : ∀ x W, 0 ≤ divCycle P' x W := fun x W => by
    unfold divCycle; split_ifs <;> simp
  have hzero : ∀ x, x ∉ G' → divCycle P' x G' = 0 := fun x hx => by
    by_contra h; exact hx (form_mem_of_divCycle_ne_zero h)
  have hG'supp : G' ∈ (P' ⊔ Ideal.span {liftForm s}).minimalPrimes ∧ IsRelevant G' := by
    by_contra h
    unfold divCycle at hsG'
    rw [dif_neg h] at hsG'
    exact (lt_irrefl 0) hsG'
  have hP'G' : P' ≤ G' := le_sup_left.trans hG'supp.1.1.2

  have hY₁G' : (newVar (some none) : MRing (extIdx ι (BlowUpIdx ι)) O) ∈ G' := by
    apply form_mem_of_divCycle_ne_zero (P := P')
    have := hnonneg (liftForm m) G'
    unfold ratDiv at hresG'; omega

  have hYiG' : ∀ i : ∀ k, ι k, (newVar (some (some i)) : MRing (extIdx ι (BlowUpIdx ι)) O) ∈ G' := by
    intro i
    by_contra hYi
    have hrel : liftForm (powMonomial e i) * newVar (some none) -
        liftForm m * newVar (some (some i)) ∈ P' := by
      rw [hP'def, blowUpOf, RingHom.mem_ker]
      simp only [map_sub, map_mul, aeval_blowUpSubst_liftForm, newVar, aeval_X, blowUpSubst, blowUpGens]
      ring
    have hYiP' : (newVar (some (some i)) : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ P' := fun h => hYi (hP'G' h)
    by_cases hp : liftForm (J := BlowUpIdx ι) (powMonomial e i : MRing ι O) ∈ P'
    · have h := P'.sub_mem (P'.mul_mem_right (newVar (some none)) hp) hrel
      rw [sub_sub_cancel] at h
      exact (hP'prime.mem_or_mem h).elim hlm hYiP'
    · have h1 := congrFun (divCycle_congr_of_sub_mem hrel) G'
      rw [hmul _ _ hP'prime hp hY₁P', hmul _ _ hP'prime hlm hYiP'] at h1
      simp only [Pi.add_apply] at h1
      have h2 := hzero _ hYi
      have h3 := hnonneg (liftForm (powMonomial e i)) G'
      unfold ratDiv at hresG'; omega

  obtain ⟨j, hj⟩ := hG'supp.2 none
  change BlowUpIdx ι at j
  rcases j with _ | _ | i
  · exact hj
  · exact absurd hY₁G' hj
  · exact absurd (hYiG' i) hj

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem ResidualComparison.proof (hpieces : BlowUpDecomposition.Statement.{u})
    (hdisj : ResidualDisjoint.Statement.{u}) (hcontr : ResidualContraction.Statement.{u}) :
    ResidualComparison.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G' hϖG' hsG' hresG'
  obtain ⟨hP', -, hsP', -, hres, hexc, -, -⟩ :=
    hpieces O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH
  have hY₀G' := hdisj O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G' hϖG' hsG' hresG'
  have hcmp := hcontr O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G' hϖG' hsG' hresG'
  set P' := blowUpOf P (blowUpGens s g f m e) with hP'def
  set G := G'.comap (liftForm (J := BlowUpIdx ι) (ι := ι) (R := O)) with hGdef
  have hP'prime : P'.IsPrime := hP'.multiProj.isPrime
  have hPprime : P.IsPrime := hP.multiProj.isPrime
  have hmul := DivCycleMul.proof O (Option K) (extIdx ι (BlowUpIdx ι)) P'
  have hmul₀ := DivCycleMul.proof O K ι P
  have nm : ∀ x y, x ∉ P' → y ∉ P' → x * y ∉ P' := fun x y hx hy h =>
    (hP'prime.mem_or_mem h).elim hx hy
  have hzero : ∀ x, x ∉ G' → divCycle P' x G' = 0 := fun x hx => by
    by_contra h; exact hx (form_mem_of_divCycle_ne_zero h)

  have hG'supp : G' ∈ (P' ⊔ Ideal.span {liftForm s}).minimalPrimes ∧ IsRelevant G' := by
    by_contra h
    unfold divCycle at hsG'
    rw [dite_eq_right h] at hsG'
    exact lt_irrefl _ hsG'
  have hG'prime : G'.IsPrime := hG'supp.1.1.1
  have hP'G' : P' ≤ G' := le_sup_left.trans hG'supp.1.1.2
  have hlift : ∀ p ∈ P, liftForm (J := BlowUpIdx ι) p ∈ P' := fun p hp => by
    rw [hP'def, blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_liftForm,
      Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]
  have hGprime : G.IsPrime := Ideal.comap_isPrime _ _
  have hPG : P ≤ G := fun p hp => hP'G' (hlift p hp)
  have hGrel : IsRelevant G := fun k => by
    obtain ⟨i, hi⟩ := hG'supp.2 (some k)
    exact ⟨i, fun h => hi (by simpa [hGdef, liftForm] using h)⟩
  have hϖG : (C ϖ : MRing ι O) ∈ G := by
    rw [hGdef, Ideal.mem_comap, liftForm_const]; exact hϖG'

  obtain ⟨u, v, huG, huv⟩ := hD.2 G hGprime hPG hGrel
  have hfP := hD.1.num_not_mem
  have hgP := hD.1.den_not_mem
  have huP : u ∉ P := fun h => huG (hPG h)
  have hvP : v ∉ P := fun hv => by
    have h : u * f ∈ P := by
      rw [show u * f = (u * f - v * g) + v * g by ring]
      exact P.add_mem huv (P.mul_mem_right g hv)
    exact (hPprime.mem_or_mem h).elim huP hfP
  have hdown : ratDiv P f g G = divCycle P v G := by
    have h1 := congrFun (divCycle_congr_of_sub_mem huv) G
    rw [hmul₀ u f hPprime huP hfP, hmul₀ v g hPprime hvP hgP] at h1
    have hu0 : divCycle P u G = 0 := by
      by_contra h; exact huG (form_mem_of_divCycle_ne_zero h)
    simp only [Pi.add_apply] at h1
    unfold ratDiv; omega

  have hluP' : liftForm (J := BlowUpIdx ι) u ∉ P' := fun h => huG (hP'G' h)
  have hlfP' : liftForm (J := BlowUpIdx ι) f ∉ P' := fun h =>
    hexc.1.num_not_mem (by rw [map_mul]; exact P'.mul_mem_right _ h)
  have hlgP' : liftForm (J := BlowUpIdx ι) g ∉ P' := fun h => hexc.1.den_not_mem (P'.mul_mem_right _ h)
  have hluv : liftForm u * liftForm f - liftForm v * liftForm g ∈ P' := by
    rw [← map_mul, ← map_mul, ← map_sub]; exact hlift _ huv
  have hlvP' : liftForm (J := BlowUpIdx ι) v ∉ P' := fun hv => by
    have h : liftForm u * liftForm f ∈ P' := by
      rw [show liftForm u * liftForm f = (liftForm u * liftForm f - liftForm v * liftForm g) +
        liftForm v * liftForm g by ring]
      exact P'.add_mem hluv (P'.mul_mem_right _ hv)
    exact nm _ _ hluP' hlfP' h
  have hup : ratDiv P' (liftForm f) (liftForm g) G' = divCycle P' (liftForm v) G' := by
    have h1 := congrFun (divCycle_congr_of_sub_mem hluv) G'
    rw [hmul _ _ hP'prime hluP' hlfP', hmul _ _ hP'prime hlvP' hlgP'] at h1
    have hu0 := hzero _ huG
    simp only [Pi.add_apply] at h1
    unfold ratDiv; omega

  have hY₁P' : (newVar (some none) : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ P' := hres.1.num_not_mem
  have hlmP' : liftForm (J := BlowUpIdx ι) m ∉ P' := hres.1.den_not_mem
  have hY₀P' : (newVar none : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ P' := fun h => hY₀G' (hP'G' h)
  have hrel := congrFun (divCycle_congr_of_sub_mem (blowUp_relation P s g f m e)) G'
  rw [map_mul, map_mul, hmul _ _ hP'prime (nm _ _ hsP' hlgP') hY₁P',
    hmul _ _ hP'prime (nm _ _ hlfP' hlmP') hY₀P', hmul _ _ hP'prime hsP' hlgP',
    hmul _ _ hP'prime hlfP' hlmP'] at hrel
  have hY₀0 := hzero _ hY₀G'
  simp only [Pi.add_apply] at hrel
  have hv := hcmp v hvP
  refine ⟨G, hϖG, hcmp s hsP, ?_⟩
  unfold ratDiv at hup hdown ⊢
  omega

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal joinCoord midDeg midVar)

def JoinVerticalDivisorRight.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (z : (Σ k, ι' k) → Ω) (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (w : (Σ k, ι₂ k) → Ω) (b : K ⊕ K' → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (Sum.elim ι ι')),
    IsVertDiv O (mcIdeal O (joinCoord x z)) b f g →
    IsVertDiv O (mcIdeal O (joinCoord x (joinCoord w z))) (midDeg (K₂ := K₂) b)
      (rename (midVar ι₂) f) (rename (midVar ι₂) g)

end GroundTheory.Heights₂.Heights.NumbersDVR
end
