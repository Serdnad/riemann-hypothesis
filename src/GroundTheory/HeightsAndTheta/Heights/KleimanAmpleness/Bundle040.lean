module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle022
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechExact
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperQuotAdd
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle029
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle036
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapper
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle006
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

namespace SnapperSubquotientFinite

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem chartRing_fg (I : Chart x) : (chartRing S x I).FG := by
  classical
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  refine ⟨Finset.univ.image (fun l => x l / x i) ∪ I.1.image (fun j => x i / x j), ?_⟩
  apply le_antisymm
  · rw [Algebra.adjoin_le_iff]
    intro a ha
    simp only [Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_union,
      Set.mem_range, Set.mem_image, Finset.mem_coe] at ha
    rcases ha with ⟨l, rfl⟩ | ⟨j, hj, rfl⟩
    · exact ⟨X l, X i, 1, X_mem_monos hi, isHomogeneous_X S l, isHomogeneous_X S i, by simp⟩
    · exact ⟨X i, X j, 1, X_mem_monos hj, isHomogeneous_X S i, isHomogeneous_X S j, by simp⟩
  · rintro a ⟨f, s, e, hs, hf, hse, rfl⟩
    set T := Algebra.adjoin S ((Finset.univ.image (fun l => x l / x i) ∪
      I.1.image (fun j => x i / x j) : Finset Ω) : Set Ω) with hT
    have h1 : aeval x f / x i ^ e ∈ T := by
      have hc : aeval x f / x i ^ e ∈ chartRing S x (singleChart hxi) :=
        ⟨f, X i ^ e, e, pow_mem (X_mem_monos (Finset.mem_singleton_self i)) e, hf,
          isHomogeneous_X_pow _ _, by simp⟩
      refine Algebra.adjoin_mono ?_ (mem_ampleBase_of_mem_chartRing hxi hc)
      rintro _ ⟨l, rfl⟩
      simp
    have h2 : ∀ s ∈ monos (S := S) I.1, ∃ e', s.IsHomogeneous e' ∧ x i ^ e' / aeval x s ∈ T := by
      intro s hs
      induction hs using Submonoid.closure_induction with
      | mem a ha =>
        obtain ⟨j, hj, rfl⟩ := ha
        refine ⟨1, isHomogeneous_X S j, ?_⟩
        rw [aeval_X, pow_one]
        exact Algebra.subset_adjoin (by simp only [Finset.coe_union, Finset.coe_image, Set.mem_union,
          Set.mem_image, Finset.mem_coe]; exact Or.inr ⟨j, hj, rfl⟩)
      | one => exact ⟨0, isHomogeneous_one _ _, by simp⟩
      | mul a b _ _ ha hb =>
        obtain ⟨ea, ha1, ha2⟩ := ha
        obtain ⟨eb, hb1, hb2⟩ := hb
        refine ⟨ea + eb, ha1.mul hb1, ?_⟩
        rw [map_mul, pow_add, mul_div_mul_comm]
        exact T.mul_mem ha2 hb2
    obtain ⟨e', hse', h2'⟩ := h2 s hs
    have hs0 : aeval x s ≠ 0 := eval_ne_zero_of_mem_monos I hs
    have hs0' : s ≠ 0 := by rintro rfl; exact hs0 (map_zero _)
    obtain rfl : e = e' := hse.inj_right hse' hs0'
    have hxe : x i ^ e ≠ 0 := pow_ne_zero _ hxi
    have : aeval x f / aeval x s = (aeval x f / x i ^ e) * (x i ^ e / aeval x s) := by
      field_simp
    rw [this]
    exact T.mul_mem h1 h2'

theorem isNoetherianRing_chart [IsNoetherianRing S] (I : Chart x) : IsNoetherianRing (chartRing S x I) := by
  have : Algebra.FiniteType S (chartRing S x I) := ⟨(Subalgebra.fg_top _).mpr (chartRing_fg I)⟩
  exact Algebra.FiniteType.isNoetherianRing S _

end SnapperSubquotientFinite



open SnapperQuotientAdditivity SnapperSubquotientFinite in
theorem SnapperSubquotFinite.proof (hfin : SnapperFinite.Statement.{u, v, w}) :
    SnapperSubquotFinite.Statement.{u, v, w} := by
  intro k _ Ω _ _ N x E _ _ _ _ F F₁ F₂ hfg h1 h21 i
  have hfg1 : ∀ I, (F₁.sub I).FG := fun I => by
    have := isNoetherianRing_chart (S := k) I
    exact (hfg I).of_le (h1 I)
  have hfg2 : ∀ I, (F₂.sub I).FG := fun I => by
    have := isNoetherianRing_chart (S := k) I
    exact (hfg I).of_le ((h21 I).trans (h1 I))

  have hH : ∀ (G : SubFamily k x E), (∀ I, (G.sub I).FG) → ∀ j,
      FiniteDimensional k (Cech.Hdeg (fun I : Chart x => (G.sub I : Type v)) (fun _ => ⊤)
        G.toSubSystem.res j) := by
    intro G hG j
    have h := hfin k Ω N x E G hG 0 Fin.elim0 Fin.elim0 0 j
    change FiniteDimensional k ((G.toSubSystem.twist (twistSys k x 0)).H j) at h
    rw [SubSystem.twist_twistSys_zero] at h
    have : FiniteDimensional k (Cech.H (fun I : Chart x => (G.sub I : Type v)) G.toSubSystem.res j) := h
    exact (hdegTopEquiv _ _ j).symm.finiteDimensional
  have hdd := CechDSq.proof (N + 1) (support x) k (fun I : Chart x => (F₁.sub I : Type v))
    F₁.toSubSystem.res (fun _ _ _ _ _ => LinearMap.ext fun _ => rfl)
  let φ : ∀ I : Chart x, F₂.sub I →ₗ[k] F₁.sub I := fun I =>
    { toFun := fun y => ⟨y, h21 I y.2⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let ψ : ∀ I : Chart x, F₁.sub I →ₗ[k] F₁.sub I ⧸ SubSystem.quotSub F₁.toSubSystem F₂.toSubSystem I :=
    fun I => (SubSystem.quotSub F₁.toSubSystem F₂.toSubSystem I).mkQ
  have L := Cech.longExact (R := k) (U := support x)
    (A := fun I : Chart x => (F₂.sub I : Type v)) (B := fun I : Chart x => (F₁.sub I : Type v))
    (C := fun I : Chart x => F₁.sub I ⧸ SubSystem.quotSub F₁.toSubSystem F₂.toSubSystem I)
    (ρA := F₂.toSubSystem.res) (ρB := F₁.toSubSystem.res)
    (ρC := SubSystem.quotRes F₁.toSubSystem F₂.toSubSystem)
    (dA := fun _ => ⊤) (dB := fun _ => ⊤) (dC := fun _ => ⊤) (φ := φ) (ψ := ψ)
  have L1 := L (fun _ _ _ _ => rfl)
  have L2 := L1 (fun _ _ _ _ => rfl)
  have L3 := L2 (fun _ _ _ => Submodule.mem_top) (fun _ _ _ => Submodule.mem_top)
  have L4 := L3 (fun I a b hab => Subtype.ext (congrArg (fun z : F₁.sub I => (z : E)) hab))
  have L5 := L4 (fun I y => (Submodule.Quotient.mk_eq_zero _).2 y.2)
  have L6 := L5 (fun I m _ hm => ⟨⟨m, (Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F₁.toSubSystem F₂.toSubSystem I)).1 hm⟩, Submodule.mem_top, rfl⟩)
  have L7 := L6 (fun I z _ => (Submodule.Quotient.mk_surjective _ z).imp fun y hy => ⟨Submodule.mem_top, hy⟩)
  have L8 := L7 (fun _ _ _ _ _ => Submodule.mem_top)
  have liftZP_newton := L8 hdd
  obtain ⟨δ, hgδ, -⟩ := (liftZP_newton.2 i).2
  have := hH F₁ hfg1 i
  have := hH F₂ hfg2 (i + 1)
  have hC := Module.Finite.of_exact (f := Cech.mapHdeg _ _ ψ _ _ i) (g := δ.rangeRestrict)
    (LinearMap.exact_iff.2 (by rw [LinearMap.ker_rangeRestrict]; exact LinearMap.exact_iff.1 hgδ))
    δ.surjective_rangeRestrict
  exact (hdegTopEquiv _ _ i).finiteDimensional

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree
open GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated (cellRes_mk cellMon_mono isMultiHomog_monomial)

noncomputable section

namespace KHFreeEmbed

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)]

theorem cellRes_monoFrac {J I : ∀ k, Finset (ι k)} (hJI : ∀ k, J k ⊆ I k) (a : (Σ k, ι k) → ℤ)
    (hJ : ∀ k, negSet a k ⊆ J k) :
    KH.cellRes S (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) J I (monoFrac S J a) = monoFrac S I a := by
  have hI : ∀ k, negSet a k ⊆ I k := fun k => (hJ k).trans (hJI k)
  unfold monoFrac
  rw [dite_eq_left hJ, dite_eq_left hI, cellRes_mk (cellMon_mono hJI)]

theorem blockSum_add_negExp (a : (Σ k, ι k) → ℤ) (k : K) :
    blockSum a k + ((∑ i, negExp a ⟨k, i⟩ : ℕ) : ℤ) = ((∑ i, posExp a ⟨k, i⟩ : ℕ) : ℤ) := by
  unfold blockSum
  push_cast
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [negExp, posExp, Finsupp.coe_equivFunOnFinite_symm]
  omega

theorem isMultiHomog_posExp (a : (Σ k, ι k) → ℤ) :
    IsMultiHomog (monomial (posExp a) (1 : S) : MRingOver S ι) fun k => ∑ i, posExp a ⟨k, i⟩ :=
  isMultiHomog_monomial _ _ _ fun _ => rfl

theorem mk_posExp_mem (a : (Σ k, ι k) → ℤ) (e : K → ℤ) (he : ∀ k, e k = ((∑ i, posExp a ⟨k, i⟩ : ℕ) : ℤ)) :
    Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι)) (monomial (posExp a) 1) ∈
      KH.quotPart S (⊥ : Ideal (MRingOver S ι)) e := by
  unfold KH.quotPart
  refine Submodule.subset_span ⟨_, ⟨fun k => ?_, ?_⟩, rfl⟩
  · rw [he k]; exact Int.natCast_nonneg _
  · have : (fun k => (e k).toNat) = fun k => ∑ i, posExp a ⟨k, i⟩ := funext fun k => by rw [he k]; rfl
    rw [this]
    exact isMultiHomog_posExp a

theorem update_erase_subset (I : ∀ k, Finset (ι k)) (k : K) (i : ι k) (l : K) :
    Function.update I k ((I k).erase i) l ⊆ I l := by
  by_cases hl : l = k
  · subst hl; rw [Function.update_self]; exact Finset.erase_subset _ _
  · rw [Function.update_of_ne hl]


open Classical in
theorem embed_apply (a : (Σ k, ι k) → ℤ) (n : ℕ) (f : CombC S (negSet a) n) (I : KH.Cell K ι n) :
    embed S a n f I = if h : ∀ k, negSet a k ⊆ I.1 k then f ⟨I, h⟩ • monoFrac S I.1 a else 0 := by
  unfold embed
  rw [LinearMap.pi_apply]
  split_ifs <;> rfl


open Classical in
theorem cechD_apply (n : ℕ) (x : KH.CechC S ι (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) n)
    (I : KH.Cell K ι (n + 1)) :
    KH.cechD S ι (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) n x I = ∑ k, ∑ i ∈ I.1 k,
      if h : (∀ l, (Function.update I.1 k ((I.1 k).erase i) l).Nonempty) ∧
          ∑ l, ((Function.update I.1 k ((I.1 k).erase i) l).card - 1) = n then
        KH.faceSign I.1 k i • KH.cellRes S _ (Function.update I.1 k ((I.1 k).erase i)) I.1
          (x ⟨Function.update I.1 k ((I.1 k).erase i), h⟩)
      else 0 := by
  unfold KH.cechD
  rw [LinearMap.pi_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> rfl


open Classical in
theorem combD_apply (J : ∀ k, Finset (ι k)) (n : ℕ) (f : CombC S J n) (I : CombCell ι J (n + 1)) :
    combD S J n f I = ∑ k, ∑ i ∈ I.1.1 k,
      if h : ((∀ l, (Function.update I.1.1 k ((I.1.1 k).erase i) l).Nonempty) ∧
          ∑ l, ((Function.update I.1.1 k ((I.1.1 k).erase i) l).card - 1) = n) ∧
          ∀ l, J l ⊆ Function.update I.1.1 k ((I.1.1 k).erase i) l then
        KH.faceSign I.1.1 k i • f ⟨⟨Function.update I.1.1 k ((I.1.1 k).erase i), h.1⟩, h.2⟩
      else 0 := by
  unfold combD
  rw [LinearMap.pi_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> rfl

theorem embed_comm (a : (Σ k, ι k) → ℤ) (n : ℕ) (f : CombC S (negSet a) n) :
    KH.cechD S ι (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) n (embed S a n f) =
      embed S a (n + 1) (combD S (negSet a) n f) := by
  classical
  funext I
  rw [cechD_apply, embed_apply]
  by_cases hI : ∀ k, negSet a k ⊆ I.1 k
  · rw [dite_eq_left hI]
    erw [combD_apply]
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hc : (∀ l, (Function.update I.1 k ((I.1 k).erase i) l).Nonempty) ∧
        ∑ l, ((Function.update I.1 k ((I.1 k).erase i) l).card - 1) = n
    · rw [dite_eq_left hc]
      erw [embed_apply]
      by_cases hJ : ∀ l, negSet a l ⊆ Function.update I.1 k ((I.1 k).erase i) l
      · rw [dite_eq_left hJ, dite_eq_left ⟨hc, hJ⟩, LinearMap.map_smul_of_tower,
          cellRes_monoFrac (update_erase_subset I.1 k i) a hJ, smul_assoc]
      · rw [dite_eq_right hJ, dite_eq_right (fun h => hJ h.2), map_zero]
        simp
    · rw [dite_eq_right hc, dite_eq_right (fun h => hc h.1), zero_smul]
  · rw [dite_eq_right hI]
    refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun i _ => ?_
    split_ifs with hc
    · erw [embed_apply]
      rw [dite_eq_right (fun hJ => hI fun l => (hJ l).trans (update_erase_subset I.1 k i l)), map_zero]
      simp
    · rfl

theorem embed_mem (a : (Σ k, ι k) → ℤ) (c d : K → ℤ) (h : blockSum a = c + d) (n : ℕ)
    (f : CombC S (negSet a) n) :
    embed S a n f ∈ KH.cechCc ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) c n := by
  classical
  unfold KH.cechCc
  refine Submodule.mem_pi.mpr fun I _ => ?_
  erw [embed_apply]
  split_ifs with hI
  · refine Submodule.smul_mem _ _ ?_
    unfold monoFrac
    rw [dite_eq_left hI]
    refine Submodule.subset_span ⟨_, _, fun k => ∑ i, negExp a ⟨k, i⟩,
      isMultiHomog_monomial _ _ _ fun _ => rfl, ?_, rfl⟩
    refine mk_posExp_mem a _ fun k => ?_
    have hk := blockSum_add_negExp a k
    rw [h] at hk
    simp only [Pi.add_apply] at hk ⊢
    linarith
  · exact zero_mem _

theorem monoFrac_of_nonneg (a : (Σ k, ι k) → ℤ) (ha : ∀ p, 0 ≤ a p) :
    ∃ m ∈ KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (blockSum a),
      ∀ I : ∀ k, Finset (ι k), monoFrac S I a = LocalizedModule.mk m 1 := by
  classical
  have hneg : ∀ k, negSet a k = ∅ := fun k =>
    Finset.filter_eq_empty_iff.mpr fun i _ => not_lt.mpr (ha _)
  have hnegExp : negExp a = 0 := by
    ext p
    simp only [negExp, Finsupp.coe_equivFunOnFinite_symm, Finsupp.coe_zero, Pi.zero_apply]
    have := ha p
    omega
  refine ⟨_, mk_posExp_mem a _ fun k => ?_, fun I => ?_⟩
  · have hk := blockSum_add_negExp a k
    rw [hnegExp] at hk
    simpa using hk
  · have hI : ∀ k, negSet a k ⊆ I k := fun k => by rw [hneg k]; exact Finset.empty_subset _
    unfold monoFrac
    rw [dite_eq_left hI]
    congr 1
    exact Subtype.ext (by simp [hnegExp])

theorem full : KHFreeEmbed.Statement := by
  intro S _ K _ _ ι _ _ a
  exact ⟨fun n f => embed_comm a n f, fun c d h n f => embed_mem a c d h n f, monoFrac_of_nonneg a⟩

end KHFreeEmbed

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section Lemmas

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]


omit [Module S E] [IsScalarTower S Ω E] in
theorem twist_sub_mono {F G : SubSystem S x E} (h : ∀ I, F.sub I ≤ G.sub I) (Q : SubSystem S x Ω)
    (I : Chart x) : (F.twist Q).sub I ≤ (G.twist Q).sub I :=
  Submodule.span_mono fun _ ⟨q, hq, y, hy, hz⟩ => ⟨q, hq, y, h I hy, hz⟩


omit [Module S E] [IsScalarTower S Ω E] in
theorem twistPows_sub_mono {F G : SubSystem S x E} (h : ∀ I, F.sub I ≤ G.sub I) :
    ∀ (t : ℕ) (L : Fin t → SubSystem S x Ω) (n : Fin t → ℕ) (I : Chart x),
      (F.twistPows t L n).sub I ≤ (G.twistPows t L n).sub I
  | 0, _, _, I => h I
  | t + 1, _, _, I => twist_sub_mono (twistPows_sub_mono h t _ _) _ I

theorem exists_subFamily_twistPows (hB : SubFamilyTwist.Statement.{u, v, w}) (F : SubFamily S x E)
    (hF : ∀ I, (F.sub I).FG) : ∀ (t : ℕ) (L : Fin t → LineBundle S x) (n : Fin t → ℕ),
      ∃ H : SubFamily S x E, H.toSubSystem = F.toSubSystem.twistPows t (fun j => (L j).toSubSystem) n ∧
        ∀ I, (H.sub I).FG := by
  intro t
  induction t with
  | zero => exact fun _ _ => ⟨F, rfl, hF⟩
  | succ t ih =>
    intro L n
    obtain ⟨H, hH, hHfg⟩ := ih (fun j => L j.castSucc) (fun j => n j.castSucc)
    obtain ⟨P, hP⟩ := exists_lineBundle_twistMul (L (Fin.last t)) (n (Fin.last t)) 0
    obtain ⟨G, hG, hGfg⟩ := hB S Ω N x E H P hHfg
    refine ⟨G, ?_, hGfg⟩
    rw [hG, hP, hH, twistMul, SubSystem.twist_twistSys_zero]
    rfl

end Lemmas

theorem SnapperQuotDevissage.proof (hF : SnapperQuotFilt.Statement.{u, v, w})
    (hI : SnapperQuotIso.Statement.{u, v, w, w}) (hA : SnapperQuotAdd.Statement.{u, v, w})
    (hB : SubFamilyTwist.Statement.{u, v, w}) : SnapperQuotDevissage.Statement.{u, v, w} := by
  intro k _ Ω _ _ N x E _ _ _ _ F₁ F₂ hfg hle J hJ hxJ hJF
  obtain ⟨r, G, pp, a, hGfg, hG0, hGr, hmono, hpp, hiso⟩ := hF k Ω N x E F₁ F₂ hfg hle J hJ hxJ hJF
  refine ⟨r, pp, a, hpp, fun t L n c => ?_⟩
  have hH : ∀ m, ∃ H : SubFamily k x E, H.toSubSystem =
      ((G m).toSubSystem.twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c) ∧
        ∀ I, (H.sub I).FG := fun m => by
    obtain ⟨H, hH, hHfg⟩ := exists_subFamily_twistPows hB (G m) (hGfg m) t L n
    obtain ⟨H', hH', hH'fg⟩ := hB k Ω N x E H (twistBundle k x c) hHfg
    exact ⟨H', by rw [hH', hH]; rfl, hH'fg⟩
  choose H hHeq hHfg using hH
  have hHmono : ∀ m < r, ∀ I, (H m).sub I ≤ (H (m + 1)).sub I := fun m hm I => by
    rw [hHeq, hHeq]
    exact twist_sub_mono (twistPows_sub_mono (hmono m hm) t _ n) _ I
  have hstep : ∀ m (hm : m < r), eulerCharQuot k (H (m + 1)).toSubSystem (H m).toSubSystem =
      pieceChar k (pp ⟨m, hm⟩) (a ⟨m, hm⟩) L n c := fun m hm => by
    rw [hHeq, hHeq]
    exact hI k Ω N x E Ω _ _ _ _ (hiso ⟨m, hm⟩ t L n c).some
  have key : ∀ m ≤ r, (∀ I, (H 0).sub I ≤ (H m).sub I) ∧
      eulerCharQuot k (H m).toSubSystem (H 0).toSubSystem =
        ∑ i ∈ Finset.range m, (if h : i < r then pieceChar k (pp ⟨i, h⟩) (a ⟨i, h⟩) L n c else 0) := by
    intro m
    induction m with
    | zero => exact fun _ => ⟨fun I => le_rfl, by simp [eulerCharQuot_self]⟩
    | succ m ih =>
      intro hm
      obtain ⟨h0, hχ⟩ := ih (by omega)
      refine ⟨fun I => (h0 I).trans (hHmono m (by omega) I), ?_⟩
      rw [hA k Ω N x E (H (m + 1)) (H m) (H 0) (hHfg _) (hHmono m (by omega)) h0, hχ,
        hstep m (by omega), Finset.sum_range_succ, dite_eq_left (by omega), add_comm]
  rw [← hGr, ← hG0, ← hHeq r, ← hHeq 0, (key r le_rfl).2, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun i _ => by simp [i.2]

end

end GroundTheory.Heights₂.Heights.Kleiman
end
