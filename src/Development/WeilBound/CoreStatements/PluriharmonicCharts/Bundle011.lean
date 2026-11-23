module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.FiniteEtaleSurjectiveOfPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle120
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle090
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle049
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle090
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle026
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv

@[expose] public section

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open GroundTheory.Heights₂.Heights.LowerBoundFree

namespace PositivityTheory.Xgp.c_bm_exists_local

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

def HoldsOff (Q₀ : Ideal (MRing J)) (G : Ideal (MRing J) → Prop) : Prop :=
  ∃ (d : K → ℕ) (h : MRing J), IsMultiHomog h d ∧ h ∉ Q₀ ∧ ∀ Q : Ideal (MRing J), h ∉ Q → G Q

variable {Q₀ : Ideal (MRing J)}

theorem HoldsOff.mono {G G' : Ideal (MRing J) → Prop} (h : HoldsOff Q₀ G) (hG : ∀ Q, G Q → G' Q) :
    HoldsOff Q₀ G' :=
  let ⟨d, f, h1, h2, h3⟩ := h
  ⟨d, f, h1, h2, fun Q hQ => hG Q (h3 Q hQ)⟩

theorem holdsOff_of_forall (hQ : Q₀.IsPrime) {G : Ideal (MRing J) → Prop} (h : ∀ Q, G Q) : HoldsOff Q₀ G :=
  ⟨0, 1, GroundTheory.Heights₂.Heights.Inter.AvoidRing.isMultiHomog_one, (Ideal.ne_top_iff_one _).1 hQ.ne_top, fun Q _ => h Q⟩

theorem HoldsOff.and (hQ : Q₀.IsPrime) {G G' : Ideal (MRing J) → Prop} (h : HoldsOff Q₀ G) (h' : HoldsOff Q₀ G') :
    HoldsOff Q₀ fun Q => G Q ∧ G' Q := by
  obtain ⟨d, f, h1, h2, h3⟩ := h
  obtain ⟨d', f', h1', h2', h3'⟩ := h'
  exact ⟨d + d', f * f', GroundTheory.Heights₂.Heights.Inter.AvoidRing.isMultiHomog_mul h1 h1', fun h => (hQ.mem_or_mem h).elim h2 h2',
    fun Q h => ⟨h3 Q fun a => h (Q.mul_mem_right _ a), h3' Q fun a => h (Q.mul_mem_left _ a)⟩⟩

theorem holdsOff_forall (hQ : Q₀.IsPrime) {α : Type} [Finite α] {G : α → Ideal (MRing J) → Prop}
    (h : ∀ a, HoldsOff Q₀ (G a)) : HoldsOff Q₀ fun Q => ∀ a, G a Q := by
  classical
  haveI := Fintype.ofFinite α
  have key : ∀ s : Finset α, HoldsOff Q₀ fun Q => ∀ a ∈ s, G a Q := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact holdsOff_of_forall hQ (by simp)
    | insert a s _ ih =>
      refine (HoldsOff.and hQ (h a) ih).mono fun Q hh b hb => ?_
      rcases Finset.mem_insert.1 hb with rfl | hb
      · exact hh.1
      · exact hh.2 b hb
  exact (key Finset.univ).mono fun Q hh a => hh a (Finset.mem_univ a)

theorem holdsOff_regAt {Ω : Type} [Field Ω] {x : (Σ k, J k) → Ω} {s : Ω} (h : RegAt x Q₀ s) :
    HoldsOff Q₀ fun Q => RegAt x Q s :=
  let ⟨d, g, t, hg, ht, h0, e⟩ := h
  ⟨d, t, ht, h0, fun _ hQ => ⟨d, g, t, hg, ht, hQ, e⟩⟩

theorem inBlockChart_of_inChart {Z : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ Z}
    {x : (Σ k, J k) → Ω} {c : ∀ k, J k} {q : Cpt ξ} (h : InChart ξ (segreCoord x) c q) : InBlockChart ξ x c q := by
  classical
  obtain ⟨h0, hc⟩ := h
  have h1 : ∀ k, x ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 h0 k (Finset.mem_univ k)
  refine fun k => ⟨h1 k, fun i => ?_⟩
  convert hc (Function.update c k i) using 1
  unfold segreCoord
  rw [← Finset.prod_div_distrib, Finset.prod_eq_single k]
  · simp
  · intro k' _ hk
    rw [Function.update_of_ne hk, div_self (h1 k')]
  · simp

theorem exists_frameDomain {Z : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ Z}
    {x : (Σ k, J k) → Ω} (tie : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, x ⟨k, c' k⟩)
    {z : Spec (CommRingCat.of ℂ) ⟶ Z} {w : (Σ k, J k) → ℂ} (hz : genPt ξ ⤳ centre z) (hw : CoordsAt ξ x z w)
    {c : ∀ k, J k} (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) {G : Ideal (MRing J) → Prop} (hG : HoldsOff (mCoordIdeal w) G) :
    ∃ f : Ω, InFrameDomain x c f w ∧
      ∀ p : Cpt ξ, InChart ξ (segreCoord x) c p → unitAt ξ p f → InBlockChart ξ x c p ∧ G (ptIdeal ξ x p) := by
  obtain ⟨d, h, hd, h0, hG⟩ := hG
  refine ⟨MvPolynomial.aeval x h / ∏ k, x ⟨k, c k⟩ ^ d k, ⟨hc, _,
    (GlobalTheory.T.valAt_iff_value_at Z Ω ξ K J x tie z w hz hw _ _).1 (valAt_form hw hz hc hd), ?_⟩, fun p hp hu => ?_⟩
  · rw [form_mem_mCoordIdeal_iff w hd] at h0
    exact div_ne_zero h0 (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k))
  · have hb := inBlockChart_of_inChart hp
    refine ⟨hb, hG _ ?_⟩
    obtain ⟨R, _, z', w', e, hw', -⟩ := exists_ptIdeal_eq tie p
    have hz' : genPt ξ ⤳ centre z' := e ▸ p.2
    obtain rfl : p = ⟨centre z', hz'⟩ := Subtype.ext e.symm
    have hc' := (inBlockChart_centre_iff hw' hz' c).1 hb
    rw [ptIdeal_centre hw' hz', form_mem_mCoordIdeal_iff w' hd]
    rw [unitAt_iff_of_valAt (valAt_form hw' hz' hc' hd) hz'] at hu
    intro h1
    exact hu (by rw [h1, zero_div])

theorem exists_goodDomain {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
    {y : (Σ k, ι k) → Φ} {Ψ : Type} [Finite Ψ] {N j : ℕ} (M : FlagModel y Ψ N j)
    (F : FrameData ι Ψ N M.Ω M.blk) {Z : Scheme.{0}} {ξ : Spec (CommRingCat.of M.Ω) ⟶ Z}
    (tie : CoordTie ℤ ξ fun c' : (k : NonPluckerBlocks M.blk) → baseIdx ι M.blk k => ∏ k, M.x ⟨k, c' k⟩)
    {z : Spec (CommRingCat.of ℂ) ⟶ Z} {w : (Σ k, baseIdx ι M.blk k) → ℂ} (hz : genPt ξ ⤳ centre z)
    (hw : CoordsAt ξ M.x z w) (hF : M.GoodAt F (mCoordIdeal w)) :
    ∃ f : M.Ω, InFrameDomain M.x F.c f w ∧
      ∀ p : Cpt ξ, InChart ξ (segreCoord M.x) F.c p → unitAt ξ p f → M.GoodAt F (ptIdeal ξ M.x p) := by
  have hP : (mCoordIdeal w).IsPrime := RingHom.ker_isPrime _
  have hc : ∀ k, w ⟨k, F.c k⟩ ≠ 0 := by
    refine (inBlockChart_centre_iff hw hz F.c).1 ((inBlockChart_iff_X_notMem tie _ F.c).2 ?_)
    rw [ptIdeal_centre hw hz]
    exact hF.1
  have h1 : HoldsOff (mCoordIdeal w) fun Q => ∀ q I, RegAt M.x Q (F.u q I) ∧ RegAt M.x Q (F.u' I q) :=
    holdsOff_forall hP fun q => holdsOff_forall hP fun I =>
      HoldsOff.and hP (holdsOff_regAt (hF.2.1 q I).1) (holdsOff_regAt (hF.2.1 q I).2)
  have h2 : HoldsOff (mCoordIdeal w) fun Q => ∀ p, M.blk p = none →
      F.υ p ≠ 0 ∧ RegAt M.x Q (F.υ p) ∧ RegAt M.x Q (F.υ p)⁻¹ := by
    refine holdsOff_forall hP fun p => ?_
    by_cases hp : M.blk p = none
    · obtain ⟨a, b, c⟩ := hF.2.2 p hp
      exact (HoldsOff.and hP (holdsOff_regAt b) (holdsOff_regAt c)).mono fun Q h _ => ⟨a, h⟩
    · exact holdsOff_of_forall hP fun Q h => absurd h hp
  obtain ⟨f, hf, hg⟩ := exists_frameDomain tie hz hw hc (HoldsOff.and hP h1 h2)
  exact ⟨f, hf, fun p a b => ⟨(inBlockChart_iff_X_notMem tie p F.c).1 (hg p a b).1, (hg p a b).2⟩⟩

end PositivityTheory.Xgp.c_bm_exists_local
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem PositivityTheory.Xgp.t_deg_generic : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : IFamily ℚ ι), IsFieldIntersection I → ∀ (D : ℕ) (P : Ideal (MRing ι)) (L : Fin D → HermLine ι), IsArithVar P (D + 1) → (∀ j, IsSmoothHerm (L j)) → ptsIntegral P (pot L) (fun _ => 1) = (I (P.map (MvPolynomial.map (Int.castRingHom ℚ))) D fun j => (L j).a : ℤ) := by
  intro hI K _ ι _ I hF D P L hP hL
  classical
  obtain ⟨I₀, -, hu⟩ := GroundTheory.Heights₂.Heights.Targets.ExistsUnique.full ℚ ι
  have hQ := GroundTheory.Heights₂.Heights.HilbertSamuel.isProjVarF_map_of_isArithVar hP
  have h1 := hu I hF _ D (fun j => (L j).a) hQ
  have h2 := hu _ (GroundTheory.Heights₂.Heights.NumbersDVR.IntNumIsFieldIntersection.full ℚ K ι) _ D (fun j => (L j).a) hQ
  rw [h1, ← h2]
  exact GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree hI.degree K ι P D L hP hL
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section
namespace PositivityTheory.Xgp.c_algsq

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def κ₁ (k₀ : K) (k : K) : Option K := if k = k₀ then none else some k

theorem κ₁_self (k₀ : K) : κ₁ k₀ k₀ = none := if_pos rfl

theorem κ₁_ne {k₀ k : K} (h : k ≠ k₀) : κ₁ k₀ k = some k := if_neg h

theorem κ₁_inj (k₀ : K) : Function.Injective (κ₁ k₀) := by
  intro a b h
  unfold κ₁ at h
  split_ifs at h with ha hb hb <;>
    first
    | exact ha.trans hb.symm
    | (cases h; rfl)
    | cases h
    | exact Option.some_injective _ h

theorem isBlockMap_v₁ (k₀ : K) :
    IsBlockMap (ι := ι) (ι' := fun o : Option K => ι (o.getD k₀)) (κ₁ k₀) (v₁ k₀) := by
  have h3 : ∀ p : (k : K) × ι k, (v₁ k₀ p).fst = κ₁ k₀ p.fst := fun p => by
    unfold v₁ κ₁
    split_ifs <;> rfl
  refine ⟨κ₁_inj k₀, ?_, h3, ?_⟩
  · rintro ⟨a, x⟩ ⟨b, y⟩ h
    have hfst : κ₁ k₀ a = κ₁ k₀ b := by
      have e := congrArg Sigma.fst h
      rwa [h3, h3] at e
    have hab : a = b := κ₁_inj k₀ hfst
    subst hab
    unfold v₁ at h
    split_ifs at h with ha
    · have h2 := (Sigma.mk.inj_iff.mp h).2
      obtain rfl := eq_of_heq ((cast_heq _ x).symm.trans (h2.trans (cast_heq _ y)))
      rfl
    · have h2 := (Sigma.mk.inj_iff.mp h).2
      obtain rfl := eq_of_heq h2
      rfl
  · rintro ⟨o, x⟩ ⟨j, hj⟩
    cases o with
    | none =>
      refine ⟨⟨k₀, x⟩, ?_⟩
      unfold v₁
      rw [dite_eq_left rfl]
      rfl
    | some k =>
      have hk : k ≠ k₀ := by
        intro hk
        unfold κ₁ at hj
        split_ifs at hj with h1 <;>
          first
          | (cases hj; exact h1 hk)
          | cases hj
          | exact h1 ((Option.some_injective _ hj).trans hk)
      refine ⟨⟨k, x⟩, ?_⟩
      unfold v₁
      rw [dite_eq_right hk]

theorem pullDeg_some (xi : K → ℤ) (o : Option K) : pullDeg (some : K → Option K) xi o = o.elim 0 xi := by
  unfold pullDeg
  cases o with
  | none =>
    have hn : ¬∃ a : K, some a = (none : Option K) := by
      rintro ⟨a, ha⟩
      cases ha
    rw [Function.extend_apply' _ _ _ hn]
    rfl
  | some k =>
    exact (Option.some_injective K).extend_apply xi 0 k

theorem pullDeg_κ₁ (k₀ : K) (xi : K → ℤ) (o : Option K) :
    pullDeg (κ₁ k₀) xi o = o.elim (xi k₀) fun k => if k = k₀ then 0 else xi k := by
  unfold pullDeg
  cases o with
  | none =>
    have e := (κ₁_inj k₀).extend_apply xi 0 k₀
    rw [κ₁_self] at e
    exact e
  | some k =>
    by_cases hk : k = k₀
    · have hn : ¬∃ j : K, κ₁ k₀ j = some k := by
        rintro ⟨j, hj⟩
        unfold κ₁ at hj
        split_ifs at hj with h1 <;>
          first
          | (cases hj; exact h1 hk)
          | cases hj
          | exact h1 ((Option.some_injective _ hj).trans hk)
      rw [Function.extend_apply' _ _ _ hn]
      simp [hk]
    · have e := (κ₁_inj k₀).extend_apply xi 0 k
      rw [κ₁_ne hk] at e
      rw [e]
      simp [hk]

end PositivityTheory.Xgp.c_algsq
end
end
