module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle022
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle025
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w v₁ v₂ v₃

namespace Cech

variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R]
  {A : Cell U → Type v₁} [∀ I, AddCommGroup (A I)] [∀ I, Module R (A I)]
  {B : Cell U → Type v₂} [∀ I, AddCommGroup (B I)] [∀ I, Module R (B I)]
  {C : Cell U → Type v₃} [∀ I, AddCommGroup (C I)] [∀ I, Module R (C I)]



theorem finite_H_zero_of_exact [IsNoetherianRing R]
    (ρA : ∀ I J : Cell U, I.1 ⊆ J.1 → A I →ₗ[R] A J) (ρB : ∀ I J : Cell U, I.1 ⊆ J.1 → B I →ₗ[R] B J)
    (ρC : ∀ I J : Cell U, I.1 ⊆ J.1 → C I →ₗ[R] C J)
    (hρB : ∀ (I J K : Cell U) (h : I.1 ⊆ J.1) (h' : J.1 ⊆ K.1) (m : B I),
      ρB J K h' (ρB I J h m) = ρB I K (h.trans h') m)
    (ι : ∀ I, A I →ₗ[R] B I) (q : ∀ I, B I →ₗ[R] C I)
    (hι : ∀ I J h m, ι J (ρA I J h m) = ρB I J h (ι I m))
    (hq : ∀ I J h m, q J (ρB I J h m) = ρC I J h (q I m))
    (hinj : ∀ I, Function.Injective (ι I)) (hsurj : ∀ I, Function.Surjective (q I))
    (hex : ∀ I b, q I b = 0 ↔ ∃ a, ι I a = b)
    (hB : Module.Finite R (H B ρB 0)) (hA : Module.Finite R (H A ρA 1)) :
    Module.Finite R (H C ρC 0) := by
  have := hA
  have hιd := mapC_d (R := R) (G := A) (G' := B) ι hι
  have hqd := mapC_d (R := R) (G := B) (G' := C) q hq
  have hιinj : ∀ i, Function.Injective (mapC (R := R) (G := A) (G' := B) ι i) := fun i a b hab =>
    _root_.funext fun I => hinj I.1 (congrFun hab I)
  have hq0 : ∀ i (c : Cochain B i), mapC (R := R) (G := B) (G' := C) q i c = 0 ↔
      ∃ a, mapC (R := R) (G := A) (G' := B) ι i a = c := fun i c => by
    constructor
    · intro h
      choose a ha using fun I => (hex I.1 (c I)).mp (congrFun h I)
      exact ⟨a, _root_.funext ha⟩
    · rintro ⟨a, rfl⟩
      exact _root_.funext fun I => (hex I.1 _).mpr ⟨a I, rfl⟩

  obtain ⟨P, hP⟩ : ∃ P : Submodule R (Cochain B 0), ∀ w, w ∈ P ↔
      mapC (R := R) (G := B) (G' := C) q 1 (d B ρB 0 w) = 0 :=
    ⟨LinearMap.ker ((mapC (R := R) (G := B) (G' := C) q 1).comp (d B ρB 0)), fun _ => LinearMap.mem_ker⟩

  obtain ⟨θ, hθ0, hθs⟩ : ∃ θ : P →ₗ[R] H C ρC 0,
      (∀ p, θ p = 0 ↔ mapC (R := R) (G := B) (G' := C) q 0 p.1 = 0) ∧ Function.Surjective θ := by
    have hk : ∀ p : P, mapC (R := R) (G := B) (G' := C) q 0 p.1 ∈ LinearMap.ker (d C ρC 0) := fun p => by
      rw [LinearMap.mem_ker, ← hqd 0]; exact (hP p.1).mp p.2
    refine ⟨(Submodule.mkQ _).comp (LinearMap.codRestrict _
      ((mapC (R := R) (G := B) (G' := C) q 0).comp P.subtype) hk), fun p => ?_, fun h => ?_⟩
    · change Submodule.Quotient.mk _ = 0 ↔ _
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      exact Submodule.mem_bot R
    · obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ h
      choose w hw using fun I : Idx U 0 => hsurj I.1 (c.1 I)
      have hmw : mapC (R := R) (G := B) (G' := C) q 0 w = c.1 := _root_.funext hw
      refine ⟨⟨w, (hP w).mpr (by rw [hqd 0, hmw]; exact c.2)⟩, ?_⟩
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk c
      congr 1
      exact Subtype.ext hmw

  have hdP : ∀ p : P, d B ρB 0 p.1 ∈ LinearMap.range (mapC (R := R) (G := A) (G' := B) ι 1) := fun p =>
    LinearMap.mem_range.mpr ((hq0 1 _).mp ((hP p.1).mp p.2))
  obtain ⟨g, hg⟩ : ∃ g : P →ₗ[R] Cochain A 1,
      ∀ p, mapC (R := R) (G := A) (G' := B) ι 1 (g p) = d B ρB 0 p.1 :=
    ⟨(LinearEquiv.ofInjective _ (hιinj 1)).symm.toLinearMap.comp
        (LinearMap.codRestrict _ ((d B ρB 0).comp P.subtype) hdP),
      fun p => congrArg Subtype.val ((LinearEquiv.ofInjective _ (hιinj 1)).apply_symm_apply _)⟩
  have hgk : ∀ p : P, g p ∈ LinearMap.ker (d A ρA 1) := fun p =>
    LinearMap.mem_ker.mpr (hιinj (1 + 1) ((hιd 1 (g p)).trans (by
      rw [hg, d_one_d_zero hρB, map_zero])))
  obtain ⟨ψ, hψ0⟩ : ∃ ψ : P →ₗ[R] H A ρA 1, ∀ p, ψ p = 0 ↔ ∃ g', d A ρA 0 g' = g p :=
    ⟨(Submodule.mkQ _).comp (LinearMap.codRestrict _ g hgk), fun p => by
      change Submodule.Quotient.mk _ = 0 ↔ _
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      exact LinearMap.mem_range⟩
  have hle : LinearMap.ker θ ≤ LinearMap.ker ψ := fun p hp => by
    obtain ⟨a, ha⟩ := (hq0 0 _).mp ((hθ0 p).mp hp)
    refine (hψ0 p).mpr ⟨a, hιinj 1 ?_⟩
    rw [hg, hιd 0, ha]

  let f := (LinearMap.ker θ).liftQ ψ hle
  have hZP : LinearMap.ker (d B ρB 0) ≤ P := fun z hz =>
    (hP z).mpr (by rw [LinearMap.mem_ker.mp hz, map_zero])
  let j := (LinearMap.ker θ).mkQ.comp (Submodule.inclusion hZP)
  have hker : LinearMap.ker f = LinearMap.range j := by
    apply le_antisymm
    · intro m hm
      obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ m
      have hm' : ψ p = 0 := hm
      obtain ⟨g', hg'⟩ := (hψ0 p).mp hm'
      have hz : p.1 - mapC (R := R) (G := A) (G' := B) ι 0 g' ∈ LinearMap.ker (d B ρB 0) := by
        rw [LinearMap.mem_ker, map_sub, ← hιd 0, hg', hg, sub_self]
      have hqι : mapC (R := R) (G := B) (G' := C) q 0 (mapC (R := R) (G := A) (G' := B) ι 0 g') = 0 :=
        (hq0 0 _).mpr ⟨g', rfl⟩
      refine ⟨⟨_, hz⟩, (Submodule.Quotient.eq _).mpr ((hθ0 _).mpr ?_)⟩
      change mapC (R := R) (G := B) (G' := C) q 0
        (p.1 - mapC (R := R) (G := A) (G' := B) ι 0 g' - p.1) = 0
      rw [sub_sub_cancel_left, map_neg, hqι, neg_zero]
    · rintro _ ⟨z, rfl⟩
      show ψ (Submodule.inclusion hZP z) = 0
      refine (hψ0 _).mpr ⟨0, hιinj 1 ?_⟩
      rw [map_zero, map_zero, hg]
      exact (LinearMap.mem_ker.mp z.2).symm

  have hZfin : Module.Finite R (LinearMap.ker (d B ρB 0)) := by
    have : Module.Finite R (LinearMap.ker (d B ρB 0) ⧸
        (bdry B ρB 0).comap (LinearMap.ker (d B ρB 0)).subtype) := hB
    exact Module.Finite.equiv (Submodule.quotEquivOfEqBot
      ((bdry B ρB 0).comap (LinearMap.ker (d B ρB 0)).subtype) (eq_bot_iff.mpr fun z hz =>
      (Submodule.mem_bot R).mpr (Subtype.ext ((Submodule.mem_bot R).mp
        (show (z : Cochain B 0) ∈ (⊥ : Submodule R (Cochain B 0)) from hz)))))
  have hM : Module.Finite R (P ⧸ LinearMap.ker θ) := by
    refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker f (IsNoetherian.noetherian _) ?_⟩
    rw [top_inf_eq, hker, LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map j
  exact Module.Finite.equiv (θ.quotKerEquivOfSurjective hθs)

end Cech

theorem QuotientH0Finite.proof : QuotientH0Finite.Statement.{u, v, w} := by
  intro S _ _ Ω _ _ N x E _ _ _ _ F G hGF hF hG
  have key := Cech.finite_H_zero_of_exact (A := fun I => ↥(G.sub I)) (B := fun I => ↥(F.sub I))
    (C := fun I => ↥(F.sub I) ⧸ SubSystem.quotSub F G I) G.res F.res (SubSystem.quotRes F G)
    (fun _ _ _ _ _ _ => rfl)
    (fun I => { toFun := fun y => ⟨y, hGF I y.2⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl })
    (fun I => (SubSystem.quotSub F G I).mkQ) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun I a b hab => Subtype.ext (congrArg (fun y : F.sub I => (y : E)) hab))
    (fun I => Submodule.mkQ_surjective _)
    (fun I b => ⟨fun h => ⟨⟨b, (Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F G I)).mp h⟩, rfl⟩,
      fun ⟨a, ha⟩ => (Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F G I)).mpr (ha ▸ a.2)⟩)
    hF hG
  exact key

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH

namespace CellZeroConst

variable {K : Type} [Fintype K] {ι : K → Type}

def pt (c : ∀ k, ι k) : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0 :=
  ⟨fun k => {c k}, fun _ => Finset.singleton_nonempty _, by simp⟩

theorem exists_pt (c : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0) : ∃ d : ∀ k, ι k, c = pt d := by
  have h1 : ∀ k, (c.1 k).card = 1 := by
    intro k
    have hk : (c.1 k).card - 1 = 0 := (Finset.sum_eq_zero_iff.mp c.2.2) k (Finset.mem_univ _)
    have := (c.2.1 k).card_pos
    omega
  choose d hd using fun k => Finset.card_eq_one.mp (h1 k)
  exact ⟨d, Subtype.ext (funext hd)⟩

theorem cellMeets_pt {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) :
    CellMeets y (pt c).1 ↔ ∀ k, y ⟨k, c k⟩ ≠ 0 := by
  simp [CellMeets, pt]

variable [LinearOrder K] [∀ k, LinearOrder (ι k)]

theorem edge (S : Type) [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)
    (s : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0 → Ω) (hs : cellD S y 0 s = 0) (d : ∀ k, ι k) (k : K)
    {i i' : ι k} (hii : i < i') (hd : ∀ l, l ≠ k → y ⟨l, d l⟩ ≠ 0) (hi : y ⟨k, i⟩ ≠ 0)
    (hi' : y ⟨k, i'⟩ ≠ 0) :
    s (pt (Function.update d k i)) = s (pt (Function.update d k i')) := by
  classical
  have hne : i ≠ i' := hii.ne
  obtain ⟨J, hJk, hJl⟩ : ∃ J : ∀ l, Finset (ι l), J k = {i, i'} ∧ ∀ l, l ≠ k → J l = {d l} :=
    ⟨Function.update (fun l => {d l}) k {i, i'}, by simp, fun l hl => by simp [hl]⟩
  have hJ1 : (∀ l, (J l).Nonempty) ∧ ∑ l, ((J l).card - 1) = 0 + 1 := by
    refine ⟨fun l => ?_, ?_⟩
    · by_cases hl : l = k
      · subst hl; simp [hJk]
      · simp [hJl l hl]
    · rw [Finset.sum_eq_single k (fun l _ hl => by simp [hJl l hl]) (by simp)]
      simp [hJk, Finset.card_pair hne]
  have hm : CellMeets y J := by
    intro l j hj
    by_cases hl : l = k
    · subst hl
      rw [hJk] at hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl <;> assumption
    · rw [hJl l hl, Finset.mem_singleton] at hj
      subst hj
      exact hd l hl

  have hface : ∀ a b : ι k, J k = {a, b} → a ≠ b →
      Function.update J k ((J k).erase a) = (pt (Function.update d k b)).1 := by
    intro a b hab habn
    funext l
    by_cases hl : l = k
    · subst hl
      simp [pt, hab, habn]
    · simp [pt, hl, hJl l hl]
  have hfa := hface i i' hJk hne
  have hfb := hface i' i (by rw [hJk, Finset.pair_comm]) hne.symm
  have hlow : ∑ l ∈ Finset.univ.filter (· < k), ((J l).card - 1) = 0 :=
    Finset.sum_eq_zero fun l hl => by
      rw [hJl l (ne_of_lt (Finset.mem_filter.mp hl).2)]
      simp
  have hsa : faceSign J k i = 1 := by
    unfold faceSign
    rw [hlow, hJk]
    simp [Finset.filter_insert, Finset.filter_singleton, not_lt_of_gt hii]
  have hsb : faceSign J k i' = -1 := by
    unfold faceSign
    rw [hlow, hJk]
    simp [Finset.filter_insert, Finset.filter_singleton, hii]
  have h0 : cellD S y 0 s ⟨J, hJ1⟩ = 0 := by rw [hs]; rfl
  unfold cellD at h0
  erw [LinearMap.pi_apply] at h0
  erw [if_pos (show CellMeets y J from hm)] at h0
  rw [LinearMap.sum_apply, Finset.sum_eq_single k] at h0
  rotate_left
  · intro l _ hl
    rw [LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [dite_eq_right]
    · rfl
    rintro ⟨hn, -⟩
    have h2 := hn l
    rw [Function.update_self] at h2
    change j ∈ J l at hj
    rw [hJl l hl, Finset.mem_singleton] at hj
    subst hj
    change ((J l).erase (d l)).Nonempty at h2
    rw [hJl l hl] at h2
    simp at h2
  · simp
  rw [LinearMap.sum_apply, Finset.sum_eq_add i i' hne] at h0
  rotate_left
  · intro j hj hj2
    change j ∈ J k at hj
    rw [hJk] at hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact absurd rfl hj2.1
    · exact absurd rfl hj2.2
  · intro h; exact absurd (show i ∈ J k by rw [hJk]; simp) h
  · intro h; exact absurd (show i' ∈ J k by rw [hJk]; simp) h
  rw [dite_eq_left (hfa ▸ (pt (Function.update d k i')).2), dite_eq_left (hfb ▸ (pt (Function.update d k i)).2)] at h0
  simp only [LinearMap.smul_apply] at h0
  erw [LinearMap.proj_apply, LinearMap.proj_apply] at h0
  have e1 : ∀ h, s ⟨Function.update J k ((J k).erase i), h⟩ = s (pt (Function.update d k i')) :=
    fun _ => congrArg s (Subtype.ext hfa)
  have e2 : ∀ h, s ⟨Function.update J k ((J k).erase i'), h⟩ = s (pt (Function.update d k i)) :=
    fun _ => congrArg s (Subtype.ext hfb)
  rw [hsa, hsb, e1, e2, one_smul, neg_smul, one_smul] at h0
  linear_combination -h0

theorem step (S : Type) [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)
    (s : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0 → Ω) (hs : cellD S y 0 s = 0) (d : ∀ k, ι k)
    (hd : ∀ l, y ⟨l, d l⟩ ≠ 0) (k : K) (j : ι k) (hj : y ⟨k, j⟩ ≠ 0) :
    s (pt d) = s (pt (Function.update d k j)) := by
  classical
  have hdl : ∀ l, l ≠ k → y ⟨l, d l⟩ ≠ 0 := fun l _ => hd l
  rcases lt_trichotomy (d k) j with h | h | h
  · have := edge S y s hs d k h hdl (hd k) hj
    rwa [Function.update_eq_self] at this
  · rw [← h, Function.update_eq_self]
  · have := edge S y s hs d k h hdl hj (hd k)
    rw [Function.update_eq_self] at this
    exact this.symm

theorem chain (S : Type) [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)
    (s : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0 → Ω) (hs : cellD S y 0 s = 0) (d d' : ∀ k, ι k)
    (hd : ∀ l, y ⟨l, d l⟩ ≠ 0) (hd' : ∀ l, y ⟨l, d' l⟩ ≠ 0) :
    s (pt d) = s (pt d') := by
  classical
  have key : ∀ T : Finset K, s (pt d) = s (pt (fun l => if l ∈ T then d' l else d l)) := by
    intro T
    refine Finset.induction_on T ?_ ?_
    · simp
    · intro a T ha ih
      rw [ih]
      have hmeet : ∀ l, y ⟨l, (fun l => if l ∈ T then d' l else d l) l⟩ ≠ 0 := fun l => by
        dsimp only
        split_ifs
        · exact hd' l
        · exact hd l
      rw [step S y s hs _ hmeet a (d' a) (hd' a)]
      congr 2
      funext l
      by_cases hl : l = a
      · subst hl
        simp
      · simp [hl]
  simpa using key Finset.univ

end CellZeroConst

theorem CellZeroConst.proof : CellZeroConst.Statement := by
  intro S _ K _ _ ι _ _ Ω _ _ y s hs c c' hc hc'
  obtain ⟨d, rfl⟩ := CellZeroConst.exists_pt c
  obtain ⟨d', rfl⟩ := CellZeroConst.exists_pt c'
  rw [CellZeroConst.cellMeets_pt] at hc hc'
  exact CellZeroConst.chain S y s hs d d' hc hc'

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

noncomputable section

universe u v w

namespace VeryAmpleZFinite

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {r : ℕ}

theorem ampleBase_le_chartRing {h : Fin (r + 1) → Ω} (J : Chart h) {j : Fin (r + 1)} (hj : j ∈ J.1) :
    ampleBase (S := S) h j ≤ chartRing S h J := by
  rw [ampleBase, Algebra.adjoin_le_iff]
  rintro _ ⟨l, rfl⟩
  exact ⟨MvPolynomial.X l, MvPolynomial.X j, 1, X_mem_monos hj, MvPolynomial.isHomogeneous_X S l,
    MvPolynomial.isHomogeneous_X S j, by simp⟩

end VeryAmpleZFinite


open VeryAmpleZFinite in
theorem VeryAmpleZFinite.proof (hExt : VeryAmpleZExtend.Statement.{u, v, w})
    (hSpan : VeryAmpleZChartSpan.Statement.{u, v, w}) (hRing : VeryAmpleZChartRing.Statement.{u, w}) :
    VeryAmpleZFinite.Statement.{u, v, w} := by
  classical
  intro S _ _ Ω _ _ N x E _ _ _ _ F hF H r h hH J
  obtain ⟨j, hj⟩ := J.2.1
  have hj0 : h j ≠ 0 := (mem_support h).mp (J.2.2 hj)
  have hsec : ∀ l, h l ∈ H.toSubSystem.secs := hH.mem_secs
  obtain ⟨n, a, b, Jk, ha, hb, hab, hrat⟩ := hH.affine j hj0
  have hA : ∀ z ∈ ampleRing H.toSubSystem 1 (h j), z ∈ chartRing S h J := fun z hz =>
    ampleBase_le_chartRing J hj (hH.closed j hj0 hz)
  choose g hg using fun k => hF (Jk k)

  have hext : ∀ k, ∀ᶠ M in atTop, ∀ y ∈ g k, b k ^ M • y ∈ secsOnZ F.toSubSystem H.toSubSystem h J :=
    fun k => (eventually_all_finset _).mpr fun y hy =>
      hExt S Ω N x E F H.toSubSystem r h hsec J j hj (b k) (hb k) (Jk k) (hrat k) y
        (by rw [← hg k]; exact Submodule.subset_span hy)
  choose M0 hM0 using fun k => eventually_atTop.mp (hext k)
  set T : Finset E := Finset.univ.biUnion fun k => (g k).image fun y => b k ^ M0 k • y with hT
  have hTmem : ∀ k, ∀ y ∈ g k, b k ^ M0 k • y ∈ T := fun k y hy =>
    Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, Finset.mem_image.mpr ⟨y, hy, rfl⟩⟩
  refine ⟨T, fun z hz => ?_, fun e he => ?_⟩
  · obtain ⟨k, -, hk⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hk
    exact hM0 k (M0 k) le_rfl y hy
  rw [Submodule.restrictScalars_mem]

  have hloc : ∀ k, ∀ᶠ L in atTop, b k ^ L • e ∈ Submodule.span (chartRing S h J) (T : Set E) := by
    intro k
    have heK : e ∈ secsOnZChart F.toSubSystem H.toSubSystem h (Jk k) J :=
      (Submodule.mem_iInf _).mp he (Jk k)
    obtain ⟨β, hβ, rfl⟩ := hSpan S Ω N x E F.toSubSystem H.toSubSystem r h hsec (Jk k) J (g k)
      (hg k).ge _ heK
    obtain ⟨L0, hL0⟩ := eventually_atTop.mp ((eventually_all_finset (g k)).mpr fun y hy =>
      hRing S Ω N x H r h hH J j hj (b k) (hb k) (Jk k) (hrat k) (β y) (hβ y hy))
    refine eventually_atTop.mpr ⟨L0 + M0 k, fun L hL => ?_⟩
    rw [Finset.smul_sum]
    refine Submodule.sum_mem _ fun y hy => ?_
    have hmem : b k ^ (L - M0 k) * β y ∈ chartRing S h J := hL0 _ (by omega) y hy
    have e1 : b k ^ L • (β y • y) = (⟨_, hmem⟩ : chartRing S h J) • (b k ^ M0 k • y) := by
      rw [Subalgebra.smul_def, smul_smul, smul_smul]
      congr 1
      change b k ^ L * β y = b k ^ (L - M0 k) * β y * b k ^ M0 k
      rw [mul_comm _ (b k ^ M0 k), ← mul_assoc, ← pow_add, Nat.add_sub_cancel' (by omega)]
    rw [e1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (hTmem k y hy))

  choose L hL using fun k => eventually_atTop.mp (hloc k)
  set L' := Finset.univ.sup L
  let bA : Fin n → chartRing S h J := fun k => ⟨b k, hA _ (hb k)⟩
  have htop : Ideal.span (Set.range bA) = ⊤ := by
    rw [Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun]
    refine ⟨fun k => ⟨a k, hA _ (ha k)⟩, Subtype.ext ?_⟩
    rw [AddSubmonoidClass.coe_finsetSum, OneMemClass.coe_one]
    exact hab
  have h1 : (1 : chartRing S h J) ∈ Ideal.span (Set.range fun k => bA k ^ L') := by
    have := Ideal.span_pow_eq_top _ htop L'
    rw [← Set.range_comp] at this
    rw [← Ideal.eq_top_iff_one]
    exact this
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp h1
  have he' : e = ∑ k, c k • (b k ^ L' • e) := by
    have : ∑ k, c k • (b k ^ L' • e) = (∑ k, c k * bA k ^ L') • e := by
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_smul]
      simp [bA]
    rw [this, hc, one_smul]
  rw [he']
  exact Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ (hL k L' (Finset.le_sup (Finset.mem_univ k)))

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def DoubleCech.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (N : ℕ)
    (x : Fin (N + 1) → Ω) (T : Kleiman.SubSystem F x Ω) (B : (∀ k, Finset (ι k)) → Submodule F Ω)
    (M : Kleiman.Chart x → (∀ k, Finset (ι k)) → Submodule F Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∃ j, x j ≠ 0) →
    (∀ I, ¬ CellMeets y I → B I = ⊥) →
    (∀ J I, ¬ CellMeets y I → M J I = ⊥) →
    (∀ (J J' : Kleiman.Chart x) I, J.1 ⊆ J'.1 → M J I ≤ M J' I) →
    (∀ J (I I' : ∀ k, Finset (ι k)), (∀ k, I k ⊆ I' k) → CellMeets y I' → M J I ≤ M J I') →
    (∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → CellMeets y I → CechAugExact F (fun J => M J I) (B I)) →
    (∀ J, CellAugExact F y (M J) ((T.sub J).restrictScalars F)) →
    ∀ n : ℕ, Nonempty (T.H n ≃ₗ[F] cellHOf F y B n)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
