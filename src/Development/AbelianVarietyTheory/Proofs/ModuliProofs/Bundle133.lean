module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle098
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle128
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle100
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliLevelQuotientByFiniteGroup
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle129
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelAutActsOnRaisedModel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModelDominatedOfMapToBaseModel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.TensorProduct.Nontrivial
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenMove
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.SiegelDescent

variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'}

private theorem hom_ext_tensor_left_of_fst_snd {B Z : Scheme.{0}} {X : Over B} (g k : Z ⟶ (X ⊗ X).left)
    (h1 : g ≫ (fst X X).left = k ≫ (fst X X).left) (h2 : g ≫ (snd X X).left = k ≫ (snd X X).left) : g = k := by
  have hw : k ≫ (X ⊗ X).hom = g ≫ (X ⊗ X).hom := by
    rw [← Over.w (fst X X), ← Category.assoc, ← h1, Category.assoc]
  have key := CartesianMonoidalCategory.hom_ext (Over.homMk g rfl : Over.mk (g ≫ (X ⊗ X).hom) ⟶ X ⊗ X)
    (Over.homMk k hw) (by ext; simpa using h1) (by ext; simpa using h2)
  exact congrArg CommaMorphism.left key

private theorem pGen_of_isGen_iso_pull {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : L'.Iso (L.pull F))
    (hw : w.IsGen) : PGen w := by
  intro Y f y j j' k k' hj hj' hk hk'
  obtain ⟨J, hJ⟩ : ∃ J : (L.pull F).ι, J = fun _ => j := ⟨_, rfl⟩
  obtain ⟨J', hJ'⟩ : ∃ J' : (L.pull F).ι, J' = fun _ => j' := ⟨_, rfl⟩
  have m1 : f y ∈ (L.pull F).U J := by rw [hJ]; exact mem_pull.2 hj
  have m2 : f y ∈ (L.pull F).U J' := by rw [hJ']; exact mem_pull.2 hj'
  have hy : f y ∈ ((L.pull F).div L').U (J, k) ⊓ ((L.pull F).div L').U (J', k') := ⟨⟨m1, hk⟩, ⟨m2, hk'⟩⟩
  have e := congrArg (gm f y _) (hw (J, k) (J', k'))
  rw [gm_res f y _ hy, map_mul, gm_res f y _ hy] at e
  have eg : gm f y (((L.pull F).div L').U (J, k) ⊓ ((L.pull F).div L').U (J', k'))
      (((L.pull F).div L').g (J, k) (J', k')) =
      gm (f ≫ F) y (L.U j ⊓ L.U j') (L.g j j') * (gm f y (L'.U k ⊓ L'.U k') (L'.g k k'))⁻¹ := by
    have hy' : f y ∈ (L.pull F).U J ⊓ L'.U k ⊓ ((L.pull F).U J' ⊓ L'.U k') := ⟨⟨m1, hk⟩, ⟨m2, hk'⟩⟩
    show gm f y ((L.pull F).U J ⊓ L'.U k ⊓ ((L.pull F).U J' ⊓ L'.U k'))
      (res _ ((L.pull F).g J J') * (res _ (L'.g k k'))⁻¹) = _
    rw [map_mul, map_inv, gm_res f y _ hy', gm_res f y _ hy', gm_pull_g L F f y J J' m1 m2]
    subst hJ hJ'
    rfl
  rw [eg] at e
  unfold gw
  subst hJ hJ'
  exact e

private theorem flat_spMap_of_field_hom' {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) : Flat (spMap i) := by
  unfold spMap
  infer_instance

private theorem surjective_spMap_of_field_hom {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) : Surjective (spMap i) := by
  constructor
  intro x
  exact ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K), Subsingleton.elim (α := PrimeSpectrum K₀) _ _⟩

theorem lift_comp_square {φ : A'.left ⟶ A.left} {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left} (hs : IsSquare φ φ₂)
    {T : Over S} {T' : Over S'} (u : T'.left ⟶ T.left) (a b : T ⟶ A) (a' b' : T' ⟶ A')
    (ha : a'.left ≫ φ = u ≫ a.left) (hb : b'.left ≫ φ = u ≫ b.left) :
    (lift a' b').left ≫ φ₂ = u ≫ (lift a b).left := by
  have e1 : (lift a' b').left ≫ (fst A' A').left = a'.left := by rw [← Over.comp_left, lift_fst]
  have e2 : (lift a b).left ≫ (fst A A).left = a.left := by rw [← Over.comp_left, lift_fst]
  have e3 : (lift a' b').left ≫ (snd A' A').left = b'.left := by rw [← Over.comp_left, lift_snd]
  have e4 : (lift a b).left ≫ (snd A A).left = b.left := by rw [← Over.comp_left, lift_snd]
  apply hom_ext_tensor_left_of_fst_snd
  · rw [Category.assoc, hs.1, ← Category.assoc, e1, ha, Category.assoc, e2]
  · rw [Category.assoc, hs.2, ← Category.assoc, e3, hb, Category.assoc, e4]

theorem eq_one_of_pull {f : S' ⟶ S} [Flat f] [Surjective f] [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left}
    {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left} {P : LB (A ⊗ A).left} {P' : LB (A' ⊗ A').left}
    (h : IsGrpPullback A' A f φ) (hs : IsSquare φ φ₂) (hP : P.IsLB) (hP' : P'.IsLB) (hw : LBIso P' (P.pull φ₂))
    (hK : ∀ (T : Over S') (x : T ⟶ A'), (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x = 1)
    (T : Over S) (x : T ⟶ A) (hx : ∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) : x = 1 := by
  obtain ⟨w, hwg⟩ := hw
  obtain ⟨t, ht⟩ := hx
  let T' : Over S' := Over.mk (pullback.snd T.hom f)
  let p : T'.left ⟶ T.left := pullback.fst T.hom f
  have hp : p ≫ T.hom = T'.hom ≫ f := pullback.condition
  have hxl : (p ≫ x.left) ≫ A.hom = T'.hom ≫ f := by rw [Category.assoc, Over.w x]; exact hp
  let xl : T'.left ⟶ A'.left := h.1.lift (p ≫ x.left) T'.hom hxl
  have hxl1 : xl ≫ φ = p ≫ x.left := h.1.lift_fst _ _ _
  have hxl2 : xl ≫ A'.hom = T'.hom := h.1.lift_snd _ _ _
  let x' : T' ⟶ A' := Over.homMk xl hxl2
  have hA : φ ≫ A.hom = A'.hom ≫ f := h.1.w
  let Z : Over S := Over.mk ((A' ⊗ T').hom ≫ f)
  let a0 : Z ⟶ A := Over.homMk ((fst A' T').left ≫ φ) (by
    rw [Category.assoc, hA, ← Category.assoc, Over.w (fst A' T')]; rfl)
  let b0 : Z ⟶ T := Over.homMk ((snd A' T').left ≫ p) (by
    rw [Category.assoc, hp, ← Category.assoc, Over.w (snd A' T')]; rfl)
  let q : (A' ⊗ T').left ⟶ (A ⊗ T).left := (lift a0 b0).left
  have hq1 : q ≫ (fst A T).left = (fst A' T').left ≫ φ := by
    rw [← Over.comp_left, lift_fst]; rfl
  have hq2 : q ≫ (snd A T).left = (snd A' T').left ≫ p := by
    rw [← Over.comp_left, lift_snd]; rfl
  have hc : (lift (snd A' T' ≫ x') (fst A' T')).left ≫ φ₂ = q ≫ (lift (snd A T ≫ x) (fst A T)).left := by
    refine lift_comp_square hs q _ _ _ _ ?_ hq1.symm
    rw [Over.comp_left, Over.comp_left, Category.assoc, ← Category.assoc q, hq2, Category.assoc]
    exact congrArg ((snd A' T').left ≫ ·) hxl1
  obtain ⟨a, ha, -⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_gen_move hP hP' w (pGen_of_isGen_iso_pull w hwg) (K := PUnit)
    (fun _ => (lift (snd A T ≫ x) (fst A T)).left) (fun _ => (lift (snd A' T' ≫ x') (fst A' T')).left)
    (fun _ => 1) q (fun _ => hc) t ht
  have hx' : x' = 1 := hK T' x' ⟨a, ha⟩
  let Zp : Over S := Over.mk (T'.hom ≫ f)
  let z : Zp ⟶ A := Over.homMk (p ≫ x.left) hxl
  have hz : z.left = (1 : T' ⟶ A').left ≫ φ := by
    show p ≫ x.left = _
    rw [← hxl1, ← hx']
    rfl
  have hzz := h.2 T' 1 1 z z hz hz
  rw [_root_.mul_one] at hzz
  have hz1 : z = 1 := by
    have e : z * z = z * 1 := by
      rw [_root_.mul_one]
      exact Over.OverMorphism.ext (hzz.trans hz.symm)
    exact mul_left_cancel e
  have hfl : Flat p := inferInstanceAs (Flat (pullback.fst T.hom f))
  have hsu : Surjective p := inferInstanceAs (Surjective (pullback.fst T.hom f))
  have hpe : Epi p := Flat.epi_of_flat_of_surjective p
  let pO : Zp ⟶ T := Over.homMk p hp
  have e1 : pO ≫ x = z := Over.OverMorphism.ext rfl
  have e2 : pO ≫ (1 : T ⟶ A) = 1 := by
    simp
  have hfin : p ≫ x.left = p ≫ (1 : T ⟶ A).left := by
    have e3 := congrArg CommaMorphism.left ((e1.trans hz1).trans e2.symm)
    exact e3
  exact Over.OverMorphism.ext ((cancel_epi p).1 hfin)

theorem principal_of_fieldExtension : ∀ (h M : ℕ) (o : Type) [CommRing o] (ζ : o) (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (s₀ : Sp K₀ ⟶ Sp o) (s : Sp K ⟶ Sp o) (c₀ : SiegPre h M ζ s₀) (c : SiegPre h M ζ s), SiegPB c c₀ (spMap i) → c.Principal → c₀.Principal := by
  intro h M o _ ζ K₀ K _ _ i s₀ s c₀ c hpb hc
  obtain ⟨φ, φ₂, hg, hs, hw, -⟩ := hpb
  have hfl : Flat (spMap i) := flat_spMap_of_field_hom' i
  have hsu : Surjective (spMap i) := surjective_spMap_of_field_hom i
  refine ⟨?_, fun T x hx => eq_one_of_pull hg hs c₀.isLB c.isLB hw hc.2 T x hx⟩
  obtain ⟨w, hwg⟩ := hw
  have hΔ : (lift (𝟙 c.A) (𝟙 c.A)).left ≫ φ₂ = φ ≫ (lift (𝟙 c₀.A) (𝟙 c₀.A)).left :=
    lift_comp_square hs φ _ _ _ _ (by simp) (by simp)
  have i1 : LBIso c.diag (c₀.P.pull (φ ≫ (lift (𝟙 c₀.A) (𝟙 c₀.A)).left)) := by
    have := iso_linComb (pGen_of_isGen_iso_pull w hwg) (K := PUnit) (fun _ => (lift (𝟙 c.A) (𝟙 c.A)).left) (fun _ => 1)
    rw [hΔ] at this
    exact this
  obtain ⟨w₀, hw₀⟩ := exists_iso_linComb c₀.isLB (K := PUnit) (F := (lift (𝟙 c₀.A) (𝟙 c₀.A)).left)
    (fun _ => (lift (𝟙 c₀.A) (𝟙 c₀.A)).left) (fun _ => 1) (fun _ _ _ => rfl)
  have i2 : LBIso (c₀.diag.pull φ) (c₀.P.pull (φ ≫ (lift (𝟙 c₀.A) (𝟙 c₀.A)).left)) :=
    iso_linComb (pGen_of_isGen_iso_pull w₀ hw₀) (K := PUnit) (fun _ => φ) (fun _ => 1)
  have hd : LBIso c.diag (c₀.diag.pull φ) :=
    LBIso.trans (pull_isLB c.isLB _) (pull_isLB c₀.isLB _) (pull_isLB (pull_isLB c₀.isLB _) _) i1 i2.symm
  exact GlobalTheory.AmpleDescent.relAmple_of_fieldExtension K₀ K i c₀.A c.A φ c₀.diag c.diag c₀.ab hg
    (pull_isLB c₀.isLB _) (pull_isLB c.isLB _) hd hc.1

end GlobalTheory.SiegelDescent
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ThetaDescent

theorem map_prod_pow {M N : Type*} [Monoid M] [Monoid N] (P : M →* N) {n : ℕ} (p : Fin n → M) (a : Fin n → ℕ) :
    P (List.ofFn fun i => p i ^ a i).prod = (List.ofFn fun i => P (p i) ^ a i).prod := by
  simp only [map_list_prod, List.map_ofFn, Function.comp_def, map_pow]

theorem existsUnique_transfer {M M₀ N C : Type*} [Monoid M] [Monoid M₀] [Monoid N] (P : M →* N) (R : M₀ →* N)
    (hP : Function.Bijective P) (hR : Function.Injective R) {n : ℕ} (p : Fin n → M) (p₀ : Fin n → M₀)
    (h : ∀ i, P (p i) = R (p₀ i)) (k : ℕ) (e : C → Fin n → ℕ)
    (H : ∀ y : M, y ^ k = 1 → ∃! c : C, (List.ofFn fun i => p i ^ e c i).prod = y)
    (y₀ : M₀) (hy : y₀ ^ k = 1) : ∃! c : C, (List.ofFn fun i => p₀ i ^ e c i).prod = y₀ := by
  obtain ⟨y, hyR⟩ := hP.2 (R y₀)
  have hyk : y ^ k = 1 := hP.1 (by rw [map_pow, hyR, ← map_pow, hy, map_one, map_one])
  have key : ∀ c : C, (List.ofFn fun i => p₀ i ^ e c i).prod = y₀ ↔ (List.ofFn fun i => p i ^ e c i).prod = y := by
    intro c
    rw [← hR.eq_iff, ← hP.1.eq_iff, hyR, map_prod_pow, map_prod_pow]
    simp only [h]
  simpa only [key] using H y hyk

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem pushHom_left (h : IsGrpPullback G' G f φ) (T : Over S') (x : T ⟶ G') :
    (pushHom h T x).left = x.left ≫ φ := rfl

theorem pushHom_bijective (h : IsGrpPullback G' G f φ) (T : Over S') : Function.Bijective (pushHom h T) := by
  refine ⟨fun x y hxy => ?_, fun z => ?_⟩
  · have e := congrArg (fun u => u.left) hxy
    simp only [pushHom_left] at e
    exact Over.OverMorphism.ext (h.1.hom_ext e (by rw [Over.w x, Over.w y]))
  · refine ⟨Over.homMk (h.1.lift z.left T.hom (Over.w z)) (h.1.lift_snd _ _ _), ?_⟩
    ext1
    rw [pushHom_left]
    exact h.1.lift_fst _ _ _

theorem preHom_injective {T T' : Over S} (U : T' ⟶ T) [Epi U.left] :
    Function.Injective (preHom (G := G) U) := by
  intro x y hxy
  ext1
  rw [← cancel_epi U.left, ← Over.comp_left, ← Over.comp_left]
  exact congrArg (fun u => u.left) hxy

theorem weilIs_congr {Z : Scheme.{0}} {s s' : Z ⟶ S} (e : s = s') (L : LB G.left) (k : ℤ)
    (x y : Over.mk s ⟶ G) (x' y' : Over.mk s' ⟶ G) (hx : x.left = x'.left) (hy : y.left = y'.left)
    (c : Γ(Z, ⊤)ˣ) : Out.WeilIs G L k x y c ↔ Out.WeilIs G L k x' y' c := by
  subst e
  obtain rfl : x = x' := Over.OverMorphism.ext hx
  obtain rfl : y = y' := Over.OverMorphism.ext hy
  exact Iff.rfl

theorem unitS_spMap {o R : Type} [CommRing o] [CommRing R] (β : o →+* R) (u : oˣ) (n : ℤ) :
    unitS (spMap β) u ^ n = unitOn (Units.map β.toMonoidHom u ^ n) := by
  unfold unitS unitOn
  simp only [← map_zpow]
  ext1
  simp only [Units.coe_map]
  exact (congrArg (fun g => CommRingCat.Hom.hom g ((u ^ n : oˣ) : o)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm

theorem epi_spMap {K Ω : Type} [Field K] [Field Ω] (j : K →+* Ω) : Epi (spMap j) := by
  have := (GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff K Ω j).1 (Sp K) (Sp Ω) (𝟙 _) (𝟙 _) (spMap j)
    (IsPullback.of_vert_isIso ⟨by simp⟩)
  exact this.1

end GlobalTheory.ThetaDescent

namespace GlobalTheory

open ThetaDescent

theorem exists_thetaObj_of_descended_data : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (β₀ : o →+* K₀) (β : o →+* K) (t : TObj g k J b (spMap β)) (A₀ : Over (Sp K₀)) [GrpObj A₀] (φ : t.A.left ⟶ A₀.left) (L₀ : LB A₀.left) (pt₀ : Fin (2 * g) → (Out.baseOver (Sp K₀) ⟶ A₀)) (act₀ : J → (A₀ ⟶ A₀)), i.comp β₀ = β → IsGrpPullback t.A A₀ (spMap i) φ → L₀.IsLB → LBIso t.L (L₀.pull φ) → (∀ a, (t.pt a).left ≫ φ = spMap i ≫ (pt₀ a).left) → (∀ j, (t.act j).left ≫ φ = φ ≫ (act₀ j).left) → ∃ t₀ : TObj g k J b (spMap β₀), TMap t t₀ (spMap i) := by
  intro o _ g k J b K₀ K _ _ i β₀ β t A₀ _ φ L₀ pt₀ act₀ hβ hpb hL₀ hLiso hpt hact
  obtain ⟨hab, hdim⟩ := GlobalTheory.T.abelian_scheme_descent_smooth_dimension K₀ K i A₀ t.A φ hpb t.ab
  obtain ⟨hrig, hsym, hkt⟩ := GlobalTheory.T.rigidified_symmetric_kernelTrivial_descend_fieldExt K₀ K i A₀ t.A φ L₀ t.L hab hpb hL₀ t.isLB hLiso
  have hamp := GlobalTheory.AmpleDescent.relAmple_of_fieldExtension K₀ K i A₀ t.A φ L₀ t.L hab hpb hL₀ t.isLB hLiso t.ample
  have hmon := (GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff K₀ K i).2
  refine ⟨{ A := A₀, ab := hab, dim := hdim g t.dim, L := L₀, isLB := hL₀
            rigid := hrig t.rigid, sym := hsym (TObj.sym t), ample := hamp, ktriv := hkt t.ktriv
            pt := pt₀, torsion := ?_, bij := ?_, pairing := ?_, act := act₀
            hom := fun j => (hmon A₀ A₀ t.A t.A φ φ (act₀ j) (t.act j) hpb hpb (hact j).symm).1 (t.hom j) },
    φ, hpb, hLiso, hpt, hact⟩
  ·
    intro a
    obtain ⟨U0, hU0⟩ : ∃ U0 : Over.mk ((Out.baseOver (Sp K)).hom ≫ spMap i) ⟶ Out.baseOver (Sp K₀),
        U0.left = spMap i := ⟨Over.homMk (spMap i) (by simp), rfl⟩
    have hE : Epi U0.left := by rw [hU0]; exact epi_spMap i
    apply preHom_injective U0
    have e1 : preHom U0 (pt₀ a) = pushHom hpb _ (t.pt a) := by
      ext1
      show (U0 ≫ pt₀ a).left = _
      rw [Over.comp_left, hU0, pushHom_left, hpt a]
    rw [map_pow, map_one, e1, ← map_pow, t.torsion a, map_one]
  ·
    intro K' _ _ x y hy
    obtain ⟨χ, rfl⟩ : ∃ χ : K₀ →+* K', spMap χ = x := ⟨(Spec.preimage x).hom, by
      show Spec.map (CommRingCat.ofHom _) = x
      rw [CommRingCat.ofHom_hom, Spec.map_preimage]⟩
    obtain ⟨Ω, _, _, jK, jL, hcomm⟩ : ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (jK : K →+* Ω) (jL : K' →+* Ω),
        jK.comp i = jL.comp χ := by
      let _ : Algebra K₀ K := i.toAlgebra
      let _ : Algebra K₀ K' := χ.toAlgebra
      have : Nontrivial (K ⊗[K₀] K') :=
        Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain K₀ K K' i.injective χ.injective
      obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[K₀] K')
      let _ := Ideal.Quotient.field m
      refine ⟨AlgebraicClosure (K ⊗[K₀] K' ⧸ m), inferInstance, inferInstance,
        ((algebraMap (K ⊗[K₀] K' ⧸ m) (AlgebraicClosure (K ⊗[K₀] K' ⧸ m))).comp (Ideal.Quotient.mk m)).comp
          (Algebra.TensorProduct.includeLeft : K →ₐ[K₀] K ⊗[K₀] K').toRingHom,
        ((algebraMap (K ⊗[K₀] K' ⧸ m) (AlgebraicClosure (K ⊗[K₀] K' ⧸ m))).comp (Ideal.Quotient.mk m)).comp
          (Algebra.TensorProduct.includeRight : K' →ₐ[K₀] K ⊗[K₀] K').toRingHom, ?_⟩
      ext r
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      have h1 := (Algebra.TensorProduct.includeLeft : K →ₐ[K₀] K ⊗[K₀] K').commutes r
      have h2 := (Algebra.TensorProduct.includeRight : K' →ₐ[K₀] K ⊗[K₀] K').commutes r
      exact congrArg (fun z => algebraMap (K ⊗[K₀] K' ⧸ m) (AlgebraicClosure (K ⊗[K₀] K' ⧸ m))
        (Ideal.Quotient.mk m z)) (h1.trans h2.symm)
    have hw : spMap jL ≫ spMap χ = spMap jK ≫ spMap i := by
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hcomm]
    have hE : Epi (Over.Hom.left (Over.homMk (spMap jL) hw :
        Over.mk (spMap jK ≫ spMap i) ⟶ Over.mk (spMap χ))) := epi_spMap jL
    refine existsUnique_transfer (pushHom hpb (Over.mk (spMap jK)))
      (preHom (G := A₀) (Over.homMk (spMap jL) hw : Over.mk (spMap jK ≫ spMap i) ⟶ Over.mk (spMap χ)))
      (pushHom_bijective hpb _) (preHom_injective _)
      (fun a => (Over.homMk (spMap jK) (by simp) : Over.mk (spMap jK) ⟶ Out.baseOver (Sp K)) ≫ t.pt a)
      (fun a => (Over.homMk (spMap χ) (by simp) : Over.mk (spMap χ) ⟶ Out.baseOver (Sp K₀)) ≫ pt₀ a)
      ?_ k (fun (c : Ix g k) a => (c a).val) (fun z hz => t.bij Ω (spMap jK) z hz) y hy
    intro a
    ext1
    rw [pushHom_left]
    show ((Over.homMk (spMap jK) (by simp) : Over.mk (spMap jK) ⟶ Out.baseOver (Sp K)) ≫ t.pt a).left ≫ φ = ((Over.homMk (spMap jL) hw : Over.mk (spMap jK ≫ spMap i) ⟶ Over.mk (spMap χ)) ≫
      (Over.homMk (spMap χ) (by simp) : Over.mk (spMap χ) ⟶ Out.baseOver (Sp K₀)) ≫ pt₀ a).left
    simp only [Over.comp_left, Over.homMk_left, Category.assoc]
    rw [hpt a, ← Category.assoc, ← Category.assoc, hw]
  ·
    intro a a'
    subst hβ
    have := t.ab.comm
    have h1 := (GlobalTheory.weilIs_grpPullback_of_comm' (Sp K₀) (Sp K) A₀ t.A (spMap i) φ L₀ t.L hL₀ t.isLB hpb hLiso
      (Out.baseOver (Sp K)) (k : ℤ) (t.pt a) (t.pt a') (pushHom hpb _ (t.pt a)) (pushHom hpb _ (t.pt a')) _
      (pushHom_left hpb _ _) (pushHom_left hpb _ _)).1 (t.pairing a a')
    have e1 : unitS (spMap (i.comp β₀)) b.ζ ^ (Out.stdSymp g a a') =
        unitOn (Units.map i.toMonoidHom (Units.map β₀.toMonoidHom b.ζ ^ (Out.stdSymp g a a'))) := by
      rw [unitS_spMap, map_zpow]
      rfl
    rw [e1] at h1
    have hxa : ∀ c, (pushHom hpb (Out.baseOver (Sp K)) (t.pt c)).left =
        ((Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ 𝟙 (Sp K₀)) ⟶ Over.mk (𝟙 (Sp K₀))) ≫ pt₀ c).left := by
      intro c
      rw [pushHom_left, hpt c]
      rfl
    have h2 := (weilIs_congr (s' := spMap i ≫ 𝟙 (Sp K₀)) (by simp) L₀ (k : ℤ) _ _ _ _ (hxa a) (hxa a') _).1 h1
    have h3 := (GlobalTheory.T.weilPairing_fieldExtension_iff (Sp K₀) A₀ K₀ K i (𝟙 _) L₀ k (pt₀ a) (pt₀ a')
      (Units.map β₀.toMonoidHom b.ζ ^ Out.stdSymp g a a') hab hL₀).1 h2
    rw [unitS_spMap]
    exact h3

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

theorem _root_.GlobalTheory.T.moduli_level_quotient_by_finite_group : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l₁ : Level H) (r : (Xo l₁).X ⟶ (Xo l₀).X) (ν : SABMap (Xo l₁).univ.t (Xo l₀).univ.t r) (k : KA l₀ →+* KA l₁), l₀.A = 1 → l₁.M = l₀.M → l₁.Mb = l₀.Mb → IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom k → r ≫ (Xo l₀).s = (Xo l₁).s ≫ spMap k → LevComp (Xo l₁).univ (Xo l₀).univ r ν → ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ) (ρ : Γ →* Aut (Xo l₁).X) (τ : Γ →* Aut (Xo l₁).univ.t.G.left) (mu : ∀ g, SABMap (Xo l₁).univ.t (Xo l₁).univ.t (ρ g).asIso.hom), Function.Injective ρ ∧ (IsAffineHom r ∧ (∀ g, (ρ g).asIso.hom ≫ r = r) ∧ ∀ V : (Xo l₀).X.Opens, Function.Injective (r.app V).hom ∧ ∀ f : Γ((Xo l₁).X, r ⁻¹ᵁ V), (∀ g (h : r ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (r ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (r.app V).hom) ∧ ∀ ω, (mu ω).φ = (τ ω).asIso.hom ∧ (τ ω).asIso.hom ≫ ν.φ = ν.φ ∧ (∀ x, ((Xo l₁).univ.eta x).left ≫ (τ ω).asIso.hom = (ρ ω).asIso.hom ≫ ((Xo l₁).univ.eta x).left) ∧ ∃ (g : D.La →ₗ[𝓞 E] D.La) (σ : KA l₁ ≃+* KA l₁), σ (baseKA l₁).ρ = (baseKA l₁).ρ ∧ (ρ ω).asIso.hom ≫ (Xo l₁).s = (Xo l₁).s ≫ spMap σ.toRingHom ∧ ∀ x, ((Xo l₁).univ.etaA (g x)).left ≫ (τ ω).asIso.hom = (ρ ω).asIso.hom ≫ ((Xo l₁).univ.etaA x).left :=
  GlobalTheory.LevQuot.exists_level_quotient
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

theorem _root_.GlobalTheory.T.exists_level_change_lift_keeping_etaA : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ∀ (l₀ l₁ : Level H) (r : (Xo l₁).X ⟶ (Xo l₀).X) (ν : SABMap (Xo l₁).univ.t (Xo l₀).univ.t r) (r₀ : (Xo l₀).X ≅ (Xo l₀).X) (ν₀ : SABMap (Xo l₀).univ.t (Xo l₀).univ.t r₀.hom) (g : D.La →ₗ[𝓞 E] D.La), l₀.A = 1 → l₁.M = l₀.M → l₁.Mb = l₀.Mb → l₁.A.Coprime l₁.M → LevComp (Xo l₁).univ (Xo l₀).univ r ν → (∃ k : KA l₀ →+* KA l₁, IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom k ∧ r ≫ (Xo l₀).s = (Xo l₁).s ≫ spMap k) → r₀.hom ≫ (Xo l₀).s = (Xo l₀).s → (∀ x, ((Xo l₀).univ.eta (g x)).left ≫ ν₀.φ = r₀.hom ≫ ((Xo l₀).univ.eta x).left) → ∃ (r₁ : (Xo l₁).X ≅ (Xo l₁).X) (ν₁ : SABMap (Xo l₁).univ.t (Xo l₁).univ.t r₁.hom), r₁.hom ≫ (Xo l₁).s = (Xo l₁).s ∧ r₁.hom ≫ r = r ≫ r₀.hom ∧ ν₁.φ ≫ ν.φ = ν.φ ≫ ν₀.φ ∧ ∀ x, ((Xo l₁).univ.etaA x).left ≫ ν₁.φ = r₁.hom ≫ ((Xo l₁).univ.etaA x).left := by
  first | exact @GlobalTheory.LiftAut.exists_lift_keeping_etaA | exact GlobalTheory.LiftAut.exists_lift_keeping_etaA | (intros; apply GlobalTheory.LiftAut.exists_lift_keeping_etaA <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

theorem _root_.GlobalTheory.T.levelAut_acts_on_raised_model : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N), 1 ≤ D.p + D.q → ∀ (l₀ : Level H) (B : BaseModel T l₀) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β), l₀.Dvd l → IsDedFrac β → Raises B Y → Y.LevelActs := by
  first | exact @GlobalTheory.LevActs.levelActs_of_raises | exact GlobalTheory.LevActs.levelActs_of_raises | (intros; apply GlobalTheory.LevActs.levelActs_of_raises <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

theorem _root_.GlobalTheory.T.model_dominated_of_map_to_baseModel : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N) (l₀ l : Level H) (B : BaseModel T l₀) (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model (Xo l) c β) (Y' : Model (Xo l) c β') (b : O →+* O') (f : pullback Y.s (spMap b) ⟶ B.C.X) (t : SAB H (pullback Y.s (spMap b))) (m₁ : SABMap t Y.t (pullback.fst _ _)) (m₂ : SABMap t B.C.t f) (r : (Xo l).XF c ⟶ (Xo l₀).X) (ν : SABMap Y.oF.t (Xo l₀).univ.t r) (k : KA l₀ →+* c.F), IsDedFrac β → IsDedFrac β' → β'.comp b = β → Raises B Y' → LevComp Y.oF (Xo l₀).univ r ν → IsInc (KA l₀).val.toRingHom c.F.val.toRingHom k → r ≫ (Xo l₀).s = pullback.snd _ _ ≫ spMap k → (∀ g : (Xo l).XF c ⟶ pullback Y.s (spMap b), g ≫ pullback.fst _ _ = Y.j → g ≫ f = r ≫ B.C.j) → (∀ y : Y.oF.t.G.left ⟶ t.G.left, y ≫ m₁.φ = Y.m.φ → y ≫ m₂.φ = ν.φ ≫ B.C.m.φ) → Dominates Y Y' b := by
  first | exact @GlobalTheory.Models.Domination.dominates_of_map_to_base | exact GlobalTheory.Models.Domination.dominates_of_map_to_base | (intros; apply GlobalTheory.Models.Domination.dominates_of_map_to_base <;> assumption)
end
