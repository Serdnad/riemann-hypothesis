module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyIsLimitBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2762
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle019
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle621
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRing
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LocTrivDescent
open GlobalTheory.CechPic

theorem triv_iff {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) :
    (∃ t : (L.pull f).Gen, t.IsGen) ↔ CechPic.pull f (cls L hL) = 0 := by
  rw [← cls_pull hL f (pull_isLB hL f), cls_eq_zero_iff]

theorem cls_lbPow_eq {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (k : ℕ) (h : (Hecke.lbPow L k).IsLB) :
    cls _ h = k • cls L hL :=
  (cls_linComb hL _ _ h).trans (by simp [pull_id])

theorem one_left_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) :
    (1 : 𝟙_ (Over S') ⟶ G').left ≫ φ = f ≫ (1 : 𝟙_ (Over S) ⟶ G).left := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
  let U : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ 𝟙_ (Over S) := Over.homMk f (by simp)
  have e2 : (1 : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G) = U ≫ 1 := (comp_one U).symm
  exact e.trans (by rw [e2]; rfl)

theorem fibre_triv {R R₁ : Type} [CommRing R] [CommRing R₁] (j : R₁ →+* R) {A : Over (Sp R)} {A₁ : Over (Sp R₁)}
    {ψ : A.left ⟶ A₁.left} (hψ : IsPullback ψ A.hom A₁.hom (spMap j)) {K : Type} [Field K] (g₀ : R →+* K)
    (c : Pic A₁.left) (h : CechPic.pull (pullback.fst A.hom (spMap g₀)) (CechPic.pull ψ c) = 0) :
    CechPic.pull (pullback.fst A₁.hom (spMap (g₀.comp j))) c = 0 := by
  have w : pullback.fst A₁.hom (spMap (g₀.comp j)) ≫ A₁.hom =
      (pullback.snd A₁.hom (spMap (g₀.comp j)) ≫ spMap g₀) ≫ spMap j := by
    rw [pullback.condition, Category.assoc, GlobalTheory.spMap_comp_ring]
  let a := hψ.lift _ _ w
  have ha1 : a ≫ ψ = pullback.fst _ _ := hψ.lift_fst _ _ _
  have ha2 : a ≫ A.hom = pullback.snd _ _ ≫ spMap g₀ := hψ.lift_snd _ _ _
  let n := pullback.lift a (pullback.snd _ _) ha2
  have hn : n ≫ pullback.fst A.hom (spMap g₀) = a := pullback.lift_fst _ _ _
  rw [← ha1, ← hn, Category.assoc, pull_comp, pull_comp, h, map_zero]

theorem basicOpen_triv {R R₁ : Type} [CommRing R] [CommRing R₁] (j : R₁ →+* R) {A : Over (Sp R)}
    {A₁ : Over (Sp R₁)} {ψ : A.left ⟶ A₁.left} (w : ψ ≫ A₁.hom = A.hom ≫ spMap j) (c : Pic A₁.left) (r : R₁)
    (h : CechPic.pull (A₁.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι c = 0) :
    CechPic.pull (A.hom ⁻¹ᵁ PrimeSpectrum.basicOpen (j r)).ι (CechPic.pull ψ c) = 0 := by
  have le : A.hom ⁻¹ᵁ PrimeSpectrum.basicOpen (j r) ≤ ψ ⁻¹ᵁ (A₁.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r) := by
    intro x hx
    have e : A₁.hom.base (ψ.base x) = (spMap j).base (A.hom.base x) := by
      rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]
    show A₁.hom.base (ψ.base x) ∈ PrimeSpectrum.basicOpen r
    rw [e]
    exact hx
  rw [← pull_comp, ← Scheme.Hom.resLE_comp_ι ψ le, pull_comp, h, map_zero]

end GlobalTheory.LocTrivDescent

namespace GlobalTheory.LocTrivDescent
open GlobalTheory.CechPic

theorem cls_spread (S : Type) [CommRing S] (R₀ : Subring S) (X X₀ : Scheme.{0}) (f : X ⟶ Sp S) (f₀ : X₀ ⟶ Sp R₀)
    (π : X ⟶ X₀) [QuasiCompact f₀] [QuasiSeparated f₀] (M : LB X₀) (hM : M.IsLB)
    (hp : IsPullback π f f₀ (spMap R₀.subtype)) (h0 : CechPic.pull π (cls M hM) = 0) :
    ∃ F : Finset S, ∀ (R₁ : Subring S) (h : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁)
      (π₁ : X₁ ⟶ X₀), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion h)) → CechPic.pull π₁ (cls M hM) = 0 := by
  have hT := LB.isLB_triv X₀
  have z : cls (LB.triv X₀) hT = 0 := rfl
  have key : ∀ {Y : Scheme.{0}} (g : Y ⟶ X₀),
      CechPic.pull g (cls M hM) = 0 ↔ LBIso (M.pull g) ((LB.triv X₀).pull g) := by
    intro Y g
    rw [← cls_eq_iff (pull_isLB hM g) (pull_isLB hT g), cls_pull hM, cls_pull hT, z, map_zero]
  obtain ⟨F, hF⟩ := GlobalTheory.lbIso_descends_to_subring_containing_finset S R₀ X X₀ f f₀ π M (LB.triv X₀) hp hM hT
    ((key π).1 h0)
  exact ⟨F, fun R₁ h hs X₁ f₁ π₁ hp₁ => (key π₁).2 (hF R₁ h hs X₁ f₁ π₁ hp₁)⟩

theorem locTriv_of_noetherian : (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → (∃ t : (M.pull (1 : 𝟙_ (Over (Sp R)) ⟶ A).left).Gen, t.IsGen) → ∀ k : ℕ, IsUnit (k : R) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) → ∀ (K : Type) [Field K] (g₀ : R →+* K), (∃ t : (M.pull (pullback.fst A.hom (spMap g₀))).Gen, t.IsGen) → ∃ r : R, g₀ r ≠ 0 ∧ ∃ t : (M.pull (A.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι).Gen, t.IsGen) → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → (∃ t : (M.pull (1 : 𝟙_ (Over (Sp R)) ⟶ A).left).Gen, t.IsGen) → ∀ k : ℕ, IsUnit (k : R) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) → ∀ (K : Type) [Field K] (g₀ : R →+* K), (∃ t : (M.pull (pullback.fst A.hom (spMap g₀))).Gen, t.IsGen) → ∃ r : R, g₀ r ≠ 0 ∧ ∃ t : (M.pull (A.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι).Gen, t.IsGen := by
  intro H R _ A _ hA M hM h1 k hk h2 K _ g₀ h3
  classical
  obtain ⟨S, G₀, _, φ, L₀, hft, hab, hφ, hL₀, hiso⟩ := GlobalTheory.AmpleFibreMove.exists_fg_model R A hA M hM
  have := hab.proper
  set c₀ := cls L₀ hL₀ with hc₀
  have hc : cls M hM = CechPic.pull φ c₀ := by
    rw [hc₀, ← cls_pull hL₀ φ (pull_isLB hL₀ φ)]
    exact (cls_eq_iff _ _).2 hiso

  let e₀ : Sp S ⟶ G₀.left := (1 : 𝟙_ (Over (Sp S)) ⟶ G₀).left
  have ha : CechPic.pull (spMap S.subtype) (CechPic.pull e₀ c₀) = 0 := by
    rw [← pull_comp, ← one_left_comp hφ, pull_comp, ← hc]
    exact (triv_iff hM _).1 h1
  obtain ⟨F₁, hF₁⟩ := cls_spread R S (Sp R) (Sp S) (𝟙 _) (𝟙 _) (spMap S.subtype) (L₀.pull e₀)
    (pull_isLB hL₀ e₀) (IsPullback.id_vert _) ha

  have hP₀ : (Hecke.lbPow L₀ k).IsLB := LB.isLB_linComb hL₀ _ _
  have hb : CechPic.pull φ (cls _ hP₀) = 0 := by
    obtain ⟨t, ht⟩ := h2
    have hPM : (Hecke.lbPow M k).IsLB := LB.isLB_linComb hM _ _
    have e := (cls_eq_zero_iff hPM).2 ⟨t, ht⟩
    rw [cls_lbPow_eq hM, hc] at e
    rw [cls_lbPow_eq hL₀, map_nsmul]
    exact e
  obtain ⟨F₂, hF₂⟩ := cls_spread R S A.left G₀.left A.hom G₀.hom φ _ hP₀ hφ.1 hb

  obtain ⟨u, hu⟩ : ∃ u : R, (k : R) * u = 1 := ⟨_, hk.mul_val_inv⟩
  obtain ⟨R₁, h, hT, hft₁⟩ := GlobalTheory.KeyTf.exists_finiteType_subring_adjoin R S (F₁ ∪ F₂ ∪ {u}) hft
  have hT₁ : (F₁ : Set R) ⊆ R₁ := fun x hx => hT (by simp [hx])
  have hT₂ : (F₂ : Set R) ⊆ R₁ := fun x hx => hT (by simp [hx])
  have hu₁ : u ∈ R₁ := hT (by simp)
  have : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing ℤ R₁
  let t : Sp R₁ ⟶ Sp S := spMap (Subring.inclusion h)
  have et : spMap R₁.subtype ≫ t = spMap S.subtype := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have := hab.comm
  have := hab.smooth
  have := hab.geomConnected
  letI : GrpObj ((Over.pullback t).obj G₀) := Functor.grpObjObj
  let A₁ : Over (Sp R₁) := (Over.pullback t).obj G₀
  have hab₁ : IsAbelianScheme A₁ :=
    { comm := inferInstance
      smooth := inferInstanceAs (Smooth (pullback.snd G₀.hom t))
      proper := inferInstanceAs (IsProper (pullback.snd G₀.hom t))
      geomConnected := inferInstanceAs (GeometricallyConnected (pullback.snd G₀.hom t)) }
  have hpb₁ : IsPullback (pullback.fst G₀.hom t) A₁.hom G₀.hom t := IsPullback.of_hasPullback _ _
  have wφ : φ ≫ G₀.hom = (A.hom ≫ spMap R₁.subtype) ≫ t := by
    rw [Category.assoc, et]; exact hφ.1.w
  let ψ : A.left ⟶ A₁.left := pullback.lift φ (A.hom ≫ spMap R₁.subtype) wφ
  have hψ₁ : ψ ≫ pullback.fst G₀.hom t = φ := pullback.lift_fst _ _ _
  have hψ₂ : ψ ≫ A₁.hom = A.hom ≫ spMap R₁.subtype := pullback.lift_snd _ _ _
  have hψ : IsGrpPullback A A₁ (spMap R₁.subtype) ψ :=
    (isGrpPullback_pullback G₀ t).cancel (hφ.congr et.symm hψ₁.symm) hψ₂
  let M₁ : LB A₁.left := L₀.pull (pullback.fst G₀.hom t)
  have hM₁ : M₁.IsLB := pull_isLB hL₀ _
  have hc₁ : cls M₁ hM₁ = CechPic.pull (pullback.fst G₀.hom t) c₀ := cls_pull hL₀ _ _
  have hcM : cls M hM = CechPic.pull ψ (cls M₁ hM₁) := by
    rw [hc₁, ← pull_comp, hψ₁, hc]
  obtain ⟨r, hr, hgen⟩ := H R₁ A₁ hab₁ M₁ hM₁
    ((triv_iff hM₁ _).2 (by
      rw [hc₁, ← pull_comp, one_left_comp (isGrpPullback_pullback G₀ t), pull_comp]
      exact hF₁ R₁ h hT₁ (Sp R₁) (𝟙 _) t (IsPullback.id_vert _)))
    k (isUnit_iff_exists_inv.2 ⟨⟨u, hu₁⟩, Subtype.ext (by simpa using hu)⟩)
    (by
      have hPM₁ : (Hecke.lbPow M₁ k).IsLB := LB.isLB_linComb hM₁ _ _
      refine (cls_eq_zero_iff hPM₁).1 ?_
      rw [cls_lbPow_eq hM₁, hc₁, ← map_nsmul, ← cls_lbPow_eq hL₀ k hP₀]
      exact hF₂ R₁ h hT₂ A₁.left A₁.hom _ hpb₁)
    K (g₀.comp R₁.subtype)
    ((triv_iff hM₁ _).2 (fibre_triv R₁.subtype hψ.1 g₀ _ (by rw [← hcM]; exact (triv_iff hM _).1 h3)))
  refine ⟨r, hr, (triv_iff hM _).2 ?_⟩
  rw [hcM]
  exact basicOpen_triv R₁.subtype hψ₂ _ r ((triv_iff hM₁ _).1 hgen)

end GlobalTheory.LocTrivDescent
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.AnySec

open MvPolynomial

theorem exists_homog {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ} (x : Fin n → S) (j : Fin n) (v : S)
    (hv : x j * v = 1) (F : MvPolynomial (Fin n) R) :
    ∃ (F' : MvPolynomial (Fin n) R) (d : ℕ), eval₂ f (fun l => x l * v) F * x j ^ d = eval₂ f x F' := by
  induction F using MvPolynomial.induction_on with
  | C a => exact ⟨C a, 0, by simp⟩
  | add p q hp hq =>
    obtain ⟨p', dp, ep⟩ := hp
    obtain ⟨q', dq, eq⟩ := hq
    refine ⟨p' * X j ^ dq + q' * X j ^ dp, dp + dq, ?_⟩
    simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_X]
    rw [← ep, ← eq]; ring
  | mul_X p l hp =>
    obtain ⟨p', dp, ep⟩ := hp
    refine ⟨p' * X l, dp + 1, ?_⟩
    simp only [eval₂_mul, eval₂_X]
    linear_combination (x l * v * x j) * ep + (x l * eval₂ f x p') * hv

variable {X Y : Scheme.{0}}

theorem isUnit_of_gs {N : X.Opens} (a : Γ(X, N)) (h : ∀ y ∈ N, IsUnit (gs (𝟙 X) y N a)) : IsUnit a :=
  X.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    have := h y hy
    rw [gs_eq (𝟙 X) y N hy] at this
    exact this

theorem gs_rs_app (p : X ⟶ Y) {U : Y.Opens} {N : X.Opens} (hle : N ≤ p ⁻¹ᵁ U) {y : X} (hy : y ∈ N) (a : Γ(Y, U)) :
    gs (𝟙 X) y N (GlobalTheory.AbLaw.rs X hle ((p.app U).hom a)) = gs p y U a := by
  rw [gs_res (𝟙 X) y hle hy, gs_pull (𝟙 X) p y U (hle hy) a, Category.id_comp]

theorem rs_comp_cst {R : Type} [CommRing R] (q : X ⟶ Spec (CommRingCat.of R)) {N N₁ : X.Opens} (hle : N ≤ N₁) :
    (GlobalTheory.AbLaw.rs X hle).comp (GlobalTheory.AbLaw.cst q N₁) = GlobalTheory.AbLaw.cst q N := by
  ext c
  simp only [GlobalTheory.AbLaw.cst, GlobalTheory.AbLaw.rs, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

end GlobalTheory.Mum.AnySec

namespace GlobalTheory.Mum.AnySec
open MvPolynomial
variable {X Y : Scheme.{0}}

theorem locGen_anySec_gen {R : Type} [CommRing R] (q : X ⟶ Spec (CommRingCat.of R)) (p : X ⟶ Y) (L : LB Y)
    (k n : ℕ) (τ : Fin n → H0 L k)
    (H : ∀ w : X, ∃ (j : Fin n) (i : Fin 1 → L.ι) (N : X.Opens) (r : Fin n → Γ(X, N)), w ∈ N ∧ IsAffineOpen N ∧
      N ≤ p ⁻¹ᵁ secChart L i ∧ (∀ y ∈ N, IsUnit (secGerm p y (τ j) i) ∧
        ∀ l, secGerm p y (τ l) i = gs (𝟙 _) y N (r l) * secGerm p y (τ j) i) ∧
      ∀ g : Γ(X, N), ∃ P Q : MvPolynomial (Fin n) R, IsUnit (eval₂ (GlobalTheory.AbLaw.cst q N) r Q) ∧
        g * eval₂ (GlobalTheory.AbLaw.cst q N) r Q = eval₂ (GlobalTheory.AbLaw.cst q N) r P)
    (s₀ : H0 L k) (i : Fin 1 → L.ι) (w : X) (hw : p w ∈ secChart L i) (hs : IsUnit (secGerm p w s₀ i)) :
    ∃ (N : X.Opens) (r : Fin n → Γ(X, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ p ⁻¹ᵁ secChart L i ∧
      (∀ y ∈ N, IsUnit (secGerm p y s₀ i) ∧ ∀ l, secGerm p y (τ l) i = gs (𝟙 _) y N (r l) * secGerm p y s₀ i) ∧
      ∀ g : Γ(X, N), ∃ P Q : MvPolynomial (Fin n) R, IsUnit (eval₂ (GlobalTheory.AbLaw.cst q N) r Q) ∧
        g * eval₂ (GlobalTheory.AbLaw.cst q N) r Q = eval₂ (GlobalTheory.AbLaw.cst q N) r P := by
  obtain ⟨j, i', N₁, ρ, hwN, hN₁, hN₁le, hgerm, hgen⟩ := H w
  let V : X.Opens := p ⁻¹ᵁ secChart L i ⊓ X.basicOpen ((p.app (secChart L i)).hom (s₀.f i))
  have hwV : w ∈ V := by
    refine ⟨hw, (Scheme.mem_basicOpen X _ w hw).2 ?_⟩
    have e : secGerm p w s₀ i = _ := gs_eq p w (secChart L i) hw (s₀.f i)
    rw [e] at hs
    exact hs
  obtain ⟨h, hhV, hwh⟩ := hN₁.exists_basicOpen_le ⟨w, hwV⟩ hwN
  have hNN₁ : X.basicOpen h ≤ N₁ := X.basicOpen_le h
  have hNi : X.basicOpen h ≤ p ⁻¹ᵁ secChart L i := hhV.trans inf_le_left
  have hNs : X.basicOpen h ≤ X.basicOpen ((p.app (secChart L i)).hom (s₀.f i)) := hhV.trans inf_le_right
  have hsN : ∀ y ∈ X.basicOpen h, IsUnit (secGerm p y s₀ i) := fun y hy => by
    have := (Scheme.mem_basicOpen _ _ _ (hNi hy)).1 (hNs hy)
    have e : secGerm p y s₀ i = _ := gs_eq p y (secChart L i) (hNi hy) (s₀.f i)
    rw [e]
    exact this
  have hu₀ : IsUnit (GlobalTheory.AbLaw.rs X hNi ((p.app (secChart L i)).hom (s₀.f i))) :=
    isUnit_of_gs _ fun y hy => by rw [gs_rs_app p hNi hy (s₀.f i)]; exact hsN y hy
  obtain ⟨r, hr_def⟩ : ∃ r : Fin n → Γ(X, X.basicOpen h), r = fun l =>
      GlobalTheory.AbLaw.rs X hNi ((p.app (secChart L i)).hom ((τ l).f i)) * (hu₀.unit⁻¹ : (Γ(X, X.basicOpen h))ˣ).val :=
    ⟨_, rfl⟩
  have hr : ∀ y ∈ X.basicOpen h, ∀ l, secGerm p y (τ l) i = gs (𝟙 X) y _ (r l) * secGerm p y s₀ i := by
    intro y hy l
    rw [secGerm, secGerm, ← gs_rs_app p hNi hy ((τ l).f i), ← gs_rs_app p hNi hy (s₀.f i), ← gs_mul _ _ _ hy]
    congr 1
    simp only [hr_def, _root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one]
  refine ⟨X.basicOpen h, r, hwh, hN₁.basicOpen h, hNi, fun y hy => ⟨hsN y hy, hr y hy⟩, fun g => ?_⟩

  have key : ∀ y ∈ X.basicOpen h, ∀ l, gs (𝟙 X) y _ (r l) = gs (𝟙 X) y _ (GlobalTheory.AbLaw.rs X hNN₁ (ρ l) * r j) ∧
      IsUnit (gs (𝟙 X) y _ (r j)) := by
    intro y hy l
    have hy₁ := hNN₁ hy
    obtain ⟨c, hc⟩ := exists_unit_secGerm k p y (hNi hy) (hN₁le hy₁)
    have gρ : gs (𝟙 X) y _ (GlobalTheory.AbLaw.rs X hNN₁ (ρ l)) = gs (𝟙 X) y N₁ (ρ l) := gs_res _ _ hNN₁ hy _
    have e1 := hr y hy l
    have e2 := hr y hy j
    have e3 := (hgerm y hy₁).2 l
    have hcl := hc (τ l)
    have hcj := hc (τ j)
    refine ⟨?_, ?_⟩
    · rw [gs_mul _ _ _ hy, gρ]
      apply (hsN y hy).mul_right_cancel
      linear_combination (-1 : _) * e1 + gs (𝟙 X) y N₁ (ρ l) * e2 + hcl - gs (𝟙 X) y N₁ (ρ l) * hcj + c.val * e3
    · have : IsUnit (gs (𝟙 X) y _ (r j) * secGerm p y s₀ i) := by
        rw [← e2, hcj]; exact c.isUnit.mul (hgerm y hy₁).1
      exact isUnit_of_mul_isUnit_left this
  have hrel : ∀ l, r l = GlobalTheory.AbLaw.rs X hNN₁ (ρ l) * r j := fun l => fn_ext fun y hy => (key y hy l).1
  have huj : IsUnit (r j) := isUnit_of_gs _ fun y hy => (key y hy j).2
  let v : Γ(X, X.basicOpen h) := (huj.unit⁻¹ : (Γ(X, X.basicOpen h))ˣ).val
  have hv : r j * v = 1 := IsUnit.mul_val_inv huj
  have hρ : (fun l => GlobalTheory.AbLaw.rs X hNN₁ (ρ l)) = fun l => r l * v := by
    funext l; rw [hrel l, _root_.mul_assoc, hv, _root_.mul_one]

  have hev : ∀ F : MvPolynomial (Fin n) R, GlobalTheory.AbLaw.rs X hNN₁ (eval₂ (GlobalTheory.AbLaw.cst q N₁) ρ F) =
      eval₂ (GlobalTheory.AbLaw.cst q (X.basicOpen h)) (fun l => r l * v) F := fun F => by
    rw [eval₂_comp_left, rs_comp_cst, ← hρ]; rfl
  haveI := hN₁.isLocalization_basicOpen h
  obtain ⟨⟨a, ⟨_, t, rfl⟩⟩, hga⟩ := IsLocalization.surj (Submonoid.powers h) g
  have hhu : IsUnit (GlobalTheory.AbLaw.rs X hNN₁ h) := IsLocalization.Away.algebraMap_isUnit h
  obtain ⟨Pa, Qa, hQa, ea⟩ := hgen a
  obtain ⟨Ph, Qh, hQh, eh⟩ := hgen h
  have ea' := congrArg (GlobalTheory.AbLaw.rs X hNN₁) ea
  have eh' := congrArg (GlobalTheory.AbLaw.rs X hNN₁) eh
  rw [map_mul, hev, hev] at ea' eh'
  have hQh' := hQh.map (GlobalTheory.AbLaw.rs X hNN₁)
  rw [hev] at hQh'
  have hga' : g * GlobalTheory.AbLaw.rs X hNN₁ h ^ t = GlobalTheory.AbLaw.rs X hNN₁ a := by
    rw [← map_pow]; exact hga
  obtain ⟨A', d3, eA⟩ := exists_homog (GlobalTheory.AbLaw.cst q (X.basicOpen h)) r j v hv Pa
  obtain ⟨B', d2, eB⟩ := exists_homog (GlobalTheory.AbLaw.cst q (X.basicOpen h)) r j v hv Qa
  obtain ⟨C', d1, eC⟩ := exists_homog (GlobalTheory.AbLaw.cst q (X.basicOpen h)) r j v hv Ph
  obtain ⟨D', d4, eD⟩ := exists_homog (GlobalTheory.AbLaw.cst q (X.basicOpen h)) r j v hv Qh
  refine ⟨A' * D' ^ t * MvPolynomial.X j ^ (d1 * t + d2), C' ^ t * B' * MvPolynomial.X j ^ (d3 + d4 * t), ?_, ?_⟩
  · simp only [eval₂_mul, eval₂_pow, eval₂_X]
    rw [← eB, ← eC, ← eh']
    have hQa' := hQa.map (GlobalTheory.AbLaw.rs X hNN₁)
    rw [hev] at hQa'
    exact ((((hhu.mul hQh').mul (huj.pow _)).pow _).mul (hQa'.mul (huj.pow _))).mul (huj.pow _)
  · simp only [eval₂_mul, eval₂_pow, eval₂_X]
    rw [← eA, ← eB, ← eC, ← eD, ← eh', ← ea']
    linear_combination (eval₂ (GlobalTheory.AbLaw.cst q (X.basicOpen h)) (fun l => r l * v) Qa *
      eval₂ (GlobalTheory.AbLaw.cst q (X.basicOpen h)) (fun l => r l * v) Qh ^ t * r j ^ (d1 * t + d2 + d3 + d4 * t)) * hga'

end GlobalTheory.Mum.AnySec

theorem GlobalTheory.Mum.locGen_ratio_anySec : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) (L : LB G.left) (k n : ℕ) (τ : Fin n → H0 L k), (∀ w : (thickObj R (maximalIdeal R) 0 G).left, ∃ (j : Fin n) (i : Fin 1 → L.ι) (N : (thickObj R (maximalIdeal R) 0 G).left.Opens) (r : Fin n → Γ((thickObj R (maximalIdeal R) 0 G).left, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart L i ∧ (∀ y ∈ N, IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ j) i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ l) i = gs (𝟙 _) y N (r l) * secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ j) i) ∧ ∀ g : Γ((thickObj R (maximalIdeal R) 0 G).left, N), ∃ P Q : MvPolynomial (Fin n) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q = MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r P) → ∀ (s₀ : H0 L k) (i : Fin 1 → L.ι) (w : (thickObj R (maximalIdeal R) 0 G).left), (fstG (maximalIdeal R) 0 G).left w ∈ secChart L i → IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left w s₀ i) → ∃ (N : (thickObj R (maximalIdeal R) 0 G).left.Opens) (m : ℕ) (σ : Fin m → H0 L k) (r : Fin m → Γ((thickObj R (maximalIdeal R) 0 G).left, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart L i ∧ (∀ y ∈ N, IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y s₀ i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (σ l) i = gs (𝟙 _) y N (r l) * secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y s₀ i) ∧ ∀ g : Γ((thickObj R (maximalIdeal R) 0 G).left, N), ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q = MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r P := by
  intro R _ _ _ G L k n τ H s₀ i w hw hs
  obtain ⟨N, r, h1, h2, h3, h4, h5⟩ :=
    GlobalTheory.Mum.AnySec.locGen_anySec_gen ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) _ L k n τ H s₀ i w hw hs
  exact ⟨N, n, τ, r, h1, h2, h3, h4, h5⟩
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

theorem gs_abCst {R : Type} [CommRing R] {X Z : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (W : X.Opens)
    (r : Z ⟶ X) (z : Z) (hz : r z ∈ W) (x : R) :
    gs r z W (GlobalTheory.AbLaw.cst f W x) = gs (r ≫ f) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x) :=
  (gs_res r z le_top hz _).trans (gs_pull r f z ⊤ trivial _)

theorem gs_top_mul {R : Type} [CommRing R] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (a b : R) :
    gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (a * b)) =
      gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) *
        gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom b) := by
  rw [map_mul]; exact gs_mul q z ⊤ trivial _ _

theorem isUnit_gs_top {R : Type} [CommRing R] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (a : Rˣ) :
    IsUnit (gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (a : R))) := by
  rw [gs_eq q z ⊤ trivial]
  exact ((a.isUnit.map _).map _).map _

theorem veryAmpleAlong_transport {K : Type} [Field K] {X Y XA : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of K))
    (pA : XA ⟶ Spec (CommRingCat.of K)) (gn : Y ⟶ XA) [IsIso gn] (hp : gn ≫ pA = p) (π : Y ⟶ X) {L : LB X}
    (hL : L.IsLB) {LA : LB XA} (hLA : LA.IsLB) {k m : ℕ} (b : Fin (m + 1) → H0 LA k)
    (hb : VeryAmpleAlong pA (𝟙 XA) LA b) (σ : Fin (m + 1) → H0 L k) (c : Fin (m + 1) → Kˣ)
    (H : ∀ (y : Y) (j : Fin 1 → L.ι) (jA : Fin 1 → LA.ι), π y ∈ L.U (j 0) → gn y ∈ LA.U (jA 0) →
      ∃ u : (Y.presheaf.stalk y)ˣ, ∀ i, secGerm π y (σ i) j =
        u.val * gs p y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (c i : K)) * secGerm gn y (b i) jA) :
    VeryAmpleAlong p π L σ := by
  classical

  have hmem : ∀ i (y : Y), y ∈ π ⁻¹ᵁ nonzeroLocus (σ i) ↔ gn y ∈ (𝟙 XA) ⁻¹ᵁ nonzeroLocus (b i) := by
    intro i y
    obtain ⟨j, hj⟩ := exists_chart hL (π y)
    obtain ⟨jA, hjA⟩ := exists_chart hLA (gn y)
    obtain ⟨u, hu⟩ := H y (fun _ => j) (fun _ => jA) hj hjA
    change π y ∈ nonzeroLocus (σ i) ↔ gn y ∈ nonzeroLocus (b i)
    rw [GlobalTheory.SectionRingIso.mem_iff_isUnit (σ i) π y (j := fun _ => j) hj,
      GlobalTheory.SectionRingIso.mem_iff_isUnit (b i) gn y (j := fun _ => jA) hjA]
    change IsUnit (secGerm π y (σ i) _) ↔ IsUnit (secGerm gn y (b i) _)
    rw [hu i, _root_.mul_assoc, IsUnit.mul_iff, IsUnit.mul_iff]
    simp only [u.isUnit, isUnit_gs_top p y (c i), true_and]
  have hW : ∀ i, π ⁻¹ᵁ nonzeroLocus (σ i) = gn ⁻¹ᵁ ((𝟙 XA) ⁻¹ᵁ nonzeroLocus (b i)) := fun i =>
    TopologicalSpace.Opens.ext (Set.ext fun y => hmem i y)
  refine ⟨?_, fun i => ⟨?_, ?_⟩⟩
  ·
    refine eq_top_iff.2 fun y _ => ?_
    have : gn y ∈ ⨆ i, (𝟙 XA) ⁻¹ᵁ nonzeroLocus (b i) := hb.1 ▸ trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (hmem i y).2 hi⟩
  · rw [hW i]; exact (hb.2 i).1.preimage gn
  · obtain ⟨-, ρ, hρ, hs⟩ := hb.2 i
    have le : π ⁻¹ᵁ nonzeroLocus (σ i) ≤ gn ⁻¹ᵁ ((𝟙 XA) ⁻¹ᵁ nonzeroLocus (b i)) := (hW i).le
    have ge : gn ⁻¹ᵁ ((𝟙 XA) ⁻¹ᵁ nonzeroLocus (b i)) ≤ π ⁻¹ᵁ nonzeroLocus (σ i) := (hW i).ge
    let φ : Γ(XA, (𝟙 XA) ⁻¹ᵁ nonzeroLocus (b i)) →+* Γ(Y, π ⁻¹ᵁ nonzeroLocus (σ i)) :=
      (GlobalTheory.AbLaw.rs Y le).comp (gn.app _).hom
    have gsφ : ∀ y (hy : y ∈ π ⁻¹ᵁ nonzeroLocus (σ i)) (a : Γ(XA, (𝟙 XA) ⁻¹ᵁ nonzeroLocus (b i))),
        gs (𝟙 Y) y _ (φ a) = gs gn y _ a := fun y hy a =>
      (gs_res (𝟙 Y) y le hy _).trans ((gs_pull (𝟙 Y) gn y _ (le hy) a).trans (by rw [Category.id_comp]))
    have hφc : ∀ x : K, φ (GlobalTheory.AbLaw.cst pA _ x) = GlobalTheory.AbLaw.cst p (π ⁻¹ᵁ nonzeroLocus (σ i)) x := fun x =>
      fn_ext fun y hy => by
        rw [gsφ y hy, gs_abCst pA _ gn y (le hy), gs_abCst p _ (𝟙 Y) y hy, hp, Category.id_comp]
    let r : Fin (m + 1) → Γ(Y, π ⁻¹ᵁ nonzeroLocus (σ i)) := fun j =>
      GlobalTheory.AbLaw.cst p (π ⁻¹ᵁ nonzeroLocus (σ i)) ((c j : K) / c i) * φ (ρ j)
    refine ⟨r, ?_, ?_⟩
    · intro j ch a ha hch
      obtain ⟨jA, hjA⟩ := exists_chart hLA (gn a)
      obtain ⟨u, hu⟩ := H a ch (fun _ => jA) (GlobalTheory.SectionRingIso.mem_ch.1 hch) hjA
      have haW : a ∈ π ⁻¹ᵁ nonzeroLocus (σ i) := ha
      have haV : gn a ∈ (𝟙 XA) ⁻¹ᵁ nonzeroLocus (b i) := le haW
      have hA : (𝟙 XA) (gn a) ∈ secChart LA (fun _ => jA) := GlobalTheory.SectionRingIso.mem_ch.2 hjA
      have key : ∀ j', secGerm gn a (b j') (fun _ => jA) =
          (gn.stalkMap a).hom (secGerm (𝟙 XA) (gn a) (b j') (fun _ => jA)) := fun j' => by
        have := secGerm_comp gn (𝟙 XA) a (b j') hA
        rwa [Category.comp_id] at this
      have e := congrArg (gn.stalkMap a).hom (hρ j (fun _ => jA) (gn a) haV hA)
      rw [map_mul, ← key, ← key, ← gs_stalkMap gn a _ haV] at e
      have hci : ((c j : K) / c i) * c i = c j := div_mul_cancel₀ _ (c i).ne_zero
      have hcst : gs p a ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (c j : K)) =
          gs p a ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom ((c j : K) / c i)) *
            gs p a ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (c i : K)) := by
        rw [← gs_top_mul, hci]
      rw [hu j, hu i, gs_mul (𝟙 Y) a _ haW, gs_abCst p _ (𝟙 Y) a haW, gsφ a haW, e, Category.id_comp, hcst]
      ring
    · intro f
      obtain ⟨g0, hg0⟩ := (ConcreteCategory.bijective_of_isIso (gn.app ((𝟙 XA) ⁻¹ᵁ nonzeroLocus (b i)))).2
        (GlobalTheory.AbLaw.rs Y ge f)
      have hf : φ g0 = f := by
        change GlobalTheory.AbLaw.rs Y le ((gn.app _).hom g0) = f
        rw [hg0, GlobalTheory.AbLaw.rs_rs, GlobalTheory.AbLaw.rs_self]
      obtain ⟨P, hP⟩ := hs g0
      have hcomp : φ.comp (MvPolynomial.eval₂Hom (GlobalTheory.AbLaw.cst pA _) ρ) =
          MvPolynomial.eval₂Hom (GlobalTheory.AbLaw.cst p (π ⁻¹ᵁ nonzeroLocus (σ i))) (fun j => φ (ρ j)) :=
        MvPolynomial.ringHom_ext (fun x => by rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, hφc])
          (fun j => by rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X'])
      have hρr : ∀ j, MvPolynomial.eval₂Hom (GlobalTheory.AbLaw.cst p (π ⁻¹ᵁ nonzeroLocus (σ i))) r
          (MvPolynomial.C ((c i : K) / c j) * MvPolynomial.X j) = φ (ρ j) := fun j => by
        have h1 : ((c i : K) / c j) * ((c j : K) / c i) = 1 := by
          rw [div_mul_div_comm, _root_.mul_comm (c i : K)]
          exact div_self (mul_ne_zero (c j).ne_zero (c i).ne_zero)
        rw [map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
        change GlobalTheory.AbLaw.cst p _ ((c i : K) / c j) * (GlobalTheory.AbLaw.cst p _ ((c j : K) / c i) * φ (ρ j)) = φ (ρ j)
        rw [← _root_.mul_assoc, ← map_mul, h1, map_one, _root_.one_mul]
      refine ⟨MvPolynomial.bind₁ (fun j => MvPolynomial.C ((c i : K) / c j) * MvPolynomial.X j) P, ?_⟩
      rw [MvPolynomial.eval₂Hom_bind₁]
      simp only [hρr]
      rw [← hf, ← hP, ← hcomp]
      rfl

end GlobalTheory.Mum
end
end
