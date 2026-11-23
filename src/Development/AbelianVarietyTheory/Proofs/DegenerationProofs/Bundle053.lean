module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ProdSurjectiveGeometricPoints
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle043
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle026
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SpecialPoints

theorem exists_torsion_lift {T M N : Type} [CommGroup T] [CommGroup M] [Group N] (i : T →* M) (q : M →* N) (n : ℕ)
    (hqi : ∀ t, q (i t) = 1) (hker : ∀ x, q x = 1 → ∃ t, i t = x) (hq : Function.Surjective q)
    (hT : ∀ t : T, ∃ s : T, s ^ n = t) (b : N) (hb : b ^ n = 1) : ∃ x, x ^ n = 1 ∧ q x = b := by
  obtain ⟨x, rfl⟩ := hq b
  obtain ⟨t, ht⟩ := hker (x ^ n) (by rw [map_pow, hb])
  obtain ⟨s, rfl⟩ := hT t
  refine ⟨x * (i s)⁻¹, ?_, ?_⟩
  · rw [mul_pow, inv_pow, ← map_pow, ht, mul_inv_cancel]
  · rw [map_mul, map_inv, hqi, inv_one, _root_.mul_one]

theorem exists_projection :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegPre V) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (g : GtCoord (IsLocalRing.maximalIdeal V) D 0 G) (κ : Type) [Field κ] [IsAlgClosed κ] (f : V →+* κ), IsLocalHom f → ∃ π : (Over.mk (spMap f) ⟶ G) →* (Over.mk (spMap f) ⟶ D.P.A), (∀ x, ∃ y : Sp κ ⟶ (thickObj V (IsLocalRing.maximalIdeal V) 0 G).left, y ≫ (fstG (IsLocalRing.maximalIdeal V) 0 G).left = x.left ∧ y ≫ g.pG.left = (π x).left) ∧ ∀ n : ℕ, 1 ≤ n → ∀ b, b ^ n = 1 → ∃ x, x ^ n = 1 ∧ π x = b := by
  intro V _ _ _ D G _ _ _ c K _ _ f hf
  obtain ⟨r₀, hr₀⟩ : ∃ r₀ : Sp K ⟶ Sp (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)),
      r₀ ≫ thick V (IsLocalRing.maximalIdeal V) 0 = spMap f := by
    have h₂ : ∀ a ∈ IsLocalRing.maximalIdeal V ^ (0 + 1), f a = 0 := fun a ha => by
      rw [zero_add, pow_one] at ha
      by_contra h
      exact ha (hf.map_nonunit a (Ne.isUnit h))
    refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _ f h₂)), ?_⟩
    rw [← Spec.map_comp]
    rfl
  have := c.q_hom
  have := c.i_hom
  have := c.q_surj
  have hk := c.isKernel
  let T : Over (Sp (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1))) := Over.mk r₀
  let eG := TorsionLift.ptsEquiv (thick V (IsLocalRing.maximalIdeal V) 0) G T _ hr₀
  let eB := TorsionLift.ptsEquiv (thick V (IsLocalRing.maximalIdeal V) 0) D.P.A T _ hr₀
  let q := IsMonHom.monoidHom c.q T
  let i := IsMonHom.monoidHom c.i T
  let e := splitTorusPointsEquiv _ D.X T
  have hqi : ∀ t, q (i t) = 1 := fun t => by
    change (t ≫ c.i) ≫ c.q = 1
    rw [Category.assoc, hk.w, ← Category.assoc, comp_toUnit]
    rfl
  have hker : ∀ x, q x = 1 → ∃ t, i t = x := fun x hx =>
    ⟨hk.lift x (toUnit _) (by rw [show x ≫ c.q = 1 from hx, Hom.one_def]), hk.lift_fst _ _ _⟩
  have hq : Function.Surjective q := fun b => by
    have : LocallyOfFiniteType (c.q.left ≫ (thickObj V (IsLocalRing.maximalIdeal V) 0 D.P.A).hom) := by
      rw [Over.w c.q]
      exact inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom (thick V (IsLocalRing.maximalIdeal V) 0)))
    have : LocallyOfFiniteType c.q.left :=
      locallyOfFiniteType_of_comp _ (thickObj V (IsLocalRing.maximalIdeal V) 0 D.P.A).hom
    obtain ⟨x, hx⟩ := GeomSurj.exists_lift_of_surjective c.q.left b.left
    exact ⟨Over.homMk x (by rw [← Over.w c.q, ← Category.assoc, ← hx]; exact Over.w b),
      Over.OverMorphism.ext hx.symm⟩
  refine ⟨eB.toMonoidHom.comp (q.comp eG.symm.toMonoidHom), fun x => ?_, fun n hn b hb => ?_⟩
  · obtain ⟨x, rfl⟩ := eG.surjective x
    refine ⟨x.left, (TorsionLift.ptsEquiv_left _ _ _ _ _ x).symm, ?_⟩
    change _ = (eB (q (eG.symm (eG x)))).left
    rw [eG.symm_apply_apply]
    exact (Category.assoc _ _ _).symm.trans (TorsionLift.ptsEquiv_left _ _ _ _ _ (q x)).symm
  · obtain ⟨x, hx, hxb⟩ := exists_torsion_lift
      ((i.comp e.symm.toMonoidHom) : (Multiplicative D.X →* Γ(T.left, ⊤)ˣ) →* _) q n
      (fun t => hqi _) (fun x hx => by
        obtain ⟨t, ht⟩ := hker x hx
        exact ⟨e t, (congrArg i (e.symm_apply_apply t)).trans ht⟩) hq
      (TorsLift.exists_pow_eq_hom (M := Γ(T.left, ⊤)ˣ) n (TorsLift.exists_pow_eq_unit K n hn))
      (eB.symm b) (by rw [← map_pow, hb, map_one])
    refine ⟨eG x, by rw [← map_pow, hx, map_one], ?_⟩
    change eB (q (eG.symm (eG x))) = b
    rw [eG.symm_apply_apply, hxb, eB.apply_symm_apply]

end GlobalTheory.SpecialPoints
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem mem_range_of_dominating {V : Type} [CommRing V] [IsDomain V] [ValuationRing V] {W C : Type} [CommRing W]
    [Field C] (α : V →+* W) (β : W →+* C) (ga : FractionRing V →+* C) (hα : IsLocalHom α)
    (hβ : Function.Injective β) (hc : β.comp α = ga.comp (algebraMap V (FractionRing V)))
    (a : FractionRing V) (w : W) (h : β w = ga a) : a ∈ (algebraMap V (FractionRing V)).range := by
  rcases ValuationRing.isInteger_or_isInteger V a with ⟨v, hv⟩ | ⟨v, hv⟩
  · exact ⟨v, hv⟩
  · by_cases ha : a = 0
    · exact ha ▸ Subring.zero_mem _
    have h1 : β (α v) = ga a⁻¹ := by rw [← hv]; exact congrArg (· v) (congrArg DFunLike.coe hc)
    have h2 : α v * w = 1 := hβ (by rw [map_mul, h1, h, ← map_mul, inv_mul_cancel₀ ha, map_one, map_one])
    obtain ⟨u, rfl⟩ := hα.map_nonunit v (IsUnit.of_mul_eq_one _ h2)
    refine ⟨(u⁻¹ : Vˣ), ?_⟩
    rw [← inv_inv a, ← hv]
    exact map_units_inv _ u

theorem point_descends_to_valuationRing : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (W C : Type) [CommRing W] [IsLocalRing W] [Field C] (α : V →+* W) (β : W →+* C) (ga : FractionRing V →+* C), IsLocalHom α → Function.Injective β → β.comp α = ga.comp (algebraMap V (FractionRing V)) → ∀ (X : Scheme.{0}) (y : Sp W ⟶ X) (x : Sp (FractionRing V) ⟶ X), spMap β ≫ y = spMap ga ≫ x → ∃ h : Sp V ⟶ X, spMap α ≫ h = y ∧ jK V ≫ h = x := by
  intro V _ _ _ W C _ _ _ α β ga hα hβ hc X y x hxy
  obtain ⟨U, hU, hp, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤)
    (x := y (IsLocalRing.closedPoint W)) trivial
  have hy : ⊤ ≤ y ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of W) y hp).ge
  have hx : ⊤ ≤ x ⁻¹ᵁ U := by
    intro p _
    have h1 : (spMap β ≫ y) (IsLocalRing.closedPoint C) ∈ U := hy (x := spMap β _) trivial
    rw [hxy] at h1
    obtain rfl : p = spMap ga (IsLocalRing.closedPoint C) :=
      Subsingleton.elim (α := PrimeSpectrum (FractionRing V)) _ _
    exact h1
  have key : ∀ f, β (valR y U f) = ga (valR x U f) := fun f => by
    rw [← HolHom.valR_spMap β y U hy, ← HolHom.valR_spMap ga x U hx, hxy]
  have hinj := IsFractionRing.injective V (FractionRing V)
  let e := RingEquiv.ofBijective (algebraMap V (FractionRing V)).rangeRestrict
    ⟨fun a b h => hinj (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
  let φ : Γ(X, U) →+* V := e.symm.toRingHom.comp ((HolHom.evalHom x U hx).codRestrict _ fun f =>
    mem_range_of_dominating α β ga hα hβ hc _ _ ((key f).trans (by rw [HolHom.valR_eq _ _ hx])))
  have hφ : ∀ f, algebraMap V (FractionRing V) (φ f) = valR x U f := fun f => by
    rw [HolHom.valR_eq _ _ hx]
    exact congrArg Subtype.val (e.apply_symm_apply _)
  let h : Sp V ⟶ X := Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec
  have hh : ⊤ ≤ h ⁻¹ᵁ U := fun p _ => hU.range_fromSpec.le ⟨_, rfl⟩
  have hval : ∀ f, valR h U f = φ f := fun f => by
    rw [HolHom.valR_eq _ _ hh]
    exact congrArg (fun ψ => ψ.hom f) (AffinePointValues.appLE_specMap_fromSpec hU (CommRingCat.ofHom φ) hh)
  refine ⟨h, HolHom.point_ext hU (fun p _ => hh (x := spMap α p) trivial) hy fun f => ?_,
    HolHom.point_ext hU (fun p _ => hh (x := jK V p) trivial) hx fun f => ?_⟩
  · rw [HolHom.valR_spMap _ _ _ hh, hval]
    refine hβ ?_
    rw [key, ← hφ]
    exact congrArg (· (φ f)) (congrArg DFunLike.coe hc)
  · exact (HolHom.valR_spMap (algebraMap V (FractionRing V)) _ _ hh f).trans (by rw [hval, hφ])

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.ZH.FrameNorm
open CrdCalc

section Reg
variable {K C : Type} [Field K] [Field C] {Y : Scheme.{0}} {q : Y ⟶ Sp K} {σ : K →+* C}


variable (q σ) in
def Reg (W : Y.Opens) (F : (Sp C ⟶ Y) → C) : Prop :=
  ∃ r : Γ(Y, W), ∀ x : Sp C ⟶ Y, x ≫ q = spMap σ → ⊤ ≤ x ⁻¹ᵁ W → F x = valR x W r

variable {W : Y.Opens} {F G : (Sp C ⟶ Y) → C}

theorem Reg.mul (hF : Reg q σ W F) (hG : Reg q σ W G) : Reg q σ W fun x => F x * G x := by
  obtain ⟨r, hr⟩ := hF
  obtain ⟨s, hs⟩ := hG
  exact ⟨r * s, fun x hx hW => by rw [valR_mul x W hW, ← hr x hx hW, ← hs x hx hW]⟩

theorem Reg.pow (hF : Reg q σ W F) (n : ℕ) : Reg q σ W fun x => F x ^ n := by
  obtain ⟨r, hr⟩ := hF
  exact ⟨r ^ n, fun x hx hW => by
    beta_reduce
    rw [hr x hx hW, valR_eq x W hW, valR_eq x W hW, map_pow]⟩

theorem Reg.sum {I : Type} [Fintype I] {F : I → (Sp C ⟶ Y) → C} (hF : ∀ i, Reg q σ W (F i)) :
    Reg q σ W fun x => ∑ i, F i x := by
  choose r hr using hF
  refine ⟨∑ i, r i, fun x hx hW => ?_⟩

  rw [valR_eq x W hW, map_sum]
  exact Finset.sum_congr rfl fun i _ => (hr i x hx hW).trans (valR_eq x W hW _)

theorem Reg.const (a : K) : Reg q σ W fun _ => σ a :=
  ⟨constFn q W a, fun x hx hW => (GlobalTheory.Points.valR_constFn_of_over q σ x hx W hW a).symm⟩

theorem Reg.pull {X : Scheme.{0}} (g : Y ⟶ X) {U : X.Opens} (h : W ≤ g ⁻¹ᵁ U) (s : Γ(X, U)) :
    Reg q σ W fun x => valR (x ≫ g) U s :=
  ⟨(g.appLE U W h).hom s, fun x _ hW => (GlobalTheory.Points.valR_appLE x g h hW s).symm⟩

theorem Reg.inv_unit {X : Scheme.{0}} (g : Y ⟶ X) {U : X.Opens} (h : W ≤ g ⁻¹ᵁ U) (s : Γ(X, U)ˣ) :
    Reg q σ W fun x => (valR (x ≫ g) U s.val)⁻¹ := by
  refine ⟨(g.appLE U W h).hom (s⁻¹).val, fun x _ hW => ?_⟩
  have hU : ⊤ ≤ (x ≫ g) ⁻¹ᵁ U := fun _ hz => h (hW hz)
  rw [GlobalTheory.Points.valR_appLE x g h hW]
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← valR_mul _ U hU, Units.mul_inv, valR_eq _ U hU, map_one]

theorem Reg.inv_basicOpen {X : Scheme.{0}} (g : Y ⟶ X) {U : X.Opens} (s : Γ(X, U))
    (h : W ≤ g ⁻¹ᵁ X.basicOpen s) : Reg q σ W fun x => (valR (x ≫ g) U s)⁻¹ := by
  obtain ⟨r, hr⟩ := Reg.inv_unit (q := q) (σ := σ) g h (X.toRingedSpace.isUnit_res_basicOpen s).unit
  refine ⟨r, fun x hx hW => ?_⟩
  rw [← hr x hx hW]
  exact congrArg _ (valR_res (x ≫ g) (X.basicOpen_le s) (fun _ hz => h (hW hz)) s).symm

end Reg

section Val
variable {C : Type} [Field C] {X Y : Scheme.{0}}

theorem val_unit_ne_zero (x : Sp C ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)ˣ) :
    valR x U s.val ≠ 0 := by
  rw [valR_eq x U h]
  exact (s.isUnit.map _).ne_zero

theorem val_zpow (x : Sp C ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)ˣ) (n : ℤ) :
    valR x U (s ^ n).val = valR x U s.val ^ n := by
  rw [valR_eq x U h, valR_eq x U h, ← MonoidHom.coe_coe, ← Units.coe_map, map_zpow, Units.val_zpow_eq_zpow_val]
  rfl

theorem val_res_pull (x : Sp C ⟶ Y) (g : Y ⟶ X) {U : X.Opens} {W : Y.Opens} (e : W ≤ g ⁻¹ᵁ U)
    (h : ⊤ ≤ x ⁻¹ᵁ W) (s : Γ(X, U)ˣ) : valR x W (res e (pullU g U s)).val = valR (x ≫ g) U s.val :=
  GlobalTheory.Points.valR_appLE x g e h s.val

def tv (L : LB X) (x : Sp C ⟶ X) (i j : L.ι) : C := valR x (L.U i ⊓ L.U j) (L.g i j).val

theorem tv_ne_zero (L : LB X) {x : Sp C ⟶ X} {i j : L.ι} (hi : ⊤ ≤ x ⁻¹ᵁ L.U i) (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) :
    tv L x i j ≠ 0 := val_unit_ne_zero x (U := L.U i ⊓ L.U j) (fun _ hz => ⟨hi hz, hj hz⟩) _

theorem tv_self {L : LB X} (hL : L.IsLB) {x : Sp C ⟶ X} {i : L.ι} (hi : ⊤ ≤ x ⁻¹ᵁ L.U i) :
    tv L x i i = 1 := by
  have e := congrArg (fun u : Γ(X, L.U i)ˣ => valR x (L.U i) u.val) (hL.g_self i)
  refine (valR_res x (le_inf le_rfl le_rfl) hi _).symm.trans (e.trans ?_)
  rw [valR_eq x _ hi, Units.val_one, map_one]

theorem le_wchart {L : LB X} {I : Type} [Fintype I] {φ : I → (Y ⟶ X)} {x : Sp C ⟶ Y} {j : I → L.ι}
    (h : ∀ k, ⊤ ≤ (x ≫ φ k) ⁻¹ᵁ L.U (j k)) : ⊤ ≤ x ⁻¹ᵁ LB.wchart L φ j :=
  fun _ hz => Set.mem_iInter.2 fun k => h k hz

theorem tv_linComb (L : LB X) {I : Type} [Fintype I] (φ : I → (Y ⟶ X)) (ε : I → ℤ) {x : Sp C ⟶ Y}
    {j j' : I → L.ι} (h : ∀ k, ⊤ ≤ (x ≫ φ k) ⁻¹ᵁ L.U (j k)) (h' : ∀ k, ⊤ ≤ (x ≫ φ k) ⁻¹ᵁ L.U (j' k)) :
    tv (LB.LinComb L φ ε) x j j' = ∏ k, tv L (x ≫ φ k) (j k) (j' k) ^ ε k := by
  have hh : ⊤ ≤ x ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j') := fun _ hz => ⟨le_wchart h hz, le_wchart h' hz⟩
  have A : ∀ u : I → Γ(Y, LB.wchart L φ j ⊓ LB.wchart L φ j')ˣ,
      valR x _ (∏ k, u k ^ ε k).val = ∏ k, valR x _ (u k).val ^ ε k := fun u => by
    rw [valR_eq x _ hh, Units.coe_prod, map_prod]
    exact Finset.prod_congr rfl fun k _ => (valR_eq x _ hh _).symm.trans (val_zpow x hh _ _)
  refine (A _).trans (Finset.prod_congr rfl fun k _ => ?_)
  exact congrArg (· ^ ε k) (val_res_pull x (φ k) (U := L.U (j k) ⊓ L.U (j' k)) _ hh (L.g (j k) (j' k)))

theorem sec_val {L : LB X} (s : L.Sec) {x : Sp C ⟶ X} {i j : L.ι} (hi : ⊤ ≤ x ⁻¹ᵁ L.U i)
    (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) : valR x (L.U i) (s.f i) = tv L x i j * valR x (L.U j) (s.f j) := by
  have hh : ⊤ ≤ x ⁻¹ᵁ (L.U i ⊓ L.U j) := fun y hy => ⟨hi hy, hj hy⟩
  have e := congrArg (valR x (L.U i ⊓ L.U j)) (s.compat i j)
  rw [valR_mul x _ hh] at e
  exact (valR_res x inf_le_left hh _).symm.trans (e.trans (congrArg _ (valR_res x inf_le_right hh _)))

theorem gen_val {L : LB X} {t : L.Gen} (ht : t.IsGen) {x : Sp C ⟶ X} {i j : L.ι} (hi : ⊤ ≤ x ⁻¹ᵁ L.U i)
    (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) : valR x (L.U i) (t.s i).val = tv L x i j * valR x (L.U j) (t.s j).val :=
  sec_val ⟨fun i => (t.s i).val, fun i j => congrArg Units.val (ht i j)⟩ hi hj

end Val

structure IsoVal {K C : Type} [Field K] [Field C] {X H Y : Scheme.{0}} (q : Y ⟶ Sp K) (σ : K →+* C)
    (L : LB X) (M : LB H) (ψ : Y ⟶ X) (j : Y ⟶ H) (ω : (Sp C ⟶ Y) → M.ι → L.ι → C) : Prop where
  ne : ∀ x l m, ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U l → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U m → ω x l m ≠ 0
  left : ∀ x l l' m, ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U l → ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U l' → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U m →
    ω x l m = tv M (x ≫ j) l l' * ω x l' m
  right : ∀ x l m m', ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U l → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U m → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U m' →
    ω x l m * tv L (x ≫ ψ) m m' = ω x l m'
  reg : ∀ (g : Y ⟶ Y) (W : Y.Opens) l m, W ≤ (g ≫ j) ⁻¹ᵁ M.U l → W ≤ (g ≫ ψ) ⁻¹ᵁ L.U m →
    Reg q σ W (fun x => ω (x ≫ g) l m) ∧ Reg q σ W (fun x => (ω (x ≫ g) l m)⁻¹)

theorem exists_isoVal {K C : Type} [Field K] [Field C] {X H Y : Scheme.{0}} (q : Y ⟶ Sp K) (σ : K →+* C)
    {L : LB X} {M : LB H} (hL : L.IsLB) (hM : M.IsLB) {ψ : Y ⟶ X} {j : Y ⟶ H}
    (h : LBIso (L.pull ψ) (M.pull j)) : ∃ ω, IsoVal q σ L M ψ j ω := by
  obtain ⟨w, hw⟩ := h
  have mem : ∀ {x : Sp C ⟶ Y} {l m}, ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U l → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U m →
      ⊤ ≤ x ⁻¹ᵁ (LB.div (M.pull j) (L.pull ψ)).U (fun _ => l, fun _ => m) := fun hl hm _ hz =>
    ⟨Set.mem_iInter.2 fun _ => hl hz, Set.mem_iInter.2 fun _ => hm hz⟩
  have key : ∀ (x : Sp C ⟶ Y) l l' m m', ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U l → ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U l' →
      ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U m → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U m' →
      valR x _ (w.s (fun _ => l, fun _ => m)).val =
        tv M (x ≫ j) l l' * (tv L (x ≫ ψ) m m')⁻¹ * valR x _ (w.s (fun _ => l', fun _ => m')).val := by
    intro x l l' m m' hl hl' hm hm'
    refine (gen_val hw (mem hl hm) (mem hl' hm')).trans (congrArg (· * _) ?_)
    have hh : ⊤ ≤ x ⁻¹ᵁ ((LB.div (M.pull j) (L.pull ψ)).U (fun _ => l, fun _ => m) ⊓
        (LB.div (M.pull j) (L.pull ψ)).U (fun _ => l', fun _ => m')) :=
      fun _ hz => ⟨mem hl hm hz, mem hl' hm' hz⟩
    refine (valR_mul x _ hh _ _).trans (congrArg₂ (· * ·) ?_ ?_)
    · refine (valR_res x _ hh _).trans ((tv_linComb M _ _ (fun _ => hl) (fun _ => hl')).trans ?_)
      simp
    · rw [← zpow_neg_one, ← zpow_neg_one]
      refine (val_zpow x hh _ _).trans (congrArg (· ^ (-1 : ℤ)) ?_)
      refine (valR_res x _ hh _).trans ((tv_linComb L _ _ (fun _ => hm) (fun _ => hm')).trans ?_)
      simp
  refine ⟨fun x l m => valR x _ (w.s (fun _ => l, fun _ => m)).val,
    fun x l m hl hm => val_unit_ne_zero x (mem hl hm) _, fun x l l' m hl hl' hm => ?_,
    fun x l m m' hl hm hm' => ?_, fun g W l m hl hm => ?_⟩
  · rw [key x l l' m m hl hl' hm hm, tv_self hL hm, inv_one, _root_.mul_one]
  · rw [key x l l m m' hl hl hm hm', tv_self hM hl, _root_.one_mul, mul_right_comm,
      inv_mul_cancel₀ (tv_ne_zero L hm hm'), _root_.one_mul]
  · have e : W ≤ g ⁻¹ᵁ (LB.div (M.pull j) (L.pull ψ)).U (fun _ => l, fun _ => m) := fun _ hz =>
      ⟨Set.mem_iInter.2 fun _ => hl hz, Set.mem_iInter.2 fun _ => hm hz⟩
    exact ⟨Reg.pull g e _, Reg.inv_unit g e _⟩

end GlobalTheory.ZH.FrameNorm
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem epi_spMap_of_finite_of_injective (V W : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [CommRing W] [IsDomain W] [Algebra V W] [Module.Finite V W]
    (hinj : Function.Injective (algebraMap V W)) : Epi (spMap (algebraMap V W)) := by
  have : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective V W).2 hinj
  have hfl : Module.Flat V W := inferInstance
  have : Flat (spMap (algebraMap V W)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 hfl
  have : Surjective (spMap (algebraMap V W)) :=
    ⟨Algebra.IsIntegral.comap_surjective V W⟩
  exact Flat.epi_of_flat_of_surjective _

theorem exists_torsion_lift_of_generic_rational : (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (W C : Type) [CommRing W] [IsLocalRing W] [Field C] (α : V →+* W) (β : W →+* C) (ga : FractionRing V →+* C), IsLocalHom α → Function.Injective β → β.comp α = ga.comp (algebraMap V (FractionRing V)) → ∀ (X : Scheme.{0}) (y : Sp W ⟶ X) (x : Sp (FractionRing V) ⟶ X), spMap β ≫ y = spMap ga ≫ x → ∃ h : Sp V ⟶ X, spMap α ≫ h = y ∧ jK V ≫ h = x) → UnramExtSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] (C : Type) [Field C] [IsAlgClosed C] (ga : FractionRing V →+* C) (m : ℕ), IsUnit (m : V) → (∀ y : Over.mk (spMap ga ≫ jK V) ⟶ G, y ^ m = 1 → ∃ x : Sp (FractionRing V) ⟶ G.left, spMap ga ≫ x = y.left) → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (f : V →+* κ), IsLocalHom f → ∀ x : Over.mk (spMap f) ⟶ G, x ^ m = 1 → ∃ h : baseOver (Sp V) ⟶ G, h ^ m = 1 ∧ spMap f ≫ h.left = x.left := by
  intro hD hU V _ _ _ hV G _ _ _ _ C _ _ ga m hm hrat κ _ _ f hf x hx
  obtain ⟨W, _, _, _, _, _, f', hfin, hinj, hloc, -, hcomp, hy⟩ :=
    exists_finite_extension_torsion_lift hU V G m hm κ f hf {x} (by simpa using hx)
  obtain ⟨y, hy, hy'⟩ := hy x (Finset.mem_singleton_self x)
  let : Algebra V C := (ga.comp (algebraMap V (FractionRing V))).toAlgebra
  have hC : Function.Injective (algebraMap V C) :=
    ga.injective.comp (IsFractionRing.injective V (FractionRing V))
  have : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective V W).2 hinj
  have : FaithfulSMul V C := (faithfulSMul_iff_algebraMap_injective V C).2 hC
  let β : W →ₐ[V] C := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hβ : Function.Injective β.toRingHom := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := V) ?_
    change Ideal.comap (algebraMap V W) (RingHom.ker β.toRingHom) = ⊥
    rw [RingHom.comap_ker]
    refine (RingHom.injective_iff_ker_eq_bot _).1 ?_
    rw [show β.toRingHom.comp (algebraMap V W) = algebraMap V C from β.comp_algebraMap]
    exact hC
  have hβα : β.toRingHom.comp (algebraMap V W) = ga.comp (algebraMap V (FractionRing V)) :=
    β.comp_algebraMap
  have hw : spMap β.toRingHom ≫ spMap (algebraMap V W) = spMap ga ≫ jK V := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hβα]
  let j : Over.mk (spMap ga ≫ jK V) ⟶ Over.mk (spMap (algebraMap V W)) :=
    Over.homMk (spMap β.toRingHom) hw
  obtain ⟨x₀, hx₀⟩ := hrat (j ≫ y) (by rw [← comp_pow, hy, comp_one])
  obtain ⟨h₀, hh₀, -⟩ := hD V W C (algebraMap V W) β.toRingHom ga hloc hβ hβα G.left y.left x₀
    hx₀.symm
  have hepi := epi_spMap_of_finite_of_injective V W hinj
  let h : baseOver (Sp V) ⟶ G := Over.homMk h₀ (by
    rw [← cancel_epi (spMap (algebraMap V W))]
    exact ((reassoc_of% hh₀) _).trans ((Over.w y).trans (Category.comp_id _).symm))
  let a : Over.mk (spMap (algebraMap V W)) ⟶ baseOver (Sp V) :=
    Over.homMk (spMap (algebraMap V W)) (Category.comp_id _)
  have ha : a ≫ h = y := Over.OverMorphism.ext hh₀
  have : Epi a.left := hepi
  have : Epi a := Over.epi_of_epi_left a
  refine ⟨h, ?_, ?_⟩
  · rw [← cancel_epi a, comp_pow, ha, hy, comp_one]
  · rw [← hy', ← hh₀, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
    rfl

end GlobalTheory
end
