module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1056
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle193
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle377
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle386
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1053
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle865
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.Bundle001
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PinchLift

theorem lbIso_pull_of_genOn (X Y : Scheme.{0}) (f : Y ⟶ X) (L : LB Y) (J : Type) (W : J → X.Opens)
    (g : ∀ x y, Γ(X, W x ⊓ W y)ˣ) (s : ∀ x k, Γ(Y, L.U k ⊓ f ⁻¹ᵁ W x)ˣ)
    (hs : ∀ x, GlobalTheory.PinchLift.GenOn L (f ⁻¹ᵁ W x) (s x))
    (hg : ∀ x y (t : Y) (k : L.ι), f t ∈ W x → f t ∈ W y → t ∈ L.U k →
      gm f t (W x ⊓ W y) (g x y) =
        gm (𝟙 Y) t (L.U k ⊓ f ⁻¹ᵁ W y) (s y k) * (gm (𝟙 Y) t (L.U k ⊓ f ⁻¹ᵁ W x) (s x k))⁻¹) :
    LBIso L ((⟨J, W, g⟩ : LB X).pull f) := by
  have le : ∀ p : (PUnit → J) × L.ι, ((⟨J, W, g⟩ : LB X).pull f).U p.1 ⊓ L.U p.2 ≤
      L.U p.2 ⊓ f ⁻¹ᵁ W (p.1 PUnit.unit) := fun p y h =>
    ⟨h.2, (mem_pull (L := (⟨J, W, g⟩ : LB X)) (F := f)).1 h.1⟩
  refine ⟨⟨fun p => res (le p) (s (p.1 PUnit.unit) p.2)⁻¹⟩, (isGen_iff_germ _).2 fun y p q hp hq => ?_⟩
  have v : ∀ p : (PUnit → J) × L.ι, y ∈ ((⟨J, W, g⟩ : LB X).pull f).U p.1 ⊓ L.U p.2 →
      gm (𝟙 Y) y _ (res (le p) (s (p.1 PUnit.unit) p.2)⁻¹) =
        (gm (𝟙 Y) y (L.U p.2 ⊓ f ⁻¹ᵁ W (p.1 PUnit.unit)) (s (p.1 PUnit.unit) p.2))⁻¹ := fun p hp =>
    (gm_res _ y _ hp _).trans (map_inv _ _)
  have hp' := le p hp
  have hq' := le q hq
  have e1 := gm_pull_g (⟨J, W, g⟩ : LB X) f (𝟙 Y) y p.1 q.1 hp.1 hq.1
  have e2 : gm (𝟙 Y ≫ f) y (W (p.1 PUnit.unit) ⊓ W (q.1 PUnit.unit)) (g _ _) =
      gm f y (W (p.1 PUnit.unit) ⊓ W (q.1 PUnit.unit)) (g _ _) := by
    rw [Category.id_comp]
  have e3 := hg (p.1 PUnit.unit) (q.1 PUnit.unit) y p.2 hp'.2 hq'.2 hp'.1
  have e4 := hs (q.1 PUnit.unit) p.2 q.2 y hp'.1 hq'.1 hq'.2
  have e5 := (e1.trans e2).trans (e3.trans (congrArg (· * _) e4))
  refine (v p hp).trans (Eq.trans ?_ (congrArg₂ (· * ·)
    ((gm_div' ((⟨J, W, g⟩ : LB X).pull f) L (𝟙 Y) y p q hp hq).trans (congrArg (· * _) e5)) (v q hq)).symm)
  have key : ∀ {G : Type} [CommGroup G] (a b c : G), c⁻¹ = a * b * c⁻¹ * a⁻¹ * b⁻¹ := by
    intro G _ a b c
    rw [mul_assoc (a * b * c⁻¹), ← mul_inv, mul_right_comm, mul_inv_cancel, _root_.one_mul]
  exact key _ _ _

end GlobalTheory.PinchLift
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Pinch

theorem commGroup_mul_eq_mul_mul_div {G : Type*} [CommGroup G] (g h w b a : G) :
    g * b * (g * h⁻¹ * w * (h * a))⁻¹ = b * (w * a)⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem comm_aux₂ {G : Type*} [CommGroup G] (w b a : G) : b = w * (b * (w * a)⁻¹ * a) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem locGen_gm {Y T : Scheme.{0}} {L : LB Y} {V : Y.Opens} {a : ∀ k, Γ(Y, V ⊓ L.U k)ˣ} (h : LocGen L V a)
    (f : T ⟶ Y) (t : T) (k k' : L.ι) (hv : f t ∈ V) (hk : f t ∈ L.U k) (hk' : f t ∈ L.U k') :
    gm f t (V ⊓ L.U k) (a k) = gm f t (L.U k ⊓ L.U k') (L.g k k') * gm f t (V ⊓ L.U k') (a k') := by
  have e : res (inf_le_left : V ⊓ L.U k ⊓ L.U k' ≤ V ⊓ L.U k) (a k) =
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right : V ⊓ L.U k ⊓ L.U k' ≤ L.U k ⊓ L.U k') (L.g k k') *
      res (le_inf (inf_le_left.trans inf_le_left) inf_le_right : V ⊓ L.U k ⊓ L.U k' ≤ V ⊓ L.U k') (a k') := by
    apply unit_ext
    intro y hy
    rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy, gm_res _ y _ hy]
    exact h y k k' hy.1.1 hy.1.2 hy.2
  have hm : f t ∈ V ⊓ L.U k ⊓ L.U k' := ⟨⟨hv, hk⟩, hk'⟩
  have := congrArg (gm f t (V ⊓ L.U k ⊓ L.U k')) e
  rwa [map_mul, gm_res _ _ _ hm, gm_res _ _ _ hm, gm_res _ _ _ hm] at this

theorem iso_gm {X' Z Z' : Scheme.{0}} {i' : Z' ⟶ X'} {p' : Z' ⟶ Z} {L' : LB X'} {N : LB Z}
    {w : LB.Iso (L'.pull i') (N.pull p')} (hw : w.IsGen) (x : Z') (k k' : L'.ι) (l l' : N.ι)
    (hk : i' x ∈ L'.U k) (hk' : i' x ∈ L'.U k') (hl : p' x ∈ N.U l) (hl' : p' x ∈ N.U l') :
    gm (𝟙 Z') x ((N.pull p').U (fun _ ↦ l) ⊓ (L'.pull i').U (fun _ ↦ k)) (w.s (fun _ ↦ l, fun _ ↦ k)) =
      gm p' x (N.U l ⊓ N.U l') (N.g l l') * (gm i' x (L'.U k ⊓ L'.U k') (L'.g k k'))⁻¹ *
        gm (𝟙 Z') x ((N.pull p').U (fun _ ↦ l') ⊓ (L'.pull i').U (fun _ ↦ k')) (w.s (fun _ ↦ l', fun _ ↦ k')) := by
  have hp : x ∈ (N.pull p').U (fun _ ↦ l) ⊓ (L'.pull i').U (fun _ ↦ k) := ⟨mem_pull.2 hl, mem_pull.2 hk⟩
  have hq : x ∈ (N.pull p').U (fun _ ↦ l') ⊓ (L'.pull i').U (fun _ ↦ k') := ⟨mem_pull.2 hl', mem_pull.2 hk'⟩
  have e := (isGen_iff_germ w).1 hw x (fun _ ↦ l, fun _ ↦ k) (fun _ ↦ l', fun _ ↦ k') hp hq
  have d := gm_div' (N.pull p') (L'.pull i') (𝟙 Z') x (fun _ ↦ l, fun _ ↦ k) (fun _ ↦ l', fun _ ↦ k') hp hq
  have g1 := gm_pull_g N p' (𝟙 Z') x (fun _ ↦ l) (fun _ ↦ l') hp.1 hq.1
  have g2 := gm_pull_g L' i' (𝟙 Z') x (fun _ ↦ k) (fun _ ↦ k') hp.2 hq.2
  rw [Category.id_comp] at g1 g2
  rw [d, g1, g2] at e
  exact e

theorem exists_ratio_unit : ∀ (X' Z Z' : Scheme.{0}) (i' : Z' ⟶ X') (p' : Z' ⟶ Z) (L' : LB X') (N : LB Z), L'.IsLB → N.IsLB → ∀ (w : LB.Iso (L'.pull i') (N.pull p')), w.IsGen → ∀ (V' : X'.Opens) (V : Z.Opens) (a : ∀ k, Γ(X', V' ⊓ L'.U k)ˣ) (b : ∀ l, Γ(Z, V ⊓ N.U l)ˣ), GlobalTheory.Pinch.LocGen L' V' a → GlobalTheory.Pinch.LocGen N V b → ∀ O : Z'.Opens, O ≤ i' ⁻¹ᵁ V' → O ≤ p' ⁻¹ᵁ V → ∃ u : Γ(Z', O)ˣ, ∀ (z : Z') (k : L'.ι) (l : N.ι), z ∈ O → i' z ∈ L'.U k → p' z ∈ N.U l → gm p' z (V ⊓ N.U l) (b l) = gm (𝟙 Z') z ((N.pull p').U (fun _ ↦ l) ⊓ (L'.pull i').U (fun _ ↦ k)) (w.s (fun _ ↦ l, fun _ ↦ k)) * (gm (𝟙 Z') z O u * gm i' z (V' ⊓ L'.U k) (a k)) := by
  intro X' Z Z' i' p' L' N hL' hN w hw V' V a b ha hb O hO hO'
  let W : L'.ι × N.ι → Z'.Opens := fun q ↦ O ⊓ (i' ⁻¹ᵁ (V' ⊓ L'.U q.1) ⊓ p' ⁻¹ᵁ (V ⊓ N.U q.2))
  have hW : ∀ q, W q ≤ O := fun q ↦ inf_le_left
  have hWw : ∀ q, W q ≤ (N.pull p').U (fun _ ↦ q.2) ⊓ (L'.pull i').U (fun _ ↦ q.1) := fun q x hx ↦
    ⟨mem_pull.2 hx.2.2.2, mem_pull.2 hx.2.1.2⟩
  have hWb : ∀ q, W q ≤ p' ⁻¹ᵁ (V ⊓ N.U q.2) := fun q x hx ↦ hx.2.2
  have hWa : ∀ q, W q ≤ i' ⁻¹ᵁ (V' ⊓ L'.U q.1) := fun q x hx ↦ hx.2.1
  let u : ∀ q, Γ(Z', W q)ˣ := fun q ↦ res (hWb q) (pullU p' _ (b q.2)) *
    (res (hWw q) (w.s (fun _ ↦ q.2, fun _ ↦ q.1)) * res (hWa q) (pullU i' _ (a q.1)))⁻¹
  have gu : ∀ q, ∀ x ∈ W q, gm (𝟙 Z') x (W q) (u q) = gm p' x _ (b q.2) *
      (gm (𝟙 Z') x ((N.pull p').U (fun _ ↦ q.2) ⊓ (L'.pull i').U (fun _ ↦ q.1)) (w.s (fun _ ↦ q.2, fun _ ↦ q.1)) *
        gm i' x _ (a q.1))⁻¹ := by
    intro q x hx
    simp only [u, map_mul, map_inv]
    rw [gm_rp₁ p' x _ _ (hWb q) hx, gm_rp₁ i' x _ _ (hWa q) hx]
    exact congrArg (fun t ↦ _ * (t * _)⁻¹) (gm_res (𝟙 Z') x (hWw q) hx _)
  have cover : O ≤ iSup W := by
    intro x hx
    obtain ⟨k, hk⟩ := exists_chart hL' (i' x)
    obtain ⟨l, hl⟩ := exists_chart hN (p' x)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(k, l), hx, ⟨hO hx, hk⟩, ⟨hO' hx, hl⟩⟩
  obtain ⟨s, hs⟩ := glue_unit O W hW cover u (by
    rintro ⟨k, l⟩ ⟨k', l'⟩ x hx
    rw [gu _ x hx.1, gu _ x hx.2]
    have hx1 := hx.1
    have hx2 := hx.2
    rw [locGen_gm hb p' x l l' hx1.2.2.1 hx1.2.2.2 hx2.2.2.2, locGen_gm ha i' x k k' hx1.2.1.1 hx1.2.1.2 hx2.2.1.2,
      iso_gm hw x k k' l l' hx1.2.1.2 hx2.2.1.2 hx1.2.2.2 hx2.2.2.2]
    exact commGroup_mul_eq_mul_mul_div _ _ _ _ _)
  refine ⟨s, fun z k l hz hk hl ↦ ?_⟩
  have hzW : z ∈ W (k, l) := ⟨hz, ⟨hO hz, hk⟩, ⟨hO' hz, hl⟩⟩
  have e := gu (k, l) z hzW
  rw [← hs (k, l), gm_res _ z _ hzW] at e
  rw [e]
  exact comm_aux₂ _ _ _

end GlobalTheory.Pinch
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CharKer

theorem appLE_eq_of_eq' {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h; rfl

theorem app_map_eq_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (x : Γ(Y, U)) :
    (X.presheaf.map (homOfLE h).op).hom ((f.app U).hom x) = (f.appLE U V h).hom x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]

theorem appLE_map_eq_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) (V V' : X.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (h' : V' ≤ V) (x : Γ(Y, U)) :
    (X.presheaf.map (homOfLE h').op).hom ((f.appLE U V h).hom x) = (f.appLE U V' (h'.trans h)).hom x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem map_app_map_eq_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) {U U' : Y.Opens} (hU : U' ≤ U)
    (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U') (h' : V ≤ f ⁻¹ᵁ U) (x : Γ(Y, U)) :
    (X.presheaf.map (homOfLE h).op).hom ((f.app U').hom ((Y.presheaf.map (homOfLE hU).op).hom x)) =
      (f.appLE U V h').hom x := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE,
    ← Category.assoc, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

theorem appLE_map_top {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U)
    (x : Γ(Y, ⊤)) :
    (f.appLE U V e).hom ((Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom x) =
      (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom (f.appTop.hom x) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  congr 2
  simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]
  rw [Scheme.Hom.naturality_assoc, ← Functor.map_comp]
  rfl

theorem map_map_apply {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (h₃ : W ≤ U)
    (x : Γ(X, U)) : (X.presheaf.map (homOfLE h₂).op).hom ((X.presheaf.map (homOfLE h₁).op).hom x) =
      (X.presheaf.map (homOfLE h₃).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

end GlobalTheory.CharKer

namespace GlobalTheory.CharKer

theorem exists_local_charUnit : ∀ (X Y Z W : Scheme.{0}) (p : X ⟶ Y) (a b : Z ⟶ X) (m₁₂ m₂₃ m₁₃ : W ⟶ Z) (χ : Γ(Z, ⊤)ˣ), IsAffineHom p → Flat p → Surjective p → IsPullback b a p p → IsPullback m₁₂ m₂₃ a b → m₁₃ ≫ b = m₁₂ ≫ b → m₁₃ ≫ a = m₂₃ ≫ a → pullTop m₁₃ χ = pullTop m₁₂ χ * pullTop m₂₃ χ → ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧ ∃ e : Γ(X, p ⁻¹ᵁ V)ˣ, ∀ (W' : Z.Opens) (h₁ : W' ≤ a ⁻¹ᵁ (p ⁻¹ᵁ V)) (h₂ : W' ≤ b ⁻¹ᵁ (p ⁻¹ᵁ V)), res h₁ (pullU a _ e) = res le_top χ * res h₂ (pullU b _ e) := by
  intro X Y Z W p a b m₁₂ m₂₃ m₁₃ χ hpA hpF hpS sq₁ sq₂ e₁₃b e₁₃a hχ y
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := y) (U := ⊤) trivial
  have ha : IsAffineHom a := MorphismProperty.of_isPullback (P := @IsAffineHom) sq₁ hpA
  have hab : a ⁻¹ᵁ (p ⁻¹ᵁ V) = b ⁻¹ᵁ (p ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, sq₁.w]
  have h12 : m₂₃ ⁻¹ᵁ (a ⁻¹ᵁ (p ⁻¹ᵁ V)) ≤ m₁₂ ⁻¹ᵁ (a ⁻¹ᵁ (p ⁻¹ᵁ V)) := by
    rw [← Scheme.Hom.comp_preimage m₁₂ a, sq₂.w, Scheme.Hom.comp_preimage, ← hab]
  have h13 : m₂₃ ⁻¹ᵁ (a ⁻¹ᵁ (p ⁻¹ᵁ V)) ≤ m₁₃ ⁻¹ᵁ (a ⁻¹ᵁ (p ⁻¹ᵁ V)) := by
    rw [← Scheme.Hom.comp_preimage m₁₃ a, e₁₃a, Scheme.Hom.comp_preimage]
  have hV₀ : IsAffineOpen (p ⁻¹ᵁ V) := hV.preimage p
  have hV₁ : IsAffineOpen (a ⁻¹ᵁ (p ⁻¹ᵁ V)) := hV₀.preimage a
  have P₁ := ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPushout_appLE sq₁ hpA hV hV₀ le_rfl hab.le
  rw [Scheme.Hom.appLE_eq_app] at P₁
  have P₂ := ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPushout_appLE sq₂ ha hV₀ hV₁ hab.le h12
  have E₁ : b.appLE (p ⁻¹ᵁ V) (a ⁻¹ᵁ (p ⁻¹ᵁ V)) hab.le ≫ m₁₃.appLE _ _ h13 =
      b.appLE (p ⁻¹ᵁ V) (a ⁻¹ᵁ (p ⁻¹ᵁ V)) hab.le ≫ m₁₂.appLE _ _ h12 := by
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    exact appLE_eq_of_eq' e₁₃b _ _ _ _
  have E₂ : a.app (p ⁻¹ᵁ V) ≫ m₁₃.appLE _ _ h13 = a.app (p ⁻¹ᵁ V) ≫ m₂₃.app _ := by
    rw [Scheme.Hom.app_eq_appLE a, Scheme.Hom.app_eq_appLE m₂₃, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.appLE_comp_appLE]
    exact appLE_eq_of_eq' e₁₃a _ _ _ _
  have FF := GlobalTheory.T.faithfullyFlat_app_of_isAffineHom_flat_surjective' X Y p V hpA hpF hpS hV
  let c : Γ(Z, a ⁻¹ᵁ (p ⁻¹ᵁ V))ˣ := res le_top χ
  have hc : (m₁₃.appLE _ _ h13).hom (c : Γ(Z, a ⁻¹ᵁ (p ⁻¹ᵁ V))) =
      (m₁₂.appLE _ _ h12).hom (c : Γ(Z, a ⁻¹ᵁ (p ⁻¹ᵁ V))) * (m₂₃.app _).hom (c : Γ(Z, a ⁻¹ᵁ (p ⁻¹ᵁ V))) := by
    have := congrArg (fun u => ((res (le_top : m₂₃ ⁻¹ᵁ (a ⁻¹ᵁ (p ⁻¹ᵁ V)) ≤ ⊤) u : Γ(W, _)ˣ) :
      Γ(W, m₂₃ ⁻¹ᵁ (a ⁻¹ᵁ (p ⁻¹ᵁ V))))) hχ
    simp only [map_mul, Units.val_mul, res, pullTop, Units.coe_map, MonoidHom.coe_coe] at this
    rw [Scheme.Hom.app_eq_appLE m₂₃]
    simp only [c, res, Units.coe_map, MonoidHom.coe_coe]
    rw [appLE_map_top, appLE_map_top, appLE_map_top]
    exact this
  obtain ⟨s, hs, x, x', hxx', hx⟩ := GlobalTheory.T.locally_trivial_unit_cocycle_faithfully_flat _ _ _ _ (p.app V) _ _ _ _ _ P₁ P₂ E₁ E₂ FF c hc
    (hV.primeIdealOf ⟨y, hyV⟩).asIdeal inferInstance
  have hyS : y ∈ Y.basicOpen s := by
    have h0 : hV.primeIdealOf ⟨y, hyV⟩ ∈ hV.fromSpec ⁻¹ᵁ Y.basicOpen s := by
      rw [hV.fromSpec_preimage_basicOpen]; exact hs
    have h1 := hV.fromSpec_primeIdealOf ⟨y, hyV⟩
    have h0' : hV.fromSpec (hV.primeIdealOf ⟨y, hyV⟩) ∈ Y.basicOpen s := h0
    rwa [h1] at h0'
  refine ⟨Y.basicOpen s, hyS, ?_⟩
  have hle : p ⁻¹ᵁ Y.basicOpen s ≤ p ⁻¹ᵁ V := fun z hz => Y.basicOpen_le s hz
  have hpre := Scheme.preimage_basicOpen p s
  have hu : IsUnit ((X.presheaf.map (homOfLE hle).op).hom x) := by
    apply isUnit_of_mul_isUnit_left (y := (X.presheaf.map (homOfLE hle).op).hom x')
    rw [← map_mul, hxx']
    have h2 := RingedSpace.isUnit_res_basicOpen X.toRingedSpace ((p.app V).hom s)
    have h3 := h2.map (X.presheaf.map (homOfLE hpre.le).op).hom
    rw [← map_map_apply (X.basicOpen_le ((p.app V).hom s)) hpre.le hle]
    exact h3
  refine ⟨hu.unit, fun W' h₁ h₂ => ?_⟩
  have hW : W' ≤ a ⁻¹ᵁ (p ⁻¹ᵁ V) := fun z hz => hle (h₁ hz)
  have hWb : W' ≤ b ⁻¹ᵁ (p ⁻¹ᵁ V) := hW.trans hab.le
  apply Units.ext
  simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe, IsUnit.unit_spec, Units.val_mul]
  rw [map_app_map_eq_appLE a hle W' h₁ hW, map_app_map_eq_appLE b hle W' h₂ hWb]
  have := congrArg (Z.presheaf.map (homOfLE hW).op).hom hx
  rw [map_mul, app_map_eq_appLE, appLE_map_eq_appLE] at this
  rw [this]
  congr 1
  simp only [c, res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

end GlobalTheory.CharKer
end
end

section

noncomputable section

open IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.OrbFinAf
open scoped TensorProduct

namespace GlobalTheory.OrbFinAf

variable {p : ℕ} [Fact p.Prime]

theorem normStep_isIntV_add {G : HTGroup p} {v : AwayP p} {y z : Qv v ⊗[ℚ] G.C} (hy : IsIntV G v y)
    (hz : IsIntV G v z) : IsIntV G v (y + z) := by
  intro i; rw [map_add (f := _), Finsupp.add_apply]; exact add_mem (hy i) (hz i)

theorem normStep_isIntV_neg {G : HTGroup p} {v : AwayP p} {y : Qv v ⊗[ℚ] G.C} (hy : IsIntV G v y) :
    IsIntV G v (-y) := by
  intro i; rw [map_neg, Finsupp.neg_apply]; exact neg_mem (hy i)

theorem normStep_isIntV_zero {G : HTGroup p} {v : AwayP p} : IsIntV G v 0 := by
  intro i; rw [map_zero, Finsupp.zero_apply]; exact zero_mem _

theorem normStep_isIntV_smul {G : HTGroup p} {v : AwayP p} {r : Qv v} {y : Qv v ⊗[ℚ] G.C}
    (hr : r ∈ v.1.adicCompletionIntegers ℚ) (hy : IsIntV G v y) : IsIntV G v (r • y) := by
  intro i; rw [map_smul, Finsupp.smul_apply, smul_eq_mul]; exact mul_mem hr (hy i)

theorem normStep_star_star (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (y : R ⊗[ℚ] G.C) :
    (starT G.star R (starT G.star R y).unop).unop = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => rw [starT_tmul, starT_tmul, G.star_star]
  | add x y hx hy => simp only [map_add (f := _), MulOpposite.unop_add, hx, hy]

theorem normStep_star_mul (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (y z : R ⊗[ℚ] G.C) :
    (starT G.star R (y * z)).unop = (starT G.star R z).unop * (starT G.star R y).unop := by
  rw [map_mul, MulOpposite.unop_mul]

theorem normStep_star_comm (G : HTGroup p) (v : AwayP p) (g : (Qv v ⊗[ℚ] G.C)ˣ) (c : (Qv v)ˣ)
    (hg : (g : Qv v ⊗[ℚ] G.C) * (starT G.star (Qv v) g).unop = algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) c)
    (y : Qv v ⊗[ℚ] G.C) (hy : y * g = g * y) :
    (starT G.star (Qv v) y).unop * g = g * (starT G.star (Qv v) y).unop := by
  set yh := (starT G.star (Qv v) y).unop with hyh
  set gh := (starT G.star (Qv v) (g : Qv v ⊗[ℚ] G.C)).unop with hgh
  set cc := algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) c with hcc'
  have key : gh * yh = yh * gh := by
    have := congrArg (fun x => (starT G.star (Qv v) x).unop) hy
    simpa only [normStep_star_mul] using this
  have hgi : gh = (↑g⁻¹ : Qv v ⊗[ℚ] G.C) * cc := by rw [← hg, ← mul_assoc, Units.inv_mul, one_mul]
  have hcu : IsUnit cc := c.isUnit.map _
  have hcc : ∀ x, cc * x = x * cc := fun x => Algebra.commutes _ _
  have h1 : yh * (↑g⁻¹ : Qv v ⊗[ℚ] G.C) = ↑g⁻¹ * yh := by
    apply hcu.mul_left_injective
    show yh * ↑g⁻¹ * cc = ↑g⁻¹ * yh * cc
    calc yh * ↑g⁻¹ * cc = yh * gh := by rw [hgi, mul_assoc]
      _ = gh * yh := key.symm
      _ = ↑g⁻¹ * yh * cc := by rw [hgi, mul_assoc, mul_assoc, hcc yh]
  calc yh * ↑g = ↑g * (↑g⁻¹ * yh) * ↑g := by rw [← mul_assoc, Units.mul_inv, one_mul]
    _ = ↑g * (yh * ↑g⁻¹) * ↑g := by rw [h1]
    _ = ↑g * yh := by rw [mul_assoc, mul_assoc, Units.inv_mul, mul_one]

theorem normStep_exists (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p) (g : (Qv v ⊗[ℚ] G.C)ˣ)
    (c : (Qv v)ˣ)
    (hg : (g : Qv v ⊗[ℚ] G.C) * (starT G.star (Qv v) g).unop = algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) c)
    (h1 : IsIntV G v 1)
    (hmul : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z))
    (hstar : ∀ y : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v (starT G.star (Qv v) y).unop)
    (hcomm : ∀ y z : Qv v ⊗[ℚ] G.C, y * g = g * y → z * g = g * z → y * z = z * y)
    (θ θ' h : Qv v ⊗[ℚ] G.C) (hθg : θ * g = g * θ) (hθ'g : θ' * g = g * θ') (hhg : h * g = g * h)
    (hθi : IsIntV G v θ) (hθ'i : IsIntV G v θ') (hhi : IsIntV G v h)
    (hθθ' : (θ - (starT G.star (Qv v) θ).unop) * θ' = 1) (h2 : 2 * h = 1)
    (s : (Qv v ⊗[ℚ] G.C)ˣ) (hsg : s * g = g * s) (hsi : IsIntV G v (s : Qv v ⊗[ℚ] G.C))
    (hsii : IsIntV G v ((s⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C))
    (hsfix : (starT G.star (Qv v) s).unop = s) :
    ∃ u : (Qv v ⊗[ℚ] G.C)ˣ, u * g = g * u ∧ IsIntV G v (u : Qv v ⊗[ℚ] G.C) ∧
      IsIntV G v ((u⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) ∧
      (u : Qv v ⊗[ℚ] G.C) * (starT G.star (Qv v) u).unop = s := by
  classical
  let A : Subring (Qv v ⊗[ℚ] G.C) :=
    { carrier := {y | y * g = g * y ∧ IsIntV G v y}
      mul_mem' := fun {a b} ha hb => ⟨Commute.mul_left ha.1 hb.1, hmul _ _ ha.2 hb.2⟩
      one_mem' := ⟨Commute.one_left _, h1⟩
      add_mem' := fun {a b} ha hb => ⟨Commute.add_left ha.1 hb.1, normStep_isIntV_add ha.2 hb.2⟩
      zero_mem' := ⟨Commute.zero_left _, normStep_isIntV_zero⟩
      neg_mem' := fun {a} ha => ⟨Commute.neg_left ha.1, normStep_isIntV_neg ha.2⟩ }
  letI : CommRing A :=
    { (inferInstance : Ring A) with mul_comm := fun a b => Subtype.ext (hcomm _ _ a.2.1 b.2.1) }
  have hτmem : ∀ y ∈ A, (starT G.star (Qv v) y).unop ∈ A := fun y hy =>
    ⟨normStep_star_comm G v g c hg y hy.1, hstar y hy.2⟩
  let τ : A →+* A :=
    { toFun := fun y => ⟨(starT G.star (Qv v) y).unop, hτmem y y.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        show (starT G.star (Qv v) ((a : Qv v ⊗[ℚ] G.C) * b)).unop =
          (starT G.star (Qv v) a).unop * (starT G.star (Qv v) b).unop
        rw [normStep_star_mul]; exact hcomm _ _ (hτmem b b.2).1 (hτmem a a.2).1)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by
        show (starT G.star (Qv v) ((a : Qv v ⊗[ℚ] G.C) + b)).unop =
          (starT G.star (Qv v) a).unop + (starT G.star (Qv v) b).unop
        rw [map_add (f := _), MulOpposite.unop_add]) }
  have hτinv : ∀ a, τ (τ a) = a := fun a => Subtype.ext (normStep_star_star G (Qv v) a)
  let O := v.1.adicCompletionIntegers ℚ
  let φ : O →+* A := ((algebraMap (Qv v) (Qv v ⊗[ℚ] G.C)).comp (algebraMap O (Qv v))).codRestrict A
    (fun r => ⟨Algebra.commutes _ _, by
      show IsIntV G v (algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) (algebraMap O (Qv v) r))
      rw [Algebra.algebraMap_eq_smul_one]
      exact normStep_isIntV_smul r.2 h1⟩)
  letI : Algebra O A := φ.toAlgebra
  let cf : A →ₗ[O] (Fin (Module.finrank ℚ G.C) → O) :=
    { toFun := fun y i => ⟨(basV G v).repr (y : Qv v ⊗[ℚ] G.C) i, y.2.2 i⟩
      map_add' := fun a b => by
        funext i; apply Subtype.ext
        show (basV G v).repr ((a : Qv v ⊗[ℚ] G.C) + b) i = (basV G v).repr a i + (basV G v).repr b i
        rw [map_add (f := _), Finsupp.add_apply]
      map_smul' := fun r a => by
        funext i; apply Subtype.ext
        show (basV G v).repr (algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) (algebraMap O (Qv v) r) * a) i =
          (r : Qv v) * (basV G v).repr a i
        rw [← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]
        rfl }
  have hinj : Function.Injective cf := by
    intro a b hab
    apply Subtype.ext
    apply (basV G v).repr.injective
    exact Finsupp.ext fun i => congrArg (fun f => ((f i : O) : Qv v)) hab
  haveI : Module.Finite O A := Module.Finite.of_injective cf hinj
  obtain ⟨hhen, hfin⟩ := GlobalTheory.T.padicIntegers_henselian_finiteResidue v.1
  haveI := hhen
  haveI := hfin
  let θA : A := ⟨θ, hθg, hθi⟩
  have hθu : IsUnit (θA - τ θA) := IsUnit.of_mul_eq_one (a := θA - τ θA) (⟨θ', hθ'g, hθ'i⟩ : A) (Subtype.ext hθθ')
  have hsg' : s⁻¹ * g = g * s⁻¹ := Commute.inv_left hsg
  let sA : A := ⟨s, congrArg Units.val hsg, hsi⟩
  let siA : A := ⟨↑s⁻¹, congrArg Units.val hsg', hsii⟩
  have hsu : IsUnit sA := IsUnit.of_mul_eq_one (a := sA) siA (Subtype.ext s.mul_inv)
  have hτs : τ sA = sA := Subtype.ext hsfix
  obtain ⟨t₀, ht₀, ht₀J⟩ := GlobalTheory.T.exists_isUnit_mul_involution_sub_mem_jacobson O A τ hτinv θA hθu sA hsu hτs
  haveI : HenselianRing A (⊥ : Ideal A).jacobson := GlobalTheory.henselianRing_of_finite O _ le_rfl
  have hτJ : ∀ a ∈ (⊥ : Ideal A).jacobson, τ a ∈ (⊥ : Ideal A).jacobson := by
    intro a ha
    rw [Ideal.mem_jacobson_bot] at ha ⊢
    intro b
    have := (ha (τ b)).map τ
    rwa [τ.map_add, τ.map_mul, hτinv, τ.map_one] at this
  have h2A : IsUnit (2 : A) := IsUnit.of_mul_eq_one (a := (2 : A)) (⟨h, hhg, hhi⟩ : A) (Subtype.ext (by
    show ((2 : A) : Qv v ⊗[ℚ] G.C) * h = 1
    rw [show ((2 : A) : Qv v ⊗[ℚ] G.C) = 2 from map_ofNat A.subtype 2]
    exact h2))
  obtain ⟨t, ht, htt⟩ := GlobalTheory.T.henselian_norm_lift A _ τ hτinv h2A hτJ sA t₀ hsu hτs ht₀ ht₀J
  refine ⟨Units.map (A.subtype : A →* Qv v ⊗[ℚ] G.C) ht.unit, ?_, ?_, ?_, ?_⟩
  · exact Units.ext t.2.1
  · exact t.2.2
  · exact ((ht.unit⁻¹ : Aˣ) : A).2.2
  · exact congrArg Subtype.val htt

end GlobalTheory.OrbFinAf
end
end

section

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel

theorem _root_.GlobalTheory.T.greenCuspidalChar_isCuspidalOfMinpoly_of_param : GlobalTheory.GLq.Green → ∀ (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p), 5 ≤ p → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (θ : Tor p (Fintype.card ι) →* ℂˣ) (x : Fbar p), 0 < Fintype.card ι → LabelsChar L θ x → (minpoly (ZMod p) x).natDegree = Fintype.card ι → GlobalTheory.GLq.IsCuspOf L (minpoly (ZMod p) x) (cuspOn θ) := by
  first | exact @GlobalTheory.ParamLabel.isCuspOf_cuspOn_of_green | exact GlobalTheory.ParamLabel.isCuspOf_cuspOn_of_green | (intros; apply GlobalTheory.ParamLabel.isCuspOf_cuspOn_of_green <;> assumption)
end
