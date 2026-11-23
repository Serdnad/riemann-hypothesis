module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle644
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle788
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle860
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1012
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.Bundle001
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Pinch.SemiLoc

variable {X : Scheme.{0}}

theorem exists_pow_mul_eq_zero_of_germ {V : X.Opens} (hV : IsAffineOpen V) (h s : Γ(X, V))
    (H : ∀ z (hz : z ∈ V), z ∈ X.basicOpen h → (X.presheaf.germ V z hz).hom s = 0) :
    ∃ m : ℕ, h ^ m * s = 0 := by
  apply exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen X hV
  apply TopCat.Presheaf.section_ext X.sheaf
  intro z hz
  simp only [TopCat.Presheaf.restrictOpen, map_zero]
  erw [TopCat.Presheaf.germ_res_apply]
  exact H z (X.basicOpen_le h hz) hz

theorem exists_germ_eq_pow_mul {V O : X.Opens} (hV : IsAffineOpen V) (h : Γ(X, V))
    (hO : X.basicOpen h ≤ O) (r : Γ(X, O)) :
    ∃ (n : ℕ) (y : Γ(X, V)), ∀ z (hz : z ∈ X.basicOpen h),
      (X.presheaf.germ V z (X.basicOpen_le h hz)).hom y =
        (X.presheaf.germ V z (X.basicOpen_le h hz)).hom h ^ n *
          (X.presheaf.germ O z (hO hz)).hom r := by
  obtain ⟨n, y, hy⟩ := exists_eq_pow_mul_of_isAffineOpen X V hV h
    ((X.presheaf.map (homOfLE hO).op).hom r)
  refine ⟨n, y, fun z hz => ?_⟩
  have := congrArg (X.presheaf.germ (X.basicOpen h) z hz).hom hy
  simp only [TopCat.Presheaf.restrictOpen, map_mul, map_pow] at this
  erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
    TopCat.Presheaf.germ_res_apply] at this
  exact this

theorem germ_cocycle {L : LB X} (hL : L.IsLB) (a b c : L.ι) (z : X) (ha : z ∈ L.U a)
    (hb : z ∈ L.U b) (hc : z ∈ L.U c) :
    (X.presheaf.germ (L.U a ⊓ L.U b) z ⟨ha, hb⟩).hom (L.g a b).val *
      (X.presheaf.germ (L.U b ⊓ L.U c) z ⟨hb, hc⟩).hom (L.g b c).val =
    (X.presheaf.germ (L.U a ⊓ L.U c) z ⟨ha, hc⟩).hom (L.g a c).val := by
  have := congrArg (fun u : Γ(X, L.U a ⊓ L.U b ⊓ L.U c)ˣ =>
    (X.presheaf.germ (L.U a ⊓ L.U b ⊓ L.U c) z ⟨⟨ha, hb⟩, hc⟩).hom u.val) (hL.cocycle a b c)
  simp only [Units.val_mul, map_mul, res, Units.coe_map] at this
  erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
    TopCat.Presheaf.germ_res_apply] at this
  exact this

end GlobalTheory.Pinch.SemiLoc

namespace GlobalTheory.Pinch.SemiLoc

theorem exists_secFam_isUnit_germ : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (W : X.Opens), IsAffineOpen W → ∀ (J : Type) [Fintype J] (f : J → Γ(X, W)) (k : J → L.ι) (hk : ∀ j, X.basicOpen (f j) ≤ L.U (k j)) (x : X), x ∈ W → ∃ e : ∀ j, Γ(X, X.basicOpen (f j)), GlobalTheory.Pinch.IsSecFam L (fun j => X.basicOpen (f j)) k hk e ∧ ∀ j (h : x ∈ X.basicOpen (f j)), IsUnit ((X.presheaf.germ (X.basicOpen (f j)) x h).hom (e j)) := by
  intro X L hL W hW J _ f k hk x hxW
  classical
  obtain ⟨k0, hk0⟩ : ∃ k0, x ∈ L.U k0 := by
    have hx : x ∈ (⨆ i, L.U i) := by rw [hL.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hx
  obtain ⟨h, hhU, hxh⟩ := hW.exists_basicOpen_le (V := L.U k0) ⟨x, hk0⟩ hxW
  have hDW : ∀ j, X.basicOpen (f j) ≤ W := fun j => X.basicOpen_le (f j)
  let hj : ∀ j, Γ(X, X.basicOpen (f j)) := fun j => (X.presheaf.map (homOfLE (hDW j)).op).hom h
  have hbj : ∀ j, X.basicOpen (hj j) = X.basicOpen (f j) ⊓ X.basicOpen h :=
    fun j => X.basicOpen_res h _
  have hgj : ∀ j z (hz : z ∈ X.basicOpen (f j)),
      (X.presheaf.germ (X.basicOpen (f j)) z hz).hom (hj j) =
        (X.presheaf.germ W z (hDW j hz)).hom h :=
    fun j z hz => TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have hO : ∀ j, X.basicOpen (hj j) ≤ L.U (k j) ⊓ L.U k0 := fun j => by
    rw [hbj]; exact inf_le_inf (hk j) hhU
  choose n y hy using fun j =>
    exists_germ_eq_pow_mul (hW.basicOpen (f j)) (hj j) (hO j) (L.g (k j) k0).val
  let N := Finset.univ.sup n
  let e : ∀ j, Γ(X, X.basicOpen (f j)) := fun j => hj j ^ (N - n j) * y j
  have he : ∀ j z (hz : z ∈ X.basicOpen (f j)) (hzh : z ∈ X.basicOpen h),
      (X.presheaf.germ (X.basicOpen (f j)) z hz).hom (e j) =
        (X.presheaf.germ W z (hDW j hz)).hom h ^ N *
          (X.presheaf.germ (L.U (k j) ⊓ L.U k0) z ⟨hk j hz, hhU hzh⟩).hom (L.g (k j) k0).val := by
    intro j z hz hzh
    have hz' : z ∈ X.basicOpen (hj j) := by rw [hbj]; exact ⟨hz, hzh⟩
    have h1 := hy j z hz'
    simp only [e, map_mul, map_pow]
    rw [h1]; simp only [hgj]; rw [← _root_.mul_assoc, ← pow_add,
      Nat.sub_add_cancel (Finset.le_sup (f := n) (Finset.mem_univ j))]
  have hdef : ∀ j j', ∃ m : ℕ, ∀ z (hz : z ∈ X.basicOpen (f j)) (hz' : z ∈ X.basicOpen (f j')),
      (X.presheaf.germ W z (hDW j hz)).hom h ^ m *
        ((X.presheaf.germ (X.basicOpen (f j)) z hz).hom (e j) -
          (X.presheaf.germ (L.U (k j) ⊓ L.U (k j')) z ⟨hk j hz, hk j' hz'⟩).hom
              (L.g (k j) (k j')).val *
            (X.presheaf.germ (X.basicOpen (f j')) z hz').hom (e j')) = 0 := by
    intro j j'
    obtain ⟨V, hVdef⟩ : ∃ V, V = X.basicOpen (f j * f j') := ⟨_, rfl⟩
    have hVeq : V = X.basicOpen (f j) ⊓ X.basicOpen (f j') := hVdef.trans (X.basicOpen_mul _ _)
    have hVa : IsAffineOpen V := hVdef ▸ hW.basicOpen (f j * f j')
    have hV1 : V ≤ X.basicOpen (f j) := hVeq ▸ inf_le_left
    have hV2 : V ≤ X.basicOpen (f j') := hVeq ▸ inf_le_right
    have hVg : V ≤ L.U (k j) ⊓ L.U (k j') := le_inf (hV1.trans (hk j)) (hV2.trans (hk j'))
    have hVW : V ≤ W := hV1.trans (hDW j)
    let d : Γ(X, V) := (X.presheaf.map (homOfLE hV1).op).hom (e j) -
      (X.presheaf.map (homOfLE hVg).op).hom (L.g (k j) (k j')).val *
        (X.presheaf.map (homOfLE hV2).op).hom (e j')
    let hV : Γ(X, V) := (X.presheaf.map (homOfLE hVW).op).hom h
    have hbV : X.basicOpen hV = V ⊓ X.basicOpen h := X.basicOpen_res h _
    obtain ⟨m, hm⟩ := exists_pow_mul_eq_zero_of_germ hVa hV d (by
      intro z hz hzb
      rw [hbV] at hzb
      simp only [d, map_sub, map_mul]
      erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
        TopCat.Presheaf.germ_res_apply]
      rw [he j z (hV1 hz) hzb.2, he j' z (hV2 hz) hzb.2,
        ← germ_cocycle hL (k j) (k j') k0 z (hk j (hV1 hz)) (hk j' (hV2 hz)) (hhU hzb.2)]
      ring)
    refine ⟨m, fun z hz hz' => ?_⟩
    have hzV : z ∈ V := by rw [hVeq]; exact ⟨hz, hz'⟩
    have := congrArg (X.presheaf.germ V z hzV).hom hm
    simp only [d, hV, map_mul, map_pow, map_sub, map_zero] at this
    erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
      TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at this
    exact this
  choose m hm using hdef
  let M := Finset.univ.sup (fun p : J × J => m p.1 p.2)
  refine ⟨fun j => hj j ^ M * e j, ?_, ?_⟩
  · intro j j' z hz hz'
    have hle : m j j' ≤ M := Finset.le_sup (f := fun p : J × J => m p.1 p.2) (Finset.mem_univ (j, j'))
    have h0 := hm j j' z hz hz'
    simp only [map_mul, map_pow]
    simp only [hgj]
    have h2 : (X.presheaf.germ W z (hDW j hz)).hom h ^ M *
        ((X.presheaf.germ (X.basicOpen (f j)) z hz).hom (e j) -
          (X.presheaf.germ (L.U (k j) ⊓ L.U (k j')) z ⟨hk j hz, hk j' hz'⟩).hom
              (L.g (k j) (k j')).val *
            (X.presheaf.germ (X.basicOpen (f j')) z hz').hom (e j')) = 0 := by
      rw [← Nat.sub_add_cancel hle, pow_add, _root_.mul_assoc, h0, mul_zero]
    linear_combination h2
  · intro j hx
    have hu : IsUnit ((X.presheaf.germ W x (hDW j hx)).hom h) := (X.mem_basicOpen h x _).1 hxh
    simp only [map_mul, map_pow]
    simp only [hgj]; rw [he j x hx hxh]
    exact (hu.pow _).mul ((hu.pow _).mul ((L.g (k j) k0).isUnit.map _))

end GlobalTheory.Pinch.SemiLoc
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent
open TensorProduct
namespace GlobalTheory.LBDescent.CocycleTensor

theorem appLE_congr_hom {A B : Scheme.{0}} {g₁ g₂ : A ⟶ B} (hg : g₁ = g₂) (U : B.Opens) (W : A.Opens)
    (e₁ : W ≤ g₁ ⁻¹ᵁ U) (e₂ : W ≤ g₂ ⁻¹ᵁ U) : g₁.appLE U W e₁ = g₂.appLE U W e₂ := by
  subst hg; rfl

theorem germ_appLE_gm {A B : Scheme.{0}} (g : A ⟶ B) {U U' : B.Opens} (W : A.Opens) (e : W ≤ g ⁻¹ᵁ U)
    (hUU' : U ≤ U') (w : A) (hw : w ∈ W) (a : Γ(B, U')ˣ) :
    (A.presheaf.germ W w hw).hom ((g.appLE U W e).hom (res hUU' a).val) = (gm g w U' a).val :=
  (TopCat.Presheaf.germ_res_apply A.presheaf (homOfLE e) w hw ((g.app U).hom (res hUU' a).val)).trans
    ((gm_val g w U (e hw) (res hUU' a)).symm.trans (congrArg Units.val (gm_res g w hUU' (e hw) a)))


theorem cocycle_tensor_of_pointwise : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] (V V₀ : Y.Opens), IsAffineOpen V₀ →
    ∀ (h : pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀ ≤ pullback.snd f f ⁻¹ᵁ f ⁻¹ᵁ V₀)
      (hle : pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀ ≤ pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V) (c : Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V)ˣ),
    (∀ w : ↥(Triple f), f (pullback.fst f f (pullback.fst (pullback.snd f f) (pullback.fst f f) w)) ∈ V →
        gm (pullback.fst (pullback.snd f f) (pullback.fst f f)) w _ c *
          gm (pullback.snd (pullback.snd f f) (pullback.fst f f)) w _ c = gm (pr13 f) w _ c) →
    letI : Algebra Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) := (f.app V₀).hom.toAlgebra
    ∀ e : Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀) ≃+* Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀),
      (∀ a b : Γ(X, f ⁻¹ᵁ V₀), e (a ⊗ₜ b) =
        ((pullback.fst f f).app (f ⁻¹ᵁ V₀)).hom a * ((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) _ h).hom b) →
      Algebra.TensorProduct.includeLeft (R := Γ(Y, V₀)) (S := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀)) (e.symm (res hle c).val) *
          Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (AlgHom.id Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀)) (e.symm (res hle c).val) =
        Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft (R := Γ(Y, V₀)) (S := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (AlgHom.id Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀)) (e.symm (res hle c).val) := by
  intro X Y f _ V V₀ hV₀ h hle c hc e he
  letI : Algebra Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) := (f.app V₀).hom.toAlgebra
  have hcond : ∀ z : ↥(pullback f f), f ((pullback.fst f f) z) = f ((pullback.snd f f) z) := fun z => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have hq : ∀ w : ↥(Triple f), (pullback.snd f f) ((pullback.fst (pullback.snd f f) (pullback.fst f f)) w) = (pullback.fst f f) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) w) := fun w => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have h1 : (pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀) ≤ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) := fun z hz => by
    show f ((pullback.fst f f) z) ∈ V₀
    rw [hcond]; exact hz
  have hleG : ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) ≤ (pullback.fst (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ ((pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) := fun w hw => by
    show f ((pullback.snd f f) ((pullback.fst (pullback.snd f f) (pullback.fst f f)) w)) ∈ V₀
    rw [hq]; exact hw
  have hp1 : pr13 f ≫ (pullback.fst f f) = (pullback.fst (pullback.snd f f) (pullback.fst f f)) ≫ (pullback.fst f f) := pullback.lift_fst _ _ _
  have hp2 : pr13 f ≫ (pullback.snd f f) = (pullback.snd (pullback.snd f f) (pullback.fst f f)) ≫ (pullback.snd f f) := pullback.lift_snd _ _ _
  have h13 : ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) ≤ pr13 f ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) := fun w hw => by
    show f ((pullback.fst f f) (pr13 f w)) ∈ V₀
    have e13 : (pullback.fst f f) (pr13 f w) = (pullback.fst f f) ((pullback.fst (pullback.snd f f) (pullback.fst f f)) w) :=
      (Scheme.Hom.comp_apply _ _ w).symm.trans ((congrArg (fun g => g w) hp1).trans (Scheme.Hom.comp_apply _ _ w))
    rw [e13]
    exact h1 (hleG hw)
  have h2 : (pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀) ≤ (pullback.fst f f) ⁻¹ᵁ f ⁻¹ᵁ V := h1.trans hle
  have hP := Out.GtBCPf.isPushout_appLE (IsPullback.of_hasPullback (pullback.snd f f) (pullback.fst f f)) inferInstance
    (hV₀.preimage f) ((hV₀.preimage f).preimage (pullback.fst f f)) le_rfl hleG
  have e1 : ∀ s : Γ(X, f ⁻¹ᵁ V₀), e.symm (((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) h).hom s) = 1 ⊗ₜ s := fun s => by
    rw [e.symm_apply_eq, he, map_one, _root_.one_mul]
  have e2 : ∀ s : Γ(X, f ⁻¹ᵁ V₀), e.symm (((pullback.fst f f).app (f ⁻¹ᵁ V₀)).hom s) = s ⊗ₜ 1 := fun s => by
    rw [e.symm_apply_eq, he, map_one, _root_.mul_one]
  let m₁ : Γ(pullback f f, (pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) ⟶ CommRingCat.of ((Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) :=
    CommRingCat.ofHom ((Algebra.TensorProduct.includeLeft (R := Γ(Y, V₀)) (S := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))).toRingHom.comp (e.symm.toRingHom.comp ((pullback f f).presheaf.map (homOfLE h).op).hom))
  let m₂ : Γ(pullback f f, (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) ⟶ CommRingCat.of ((Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) :=
    CommRingCat.ofHom ((Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (AlgHom.id Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀))).toRingHom.comp e.symm.toRingHom)
  have cond : (pullback.snd f f).app (f ⁻¹ᵁ V₀) ≫ m₁ = (pullback.fst f f).appLE (f ⁻¹ᵁ V₀) (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) le_rfl ≫ m₂ := by
    ext s
    show (Algebra.TensorProduct.includeLeft (R := Γ(Y, V₀)) (S := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (e.symm (((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) h).hom s)) = (Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (AlgHom.id Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀))) (e.symm (((pullback.fst f f).appLE (f ⁻¹ᵁ V₀) (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) le_rfl).hom s))
    rw [Scheme.Hom.appLE_eq_app, e1, e2]
    simp
  let Ψ := hP.desc m₁ m₂ cond
  have hΨ1 : ∀ y, Ψ.hom (((pullback.fst (pullback.snd f f) (pullback.fst f f)).appLE ((pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) hleG).hom y) = m₁.hom y := fun y =>
    congrArg (fun k => k.hom y) (hP.inl_desc m₁ m₂ cond)
  have hΨ2 : ∀ y, Ψ.hom (((pullback.snd (pullback.snd f f) (pullback.fst f f)).app (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)).hom y) = m₂.hom y := fun y =>
    congrArg (fun k => k.hom y) (hP.inr_desc m₁ m₂ cond)
  have ka : ∀ a : Γ(X, f ⁻¹ᵁ V₀), ((pr13 f).appLE (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) h13).hom (((pullback.fst f f).app (f ⁻¹ᵁ V₀)).hom a) =
      ((pullback.fst (pullback.snd f f) (pullback.fst f f)).appLE ((pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) hleG).hom (((pullback.fst f f).appLE (f ⁻¹ᵁ V₀) ((pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) h1).hom a) := fun a => by
    rw [Scheme.Hom.app_eq_appLE]
    exact congrArg (fun k => k.hom a) ((Scheme.Hom.appLE_comp_appLE (pr13 f) (pullback.fst f f) (f ⁻¹ᵁ V₀) (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) le_rfl h13).trans
      ((appLE_congr_hom hp1 (f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) _ _).trans (Scheme.Hom.appLE_comp_appLE (pullback.fst (pullback.snd f f) (pullback.fst f f)) (pullback.fst f f) (f ⁻¹ᵁ V₀) ((pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) h1 hleG).symm))
  have kb : ∀ b : Γ(X, f ⁻¹ᵁ V₀), ((pr13 f).appLE (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) h13).hom (((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) h).hom b) =
      ((pullback.snd (pullback.snd f f) (pullback.fst f f)).app (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)).hom (((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) h).hom b) := fun b => by
    rw [Scheme.Hom.app_eq_appLE]
    exact congrArg (fun k => k.hom b) ((Scheme.Hom.appLE_comp_appLE (pr13 f) (pullback.snd f f) (f ⁻¹ᵁ V₀) (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) h h13).trans
      ((appLE_congr_hom hp2 (f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) _ _).trans (Scheme.Hom.appLE_comp_appLE (pullback.snd (pullback.snd f f) (pullback.fst f f)) (pullback.snd f f) (f ⁻¹ᵁ V₀) (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) h le_rfl).symm))
  have ra : ∀ a : Γ(X, f ⁻¹ᵁ V₀), ((pullback f f).presheaf.map (homOfLE h).op).hom (((pullback.fst f f).appLE (f ⁻¹ᵁ V₀) ((pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) h1).hom a) =
      ((pullback.fst f f).app (f ⁻¹ᵁ V₀)).hom a := fun a => by
    rw [Scheme.Hom.app_eq_appLE]
    exact congrArg (fun k => k.hom a) (Scheme.Hom.appLE_map (pullback.fst f f) h1 (homOfLE h).op)
  have hΨ3 : ∀ t, Ψ.hom (((pr13 f).appLE (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) h13).hom (e t)) = (Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft (R := Γ(Y, V₀)) (S := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (AlgHom.id Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀))) t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a b =>
      rw [he, map_mul, map_mul, ka, kb, hΨ1, hΨ2]
      show (Algebra.TensorProduct.includeLeft (R := Γ(Y, V₀)) (S := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (e.symm (((pullback f f).presheaf.map (homOfLE h).op).hom (((pullback.fst f f).appLE (f ⁻¹ᵁ V₀) ((pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) h1).hom a))) *
        (Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (AlgHom.id Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀))) (e.symm (((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) h).hom b)) = _
      rw [ra, e1, e2]
      simp
  have hABC : ((pullback.fst (pullback.snd f f) (pullback.fst f f)).appLE ((pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) hleG).hom (res h2 c).val * ((pullback.snd (pullback.snd f f) (pullback.fst f f)).app (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)).hom (res hle c).val =
      ((pr13 f).appLE (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) h13).hom (res hle c).val := by
    apply TopCat.Presheaf.section_ext (Triple f).sheaf ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀))
    intro w hw
    have hw1 : (pullback.fst (pullback.snd f f) (pullback.fst f f)) w ∈ (pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀) := hleG hw
    have hw13 : pr13 f w ∈ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) := h13 hw
    have key := congrArg Units.val (hc w (hle (h1 hw1)))
    show ((Triple f).presheaf.germ ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) w hw).hom (((pullback.fst (pullback.snd f f) (pullback.fst f f)).appLE ((pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) hleG).hom (res h2 c).val * ((pullback.snd (pullback.snd f f) (pullback.fst f f)).app (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)).hom (res hle c).val) =
      ((Triple f).presheaf.germ ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) w hw).hom (((pr13 f).appLE (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) h13).hom (res hle c).val)
    rw [Scheme.Hom.app_eq_appLE]
    refine (RingHom.map_mul _ _ _).trans ?_
    exact (congrArg₂ (· * ·) (germ_appLE_gm (pullback.fst (pullback.snd f f) (pullback.fst f f)) _ hleG h2 w hw c) (germ_appLE_gm (pullback.snd (pullback.snd f f) (pullback.fst f f)) _ _ hle w hw c)).trans
      ((Units.val_mul _ _).symm.trans (key.trans (germ_appLE_gm (pr13 f) _ h13 hle w hw c).symm))
  have hA : (Algebra.TensorProduct.includeLeft (R := Γ(Y, V₀)) (S := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (e.symm (res hle c).val) = Ψ.hom (((pullback.fst (pullback.snd f f) (pullback.fst f f)).appLE ((pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) hleG).hom (res h2 c).val) := by
    have hres : ((pullback f f).presheaf.map (homOfLE h).op).hom (res h2 c).val = (res hle c).val := by
      show ((pullback f f).presheaf.map (homOfLE h).op).hom (((pullback f f).presheaf.map (homOfLE h2).op).hom c.val) =
        ((pullback f f).presheaf.map (homOfLE hle).op).hom c.val
      rw [← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl
    exact (congrArg (fun y => (Algebra.TensorProduct.includeLeft (R := Γ(Y, V₀)) (S := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (e.symm y)) hres).symm.trans (hΨ1 _).symm
  have hB : (Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (AlgHom.id Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀))) (e.symm (res hle c).val) = Ψ.hom (((pullback.snd (pullback.snd f f) (pullback.fst f f)).app (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)).hom (res hle c).val) := (hΨ2 _).symm
  have hC : (Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft (R := Γ(Y, V₀)) (S := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (AlgHom.id Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀))) (e.symm (res hle c).val) = Ψ.hom (((pr13 f).appLE (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) h13).hom (res hle c).val) := by
    exact (hΨ3 (e.symm (res hle c).val)).symm.trans (congrArg (fun y => Ψ.hom (((pr13 f).appLE (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) h13).hom y)) (e.apply_symm_apply _))
  exact (congrArg₂ (· * ·) hA hB).trans ((map_mul Ψ.hom _ _).symm.trans ((congrArg Ψ.hom hABC).trans hC.symm))

end GlobalTheory.LBDescent.CocycleTensor
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent

set_option autoImplicit false

namespace GlobalTheory.LBDescent

private theorem alg {G : Type*} [CommGroup G] (a P b G₁ G₃ : G) :
    a * P * b⁻¹ = G₁ * a * (G₁⁻¹ * P * G₃) * (G₃⁻¹ * b⁻¹) := by
  rw [mul_comm G₁ a]; group

theorem frame_cocycle {X Y : Scheme.{0}} (f : X ⟶ Y) (L : LB X) (hL : L.IsLB)
    (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ) (hC : DescCompat f L φ) (hK : DescCocycle f L φ)
    (V : Y.Opens) (t : ∀ i, Γ(X, f ⁻¹ᵁ V ⊓ L.U i)ˣ) (ht : ∀ (i j : L.ι) (x : X), f x ∈ V → x ∈ L.U i → x ∈ L.U j →
      gm (𝟙 X) x _ (t i) = gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (t j)) :
    ∃ c : Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V)ˣ,
      (∀ (z : ↥(pullback f f)) (i j : L.ι), f (pullback.fst f f z) ∈ V → pullback.fst f f z ∈ L.U i →
        pullback.snd f f z ∈ L.U j →
        gm (𝟙 _) z _ c = gm (pullback.fst f f) z _ (t i) * gm (𝟙 _) z _ (φ i j) * (gm (pullback.snd f f) z _ (t j))⁻¹) ∧
      ∀ w : ↥(Triple f), f (pullback.fst f f (pullback.fst (pullback.snd f f) (pullback.fst f f) w)) ∈ V →
        gm (pullback.fst (pullback.snd f f) (pullback.fst f f)) w _ c *
          gm (pullback.snd (pullback.snd f f) (pullback.fst f f)) w _ c = gm (pr13 f) w _ c := by

  have hf : ∀ z : ↥(pullback f f), f (pullback.snd f f z) = f (pullback.fst f f z) := fun z => by
    change (pullback.snd f f ≫ f) z = (pullback.fst f f ≫ f) z
    rw [pullback.condition]
  set V' : (pullback f f).Opens := pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V with hV'
  let W : L.ι × L.ι → (pullback f f).Opens := fun p => chart f L p.1 p.2 ⊓ V'
  have le1 : ∀ p : L.ι × L.ι, W p ≤ pullback.fst f f ⁻¹ᵁ (f ⁻¹ᵁ V ⊓ L.U p.1) :=
    fun p z hz => ⟨hz.2, hz.1.1⟩
  have le2 : ∀ p : L.ι × L.ι, W p ≤ chart f L p.1 p.2 := fun p => inf_le_left
  have le3 : ∀ p : L.ι × L.ι, W p ≤ pullback.snd f f ⁻¹ᵁ (f ⁻¹ᵁ V ⊓ L.U p.2) :=
    fun p z hz => ⟨show f (pullback.snd f f z) ∈ V by rw [hf]; exact hz.2, hz.1.2⟩
  let u : ∀ p, Γ(pullback f f, W p)ˣ := fun p =>
    res (le1 p) (pullU (pullback.fst f f) _ (t p.1)) * res (le2 p) (φ p.1 p.2) *
      (res (le3 p) (pullU (pullback.snd f f) _ (t p.2)))⁻¹
  have key : ∀ {T : Scheme.{0}} (h : T ⟶ pullback f f) (y : T) (p : L.ι × L.ι) (hy : h y ∈ W p),
      gm h y (W p) (u p) = gm (h ≫ pullback.fst f f) y _ (t p.1) * gm h y _ (φ p.1 p.2) *
        (gm (h ≫ pullback.snd f f) y _ (t p.2))⁻¹ := by
    intro T h y p hy
    simp only [u, map_mul, map_inv]
    rw [gm_res h y (le1 p) hy, gm_res h y (le2 p) hy, gm_res h y (le3 p) hy,
      gm_pull h (pullback.fst f f) y _ (le1 p hy), gm_pull h (pullback.snd f f) y _ (le3 p hy)]

  have tpull : ∀ {T : Scheme.{0}} (h : T ⟶ X) (y : T) (i j : L.ι), f (h y) ∈ V → h y ∈ L.U i → h y ∈ L.U j →
      gm h y _ (t i) = gm h y _ (L.g i j) * gm h y _ (t j) := by
    intro T h y i j hV hi hj
    have hle1 : f ⁻¹ᵁ V ⊓ (L.U i ⊓ L.U j) ≤ f ⁻¹ᵁ V ⊓ L.U i := inf_le_inf_left _ inf_le_left
    have hle2 : f ⁻¹ᵁ V ⊓ (L.U i ⊓ L.U j) ≤ L.U i ⊓ L.U j := inf_le_right
    have hle3 : f ⁻¹ᵁ V ⊓ (L.U i ⊓ L.U j) ≤ f ⁻¹ᵁ V ⊓ L.U j := inf_le_inf_left _ inf_le_right
    have e : res hle1 (t i) = res hle2 (L.g i j) * res hle3 (t j) := by
      apply unit_ext
      intro x hx
      rw [map_mul, gm_res _ x hle1 hx, gm_res _ x hle2 hx, gm_res _ x hle3 hx]
      exact ht i j x hx.1 hx.2.1 hx.2.2
    have hm : h y ∈ f ⁻¹ᵁ V ⊓ (L.U i ⊓ L.U j) := ⟨hV, hi, hj⟩
    have := congrArg (gm h y _) e
    rwa [map_mul, gm_res h y hle1 hm, gm_res h y hle2 hm, gm_res h y hle3 hm] at this
  have hW : ∀ p, W p ≤ V' := fun p => inf_le_right
  have hcov : V' ≤ iSup W := by
    intro z hz
    obtain ⟨i, hi⟩ := exists_chart hL (pullback.fst f f z)
    obtain ⟨j, hj⟩ := exists_chart hL (pullback.snd f f z)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j), ⟨hi, hj⟩, hz⟩
  have hagree : ∀ p q, ∀ x ∈ W p ⊓ W q, gm (𝟙 _) x (W p) (u p) = gm (𝟙 _) x (W q) (u q) := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ x ⟨hp, hq⟩
    rw [key (𝟙 _) x _ hp, key (𝟙 _) x _ hq]
    simp only [Category.id_comp]
    have hx1 : f (pullback.fst f f x) ∈ V := hp.2
    have hx2 : f (pullback.snd f f x) ∈ V := by rw [hf]; exact hx1
    rw [tpull (pullback.fst f f) x i' i hx1 hq.1.1 hp.1.1, tpull (pullback.snd f f) x j' j hx2 hq.1.2 hp.1.2,
      hC x i i' j j' hp.1.1 hq.1.1 hp.1.2 hq.1.2]
    have hg : gm (pullback.fst f f) x _ (L.g i' i) * gm (pullback.fst f f) x _ (L.g i i') = 1 := by
      rw [gm_cocycle hL _ x hq.1.1 hp.1.1 hq.1.1, gm_self hL _ x hq.1.1]
    rw [eq_inv_of_mul_eq_one_right hg, mul_inv]
    exact alg _ _ _ _ _
  obtain ⟨c, hc⟩ := glue_unit V' W hW hcov u hagree
  have cgerm : ∀ {T : Scheme.{0}} (h : T ⟶ pullback f f) (y : T) (p : L.ι × L.ι) (hy : h y ∈ W p),
      gm h y V' c = gm (h ≫ pullback.fst f f) y _ (t p.1) * gm h y _ (φ p.1 p.2) *
        (gm (h ≫ pullback.snd f f) y _ (t p.2))⁻¹ := by
    intro T h y p hy
    rw [← key h y p hy, ← hc p, gm_res h y (hW p) hy]
  refine ⟨c, ?_, ?_⟩
  · intro z i j hV hi hj
    have := cgerm (𝟙 _) z (i, j) ⟨⟨hi, hj⟩, hV⟩
    simpa only [Category.id_comp] using this
  · intro w hV
    set q₁ := pullback.fst (pullback.snd f f) (pullback.fst f f)
    set q₂ := pullback.snd (pullback.snd f f) (pullback.fst f f)
    have hmid : q₁ ≫ pullback.snd f f = q₂ ≫ pullback.fst f f := pullback.condition
    have h13a : pr13 f ≫ pullback.fst f f = q₁ ≫ pullback.fst f f := by unfold pr13; exact pullback.lift_fst _ _ _
    have h13b : pr13 f ≫ pullback.snd f f = q₂ ≫ pullback.snd f f := by unfold pr13; exact pullback.lift_snd _ _ _
    have pmid : pullback.snd f f (q₁ w) = pullback.fst f f (q₂ w) := by
      change (q₁ ≫ pullback.snd f f) w = (q₂ ≫ pullback.fst f f) w
      rw [hmid]
    have p13a : pullback.fst f f (pr13 f w) = pullback.fst f f (q₁ w) := by
      change (pr13 f ≫ pullback.fst f f) w = (q₁ ≫ pullback.fst f f) w
      rw [h13a]
    have p13b : pullback.snd f f (pr13 f w) = pullback.snd f f (q₂ w) := by
      change (pr13 f ≫ pullback.snd f f) w = (q₂ ≫ pullback.snd f f) w
      rw [h13b]
    obtain ⟨i, hi⟩ := exists_chart hL (pullback.fst f f (q₁ w))
    obtain ⟨j, hj⟩ := exists_chart hL (pullback.snd f f (q₁ w))
    obtain ⟨k, hk⟩ := exists_chart hL (pullback.snd f f (q₂ w))
    have hV2 : f (pullback.fst f f (q₂ w)) ∈ V := by rw [← pmid, hf]; exact hV
    have hV3 : f (pullback.fst f f (pr13 f w)) ∈ V := by rw [p13a]; exact hV
    have m1 : q₁ w ∈ W (i, j) := ⟨⟨hi, hj⟩, hV⟩
    have m2 : q₂ w ∈ W (j, k) := ⟨⟨show pullback.fst f f (q₂ w) ∈ L.U j by rw [← pmid]; exact hj, hk⟩, hV2⟩
    have m3 : pr13 f w ∈ W (i, k) := ⟨⟨show pullback.fst f f (pr13 f w) ∈ L.U i by rw [p13a]; exact hi,
      show pullback.snd f f (pr13 f w) ∈ L.U k by rw [p13b]; exact hk⟩, hV3⟩
    rw [cgerm q₁ w (i, j) m1, cgerm q₂ w (j, k) m2, cgerm (pr13 f) w (i, k) m3, hmid, h13a, h13b,
      ← hK w i j k hi hj hk]
    dsimp only
    simp only [q₁, q₂]
    group

end GlobalTheory.LBDescent
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES


theorem _root_.GlobalTheory.T.harrisTaylorType_iff_pulledBack_identity : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (T Y : Scheme.{0}) (s₁ : T ⟶ Sp R) (s : Y ⟶ Sp R) (t : T ⟶ Y) (o₁ : Obj b N s₁) (o : Obj b N s) (m : ObjMap o₁ o t) (B₁ : Over T) [GrpObj B₁] [IsCommMonObj B₁] (B : Over Y) [GrpObj B] [IsCommMonObj B] (θ : B₁.left ⟶ B.left) (ψ₁ : o₁.A ⟶ B₁) (ψ : o.A ⟶ B) (r : ℤ) (w : Ideal (𝓞 D.F)) (j : ℕ), IsGrpPullback B₁ B t θ → m.φ ≫ ψ.left = ψ₁.left ≫ θ → (TjAt r w j o ψ t ↔ TjAt r w j o₁ ψ₁ (𝟙 T)) := by
  first | (exact @GlobalTheory.UPel.HT.ES.tjAt_iff_tjAt_pull) | (exact GlobalTheory.UPel.HT.ES.tjAt_iff_tjAt_pull) | (intros; apply GlobalTheory.UPel.HT.ES.tjAt_iff_tjAt_pull  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.diagonalPullbackPower_isRigidified_relAmple : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), QHyp A Q → ∀ (d : ℕ), 0 < d → (diagPow A Q d).IsLB ∧ Out.Rigidified A (diagPow A Q d) ∧ Out.RelAmple A (diagPow A Q d) := by
  first | (exact @GlobalTheory.ActFin.DiagPow.diagPow_isLB_rigidified_relAmple) | (exact GlobalTheory.ActFin.DiagPow.diagPow_isLB_rigidified_relAmple) | (intros; apply GlobalTheory.ActFin.DiagPow.diagPow_isLB_rigidified_relAmple  <;> assumption)
end

section

open Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame Formalism.CohomologicalDescent.LD GlobalTheory.CapelliLink

theorem _root_.GlobalTheory.T.capelliCoeff_dualWeyl_eq_coeff_prod : ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (N : ℕ), ∃ F : ℕ → FreeAlgebra O (Fin N × Fin N), ∀ ν : Fin N → ℕ, Antitone ν → ∀ f ∈ Formalism.GradedWeylDivisibility.dualWeyl O N N ν, ∀ k : ℕ, evalPol O N (F k) f = (((∏ a : Fin N, (Polynomial.X + Polynomial.C (((ν a : ℤ) - (a : ℕ) : ℤ)))).coeff k : ℤ) : O) • f := by
  first | exact @GlobalTheory.CapelliCoeffs.capelli_coeff_dualWeyl | exact GlobalTheory.CapelliCoeffs.capelli_coeff_dualWeyl | (intros; apply GlobalTheory.CapelliCoeffs.capelli_coeff_dualWeyl <;> assumption)
end
