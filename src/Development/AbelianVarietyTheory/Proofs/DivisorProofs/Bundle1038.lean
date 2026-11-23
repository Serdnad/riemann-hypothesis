module

public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle038
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthRestrictScalarsEqSumInertiaDegOfSubset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
public import Formalism.SharpRestriction.Divisibility.Bundle001
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle266
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle616
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle977
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalDescendedBundleGaloisCover
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LBDescent

theorem exists_smul_mem_span_away {R S M : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [AddCommGroup M] [Module S M] [Module.Invertible S M]
    (p : Ideal R) [p.IsPrime] :
    ∃ r : R, r ∉ p ∧ ∃ m : M, ∀ x : M, ∃ a : S, algebraMap R S r • x = a • m := by
  classical
  let Q : Submonoid S := Algebra.algebraMapSubmonoid S p.primeCompl
  let T := Localization Q
  letI : Algebra (Localization.AtPrime p) T := localizationAlgebra p.primeCompl S
  haveI : Module.Finite (Localization.AtPrime p) T :=
    Module.Finite.of_isLocalization R S p.primeCompl
  haveI : Finite (MaximalSpectrum T) :=
    GlobalTheory.finite_maximalSpectrum_of_finite (Localization.AtPrime p) T
  obtain ⟨z, hz⟩ :=
    GlobalTheory.exists_bijective_toSpanSingleton_of_finite_maximalSpectrum T (LocalizedModule Q M)
  induction z using LocalizedModule.induction_on with
  | h m s =>
  have hloc : ∀ x : M, ∃ q ∈ Q, q • x ∈ Submodule.span S {m} := by
    intro x
    obtain ⟨c, hc⟩ := hz.2 (LocalizedModule.mk x 1)
    induction c using Localization.induction_on with
    | H c =>
    obtain ⟨a, t⟩ := c
    rw [LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq] at hc
    obtain ⟨u, hu⟩ := hc
    refine ⟨(u : S) * ((t : S) * (s : S)), Q.mul_mem u.2 (Q.mul_mem t.2 s.2), ?_⟩
    rw [mul_smul, mul_smul]
    have hu' : (u : S) • (((t * s : Q) : S)) • x = (u : S) • ((1 : Q) : S) • a • m := hu.symm
    rw [Submonoid.coe_mul] at hu'
    rw [mul_smul] at hu'
    rw [hu', Submodule.mem_span_singleton]
    exact ⟨(u : S) * a, by simp [mul_smul]⟩
  choose q hqQ hq using hloc
  obtain ⟨F, hF⟩ := Module.Finite.fg_top (R := S) (M := M)
  let q₀ : S := ∏ x ∈ F, q x
  have hq₀ : q₀ ∈ Q := Q.prod_mem fun x _ => hqQ x
  have key : ∀ y ∈ Submodule.span S (F : Set M), q₀ • y ∈ Submodule.span S {m} := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      have : q₀ = (∏ x' ∈ F.erase x, q x') * q x := (Finset.prod_erase_mul F q hx).symm
      rw [this, mul_smul]
      exact Submodule.smul_mem _ _ (hq x)
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add y₁ y₂ _ _ h₁ h₂ => rw [smul_add]; exact Submodule.add_mem _ h₁ h₂
    | smul a y _ h => rw [smul_comm]; exact Submodule.smul_mem _ _ h
  obtain ⟨r, hr, hrq⟩ := hq₀
  refine ⟨r, hr, m, fun x => ?_⟩
  have := key x (hF ▸ Submodule.mem_top)
  rw [Submodule.mem_span_singleton] at this
  obtain ⟨a, ha⟩ := this
  exact ⟨a, by rw [hrq]; exact ha.symm⟩

theorem isFrame_res_of_smul_mem {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {U : X.Opens}
    (hU : IsAffineOpen U) (h : Γ(X, U)) (m : Γ(GlobalTheory.LB.toMod L, U))
    (hm : ∀ x : Γ(GlobalTheory.LB.toMod L, U), ∃ a : Γ(X, U), h • x = a • m) :
    GlobalTheory.LB.IsFrame ((GlobalTheory.LB.toMod L).presheaf.map (homOfLE (X.basicOpen_le h)).op m) := by
  haveI := GlobalTheory.LB.isQuasicoherent_toMod hL
  have hD : IsAffineOpen (X.basicOpen h) := hU.basicOpen h
  haveI := GlobalTheory.LB.invertible_sections hL hD
  rw [GlobalTheory.LB.isFrame_iff_bijective hD]
  have h₁ := ((GlobalTheory.QCoh.isLocalizedModule_resBasicOpen_iff (GlobalTheory.LB.toMod L) h).1
    (GlobalTheory.QCoh.isLocalizedModule_resBasicOpen (GlobalTheory.LB.toMod L) hU h)).1
  refine Module.Invertible.bijective_of_surjective
    (f := LinearMap.toSpanSingleton Γ(X, X.basicOpen h) _
      ((GlobalTheory.LB.toMod L).presheaf.map (homOfLE (X.basicOpen_le h)).op m)) ?_
  intro s
  obtain ⟨n, t, ht⟩ := h₁ s
  obtain ⟨a, ha⟩ := hm t
  obtain ⟨u, hu⟩ := GlobalTheory.QCoh.isUnit_res_of_le_basicOpen h (X.basicOpen_le h) le_rfl
  have e1 := GlobalTheory.LB.map_smul_resG (F := GlobalTheory.LB.toMod L) (X.basicOpen_le h) h t
  rw [ha, GlobalTheory.LB.map_smul_resG] at e1
  refine ⟨((u⁻¹ : Γ(X, X.basicOpen h)ˣ) : Γ(X, X.basicOpen h)) ^ (n + 1) *
    resG X (X.basicOpen_le h) a, ?_⟩
  rw [← hu] at ht
  have hu' : resG X (X.basicOpen_le h) h = (u : Γ(X, X.basicOpen h)) := hu.symm
  rw [hu', ← ht, ← mul_smul] at e1
  rw [LinearMap.toSpanSingleton_apply, mul_smul, e1, ← mul_smul, ← pow_succ', ← mul_pow,
    Units.inv_mul, one_pow, one_smul]

theorem exists_trivial_near_fibre : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] (L : LB X), L.IsLB →
    ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧
    ∃ t : ∀ i, Γ(X, f ⁻¹ᵁ V ⊓ L.U i)ˣ, ∀ (i j : L.ι) (x : X), f x ∈ V → x ∈ L.U i → x ∈ L.U j →
      gm (𝟙 X) x _ (t i) = gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (t j) := by
  intro X Y f _ L hL y
  obtain ⟨W, hW, hyW, -⟩ : ∃ W ∈ Y.affineOpens, y ∈ W ∧ W ≤ ⊤ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens)
    (show y ∈ (⊤ : Y.Opens) from trivial)
  let p : Ideal Γ(Y, W) :=
    (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).comap (Y.presheaf.germ W y hyW).hom
  letI : Algebra Γ(Y, W) Γ(X, f ⁻¹ᵁ W) := (f.app W).hom.toAlgebra
  haveI : Module.Finite Γ(Y, W) Γ(X, f ⁻¹ᵁ W) := f.finite_app W hW
  have hW : IsAffineOpen W := hW
  have hU : IsAffineOpen (f ⁻¹ᵁ W) := hW.preimage f
  haveI := GlobalTheory.LB.invertible_sections hL hU
  obtain ⟨r, hr, m, hm⟩ := exists_smul_mem_span_away (R := Γ(Y, W)) (S := Γ(X, f ⁻¹ᵁ W))
    (M := Γ(GlobalTheory.LB.toMod L, f ⁻¹ᵁ W)) p
  have he := isFrame_res_of_smul_mem hL hU (f.app W r) m hm
  have hpre : f ⁻¹ᵁ Y.basicOpen r = X.basicOpen (f.app W r) := Scheme.preimage_basicOpen f r
  refine ⟨Y.basicOpen r, ?_, ?_⟩
  · rw [Scheme.mem_basicOpen (x := y) (hx := hyW)]
    by_contra hn
    exact hr ((IsLocalRing.mem_maximalIdeal _).2 hn)
  let F := GlobalTheory.LB.toMod L
  let e : Γ(F, f ⁻¹ᵁ Y.basicOpen r) :=
    F.presheaf.map (homOfLE hpre.le).op (F.presheaf.map (homOfLE (X.basicOpen_le _)).op m)
  have he' : GlobalTheory.LB.IsFrame e := he.map hpre.le
  let u : ∀ i, Γ(X, f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i)ˣ := fun i =>
    (GlobalTheory.LB.isFrame_chartSec hL i).unit he' inf_le_right inf_le_left
  have hu : ∀ i, ((u i : Γ(X, f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i)ˣ) : Γ(X, f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i)) =
      GlobalTheory.LB.coord e i := fun i => by
    rw [GlobalTheory.LB.IsFrame.val_unit]
    apply GlobalTheory.LB.IsFrame.repr_eq
    apply Subtype.ext
    funext j
    change GlobalTheory.LB.coord (GlobalTheory.LB.coord e i •
      (GlobalTheory.LB.toMod L).presheaf.map (homOfLE inf_le_right).op
        (GlobalTheory.LB.chartSec hL i)) j =
      GlobalTheory.LB.coord ((GlobalTheory.LB.toMod L).presheaf.map
        (homOfLE inf_le_left).op e) j
    simp only [GlobalTheory.LB.coord_smul, GlobalTheory.LB.coord_map,
      GlobalTheory.LB.coord_chartSec, GlobalTheory.LB.resG_resG]
    rw [mul_comm]
    exact (GlobalTheory.LB.coord_rel e j i _ _ _).symm
  refine ⟨u, fun i j x hxV hi hj => ?_⟩
  have hxO : x ∈ f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i ⊓ L.U j := ⟨⟨hxV, hi⟩, hj⟩
  rw [← gm_res (𝟙 X) x (inf_le_left : f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i ⊓ L.U j ≤ _) hxO,
    ← gm_res (𝟙 X) x (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i ⊓ L.U j ≤ L.U i ⊓ L.U j) hxO,
    ← gm_res (𝟙 X) x (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i ⊓ L.U j ≤ f ⁻¹ᵁ Y.basicOpen r ⊓ L.U j) hxO, ← map_mul]
  congr 1
  apply Units.ext
  rw [Units.val_mul, GlobalTheory.LB.val_res, GlobalTheory.LB.val_res, GlobalTheory.LB.val_res, hu, hu]
  exact GlobalTheory.LB.coord_rel e i j _ _ _

end GlobalTheory.LBDescent
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PinchLift

theorem germ_appLE_eq_gm_val {Y X : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) (O : Y.Opens) (hle : O ≤ f ⁻¹ᵁ U)
    (y : Y) (hy : y ∈ O) (a : Γ(X, U)ˣ) :
    (Y.presheaf.germ O y hy).hom ((f.appLE U O hle).hom a.val) = (gm f y U a).val := by
  rw [gm_val f y U (hle hy)]
  exact TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE hle) y hy _

theorem exists_unit_of_glues : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), i' ≫ p = p' ≫ i → GlobalTheory.PinchLift.Glues p i i' p' → ∀ (V : X.Opens) (a : Γ(X', p ⁻¹ᵁ V)ˣ) (b : Γ(Z, i ⁻¹ᵁ V)ˣ), (∀ z : Z', p (i' z) ∈ V → gm i' z (p ⁻¹ᵁ V) a = gm p' z (i ⁻¹ᵁ V) b) → ∃ u : Γ(X, V)ˣ, (∀ x' : X', p x' ∈ V → gm p x' V u = gm (𝟙 X') x' (p ⁻¹ᵁ V) a) ∧ (∀ z : Z, i z ∈ V → gm i z V u = gm (𝟙 Z) z (i ⁻¹ᵁ V) b) := by
  intro X X' Z Z' p i i' p' _ hG V a b hab
  have key : ∀ (a : Γ(X', p ⁻¹ᵁ V)ˣ) (b : Γ(Z, i ⁻¹ᵁ V)ˣ),
      (∀ z : Z', p (i' z) ∈ V → gm i' z (p ⁻¹ᵁ V) a = gm p' z (i ⁻¹ᵁ V) b) →
      ∃! s : Γ(X, V), (p.app V).hom s = a.val ∧ (i.app V).hom s = b.val := by
    intro a b hab
    apply hG V
    apply TopCat.Presheaf.section_ext Z'.sheaf
    intro z hz
    exact (germ_appLE_eq_gm_val i' _ _ inf_le_left z hz a).trans
      ((congrArg Units.val (hab z hz.1)).trans (germ_appLE_eq_gm_val p' _ _ inf_le_right z hz b).symm)
  obtain ⟨s, ⟨hs₁, hs₂⟩, -⟩ := key a b hab
  obtain ⟨t, ⟨ht₁, ht₂⟩, -⟩ := key a⁻¹ b⁻¹ (fun z hz => by rw [map_inv, map_inv, hab z hz])
  have h₁ := key 1 1 (fun z _ => by rw [map_one, map_one])
  have e : s * t = 1 := by
    apply h₁.unique
    · constructor
      · rw [map_mul, hs₁, ht₁, Units.mul_inv, Units.val_one]
      · rw [map_mul, hs₂, ht₂, Units.mul_inv, Units.val_one]
    · constructor
      · rw [map_one, Units.val_one]
      · rw [map_one, Units.val_one]
  refine ⟨⟨s, t, e, (mul_comm _ _).trans e⟩, fun x hx => ?_, fun x hx => ?_⟩
  · apply Units.ext
    rw [gm_val p x V hx, gm_val (𝟙 X') x (p ⁻¹ᵁ V) hx]
    exact congrArg (X'.presheaf.germ (p ⁻¹ᵁ V) x hx).hom hs₁
  · apply Units.ext
    rw [gm_val i x V hx, gm_val (𝟙 Z) x (i ⁻¹ᵁ V) hx]
    exact congrArg (Z.presheaf.germ (i ⁻¹ᵁ V) x hx).hom hs₂

end GlobalTheory.PinchLift
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PinchLift

theorem unit_eq_of_germs_glues : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), i' ≫ p = p' ≫ i → GlobalTheory.PinchLift.Glues p i i' p' → ∀ (V : X.Opens) (u v : Γ(X, V)ˣ), (∀ x' : X', p x' ∈ V → gm p x' V u = gm p x' V v) → (∀ z : Z, i z ∈ V → gm i z V u = gm i z V v) → u = v := by
  intro X X' Z Z' p i i' p' hc hG V u v hp hi
  have ep : (p.app V).hom u.val = (p.app V).hom v.val := by
    apply TopCat.Presheaf.section_ext X'.sheaf (p ⁻¹ᵁ V)
    intro x hx
    have h := congrArg Units.val (hp x hx)
    rwa [gm_val _ x V hx, gm_val _ x V hx] at h
  have ei : (i.app V).hom u.val = (i.app V).hom v.val := by
    apply TopCat.Presheaf.section_ext Z.sheaf (i ⁻¹ᵁ V)
    intro z hz
    have h := congrArg Units.val (hi z hz)
    rwa [gm_val _ z V hz, gm_val _ z V hz] at h
  have key : ∀ (f g : Z' ⟶ X) (_ : f = g) (O : Z'.Opens) (e : O ≤ f ⁻¹ᵁ V) (e' : O ≤ g ⁻¹ᵁ V),
      f.appLE V O e = g.appLE V O e' := by
    intro f g hfg O e e'; subst hfg; rfl
  have hag : (i'.appLE (p ⁻¹ᵁ V) (i' ⁻¹ᵁ (p ⁻¹ᵁ V) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ V)) inf_le_left).hom ((p.app V).hom u.val) =
      (p'.appLE (i ⁻¹ᵁ V) (i' ⁻¹ᵁ (p ⁻¹ᵁ V) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ V)) inf_le_right).hom ((i.app V).hom u.val) := by
    have e1 := Scheme.Hom.comp_appLE i' p V (i' ⁻¹ᵁ (p ⁻¹ᵁ V) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ V)) inf_le_left
    have e2 := Scheme.Hom.comp_appLE p' i V (i' ⁻¹ᵁ (p ⁻¹ᵁ V) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ V)) inf_le_right
    have e3 := key _ _ hc (i' ⁻¹ᵁ (p ⁻¹ᵁ V) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ V)) inf_le_left inf_le_right
    rw [e1, e2] at e3
    have := congrArg (fun f => f.hom u.val) e3
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using this
  exact Units.ext ((hG V _ _ hag).unique ⟨rfl, rfl⟩ ⟨ep.symm, ei.symm⟩)

end GlobalTheory.PinchLift
end

section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ColumnNormCompare
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam recGlob Twist)

namespace GlobalTheory.ColumnNormCompare.SizeRows

variable {D : D7} {large₂ : SizeData₂ D}

theorem one_le_b (s : Scale) : 1 ≤ s.b := by
  unfold Scale.b Scale.L
  have := s.one_lt_alt
  exact Real.one_le_exp (by positivity)

theorem condE_le_b (P : ParameterChoice' D large₂) : (LevelStarExponents.condE D : ℝ) ≤ large₂.sc.b := by
  have h := P.condE_le
  have hb := one_le_b large₂.sc
  have h1 : large₂.sc.b ^ ((1 : ℝ) / 2) ≤ large₂.sc.b := by
    simpa using Real.rpow_le_rpow_of_exponent_le hb (show (1 : ℝ) / 2 ≤ 1 by norm_num)
  have ht : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150 := one_le_pow₀ large₂.t_win.1
  have hc : (LevelStarExponents.condE D : ℝ) ≤ (LevelStarExponents.condE D : ℝ) ^ 36 := by
    exact_mod_cast Nat.le_self_pow (by norm_num) _
  have h2 : (LevelStarExponents.condE D : ℝ) ^ 36 ≤ (LevelStarExponents.condE D : ℝ) ^ 36 * (D.R.t : ℝ) ^ 150 :=
    le_mul_of_one_le_right (by positivity) ht
  linarith

theorem log_le_L_of_le_cond (P : ParameterChoice' D large₂) {p : ℕ} (hp : 0 < p) (h : p ≤ LevelStarExponents.condE D) :
    Real.log p ≤ large₂.sc.L := by
  have h1 : (p : ℝ) ≤ Real.exp large₂.sc.L := le_trans (by exact_mod_cast h) (condE_le_b P)
  exact (Real.log_le_iff_le_exp (by exact_mod_cast hp)).2 h1

theorem f_mul_N_le_b (P : ParameterChoice' D large₂) (h4 : 4 * placeRankTwoOne.NN D ^ 3 ≤ large₂.etaSz) :
    (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ≤ large₂.sc.b := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hk' : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hf : (0 : ℝ) < D.R.f := by
    have : 0 < D.R.f := by
      have hn : 0 < D.R.n := D.R.ord_pos
      unfold Ranks.f
      omega
    exact_mod_cast this
  have ht := large₂.t_win.1
  have he := large₂.etaSz_pos
  have h := P.eta_le
  rw [le_div_iff₀ (by positivity)] at h
  have hN : (D.R.N D.R.m : ℝ) ≤ (D.R.N D.R.m : ℝ) ^ 3 := by
    exact_mod_cast Nat.le_self_pow (by norm_num) _
  have hN0 : (0 : ℝ) ≤ (D.R.N D.R.m : ℝ) ^ 3 := by positivity
  unfold placeRankTwoOne.NN at h4
  have h5 : (D.R.N D.R.m : ℝ) ≤ large₂.etaSz := by linarith
  have h6 : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 3 := one_le_pow₀ ht
  have h7 : (1 : ℝ) ≤ (D.R.k : ℝ) ^ 3 := one_le_pow₀ hk'
  calc (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) = (D.R.N D.R.m : ℝ) * (1 * D.R.f * 1) := by ring
    _ ≤ large₂.etaSz * ((D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3) := by gcongr
    _ ≤ _ := h

theorem eTau_tauPl (z : RPl D.R) : (D.eTau (tauPl D z) : D.R.GG) = G.plGG D z := by
  unfold tauPl
  rw [Equiv.apply_symm_apply]

theorem not_top_of (z : RPl D.R) (hz : ¬ PlaceLogThetaBounds.IsTopPl (numDatumOfParameters D large₂) z) :
    (D.eTau (tauPl D z) : D.R.GG) ∉ D.host.topPlaces := by
  rw [eTau_tauPl]
  intro h
  unfold Host.topPlaces at h
  obtain ⟨t, ht, he⟩ := Finset.mem_image.1 h
  obtain ⟨b, s⟩ := z
  cases b
  · have h1 : D.R.tau1 t = D.R.tau1 s := he
    have h2 : t = s := D.R.toFrame.tau1_injective h1
    subst h2
    exact hz ⟨rfl, ht⟩
  · have h1 : D.R.tau1 t = D.R.tau2 s := he
    exact (factPlaces D.R.toFrame).2 _ _ h1

end GlobalTheory.ColumnNormCompare.SizeRows
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV

namespace GlobalTheory.ColumnNormCompare

theorem numRec_eq_ofRecord : ∀ (D : D7) (L : SizeData₂ D) (Del h0 : ℕ), D.s.Del = (Del : ℚ) → L.etaSz = (D.R.m : ℝ) * (h0 : ℝ) →
    GlobalTheory.ColumnNormCompare.numDatumOfParameters D L = ofRecord D L Del h0 := by
  intro D L Del h0 hD hE
  have hm : (D.R.m : ℝ) ≠ 0 := by
    have := D.R.two_le_m
    exact_mod_cast (show D.R.m ≠ 0 by omega)
  have h1 : ⌊D.s.Del⌋₊ = Del := by rw [hD]; exact Nat.floor_natCast Del
  have h2 : ⌈LevelStarExponents.h0 L⌉₊ = h0 := by
    have : LevelStarExponents.h0 L = (h0 : ℝ) := by
      unfold LevelStarExponents.h0
      rw [hE]; field_simp
    rw [this]; exact Nat.ceil_natCast h0
  simp only [numDatumOfParameters, ofRecord, h1, h2]

end GlobalTheory.ColumnNormCompare
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.ColNorms

theorem errUnit_nonneg (N : NumDatum) {T : ℕ} (hT : 1 ≤ T) : 0 ≤ errUnit N T := by
  have h0 : (1 : ℝ) ≤ N.g 0 := by exact_mod_cast (N.g_prime 0).one_lt.le
  have h1 : (1 : ℝ) ≤ N.g 1 := by exact_mod_cast (N.g_prime 1).one_lt.le
  have h2 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have h3 : 0 ≤ Real.log ((N.g 0 : ℝ) * N.g 1 * T) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h0 h1) h2)
  unfold errUnit
  positivity

theorem kernelBound_ge (N : NumDatum) (δ : Code N) (T : ℕ) (C₁ C₂ : ℝ) (j : ℕ) (lo : RPl N.R → ℝ) (lt : ℝ) (h h' n n' : ℕ) :
    kernelBound_sq N δ T C₁ j lo lt 1 1 1 1 + 2 * (C₂ * errUnit N T) ≤ kernelBound_sq N δ T (C₁ + C₂) j lo lt h h' n n' := by
  have a1 : 0 ≤ Real.log ((h : ℝ) * h') := by exact_mod_cast Real.log_natCast_nonneg (h * h')
  have a2 : 0 ≤ Real.log ((n : ℝ) * n') := by exact_mod_cast Real.log_natCast_nonneg (n * n')
  unfold kernelBound_sq errUnit
  simp only [Nat.cast_one, mul_one, Real.log_one]
  nlinarith

theorem SmallDatum.mono {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ}
    {S : Finset (HeightOneSpectrum (𝓞 E))} {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)} {c : ℕ}
    {Ξ : HomE E a b → K} {β β' : ℝ} (h : SmallDatum S N N' c Ξ β) (hβ : β ≤ β') : SmallDatum S N N' c Ξ β' :=
  ⟨h.1, h.2.1, fun σ x => (h.2.2 σ x).trans hβ⟩

end GlobalTheory.ColNorms
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.PDivGroup

theorem pow_finrank_omega_le_finrank_frobKer : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0)
    (G : PDivGroup p K), ∀ r : ℕ,
    (p ^ r) ^ Module.finrank K G.omega ≤ Module.finrank K (G.A r ⧸ frobKerIdeal (p ^ r) K (G.A r)) := by
  intro p _ K _ h G r
  haveI : CharP K p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 h
  have hN : Module.finrank K (G.A r) = p ^ (r * G.height) := by
    have := G.rank_eq r (IsLocalRing.closedPoint K)
    rwa [Module.rankAtStalk_eq_finrank_of_free] at this
  have hdim := (GlobalTheory.T.finrank_rigidExtensions_eq_height_and_dim_add_dual p K h G).2.2.2
  have hord := GlobalTheory.T.finrank_le_frobeniusKernel_mul_span_primePowers p K (G.A r) r
  have hspan := GlobalTheory.T.finrank_span_pow_pDivGroup_level_le p K h G r
  have hpos : 0 < (p ^ r) ^ Module.finrank K G.dual.omega :=
    pow_pos (pow_pos (Fact.out : p.Prime).pos _) _
  have key : (p ^ r) ^ Module.finrank K G.omega * (p ^ r) ^ Module.finrank K G.dual.omega ≤
      Module.finrank K (G.A r ⧸ frobKerIdeal (p ^ r) K (G.A r)) * (p ^ r) ^ Module.finrank K G.dual.omega := by
    rw [← pow_add, hdim, ← pow_mul, ← hN]
    exact hord.trans (Nat.mul_le_mul_left _ hspan)
  exact Nat.le_of_mul_le_mul_right key hpos

end GlobalTheory.PDivGroup
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.relAmple_diagonal_descended_bundle_galois_cover : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (M : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A') (G : Subgroup (𝟙_ (Over S) ⟶ o.A)), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover G (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → ∀ (m : ℕ), 1 ≤ m → ∀ (P' : LB (G2 A').left), P'.IsLB → LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → Out.RelAmple A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) := by
  first | exact @GlobalTheory.HeckeAmple.relAmple_diag_of_galois | exact GlobalTheory.HeckeAmple.relAmple_diag_of_galois | (intros; apply GlobalTheory.HeckeAmple.relAmple_diag_of_galois <;> assumption)
end
