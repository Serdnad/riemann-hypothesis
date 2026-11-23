module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.Bundle003
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsExpandsFScale
public import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.MapPowLeOfIsPullUnif
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2825
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle054
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle037
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle033
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GSep

theorem exists_opens_R_le_O : ∀ X₁ : GlobalTheory.GSep.GSet, ∃ U : X₁.M.Z.Opens, (U : Set X₁.M.Z).Nonempty ∧
    ∀ z ∈ U, X₁.S.R ≤ X₁.M.O z := by
  intro X₁
  obtain ⟨s, hs⟩ := X₁.S.fg
  refine ⟨⟨⋂ x ∈ s, {z | x ∈ X₁.M.O z}, isOpen_biInter_finset fun x _ => X₁.M.isOpen_setOf_mem_O x⟩,
    ⟨genericPoint X₁.M.Z, ?_⟩, ?_⟩
  · show genericPoint X₁.M.Z ∈ ⋂ x ∈ s, {z | x ∈ X₁.M.O z}
    refine Set.mem_iInter₂.2 fun x _ => ?_
    show x ∈ X₁.M.O (genericPoint X₁.M.Z)
    rw [RatModel.O_genericPoint]
    exact Algebra.mem_top
  · intro z hz
    have hz' : z ∈ ⋂ x ∈ s, {z | x ∈ X₁.M.O z} := hz
    rw [← hs]
    exact Algebra.adjoin_le fun x hx => Set.mem_iInter₂.1 hz' x hx

end GlobalTheory.GSep
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.GSep

variable {I : Type} {X₁ : GSet} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}

theorem Tower.map_mem_O (𝔗 : GlobalTheory.GSep.Tower X₁ act) {w : 𝔗.X₂.M.Z} {x : X₁.Ω₁} (hx : x ∈ X₁.M.O (𝔗.p w)) :
    algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁ x ∈ 𝔗.X₂.M.O w := by
  obtain ⟨U, f, hz, rfl⟩ := hx
  refine ⟨𝔗.p ⁻¹ᵁ U, 𝔗.p.app U f, hz, ?_⟩
  refine (GlobalTheory.Points.valR_comp 𝔗.X₂.M.pt 𝔗.p U f).symm.trans ?_
  rw [𝔗.p_pt]
  exact GlobalTheory.Points.valR_spMap_comp _ X₁.M.pt U (X₁.M.top_le_preimage_pt ⟨_, hz⟩) f

theorem Tower.stalkHom_stalkMap (𝔗 : GlobalTheory.GSep.Tower X₁ act) (z₂ : 𝔗.X₂.M.Z) (x : X₁.M.Z.presheaf.stalk (𝔗.p z₂)) :
    𝔗.X₂.M.stalkHom z₂ ((𝔗.p.stalkMap z₂).hom x) = algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁ (X₁.M.stalkHom (𝔗.p z₂) x) := by
  obtain ⟨U, hz, f, rfl⟩ := X₁.M.Z.presheaf.exists_germ_eq x
  rw [Scheme.Hom.germ_stalkMap_apply, RatModel.stalkHom_germ hz]
  refine (RatModel.stalkHom_germ (U := 𝔗.p ⁻¹ᵁ U) hz _).trans ?_
  refine (GlobalTheory.Points.valR_comp 𝔗.X₂.M.pt 𝔗.p U f).symm.trans ?_
  rw [𝔗.p_pt]
  exact GlobalTheory.Points.valR_spMap_comp _ X₁.M.pt U (X₁.M.top_le_preimage_pt ⟨_, hz⟩) f

theorem Tower.regAt : ∀ {I : Type} {X₁ : GlobalTheory.GSep.GSet} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : GlobalTheory.GSep.Tower X₁ act) {z₁ : X₁.M.Z} {z₂ : 𝔗.X₂.M.Z}, 𝔗.p z₂ = z₁ → ∀ {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V'), Function.Injective io → 𝔗.Ext ev io ev₂ → GlobalTheory.GSep.RegAt X₁ z₁ ev → GlobalTheory.GSep.RegAt 𝔗.X₂ z₂ ev₂ := by
  intro I X₁ act 𝔗 z₁ z₂ hz V V' _ _ _ _ ev io ev₂ hio hext hreg
  subst hz
  have key : ev₂.comp (𝔗.p.stalkMap z₂).hom = io.comp ev :=
    RingHom.ext fun x => hext.2 x _ (𝔗.stalkHom_stalkMap z₂ x)
  let fm : FractionRing V →+* FractionRing V' :=
    IsLocalization.map (M := nonZeroDivisors V) (S := FractionRing V) (FractionRing V') io
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective io hio)
  have e1 : spMap ev₂ ≫ Spec.map (𝔗.p.stalkMap z₂) = spMap io ≫ spMap ev := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact congrArg (fun φ : _ →+* V' => φ x) key
  have e2 : jK V' ≫ spMap io = spMap fm ≫ jK V := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    show algebraMap V' (FractionRing V') (io x) = fm (algebraMap V (FractionRing V) x)
    exact (IsLocalization.map_eq (M := nonZeroDivisors V) (S := FractionRing V) (T := nonZeroDivisors V')
      (Q := FractionRing V') (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective io hio) x).symm
  have hm : jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂ ≫ 𝔗.p =
      spMap fm ≫ jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk (𝔗.p z₂) := by
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc (spMap ev₂), e1, Category.assoc,
      ← Category.assoc (jK V'), e2, Category.assoc]
  have hpt : 𝔗.p ((jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (closedPoint (FractionRing V'))) =
      (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk (𝔗.p z₂)) (closedPoint (FractionRing V)) := by
    refine (Scheme.Hom.comp_apply _ 𝔗.p _).symm.trans ?_
    rw [Category.assoc, Category.assoc, hm]
    refine (Scheme.Hom.comp_apply (spMap fm) _ _).trans (congrArg _ ?_)
    exact Spec_closedPoint
  intro a ha
  set P₂ := (jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (closedPoint (FractionRing V'))
  haveI := 𝔗.X₂.normal.isIntegrallyClosed_stalk P₂
  haveI : IsIntegrallyClosed (𝔗.X₂.M.O P₂) := IsIntegrallyClosed.of_equiv (𝔗.X₂.M.stalkEquiv P₂)
  have hmem : ∀ c : X₁.S.R, ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp X₁.S.R.val.toRingHom) c ∈ 𝔗.X₂.M.O P₂ := fun c =>
    𝔗.map_mem_O (by rw [hpt]; exact hreg c.1 c.2)
  let q : X₁.S.R →+* 𝔗.X₂.M.O P₂ := ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp X₁.S.R.val.toRingHom).codRestrict _ hmem
  obtain ⟨p, hmon, hp⟩ := 𝔗.om_fin.to_isIntegral ⟨a, ha⟩
  have hq : (algebraMap (𝔗.X₂.M.O P₂) 𝔗.X₂.Ω₁).comp q = 𝔗.X₂.S.R.val.toRingHom.comp 𝔗.om :=
    RingHom.ext fun c => (𝔗.om_eq c).symm
  have hia : IsIntegral (𝔗.X₂.M.O P₂) a := by
    refine ⟨p.map q, hmon.map q, ?_⟩
    rw [Polynomial.eval₂_map, hq]
    have := Polynomial.hom_eval₂ p 𝔗.om 𝔗.X₂.S.R.val.toRingHom ⟨a, ha⟩
    rw [hp, map_zero] at this
    exact this.symm
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hia
  rw [← hy]
  exact y.2

end GlobalTheory.GSep
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GSep.IntTerm

theorem torsion_has_label : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (xb : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A), xb ^ (X₁.S.r * X₁.S.N) = 1 → ∃ a : X₁.S.Gam, xb.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫ (X₁.ρ.pt a).left := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪 xb hxb
  let T := TFK (R := V) (AlgebraicClosure (FractionRing V))
  obtain ⟨a, ha, -⟩ := X₁.ρ.pt_bij (AlgebraicClosure (FractionRing V)) (T.hom ≫ spMap 𝔪.yK) (pushHom 𝔪.cart T xb)
    (by rw [← map_pow, hxb, map_one])
  refine ⟨a, ?_⟩
  have h1 : (T.hom ≫ spMap 𝔪.yK) ≫ (X₁.ρ.pt a).left = xb.left ≫ 𝔪.φ := congrArg (fun z => z.left) ha
  rw [← h1]
  congr 1
  exact (Spec.map_comp (CommRingCat.ofHom 𝔪.yK)
    (CommRingCat.ofHom (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))))).symm

end GlobalTheory.GSep.IntTerm
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GSep

theorem stalk_isNoetherian_normal_fractionRing : ∀ (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ := (X₁.M.stalkHom z₁).toAlgebra; IsDomain (X₁.M.Z.presheaf.stalk z₁) ∧ IsFractionRing (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ ∧ IsIntegrallyClosed (X₁.M.Z.presheaf.stalk z₁) ∧ IsNoetherianRing (X₁.M.Z.presheaf.stalk z₁) := by
  intro X₁ z₁
  letI : Algebra (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ := (X₁.M.stalkHom z₁).toAlgebra
  have hN := X₁.normal
  refine ⟨GlobalTheory.IsNormalScheme.isDomain_stalk z₁, ?_, GlobalTheory.IsNormalScheme.isIntegrallyClosed_stalk z₁, ?_⟩
  · have : FaithfulSMul (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 (X₁.M.stalkHom_injective z₁)
    refine IsFractionRing.of_field _ _ fun x => ?_
    obtain ⟨a, b, -, hx⟩ := IsFractionRing.div_surjective (A := X₁.M.O z₁) x
    refine ⟨(X₁.M.stalkEquiv z₁).symm a, (X₁.M.stalkEquiv z₁).symm b, ?_⟩
    have h : ∀ c : X₁.M.O z₁, algebraMap (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ ((X₁.M.stalkEquiv z₁).symm c) = c := fun c => by
      change X₁.M.stalkHom z₁ _ = _
      rw [← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply]
    rw [h, h, ← hx]
    rfl
  · have : IsDedekindDomain X₁.o₁ := X₁.ar.ded
    have := X₁.M.lft
    have : IsLocallyNoetherian (Sp X₁.o₁) :=
      inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of X₁.o₁)))
    have : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian X₁.M.s
    infer_instance

end GlobalTheory.GSep
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section

namespace GlobalTheory.GSep.TransTerms

variable {I : Type}

def TorChar {X₁ : GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X}
    (𝔪 : GMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ) : Prop :=
  χ ^ (X₁.S.r * X₁.S.N) = 1 ∧ ∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ →
    ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A),
      p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧
      x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left

def TransExp {X₁ : GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X}
    (𝔪 : GMem X₁ z₁ act V ev X t δ) (x₀ a τ : X₁.S.Gam) (e : ℕ) : Prop :=
  ∀ χ, TorChar 𝔪 τ χ → ∀ (C : Type) (lab : C → X₁.S.Gam) (T : X → C → V), 𝔪.Terms x₀ lab T →
    ∀ c, lab c = a → ∀ (C' : Type) (lab' : C' → X₁.S.Gam) (T' : X → C' → V), 𝔪.Terms x₀ lab' T' →
    ∀ c', lab' c' = a + τ → ∀ mu : X,
      ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) * algebraMap V (FractionRing V) (T mu c) =
        𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)) * algebraMap V (FractionRing V) (T' mu c')

theorem sumF_comp_equiv {R : Type} [CommRing R] [IsDomain R] {J : Ideal R} {K : Type} [Field K]
    [Algebra (FractionRing R) K] {Ix Jx : Type} {x : Ix → K} {s : K} (e : Jx ≃ Ix) (h : SumF J K x s) :
    SumF J K (fun j => x (e j)) s := by
  letI : Module R K := Module.compHom K (algebraMap R (FractionRing R))
  obtain ⟨N, hN, hs, hx, hlim⟩ := h
  refine ⟨N, hN, hs, fun j => hx _, fun k => ?_⟩
  classical
  obtain ⟨S, hS⟩ := hlim k
  refine ⟨S.map e.symm.toEmbedding, fun T hT => ?_⟩
  have hsub : S ⊆ T.map e.toEmbedding := by
    intro a ha
    have := hT (Finset.mem_map_of_mem e.symm.toEmbedding ha)
    exact Finset.mem_map.2 ⟨e.symm a, this, by simp⟩
  have := hS _ hsub
  rwa [Finset.sum_map] at this

end GlobalTheory.GSep.TransTerms
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenFrameScale

section General

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange GlobalTheory.ExpFieldCompare

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem exists_expandsF_scale_pow (w w' : IndefiniteRowSideFullHecke.BaseChangeCharts.Ident U) : ∃ d : F, d ≠ 0 ∧
    ∀ (k : ℕ) t s, U.ExpandsF F k w'.1 t s → U.ExpandsF F k w.1 t (d ^ k • s) := by
  obtain ⟨u, hu⟩ := exists_isoVal_ratio A.isLB U.LG.isLB w'.2 w.2
  obtain ⟨c₀, hc₀, huc⟩ := BoxExpansion.unit_const globalFns_holds A U.gen u
  refine ⟨algebraMap (FractionRing R) F c₀, (map_ne_zero _).2 hc₀, fun k t s h => ?_⟩
  obtain ⟨v, h₁, h₂⟩ := h
  have z : U.ExpandsG F k (0 : GroupSec U F k) 0 := (expandsG_iff U F k _ _).2
    ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, (Fin.sum_univ_zero _).symm,
      fun α => (map_zero _).trans (Fin.sum_univ_zero _).symm⟩
  have h₃ := expandsG_lin U F k (algebraMap (FractionRing R) F c₀ ^ k) h₂ z
  rw [add_zero, add_zero] at h₃
  refine ⟨_, ?_, h₃⟩
  refine (isoRelM_iff w.1 (prGK G F) k (U.genF F).left h₁.1 (𝟙 _) h₁.2.1 t _).2 fun y a b ha hb => ?_
  have e := (isoRelM_iff w'.1 (prGK G F) k (U.genF F).left h₁.1 (𝟙 _) h₁.2.1 t v).1 h₁ _ (𝟙 _) y a b ha hb
  have e₃ : (𝟙 _ ≫ prGK G F) ≫ ((Over.pullback (jK R)).obj G).hom =
      ((𝟙 _ ≫ 𝟙 _) ≫ groupBase G F) ≫ jFK (R := R) F := by
    simp only [Category.id_comp]
    exact (isPullback_groupBase F).w
  have e₄ : (gm (𝟙 _ ≫ prGK G F) y ⊤ u).val = BoxExpansion.constHomVal ((𝟙 _ ≫ 𝟙 _) ≫ groupBase G F) y
      (algebraMap (FractionRing R) F c₀) :=
    ((gs_unit (𝟙 _ ≫ prGK G F) y ⊤ trivial u).symm.trans
      (congrArg (gs _ y ⊤) huc)).trans ((gs_scal _ _ y c₀).trans ((congrArg (fun q => constVal q y c₀) e₃).trans
        ((constVal_specMap _ _ y c₀).trans (BoxExpansion.constVal_eq _ _ _))))
  refine (powVal_smul (π := groupBase G F) _ v (𝟙 _ ≫ 𝟙 _) y (i := a) ha).trans ?_
  rw [e, hu _ (𝟙 _ ≫ prGK G F) y a b ha hb, mul_zpow, Units.val_mul, BoxExpansion.constVal_eq, map_pow, ← e₄,
    zpow_natCast (gm _ _ _ _), Units.val_pow_eq_pow_val, _root_.mul_assoc]

end General

theorem frames_scale : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (w₀ w₀₂ : W0 𝔪.U.toUnifPre), w₀.IsGen → w₀₂.IsGen →
  ∃ u : FractionRing V, u ≠ 0 ∧ ∀ (k : ℕ) (th : SecA 𝔪.A (FractionRing V) k) (s : Fam 𝔪.D.toPre (FractionRing V) k),
    𝔪.U.ExpandsF (FractionRing V) k w₀ th s → 𝔪.U.ExpandsF (FractionRing V) k w₀₂ th (u ^ k • s) := by
  intro I X₁ z₁ act V _ _ _ ev Y _ t δ 𝔪 w₀ w₀₂ h₀ h₂
  obtain ⟨d, hd, H⟩ := exists_expandsF_scale_pow 𝔪.U.toUnifPre (FractionRing V) ⟨w₀₂, h₂⟩ ⟨w₀, h₀⟩
  exact ⟨d, hd, fun k th s h => H k th s h⟩

end GlobalTheory.GenFrameScale
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.GSep



theorem GMem.exists_baseChange : ∀ {I : Type} (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V') (f : FractionRing V →+* FractionRing V'), (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) → IsCN V' → Function.Injective io → io.Finite → ∃ (D' : DegData V' (maximalIdeal V')) (e₈' : X ≃+ D'.toPre.X) (G' : Over (Sp V')) (_ : GrpObj G') (_ : IsCommMonObj G') (A' : PolAV (Sp (FractionRing V'))) (U' : Unif (maximalIdeal V') D' A' G') (ψ : A'.A.left ⟶ 𝔪.A.A.left) (hD : IsPullDeg io 𝔪.D.toPre D'.toPre) (bc : G' ≅ (Over.pullback (spMap io)).obj 𝔪.G), IsSemiAbelian G' ∧ IsGrpPullback A'.A 𝔪.A.A (spMap f) ψ ∧ (∃ w : LB.Iso A'.L (𝔪.A.L.pull ψ), w.IsGen) ∧ IsMonHom bc.hom ∧ IsPullUnif io hD bc 𝔪.U U' ∧ (∀ mu, hD.xe (e₈' mu) = 𝔪.e₈ mu) ∧ U'.gen.hom.left ≫ ψ ≫ 𝔪.U.gen.inv.left ≫ pullback.fst 𝔪.G.hom (jK V) = pullback.fst G'.hom (jK V') ≫ bc.hom.left ≫ pullback.fst 𝔪.G.hom (spMap io) ∧ (∀ E : EndU 𝔪.U.toUnifPre, ∃ E' : EndU U'.toUnifPre, E'.aA.left ≫ ψ = ψ ≫ E.aA.left ∧ ∀ χ, hD.xe (E'.h χ) = E.h (hD.xe χ)) ∧ ∀ mu, ∃ u : V'ˣ, Formalism.L2.Pj.PsiCoord D'.toPre (e₈' mu) (u * io (t mu)) := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪 V' _ _ _ io f hf hcn hinj hfin
  have hV := 𝔪.cn
  have aR : AdmBase V (maximalIdeal V) := ⟨hV.1, inferInstance, hV.2.1, hV.2.2.1⟩
  have aR' : AdmBase V' (maximalIdeal V') := ⟨hcn.1, inferInstance, hcn.2.1, hcn.2.2.1⟩
  have hI : (maximalIdeal V).map io ≤ maximalIdeal V' := by
    letI := io.toAlgebra
    haveI : Algebra.IsIntegral V V' := ⟨hfin.to_isIntegral⟩
    have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := V) (algebraMap _ _) hfin.to_isIntegral (maximalIdeal V')
    rw [Ideal.map_le_iff_le_comap]
    exact (IsLocalRing.eq_maximalIdeal hmax).ge
  let G' : Over (Sp V') := (Over.pullback (spMap io)).obj 𝔪.G
  let bc : G' ≅ (Over.pullback (spMap io)).obj 𝔪.G := Iso.refl _
  have mbc : IsMonHom bc.hom := inferInstanceAs (IsMonHom (𝟙 G'))
  have semi' : IsSemiAbelian G' := IsSemiAbelian.pullback (spMap io) 𝔪.G 𝔪.semi
  obtain ⟨A', gA, pA, dA, mA, tA⟩ := GlobalTheory.polBaseChange_holds _ _ (spMap f) 𝔪.A
  have gpA : IsGrpPullback A'.A 𝔪.A.A (spMap f) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  have sq : spMap f ≫ jK V = jK V' ≫ spMap io :=
    (spMap_comp _ f).symm.trans ((congrArg spMap (RingHom.ext hf)).trans (spMap_comp io _))
  have gpG : IsGrpPullback 𝔪.A.A 𝔪.G (jK V) (𝔪.U.gen.inv.left ≫ pullback.fst 𝔪.G.hom (jK V)) := by
    have := 𝔪.U.gen_hom
    have : IsMonHom 𝔪.U.gen.symm.hom := by show IsMonHom 𝔪.U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso 𝔪.U.gen.symm).comp (isGrpPullback_pullback 𝔪.G (jK V))).congr
      (Category.id_comp _) rfl
  have gp' : IsGrpPullback ((Over.pullback (jK V')).obj G') 𝔪.G (spMap f ≫ jK V)
      (pullback.fst G'.hom (jK V') ≫ pullback.fst 𝔪.G.hom (spMap io)) :=
    ((isGrpPullback_pullback G' (jK V')).comp (isGrpPullback_pullback 𝔪.G (spMap io))).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have := 𝔪.U.gen_hom

  have hgi : 𝔪.U.gen.inv.left ≫ 𝔪.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hbc0 : bc.hom.left ≫ pullback.fst 𝔪.G.hom (specOf io) = pullback.fst 𝔪.G.hom (spMap io) :=
    Category.id_comp _
  have wA : LBIso (A'.L.pull eA.hom.left) (𝔪.U.LG.L.pull (pullback.fst G'.hom (jK V') ≫
      bc.hom.left ≫ pullback.fst 𝔪.G.hom (specOf io))) := by
    refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB 𝔪.A.isLB gA) eA.hom.left)
      (pull_isLB 𝔪.U.LG.isLB _)
      ((LBIso.symm tA).chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A'.L _ _ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (𝔪.A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ 𝔪.U.gen.inv.left)
      (chartPullLinComb 𝔪.A.L gA (fun _ => eA.hom.left) (fun _ => 𝔪.U.gen.hom.left) _ _ fun _ => ?_)
      (chartPullSame 𝔪.U.LG.L _ (fun _ => pullback.fst 𝔪.G.hom (jK V)) _ _ fun _ => ?_) 𝔪.U.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [hbc0, ← heA]; simp only [Category.assoc]
  have hbc : IsGrpPullback G' 𝔪.G (specOf io) (bc.hom.left ≫ pullback.fst 𝔪.G.hom (specOf io)) :=
    (isGrpPullback_pullback 𝔪.G (specOf io)).congr rfl hbc0.symm
  have he := GlobalTheory.PolBaseChange.eSec_comm hbc
  let L' : RigLB G' := ⟨𝔪.U.LG.L.pull (bc.hom.left ≫ pullback.fst 𝔪.G.hom (specOf io)),
    rigPullOf (G' := G') (G := 𝔪.G) (bc.hom.left ≫ pullback.fst 𝔪.G.hom (specOf io)) (specOf io) he 𝔪.U.LG.L 𝔪.U.LG.rig,
    pull_isLB 𝔪.U.LG.isLB _,
    GlobalTheory.Proof.TautologicalModel.rigPullOf_isGen (G' := G') (G := 𝔪.G) (bc.hom.left ≫ pullback.fst 𝔪.G.hom (specOf io)) (specOf io) he
      𝔪.U.LG.L 𝔪.U.LG.rig 𝔪.U.LG.rigGen⟩
  obtain ⟨wL, gL, rL⟩ := GlobalTheory.Unif.RigidifyIso.exists_rigidified_iso _ _ (specOf io) 𝔪.G G' _ he 𝔪.U.LG L'
    (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB 𝔪.U.LG.isLB _))
  obtain ⟨Wo, hWo, hψ⟩ := GlobalTheory.psiOnExists V _ aR 𝔪.D
  have hgen : (specOf io).base (genericPoint (Spec (CommRingCat.of V'))) ∈ Wo := by
    have : (specOf io).base (genericPoint (Spec (CommRingCat.of V'))) = genericPoint (Spec (CommRingCat.of V)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective io hinj)
    rw [this]; exact hWo
  obtain ⟨D', hD, U', hLG, hgenU, hPU⟩ := GlobalTheory.UnifPullGuards.unifBaseChange_holds V V' _ _ aR aR' io hI 𝔪.D 𝔪.A 𝔪.G
    𝔪.semi 𝔪.U Wo hψ hgen G' bc mbc A' dA eA mE wA L' wL he gL rL
  have hgc : U'.gen.hom.left ≫ gA ≫ 𝔪.U.gen.inv.left ≫ pullback.fst 𝔪.G.hom (jK V) =
      pullback.fst G'.hom (jK V') ≫ bc.hom.left ≫ pullback.fst 𝔪.G.hom (spMap io) := by
    rw [hgenU, hbc0, heA]
  refine ⟨D', 𝔪.e₈.trans hD.xe.symm, G', inferInstance, inferInstance, A', U', gA, hD, bc, semi', gpA,
    LBIso.symm tA, mbc, hPU, fun mu => hD.xe.apply_symm_apply _, hgc, fun E => ?_, fun mu => ?_⟩
  · have := E.homG
    have := E.homA
    have := U'.gen_hom
    let aG' : G' ⟶ G' := (Over.pullback (spMap io)).map E.aG
    have maG : IsMonHom aG' := inferInstanceAs (IsMonHom ((Over.pullback (spMap io)).map E.aG))
    have mi : IsMonHom U'.gen.inv := by infer_instance
    let aA' : A'.A ⟶ A'.A := U'.gen.inv ≫ (Over.pullback (jK V')).map aG' ≫ U'.gen.hom
    have maA : IsMonHom aA' := by infer_instance
    have hext : (Over.pullback (jK V')).map aG' ≫ U'.gen.hom = U'.gen.hom ≫ aA' := by
      simp only [aA', Iso.hom_inv_id_assoc]
    obtain ⟨E', hG', hA'⟩ := exists_degenerationEndomorphism_of_admissibleBase V' _ aR' D' A' G' semi' U' aG' aA' maG maA hext
    have hfa : aG'.left ≫ pullback.fst 𝔪.G.hom (spMap io) = pullback.fst 𝔪.G.hom (spMap io) ≫ E.aG.left :=
      pullback.lift_fst _ _ _
    have hgG : E'.aG.left ≫ bc.hom.left ≫ pullback.fst 𝔪.G.hom (spMap io) =
        bc.hom.left ≫ pullback.fst 𝔪.G.hom (spMap io) ≫ E.aG.left := by
      rw [hG', hbc0]; exact hfa
    refine ⟨E', ?_, GlobalTheory.EndPullChar.pull_char_eq V V' _ _ aR aR' io hinj hI 𝔪.D D' hD 𝔪.A A' 𝔪.G G' 𝔪.semi semi' 𝔪.U U' bc mbc hPU E E' hgG⟩
    have actA : E.aA.left ≫ 𝔪.U.gen.inv.left ≫ pullback.fst 𝔪.G.hom (jK V) =
        𝔪.U.gen.inv.left ≫ pullback.fst 𝔪.G.hom (jK V) ≫ E.aG.left := by
      have e : E.aA ≫ 𝔪.U.gen.inv = 𝔪.U.gen.inv ≫ (Over.pullback (jK V)).map E.aG := by
        rw [Iso.comp_inv_eq, Category.assoc]
        exact ((Iso.inv_comp_eq _).2 E.ext).symm
      rw [← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
      exact congrArg _ (pullback.lift_fst _ _ _)
    have hfa' : ((Over.pullback (jK V')).map aG').left ≫ pullback.fst G'.hom (jK V') =
        pullback.fst G'.hom (jK V') ≫ aG'.left := pullback.lift_fst _ _ _
    have hgc' : U'.gen.inv.left ≫ pullback.fst G'.hom (jK V') ≫ pullback.fst 𝔪.G.hom (spMap io) =
        gA ≫ 𝔪.U.gen.inv.left ≫ pullback.fst 𝔪.G.hom (jK V) := by
      have hi : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
      have := hgc
      rw [hbc0] at this
      rw [← this, ← Category.assoc, hi, Category.id_comp]
    rw [hA']
    apply gpG.1.hom_ext
    · simp only [aA', Over.comp_left, Category.assoc]
      rw [hgc, hbc0, ← Category.assoc ((Over.pullback (jK V')).map aG').left, hfa', Category.assoc, hfa, actA]
      simpa only [Category.assoc] using congrArg (· ≫ E.aG.left) hgc'
    · simp only [aA', Over.comp_left, Category.assoc, Over.w, Over.w_assoc, pA.w, pA.w_assoc]
  · obtain ⟨u, hu⟩ := 𝔪.psi mu
    have hx : hD.xe ((𝔪.e₈.trans hD.xe.symm) mu) = 𝔪.e₈ mu := hD.xe.apply_symm_apply _
    obtain ⟨u', hu'⟩ := GlobalTheory.PelCoordPull.psiCoord_pull hD _ _ (hx.symm ▸ hu)
    refine ⟨u' * Units.map io.toMonoidHom u, ?_⟩
    have e : ((u' * Units.map io.toMonoidHom u : V'ˣ) : V') * io (t mu) = u' * io (u * t mu) := by
      rw [Units.val_mul, map_mul, ← _root_.mul_assoc]; rfl
    rw [e]; exact hu'

end GlobalTheory.GSep
end
end
