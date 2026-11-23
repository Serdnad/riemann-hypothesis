module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle065
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle144
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle248
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle119
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeights
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle042
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle044
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle131
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle043
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle032
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.SpreadTrait

theorem pull_cancel {S S' S'' : Scheme.{0}} {G : Over S} [GrpObj G] {G₁ : Over S'} [GrpObj G₁] {f : S' ⟶ S}
    {m₁ : G₁.left ⟶ G.left} (h₁ : IsGrpPullback G₁ G f m₁) (u : S'' ⟶ S') {Gl : Over S''} [GrpObj Gl]
    {φl : Gl.left ⟶ G.left} (hGl : IsGrpPullback Gl G (u ≫ f) φl) :
    ∃ φ : Gl.left ⟶ G₁.left, IsGrpPullback Gl G₁ u φ ∧ φ ≫ m₁ = φl :=
  ⟨h₁.1.lift φl (Gl.hom ≫ u) (by rw [hGl.1.w, Category.assoc]),
    h₁.cancel (hGl.congr rfl (h₁.1.lift_fst _ _ _).symm) (h₁.1.lift_snd _ _ _), h₁.1.lift_fst _ _ _⟩

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (u : A →+* B) (v : B →+* C) :
    spMap v ≫ spMap u = spMap (v.comp u) := (Spec.map_comp _ _).symm

theorem spread_of_trait {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {D' : DegData V (maximalIdeal V)}
    {A' : PolAV (Sp (FractionRing V))} {G' : Over (Sp V)} [GrpObj G'] [IsCommMonObj G']
    (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left)
    (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsDiscreteValuationRing V₁] (ψ : R →+* V₁) (hψ : IsLocalHom ψ)
    (Ω : Type) [Field Ω] (α : V₁ →+* Ω) (hα : Function.Injective α) (b : V →+* Ω)
    (hb : ∀ x ∈ maximalIdeal V ^ (0 + 1), b x = 0) (eα : α.comp ψ = b.comp g)
    (GΩ : Over (Sp Ω)) [GrpObj GΩ] (n : GΩ.left ⟶ ((Over.pullback (spMap ψ)).obj G).left)
    (hn : IsGrpPullback GΩ ((Over.pullback (spMap ψ)).obj G) (spMap α) n)
    (n' : GΩ.left ⟶ G'.left) (hn' : IsGrpPullback GΩ G' (spMap b) n')
    (hnn : n ≫ pullback.fst G.hom (spMap ψ) = n' ≫ β)
    (j : splitTorus (Sp V₁) D'.toPre.X ⟶ (Over.pullback (spMap ψ)).obj G) (hj : IsMonHom j)
    (ej : GlobalTheory.TorusPart.pullTorus hn j = GlobalTheory.TorusPart.gtTorus (U'.gt 0) hb hn') :
    ∃ ρ, Spread U U' g β ρ := by
  haveI := hψ
  haveI := hj
  have hm₁ := isGrpPullback_pullback G (spMap ψ)
  have hm₀ := isGrpPullback_pullback ((Over.pullback (spMap ψ)).obj G) (spMap (residue V₁))
  have hm₀' := (hm₀.comp hm₁).congr (spMap_comp' ψ (residue V₁)) rfl
  have h₀ : ∀ x ∈ maximalIdeal R, (residue V₁).comp ψ x = 0 := GlobalTheory.TorusPart.map_eq_zero_of_isLocalHom _
  obtain ⟨ρ, hρ⟩ := (GlobalTheory.TorusPart.mono_gtTorus_and_factor (U.gt 0) (GlobalTheory.TorusPart.map_pow_one_eq_zero h₀)
    hm₀').2 _ (GlobalTheory.TorusPart.pullTorus hm₀ j) inferInstance
  exact ⟨ρ, V₁, inferInstance, inferInstance, inferInstance, ψ, (Over.pullback (spMap ψ)).obj G, inferInstance,
    inferInstance, pullback.fst G.hom (spMap ψ), Ω, inferInstance, α, b, hb, GΩ, inferInstance, n, hn, n', hn', j, _,
    inferInstance, _, hm₀, GlobalTheory.TorusPart.map_pow_one_eq_zero h₀, hm₀', hψ, hm₁, hj, hα, eα, hnn, ej, hρ⟩

theorem exists_spread : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left), IsGrpPullback G' G (spMap g) β → ∃ ρ, Spread U U' g β ρ := by
  intro R _ _ _ hR G _ _ hG D A U V _ _ _ hV G' _ _ hG' D' A' U' g β hβ
  haveI : IsNoetherianRing R := hR.1.1
  by_cases hl : IsLocalHom g
  · haveI := hl
    let κ := ResidueField V
    have hC : IsLocalHom (PowerSeries.C (R := κ)) :=
      ⟨fun a ha => by simpa using ha.map (PowerSeries.constantCoeff (R := κ))⟩
    let c : V →+* PowerSeries κ := (PowerSeries.C (R := κ)).comp (residue V)
    have hcl : IsLocalHom c := RingHom.isLocalHom_comp _ _
    let ψ : R →+* PowerSeries κ := c.comp g
    have hψ : IsLocalHom ψ := RingHom.isLocalHom_comp _ _
    let α := algebraMap (PowerSeries κ) (FractionRing (PowerSeries κ))
    have hα : Function.Injective α := IsFractionRing.injective _ _
    let b : V →+* FractionRing (PowerSeries κ) := α.comp c
    have hc0 : ∀ x ∈ maximalIdeal V, c x = 0 := fun x hx => by
      simp [c, (IsLocalRing.residue_eq_zero_iff x).2 hx]
    have hc : ∀ x ∈ maximalIdeal V ^ (0 + 1), c x = 0 := GlobalTheory.TorusPart.map_pow_one_eq_zero hc0
    have hb : ∀ x ∈ maximalIdeal V ^ (0 + 1), b x = 0 := fun x hx => by
      simp [b, hc x hx]
    have hm₁ := isGrpPullback_pullback G (spMap ψ)
    obtain ⟨mc, hmc, hmcβ⟩ := pull_cancel hβ (spMap c) (hm₁.congr (spMap_comp' g c).symm rfl)
    have hn := isGrpPullback_pullback ((Over.pullback (spMap ψ)).obj G) (spMap α)
    have hn' : IsGrpPullback _ G' (spMap b) _ := (hn.comp hmc).congr (spMap_comp' c α) rfl
    have hnn : pullback.fst ((Over.pullback (spMap ψ)).obj G).hom (spMap α) ≫ pullback.fst G.hom (spMap ψ) =
        (pullback.fst ((Over.pullback (spMap ψ)).obj G).hom (spMap α) ≫ mc) ≫ β := by
      rw [Category.assoc, hmcβ]
    exact spread_of_trait U U' g β (PowerSeries κ) ψ hψ _ α hα b hb rfl _ _ hn _ hn' hnn
      (GlobalTheory.TorusPart.gtTorus (U'.gt 0) hc hmc) inferInstance
      (GlobalTheory.TorusPart.pullTorus_gtTorus (U'.gt 0) hc hb hmc hn' hn rfl rfl)
  · obtain ⟨V₁, _, _, _, ψ, Ω, _, αK, b, hψ, hb, eα, hT⟩ := GlobalTheory.T.exists_trait_nonlocal_torusExtension' R G hG V g hl
    haveI := hψ
    let alg := algebraMap V₁ (FractionRing V₁)
    have hα : Function.Injective (αK.comp alg) :=
      αK.injective.comp (IsFractionRing.injective V₁ (FractionRing V₁))
    have hm₁ := isGrpPullback_pullback G (spMap ψ)
    have hG₁ : IsSemiAbelian ((Over.pullback (spMap ψ)).obj G) := IsSemiAbelian.pullback _ G hG
    obtain ⟨φ₁, hφ₁, -⟩ := pull_cancel hm₁ (spMap alg)
      ((isGrpPullback_pullback G (spMap (alg.comp ψ))).congr (spMap_comp' ψ alg).symm rfl)
    have hn' := isGrpPullback_pullback G' (spMap b)
    obtain ⟨n, hn, hnm⟩ := pull_cancel hm₁ (spMap (αK.comp alg))
      ((hn'.comp hβ).congr ((spMap_comp' g b).trans ((congrArg spMap eα.symm).trans
        (spMap_comp' ψ (αK.comp alg)).symm)) rfl)
    have hb' : ∀ x ∈ maximalIdeal V ^ (0 + 1), b x = 0 := GlobalTheory.TorusPart.map_pow_one_eq_zero hb
    obtain ⟨j, hj, ej⟩ := GlobalTheory.T.extend_splitTorus_hom_over_dvr V₁ ((Over.pullback (spMap ψ)).obj G) hG₁ _ φ₁ hφ₁ hT Ω αK _ n hn _
      (GlobalTheory.TorusPart.gtTorus (U'.gt 0) hb' hn') inferInstance
    exact spread_of_trait U U' g β V₁ ψ hψ Ω (αK.comp alg) hα b hb' eα _ n hn _ hn' hnm j hj ej

end GlobalTheory.SpreadTrait
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

attribute [local instance] GlobalTheory.TorusExt.gtGroup

namespace GlobalTheory.Poinc.Eq8.TorMatchLaws

theorem alg_eq {R F : Type} [CommRing R] [IsDomain R] [Field F] (i₁ i₂ : Algebra (FractionRing R) F)
    (h : ∀ r, @algebraMap _ _ _ _ i₁ (algebraMap R (FractionRing R) r) =
      @algebraMap _ _ _ _ i₂ (algebraMap R (FractionRing R) r)) : i₁ = i₂ := by
  apply Algebra.algebra_ext
  intro x
  have e := IsLocalization.ringHom_ext (M := nonZeroDivisors R) (S := FractionRing R)
    (j := @algebraMap _ _ _ _ i₁) (k := @algebraMap _ _ _ _ i₂) (RingHom.ext h)
  exact RingHom.congr_fun e x

theorem qk_eq {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {k : ℕ} {q q' : QkPt D F k} (hy : q.y = q'.y) (hg : q.g = q'.g) : q = q' := by
  cases q; cases q'; cases hy; cases hg; rfl

theorem tor_eq {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {τ : Multiplicative D.X →* Fˣ} {g : GtPtF D F} (h : GlobalTheory.UT.IsTor τ g) :
    g = GlobalTheory.TorusExt.torusPt D F (Additive.ofMul τ) :=
  (GlobalTheory.TorusExt.isTorusPtF_iff_eq g τ).1 ((GlobalTheory.UT.isTor_iff τ g).1 h)

theorem one_le_of_isUnit {R : Type} [CommRing R] [IsDomain R] {k : ℕ} (hk : IsUnit (k : R)) : 1 ≤ k := by
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h; simp at hk
  · exact h

end GlobalTheory.Poinc.Eq8.TorMatchLaws

namespace GlobalTheory.Poinc.Eq8.TorMatchLaws

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem tors_fun (hR : GlobalTheory.Mum.Base R) {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))} (U : Unif (maximalIdeal R) D A G)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] {k : ℕ} (hk : IsUnit (k : R)) :
    ∃ f : QkPt D.toPre F k → (TFK (R := R) F ⟶ A.A), (∀ p x, QkToAkU U.toUnifPre F k p x ↔ x = f p) ∧
      (∀ p p', f p = f p' ↔ QkPt.Equiv D.toPre F p p') ∧ (∀ p p' p'', QkAdd p p' p'' → f p'' = f p * f p') := by
  haveI := hR.2
  obtain ⟨f, ⟨h1, -, h3, h4, -⟩, -⟩ :=
    GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hR.1 D A G hG U F k (one_le_of_isUnit hk)
  exact ⟨f, h1, h3, h4⟩

theorem push {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))}
    (U : Unif (maximalIdeal R) D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] :
    ∃ e : (TFK (R := R) F ⟶ A.A) ≃* (Over.mk (jFK (R := R) F ≫ jK R) ⟶ G), ∀ x, (e x).left = x.left ≫ genMap U :=
  GlobalTheory.LiePull.exists_pushEquiv (GlobalTheory.ThetaBaseChange.grp_generic U.toUnifPre) (TFK (R := R) F) _ rfl

end GlobalTheory.Poinc.Eq8.TorMatchLaws

namespace GlobalTheory.Poinc.Eq8.TorMatchLaws

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem torMatch_id (hR : GlobalTheory.Mum.Base R) {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))} (U : Unif (maximalIdeal R) D A G) :
    TorMatch U U (RingHom.id R) (𝟙 G.left) (AddMonoidHom.id _) := by
  intro F _ _ i₁ i₂ hF
  obtain rfl : i₁ = i₂ := alg_eq i₁ i₂ hF
  intro k hk τ τ' q q' a a' _ hρ hy hτ hy' hτ' hq hq'
  obtain ⟨f, h1, -, -⟩ := tors_fun hR hG U F hk
  have e : τ = τ' := MonoidHom.ext fun x => hρ (Multiplicative.toAdd x)
  subst e
  have hqq : q = q' := qk_eq (hy.trans hy'.symm) ((tor_eq hτ).trans (tor_eq hτ').symm)
  subst hqq
  rw [(h1 q a).1 hq, (h1 q a').1 hq', Category.comp_id]

theorem torMatch_one (hR : GlobalTheory.Mum.Base R) {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))} (U : Unif (maximalIdeal R) D A G)
    {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {D' : DegData R (maximalIdeal R)} {A' : PolAV (Sp (FractionRing R))}
    (U' : Unif (maximalIdeal R) D' A' G') :
    TorMatch U U' (RingHom.id R) (1 : G' ⟶ G).left 0 := by
  intro F _ _ i₁ i₂ hF
  obtain rfl : i₁ = i₂ := alg_eq i₁ i₂ hF
  intro k hk τ τ' q q' a a' _ hρ hy hτ _ _ hq _
  obtain ⟨f, h1, h3, h4⟩ := tors_fun hR hG U F hk
  have e : τ = 1 := MonoidHom.ext fun x => by
    rw [MonoidHom.one_apply]
    refine (hρ (Multiplicative.toAdd x)).trans ?_
    rw [AddMonoidHom.zero_apply, ofAdd_zero, map_one]
  subst e
  have hg : q.g = 0 := by rw [tor_eq hτ, ofMul_one, map_zero]
  have hadd : QkAdd q q q := ⟨q, by rw [hy, add_zero], (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 (by rw [hg, add_zero]),
    (h3 q q).1 rfl⟩
  have ha : a = 1 := by
    rw [(h1 q a).1 hq]
    exact mul_eq_left.1 (h4 q q q hadd).symm
  obtain ⟨eU, heU⟩ := push U F
  obtain ⟨eU', heU'⟩ := push U' F
  have key : eU a = eU' a' ≫ (1 : G' ⟶ G) := by rw [comp_one, ha, map_one]
  rw [← heU, key, Over.comp_left, heU', Category.assoc]

theorem torMatch_mul (hR : GlobalTheory.Mum.Base R) {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))} (U : Unif (maximalIdeal R) D A G)
    {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {D' : DegData R (maximalIdeal R)} {A' : PolAV (Sp (FractionRing R))}
    (U' : Unif (maximalIdeal R) D' A' G') (p p' : G' ⟶ G) (ρ ρ' : D.toPre.X →+ D'.toPre.X)
    (hp : TorMatch U U' (RingHom.id R) p.left ρ) (hp' : TorMatch U U' (RingHom.id R) p'.left ρ') :
    TorMatch U U' (RingHom.id R) (p * p').left (ρ + ρ') := by
  intro F _ _ i₁ i₂ hF
  obtain rfl : i₁ = i₂ := alg_eq i₁ i₂ hF
  intro k hk τ τ' q q' a a' hτk hρ hy hτ hy' hτ' hq hq'
  obtain ⟨f, h1, h3, h4⟩ := tors_fun hR hG U F hk
  let τ₁ : Multiplicative D.toPre.X →* Fˣ := τ'.comp (AddMonoidHom.toMultiplicative ρ)
  let τ₂ : Multiplicative D.toPre.X →* Fˣ := τ'.comp (AddMonoidHom.toMultiplicative ρ')
  have pw : ∀ σ : D.toPre.X →+ D'.toPre.X, (τ'.comp (AddMonoidHom.toMultiplicative σ)) ^ k = 1 := fun σ =>
    MonoidHom.ext fun x => by
      rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← MonoidHom.pow_apply, hτk, MonoidHom.one_apply,
        MonoidHom.one_apply]
  obtain ⟨q₁, hy₁, hτ₁⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor D.tau_bimult τ₁ (pw ρ)
  obtain ⟨q₂, hy₂, hτ₂⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor D.tau_bimult τ₂ (pw ρ')
  have e₁ := hp F hF k hk τ₁ τ' q₁ q' (f q₁) a' hτk (fun _ => rfl) hy₁ hτ₁ hy' hτ' ((h1 q₁ _).2 rfl) hq'
  have e₂ := hp' F hF k hk τ₂ τ' q₂ q' (f q₂) a' hτk (fun _ => rfl) hy₂ hτ₂ hy' hτ' ((h1 q₂ _).2 rfl) hq'
  have hτe : τ = τ₁ * τ₂ := MonoidHom.ext fun x => by
    rw [MonoidHom.mul_apply]
    refine (hρ (Multiplicative.toAdd x)).trans ?_
    rw [AddMonoidHom.add_apply, ofAdd_add, map_mul]
    rfl
  have hg : q.g = q₁.g + q₂.g := by
    rw [tor_eq hτ, tor_eq hτ₁, tor_eq hτ₂, hτe, ofMul_mul, map_add (f := _)]
  have hadd : QkAdd q₁ q₂ q := ⟨q, by rw [hy, hy₁, hy₂, add_zero], (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 hg,
    (h3 q q).1 rfl⟩
  have ha : a = f q₁ * f q₂ := by rw [(h1 q a).1 hq]; exact h4 q₁ q₂ q hadd
  obtain ⟨eU, heU⟩ := push U F
  obtain ⟨eU', heU'⟩ := push U' F
  have k₁ : eU (f q₁) = eU' a' ≫ p := Over.OverMorphism.ext (by rw [heU, e₁, Over.comp_left, heU', Category.assoc])
  have k₂ : eU (f q₂) = eU' a' ≫ p' := Over.OverMorphism.ext (by rw [heU, e₂, Over.comp_left, heU', Category.assoc])
  have key : eU a = eU' a' ≫ (p * p') := by rw [comp_mul, ha, map_mul, k₁, k₂]
  rw [← heU, key, Over.comp_left, heU', Category.assoc]

end GlobalTheory.Poinc.Eq8.TorMatchLaws

namespace GlobalTheory.Poinc.Eq8


open TorMatchLaws in
theorem torMatch_id_one_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G'), TorMatch U U (RingHom.id R) (𝟙 G.left) (AddMonoidHom.id _) ∧ TorMatch U U' (RingHom.id R) (1 : G' ⟶ G).left 0 ∧ ∀ (p p' : G' ⟶ G) ρ ρ', TorMatch U U' (RingHom.id R) p.left ρ → TorMatch U U' (RingHom.id R) p'.left ρ' → TorMatch U U' (RingHom.id R) (p * p').left (ρ + ρ') := by
  intro R _ _ _ hR G _ _ hG D A U G' _ _ _ D' A' U'
  exact ⟨torMatch_id hR hG U, torMatch_one hR hG U U', fun p p' ρ ρ' hp hp' => torMatch_mul hR hG U U' p p' ρ ρ' hp hp'⟩

end GlobalTheory.Poinc.Eq8
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.Points

namespace GlobalTheory.Poinc.ChartAt

theorem exists_affine_chart_lift : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (w : X₁.M.Z), X₁.π w ∈ Set.range i → ∃ (U : X₁.M.Z.Opens) (u : Sp (X₁.M.ringOn U) ⟶ F.X), IsAffineOpen U ∧ w ∈ U ∧ (∀ w' ∈ U, X₁.π w' ∈ Set.range i) ∧ spMap (X₁.M.ringOn U).val.toRingHom ≫ u = spMap X₁.S.R.val.toRingHom ≫ X₁.u := by
  intro g n F W Z i X₁ w hw
  haveI := X₁.imm
  set V : X₁.M.Z.Opens := X₁.π ⁻¹ᵁ i.opensRange with hVdef
  have hwV : w ∈ V := by
    show X₁.π w ∈ (i.opensRange : Set Z)
    simpa [Scheme.Hom.coe_opensRange] using hw
  obtain ⟨U, hU, hwU, hUV⟩ := exists_isAffineOpen_mem_and_subset (X := X₁.M.Z) (U := V) hwV
  have hne : ((U : X₁.M.Z.Opens) : Set X₁.M.Z).Nonempty := ⟨w, hwU⟩
  have hUi : ∀ w' ∈ U, X₁.π w' ∈ Set.range i := by
    intro w' hw'
    have := hUV hw'
    simpa [hVdef, Scheme.Hom.coe_opensRange] using this
  let φ : Γ(X₁.M.Z, U) ⟶ CommRingCat.of (X₁.M.ringOn U) :=
    CommRingCat.ofHom (X₁.M.sectionsEquiv U hne).toRingHom
  let f : Sp (X₁.M.ringOn U) ⟶ X₁.M.Z := Spec.map φ ≫ hU.fromSpec
  have hrange : Set.range (f ≫ X₁.π) ⊆ Set.range i := by
    rintro _ ⟨y, rfl⟩
    apply hUi
    have : hU.fromSpec (Spec.map φ y) ∈ Set.range hU.fromSpec := ⟨_, rfl⟩
    rw [hU.range_fromSpec] at this
    exact this
  refine ⟨U, IsOpenImmersion.lift i (f ≫ X₁.π) hrange, hU, hwU, hUi, ?_⟩
  rw [← cancel_mono i, Category.assoc, IsOpenImmersion.lift_fac, Category.assoc, Category.assoc, ← X₁.comp]
  have hpt : ⊤ ≤ X₁.M.pt ⁻¹ᵁ U := X₁.M.top_le_preimage_pt hne
  have hφ : φ ≫ CommRingCat.ofHom (X₁.M.ringOn U).val.toRingHom = valMap X₁.M.pt U hpt := by
    ext a
    show ((X₁.M.sectionsEquiv U hne a : X₁.M.ringOn U) : X₁.Ω₁) = _
    rw [RatModel.coe_sectionsEquiv, ← valR_eq, valF_eq_valR]
  have hf : spMap (X₁.M.ringOn U).val.toRingHom ≫ f = X₁.M.pt := by
    simp only [f, ← Category.assoc]
    rw [spMap, ← Spec.map_comp, hφ, specMap_valMap_fromSpec]
  rw [← hf]
  simp only [f, Category.assoc]

end GlobalTheory.Poinc.ChartAt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem approxAt_mul_of_one_le (g n : ℕ) (F : SFam g n (zetaAway n)) (W8 : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0})
    (i : F.X ⟶ Z) (X₁ : Setup F W8 i) (φ : InvFun ℤ) (d m : ℕ) (hm : 1 ≤ m) (hd : ApproxAt X₁ φ d) :
    ApproxAt X₁ φ (d * m) := by
  intro p _ z₁ c₀ e
  obtain ⟨f, hf0, hf⟩ := hd p z₁ c₀ e
  have hpow : ∀ c : CTrait X₁ p z₁, ‖c.val (f ^ m)‖ = ‖c.val f‖ ^ m := fun c => by
    rw [CTrait.val_eq_valInt, CTrait.val_eq_valInt, map_pow]
    push_cast
    exact norm_pow _ _
  have hexp : ∀ c : CTrait X₁ p z₁, Real.exp (-(c.sc * (((d * m : ℕ) : ℝ) * φ.evalZ c.T.β))) =
      Real.exp (-(c.sc * (d * φ.evalZ c.T.β))) ^ m := fun c => by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  refine ⟨f ^ m, ?_, fun c => ?_⟩
  · rw [hpow, hf0, hexp]
  · rcases hf c with h1 | ⟨h, hh, h2⟩
    · left
      rw [hpow, hexp]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 m
    · right
      refine ⟨h, hh, ?_⟩
      rw [hpow]
      exact (pow_le_of_le_one (norm_nonneg _) (c.norm_val_le f) (by omega)).trans h2

theorem approxAt_mul : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W8 : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W8 i) (φ : InvFun ℤ) (d m : ℕ), 1 ≤ m → ApproxAt X₁ φ d → ApproxAt X₁ φ (d * m) := approxAt_mul_of_one_le

end GlobalTheory.Poinc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem stalk_isNoetherian_normal_fractionRing : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ)
    (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z),
    letI : Algebra (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ := (X₁.M.stalkHom z₁).toAlgebra;
    IsDomain (X₁.M.Z.presheaf.stalk z₁) ∧ IsFractionRing (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ ∧
      IsIntegrallyClosed (X₁.M.Z.presheaf.stalk z₁) ∧ IsNoetherianRing (X₁.M.Z.presheaf.stalk z₁) := by
  intro g n F W Z i X₁ z₁
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

end GlobalTheory.Poinc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PsiCoordRescaleLocal

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (q : D.X → (FractionRing R)ˣ) (y : D.X),
    PsiUnitOn D y Set.univ → ∀ s : R, (q y : FractionRing R) = algebraMap R (FractionRing R) s →
      ∃ u : Rˣ, Formalism.L2.Pj.PsiCoord (GlobalTheory.PolDeg.rescale D q) y (u * s) := by
  intro R _ _ _ D q y h s hs
  have hex : ∃ v : Rˣ, Formalism.L2.Pj.PsiCoord D y v := by
    obtain ⟨j, hj⟩ := GlobalTheory.PsiCoordLocal.exists_chart_top D y
    have hh := GlobalTheory.PsiCoordLocal.generic_le D y j hj
    obtain ⟨t, ht, e⟩ := h j ⊤ (isAffineOpen_top _) (Set.subset_univ _) hj hh
    obtain ⟨r, rfl⟩ := GlobalTheory.PsiCoordLocal.toOpen_top_bijective.2 t
    have hu : IsUnit r := (MulEquiv.isUnit_map
      (RingEquiv.ofBijective (Out.DegPre.toOpen (R := R) ⊤)
        GlobalTheory.PsiCoordLocal.toOpen_top_bijective).toMulEquiv).1 ht
    exact ⟨hu.unit, j, hj, hh, e⟩
  obtain ⟨v, hv⟩ := hex
  have h2 : Formalism.L2.Pj.PsiCoord (GlobalTheory.TauTwist.rescale D q) y (s * (v : R)) := by
    obtain ⟨x, ⟨j, hj, hj', rfl⟩, e⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D y v).1 hv
    refine (GlobalTheory.PeriodFormCompare.psiCoord_iff (GlobalTheory.TauTwist.rescale D q) y (s * (v : R))).2
      ⟨q y * GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.genVal (D.psi y) j hj, ⟨j, hj, hj', ?_⟩, ?_⟩
    · dsimp only [GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.genVal, GlobalTheory.TauTwist.rescale, GlobalTheory.TauTwist.withPsi, ReciprocityTheory.ChartRestriction.G.DVR.scaleGen]
      rw [map_mul, map_mul, GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.res_res]
      congr 1
      ext
      show (q y : FractionRing R) = (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom
        (((Sp (FractionRing R)).presheaf.map (𝟙 _)).hom
          ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (q y : FractionRing R)))
      rw [CategoryTheory.Functor.map_id]
      exact ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv_hom_id_apply _).symm
    · rw [Units.val_mul, hs, e, map_mul]
  refine ⟨v, ?_⟩
  rw [mul_comm]
  exact h2

end GlobalTheory.PsiCoordRescaleLocal
end
