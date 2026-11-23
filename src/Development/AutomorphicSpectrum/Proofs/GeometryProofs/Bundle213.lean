module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle090
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle082
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle015
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle156
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentPointValueHolomorphic
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle146
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle195
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WedgeEigenLineGenerator
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle016
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.YBrLat
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle208
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle209
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle032
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericCoordsDescendSubfield
public import Development.WeilBound.CoreStatements.AmpleLineBundles.NonemptyLieMetricOfCoordinates
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyExpLogCoverBound
import Formalism.LocalRingCardinality.DataHost
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle001
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002

@[expose] public section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.XR

theorem genMap_germ {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (p : Cpt ξ)
    {U : X.Opens} (hpU : p.1 ∈ U) (heU : genPt ξ ∈ U) (s : Γ(X, U)) :
    genMap ξ p ((X.presheaf.germ U p.1 hpU).hom s) =
      (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.germ U (genPt ξ) heU).hom s) := by
  have e : (X.presheaf.stalkSpecializes p.2).hom ((X.presheaf.germ U p.1 hpU).hom s) =
      (X.presheaf.germ U (genPt ξ) heU).hom s :=
    ConcreteCategory.congr_hom (X.presheaf.germ_stalkSpecializes hpU p.2) s
  exact congrArg (fun t : X.presheaf.stalk (genPt ξ) => (Scheme.stalkClosedPointTo ξ).hom t) e

theorem exists_eq_div_genMap {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (hξ : IsCptGen ξ) (p : Cpt ξ) (a : Ω) :
    ∃ u v : X.presheaf.stalk p.1, genMap ξ p v ≠ 0 ∧ a = genMap ξ p u / genMap ξ p v := by
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (x := p.1) (U := ⊤) trivial
  have heU : genPt ξ ∈ U := p.2.mem_open U.isOpen hpU
  obtain ⟨g, hg⟩ : ∃ g : X.presheaf.stalk (genPt ξ), (Scheme.stalkClosedPointTo ξ).hom g = a := hξ.bij.2 a
  letI alg : Algebra Γ(X, U) (X.presheaf.stalk (genPt ξ)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨genPt ξ, heU⟩ : U)
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk (genPt ξ)) (hU.primeIdealOf ⟨genPt ξ, heU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨genPt ξ, heU⟩
  obtain ⟨⟨f, h⟩, hfh⟩ := IsLocalization.surj (hU.primeIdealOf ⟨genPt ξ, heU⟩).asIdeal.primeCompl g
  have hunit := IsLocalization.map_units (X.presheaf.stalk (genPt ξ)) h
  let ψ : X.presheaf.stalk (genPt ξ) →+* Ω := (Scheme.stalkClosedPointTo ξ).hom
  have germ_val : ∀ s : Γ(X, U), genMap ξ p ((X.presheaf.germ U p.1 hpU).hom s) =
      (Scheme.stalkClosedPointTo ξ).hom (algebraMap Γ(X, U) (X.presheaf.stalk (genPt ξ)) s) :=
    fun s => genMap_germ p hpU heU s
  have hv : (Scheme.stalkClosedPointTo ξ).hom
      (algebraMap Γ(X, U) (X.presheaf.stalk (genPt ξ)) (h : Γ(X, U))) ≠ 0 :=
    (hunit.map (Scheme.stalkClosedPointTo ξ).hom).ne_zero
  refine ⟨(X.presheaf.germ U p.1 hpU).hom f, (X.presheaf.germ U p.1 hpU).hom h, ?_, ?_⟩
  · rw [germ_val]
    exact hv
  · rw [germ_val, germ_val, eq_div_iff hv, ← hg]
    exact (map_mul ψ _ _).symm.trans (congrArg ψ hfh)

theorem normalCpt_of_isCptGen {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (hξ : IsCptGen ξ) (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) : Flat.NormalCpt ξ := by
  intro p a ha
  obtain ⟨hd, hc⟩ := hX p.1
  letI : Algebra (X.presheaf.stalk p.1) Ω := (genMap ξ p).toAlgebra
  have hinj : Function.Injective (algebraMap (X.presheaf.stalk p.1) Ω) := hξ.inj p
  haveI : FaithfulSMul (X.presheaf.stalk p.1) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI : IsFractionRing (X.presheaf.stalk p.1) Ω := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨u, v, -, e⟩ := exists_eq_div_genMap hξ p z
    exact ⟨u, v, e⟩
  letI : Algebra (X.presheaf.stalk p.1) (regAt ξ p) := (genMap ξ p).rangeRestrict.toAlgebra
  haveI : IsScalarTower (X.presheaf.stalk p.1) (regAt ξ p) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsIntegral (X.presheaf.stalk p.1) (regAt ξ p) :=
    Algebra.IsIntegral.of_surjective (R := X.presheaf.stalk p.1) (A := X.presheaf.stalk p.1)
      (Algebra.ofId _ _) (genMap ξ p).rangeRestrict_surjective
  obtain ⟨b, hb⟩ := (IsIntegrallyClosed.isIntegral_iff (R := X.presheaf.stalk p.1) (K := Ω)).1
    (isIntegral_trans (R := X.presheaf.stalk p.1) (A := regAt ξ p) a ha)
  exact ⟨b, hb⟩

theorem exists_cpt_of_genericPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)), ∀ e ∈ genericPoints Y.X, ∃ (K : Type) (_ : Field K) (_ : CharZero K) (n : ℕ) (x : Fin n → K) (y : Sp K ⟶ Xo.XF c), CoordTie ℤ (y ≫ Y.j) x ∧ Flat.NormalCpt (y ≫ Y.j) ∧ GlobalTheory.CompanionTheory.Ar.genPt (y ≫ Y.j) = e := by
  intro E _ _ _ H D l Xo c Y e he
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  have hfrac : (letI := (algebraMap (𝓞 c.F) c.F).toAlgebra; IsFractionRing (𝓞 c.F) c.F) := by
    have : (algebraMap (𝓞 c.F) c.F).toAlgebra = (inferInstance : Algebra (𝓞 c.F) c.F) :=
      Algebra.algebra_ext _ _ fun _ => rfl
    rw [this]
    infer_instance
  have hmax : ∀ y : Y.X, y ⤳ e → y = e := by
    intro y hy
    have h1 : closure {e} = closure {y} :=
      (show Maximal IsIrreducible (closure {e}) from he).eq_of_le isIrreducible_singleton.closure
        (specializes_iff_closure_subset.1 hy)
    exact (inseparable_iff_closure_eq.2 h1.symm).eq
  have hgen : IsCptGen (Ω := Y.X.residueField e) (Y.X.fromSpecResidueField e) :=
    isCptGen_of_maximal Y.X (fun x => (Y.normal x).1) e hmax
  have hj : e ∈ Set.range Y.j :=
    GlobalTheory.T.generic_points_in_generic_fibre E H D l Xo c (𝓞 c.F) _ Y inferInstance hfrac he
  have hr : Set.range (Y.X.fromSpecResidueField e) ⊆ Set.range Y.j := by
    rw [Scheme.range_fromSpecResidueField]
    exact Set.singleton_subset_iff.2 hj
  obtain ⟨y, hy⟩ := GlobalTheory.T.field_point_lifts_generic_fibre E H D l Xo c (𝓞 c.F) _ Y hfrac (Y.X.residueField e)
    (Y.X.fromSpecResidueField e) hr
  have hch : CharZero (Y.X.residueField e) := by
    let φ : c.F →+* Y.X.residueField e :=
      (Spec.preimage (y ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))).hom
    exact charZero_of_injective_ringHom φ.injective
  have hover : Y.X.fromSpecResidueField e ≫ Y.s ≫ spMap (Int.castRingHom (𝓞 c.F)) =
      spMap (algebraMap ℤ (Y.X.residueField e)) := by
    rw [← Spec.map_preimage (Y.X.fromSpecResidueField e ≫ Y.s ≫ spMap (Int.castRingHom (𝓞 c.F)))]
    congr 1
    ext1
    exact Subsingleton.elim (α := ℤ →+* Y.X.residueField e) _ _
  obtain ⟨n, x, hx⟩ := GlobalTheory.T.projective_over_coords_exist ℤ Y.X (Y.s ≫ spMap (Int.castRingHom (𝓞 c.F)))
    (GlobalTheory.T.projective_over_restrict_int (𝓞 c.F) Y.X Y.s Y.proj) (Y.X.residueField e) (Y.X.fromSpecResidueField e) hgen hover
  refine ⟨Y.X.residueField e, inferInstance, hch, n, x, y, ?_, ?_, ?_⟩
  · rw [hy]; exact hx
  · rw [hy]; exact normalCpt_of_isCptGen hgen Y.normal
  · rw [hy]; exact Y.X.fromSpecResidueField_apply e _

end GlobalTheory.CompanionTheory.Ar.XR
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagStep

theorem mem_of_mem_iSup_of_indep {Ω W I : Type} [Field Ω] [AddCommGroup W] [Module Ω W] (A : Subring Ω)
    {F : I → Submodule Ω W} (hF : iSupIndep F) {P : I → Submodule A W}
    (hP : ∀ t, P t ≤ (F t).restrictScalars A) (s : I) {x : W} (hx : x ∈ ⨆ t, P t) (hxs : x ∈ F s) : x ∈ P s := by
  classical
  have hsplit : (⨆ t, P t) ≤ P s ⊔ ⨆ (t) (_ : t ≠ s), P t := iSup_le fun t => by
    by_cases e : t = s
    · subst e
      exact le_sup_left
    · exact le_sup_of_le_right (le_iSup₂_of_le t e le_rfl)
  obtain ⟨a, ha, d, hd, rfl⟩ := Submodule.mem_sup.1 (hsplit hx)
  have hd2 : d ∈ ⨆ (t) (_ : t ≠ s), F t := by
    have hle : (⨆ (t) (_ : t ≠ s), P t) ≤ (⨆ (t) (_ : t ≠ s), F t).restrictScalars A :=
      iSup₂_le fun t e v hv => (le_iSup₂_of_le t e le_rfl : F t ≤ ⨆ (t) (_ : t ≠ s), F t) (hP t hv)
    exact hle hd
  have hd3 : d ∈ F s := by
    have h := sub_mem hxs (show a ∈ F s from hP s ha)
    simpa using h
  have h0 : d = 0 := Submodule.disjoint_def.1 (hF s) d hd3 hd2
  rw [h0, add_zero]
  exact ha

theorem eigLat_isFlagVBOn_of_pull_char0 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Tor.Level H) (c : Coeff l)
    (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω₀]
    [CharZero Ω] [Algebra Ω₀ Ω] (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X')
    (cst : c.F →+* Ω₀) (V V' : Type) [AddCommGroup V] [Module Ω₀ V] [AddCommGroup V'] [Module Ω V']
    (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ' V') (ρ : 𝓞 E →+* Module.End Ω₀ V) (ρ' : 𝓞 E →+* Module.End Ω V')
    (L : CMType H ⊕ CMType H → Lat ξ V) (j : V →+ V') (r : CMType H ⊕ CMType H → ℕ)
    (b : ∀ s, Fin (r s) → V'),
    IsCptGen ξ → IsCptGen ξ' → GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f (algebraMap Ω₀ Ω) →
    M.IsActOf t.act.act ρ → M'.IsActOf t'.act.act ρ' →
    (∀ q : Cpt ξ, (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → IsIntegrallyClosed (regAt ξ q)) →
    (∀ q : Cpt ξ', (∀ r : ℕ, r.Prime → ¬ InFibre ξ' r q) → IsIntegrallyClosed (regAt ξ' q)) →
    (∀ s (q : Cpt ξ), (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → L s q = M.eigLat ρ (cst.comp (labelEmb c s)) q) →
    M'.lat = M.lat.pull ξ' f j →
    (∀ s, ∀ e ∈ eigSp ρ (cst.comp (labelEmb c s)),
      j e ∈ eigSp ρ' (((algebraMap Ω₀ Ω).comp cst).comp (labelEmb c s))) →
    (∀ s, ((L s).pull ξ' f j).IsFlagVBOn Set.univ (b s)) →
    ∀ s, (M'.eigLat ρ' (((algebraMap Ω₀ Ω).comp cst).comp (labelEmb c s))).IsFlagVBOn
      {q | ∀ r : ℕ, r.Prime → ¬ InFibre ξ' r q} (b s) := by
  intro E _ _ _ H l c X X' t t' f Ω₀ Ω _ _ _ _ _ ξ ξ' cst V V' _ _ _ _ M M' ρ ρ' L j r b hg hg' hd hact hact' hint hint'
    hL hlat hj hfl
  have key : ∀ s (q : Cpt ξ'), (∀ r : ℕ, r.Prime → ¬ InFibre ξ' r q) →
      (M'.eigLat ρ' (((algebraMap Ω₀ Ω).comp cst).comp (labelEmb c s))) q = ((L s).pull ξ' f j) q := by
    intro s q hq
    obtain ⟨h, -, h2⟩ := RegAtDom.regAt_dominates X Ω₀ ξ X' Ω ξ' f (algebraMap Ω₀ Ω) hd q
    have hp : ∀ r : ℕ, r.Prime → ¬ InFibre ξ r ⟨f q.1, h⟩ := fun r hr hn =>
      hn (h2 hg' _ (natCast_mem _ r) (by rw [map_natCast]; exact not_not.1 (hq r hr)))
    have hsum := (SatModel.lat_eq_iSup_of_char0 c t ξ hg cst M ρ hact hint).2 _ hp
    have hind := (SatModel.lat_eq_iSup_of_char0 c t' ξ' hg' ((algebraMap Ω₀ Ω).comp cst) M' ρ' hact' hint').1
    have hle : ∀ u, ((L u).pull ξ' f j) q ≤ M'.lat q ⊓
        (eigSp ρ' (((algebraMap Ω₀ Ω).comp cst).comp (labelEmb c u))).restrictScalars (regAt ξ' q) := by
      intro u
      refine Submodule.span_le.2 ?_
      rintro _ ⟨h', e, he, rfl⟩
      have he' : e ∈ M.lat.inter (eigSp ρ (cst.comp (labelEmb c u))) ⟨f q.1, h⟩ := by
        have h3 := hL u ⟨f q.1, h⟩ hp
        have h4 : e ∈ L u ⟨f q.1, h⟩ := he
        rw [h3] at h4
        exact h4
      refine ⟨?_, hj u e he'.2⟩
      show j e ∈ M'.lat q
      rw [hlat]
      exact Submodule.subset_span ⟨h, e, he'.1, rfl⟩
    have hall : M'.lat q ≤ ⨆ u, ((L u).pull ξ' f j) q := by
      rw [hlat]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨h', e, he, rfl⟩
      have he1 : e ∈ ⨆ u, M.lat.inter (eigSp ρ (cst.comp (labelEmb c u))) ⟨f q.1, h⟩ := by
        rw [← hsum]
        exact he
      refine Submodule.iSup_induction _ (motive := fun e => j e ∈ ⨆ u, ((L u).pull ξ' f j) q) he1
        (fun u e he => ?_) ?_ (fun x y hx hy => ?_)
      · refine Submodule.mem_iSup_of_mem u (Submodule.subset_span ⟨h, e, ?_, rfl⟩)
        have h3 := hL u ⟨f q.1, h⟩ hp
        rw [h3]
        exact he
      · simp only [map_zero]
        exact zero_mem _
      · simp only [map_add (f := _)]
        exact add_mem hx hy
    refine le_antisymm ?_ (hle s)
    rintro x ⟨hx1, hx2⟩
    exact mem_of_mem_iSup_of_indep (regAt ξ' q) hind (fun u => (hle u).trans inf_le_right) s (hall hx1) hx2
  intro s p hp
  obtain ⟨U, hU, b', hb, hf⟩ := hfl s p trivial
  refine ⟨U, hU, b', hb, fun q hq hqU => ?_⟩
  obtain ⟨h1, h2⟩ := hf q trivial hqU
  exact ⟨h1, (key s q hq).trans h2⟩

end GlobalTheory.CompanionTheory.Ar.FlagStep
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.MetricAny

theorem exists_lieMetric : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), CharZero Ω → (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li), Nonempty (LieMetric M y) := by
  exact @CoverDenseAlt.nonempty_lie_metric_of_coordinates

end GlobalTheory.CompanionTheory.Ar.MetricAny
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FrameVal

theorem exists_framed_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (b₁ : Fin D.p → Z.V) (b₂ : Fin D.q → Z.V) (y : Sp ℂ ⟶ Xo.XF c) (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → σ (tauIn c τ H.rt) = H.rt0 → y ≫ pullback.snd _ _ = spMap σ → (Z.eig τ).IsFrameAt b₁ ⟨_, h⟩ → (Z.eig (ComplexEmbedding.conjugate τ)).IsFrameAt b₂ ⟨_, h⟩ → ∃ (v : Vecs y D.p) (w : Vecs y D.q), IsFramed Set.univ τ σ y v w ∧ (∀ i, ∃ v', Z.M.ValAt (y ≫ Y.j) (b₁ i) v' ∧ SameVec Y y (v i) v') ∧ ∀ j, ∃ w', Z.M.ValAt (y ≫ Y.j) (b₂ j) w' ∧ SameVec Y y (w j) w' := by
  intro E _ _ _ H D l Xo c O _ β Y U Z τ σ b₁ b₂ y h hO hτ _ hy hf₁ hf₂
  haveI : Smooth Y.t.G.hom := Y.t.semi.smooth
  obtain ⟨-, -, h3, -⟩ := GlobalTheory.T.eigen_lattice_vector_bundle E H D l Xo c O β Y U Z τ hO hτ
  have hfib : (⟨centre (y ≫ Y.j), h⟩ : Cpt (Z.ξ₀ ≫ Y.j)) ∈ Z.genFib :=
    ⟨Y.jQ (y (IsLocalRing.closedPoint ℂ)), by simp only [Model.j, centre, Scheme.Hom.comp_apply]⟩
  obtain ⟨g, b, hb, hS⟩ := h3 _ hfib
  obtain ⟨ER, _, _, ⟨MR⟩⟩ := lieModel_exists Y.X Y.t.G ℂ (y ≫ Y.j)
  obtain ⟨ev, hev, -, -⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring Y.X Y.t.G Z.Ω (Z.ξ₀ ≫ Y.j) Z.V Z.M ℂ (y ≫ Y.j) h ER MR Z.gen inferInstance
  have hval : ∀ {n : ℕ} (τ' : E →+* ℂ) (e : Fin n → Z.V), (Z.eig τ').IsFrameAt e ⟨centre (y ≫ Y.j), h⟩ →
      ∀ i, ∃ w, Z.M.ValAt (y ≫ Y.j) (e i) (MR.pt w) := fun τ' e hf i => by
    have hmem : e i ∈ Z.eig τ' ⟨centre (y ≫ Y.j), h⟩ := by
      rw [hf.2]
      exact Submodule.subset_span ⟨i, rfl⟩
    exact ⟨ev ⟨e i, hmem.1⟩, (hev _ _).2 ⟨hmem.1, rfl⟩⟩
  choose w₁ hw₁ using hval τ b₁ hf₁
  choose w₂ hw₂ using hval _ b₂ hf₂
  choose v hv using fun i => exists_sameVec_left Y y (MR.pt (w₁ i))
  choose w hw using fun j => exists_sameVec_left Y y (MR.pt (w₂ j))
  obtain ⟨hL₁, hL₂⟩ := GlobalTheory.CompanionTheory.Ar.LocFrames.lieMult_at y σ τ hy hτ
  refine ⟨v, w, ⟨hy, Set.subset_univ _, ?_, ?_⟩, fun i => ⟨_, hw₁ i, hv i⟩, fun j => ⟨_, hw₂ j, hw j⟩⟩
  · exact GlobalTheory.CompanionTheory.Ar.LocFrames.isEigFrame_of_values Z σ y τ D.p b₁ v (fun i => MR.pt (w₁ i)) h hO.2.2 hy hL₁
      ⟨g, b, hb, hS τ⟩ hf₁ hw₁ hv
  · exact GlobalTheory.CompanionTheory.Ar.LocFrames.isEigFrame_of_values Z σ y _ D.q b₂ w (fun j => MR.pt (w₂ j)) h hO.2.2 hy hL₂
      ⟨g, b, hb, hS _⟩ hf₂ hw₂ hw

end GlobalTheory.CompanionTheory.Ar.FrameVal
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric


theorem _root_.GlobalTheory.T.component_point_value_holomorphic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (y₀ : Sp ℂ ⟶ Xo.XF c), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → y₀ ≫ pullback.snd _ _ = spMap σ → Set.range y₀ ⊆ U → ∃ (V₀ : (Xo.XF c).Opens) (hV₀ : IsAffineOpen V₀) (c₁ : Fin D.p → Z.V) (c₂ : Fin D.q → Z.V) (vR : Fin D.p → (epsAt (under hV₀.fromSpec) ⟶ Xo.univ.t.G)) (wR : Fin D.q → (epsAt (under hV₀.fromSpec) ⟶ Xo.univ.t.G)), ⊤ ≤ y₀ ⁻¹ᵁ V₀ ∧ LinearIndependent Z.Ω c₁ ∧ Submodule.span Z.Ω (Set.range c₁) = eigSp Z.ρ (Z.inc.comp (tauIn c τ)) ∧ LinearIndependent Z.Ω c₂ ∧ Submodule.span Z.Ω (Set.range c₂) = eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ))) ∧ ∀ (χ : Γ(Xo.XF c, V₀) →+* ℂ) (v : Vecs (spMap χ ≫ hV₀.fromSpec) D.p) (w : Vecs (spMap χ ≫ hV₀.fromSpec) D.q), (spMap χ ≫ hV₀.fromSpec) ≫ pullback.snd _ _ = spMap σ → Set.range (spMap χ ≫ hV₀.fromSpec) ⊆ U → (∀ a, (v a).left = spMap (dualMap χ) ≫ (vR a).left) → (∀ j, (w j).left = spMap (dualMap χ) ≫ (wR j).left) → IsFramed U τ σ (spMap χ ≫ hV₀.fromSpec) v w ∧ (∀ i, ∃ v', Z.M.ValAt ((spMap χ ≫ hV₀.fromSpec) ≫ Y.j) (c₁ i) v' ∧ SameVec Y (spMap χ ≫ hV₀.fromSpec) (v i) v') ∧ ∀ j, ∃ w', Z.M.ValAt ((spMap χ ≫ hV₀.fromSpec) ≫ Y.j) (c₂ j) w' ∧ SameVec Y (spMap χ ≫ hV₀.fromSpec) (w j) w' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFrames.exists_local_eigenframes | exact GlobalTheory.CompanionTheory.Ar.LocFrames.exists_local_eigenframes | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFrames.exists_local_eigenframes <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.generic_coords_descend_subfield : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ X) (f : X ⟶ Y.X) (Ω₀ : Type) [Field Ω₀] [Algebra Ω₀ Ω] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X) (cst : c.F →+* Ω) (t : SAB H X) (m : SABMap t Y.t f) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (ρ : 𝓞 E →+* Module.End Ω Li) (Li₀ : Type) [AddCommGroup Li₀] [Module Ω₀ Li₀] (M₀ : LieModel Y.t.G ξ₀ Li₀) (j : Li₀ →+ Li) (V₀ : CMType H ⊕ CMType H → Submodule Ω₀ Li₀) (b : ∀ s, Fin (labelRk D s) → Li) (d : ℕ), (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → (∀ q : Cpt ξ, (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → IsIntegrallyClosed (regAt ξ q)) → IsCptGen ξ₀ → GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ f (algebraMap Ω₀ Ω) → ξ ≫ f ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) → M.IsActOf t.act.act ρ → (∀ e, (M.pt (j e)).left ≫ m.φ = spMap (dualMap (algebraMap Ω₀ Ω)) ≫ (M₀.pt e).left) → (∀ s e, e ∈ V₀ s ↔ j e ∈ eigSp ρ (cst.comp (labelEmb c s))) → IsGenericFlag (Ω' := Ω) j V₀ b d → (∀ s, (M.eigLat ρ (cst.comp (labelEmb c s))).IsFlagVBOn {q | ∀ r : ℕ, r.Prime → ¬ InFibre ξ r q} (b s)) → ∃ (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k)) (y' : (Σ k, J' k) → Ω) (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (𝔐 : HodgeCpt Y ∅ y') (g : 𝔐.X ⟶ X) (Fl : 𝔐.Flag) (xdeg : RootIx D → K' → ℤ) (e : RootIx D → Ω), Function.Injective bk ∧ (∀ k a, y' ⟨bk k, bx k a⟩ = y ⟨k, a⟩) ∧ 𝔐.ξ ≫ g = ξ ∧ 𝔐.f = g ≫ f ∧ genPt 𝔐.ξ₀ = genPt ξ₀ ∧ Fl.deg = d ∧ Fl.RootLines xdeg e ∧ (∀ s i, (𝔐.M.pt (Fl.b s i)).left ≫ 𝔐.m.φ = (M.pt (b s i)).left ≫ m.φ) ∧ (∀ q' : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q') → ∀ h : genPt ξ ⤳ g q'.1, regAt 𝔐.ξ q' = regAt ξ ⟨g q'.1, h⟩) ∧ ∀ q₁ q₂ : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q₁) → g q₁.1 = g q₂.1 → q₁ = q₂ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_sat_model | exact GlobalTheory.CompanionTheory.Ar.exists_sat_model | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_sat_model <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.wedge_eigen_line_generator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (a : ⋀[Z.Ω]^D.p Z.V) (b : ⋀[Z.Ω]^D.q Z.V), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → IsLineGenOn (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q a b Z.genFib → ∃ φ : FrameFn Xo c, IsLineFn U τ φ ∧ Represents Y U τ Z.M a b φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_frameFn_of_gen | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_frameFn_of_gen | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_frameFn_of_gen <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.tower_components_equiv_of_given : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : TowerOrigin Y T), Top.Given → ∃ κ : Comp Xo c ≃ T.Comp, CompOf o κ := by
  first | exact @GlobalTheory.CompanionTheory.Relay.tower_components_equiv_of_given | exact GlobalTheory.CompanionTheory.Relay.tower_components_equiv_of_given | (intros; apply GlobalTheory.CompanionTheory.Relay.tower_components_equiv_of_given <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.CompanionTheory.Relay.lattice_sections_cusp_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (a : WZ E) (x : ℝ), (Lat.secZ Xo c a 0 = secZ Xo c a ∧ Lat.cuspZ U a 0 = cuspZ Xo c U a ∧ Lat.lieZ Dw x a = lieFacZ Dw x a ∧ ∀ f, f ∈ Lat.latZ U a 0 ↔ f ∈ cuspZ Xo c U a ∧ ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f) ∧ ∀ b, WEq Dw a b → secZ Xo c a = secZ Xo c b ∧ cuspZ Xo c U a = cuspZ Xo c U b ∧ lieFacZ Dw x a = lieFacZ Dw x b ∧ towerWt Dw a = towerWt Dw b ∧ (∀ σ, GoodEmb c σ → laZ (U σ) a = laZ (U σ) b) ∧ ∀ Z, cuspOn U h a Z = cuspOn U h b Z ∧ latOn U h a Z = latOn U h b Z := by
  first | exact @PositivityTheory.UnitarySelfGeneration.y_br_lat | exact PositivityTheory.UnitarySelfGeneration.y_br_lat
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.cm_image_unique_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (b : Bool) (a : PureType.lat hP (sgnRt H b)), (∃! u, X.IsImage b a u) ∧ ∀ u, X.IsImage b a u → IsTanAt Xo.univ.t.G _ u ∧ IsDerivAt0 (fun s => (FU.ex i P s).left) ((Z b).z • P a) (spMap (dualMap (algebraMap X.K ℂ)) ≫ u.left) := by
  exact @GlobalTheory.CompanionTheory.Relay.cm_image_unique_lattice
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.family_exp_log_cover_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n a : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (ρ : ℝ) (e : Flat.FamExp t.G M (Metric.ball 0 ρ) ψ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ), 0 < ρ → ρ ≤ 1 → Flat.IsHolPts (Metric.ball 0 ρ) ψ → (∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, (∀ p, p ∈ e.per ((ρ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a w) ↔ ∃ x, L.P w x = p) ∧ ∀ (N : ℕ) (ζ : ℂˣ) (x x' : Λ), 0 < N → GlobalTheory.UU.CubWeil t.cub N (e.ex ((ρ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a w) ((N : ℂ)⁻¹ • L.P w x)) (e.ex ((ρ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a w) ((N : ℂ)⁻¹ • L.P w x')) (unitOn ζ) → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((L.E x x' : ℤ) : ℂ) / N)) → ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ (ws : ℕ → Fin n → ℂ) (W : Submodule ℤ Λ) (per : W →+ (Fin g → ℂ)), (∀ m, ws m ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le) → Tendsto (fun m => GroundTheory.Heights₂.Heights.Regular.expCover a (ws m)) atTop (𝓝 z) → (∀ x : W, Tendsto (fun m => L.P (ws m) x) atTop (𝓝 (per x))) → (∀ (x : ℕ → Λ) (p : Fin g → ℂ), Tendsto (fun m => L.P (ws m) (x m)) atTop (𝓝 p) → ∃ x₀ : W, p = per x₀ ∧ ∀ᶠ m in atTop, x m = x₀) → (∀ x : W, per x ∈ e.per ((ρ : ℂ) • z)) ∧ (∀ p ∈ e.per ((ρ : ℂ) • z), ∃ x : W, per x = p) ∧ ∀ (N : ℕ) (ζ : ℂˣ) (x x' : W), 0 < N → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((L.E x x' : ℤ) : ℂ) / N) → GlobalTheory.UU.CubWeil t.cub N (e.ex ((ρ : ℂ) • z) ((N : ℂ)⁻¹ • per x)) (e.ex ((ρ : ℂ) • z) ((N : ℂ)⁻¹ • per x')) (unitOn ζ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotLoc.limit_lattice | exact GlobalTheory.CompanionTheory.Ar.QuotLoc.limit_lattice | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotLoc.limit_lattice <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.form_off_specialization_ring : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω), Birational y → ∀ B : Finset Ω, ∃ u : MRing ι, Small.IsFormOff (mCoordIdeal y) u ∧ ∀ (𝕜 : Type) [Field 𝕜] [CharZero 𝕜] (z : (Σ k, ι k) → 𝕜), z ∈ Small.ptsOver 𝕜 (mCoordIdeal y) → MvPolynomial.aeval z u ≠ 0 → ∃ (A : Subring Ω) (ev : A →+* 𝕜), (↑B : Set Ω) ⊆ A ∧ (∀ n : ℕ, n ≠ 0 → ((n : Ω))⁻¹ ∈ A) ∧ ∀ x : A, Small.HasVal y 0 (x : Ω) z (ev x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ValSub.exists_subring_val | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ValSub.exists_subring_val | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ValSub.exists_subring_val <;> assumption)
end
