module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle052
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.QSurjective
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsPullbackCompIsoMonHom
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle053
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsLevelStructureOfGenericOfFibrewiseIndep
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle049
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_primitive_scaling_alt : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Sp V)) [GrpObj G], IsSemiAbelian G → ∀ (M : LB G.left), M.IsLB → ∀ (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (ψ : pullback G.hom (jK V) ⟶ Y) (w : LB.Iso (M.pull (pullback.fst G.hom (jK V))) (L.pull ψ)), w.IsGen → ∀ θ : LB.Sec L, (∃ z, ψ z ∈ nonzeroLocus θ) → ∃ (ϑ : H0 M 1) (c : FractionRing V), c ≠ 0 ∧ (∃ z ∈ nonzeroLocus ϑ, G.hom z = IsLocalRing.closedPoint V) ∧ ∀ x : Sp (FractionRing V) ⟶ pullback G.hom (jK V), x ≫ pullback.snd G.hom (jK V) = 𝟙 _ → ∀ (i : M.ι) (k : L.ι), ⊤ ≤ (x ≫ pullback.fst G.hom (jK V)) ⁻¹ᵁ M.U i → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U k → valR x _ (w.s (fun _ => k, fun _ => i)).val * valR (x ≫ pullback.fst G.hom (jK V)) _ (ϑ.f (fun _ => i)) = c * valR (x ≫ ψ) _ (θ.f k) := by
  first | exact @GlobalTheory.PrimScale.exists_primitive_scaling | exact GlobalTheory.PrimScale.exists_primitive_scaling | (intros; apply GlobalTheory.PrimScale.exists_primitive_scaling <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

theorem _root_.GlobalTheory.T.exists_fg_subalgebra_spec_factor_through_open : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω), R.FG → ∀ V : (Sp R).Opens, (V : Set (Sp R)).Nonempty → ∃ (R' : Subalgebra o Ω) (h : R ≤ R'), R'.FG ∧ ∃ τ : Sp R' ⟶ V.toScheme, τ ≫ V.ι = spMap (Subalgebra.inclusion h).toRingHom := by
  first | exact @GlobalTheory.exists_fg_subalgebra_spec_factors_open | exact GlobalTheory.exists_fg_subalgebra_spec_factors_open | (intros; apply GlobalTheory.exists_fg_subalgebra_spec_factors_open <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_torsion_lift_specialFibre_of_generic_rational : (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (W C : Type) [CommRing W] [IsLocalRing W] [Field C] (α : V →+* W) (β : W →+* C) (ga : FractionRing V →+* C), IsLocalHom α → Function.Injective β → β.comp α = ga.comp (algebraMap V (FractionRing V)) → ∀ (X : Scheme.{0}) (y : Sp W ⟶ X) (x : Sp (FractionRing V) ⟶ X), spMap β ≫ y = spMap ga ≫ x → ∃ h : Sp V ⟶ X, spMap α ≫ h = y ∧ jK V ≫ h = x) → UnramExtSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] (C : Type) [Field C] [IsAlgClosed C] (ga : FractionRing V →+* C) (m : ℕ), IsUnit (m : V) → (∀ y : Over.mk (spMap ga ≫ jK V) ⟶ G, y ^ m = 1 → ∃ x : Sp (FractionRing V) ⟶ G.left, spMap ga ≫ x = y.left) → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (f : V →+* κ), IsLocalHom f → ∀ x : Over.mk (spMap f) ⟶ G, x ^ m = 1 → ∃ h : baseOver (Sp V) ⟶ G, h ^ m = 1 ∧ spMap f ≫ h.left = x.left := by
  first | exact @GlobalTheory.exists_torsion_lift_of_generic_rational | exact GlobalTheory.exists_torsion_lift_of_generic_rational | (intros; apply GlobalTheory.exists_torsion_lift_of_generic_rational <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section

namespace GlobalTheory


open GtBaseChange in
theorem exists_gtDatum_baseChange_maps :
    ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (E : SplitExt S) (G : Over S) [GrpObj G] (d : E.GtDatum G), ∃ (E' : SplitExt S') (xe : E'.X ≃+ E.X) (d' : E'.GtDatum ((Over.pullback f).obj G)) (π : E'.B.left ⟶ E.B.left), IsGrpPullback E'.B E.B f π ∧ d'.q.left ≫ π = pullback.fst G.hom f ≫ d.q.left ∧ (∀ χ, LBIso (E'.O χ).L ((E.O (xe χ)).L.pull π)) ∧ ∀ (Z : Over S') (τ : Z ⟶ splitTorus S' E'.X), ∃ τ₀ : Over.mk (Z.hom ≫ f) ⟶ splitTorus S E.X, (τ₀ ≫ d.i).left = (τ ≫ d'.i).left ≫ pullback.fst G.hom f ∧ ∀ (χ : E'.X) (z : Z.left), gm (Y := Z.left) τ₀.left z ⊤ (charUnit S E.X (xe χ)) = gm τ.left z ⊤ (charUnit S' E'.X χ) := by
  intro S S' f E G _ d
  have := d.q_hom
  have := d.i_hom
  have : IsMonHom (Iso.refl ((Over.pullback f).obj G)).hom := inferInstanceAs (IsMonHom (𝟙 _))
  have : IsMonHom (Iso.refl ((Over.pullback f).obj E.B)).hom := inferInstanceAs (IsMonHom (𝟙 _))
  obtain ⟨eT, mT, hT⟩ := splitTorus_baseChange S S' f E.X
  obtain ⟨q, i, h1, h2, h3, h4, h5, h6, h7, h8⟩ := TorusExtBaseChange.exists_extension f eT
    (Iso.refl ((Over.pullback f).obj G)) (Iso.refl ((Over.pullback f).obj E.B)) d.i d.q d.q_flat d.q_surjective
    d.q_affine d.isKernel
  have hq : q.left ≫ pullback.fst E.B.hom f = pullback.fst G.hom f ≫ d.q.left := by simpa using h7
  have hi : i.left ≫ pullback.fst G.hom f = (eT.hom.left ≫ pullback.fst _ f) ≫ d.i.left := by simpa using h8
  have le : ∀ j : (extBC f E).ChartIdx, q.left ⁻¹ᵁ (extBC f E).chart j ≤
      pullback.fst G.hom f ⁻¹ᵁ (d.q.left ⁻¹ᵁ E.chart (fun k => j k PUnit.unit)) := fun j y hy => by
    change (pullback.fst G.hom f ≫ d.q.left) y ∈ E.chart (fun k => j k PUnit.unit)
    rw [← hq]
    exact chart_le_preimage f E j hy
  let u : ∀ (j : (extBC f E).ChartIdx) (_ : Module.Free.ChooseBasisIndex ℤ E.X),
      Γ(((Over.pullback f).obj G).left, q.left ⁻¹ᵁ (extBC f E).chart j)ˣ := fun j k =>
    res (le j) (pullU (pullback.fst G.hom f) _ (d.u (fun k => j k PUnit.unit) k))
  have hw : ∀ j k, HasWeight i _ (u j k) (E.basis k) := fun j k =>
    HasWeight.baseChange f ((hasWeight_iff d.i _ _ _ (d.act_le _) _).2 (d.equiv _ k)) i _ (by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      exact congrArg (· ≫ f) (Over.w eT.hom)) hi (hT _) (le j)
      fun Z t g z hz => translate_mem q i h6 t g _ z hz
  refine ⟨extBC f E, AddEquiv.refl _,
    { q := q
      i := i
      q_hom := h1
      i_hom := h5
      q_flat := h2
      q_surjective := h3
      q_affine := h4
      isKernel := h6
      u := u
      coord := fun j V hV h => coord_of_hasWeight E.basis q i h2 h3 h4 h6 _ (u j) (hw j) V hV h
      trans := fun j j' k => unit_ext fun y hy => ?_
      act_le := fun j y hy => translate_mem q i h6 (fst _ _) (snd _ _) ((extBC f E).chart j) y hy
      equiv := fun j k => (hasWeight_iff i _ _ _ _ _).1 (hw j k)
      unit_norm := fun j k => unit_ext fun y hy => ?_ }, pullback.fst E.B.hom f,
    isGrpPullback_pullback E.B f, hq, fun χ => GtBaseChange.lbIso_refl (pull_isLB (E.O χ).isLB _),
    fun Z τ => ?_⟩
  · have hm : pullback.fst G.hom f y ∈ d.q.left ⁻¹ᵁ
        (E.chart (fun k => j k PUnit.unit) ⊓ E.chart (fun k => j' k PUnit.unit)) := ⟨le j hy.1, le j' hy.2⟩
    have e := congrArg (gm (pullback.fst G.hom f) y _)
      (d.trans (fun k => j k PUnit.unit) (fun k => j' k PUnit.unit) k)
    have e' := (gm_res _ y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_pull _ d.q.left y _ hm _).trans (gm_res (pullback.fst G.hom f ≫ d.q.left) y _ hm _))
      (gm_res _ y _ hm _))))
    refine ((gm_res (𝟙 _) y _ hy _).trans (gm_res_pullU' _ y (le j') hy.2 _)).trans (e'.trans (Eq.symm ?_))
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ?_
      ((gm_res (𝟙 _) y _ hy _).trans (gm_res_pullU' _ y (le j) hy.1 _)))
    refine ((gm_pull (𝟙 _) q.left y _ hy _).trans (gm_res (𝟙 _ ≫ q.left) y _ hy _)).trans ?_
    refine (gm_pull_g (E.O (E.basis k)).L (pullback.fst E.B.hom f) (𝟙 _ ≫ q.left) y (j k) (j' k)
      ((extBC f E).chart_le j k hy.1) ((extBC f E).chart_le j' k hy.2)).trans ?_
    rw [Category.id_comp, hq]
  · have hs := eSec_fst f G
    have h₁ : (eSec ((Over.pullback f).obj G) ≫ pullback.fst G.hom f) y ∈
        d.q.left ⁻¹ᵁ E.chart (fun k => j k PUnit.unit) := le j hy.1
    rw [hs] at h₁
    have h₂ := (rigChart f E.B (E.O (E.basis k)).L).le (fun _ => j k) hy.2
    let f' : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left := f
    have hm : f' y ∈ eSec G ⁻¹ᵁ (d.q.left ⁻¹ᵁ E.chart (fun k => j k PUnit.unit)) ⊓
        ((E.O (E.basis k)).L.pull (eSec E.B)).U (fun _ => j k PUnit.unit) := ⟨h₁, h₂⟩
    have e := congrArg (gm f' y _) (d.unit_norm (fun k => j k PUnit.unit) k)
    have e' := ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_res_pullU f' _ y _ hm _) (gm_res f' y _ hm _))).symm.trans (e.trans (map_one _))
    refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ ?_)).trans (e'.trans (map_one _).symm)
    · refine (gm_res_pullU' _ y _ hy _).trans ((gm_res_pullU _ _ y (le j) hy.1 _).trans ?_)
      rw [hs]
    · exact (gm_res (𝟙 _) y _ hy _).trans
        (gm_res_pullU' f' y ((rigChart f E.B (E.O (E.basis k)).L).le (fun _ => j k)) hy.2 _)
  · have hτ : (eT.hom.left ≫ pullback.fst (splitTorus S E.X).hom f) ≫ (splitTorus S E.X).hom =
        (splitTorus S' E.X).hom ≫ f := by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      exact congrArg (· ≫ f) (Over.w eT.hom)
    refine ⟨pushPt hτ τ, ?_, fun χ z => ?_⟩
    · change (τ.left ≫ eT.hom.left ≫ pullback.fst (splitTorus S E.X).hom f) ≫ d.i.left =
        (τ.left ≫ i.left) ≫ pullback.fst G.hom f
      exact (Category.assoc _ _ _).trans
        ((congrArg (τ.left ≫ ·) hi.symm).trans (Category.assoc _ _ _).symm)
    · have e₂ : charUnit S' E.X χ =
          pullU (eT.hom.left ≫ pullback.fst (splitTorus S E.X).hom f) ⊤ (charUnit S E.X χ) :=
        Units.ext (hT χ).symm
      refine Eq.trans ?_ (congrArg (gm τ.left z ⊤) e₂).symm
      exact (gm_pull τ.left _ z ⊤ trivial _).symm

end GlobalTheory
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isLevelStructure_of_generic_of_fibrewise_indep : Laws → ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (P : PolAV (Sp R)) (P₀ : PolAV (Sp K)) (φ : P₀.A.left ⟶ P.A.left), IsGrpPullback P₀.A P.A (spMap (algebraMap R K)) φ → LBIso P₀.L (P.L.pull φ) → P.g = P₀.g → ∀ (M : ℕ) (ze : Rˣ) (ze₀ : Kˣ), IsUnit (M : R) → algebraMap R K ze = ze₀ → ∀ (lev₀ : Out.Level P₀ M (unitOn ze₀)) (y : Fin (2 * P.g) → (baseOver (Sp R) ⟶ P.A)), (∀ (i₀ : Fin (2 * P₀.g)) (i : Fin (2 * P.g)), (i₀ : ℕ) = i → (lev₀.pt i₀).left ≫ φ = spMap (algebraMap R K) ≫ (y i).left) → (∀ (F : Type) [Field F] [IsAlgClosed F] (s : Spec (CommRingCat.of F) ⟶ Sp R) (c c' : Fin (2 * P.g) → Fin M), linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R)) ≫ y i) (fun i => (c i : ℕ)) = linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R)) ≫ y i) (fun i => (c' i : ℕ)) → c = c') → ∃ lev : Out.Level P M (unitOn ze), lev.pt = y := by
  first | exact @GlobalTheory.level_of_generic_of_indep | exact GlobalTheory.level_of_generic_of_indep | (intros; apply GlobalTheory.level_of_generic_of_indep <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

noncomputable section

namespace GlobalTheory.ThetaReal.NormMul

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

theorem rigT_isGen {ρ : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (k : ℤ) : (rigT A L ρ T k).IsGen := by
  have v : ∀ (y : T.left) (i : Fin 1 → L.ι), y ∈ LB.wchart L (fun _ : Fin 1 => T.hom ≫ eSec A) i →
      gm (𝟙 T.left) y (LB.wchart L (fun _ : Fin 1 => T.hom ≫ eSec A) i) ((rigT A L ρ T k).s i) =
        gm T.hom y (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => i 0)) (ρ.s fun _ => i 0) ^ k :=
    fun y i hi => (map_zpow _ _ _).trans (congrArg (· ^ k) ((gm_res (𝟙 T.left) y (rigT_le A L i) hi _).trans
      (gm_pull (𝟙 T.left) T.hom y _ (rigT_le A L i hi) (ρ.s fun _ => i 0))))
  refine SymLiftOdd.isGen_of_gm fun y i j hi hj => ?_
  have e := gen_trans (L := L) (φ := fun _ : PUnit.{1} => eSec A) (ε := fun _ => 1) hρ T.hom y
    (j := fun _ => i 0) (j' := fun _ => j 0) (rigT_le A L (T := T) i hi) (rigT_le A L (T := T) j hj)
  rw [trF, Fintype.prod_unique, zpow_one] at e
  rw [v y i hi, v y j hj, trF, Fin.prod_univ_one, Category.id_comp, ← mul_zpow]
  exact congrArg (· ^ k) e

theorem ptSec_fst : (ptSecT A (1 : T ⟶ A)).left ≫ (fst T A).left = 𝟙 T.left := by
  rw [← Over.comp_left, ptSecT, lift_fst]; rfl

theorem ptSec_snd : (ptSecT A (1 : T ⟶ A)).left ≫ (snd T A).left = T.hom ≫ eSec A := by
  rw [← Over.comp_left, ptSecT, lift_snd]; rfl

theorem ptSec_snd_pow (m : ℕ) : (ptSecT A (1 : T ⟶ A)).left ≫ (snd T A ^ m).left = T.hom ≫ eSec A := by
  rw [← Over.comp_left, MonObj.comp_pow, ptSecT, lift_snd, one_pow]; rfl

theorem exists_normalised (hL : L.IsLB) {ρ : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (m : ℕ) (a b : ℤ)
    (α₀ : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, b])) (h₀ : α₀.IsGen) :
    ∃ α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, b]), α.IsGen ∧
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ α (ptSecT A 1).left)
        (LB.mulGen L _ _ _ _ (rigT A L ρ T a) (rigT A L ρ T b)) := by
  obtain ⟨α, hα, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (snd T A ^ m).left]) (ε' := ![a, b])
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, ptSec_snd, ptSec_snd_pow]
      rw [← zpow_add, ← zpow_add, ← zpow_add, show -a + -b + (a + b) = 0 by ring, zpow_zero, _root_.mul_one])
    (LB.mulGen L _ _ _ _ α₀ (LB.pullGen L _ _ (LB.mulGen L _ _ _ _
      (LB.invGen L _ _ (LB.pullGen L _ _ α₀ (ptSecT A 1).left))
      (LB.mulGen L _ _ _ _ (rigT A L ρ T a) (rigT A L ρ T b))) (fst T A).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ h₀ (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ h₀ _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (rigT_isGen hρ a) (rigT_isGen hρ b))) _))
  refine ⟨α, hα, corr_of_val hL fun y J hJ => ?_⟩
  rw [val_pull hJ, hv _ _ y J hJ, val_mul hJ, val_pull hJ, Category.assoc, ptSec_fst, Category.comp_id,
    val_mul hJ, val_inv, val_pull hJ, mul_inv_cancel_left]

end GlobalTheory.ThetaReal.NormMul

namespace GlobalTheory.ThetaReal

theorem exists_normalised_mulPull : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))), rig.IsGen → ∀ (m N : ℕ), N = m ^ 2 → ∀ T : Over S, ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ m).left] ![(N : ℤ), -1]), α.IsGen ∧ LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ α (ptSecT P.A 1).left) (LB.mulGen P.L _ _ _ _ (rigT P.A P.L rig T N) (rigT P.A P.L rig T (-1))) := by
  intro hLaw S _ P rig hrig m N hN T
  subst hN
  have H := hLaw.mulPull _ P m
  rw [← Nat.cast_pow] at H
  obtain ⟨α₀, hα₀⟩ := H
  obtain ⟨α₁, hα₁, -⟩ := VVRank.exists_gen_pullTo
    (φ' := ![(snd T P.A).left, (snd T P.A ^ m).left]) α₀ hα₀ (snd T P.A).left (fun k => by
      fin_cases k
      · exact Category.comp_id _
      · change (snd T P.A).left ≫ (mulA P.A m).left = (snd T P.A ^ m).left
        rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id])
  exact NormMul.exists_normalised P.isLB hrig m _ _ α₁ hα₁

end GlobalTheory.ThetaReal

end
end
