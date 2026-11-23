module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechTripleRestrictCompositeInjectiveSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle601
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle292
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle452
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCocycleCoboundaryCommaLocalBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle155
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle157
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle290
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.IwasawaUnitaryAdelic.IUAIwa
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.Bundle002
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.Bundle003
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinOfPI
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.GoodPI
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.Transfer
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Topology.LocallyConstant.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KummerCocycleNormCriterion
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import ReciprocityTheory.NeutralLocalFields.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle193
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle026
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsOpenKerFinIdele
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Axis.PullO

theorem restrict_pull1_bijective_of_basis {R' : Type} [CommRing R'] {X' : Scheme.{0}} (s' : X' ⟶ Sp R')
    {C' : Type} [Category.{0} C'] [Quiver.IsThin C'] (G : C' ⥤ AffOp X')
    (hcov : ∀ T : AffOp X', ∃ (n : ℕ) (b : Fin n → (OAff s').obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X') (u : T ⟶ S),
        IsUnit (mp (OAff s') u (b i)) →
          ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u)
    (hdir : ∀ (t₁ t₂ : C') (S : AffOp X'), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) →
      ∃ (n : ℕ) (b : Fin n → (OAff s').obj S), Ideal.span (Set.range b) = ⊤ ∧
        ∀ (i : Fin n) (S' : AffOp X') (u : S ⟶ S'), IsUnit (mp (OAff s') u (b i)) →
          ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) :
    Function.Bijective (CoefMap.restrict (OAff s') G).pull1 := by
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s'
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s') G H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s') G H hcov hdir
  have hv := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (OAff s') G H hcov hdir
  exact ⟨_root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ hs hg,
    _root_.GlobalTheory.CatCoh.pull1_restrict_surjective_of_comma _ _ hs hg hv⟩

section Triple

variable {R'' : Type} [CommRing R''] {X X' X'' : Scheme.{0}}
variable (ψ : X'' ⟶ X') (φ : X' ⟶ X)

theorem triple_restriction_pair_restriction (s'' : X'' ⟶ Sp R'') (c : HO1 s'') :
    (cechTripleRestrictComposite ψ φ s'').pull1 ((pairRes (ψ ≫ φ) s'').pull1 c) =
      (CoefMap.restrict (OAff s'') (cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ))).pull1 c := by
  rw [← GlobalTheory.CatCoh.CoefMap.pullCohomologyOne_comp]
  refine GlobalTheory.CatCoh.CoefMap.pullCohomologyOne_eq_of_natTrans _ _ { app := fun _ => 𝟙 _, naturality := fun _ _ _ => Quiver.Hom.unop_inj (Subsingleton.elim _ _) } ?_ c
  intro T b
  rw [GlobalTheory.CatCoh.mp_id]

theorem triple_restriction_injective (s'' : X'' ⟶ Sp R'') : Function.Injective (cechTripleRestrictComposite ψ φ s'').pull1 := by
  intro x y hxy
  obtain ⟨x', rfl⟩ := (pairRes_bijective (ψ ≫ φ) s'').1.2 x
  obtain ⟨y', rfl⟩ := (pairRes_bijective (ψ ≫ φ) s'').1.2 y
  rw [triple_restriction_pair_restriction, triple_restriction_pair_restriction] at hxy
  rw [(restrict_pull1_bijective_of_basis s'' (cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ))
    (triple_cover_affine ψ φ s'') (exists_triple_below_two ψ φ s'')).1 hxy]

end Triple

section Comp

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {X X' X'' : Scheme.{0}}
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R →+* R'} {τ : R' →+* R''}
  {φ : X' ⟶ X} {ψ : X'' ⟶ X'}

theorem tri_pull_pull (h : φ ≫ s = s' ≫ spMap σ) (h' : ψ ≫ s' = s'' ≫ spMap τ)
    (h'' : (ψ ≫ φ) ≫ s = s'' ≫ spMap (τ.comp σ)) (a : HO1 s) :
    (cechTripleRestrictComposite ψ φ s'').pull1 ((pairPull h'').pull1 a) =
      (cechTriplePullbackSecond h').pull1 ((pairPull h).pull1 a) := by
  rw [← GlobalTheory.CatCoh.CoefMap.pullCohomologyOne_comp, ← GlobalTheory.CatCoh.CoefMap.pullCohomologyOne_comp]
  refine GlobalTheory.CatCoh.CoefMap.pullCohomologyOne_eq_of_natTrans ((pairPull h'').comp (cechTripleRestrictComposite ψ φ s''))
    ((pairPull h).comp (cechTriplePullbackSecond h')) { app := fun _ => 𝟙 _, naturality := fun _ _ _ => Quiver.Hom.unop_inj (Subsingleton.elim _ _) } ?_ a
  intro T b
  erw [GlobalTheory.CatCoh.mp_id]
  show (CommRingCat.Hom.hom (Scheme.Hom.appLE φ _ _ _ ≫ Scheme.Hom.appLE ψ _ _ _)) b =
    CommRingCat.Hom.hom (Scheme.Hom.appLE (ψ ≫ φ) _ _ _) b
  exact congrArg (fun k => CommRingCat.Hom.hom k b) (Scheme.Hom.appLE_comp_appLE ψ φ _ _ _ _ _)

theorem tri_res_pull (h' : ψ ≫ s' = s'' ≫ spMap τ) (a : HO1 s') :
    (cechTriplePullbackSecond (φ := φ) h').pull1 ((pairRes φ s').pull1 a) =
      (cechTripleRestrictFirst ψ φ s'').pull1 ((pairPull h').pull1 a) := by
  rw [← GlobalTheory.CatCoh.CoefMap.pullCohomologyOne_comp, ← GlobalTheory.CatCoh.CoefMap.pullCohomologyOne_comp]
  refine GlobalTheory.CatCoh.CoefMap.pullCohomologyOne_eq_of_natTrans _ _ { app := fun _ => 𝟙 _, naturality := fun _ _ _ => Quiver.Hom.unop_inj (Subsingleton.elim _ _) } ?_ a
  intro T b
  rw [GlobalTheory.CatCoh.mp_id]

theorem tri_res_res (a : HO1 s'') :
    (cechTripleRestrictFirst ψ φ s'').pull1 ((pairRes ψ s'').pull1 a) =
      (cechTripleRestrictComposite ψ φ s'').pull1 ((pairRes (ψ ≫ φ) s'').pull1 a) := by
  rw [← GlobalTheory.CatCoh.CoefMap.pullCohomologyOne_comp, ← GlobalTheory.CatCoh.CoefMap.pullCohomologyOne_comp]
  refine GlobalTheory.CatCoh.CoefMap.pullCohomologyOne_eq_of_natTrans _ _ { app := fun _ => 𝟙 _, naturality := fun _ _ _ => Quiver.Hom.unop_inj (Subsingleton.elim _ _) } ?_ a
  intro T b
  rw [GlobalTheory.CatCoh.mp_id]

theorem isPullO_comp (h : φ ≫ s = s' ≫ spMap σ) (h' : ψ ≫ s' = s'' ≫ spMap τ)
    (h'' : (ψ ≫ φ) ≫ s = s'' ≫ spMap (τ.comp σ)) (a : HO1 s) (b : HO1 s') (c : HO1 s'') :
    IsPullO h a b → IsPullO h' b c → IsPullO h'' a c := by
  intro hab hbc
  apply triple_restriction_injective ψ φ s''
  unfold IsPullO at hab hbc
  rw [tri_pull_pull h h' h'' a, hab, tri_res_pull h' b, hbc, tri_res_res (φ := φ) c]

end Comp

theorem isPullO_wOver_comp : ∀ (R : Type) [CommRing R] (X Y Z : Over (Sp R)) (f : X ⟶ Y) (g : Y ⟶ Z)
    (a : HO1 Z.hom) (b : HO1 Y.hom) (c : HO1 X.hom), IsPullO (wOver g) a b → IsPullO (wOver f) b c →
    IsPullO (wOver (f ≫ g)) a c := by
  intro R _ X Y Z f g a b c hab hbc
  exact isPullO_comp (wOver g) (wOver f) (wOver (f ≫ g)) a b c hab hbc

end GlobalTheory.CompanionTheory.Axis.PullO
end
end

section

open MeasureTheory Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.AdmIwa

open CompanionTheory.D.gk.admitted

variable {n : ℕ}

def Gp (G : Set (Matrix (Fin n) (Fin n) ℂ)) : Type := {g : Matrix (Fin n) (Fin n) ℂ // g ∈ G}

variable {G : Set (Matrix (Fin n) (Fin n) ℂ)}

instance : TopologicalSpace (Gp G) := instTopologicalSpaceSubtype
instance : T2Space (Gp G) := inferInstanceAs (T2Space {g : Matrix (Fin n) (Fin n) ℂ // g ∈ G})
instance : SecondCountableTopology (Gp G) :=
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  inferInstanceAs (SecondCountableTopology {g : Matrix (Fin n) (Fin n) ℂ // g ∈ G})

def Gp.m (g : Gp G) : Matrix (Fin n) (Fin n) ℂ := g.1

theorem Gp.ext {a b : Gp G} (h : a.m = b.m) : a = b := Subtype.ext h

theorem continuous_m : Continuous (Gp.m : Gp G → Matrix (Fin n) (Fin n) ℂ) := continuous_subtype_val

theorem isEmbedding_m : Topology.IsEmbedding (Gp.m : Gp G → Matrix (Fin n) (Fin n) ℂ) :=
  Topology.IsEmbedding.subtypeVal

variable [hG : Fact (GlobalTheory.LinRed.IsLinRed G)]

instance : Group (Gp G) where
  mul a b := ⟨a.1 * b.1, hG.out.mul_mem _ a.2 _ b.2⟩
  one := ⟨1, hG.out.one_mem⟩
  inv a := ⟨a.1⁻¹, hG.out.inv_mem _ a.2⟩
  mul_assoc a b c := Subtype.ext (Matrix.mul_assoc _ _ _)
  one_mul a := Subtype.ext (Matrix.one_mul _)
  mul_one a := Subtype.ext (Matrix.mul_one _)
  inv_mul_cancel a := Subtype.ext
    (Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (hG.out.isUnit _ a.2)))

instance : IsTopologicalGroup (Gp G) where
  continuous_mul := by
    refine isEmbedding_m.continuous_iff.2 ?_
    exact (continuous_m.comp continuous_fst).matrix_mul (continuous_m.comp continuous_snd)
  continuous_inv := by
    refine isEmbedding_m.continuous_iff.2 ?_
    have h : ((Gp.m : Gp G → _) ∘ fun a : Gp G => a⁻¹) =
        fun a : Gp G => (a.m.det)⁻¹ • a.m.adjugate := by
      funext a
      show (a.m)⁻¹ = _
      rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [h]
    refine Continuous.smul (Continuous.inv₀ continuous_m.matrix_det fun a => ?_)
      continuous_m.matrix_adjugate
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (hG.out.isUnit _ a.2)).ne_zero

def Kc (G : Set (Matrix (Fin n) (Fin n) ℂ)) [hG : Fact (GlobalTheory.LinRed.IsLinRed G)] : Subgroup (Gp G) where
  carrier := {g | g.m ∈ Matrix.unitaryGroup (Fin n) ℂ}
  one_mem' := Submonoid.one_mem (Matrix.unitaryGroup (Fin n) ℂ)
  mul_mem' ha hb := Submonoid.mul_mem (Matrix.unitaryGroup (Fin n) ℂ) ha hb
  inv_mem' {a} ha := by
    show (a.m)⁻¹ ∈ Matrix.unitaryGroup (Fin n) ℂ
    rw [Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 ha)]
    exact Unitary.star_mem ha

theorem mem_Kc {k : Gp G} : k ∈ Kc G ↔ k.m ∈ Matrix.unitaryGroup (Fin n) ℂ := Iff.rfl

theorem isCompact_maxCpt : IsCompact (GlobalTheory.LinRed.maxCpt G) := by
  have hbd : GlobalTheory.LinRed.maxCpt G ⊆ Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n =>
      Metric.closedBall (0 : ℂ) 1 := by
    intro g hg i _ j _
    simpa using entry_norm_bound_of_unitary hg.2 i j
  have hcmp : IsCompact (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n =>
      Metric.closedBall (0 : ℂ) 1 : Set (Fin n → Fin n → ℂ)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine IsCompact.of_isClosed_subset hcmp ?_ hbd
  refine isClosed_of_closure_subset fun g hg => ?_
  have hU : IsClosed (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) := by
    have : (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) = {m | mᴴ * m = 1} := by
      ext m
      exact Matrix.mem_unitaryGroup_iff'
    rw [this]
    exact isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) continuous_const
  have hgU : g ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    hU.closure_subset_iff.2 Set.inter_subset_right (closure_mono (le_refl _) hg)
  have hgu : IsUnit g := IsUnit.of_mul_eq_one _ (Matrix.mem_unitaryGroup_iff.1 hgU)
  exact ⟨hG.out.closed g hgu (closure_mono Set.inter_subset_left hg), hgU⟩

instance : CompactSpace (Kc G) := by
  refine isCompact_univ_iff.1 ?_
  have he : Topology.IsEmbedding fun k : Kc G => (k.1).m :=
    isEmbedding_m.comp Topology.IsEmbedding.subtypeVal
  rw [he.isCompact_iff, Set.image_univ]
  have : Set.range (fun k : Kc G => (k.1).m) = GlobalTheory.LinRed.maxCpt G := by
    ext m
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k.1.2, mem_Kc.1 k.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨⟨m, h1⟩, mem_Kc.2 h2⟩, rfl⟩
  rw [this]
  exact isCompact_maxCpt

instance : MeasurableSpace (Kc G) := borel _
instance : BorelSpace (Kc G) := ⟨rfl⟩

def homG {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : Formalism.MainNotions.S.IsURepOn G σ) : Gp G →* (H →L[ℂ] H) where
  toFun g := σ g.m
  map_one' := hσ.1.1
  map_mul' a b := hσ.1.2 _ a.2 _ b.2

def stdG (G : Set (Matrix (Fin n) (Fin n) ℂ)) [hG : Fact (GlobalTheory.LinRed.IsLinRed G)]
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    Gp G →* Matrix (Fin n) (Fin n) ℂ where
  toFun g := Uᴴ * g.m * U
  map_one' := by
    have h1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
    show Uᴴ * 1 * U = 1
    rw [Matrix.mul_one, h1]
  map_mul' a b := by
    have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU
    show Uᴴ * (a.m * b.m) * U = _
    calc Uᴴ * (a.m * b.m) * U = Uᴴ * a.m * (U * Uᴴ) * b.m * U := by
          rw [h1]; simp only [Matrix.mul_assoc, Matrix.one_mul]
      _ = _ := by simp only [Matrix.mul_assoc]


omit hG in
theorem admissible_of_polynomial_identity (h1 : FinOfPI) (h2 : GoodPI) (h3 : Transfer) (h4 : ExistsAvg)
    (hLR : GlobalTheory.LinRed.IsLinRed G) (h5 : PositivityTheory.Tls2.Iua.IwaOn G) : PositivityTheory.Tls2.Iua.AdmG G := by
  haveI : Fact (GlobalTheory.LinRed.IsLinRed G) := ⟨hLR⟩
  intro H _ _ _ σ hσ hirr S _ hS v hv
  obtain ⟨U, hU, hiwa⟩ := h5
  let μ : Measure (Kc G) := (Measure.haar : Measure (Kc G)).inv
  have hμ : IsFiniteMeasure μ := CompactSpace.isFiniteMeasure
  have hsc : SecondCountableTopology (Kc G) := TopologicalSpace.Subtype.secondCountableTopology _
  have hiso : ∀ g u, ‖homG hσ g u‖ = ‖u‖ := fun g u => hσ.2.1 _ g.2 u
  have hc : ∀ u, Continuous fun g => homG hσ g u := fun u =>
    (hσ.2.2 u).comp_continuous continuous_m fun g => g.2
  obtain ⟨e, E, he, hfin, hE, hEv⟩ := h4 (Kc G) μ H ((homG hσ).comp (Kc G).subtype) (fun k u => hiso k u)
    (fun u => (hc u).comp continuous_subtype_val) S (fun k u hu => hS _ ⟨k.1.2, mem_Kc.1 k.2⟩ u hu) v hv
  let st : Gp G → Gp G := fun g => ⟨g.mᴴ, hLR.star_mem _ g.2⟩
  let Tr : Set (Gp G) := {s | (stdG G hU s).BlockTriangular id}
  have hgood : IsGood st Tr (stdG G hU) := by
    refine ⟨(continuous_const.matrix_mul continuous_m).matrix_mul continuous_const, fun g => ?_,
      Fin.val, Fin.val_injective, fun s hs i j hij => hs hij⟩
    show Uᴴ * g.mᴴ * U = (Uᴴ * g.m * U)ᴴ
    simp [Matrix.mul_assoc]
  have hinj : Function.Injective (stdG G hU) := by
    intro a b hab
    have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU
    have key : ∀ g : Gp G, U * stdG G hU g * Uᴴ = g.m := fun g => by
      show U * (Uᴴ * g.m * U) * Uᴴ = _
      calc U * (Uᴴ * g.m * U) * Uᴴ = (U * Uᴴ) * g.m * (U * Uᴴ) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [h1, Matrix.one_mul, Matrix.mul_one]
    exact Gp.ext ((key a).symm.trans (hab ▸ key b))
  have hKS : ∀ g : Gp G, ∃ k ∈ Kc G, ∃ s ∈ Tr, g = k * s := by
    intro g
    obtain ⟨k, hk, s, hs, hg, ht⟩ := hiwa g.m g.2
    exact ⟨⟨k, hk.1⟩, mem_Kc.2 hk.2, ⟨s, hs⟩, ht, Gp.ext hg⟩
  have hPI : ∀ g : Fin (Module.finrank ℂ S ^ 2 + 1) → Gp G, stdPoly E (fun i => homG hσ (g i)) = 0 := fun g =>
    h3 (Gp G) (Kc G) μ st Tr (Fin n) (stdG G hU) hgood hinj e he _ g
      (fun ι _ _ ρ hρ E' hE' => h2 (Gp G) (Kc G) μ st Tr hKS e _ _ he hfin (Nat.lt_succ_self _) ι ρ hρ E' hE' g)
      H (homG hσ) hc E hE
  obtain ⟨hfd, hrk⟩ := h1 (Gp G) H (homG hσ) hiso (fun S' hcl hS' => hirr S' hcl fun g hg u hu =>
    hS' ⟨g, hg⟩ u hu) E _ hPI
  refine ⟨_, hfd, hrk, ⟨v, hEv⟩, ?_⟩
  rintro T hT _ ⟨u, rfl⟩
  refine ⟨T u, ?_⟩
  show E (T u) = T (E u)
  rw [hE, hE, ← T.integral_comp_comm]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    show e k • σ k.1.1 (T u) = T (e k • σ k.1.1 u)
    rw [map_smul, hT _ ⟨k.1.2, mem_Kc.1 k.2⟩ u]
  · exact (he.smul ((hc u).comp continuous_subtype_val)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem RamifiedPrimeLengthBound {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hLR : GlobalTheory.LinRed.IsLinRed G)
    (h : PositivityTheory.Tls2.Iua.IwaOn G) : PositivityTheory.Tls2.Iua.AdmG G :=
  admissible_of_polynomial_identity finite_rank_of_irreducible_unitary (goodPI_of small_irreducible_representation) transfer_holds exists_averaging_operator hLR h

end GlobalTheory.CompanionTheory.AdmIwa
end
end

section


theorem _root_.GlobalTheory.T.kummer_cocycle_norm_criterion : ∀ {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (N : ℕ), 0 < N → ∀ ζ : Ω, IsPrimitiveRoot ζ N → ∀ c0 : (Ω ≃ₐ[K] Ω) → ZMod N, (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ ^ (c0 g).val) → ∀ ψ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod N), IsOpen (ψ.ker : Set (Ω ≃ₐ[K] Ω)) → ∀ U : Kˣ, (∃ y : IntermediateField.fixedField ψ.ker, Algebra.norm K y = (U : K)) → ∀ (T : Ω) (κ : (Ω ≃ₐ[K] Ω) → ZMod N), T ^ N = algebraMap K Ω (U : K) → (∀ g : Ω ≃ₐ[K] Ω, g T = ζ ^ (κ g).val * T) → ∃ c : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant c ∧ ∀ g h : Ω ≃ₐ[K] Ω, c0 g * c h - c (g * h) + c g = κ g * Multiplicative.toAdd (ψ h) := by
  first | exact @GlobalTheory.CompanionTheory.KummerCup.kummerCup_eq_coboundary | exact GlobalTheory.CompanionTheory.KummerCup.kummerCup_eq_coboundary | (intros; apply GlobalTheory.CompanionTheory.KummerCup.kummerCup_eq_coboundary <;> assumption)
end

section

open NumberField
open scoped nonZeroDivisors
open scoped GlobalTheory.Idele

theorem _root_.GlobalTheory.T.artin_map_abelian_unique : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (Art Art' : Neutral.B1.IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K), Neutral.B1.IsGlobalArtinMap K Art → Neutral.B1.IsGlobalArtinMap K Art' → ∀ (L : IntermediateField K (AlgebraicClosure K)) (h : Neutral.B1.IsFiniteAbelian K L) (c : Neutral.B1.IdeleClassGroup K), Neutral.B1.abRestrict K L h (Art c) = Neutral.B1.abRestrict K L h (Art' c) := by
  first | exact @GlobalTheory.CompanionTheory.ArtinUniq.abRestrict_eq | exact GlobalTheory.CompanionTheory.ArtinUniq.abRestrict_eq | (intros; apply GlobalTheory.CompanionTheory.ArtinUniq.abRestrict_eq <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Topology Formalism.L2.Host GlobalTheory.CuspRep Neutral.B1

namespace GlobalTheory.CompanionTheory.HeckeFin

variable (L : Type) [Field L] [NumberField L]

def infIdele : (InfiniteAdeleRing L)ˣ →* Ideles L :=
  Units.map (MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))

theorem continuous_infIdele : Continuous (infIdele L) :=
  Continuous.units_map _ (continuous_id.prodMk continuous_const)

theorem isOpenEmbedding_val :
    IsOpenEmbedding (Units.val : (InfiniteAdeleRing L)ˣ → InfiniteAdeleRing L) :=
  Units.isOpenEmbedding_val (R := ∀ v : InfinitePlace L, v.Completion)

theorem denseRange_units :
    DenseRange (Units.map (algebraMap L (InfiniteAdeleRing L)).toMonoidHom : Lˣ → (InfiniteAdeleRing L)ˣ) := by
  refine dense_iff_inter_open.2 fun U hU ⟨u, hu⟩ => ?_
  obtain ⟨l, w, hw, hl⟩ := (InfiniteAdeleRing.denseRange_algebraMap L).exists_mem_open
    ((isOpenEmbedding_val L).isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [map_zero] at hl
    exact w.ne_zero hl
  exact ⟨w, hw, Units.mk0 l hl0, Units.ext hl.symm⟩

variable {L}

end GlobalTheory.CompanionTheory.HeckeFin
end
end
