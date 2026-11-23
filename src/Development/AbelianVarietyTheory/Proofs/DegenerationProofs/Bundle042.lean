module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle037
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueModelHasJacobianOrder
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueRigidifiedGeneratorExtendNormal
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.NumberTheory.Padics.Complex
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle038
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableReductionPlusSplit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001

@[expose] public section

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
theorem _root_.GlobalTheory.T.degenerationWeilPairing_properties : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (k : ℕ) (p p' p'' : N.QT k), N.wp (p * p') p'' = N.wp p p'' * N.wp p' p'' ∧ N.wp p p = 1 ∧ N.wp p p' * N.wp p' p = 1 ∧ N.wp p p' ^ k = 1 ∧ (N.QEq p p' → N.wp p p'' = N.wp p' p'') ∧ (p.1.1 = 1 → p.1.2.b = 1 → N.wp p p' = p.1.2.s p'.1.1.toAdd) ∧ (p.1.1 = 1 → p'.1.1 = 1 → N.wp p p' = N.weil k p.1.2.b p'.1.2.b) := by
  first | exact @GlobalTheory.Ex.WpPairing.wp_pairing | exact GlobalTheory.Ex.WpPairing.wp_pairing | (intros; apply GlobalTheory.Ex.WpPairing.wp_pairing <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.Ord
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GlobalTheory.SS.Ord

theorem model_smoothOfRelativeDimension {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {A : Over (Sp K)} {d : ℕ} (hA : SmoothOfRelativeDimension d A.hom) (M : Model R A) :
    SmoothOfRelativeDimension d M.Y.hom := by
  have := M.smooth
  choose n W hW hd using H1.exists_dim M.Y.hom
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension d) := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension d) W
    (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩) fun x => ?_
  have hne : ∃ y : A.left, M.j y ∈ W x := by
    by_contra hc
    have e : M.j ⁻¹ᵁ W x = ⊥ := le_bot_iff.1 fun y hy => (hc ⟨y, hy⟩).elim
    have h1 : Subsingleton Γ(A.left, M.j ⁻¹ᵁ W x) := by rw [e]; infer_instance
    have h2 : Subsingleton Γ(M.Y.left, W x) := (j_app_injective M (W x)).subsingleton
    have : Nonempty (W x) := ⟨⟨x, hW x⟩⟩
    exact not_subsingleton _ h2
  obtain ⟨y, hy⟩ := hne
  rw [← H1.dim_base (isPullback_j M) (hd x) hA y hy]
  exact hd x

theorem exists_etale_coord : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)) (I : Type) [Fintype I], SmoothOfRelativeDimension (Fintype.card I) A.hom → ∀ (M : Model R A) (x : M.Y.left) (O : M.Y.left.Opens), x ∈ O → ∃ (U : M.Y.left.Opens) (t : I → Γ(M.Y.left, U)), IsAffineOpen U ∧ x ∈ U ∧ U ≤ O ∧ (MvPolynomial.eval₂Hom (cst M U) t).Etale := by
  intro R K _ _ _ _ _ _ A I _ hA M x O hx
  have hM := model_smoothOfRelativeDimension hA M
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWO⟩ := M.Y.left.isBasis_affineOpens.exists_subset_of_mem_open hx O.isOpen
  have hW : IsAffineOpen W := hW
  have h0 := HasRingHomProperty.appLE (@SmoothOfRelativeDimension (Fintype.card I)) M.Y.hom hM
    ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top
  obtain ⟨s, hs, h'⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h0
  have hcov := hW.self_le_iSup_basicOpen_iff.2 hs hxW
  obtain ⟨⟨g, hg⟩, hxg⟩ := TopologicalSpace.Opens.mem_iSup.1 hcov
  have hl := hW.isLocalization_basicOpen g
  have h1 := h' g hg Γ(M.Y.left, M.Y.left.basicOpen g)
  have h2 : (cst M (M.Y.left.basicOpen g)).IsStandardSmoothOfRelativeDimension (Fintype.card I) := by
    have h3 := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv h1
    have e : cst M (M.Y.left.basicOpen g) = (rs _ (M.Y.left.basicOpen_le g)).comp (cst M W) :=
      RingHom.ext fun r => (rs_cst M (M.Y.left.basicOpen_le g) r).symm
    rw [e]
    exact h3
  obtain ⟨φ, hC, hφ⟩ := h2.exists_etale_mvPolynomial
  let e := Fintype.equivFin I
  refine ⟨M.Y.left.basicOpen g, fun i => φ (MvPolynomial.X (e i)), hW.basicOpen g, hxg,
    (M.Y.left.basicOpen_le g).trans hWO, ?_⟩
  have h4 := RingHom.Etale.respectsIso.2 φ (MvPolynomial.renameEquiv R e).toRingEquiv hφ
  convert h4 using 1
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · simp [← hC]
  · simp

end GlobalTheory.SS.Ord
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.IsoExtend

variable {X Y Y' : Scheme.{0}}

theorem exists_gen_chartPull {A' : LB Y'} {A : LB Y} {h : Y' ⟶ Y} (a : ChartPull A' A h)
    (H : ∃ t : LB.Gen A, t.IsGen) : ∃ t : LB.Gen A', t.IsGen := by
  obtain ⟨w, hw⟩ := H
  refine ⟨⟨fun i => res (a.le i) (pullU h _ (w.s (a.idx i)))⟩, fun i j => unit_ext fun y hy => ?_⟩
  have val : ∀ i, y ∈ A'.U i → gm (𝟙 Y') y _ (res (a.le i) (pullU h _ (w.s (a.idx i)))) =
      gm h y (A.U (a.idx i)) (w.s (a.idx i)) := fun i hi =>
    (gm_res (𝟙 Y') y (a.le i) hi _).trans ((gm_pull (𝟙 Y') h y _ (a.le i hi) _).trans (by rw [Category.id_comp]))
  have hm : h y ∈ A.U (a.idx i) ⊓ A.U (a.idx j) := ⟨a.le i hy.1, a.le j hy.2⟩
  have e := congrArg (gm h y (A.U (a.idx i) ⊓ A.U (a.idx j))) (hw (a.idx i) (a.idx j))
  have e' := (gm_res h y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    rfl (gm_res h y _ hm _))))
  refine ((gm_res (𝟙 Y') y _ hy _).trans (val i hy.1)).trans (e'.trans (Eq.symm ?_))
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (a.g y i j hy.1 hy.2)
    ((gm_res (𝟙 Y') y _ hy _).trans (val j hy.2)))

theorem gm_div_pull (L M : LB X) (f : Y ⟶ X) (y : Y) (J J' : PUnit → M.ι × L.ι) (p q : (PUnit → M.ι) × (PUnit → L.ι))
    (ep : J PUnit.unit = (p.1 PUnit.unit, p.2 PUnit.unit)) (eq : J' PUnit.unit = (q.1 PUnit.unit, q.2 PUnit.unit))
    (hJ : y ∈ ((LB.div M L).pull f).U J) (hJ' : y ∈ ((LB.div M L).pull f).U J')
    (hp : y ∈ (M.pull f).U p.1 ⊓ (L.pull f).U p.2) (hq : y ∈ (M.pull f).U q.1 ⊓ (L.pull f).U q.2) :
    gm (𝟙 Y) y (((LB.div M L).pull f).U J ⊓ ((LB.div M L).pull f).U J') (((LB.div M L).pull f).g J J') =
      gm (𝟙 Y) y ((LB.div (M.pull f) (L.pull f)).U p ⊓ (LB.div (M.pull f) (L.pull f)).U q)
        ((LB.div (M.pull f) (L.pull f)).g p q) := by
  refine (gm_pull_g (LB.div M L) f (𝟙 Y) y J J' hJ hJ').trans ?_
  rw [ep, eq]
  refine (gm_div L M (𝟙 Y ≫ f) y (p.1 PUnit.unit, p.2 PUnit.unit) (q.1 PUnit.unit, q.2 PUnit.unit)
    ⟨⟨mem_pull.1 hp.1, mem_pull.1 hp.2⟩, mem_pull.1 hq.1, mem_pull.1 hq.2⟩).trans (Eq.symm ?_)
  refine (gm_div (L.pull f) (M.pull f) (𝟙 Y) y p q ⟨hp, hq⟩).trans ?_
  exact congrArg₂ (· * ·) (gm_pull_g M f (𝟙 Y) y p.1 q.1 hp.1 hq.1)
    (congrArg (·⁻¹) (gm_pull_g L f (𝟙 Y) y p.2 q.2 hp.2 hq.2))

def chartPullDiv (L M : LB X) (f : Y ⟶ X) :
    ChartPull ((LB.div M L).pull f) (LB.div (M.pull f) (L.pull f)) (𝟙 Y) :=
  have le : ∀ (J : PUnit → M.ι × L.ι) (y : Y), y ∈ ((LB.div M L).pull f).U J →
      y ∈ (M.pull f).U (fun _ => (J PUnit.unit).1) ⊓ (L.pull f).U (fun _ => (J PUnit.unit).2) := fun J y hy =>
    have h : f y ∈ M.U (J PUnit.unit).1 ⊓ L.U (J PUnit.unit).2 := (mem_pull (L := LB.div M L) (J := J)).1 hy
    ⟨mem_pull.2 h.1, mem_pull.2 h.2⟩
  { idx := fun J => (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
    le := le
    g := fun y J J' hJ hJ' => gm_div_pull L M f y J J' (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
      (fun _ => (J' PUnit.unit).1, fun _ => (J' PUnit.unit).2) rfl rfl hJ hJ' (le J y hJ) (le J' y hJ') }

def chartDivPull (L M : LB X) (f : Y ⟶ X) :
    ChartPull (LB.div (M.pull f) (L.pull f)) ((LB.div M L).pull f) (𝟙 Y) :=
  have le : ∀ (p : (PUnit → M.ι) × (PUnit → L.ι)) (y : Y), y ∈ (M.pull f).U p.1 ⊓ (L.pull f).U p.2 →
      y ∈ ((LB.div M L).pull f).U (fun _ => (p.1 PUnit.unit, p.2 PUnit.unit)) := fun p y hy =>
    (mem_pull (L := LB.div M L) (J := fun _ => (p.1 PUnit.unit, p.2 PUnit.unit))).2
      ⟨mem_pull.1 hy.1, mem_pull.1 hy.2⟩
  { idx := fun p _ => (p.1 PUnit.unit, p.2 PUnit.unit)
    le := le
    g := fun y p q hp hq => (gm_div_pull L M f y (fun _ => (p.1 PUnit.unit, p.2 PUnit.unit))
      (fun _ => (q.1 PUnit.unit, q.2 PUnit.unit)) p q rfl rfl (le p y hp) (le q y hq) hp hq).symm }

theorem lbIso_pull_iff_gen (L M : LB X) (f : Y ⟶ X) :
    LBIso (L.pull f) (M.pull f) ↔ ∃ t : LB.Gen ((LB.div M L).pull f), t.IsGen :=
  ⟨exists_gen_chartPull (chartPullDiv L M f), exists_gen_chartPull (chartDivPull L M f)⟩

theorem exists_gen_of_chart {D : LB X} (hD : D.IsLB) (f : Y ⟶ X) (i : D.ι) (hf : ∀ y, f y ∈ D.U i) :
    ∃ t : LB.Gen (D.pull f), t.IsGen := by
  have le : ∀ J : PUnit → D.ι, (D.pull f).U J ≤ f ⁻¹ᵁ (D.U (J PUnit.unit) ⊓ D.U i) :=
    fun J y hy => ⟨mem_pull.1 hy, hf y⟩
  refine ⟨⟨fun J => res (le J) (pullU f _ (D.g (J PUnit.unit) i))⟩, fun J J' => unit_ext fun y hy => ?_⟩
  have val : ∀ J, y ∈ (D.pull f).U J → gm (𝟙 Y) y _ (res (le J) (pullU f _ (D.g (J PUnit.unit) i))) =
      gm (𝟙 Y ≫ f) y _ (D.g (J PUnit.unit) i) := fun J hJ =>
    (gm_res (𝟙 Y) y (le J) hJ _).trans (gm_pull (𝟙 Y) f y _ (le J hJ) _)
  refine ((gm_res (𝟙 Y) y _ hy _).trans (val J hy.1)).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_pull_g D f (𝟙 Y) y J J' hy.1 hy.2)
    ((gm_res (𝟙 Y) y _ hy _).trans (val J' hy.2)))).trans ?_
  exact gm_cocycle hD (𝟙 Y ≫ f) y (mem_pull.1 hy.1) (mem_pull.1 hy.2) (hf y)

theorem exists_gen_of_diff {D : LB X} (hD : D.IsLB) (σ : X ⟶ X)
    (c : LB.Gen (LB.LinComb D ![𝟙 X, σ] ![1, -1])) (hc : c.IsGen) (r : Y ⟶ X) {B : Scheme.{0}} (q : Y ⟶ B)
    (τ : B ⟶ X) (hr : r ≫ σ = q ≫ τ) (H : ∃ t : LB.Gen (D.pull τ), t.IsGen) :
    ∃ t : LB.Gen (D.pull r), t.IsGen := by
  obtain ⟨t, ht⟩ := H
  obtain ⟨u, hu, -⟩ := exists_gen hD (φ' := fun _ : PUnit => r) (ε' := fun _ => 1) (by
      intro U _ h
      simp [Fintype.prod_sum_type, Fin.prod_univ_two, hr])
    (LB.mulGen D _ _ _ _ (LB.pullGen D _ _ c r) (LB.pullGen D _ _ t q))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ c hc r) (DVR.pullGen_isGen _ _ _ t ht q))
  exact ⟨u, hu⟩

theorem exists_gen_diff (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S] (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S)
    (U H HU : Scheme.{0}) [Nonempty U] (j : U ⟶ S) [IsOpenImmersion j] (p : H ⟶ S) (e : S ⟶ H) (jH : HU ⟶ H)
    (pU : HU ⟶ U) (hp : Smooth p) (hg : GeometricallyIntegral p) (he : e ≫ p = 𝟙 _) (sq : IsPullback jH pU p j)
    {D : LB H} (hD : D.IsLB) (H₀ : ∃ t : LB.Gen (D.pull jH), t.IsGen) :
    ∃ c : LB.Gen (LB.LinComb D ![𝟙 H, p ≫ e] ![1, -1]), c.IsGen := by
  obtain ⟨t, ht⟩ := H₀
  let eU : U ⟶ HU := sq.lift (j ≫ e) (𝟙 U) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])
  have h₁ : eU ≫ jH = j ≫ e := sq.lift_fst _ _ _
  have h₂ : eU ≫ pU = 𝟙 U := sq.lift_snd _ _ _
  have h₃ : jH ≫ p ≫ e = (pU ≫ eU) ≫ jH := by rw [Category.assoc, h₁, sq.w_assoc]
  obtain ⟨t', ht', vt⟩ := exists_gen hD (φ' := fun i => jH ≫ ![𝟙 H, p ≫ e] i) (ε' := ![1, -1]) (by
      intro U _ h
      simp [Fintype.prod_sum_type, Fin.prod_univ_two, h₃])
    (LB.mulGen D _ _ _ _ t (LB.invGen D _ _ (LB.pullGen D _ _ t (pU ≫ eU))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ t ht _)))
  obtain ⟨ρ, hρ, vρ⟩ := exists_gen hD (φ' := fun i => e ≫ ![𝟙 H, p ≫ e] i) (ε' := ![1, -1]) (by
      intro U _ h
      simp [Fin.prod_univ_two, reassoc_of% he])
    (LB.oneGen D) (LB.isGen_oneGen D)
  obtain ⟨c, ⟨hc, -⟩, -⟩ := GlobalTheory.GenExtendNormal.existsUnique_gen_extend S hS U H HU H j p e jH pU eU hp hg he sq h₁ D hD (Fin 2) _ _ t' ρ ht' hρ
    (corr_of_val hD fun y J hJ => by
      rw [val_pull hJ, val_pull hJ, vt _ _ _ _ hJ, vρ _ _ _ _ hJ, val_mul hJ, val_inv, val_pull hJ, val_one,
        Category.id_comp, reassoc_of% h₂, mul_inv_cancel])
  exact ⟨c, hc⟩

end GlobalTheory.IsoExtend


open GlobalTheory.IsoExtend in
theorem GlobalTheory.lbIso_extend_of_normal : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ∀ (U H HU : Scheme.{0}) [Nonempty U] (j : U ⟶ S) [IsOpenImmersion j] (p : H ⟶ S) (e : S ⟶ H) (jH : HU ⟶ H) (pU : HU ⟶ U), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → IsPullback jH pU p j → ∀ (L M : LB H), L.IsLB → M.IsLB → LBIso (L.pull jH) (M.pull jH) → (LBIso (L.pull e) (M.pull e) → LBIso L M) ∧ ∀ s : S, ∃ N : S.Opens, s ∈ N ∧ LBIso (L.pull (p ⁻¹ᵁ N).ι) (M.pull (p ⁻¹ᵁ N).ι) := by
  intro S _ _ hS U H HU _ j _ p e jH pU hp hg he sq L M hL hM h
  have hD : (LB.div M L).IsLB := LB.isLB_div hM hL
  obtain ⟨c, hc⟩ := exists_gen_diff S hS U H HU j p e jH pU hp hg he sq hD ((lbIso_pull_iff_gen L M jH).1 h)
  refine ⟨fun h' => ?_, fun s => ?_⟩
  · exact exists_gen_chartPull (chartPullUnpull (LB.div M L) (𝟙 H) rfl)
      (exists_gen_of_diff hD _ c hc (𝟙 H) p e (Category.id_comp _) ((lbIso_pull_iff_gen L M e).1 h'))
  · obtain ⟨i, hi⟩ := exists_chart hD (e s)
    refine ⟨e ⁻¹ᵁ (LB.div M L).U i, hi, (lbIso_pull_iff_gen L M _).2 ?_⟩
    exact exists_gen_of_diff hD _ c hc _ (𝟙 _) _ (Category.id_comp _).symm
      (exists_gen_of_chart hD _ i fun y => y.2)
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))

namespace GlobalTheory

theorem finite_of_isClosed_of_finite_inter_closedPoints {T : Type*} [TopologicalSpace T]
    [JacobsonSpace T] {S : Set T} (hS : IsClosed S) (h : (S ∩ closedPoints T).Finite) :
    S.Finite := by
  have hc : IsClosed (S ∩ closedPoints T) := by
    rw [← Set.biUnion_of_singleton (S ∩ closedPoints T)]
    exact h.isClosed_biUnion fun x hx ↦ hx.2
  rw [← JacobsonSpace.closure_inter_closedPoints hS, hc.closure_eq]
  exact h

theorem finite_pullback_over_closedPoint {X Z P : Scheme.{0}} (π : X ⟶ Sp ℤ)
    [LocallyOfFiniteType π] (s : X ⟶ Z) (t : P ⟶ Z) (σ : X) (hσ : IsClosed ({σ} : Set X))
    {F : Set P} (hF : F.Finite) :
    {w : ↑(pullback s t) | pullback.fst s t w = σ ∧ pullback.snd s t w ∈ F}.Finite := by
  have := isClosed_singleton_iff_isClosedImmersion.mp hσ
  let i := X.fromSpecResidueField σ
  have h1 : LocallyOfFiniteType ((i ≫ s) ≫ specZIsTerminal.from Z) := by
    rw [specZIsTerminal.hom_ext ((i ≫ s) ≫ specZIsTerminal.from Z) (i ≫ π)]
    infer_instance
  have h2 : LocallyOfFiniteType (i ≫ s) := locallyOfFiniteType_of_comp _ (specZIsTerminal.from Z)
  have h3 : LocallyQuasiFinite (i ≫ s) :=
    .of_injective (Function.injective_of_subsingleton _)
  have h4 : QuasiCompact (i ≫ s) := ⟨fun U _ _ ↦ (Set.toFinite _).isCompact⟩
  have H := (IsPullback.of_hasPullback (pullback.fst s t) i).paste_horiz
    (IsPullback.of_hasPullback s t).flip
  have h5 : LocallyQuasiFinite (pullback.fst (pullback.fst s t) i ≫ pullback.snd s t) :=
    MorphismProperty.of_isPullback H.flip h3
  have h6 : QuasiCompact (pullback.fst (pullback.fst s t) i ≫ pullback.snd s t) :=
    MorphismProperty.of_isPullback H.flip h4
  refine (((pullback.fst (pullback.fst s t) i ≫ pullback.snd s t).finite_preimage hF).image
    (pullback.fst (pullback.fst s t) i)).subset ?_
  rintro w ⟨hw, hw'⟩
  have : w ∈ Set.range (pullback.fst (pullback.fst s t) i) := by
    rw [Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]
    exact hw
  obtain ⟨v, rfl⟩ := this
  exact ⟨v, by simpa using hw', rfl⟩

theorem locallyQuasiFinite_of_finite_fibres_closedPoints {Y X : Scheme.{0}} (f : Y ⟶ X)
    [LocallyOfFiniteType f] [JacobsonSpace Y]
    (h : ∀ y : Y, IsClosed ({y} : Set Y) → (f ⁻¹' {f y}).Finite) : LocallyQuasiFinite f := by
  rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff, eq_top_iff]
  refine subset_of_isOpen_of_closedPoints isOpen_univ f.quasiFiniteLocus.isOpen fun y hy _ ↦ ?_
  have : Finite (f.fiber (f y)) := (f.fiberHomeo (f y)).finite_iff.mpr (h y hy)
  exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)

theorem existsUnique_extension_of_finite_specializations :
    ∀ (X : Scheme.{0}) [IsIntegral X] (π : X ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π] [QuasiCompact π], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ (Z P : Scheme.{0}) (s : X ⟶ Z) (t : P ⟶ Z) [IsProper t] (G : P.Opens) (U : X.Opens) (φ : U.toScheme ⟶ P), (U : Set X).Nonempty → φ ≫ t = U.ι ≫ s → (∀ σ : X, IsClosed ({σ} : Set X) → ∃ F : Set P, F.Finite ∧ F ⊆ G ∧ ∀ (p : ℕ) [Fact p.Prime] (a : Sp (OO p) ⟶ X) (a₀ : Sp (PadicAlgCl p) ⟶ U.toScheme) (b : Sp (OO p) ⟶ P), a (cPt p) = σ → a₀ ≫ U.ι = gPt p ≫ a → gPt p ≫ b = a₀ ≫ φ → b ≫ t = a ≫ s → b (cPt p) ∈ F) → ∃! Φ : X ⟶ G.toScheme, U.ι ≫ Φ ≫ G.ι = φ ∧ Φ ≫ G.ι ≫ t = s := by
  intro X _ π _ _ _ hX Z P s t _ G U φ hU hφ H
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian π
  have : Nonempty U.toScheme := hU.to_subtype
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  have : QuasiCompact U.ι := inferInstance
  have : IsDominant U.ι := ⟨by
    rw [DenseRange, Scheme.Opens.range_ι]; exact U.isOpen.dense hU⟩
  let Γ := graphClosure s t U.ι φ hφ.symm
  let f : Γ ⟶ X := graphClosure.fst s t U.ι φ hφ.symm
  let g : Γ ⟶ P := graphClosure.snd s t U.ι φ hφ.symm
  let j : U.toScheme ⟶ Γ := graphClosure.incl s t U.ι φ hφ.symm
  have hjf : j ≫ f = U.ι := graphClosure.incl_fst ..
  have hjg : j ≫ g = φ := graphClosure.incl_snd ..
  have hfg : f ≫ s = g ≫ t := graphClosure.condition ..
  have : Flat (j ≫ f ≫ π) := by rw [reassoc_of% hjf]; infer_instance
  have : Flat (f ≫ π) := flat_of_schemeDominant_of_isDedekindDomain j _
  have : JacobsonSpace Γ := jacobsonSpace_of_locallyOfFiniteType_int (f ≫ π)
  choose F hF hFG hFH using H
  have hcl (z : Γ) (hz : IsClosed ({z} : Set Γ)) : IsClosed ({f z} : Set X) := by
    simpa using f.isClosedMap _ hz
  have key (z : Γ) (hz : IsClosed ({z} : Set Γ)) : g z ∈ F (f z) (hcl z hz) := by
    obtain ⟨p, hp, y, hy, hyU⟩ := padicAlgCl_integral_points.1 Γ (f ≫ π) z hz j.opensRange
      (Set.range_nonempty _)
    obtain ⟨l, e⟩ : ∃ l, l ≫ j = gPt p ≫ y := ⟨_, IsOpenImmersion.lift_fac j (gPt p ≫ y) hyU⟩
    have := hFH (f z) (hcl z hz) p (y ≫ f) l (y ≫ g)
      ((Scheme.Hom.comp_apply _ _ _).trans (congrArg f hy))
      (by rw [← reassoc_of% e, hjf]) (by rw [← reassoc_of% e, hjg]) (by simp [hfg])
    exact ((Scheme.Hom.comp_apply y g _).trans (congrArg g hy)) ▸ this
  have : LocallyQuasiFinite f := by
    refine locallyQuasiFinite_of_finite_fibres_closedPoints f fun y hy ↦ ?_
    refine finite_of_isClosed_of_finite_inter_closedPoints
      ((hcl y hy).preimage f.continuous) ?_
    refine ((finite_pullback_over_closedPoint π s t (f y) (hcl y hy) (hF _ (hcl y hy))).preimage
      (graphClosure.ι s t U.ι φ hφ.symm).isClosedEmbedding.injective.injOn).subset ?_
    rintro z ⟨hz, hz'⟩
    have hz₁ : f z = f y := hz
    have h₂ := key z hz'
    refine ⟨?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply]; exact hz₁
    · rw [← Scheme.Hom.comp_apply]
      have : ∀ (x : X) (hx : IsClosed ({x} : Set X)), f z = x → g z ∈ F x hx := by
        rintro _ _ rfl; exact h₂
      exact this _ _ hz₁
  have : IsIso f := isIso_of_isProper_of_quasiFinite_of_birational f (fun x ↦ (hX x).2) U ‹_›
  have hG : Set.range (inv f ≫ g) ⊆ Set.range G.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact subset_of_isOpen_of_closedPoints isOpen_univ (g ⁻¹ᵁ G).isOpen
      (fun z hz _ ↦ hFG _ _ (key z hz)) (Set.mem_univ _)
  have e := IsOpenImmersion.lift_fac G.ι (inv f ≫ g) hG
  have e' : U.ι ≫ inv f = j := by simp [hjf]
  refine ⟨IsOpenImmersion.lift G.ι (inv f ≫ g) hG, ⟨?_, ?_⟩, fun Φ hΦ ↦ ?_⟩
  · rw [e, reassoc_of% e', hjg]
  · rw [reassoc_of% e, ← hfg, IsIso.inv_hom_id_assoc]
  · rw [← cancel_mono G.ι, e]
    refine ext_of_isDominant_of_isSeparated t ?_ U.ι ?_
    · rw [Category.assoc, hΦ.2, Category.assoc, ← hfg, IsIso.inv_hom_id_assoc]
    · rw [hΦ.1, reassoc_of% e', hjg]

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem exists_semiAbelian_model_of_proper_base :
    ∀ (o W L : Type) [CommRing o] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (β : o →+* W) (Z : Scheme.{0}) (s : Z ⟶ Sp o) (x : Sp L ⟶ Z) (G : Over Z) [GrpObj G] (A : Over (Sp L)) [GrpObj A] (φ : A.left ⟶ G.left), IsProper s → x ≫ s = spMap ((algebraMap W L).comp β) → IsSemiAbelian G → IsGrpPullback A G x φ → ∃ (G' : Over (Sp W)) (_ : GrpObj G') (e : (Over.pullback (spMap (algebraMap W L))).obj G' ≅ A), IsSemiAbelian G' ∧ IsMonHom e.hom := by
  intro o W L _ _ _ _ _ _ _ β Z s x G _ A _ φ hs hx hG hA
  have hE : ValuativeCriterion.Existence s :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed s) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) s).1
  have hw : x ≫ s = Spec.map (CommRingCat.ofHom (algebraMap W L)) ≫ spMap β := by
    rw [hx, ← Spec.map_comp]; rfl
  obtain ⟨⟨y, hy, -⟩⟩ := (hE { R := W, K := L, i₁ := x, i₂ := spMap β, commSq := ⟨hw⟩ }).exists_lift
  have hy' : spMap (algebraMap W L) ≫ y = x := hy
  obtain ⟨e, he, -⟩ := grpPullback_iso
    (((isGrpPullback_pullback ((Over.pullback y).obj G) (spMap (algebraMap W L))).comp
      (isGrpPullback_pullback G y)).congr hy' rfl) hA
  exact ⟨(Over.pullback y).obj G, inferInstance, e, IsSemiAbelian.pullback y G hG, he⟩

end GlobalTheory.SS
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.SS

theorem baseChange_iso_tower (K K' V' V'' L : Type) [CommRing K] [CommRing K'] [CommRing V'] [CommRing V''] [CommRing L]
    [Algebra K K'] [Algebra V' K'] [Algebra V' V''] [Algebra V'' L] [Algebra K L] (j : K' →+* L)
    (t : j.comp (algebraMap V' K') = (algebraMap V'' L).comp (algebraMap V' V''))
    (e₂ : algebraMap K L = j.comp (algebraMap K K'))
    (A : Over (Spec (CommRingCat.of K))) [GrpObj A] (G : Over (Spec (CommRingCat.of V'))) [GrpObj G]
    (e : baseChange V' K' G ≅ baseChange K K' A) (he : IsMonHom e.hom) :
    ∃ e : baseChange V'' L (baseChange V' V'' G) ≅ baseChange K L A, IsMonHom e.hom := by
  have s₁ : specMap V'' L ≫ specMap V' V'' = spMap j ≫ specMap V' K' := by
    show spMap (algebraMap V'' L) ≫ spMap (algebraMap V' V'') = spMap j ≫ spMap (algebraMap V' K')
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, t]
  have s₂ : spMap j ≫ 𝟙 _ ≫ specMap K K' = specMap K L := by
    show spMap j ≫ 𝟙 _ ≫ spMap (algebraMap K K') = spMap (algebraMap K L)
    rw [Category.id_comp, e₂, ← Spec.map_comp]; rfl
  have p₁ := ((isGrpPullback_pullback (baseChange V' V'' G) (specMap V'' L)).comp
    (isGrpPullback_pullback G (specMap V' V''))).congr s₁ rfl
  have p₂ := (isGrpPullback_pullback (baseChange V' K' G) (spMap j)).comp
    (isGrpPullback_pullback G (specMap V' K'))
  have p₃ := ((isGrpPullback_pullback (baseChange V' K' G) (spMap j)).comp
    ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback A (specMap K K')))).congr s₂ rfl
  obtain ⟨i₁, hi₁, -⟩ := grpPullback_iso p₁ p₂
  obtain ⟨i₂, hi₂, -⟩ := grpPullback_iso p₃ (isGrpPullback_pullback A (specMap K L))
  refine ⟨i₁ ≪≫ i₂, ?_⟩
  rw [Iso.trans_hom]; infer_instance

theorem exists_finite_frac (V' K' V'' L : Type) [CommRing V'] [IsDomain V'] [Field K'] [Algebra V' K'] [IsFractionRing V' K']
    [CommRing V''] [IsDomain V''] [Algebra V' V''] [Field L] [Algebra V'' L] [IsFractionRing V'' L]
    (hf : Module.Finite V' V'') (hi : Function.Injective (algebraMap V' V'')) :
    ∃ j : K' →+* L, j.Finite ∧ j.comp (algebraMap V' K') = (algebraMap V'' L).comp (algebraMap V' V'') := by
  have : FaithfulSMul V' V'' := (faithfulSMul_iff_algebraMap_injective V' V'').2 hi
  have hinj : Function.Injective ((algebraMap V'' L).comp (algebraMap V' V'')) :=
    (IsFractionRing.injective V'' L).comp hi
  obtain ⟨j, t⟩ : ∃ j : K' →+* L, j.comp (algebraMap V' K') = (algebraMap V'' L).comp (algebraMap V' V'') :=
    ⟨IsFractionRing.lift (K := K') hinj, RingHom.ext fun x => IsFractionRing.lift_algebraMap hinj x⟩
  let a₁ : Algebra V' L := ((algebraMap V'' L).comp (algebraMap V' V'')).toAlgebra
  let a₂ : Algebra K' L := j.toAlgebra
  have : IsScalarTower V' V'' L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower V' K' L := IsScalarTower.of_algebraMap_eq' t.symm
  have : IsLocalization (Algebra.algebraMapSubmonoid V'' (nonZeroDivisors V')) L := inferInstance
  have h : Module.Finite K' L := Module.Finite.of_isLocalization V' V'' (nonZeroDivisors V')
  exact ⟨j, h, t⟩

theorem model_finite_ext : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A] (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (V' : Type) [CommRing V'] [IsDomain V'] [Algebra V V'] [Algebra V' K'] [IsFractionRing V' K'], (algebraMap V' K').comp (algebraMap V V') = (algebraMap K K').comp (algebraMap V K) → ∀ (G : Over (Spec (CommRingCat.of V'))) [GrpObj G], (∃ e : baseChange V' K' G ≅ baseChange K K' A, IsMonHom e.hom) → ∀ (V'' : Type) [CommRing V''] [IsDomain V''] [Algebra V' V''], Module.Finite V' V'' → Function.Injective (algebraMap V' V'') → ∃ (_ : Algebra K (FractionRing V'')) (_ : FiniteDimensional K (FractionRing V'')), (algebraMap V'' (FractionRing V'')).comp ((algebraMap V' V'').comp (algebraMap V V')) = (algebraMap K (FractionRing V'')).comp (algebraMap V K) ∧ ∃ e : baseChange V'' (FractionRing V'') (baseChange V' V'' G) ≅ baseChange K (FractionRing V'') A, IsMonHom e.hom := by
  intro V _ _ _ K _ _ _ A _ K' _ _ hK V' _ _ _ _ _ hc G _ ⟨e, he⟩ V'' _ _ _ hf hi
  obtain ⟨j, hj, t⟩ := exists_finite_frac V' K' V'' (FractionRing V'') hf hi
  let aK : Algebra K (FractionRing V'') := (j.comp (algebraMap K K')).toAlgebra
  have e₂ : algebraMap K (FractionRing V'') = j.comp (algebraMap K K') := rfl
  refine ⟨aK, hj.comp (RingHom.finite_algebraMap.2 hK), ?_, baseChange_iso_tower K K' V' V'' _ j t e₂ A G e he⟩
  rw [e₂, ← RingHom.comp_assoc, ← t, RingHom.comp_assoc, hc, RingHom.comp_assoc]

end GlobalTheory.SS
end
