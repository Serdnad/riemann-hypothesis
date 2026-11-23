module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ContinuousOnValue
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsLocalHomeomorphAddMonoidHomOfEventuallyEq
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle035
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle025
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEtaleCoordsVanishing
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle010
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle007
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle011
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle014
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.HermitianLattice
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle138
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.NumberTheory.NumberField.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle185
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle170
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle186
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle074
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFreeOverLocalRingStatement
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle187
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle016
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.dual_basis_hermitian_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H) (σ : E →+* ℂ) (κ : OK H →+* ℂ) (n : ℕ) (e : Fin n ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (x y : D.La), IsKForm D ε h → κ (wK H) = σ (H.w0 : E) → ∑ k, ∑ k', σ (HT.dualInt E (e k)) * κ (h (RingOfIntegers.basis E (e k) • x) (RingOfIntegers.basis E (e k') • y)) * starRingEnd ℂ (σ (HT.dualInt E (e k'))) = ((ε : ℤ) : ℂ) * σ ((H.rt : E) * sesq D x y) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.KForm.sigma_component | exact GlobalTheory.CompanionTheory.Ar.Fl.KForm.sigma_component | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.KForm.sigma_component <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CompanionTheory.Ar.UnifDim

open GlobalTheory.AbelianExp

attribute [local instance] GlobalTheory.AbelianExp.pointTopology

theorem eq_of_linear_lift {M : Type*} [Group M] {g d : ℕ} (e : (Fin g → ℂ) → M)
    (e' : (Fin d → ℂ) → M) (he' : ∀ z w, e' (z + w) = e' z * e' w)
    (hon : Function.Surjective e) (Λ : Submodule ℤ (Fin g → ℂ)) (Λ' : Submodule ℤ (Fin d → ℂ))
    (hk : ∀ z, e z = 1 ↔ z ∈ Λ) (hk' : ∀ z, e' z = 1 ↔ z ∈ Λ')
    [DiscreteTopology Λ] [DiscreteTopology Λ']
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin d → ℂ)) (hF : ∀ z, e' (F z) = e z) : g = d := by
  have hinj := AnyUnif.injective_of_ker_le_discrete Λ F fun z hz => by
    rw [← hk, ← hF, hz]
    exact (hk' 0).2 Λ'.zero_mem
  have hsurj : LinearMap.range F = ⊤ := AHWeil.eq_top_of_add_discrete Λ' _ fun w => by
    obtain ⟨z, hz⟩ := hon (e' w)
    refine ⟨⟨w - F z, (hk' _).1 ?_⟩, z, by simp⟩
    have h := he' (w - F z) (F z)
    rw [sub_add_cancel, hF, hz] at h
    exact (mul_eq_right.1 h.symm)
  simpa using (LinearEquiv.ofBijective F ⟨hinj, LinearMap.range_eq_top.1 hsurj⟩).finrank_eq

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

theorem holOn_ex (u : HolUnif A L g) : HolOn Set.univ u.ex := fun U f => by
  simpa only [Set.mem_univ, true_and] using u.hol U f

theorem compactSpace_points (u : HolUnif A L g) : CompactSpace (𝟙_ (Over (Sp ℂ)) ⟶ A) := by
  have hc : Continuous u.ex :=
    continuous_iff_continuousAt.2 fun z => (holOn_ex u).continuousAt (Set.mem_univ z)
  haveI := u.discrete
  haveI := holUnif_isZLattice u
  haveI : Module.Free ℤ u.Λ := ZLattice.module_free ℝ u.Λ
  haveI : Module.Finite ℤ u.Λ := ZLattice.module_finite ℝ u.Λ
  let b := (Module.Free.chooseBasis ℤ u.Λ).ofZLatticeBasis ℝ u.Λ
  have hK : IsCompact (closure (ZSpan.fundamentalDomain b)) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure
      (ZSpan.fundamentalDomain_isBounded b).closure
  refine isCompact_univ_iff.1 ((hK.image hc).of_isClosed_subset isClosed_univ fun x _ => ?_)
  obtain ⟨z, rfl⟩ := u.ex_onto x
  refine ⟨ZSpan.fract b z, subset_closure (ZSpan.fract_mem_fundamentalDomain b z), ?_⟩
  have hm : ((ZSpan.floor b z : _) : Fin g → ℂ) ∈ u.Λ := by
    have e := Module.Basis.ofZLatticeBasis_span ℝ u.Λ (Module.Free.chooseBasis ℤ u.Λ)
    exact e.le (ZSpan.floor b z).2
  have h := u.ex_add (ZSpan.fract b z) (ZSpan.floor b z)
  rw [(u.ker _).2 hm, _root_.mul_one, ZSpan.fract_apply, sub_add_cancel] at h
  rw [ZSpan.fract_apply]
  exact h.symm

theorem eq_relativeDimension : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g d : ℕ)
    (u : HolUnif A L g), SmoothOfRelativeDimension d A.hom → g = d := by
  intro A _ L g d u hd
  letI : CommGroup (𝟙_ (Over (Sp ℂ)) ⟶ A) :=
    { (inferInstance : Group (𝟙_ (Over (Sp ℂ)) ⟶ A)) with
      mul_comm := fun a b ↦ by
        obtain ⟨z, rfl⟩ := u.ex_onto a
        obtain ⟨w, rfl⟩ := u.ex_onto b
        exact (u.ex_add z w).symm.trans ((congrArg u.ex (add_comm z w)).trans (u.ex_add w z)) }
  have hval := @valAt'_rules
  have hprod := @holFamily_lift hval
  have htop := @isTopologicalGroup_complexPoints hval
  have hchart := @HolChart.exists_holomorphic_chart hval (@existsUnique_point_of_ringHom)
    (@exists_holomorphic_section_of_etale)
  have := htop A
  have := compactSpace_points u
  have hpost := fun X x => (hval X x).2.2.2.1
  have hmulHol : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E)
      (a b : E → (𝟙_ (Over (Sp ℂ)) ⟶ A)), HolOn W a → HolOn W b → HolOn W fun w => a w * b w :=
    fun E _ _ W a b ha hb => HolOn.post hpost (hprod E W _ _ a b ha hb) μ[A]
  obtain ⟨W, σ, U, t, hW, h0, hσ0, hU, hσ, ht, ho, hD⟩ := hchart A d hd 1
  let φ : OpenPartialHomeomorph (Additive (𝟙_ (Over (Sp ℂ)) ⟶ A)) (Fin d → ℂ) :=
    chart t hW hσ ht ho
  have hU1 : ⊤ ≤ (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A).left ⁻¹ᵁ U := hσ0 ▸ (ht 0 h0).1
  have hφ : IsAnalyticGroupChart φ := by
    refine ⟨⟨0, h0, hσ0⟩, funext fun i => ?_, ?_⟩
    · have := (ht 0 h0).2 i
      rwa [hσ0] at this
    · have hH := hmulHol _ (W ×ˢ W) _ _
        (HolOn.comp hσ (hW.prod hW) differentiableOn_fst fun p hp => hp.1)
        (HolOn.comp hσ (hW.prod hW) differentiableOn_snd fun p hp => hp.2)
      refine hH.analyticAt t (w := 0) ⟨h0, h0⟩ ?_
      simpa only [Prod.fst_zero, Prod.snd_zero, hσ0, _root_.mul_one] using hU1
  have hu := holOn_ex u
  have hu0 : u.ex 0 = 1 := holUnif_ex_zero_eq_one u
  have h1 : φ (u.ex 0) = 0 := by rw [hu0]; exact hφ.map_zero
  have h2 : AnalyticAt ℂ (fun w => φ (u.ex w)) 0 :=
    hu.analyticAt t (Set.mem_univ _) (hu0 ▸ hU1)
  have hG0 : hφ.log (φ (u.ex 0)) = 0 := by
    simp only [h1]
    exact hφ.isLocalCommGroupLaw.log_zero
  have hGa : AnalyticAt ℂ (fun w => hφ.log (φ (u.ex w))) 0 :=
    AnalyticAt.comp (g := hφ.log) (h1 ▸ hφ.isLocalCommGroupLaw.analyticAt_log) h2
  have hGe : ∀ᶠ w in 𝓝 (0 : Fin g → ℂ), (hφ.exp (hφ.log (φ (u.ex w)))).toMul = u.ex w := by
    have h3 : Tendsto u.ex (𝓝 0) (𝓝 1) := hu0 ▸ (hu.continuousAt (Set.mem_univ 0)).tendsto
    exact h3.eventually hφ.exp_log
  have hF := EndoLinear.fderiv_lifts (fun v => (hφ.exp v).toMul)
    (fun z w => congrArg Additive.toMul (hφ.exp.map_add z w)) hφ.periodLattice (fun z => Iff.rfl)
    inferInstance u.ex u.ex_add _ hG0 hGa.differentiableAt hGe
  haveI := u.discrete
  exact eq_of_linear_lift u.ex (fun v => (hφ.exp v).toMul)
    (fun z w => congrArg Additive.toMul (hφ.exp.map_add z w)) u.ex_onto u.Λ hφ.periodLattice u.ker
    (fun z => Iff.rfl) (fderiv ℂ (fun w => hφ.log (φ (u.ex w))) 0).toLinearMap hF

end GlobalTheory.CompanionTheory.Ar.UnifDim
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lie_model_complex_base_change : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ S) (V : Type) [AddCommGroup V] [Module (𝓞 L) V] (M : LieModel G z V) (σ : L →+* ℂ), ∃ Mσ : LieModel G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) (GroundTheory.Heights₂.Heights.Fibre σ V), ∀ e : V, ((Mσ.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (M.pt e).left) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieSigma.lieModel_fibre | exact GlobalTheory.CompanionTheory.Ar.LieSigma.lieModel_fibre | (intros; apply GlobalTheory.CompanionTheory.Ar.LieSigma.lieModel_fibre <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lie_model_rank_eq_generic : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), (∀ q : X, genPt ξ ⤳ q) → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X) (V : Type) [AddCommGroup V] [Module (𝓞 L) V] (MB : LieModel G z V), Module.finrank (𝓞 L) V = Module.finrank Ω Li := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lieModel_finrank_eq | exact GlobalTheory.CompanionTheory.Ar.lieModel_finrank_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.lieModel_finrank_eq <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.CompanionTheory.Ar.LieBc

theorem exists_model_of_eq {S : Scheme.{0}} {R : Type} [CommRing R] (G : Over S) [GrpObj G] {x₁ x₂ : Sp R ⟶ S}
    (hx : x₁ = x₂) {T : Type} [AddCommGroup T] [Module R T] (M₁ : LieModel G x₁ T) :
    ∃ M₂ : LieModel G x₂ T, ∀ t, (M₂.pt t).left = (M₁.pt t).left := by
  subst hx
  exact ⟨M₁, fun _ => rfl⟩

theorem injective_of_isBaseChange {K K' : Type} [Field K] [Field K'] [Algebra K K'] {V T : Type} [AddCommGroup V]
    [Module K V] [AddCommGroup T] [Module K T] [Module K' T] [IsScalarTower K K' T] {j : V →ₗ[K] T}
    (hj : IsBaseChange K' j) : Function.Injective j := by
  have e : ⇑j = hj.equiv ∘ TensorProduct.mk K K' V 1 := by
    funext x
    simp [IsBaseChange.equiv_tmul]
  rw [e]
  exact hj.equiv.injective.comp (Module.FaithfullyFlat.tensorProduct_mk_injective V)

theorem span_range_of_isBaseChange {K K' : Type} [CommRing K] [CommRing K'] [Algebra K K'] {V T : Type}
    [AddCommGroup V] [Module K V] [AddCommGroup T] [Module K T] [Module K' T] [IsScalarTower K K' T]
    {j : V →ₗ[K] T} (hj : IsBaseChange K' j) : Submodule.span K' (Set.range j) = ⊤ := by
  rw [eq_top_iff]
  intro t _
  refine hj.inductionOn t (fun m => Submodule.subset_span ⟨m, rfl⟩) (fun s n h => Submodule.smul_mem _ s h)
    (fun a b ha hb => Submodule.add_mem _ ha hb)

end GlobalTheory.CompanionTheory.Ar.LieBc

theorem GlobalTheory.CompanionTheory.Ar.LieBc.main : ∀ (L L' : Type) [Field L] [Field L'] (e : L →+* L') (G : Over (Sp L)) (G' : Over (Sp L')) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [GrpObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G (spMap e) φ → ∀ (V : Type) [AddCommGroup V] [Module L V] (MV : LieModel G (𝟙 (Sp L)) V), ∃ (V' : Type) (_ : AddCommGroup V') (_ : Module L' V') (MV' : LieModel G' (𝟙 (Sp L')) V') (j : V →+ V'), (∀ (c : L) x, j (c • x) = e c • j x) ∧ Function.Injective j ∧ (∀ x, (MV'.pt (j x)).left ≫ φ = spMap (dualMap e) ≫ (MV.pt x).left) ∧ Submodule.span L' (Set.range j) = ⊤ := by
  intro L L' _ _ e G G' _ _ _ _ φ h V _ _ MV
  letI : Algebra L L' := e.toAlgebra
  obtain ⟨T, iT, mT, mR, tower, M', j, hl, hbc⟩ :=
    GlobalTheory.CompanionTheory.Ar.FlagFib.lieModel_liftBaseChange (Sp L) G L L' (𝟙 _) V MV
  have hx : spMap (algebraMap L L') ≫ 𝟙 (Sp L) = 𝟙 (Sp L') ≫ spMap e := by
    rw [Category.comp_id, Category.id_comp]
    rfl
  obtain ⟨M₂, hM₂⟩ := GlobalTheory.CompanionTheory.Ar.LieBc.exists_model_of_eq G hx M'
  refine ⟨T, iT, mT, GlobalTheory.CompanionTheory.Ar.LieMove.pullModel h M₂, j.toAddMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro c x
    change j (c • x) = e c • j x
    rw [map_smul]
    exact (algebraMap_smul L' c (j x)).symm
  · exact GlobalTheory.CompanionTheory.Ar.LieBc.injective_of_isBaseChange hbc
  · intro x
    have e₁ := hl x
    have e₂ : (M'.pt (j x)).left ≫ 𝟙 G.left = spMap (dualMap (algebraMap L L')) ≫ (MV.pt x).left := e₁
    change (GlobalTheory.CompanionTheory.Ar.LieMove.liftEps h (M₂.pt (j x))).left ≫ φ = _
    rw [GlobalTheory.CompanionTheory.Ar.LieMove.liftEps_left, hM₂]
    exact (Category.comp_id _).symm.trans e₂
  · exact GlobalTheory.CompanionTheory.Ar.LieBc.span_range_of_isBaseChange hbc
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieStalk

theorem _root_.GlobalTheory.T.lie_model_descends_base_change : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (x : Sp R ⟶ S) (E' : Type) [AddCommGroup E'] [Module R' E'] [Module R E'] [IsScalarTower R R' E'] (M' : LieModel G (spMap (algebraMap R R') ≫ x) E'), ∃ (E : Type) (_ : AddCommGroup E) (_ : Module R E) (M : LieModel G x E) (j : E →ₗ[R] E'), IsBaseChange R' j ∧ ∀ e, (M'.pt (j e)).left = spMap (dualMap (algebraMap R R')) ≫ (M.pt e).left := by
  exact @GlobalTheory.CompanionTheory.Ar.LieBaseChange.exists_isBaseChange
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.exists_lie_model_base_change : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (x : Sp R ⟶ X) (V : Type) [AddCommGroup V] [Module R V] (M : LieModel G x V), ∃ (T : Type) (_ : AddCommGroup T) (_ : Module R' T) (_ : Module R T) (_ : IsScalarTower R R' T) (M' : LieModel G (spMap (algebraMap R R') ≫ x) T) (j : V →ₗ[R] T), (∀ e, ((M'.pt (j e)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap R R')) ≫ (M.pt e).left)) ∧ IsBaseChange R' j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagFib.lieModel_liftBaseChange | exact GlobalTheory.CompanionTheory.Ar.FlagFib.lieModel_liftBaseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagFib.lieModel_liftBaseChange <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.torus_embedding_lie_injective : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (S : Scheme.{0}) (b : Sp R ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] [IsSeparated G.hom] [Smooth G.hom] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u : splitTorus S X ⟶ G) [IsMonHom u], (∀ (A : Type) [CommRing A] (g : K →+* A) (t : Over.mk (spMap g ≫ spMap (algebraMap R K) ≫ b) ⟶ splitTorus S X), t ≫ u = 1 → t = 1) → ∀ (MT : LieModel (splitTorus S X) b (X →+ R)), IsCocharLie MT → ∀ (E : Type) [AddCommGroup E] [Module R E] (M : LieModel G b E) (A : (X →+ R) →ₗ[R] E), (∀ δ, M.pt (A δ) = MT.pt δ ≫ u) → Function.Injective A ∧ ∀ (a : R) (y : E), a ≠ 0 → a • y ∈ LinearMap.range A → y ∈ LinearMap.range A := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorusSat.lie_torus_saturated | exact GlobalTheory.CompanionTheory.Ar.TorusSat.lie_torus_saturated | (intros; apply GlobalTheory.CompanionTheory.Ar.TorusSat.lie_torus_saturated <;> assumption)
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem FlatHerm.inter_eq : PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω)
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (W : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (A : HermLine ι) (S : FlatHerm y φ A) (d : ℕ),
    IsIntersectionFamily I → IsArithVar (mCoordIdeal y) d → OverInt y φ → mCoordIdeal y ≤ W →
    IsArithVar W (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
    I W (n + 1) (Fin.snoc L A) = S.ht * ptsIntegral W (pot L) (fun _ => 1) := by
  intro hP K _ ι _ Ω _ F _ _ y φ I W n L A S d hI hY hO hyW hW hL hA
  obtain ⟨u, hu, -⟩ := GlobalTheory.T.exists_place_weight_conj_invariant K ι Ω F y φ (fun σ => Real.log (S.κ σ)) hO
  rw [GlobalTheory.T.intersection_family_flat_twist K ι Ω F y φ I W n L A S d u hI hY hO hyW hW hL hA hu,
    GlobalTheory.T.intersection_family_place_weight hP K ι Ω F y φ I W n L d (fun σ => Real.log (S.κ σ)) u hI hY hO hyW hW hL
      (fun σ => congrArg Real.log (S.κ_conj σ)) (fun σ z hz => (hu.near σ z hz).self_of_nhds),
    FlatHerm.ht, neg_mul]

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

theorem exists_base {S : Scheme.{0}} {G : Over S} [GrpObj G] {A R : Type} [CommRing A] [CommRing R] (φ : A →+* R)
    (x : Spec (CommRingCat.of A) ⟶ S) (z : Spec (CommRingCat.of R) ⟶ S)
    (hz : Spec.map (CommRingCat.ofHom φ) ≫ x = z) {E F : Type} [AddCommGroup E] [Module A E] [AddCommGroup F]
    [Module R F] (M : LieModel G x E) (N : LieModel G z F) :
    ∃ j : E →+ F, (∀ e, (N.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ (M.pt e).left) ∧
      (∀ (a : A) e, j (a • e) = φ a • j e) ∧
      (Smooth G.hom → ∀ (n : ℕ) (b : Module.Basis (Fin n) A E),
        Submodule.span R (Set.range fun k => j (b k)) = ⊤) := by
  subst hz
  letI := φ.toAlgebra
  obtain ⟨j, h1, h2, h3⟩ := GlobalTheory.T.lie_model_base_change_map S G A R x E F M N
  exact ⟨j, h1, h2, fun hs n b => (h3 hs n b).2⟩

end GlobalTheory.CompanionTheory.Ar.LieVal

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

theorem lieLat_val (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (Ω : Type) [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (R : Type)
    [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X) (h : genPt ξ ⤳ centre z) (ER : Type)
    [AddCommGroup ER] [Module R ER] (MR : LieModel G z ER) :
    IsCptGen ξ → Smooth G.hom → ∃ ev : M.lat ⟨centre z, h⟩ →+ ER,
      (∀ (e : E) (w : ER), M.ValAt z e (MR.pt w) ↔ ∃ he : e ∈ M.lat ⟨centre z, h⟩, ev ⟨e, he⟩ = w) ∧
      (∀ (a : regAt ξ ⟨centre z, h⟩) (r : R) e, ValAt ξ z (a : Ω) r → ev (a • e) = r • ev e) ∧
      Submodule.span R (Set.range ev) = ⊤ := by
  intro hξ hs
  obtain ⟨EA, _, _, ⟨MA⟩⟩ := lieModel_exists X G (X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z))
  obtain ⟨j, hj, hjs, hjb⟩ := LieVal.exists_base (A := X.presheaf.stalk (centre z)) (Scheme.stalkClosedPointTo z).hom _ z
    (LieTangent.spec_centre z) MA MR
  obtain ⟨i, hi, his, -⟩ := LieVal.exists_base (genMap ξ ⟨centre z, h⟩) _ ξ
    (LieTangent.spec_genMap ξ ⟨centre z, h⟩) MA M

  have hext : ∀ a, M.Extends ⟨centre z, h⟩ (i a) (MA.pt a) := fun a => ⟨MA.tan a, hi a⟩
  have hmem : ∀ a, i a ∈ M.lat ⟨centre z, h⟩ := fun a => (M.mem_lat_iff _ _).2 ⟨_, hext a⟩
  have hinj : ∀ a b, i a = i b → a = b := fun a b hab =>
    MA.inj ((hext a).unique (hξ.inj _) (hab ▸ hext b))
  have hsurj : ∀ e v, M.Extends ⟨centre z, h⟩ e v → ∃ a, i a = e ∧ MA.pt a = v := by
    intro e v hv
    obtain ⟨a, rfl⟩ := MA.onto v hv.1
    exact ⟨a, M.inj (Over.OverMorphism.ext ((hi a).trans hv.2.symm)), rfl⟩
  let i' : EA →+ M.lat ⟨centre z, h⟩ :=
    { toFun := fun a => ⟨i a, hmem a⟩
      map_zero' := Subtype.ext (map_zero i)
      map_add' := fun a b => Subtype.ext (map_add i a b) }
  have hbij : Function.Bijective i' := by
    refine ⟨fun a b hab => hinj a b (congrArg Subtype.val hab), fun e => ?_⟩
    obtain ⟨v, hv⟩ := (M.mem_lat_iff _ _).1 e.2
    obtain ⟨a, ha, -⟩ := hsurj _ _ hv
    exact ⟨a, Subtype.ext ha⟩
  let q := AddEquiv.ofBijective i' hbij
  have hq : ∀ a, q.symm ⟨i a, hmem a⟩ = a := fun a => q.symm_apply_apply a
  refine ⟨j.comp q.symm.toAddMonoidHom, ?_, ?_, ?_⟩
  · intro e w
    constructor
    · rintro ⟨h', v, hv, hw⟩
      obtain ⟨a, rfl, rfl⟩ := hsurj _ _ hv
      refine ⟨hmem a, ?_⟩
      change j (q.symm ⟨i a, hmem a⟩) = w
      rw [hq]
      exact MR.inj (Over.OverMorphism.ext ((hj a).trans hw.symm))
    · rintro ⟨he, rfl⟩
      obtain ⟨v, hv⟩ := (M.mem_lat_iff _ _).1 he
      obtain ⟨a, rfl, rfl⟩ := hsurj _ _ hv
      change M.ValAt z (i a) (MR.pt (j (q.symm ⟨i a, hmem a⟩)))
      rw [hq]
      exact ⟨h, _, hext a, hj a⟩
  · rintro a r e ⟨_, s, hsa, rfl⟩
    obtain ⟨b, rfl⟩ := q.surjective e
    have : a • q b = q (s • b) := Subtype.ext (by
      change (a : Ω) • i b = i (s • b)
      rw [his, hsa])
    change j (q.symm (a • q b)) = _ • j (q.symm (q b))
    rw [this, q.symm_apply_apply, q.symm_apply_apply]
    exact hjs s b
  · obtain ⟨n, ⟨b⟩⟩ := GlobalTheory.T.lie_model_free_over_local_ring X G hs (X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z)) EA MA
    refine top_le_iff.1 ((hjb hs n b).symm.le.trans (Submodule.span_mono ?_))
    rintro _ ⟨k, rfl⟩
    refine ⟨q (b k), ?_⟩
    change j (q.symm (q (b k))) = _
    rw [q.symm_apply_apply]

end GlobalTheory.CompanionTheory.Ar
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights


theorem _root_.GlobalTheory.T.regular_functional_specializes : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X)
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (f : Module.Dual Ω Li) (p q : Cpt ξ),
    IsCptGen ξ → q.1 ⤳ p.1 → (∀ e ∈ M.lat p, f e ∈ regAt ξ p) → ∀ e ∈ M.lat q, f e ∈ regAt ξ q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.lat_form_regular_generizes | exact GlobalTheory.CompanionTheory.Ar.RootHt.lat_form_regular_generizes | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.lat_form_regular_generizes <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

namespace GlobalTheory.CompanionTheory.Ar.Ht.TopLower

theorem i5_of_hasRef_of_fibreInput : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (j k : ℕ) (T : RootTower Ψ (j + 1 + (k + 1)))
    (II : IntersectionSystem) (R : T.Comp → RootModel Ψ (j + 1 + (k + 1))), IsIntersectionSystem II → HasRef T R →
    (∀ c, AmpleQ (R c).y (R c).A.a ∧ FlatUnit (R c) ∧ FibreInput (R c)) → T.I5 II := by
  intro Ψ _ _ j k T II R hII hR h
  exact GlobalTheory.T.tower_i5_of_reference Ψ _ T II R hII hR fun c =>
    GlobalTheory.T.ref_lower_of_fibre_input Ψ j k (R c) (h c).1 (h c).2.1 (h c).2.2

end GlobalTheory.CompanionTheory.Ar.Ht.TopLower
end
