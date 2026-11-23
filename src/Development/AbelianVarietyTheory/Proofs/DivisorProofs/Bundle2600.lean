module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2308
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2590
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2520
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1763
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1852
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1851
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1646
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle085
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle115
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemistableReductionZero
public import Formalism.LocalToGlobal.ProjectiveLattices.EmbKCoe
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle210
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle039
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle024
public import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle629
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
import Mathlib.RingTheory.TensorProduct.Nontrivial
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
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle005
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.SmoothLift

theorem exists_linearEquiv_of_rel {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (p : M → N → Prop) (h1 : ∀ c, ∃ h, p c h) (h2 : ∀ h, ∃ c, p c h)
    (h0 : ∀ c h, p c h → (c = 0 ↔ h = 0)) (hadd : ∀ a b h h', p a h → p b h' → p (a + b) (h + h'))
    (hsmul : ∀ (r : R) a h, p a h → p (r • a) (r • h)) : ∃ e : M ≃ₗ[R] N, ∀ c h, e c = h ↔ p c h := by
  choose f hf using h1
  have uniq : ∀ c h h', p c h → p c h' → h' = h := by
    intro c h h' ph ph'
    have q := hadd _ _ _ _ ph' (hsmul (-1) _ _ ph)
    rw [neg_one_smul, neg_one_smul, add_neg_cancel] at q
    exact add_neg_eq_zero.1 ((h0 _ _ q).1 rfl)
  let g : M →ₗ[R] N :=
    { toFun := f
      map_add' := fun a b ↦ uniq _ _ _ (hadd _ _ _ _ (hf a) (hf b)) (hf (a + b))
      map_smul' := fun r a ↦ uniq _ _ _ (hsmul r _ _ (hf a)) (hf (r • a)) }
  have inj : Function.Injective g := by
    intro a b hab
    have q := hadd _ _ _ _ (hf a) (hsmul (-1) _ _ (hf b))
    rw [neg_one_smul, neg_one_smul] at q
    have hab' : f a = f b := hab
    rw [hab', add_neg_cancel] at q
    exact add_neg_eq_zero.1 ((h0 _ _ q).2 rfl)
  have surj : Function.Surjective g := by
    intro h
    obtain ⟨c, hc⟩ := h2 h
    exact ⟨c, uniq _ _ _ hc (hf c)⟩
  refine ⟨LinearEquiv.ofBijective g ⟨inj, surj⟩, fun c h ↦ ⟨?_, fun ph ↦ uniq _ _ _ ph (hf c)⟩⟩
  rintro rfl
  exact hf c

end GlobalTheory.SmoothLift

namespace GlobalTheory.SmoothLift

theorem crystallineSmoothLift_of_relations : GlobalTheory.Published.CrystallineSmoothLift := by
  have Λ : ∀ D : Data, Lift D := fun D ↦ Classical.choice (GlobalTheory.T.nonempty_smoothLiftAffineThickenings D)
  obtain ⟨hr1, hr2⟩ := GlobalTheory.T.crystallineCechDeRham_relations_total_detect_zero
  have E1 : ∀ D : Data, ∃ e : CatCoh.H1 (O D.κ D.t) ≃ₗ[D.R] HH1 D.s, ∀ c h, e c = h ↔ (Λ D).Rel1 c h := fun D ↦
    exists_linearEquiv_of_rel _ (hr1 D (Λ D)).1 (hr1 D (Λ D)).2.1 (hr1 D (Λ D)).2.2
      (GlobalTheory.T.smoothLift_comparisonRelations_add_smul D (Λ D)).1 (GlobalTheory.T.smoothLift_comparisonRelations_add_smul D (Λ D)).2.1
  have E2 : ∀ D : Data, ∃ e : CatCoh.H2 (O D.κ D.t) ≃ₗ[D.R] HH2 D.s, ∀ c h, e c = h ↔ (Λ D).Rel2 c h := fun D ↦
    exists_linearEquiv_of_rel _ (hr2 D (Λ D)).1 (hr2 D (Λ D)).2.1 (hr2 D (Λ D)).2.2
      (GlobalTheory.T.smoothLift_comparisonRelations_add_smul D (Λ D)).2.2.1 (GlobalTheory.T.smoothLift_comparisonRelations_add_smul D (Λ D)).2.2.2
  choose e₁ he₁ using E1
  choose e₂ he₂ using E2
  have r1 : ∀ D c, (Λ D).Rel1 c (e₁ D c) := fun D c ↦ (he₁ D c _).1 rfl
  have r2 : ∀ D c, (Λ D).Rel2 c (e₂ D c) := fun D c ↦ (he₂ D c _).1 rfl
  refine ⟨e₁, e₂, ?_, ?_, ?_⟩
  · intro D a b
    exact (he₂ D _ _).2 (GlobalTheory.T.comparison_relations_respect_cup D (Λ D) a b _ _ (r1 D a) (r1 D b))
  · intro D m c
    exact (he₁ D _ _).2 (GlobalTheory.T.smoothLift_degreeOne_comparisonRelation D (Λ D) m c)
  · intro D D' σ φ φ₀ h m hc
    exact ⟨fun c ↦ GlobalTheory.T.crystallineDeRhamRelation_natural_smoothLift_morphism.1 D D' (Λ D) (Λ D') σ φ φ₀ h m hc c _ _ (r1 D c) (r1 D' _),
      fun c ↦ GlobalTheory.T.crystallineDeRhamRelation_natural_smoothLift_morphism.2 D D' (Λ D) (Λ D') σ φ φ₀ h m hc c _ _ (r2 D c) (r2 D' _)⟩

end GlobalTheory.SmoothLift
end
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

namespace GlobalTheory.LineForm.FirstChern

open Filter Topology GlobalTheory.HermFrame GlobalTheory.Points
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder ComplexConjugate

theorem chernAt_exp_neg {n : ℕ} {u : V n → ℝ} {v : V n} (hu : ContDiffAt ℝ 2 u v) :
    chernAt (fun x => (Matrix.of fun _ _ : Unit => ((Real.exp (-u x) : ℝ) : ℂ))) v 1 = ofValues (ddc u v) := by
  have h1 (G : V n → Matrix Unit Unit ℂ) : chernAt G v 1 = ofValues (chernOne G v) := by
    unfold chernAt ofValues GlobalTheory.GoodMetric.chernPoly chernOne
    rw [Matrix.coeff_charpolyRev_eq_neg_trace, Matrix.trace_neg, neg_neg, pow_one]

    simp only [Matrix.trace, Matrix.diag, GlobalTheory.GoodMetric.curvPoly, Matrix.of_apply, map_sum, map_mul,
    MvPolynomial.aeval_C, MvPolynomial.aeval_X, ← Algebra.smul_def, mul_smul, ← Finset.smul_sum, Finset.sum_smul]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
  rw [h1]
  congr 1
  funext ξ η
  rw [chernOne_line (f := fun x => Real.exp (-u x)) (Real.contDiff_exp.contDiffAt.comp v hu.neg) (Real.exp_ne_zero _)
    (Eventually.of_forall fun _ => rfl)]
  simp only [Real.log_exp, ddc, leviForm_neg]
  simp

end GlobalTheory.LineForm.FirstChern
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.LineForm
open scoped Classical

namespace GlobalTheory.CxFormStokesBoth

open Set

section
variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem eq_sum_fn_mul {N : ℕ} (χ : Fin N → M → ℝ) (hχ : ∀ y, ∑ j, χ j y = 1) (η : A.Fld) :
    η = ∑ j, A.fn (χ j) * η := by
  rw [← Finset.sum_mul]
  have : (∑ j, A.fn (χ j)) = 1 := by
    funext x
    simp only [Finset.sum_apply, HolAtlas.fn, Pi.one_apply]

    rw [← map_sum, ← Complex.ofReal_sum, hχ, Complex.ofReal_one, map_one]
  rw [this, one_mul]

theorem dbar_sum {N : ℕ} (α : Fin N → A.Fld) (hα : ∀ j, A.IsForm (α j)) :
    A.dbar (∑ j, α j) = ∑ j, A.dbar (α j) := by
  funext x
  have hloc : ∀ w, A.loc (∑ j, α j) x.1.1 w = ∑ j, A.loc (α j) x.1.1 w := by
    intro w
    by_cases hw : w ∈ (A.e x.1.1).target
    · simp only [HolAtlas.loc, dite_eq_left hw]
      exact Finset.sum_apply _ _ _
    · simp [HolAtlas.loc, hw]
  have hx := (A.e x.1.1).open_target.mem_nhds (x.ch.map_source x.2)
  have hdiff : ∀ j S, DifferentiableAt ℝ (fun w => (bas n).repr (A.loc (α j) x.1.1 w) S) x.crd :=
    fun j S => (((hα j).smooth x.1.1 S).differentiableOn (by simp)).differentiableAt hx
  have hcoeff : ∀ S u,
      GlobalTheory.dbar (fun w => (bas n).repr (A.loc (∑ j, α j) x.1.1 w) S) x.crd u =
        ∑ j, GlobalTheory.dbar (fun w => (bas n).repr (A.loc (α j) x.1.1 w) S) x.crd u := by
    intro S u
    have hsum : (fun w => (bas n).repr (A.loc (∑ j, α j) x.1.1 w) S) =
        fun w => ∑ j, (bas n).repr (A.loc (α j) x.1.1 w) S := by
      funext w
      rw [hloc, map_sum, Finsupp.finsetSum_apply]
    rw [hsum, GlobalTheory.dbar_sum (fun j _ => hdiff j S), _root_.sum_apply]
  rw [Finset.sum_apply]
  simp only [HolAtlas.dbar, dbarAt, coefwise, hcoeff, Finset.sum_smul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
end

theorem stokes : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n),
    ∀ η : A.Fld, A.IsForm η → A.integral (A.del η) = 0 ∧ A.integral (A.dbar η) = 0 := by
  intro M _ _ _ _ _ _ n A η hη
  obtain ⟨N, c, χ, hs, hsupp, hone⟩ := GlobalTheory.T.exists_finite_smooth_partition_unity_holAtlas A
  have hf : ∀ j, A.IsForm (A.fn (χ j) * η) := fun j =>
    FormMul.isForm_mul A _ _ (A.isForm_fn (hs j)) hη
  have hdiff : ∀ j, A.IsForm (A.del (A.fn (χ j) * η)) ∧ A.IsForm (A.dbar (A.fn (χ j) * η)) :=
    fun j => GlobalTheory.T.holAtlas_isForm_del_dbar_smooth M n A _ (hf j)
  have hdec := eq_sum_fn_mul A χ hone η
  constructor
  · rw [hdec, GlobalTheory.T.holAtlas_del_finset_sum A _ hf,
      GlobalTheory.T.holAtlas_integral_fin_sum_compact A _ (fun j => (hdiff j).1)]
    exact Finset.sum_eq_zero fun j _ => GlobalTheory.T.integral_del_chartSupported_mul_form_eq_zero A η (χ j) (c j) hη (hs j) (hsupp j)
  · rw [hdec, dbar_sum A _ hf,
      GlobalTheory.T.holAtlas_integral_fin_sum_compact A _ (fun j => (hdiff j).2)]
    exact Finset.sum_eq_zero fun j _ => GlobalTheory.T.integral_dbar_cutoff_mul_form_eq_zero_local_stokes A η (χ j) (c j) hη (hs j) (hsupp j)

end GlobalTheory.CxFormStokesBoth
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory.SS

theorem potModel_semiAbelian_torusExtension : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → GlobalTheory.SS.PotModel V K A (fun _ _ _ G _ => IsSemiAbelian G ∧ Nonempty (TorusExtension (GlobalTheory.SS.spFibre G))) := by
  intro V K _ _ _ _ _ _ _ _ A _ hA
  obtain ⟨K', _, _, _, V', _, _, _, _, _, _, hfin, hinj, hcomm, G, _, hc, hsm, hsep, hqc, he, hT⟩ :=
    GlobalTheory.SS.semistableReduction_zero V K A hA
  obtain ⟨hloc, hcpl⟩ := GlobalTheory.isLocalHom_and_isAdicComplete_of_finite_dvr V V' hfin hinj
  haveI := hcpl
  have hA' : IsAbelianScheme (baseChange K K' A) := Out.TLinPf.isAb_pullback _ A hA
  have hG : IsSemiAbelian G :=
    GlobalTheory.SS.isSemiAbelian_of_abelian_generic_of_torusExt V' K' (baseChange K K' A) hA' G hc hsm hsep hqc he hT
  obtain ⟨V'', _, _, _, hcpl', _, hfin', hinj', hloc', hG', hT'⟩ :=
    GlobalTheory.exists_finite_dvr_torusExtension_specialFibre V' G hG
  obtain ⟨alg, hfd, hcomm', he'⟩ := GlobalTheory.SS.model_finite_ext V K A K' V' hcomm G he V'' hfin' hinj'
  let : Algebra V V'' := ((algebraMap V' V'').comp (algebraMap V V')).toAlgebra
  have : IsScalarTower V V' V'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hfinV : Module.Finite V V'' := Module.Finite.trans V' V''
  have hlocV : IsLocalHom (algebraMap V V'') := by
    haveI := hloc; haveI := hloc'
    exact (inferInstance : IsLocalHom ((algebraMap V' V'').comp (algebraMap V V')))
  exact ⟨V'', FractionRing V'', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, alg, inferInstance, hcomm', hfinV, hlocV, hcpl', baseChange V' V'' G, inferInstance, he', hG', hT'⟩

end GlobalTheory.SS
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels

namespace GlobalTheory.LevelLift

open scoped TensorProduct

theorem exists_field_over (K F M : Type) [Field K] [Field F] [Field M] [Algebra K F] [FiniteDimensional K F]
    (io : K →+* M) :
    ∃ (L₀ : Type) (_ : Field L₀) (_ : Algebra M L₀) (_ : FiniteDimensional M L₀) (io' : F →+* L₀),
      io'.comp (algebraMap K F) = (algebraMap M L₀).comp io := by
  letI : Algebra K M := io.toAlgebra
  haveI : Nontrivial (M ⊗[K] F) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain K M F io.injective
      (algebraMap K F).injective
  obtain ⟨I, hI⟩ := Ideal.exists_maximal (M ⊗[K] F)
  letI : Field (M ⊗[K] F ⧸ I) := Ideal.Quotient.field I
  refine ⟨M ⊗[K] F ⧸ I, inferInstance, inferInstance, inferInstance,
    (Ideal.Quotient.mk I).comp Algebra.TensorProduct.includeRight.toRingHom, ?_⟩
  ext k
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  rw [IsScalarTower.algebraMap_apply K M (M ⊗[K] F), Ideal.Quotient.mk_algebraMap]
  rfl

theorem exists_point_finite_surjective {X Y : Scheme.{0}} (f : X ⟶ Y) (hf : IsFinite f) (hs : Surjective f)
    (L₀ : Type) [Field L₀] (y : Sp L₀ ⟶ Y) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra L₀ L) (_ : FiniteDimensional L₀ L) (x : Sp L ⟶ X),
      x ≫ f = spMap (algebraMap L₀ L) ≫ y := by
  haveI := hf
  haveI := hs
  haveI : Surjective (pullback.snd f y) := inferInstance
  haveI : IsAffine (pullback f y) := isAffine_of_isAffineHom (pullback.snd f y)
  let P := pullback f y
  let g' : Spec Γ(P, ⊤) ⟶ Sp L₀ := P.isoSpec.inv ≫ pullback.snd f y
  haveI : IsFinite g' := inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective g'
  have hφf : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]
    infer_instance
  haveI : Nonempty (Sp L₀) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨p, -⟩ := (pullback.snd f y).surjective (Classical.arbitrary (Sp L₀))
  haveI : Nontrivial Γ(P, ⊤) := PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨P.isoSpec.hom p⟩
  obtain ⟨I, hI⟩ := Ideal.exists_maximal Γ(P, ⊤)
  letI : Field (Γ(P, ⊤) ⧸ I) := Ideal.Quotient.field I
  letI : Algebra L₀ (Γ(P, ⊤) ⧸ I) := ((Ideal.Quotient.mk I).comp φ.hom).toAlgebra
  have hfin : ((Ideal.Quotient.mk I).comp φ.hom).Finite :=
    RingHom.Finite.comp (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective) hφf
  refine ⟨Γ(P, ⊤) ⧸ I, inferInstance, inferInstance, hfin,
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ P.isoSpec.inv ≫ pullback.fst f y, ?_⟩
  rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc P.isoSpec.inv]
  change _ ≫ g' ≫ y = _
  rw [← hφ, ← Category.assoc, ← Spec.map_comp]
  rfl

theorem lift_to_finer_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l l₂ : Level H) (Xo : Moduli Dw l) (Xo₂ : Moduli Dw l₂) (c : Coeff l), 1 ≤ Dw.p + Dw.q → l.Dvd l₂ → l₂.A = l.A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ (x : Sp T.Fr ⟶ Xo.X), x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom) → ∃ (c₂ : Coeff l₂) (la₂ : HeightOneSpectrum (𝓞 c₂.F)) (T' : CDVR) (iT : T.Fr →+* T'.Fr) (φ : T.V →+* T'.V) (e' : ℕ) (io₂ : c₂.F →+* T'.Fr) (e₂ : ℕ) (x₂ : Sp T'.Fr ⟶ Xo₂.X) (r : Xo₂.X ⟶ Xo.X) (_ : SABMap Xo₂.univ.t Xo.univ.t r), 0 < e' ∧ (∀ a : T.Fr, vV T'.V (iT a) = (e' : ℤ) * vV T.V a) ∧ (∀ a : T.V, algebraMap T'.V T'.Fr (φ a) = iT (algebraMap T.V T.Fr a)) ∧ OverLa la₂ T'.V io₂ e₂ ∧ x₂ ≫ Xo₂.s = spMap (io₂.comp (IntermediateField.inclusion c₂.le).toRingHom) ∧ x₂ ≫ r = spMap iT ≫ x := by
  intro E _ _ _ H Dw l l₂ Xo Xo₂ c hpq hd hA la T io e ho x hx
  obtain ⟨r, jK, m, -, -, -, -, -, hrF⟩ :=
    ((GlobalTheory.moduliScheme_levelMaps_heckePoints).2 E H Dw hpq).1 l l₂ Xo Xo₂ hd
  let F₂ : IntermediateField ℚ ℂ := c.F ⊔ IntermediateField.adjoin ℚ {zeta l₂.M'}
  have hle : c.F ≤ F₂ := le_sup_left
  have hpos : 0 < l₂.M' := Nat.lcm_pos (by have := l₂.three_le; omega) l₂.A_pos
  have hint : IsIntegral ℚ (zeta l₂.M') :=
    ((Complex.isPrimitiveRoot_exp l₂.M' hpos.ne').isIntegral hpos).tower_top
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {zeta l₂.M'}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hfin : FiniteDimensional ℚ F₂ := IntermediateField.finiteDimensional_sup _ _
  have hKA : KA l₂ = KA l := by unfold KA; rw [hA]
  let c₂ : Coeff l₂ :=
    { F := F₂, fin := hfin, conj := fun τ a => hle (c.conj τ a),
      zeta_mem := le_sup_right (a := c.F) (IntermediateField.subset_adjoin ℚ _ rfl),
      le := hKA ▸ c.le.trans hle }
  let c' : Coeff l :=
    { F := F₂, fin := hfin, conj := fun τ a => hle (c.conj τ a), zeta_mem := hle c.zeta_mem,
      le := c.le.trans hle }
  obtain ⟨rF, hr1, hr2, hfinr, -, hsurj, -⟩ := hrF c' c₂ rfl
  letI : Algebra c.F F₂ := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ c.F F₂ := IsScalarTower.of_algebraMap_eq fun q => by
    simp
  haveI : FiniteDimensional c.F F₂ := Module.Finite.of_restrictScalars_finite ℚ c.F F₂
  obtain ⟨L₀, _, _, _, io', hio'⟩ := exists_field_over c.F F₂ T.Fr io
  have cond : (spMap (algebraMap T.Fr L₀) ≫ x) ≫ Xo.s =
      spMap io' ≫ spMap (IntermediateField.inclusion c'.le).toRingHom := by
    rw [Category.assoc, hx, Formalism.L2.PjFree.spMap_comp', Formalism.L2.PjFree.spMap_comp']
    congr 1
    ext a
    have h := RingHom.congr_fun hio' (IntermediateField.inclusion c.le a)
    exact h.symm
  let z' : Sp L₀ ⟶ Xo.XF c' := pullback.lift (spMap (algebraMap T.Fr L₀) ≫ x) (spMap io') cond
  obtain ⟨L, _, _, _, x', hx'⟩ := exists_point_finite_surjective rF hfinr hsurj L₀ z'
  letI : Algebra T.Fr L := ((algebraMap L₀ L).comp (algebraMap T.Fr L₀)).toAlgebra
  haveI : IsScalarTower T.Fr L₀ L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FiniteDimensional T.Fr L := Module.Finite.trans L₀ L
  obtain ⟨T', iT, e', ψ, φ, he', hv, hψ, hφ, -⟩ := GlobalTheory.PlaceExtField.exists_cdvr_finite_extension T L
  let io₂ : c₂.F →+* T'.Fr := ψ.toRingHom.comp ((algebraMap L₀ L).comp io')
  haveI : NumberField c₂.F := { to_charZero := inferInstance, to_finiteDimensional := hfin }
  obtain ⟨la₂, e₂, ho₂⟩ := GlobalTheory.LocalDepthCompare.exists_overLa_of_not_charZero (V := T'.V) io₂
    (GlobalTheory.LocalDepthCompare.not_charZero_of_overLa (ho.bc iT he' hv))
  have hid : spMap (IntermediateField.inclusion (le_of_eq (rfl : c'.F = c₂.F))).toRingHom = 𝟙 (Sp c₂.F) := by
    have : (IntermediateField.inclusion (le_of_eq (rfl : c'.F = c₂.F))).toRingHom = RingHom.id _ :=
      RingHom.ext fun _ => rfl
    rw [this]
    exact (congrArg Spec.map (CommRingCat.ofHom_id)).trans (Spec.map_id _)
  have hs : x' ≫ pullback.snd _ _ = spMap ((algebraMap L₀ L).comp io') := by
    have h := congrArg (· ≫ pullback.snd _ _) hx'
    simp only [Category.assoc, hr2, pullback.lift_snd, z'] at h
    rw [hid, Category.comp_id] at h
    rw [h, Formalism.L2.PjFree.spMap_comp']
  have hf : x' ≫ pullback.fst _ _ ≫ r = spMap (algebraMap T.Fr L) ≫ x := by
    have h := congrArg (· ≫ pullback.fst _ _) hx'
    simp only [Category.assoc, hr1, pullback.lift_fst, z'] at h
    rw [h, ← Category.assoc, Formalism.L2.PjFree.spMap_comp']
  refine ⟨c₂, la₂, T', iT, φ, e', io₂, e₂, spMap ψ.toRingHom ≫ x' ≫ pullback.fst _ _, r, m, he', hv, hφ, ho₂,
    ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc x', hs, ← Category.assoc,
      Formalism.L2.PjFree.spMap_comp', Formalism.L2.PjFree.spMap_comp']
  · rw [Category.assoc, Category.assoc, hf, ← Category.assoc, Formalism.L2.PjFree.spMap_comp']
    have hc : ψ.toRingHom.comp (algebraMap T.Fr L) = iT := RingHom.ext fun a => hψ a
    rw [hc]

end GlobalTheory.LevelLift
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.ClosedImmIdeal

theorem ideal_comap_preimage {T W : Scheme.{0}} (i : T ⟶ W) [IsClosedImmersion i]
    (J : W.IdealSheafData) (U : W.affineOpens) :
    (J.comap i).ideal ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩ = Ideal.map (i.app U.1).hom (J.ideal U) := by
  rw [GlobalTheory.Principalise.comapIdealAffine J i U ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩ le_rfl,
    Scheme.Hom.app_eq_appLE]

theorem iSup_preimage_affineOpens {T W : Scheme.{0}} (i : T ⟶ W) :
    ⨆ U : W.affineOpens, i ⁻¹ᵁ U.1 = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]

theorem comap_map_eq {T W : Scheme.{0}} (i : T ⟶ W) [IsClosedImmersion i] (a : T.IdealSheafData) :
    (a.map i).comap i = a := by
  refine le_antisymm (Scheme.IdealSheafData.comap_map_le _ _) ?_
  refine Scheme.IdealSheafData.le_of_iSup_eq_top
    (fun U : W.affineOpens => ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩) (iSup_preimage_affineOpens i) fun U => ?_
  rw [ideal_comap_preimage, Scheme.IdealSheafData.ideal_map_of_isAffineHom,
    Ideal.map_comap_of_surjective _ (i.app_surjective U.1 U.2)]

theorem map_comap_eq {T W : Scheme.{0}} (i : T ⟶ W) [IsClosedImmersion i] (b : W.IdealSheafData)
    (hb : (⊥ : T.IdealSheafData).map i ≤ b) : (b.comap i).map i = b := by
  refine le_antisymm ?_ (Scheme.IdealSheafData.le_map_comap _ _)
  refine Scheme.IdealSheafData.le_of_iSup_eq_top (fun U : W.affineOpens => U)
    (iSup_affineOpens_eq_top W) fun U => ?_
  have h0 := hb U
  rw [Scheme.IdealSheafData.ideal_map_of_isAffineHom] at h0 ⊢
  rw [ideal_comap_preimage, Ideal.comap_map_of_surjective _ (i.app_surjective U.1 U.2)]
  refine sup_le le_rfl (le_trans ?_ h0)
  simp

theorem map_sup_comap_and_comap_map : ∀ (T W : Scheme.{0}) (i : T ⟶ W), IsClosedImmersion i →
    ∀ (a : T.IdealSheafData) (J : W.IdealSheafData),
      (a ⊔ J.comap i).map i = a.map i ⊔ J ∧ (a.map i).comap i = a := by
  intro T W i hi a J
  haveI := hi
  refine ⟨?_, comap_map_eq i a⟩
  have hb : (⊥ : T.IdealSheafData).map i ≤ a.map i ⊔ J :=
    le_sup_of_le_left (Scheme.IdealSheafData.map_mono i bot_le)
  rw [← map_comap_eq i _ hb, Scheme.IdealSheafData.comap_sup, comap_map_eq]

end GlobalTheory.ClosedImmIdeal
end
