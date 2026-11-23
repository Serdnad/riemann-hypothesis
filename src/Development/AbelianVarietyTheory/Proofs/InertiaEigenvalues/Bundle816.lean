module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Formalism.AlgebraicWeights.InertDatumExists
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle298
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle067
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle277
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle013
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle104
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle028
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle806
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle413
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle172
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle096
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle809
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle807
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle020
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertDatumGiven

open scoped TensorProduct

theorem continuous_of_valued_eq {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (s : K →+* K) (hs : ∀ x, Valued.v (s x) = Valued.v x) : Continuous s := by
  have h : Filter.Tendsto s (nhds 0) (nhds 0) := by
    rw [(Valued.hasBasis_nhds_zero K Γ₀).tendsto_iff (Valued.hasBasis_nhds_zero K Γ₀)]
    intro γ _
    refine ⟨γ, trivial, fun x hx => ?_⟩
    simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding] at hx ⊢
    rwa [hs]
  exact continuous_of_continuousAt_zero s (by simpa [ContinuousAt] using h)

theorem exists_inertDatum_of : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal → ¬ IsSplitAt w → ∀ (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L), (∀ x : L, s (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → Formalism.UG.IsUnramInv ϖ s (Formalism.UG.qV (maximalRealSubfield L) v) → ∃ Dv : InertDatum L n v w, Dv.σw = s ∧ Dv.ϖ = ϖ := by
  intro L _ _ _ n v w hov hu hns s ϖ hs hU
  classical
  have hunder : w.under (𝓞 (maximalRealSubfield L)) = v := HeightOneSpectrum.ext hov
  have hw : Formalism.UG.IsInertAt (maximalRealSubfield L) L v w := by
    have h := GlobalTheory.InertPlaceConj.isInertAt_of_not_split w hu hns
    rwa [hunder] at h
  obtain ⟨c, hc, -⟩ := GlobalTheory.LFun.InertChart.existsUnique_isConjAt
    (IsCMField.complexConj L).toAlgHom hw hunder
  obtain ⟨ϖ', hU'⟩ := GlobalTheory.LFun.InertChart.exists_isUnramInv (GlobalTheory.InertDatumExist.isCMExt L) hw hc
  have hsc : s = c := by
    apply DFunLike.coe_injective
    refine GlobalTheory.UnramCompletion.ringHom_ext_of_continuous w (continuous_of_valued_eq s hU.2.1)
      (continuous_of_valued_eq c hU'.2.1) fun k => ?_
    rw [hs, GlobalTheory.LFun.InertChart.conj_algebraMap hc]
    rfl
  subst hsc
  obtain ⟨k, hk, hke⟩ := GlobalTheory.LFun.InertChart.exists_congr_antiJ (n := n) hU (B := 1) (one_mem _)
    (by simp [Formalism.UG.cT, Matrix.map_one])
  have hO : Formalism.UG.Ov L w = Formalism.UG.intL (w.adicCompletion L) := Subring.ext fun _ => Iff.rfl
  let e := (Algebra.TensorProduct.comm (maximalRealSubfield L) L
    (v.adicCompletion (maximalRealSubfield L))).toRingEquiv.trans (GlobalTheory.LFun.InertChart.complEquiv hw hunder)
  refine ⟨⟨e, s, ϖ, k, ?_, hU, ?_, ?_, ?_⟩, rfl, rfl⟩
  · intro x
    show GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _
        (Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom _ x)) =
      s (GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _ x))
    rw [hc]
    congr 1
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · intro x
    rw [GlobalTheory.InertDatumExist.mem_tensInt_iff, GlobalTheory.LFun.InertChart.mem_intLoc_iff hw hunder, hO]
    exact Iff.rfl
  · rw [← hO]; exact hk
  · simpa using hke

end GlobalTheory.InertDatumGiven

end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.Reg


set_option synthInstance.maxHeartbeats 200000 in
theorem sec_eq_zero_of_finite_values :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (h : Rul Xo c), h ∈ sec Xo c a n → (∀ (L : Type) [Field L] [Algebra c.F L] [FiniteDimensional c.F L] (y : FrPt Xo c L), evR Xo c h y = 0) → h = 0 := by
  intro E _ _ _ H Dw l Xo c a n h hh hv
  obtain ⟨hL, -, -, -⟩ := evLaws_genFr_nonempty_comp E H Dw l Xo c
  funext p y
  show h p y = 0

  have key : ∀ m : Ideal p.R, m.IsMaximal → h p y ∈ m := by
    intro m hm
    letI : Field (p.R ⧸ m) := Ideal.Quotient.field m
    haveI : Algebra.FiniteType c.F (p.R ⧸ m) := inferInstance
    haveI : FiniteDimensional c.F (p.R ⧸ m) := finite_of_finite_type_of_isJacobsonRing c.F (p.R ⧸ m)
    obtain ⟨w, hw⟩ := hL.bc p.R (p.R ⧸ m) (Ideal.Quotient.mkₐ c.F m) y
    have e := evR_eq_map_of_test_point hL hh p (Ideal.Quotient.mkₐ c.F m) y w hw
    rw [hv (p.R ⧸ m) w, Ideal.Quotient.mkₐ_eq_mk] at e
    exact Ideal.Quotient.eq_zero_iff_mem.mp e.symm

  have hj : h p y ∈ (⊥ : Ideal p.R).jacobson :=
    Ideal.mem_sInf.mpr fun J hJ => key J hJ.2
  have hrad : (⊥ : Ideal p.R).IsRadical := by
    intro x hx
    obtain ⟨k, hk⟩ := hx
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.mem_bot, ← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hk
    rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    exact p.rad ⟨k, hk⟩
  rw [IsJacobsonRing.out (inferInstance : IsJacobsonRing p.R) hrad] at hj
  exact hj

end GlobalTheory.Reg
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IdemInt

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39

section Val

variable {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R]
  {la : HeightOneSpectrum (𝓞 K)} {u : R → EReal}

theorem nonneg_of_idem (hu : IsVal la u) {x : R} (hx : x * x = x) : 0 ≤ u x := by
  have h := hu.mul x x
  rw [hx] at h
  rcases eq_or_ne (u x) ⊤ with h0 | h0
  · rw [h0]
    exact le_top
  · have hr : (((u x).toReal : ℝ) : EReal) = u x := EReal.coe_toReal h0 (hu.ne_bot x)
    rw [← hr] at h ⊢
    rw [← EReal.coe_add, EReal.coe_eq_coe_iff] at h
    exact EReal.coe_nonneg.mpr (by linarith)

theorem nonneg_smul (hu : IsVal la u) {a : K} (ha : la.valuation K a ≤ 1) {x : R} (hx : 0 ≤ u x) :
    0 ≤ u (a • x) := by
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [zero_smul, hu.zero]
    exact le_top
  · rw [hu.smul a x ha0]
    have hv0 : la.valuation K a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha0
    have hlog : (la.valuation K a).log ≤ 0 := by
      rw [WithZero.log_le_iff_le_exp hv0, WithZero.exp_zero]
      exact ha
    refine add_nonneg ?_ hx
    unfold Formalism.BasicNotions.vAdd
    have hn : (0 : ℤ) ≤ -(la.valuation K a).log := neg_nonneg.mpr hlog
    exact_mod_cast hn

theorem nonneg_sum (hu : IsVal la u) {ι : Type} (s : Finset ι) (x : ι → R) (hx : ∀ i ∈ s, 0 ≤ u (x i)) :
    0 ≤ u (∑ i ∈ s, x i) := by
  refine Finset.sum_induction x (fun y => 0 ≤ u y) (fun a b ha hb => ?_) ?_ hx
  · exact le_trans (le_min ha hb) (hu.add a b)
  · show (0 : EReal) ≤ u 0
    rw [hu.zero]
    exact le_top

end Val

theorem idem_comb_mul_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) (m : ℕ) (χ : Fin m → Rul Xo c) (v : Fin m → c.F), (∀ i, χ i ∈ sec Xo c 0 0 ∧ χ i * χ i = χ i) → (∀ i, la.valuation c.F (v i) ≤ 1) → ∀ f : Rul Xo c, (∀ u ∈ valSet Xo c (algCls Xo c) la, 0 ≤ u f) → ∀ u ∈ valSet Xo c (algCls Xo c) la, 0 ≤ u ((∑ i, v i • χ i) * f) := by
  intro E _ _ _ H Dw l Xo c la m χ v hχ hv f hf u hu
  have hV : IsVal la u := isVal_valSet la u hu
  have h1 : 0 ≤ u (∑ i, v i • χ i) :=
    nonneg_sum hV Finset.univ _ fun i _ => nonneg_smul hV (hv i) (nonneg_of_idem hV (hχ i).2)
  rw [hV.mul]
  exact add_nonneg h1 (hf u hu)

end GlobalTheory.IdemInt
end
end

section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

theorem _root_.GlobalTheory.T.globalLatticeIndexTheorem_of_lengthBoundAtPlaces : GlobalTheory.Published.GlobalArtinReciprocity → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i) (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ), TruncatedSeriesCountingIdentities.admG1 i r → TruncatedSeriesCountingIdentities.admG2 i r ρ π → TruncatedSeriesCountingIdentities.admG3 i r ρ π → TruncatedSeriesCountingIdentities.admG4 i r → TruncatedSeriesCountingIdentities.admG5 i r → TruncatedSeriesCountingIdentities.TameGeneratorConditions i → TruncatedSeriesCountingIdentities.admG6 i r → TruncatedSeriesCountingIdentities.admBK i → LargeLevelLemmas.BlochKatoAnnihilators i → TruncatedSeriesCountingIdentities.FamilyContinuous i r → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i → LargeLevelLemmas.tateH1FinitenessAtPlacesOver i → TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i → LargeLevelLemmas.adm51 i r ρ π → EmbeddingTypes.UnramifiedTrivialH1f i dc → TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc lenRow → TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i r dc e' → EmbeddingTypes.admTB i r π dc cB → TruncatedSeriesCountingIdentities.GlobalLatticeIndexTheorem i ρ π dc lenRow e' cB := by
  first | exact @GlobalTheory.SelmerBoundAtPoint.main | exact GlobalTheory.SelmerBoundAtPoint.main | (intros; apply GlobalTheory.SelmerBoundAtPoint.main <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory.TheoremTB

theorem tb_assembled : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW),
    admitted D HW F → Conclusion5 D → Conclusion4 D HW F := by
  intro D HW F hA h5 l _ K s LL h
  exact ⟨GlobalTheory.T.crystalline_extension_class_bound D HW F hA l K s LL h, GlobalTheory.T.weight_good_reduction_at_prime D HW F hA h5 l K s LL h⟩

end GlobalTheory.TheoremTB
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.valued_map_eq_of_continuous_completionIso_extending : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E'] (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) (w' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E')) (i : w.adicCompletion E ≃+* w'.adicCompletion E'), Continuous i → (∀ x : E, i (algebraMap E _ x) = algebraMap E' _ (algebraMap E E' x)) → ∀ y : w.adicCompletion E, Valued.v (i y) = Valued.v y := by
  first | exact @GlobalTheory.CompletionIsom.valued_v_map | exact GlobalTheory.CompletionIsom.valued_v_map | (intros; apply GlobalTheory.CompletionIsom.valued_v_map <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix

noncomputable section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.PermUnif

variable {g g' : ℕ}

def permCLE (π : Fin g ≃ Fin g') : (Fin g' → ℂ) ≃L[ℂ] (Fin g → ℂ) :=
  (LinearEquiv.funCongrLeft ℂ ℂ π).toContinuousLinearEquiv

@[simp] theorem permCLE_apply (π : Fin g ≃ Fin g') (z : Fin g' → ℂ) (j : Fin g) : permCLE π z j = z (π j) := rfl

@[simp] theorem permCLE_symm_apply (π : Fin g ≃ Fin g') (z : Fin g → ℂ) (j : Fin g') :
    (permCLE π).symm z j = z (π.symm j) := by
  have : permCLE π (fun j' => z (π.symm j')) = z := funext fun j => by simp
  rw [(permCLE π).symm_apply_eq.2 this.symm]

def permP {L : Type} [AddCommGroup L] (π : Fin g ≃ Fin g') (P : L →+ (Fin g → ℂ)) : L →+ (Fin g' → ℂ) where
  toFun a j := P a (π.symm j)
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

@[simp] theorem permP_apply {L : Type} [AddCommGroup L] (π : Fin g ≃ Fin g') (P : L →+ (Fin g → ℂ)) (a : L)
    (j : Fin g') : permP π P a j = P a (π.symm j) := rfl

theorem permCLE_permP {L : Type} [AddCommGroup L] (π : Fin g ≃ Fin g') (P : L →+ (Fin g → ℂ)) (a : L) :
    permCLE π (permP π P a) = P a := funext fun j => by simp

theorem hermForm_perm (π : Fin g ≃ Fin g') (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g' → ℂ) :
    hermForm (Hm.submatrix π.symm π.symm) z w = hermForm Hm (permCLE π z) (permCLE π w) := by
  unfold hermForm
  simp only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply, Pi.star_apply, permCLE_apply]
  rw [← Equiv.sum_comp π]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp π]
  simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem isPeriod_permP {D : Datum H} {ty : Fin g → (E →+* ℂ)} {ty' : Fin g' → (E →+* ℂ)} (π : Fin g ≃ Fin g')
    (hπ : ∀ j, ty' (π j) = ty j) {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) : IsPeriod D ty' (permP π P) := by
  obtain ⟨hlin, hinj, hdisc, hspan, Hm, hH, hpos, hEF⟩ := hP
  refine ⟨fun a x j => ?_, fun x y hxy => hinj (funext fun j => ?_), ?_, ?_,
    ⟨Hm.submatrix π.symm π.symm, hH.submatrix _, fun z hz => ?_, fun x y => ?_⟩⟩
  · rw [permP_apply, permP_apply, hlin, ← hπ, Equiv.apply_symm_apply]
  · have := congrFun hxy (π j)
    simpa using this
  · haveI := hdisc
    refine DiscreteTopology.of_continuous_injective (f := fun v : (permP π P).range =>
      (⟨permCLE π v.1, ?_⟩ : P.range)) ?_ ?_
    · obtain ⟨x, hx⟩ := v.2
      exact ⟨x, by rw [← hx, permCLE_permP]⟩
    · exact Continuous.subtype_mk ((permCLE π).continuous.comp continuous_subtype_val) _
    · intro v w hvw
      exact Subtype.ext ((permCLE π).injective (congrArg Subtype.val hvw))
  · have hr : Set.range (permP π P) = ((permCLE π).symm.toLinearEquiv.restrictScalars ℝ).toLinearMap '' Set.range P := by
      ext v
      constructor
      · rintro ⟨x, rfl⟩
        refine ⟨P x, ⟨x, rfl⟩, ?_⟩
        funext j
        simp
      · rintro ⟨w, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, funext fun j => by simp⟩
    rw [hr, Submodule.span_image, hspan, Submodule.map_top, LinearMap.range_eq_top]
    exact ((permCLE π).symm.toLinearEquiv.restrictScalars ℝ).surjective
  · rw [hermForm_perm]
    refine hpos _ fun h0 => hz (funext fun j => ?_)
    have := congrFun h0 (π.symm j)
    simpa using this
  · rw [hermForm_perm, permCLE_permP, permCLE_permP, hEF]

theorem isHolTo_comp_cle {X : Scheme.{0}} (L : (Fin g' → ℂ) ≃L[ℂ] (Fin g → ℂ)) {y : (Fin g → ℂ) → (Sp ℂ ⟶ X)}
    (hy : IsHolTo Set.univ y) : IsHolTo Set.univ (fun z => y (L z)) := by
  intro U f
  obtain ⟨ho, hd⟩ := hy U f
  have hs : {b ∈ (Set.univ : Set (Fin g' → ℂ)) | ⊤ ≤ y (L b) ⁻¹ᵁ U} = L ⁻¹' {b ∈ Set.univ | ⊤ ≤ y b ⁻¹ᵁ U} := by
    ext b
    simp
  rw [hs]
  exact ⟨ho.preimage L.continuous, hd.comp L.differentiableOn (fun b hb => hb)⟩

theorem isDerivAt0_comp_cle {X : Scheme.{0}} (L : (Fin g' → ℂ) ≃L[ℂ] (Fin g → ℂ)) (y : (Fin g → ℂ) → (Sp ℂ ⟶ X))
    (w : Fin g' → ℂ) (v : Sp (DualNumber ℂ) ⟶ X) :
    IsDerivAt0 (fun z => y (L z)) w v ↔ IsDerivAt0 y (L w) v := by
  unfold IsDerivAt0
  simp only [map_zero]
  refine and_congr Iff.rfl (forall_congr' fun U => forall_congr' fun h => forall_congr' fun f => ?_)
  rw [show (fun z => valAt' (y (L z)) U f) = (fun z => valAt' (y z) U f) ∘ L from rfl, L.comp_right_fderiv,
    map_zero]
  rfl

theorem isometry_of_point_eq_perm : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g g' : ℕ}
    {ty : Fin g → (E →+* ℂ)} {ty' : Fin g' → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty) (F' : FamilyUnif Xo σ' ty')
    (hpq : 1 ≤ Dw.p + Dw.q) (hσ : σ' (baseKA l).ρ = H.rt0) (hty : IsTypeFn H Dw.p Dw.q ty)
    (hty' : IsTypeFn H Dw.p Dw.q ty') (π : Fin g ≃ Fin g') (hπ : ∀ j, ty' (π j) = ty j)
    (k : Fin F.n) (k' : Fin F'.n) (P : (F.Di k).La →+ (Fin g → ℂ)) (P' : (F'.Di k').La →+ (Fin g' → ℂ))
    (hP : IsPeriod (F.Di k) ty P) (hP' : IsPeriod (F'.Di k') ty' P') (h : F.u k P = F'.u k' P'), ∃ gam : (F.Di k).La ≃ₗ[𝓞 E] (F'.Di k').La, (∀ a b, (F'.Di k').EF (gam a) (gam b) = (F.Di k).EF a b) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), ∃ x, gam (F.t k a) = F'.t k' a + l.M • x := by
  intro E _ _ _ H Dw l Xo σ' g g' ty ty' F F' hpq hσ hty hty' π hπ k k' P P' hP hP' h
  have hL : ∀ a, permCLE π (permP π P a) = P a := permCLE_permP π P
  have hd := F.ex_diff k P hP
  have key := GlobalTheory.UnifPoint.point_eq_iff_isometry_closed GlobalTheory.thetaUnifAV_all
    GlobalTheory.firstFiveLaws.1 E H Dw l Xo σ' g' ty' hpq hσ hty' (F.Di k) (F'.Di k') (F.t k) (F'.t k') (permP π P) P'
    (F.u k P) (F'.u k' P') (fun z => F.ex k P (permCLE π z)) (F'.ex k' P')
  obtain ⟨gam, -, hEF, hM, -, -⟩ := (key (by
    refine ⟨F.over_σ k P hP, isPeriod_permP π hπ hP, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro z w
      rw [map_add (f := _)]
      exact F.ex_add k P hP _ _
    · exact (F.ex_onto k P hP).comp (permCLE π).surjective
    · exact isHolTo_comp_cle (permCLE π) (y := fun z => (F.ex k P z).left) (GlobalTheory.ClassUniq.isHolTo_ex F k P hP)
    · intro w
      obtain ⟨v, hv, hu⟩ := hd.1 (permCLE π w)
      exact ⟨v, (isDerivAt0_comp_cle (permCLE π) (fun z => (F.ex k P z).left) w v.left).2 hv,
        fun v' hv' => hu v' ((isDerivAt0_comp_cle (permCLE π) (fun z => (F.ex k P z).left) w v'.left).1 hv')⟩
    · intro v hv
      have h0 : (permCLE π) 0 = 0 := map_zero _
      have hv0 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (F.ex k P 0).left := by
        rw [← h0]; exact hv
      obtain ⟨w, hw, hu⟩ := hd.2 v hv0
      refine ⟨(permCLE π).symm w, (isDerivAt0_comp_cle (permCLE π) (fun z => (F.ex k P z).left) _ v.left).2 (by
        rwa [(permCLE π).apply_symm_apply]), fun w' hw' => ?_⟩
      rw [← hu _ ((isDerivAt0_comp_cle (permCLE π) (fun z => (F.ex k P z).left) w' v.left).1 hw'),
        (permCLE π).symm_apply_apply]
    · intro z
      refine (F.ex_ker k P hP (permCLE π z)).trans ⟨?_, ?_⟩
      · rintro ⟨x, hx⟩
        refine ⟨x, funext fun j => ?_⟩
        have := congrFun hx (π.symm j)
        simpa using this
      · rintro ⟨x, rfl⟩
        exact ⟨x, (hL x).symm⟩
    · intro a z
      have e : permCLE π (fun j => ty' j (a : E) * z j) = fun j => ty j (a : E) * permCLE π z j :=
        funext fun j => by simp [hπ]
      rw [e]
      exact F.ex_lin k P hP a (permCLE π z)
    · intro n a a₂ c hn hc
      rw [map_smul, map_smul, hL, hL]
      exact F.ex_weil k P hP n a a₂ c hn hc
    · intro a ha
      rw [map_smul, hL]
      exact F.ex_eta k P hP a ha
    · intro a
      rw [map_smul, hL]
      exact F.ex_etaA k P hP a) (by
    exact ⟨F'.over_σ k' P' hP', hP', ⟨F'.ex_add k' P' hP', F'.ex_onto k' P' hP', GlobalTheory.ClassUniq.isHolTo_ex F' k' P' hP',
      (F'.ex_diff k' P' hP').1, (F'.ex_diff k' P' hP').2⟩, F'.ex_ker k' P' hP', F'.ex_lin k' P' hP',
      F'.ex_weil k' P' hP', F'.ex_eta k' P' hP', F'.ex_etaA k' P' hP'⟩)).1 h
  exact ⟨gam, hEF, hM⟩

end GlobalTheory.PermUnif
end
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.QForm (QVal IsQ bOf)

theorem _root_.GlobalTheory.T.nontrivial_X_of_not_range_subset_abLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (S : Scheme.{0}) (t₀ : SAB H S) (T T' : Formalism.L2.Pj.CDVR) (g : T.V →+* T'.V) (y : Sp T.V ⟶ S) (t : SAB H (Sp T'.V)) (_ : SABMap t t₀ (spMap g ≫ y)) (P : PELUnif (IsLocalRing.maximalIdeal T'.V) t), Function.Injective g → g.Finite → ¬ Set.range y ⊆ abLocus t₀.G → Nontrivial P.D.toPre.X := by
  first | exact @GlobalTheory.BadReductionLattice.nontrivial_of_not_range_subset_abLocus | exact GlobalTheory.BadReductionLattice.nontrivial_of_not_range_subset_abLocus | (intros; apply GlobalTheory.BadReductionLattice.nontrivial_of_not_range_subset_abLocus <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.QForm (QVal IsQ bOf)

theorem _root_.GlobalTheory.T.exists_cdvr_extension_qkPoints_rational : ∀ (T : Formalism.L2.Pj.CDVR) (D : DegPre T.V), D.TauBimult → ∀ N : ℕ, 0 < N → ∀ ϖ : T.V, Irreducible ϖ → ∃ (T' : Formalism.L2.Pj.CDVR) (g : T.V →+* T'.V) (ϖ' : T'.V) (e : ℕ), Function.Injective g ∧ g.Finite ∧ Irreducible ϖ' ∧ N ∣ e ∧ Associated (g ϖ) (ϖ' ^ e) ∧ ∀ (D' : DegPre T'.V) (_ : IsPullDeg g D D'), D'.TauBimult → ∀ k : ℕ, k ∣ N → ∀ q : QkPt D' (AlgebraicClosure (FractionRing T'.V)) k, ∃ p : QkPt D' (FractionRing T'.V) k, QkExt (algebraMap (FractionRing T'.V) (AlgebraicClosure (FractionRing T'.V))) p q := by
  first | exact @GlobalTheory.QkRationalExt.exists_cdvr_ext_rational | exact GlobalTheory.QkRationalExt.exists_cdvr_ext_rational | (intros; apply GlobalTheory.QkRationalExt.exists_cdvr_ext_rational <;> assumption)
end
