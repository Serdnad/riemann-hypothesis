module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTaylorShiftFrobeniusTwoVariableCompatible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle308
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle639
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle564
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle519
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle516
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle637
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle180
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle631
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleBasisOfFCrystal
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConnPhiExtensionGeneratorEqZeta
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle640
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle626
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem exists_eq_of_coeff_box_eq_zero {R : Type} [CommRing R] (i n : ℕ) (D : R⟦X⟧⟦X⟧)
    (h : ∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' D) = 0) :
    ∃ A B : R⟦X⟧⟦X⟧, D = X ^ (i + 1) * A + C (X ^ (n + 1)) * B := by
  classical
  obtain ⟨B, hlow⟩ : ∃ B : R⟦X⟧⟦X⟧, ∀ k ≤ i, X ^ (n + 1) * coeff k B = coeff k D := by
    refine ⟨mk fun k => mk fun m => coeff (m + (n + 1)) (coeff k D), fun k hk => ?_⟩
    ext m
    rw [coeff_X_pow_mul', coeff_mk]
    split_ifs with hm
    · rw [coeff_mk, Nat.sub_add_cancel hm]
    · exact (h k hk m (by omega)).symm
  have hdvd : (X : R⟦X⟧⟦X⟧) ^ (i + 1) ∣ D - C (X ^ (n + 1)) * B := by
    rw [X_pow_dvd_iff]
    intro k hk
    rw [map_sub, coeff_C_mul, hlow k (by omega), sub_self]
  obtain ⟨A, hA⟩ := hdvd
  exact ⟨A, B, by rw [← hA]; ring⟩

theorem coeff_frob2_congr_box : ∀ (l : ℕ) [Fact l.Prime] (K : Type) [NormedField K] (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) → φ₂ X = (C X + X) ^ l - C (X ^ l) → ∀ (i n : ℕ) (G H : K⟦X⟧⟦X⟧), (∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' G) = coeff n' (coeff i' H)) → coeff n (coeff i (φ₂ G)) = coeff n (coeff i (φ₂ H)) := by
  intro l _ K _ φ₂ hC hX i n G H h
  obtain ⟨A, B, hAB⟩ := exists_eq_of_coeff_box_eq_zero i n (G - H) (fun i' hi' n' hn' => by
    rw [map_sub, map_sub, h i' hi' n' hn', sub_self])
  obtain ⟨c, hc⟩ : (X : K⟦X⟧⟦X⟧) ∣ φ₂ X := by
    rw [hX, map_pow]
    have hd := sub_dvd_pow_sub_pow (C X + X : K⟦X⟧⟦X⟧) (C X) l
    rwa [add_sub_cancel_left] at hd
  have hl : 1 ≤ l := (Fact.out : Nat.Prime l).one_lt.le
  have e1 : φ₂ (X ^ (i + 1) * A) = X ^ (i + 1) * (c ^ (i + 1) * φ₂ A) := by
    rw [map_mul, map_pow, hc]
    ring
  have e2 : φ₂ (C (X ^ (n + 1)) * B) = C (X ^ (l * (n + 1))) * φ₂ B := by
    rw [map_mul, hC, map_pow, frob_X, ← pow_mul]
  have hz : coeff n (coeff i (φ₂ (G - H))) = 0 := by
    rw [hAB, map_add (f := _), e1, e2, map_add (f := _), map_add (f := _), coeff_X_pow_mul',
      if_neg (show ¬ (i + 1 ≤ i) by omega), map_zero, zero_add, coeff_C_mul, coeff_X_pow_mul',
      if_neg (show ¬ (l * (n + 1) ≤ n) by nlinarith)]
  rwa [map_sub, map_sub, map_sub, sub_eq_zero] at hz

end GlobalTheory.CrysPrism
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_taylorShift_frobenius_twoVariable_compatible : ∀ (l : ℕ) [Fact l.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[l] K], ∃ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) ∧ (∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f)) ∧ (∀ f : K⟦X⟧, φ₂ (sh f) = sh (frob K l f)) := by
  first | exact @GlobalTheory.TaylorShift.shift_frob_exists | exact GlobalTheory.TaylorShift.shift_frob_exists | (intros; apply GlobalTheory.TaylorShift.shift_frob_exists <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module

namespace GlobalTheory.UseLoc

theorem descUr_entry (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw)
    (a b : Fin k) :
    (mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (locOC C M)) g a b =
      IntermediateField.inclusion C.le ((Br.loc D.nbr i w hw M) g a b) := by
  simp only [mapM, locOC, Br.loc, Br.locM, MonoidHom.coe_comp, Function.comp_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
  rfl



theorem descUr_mem : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (I : Subgroup (Br.G D.nbr i w hw))
    (z : Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T),
    (fun g => liftQ C.le k (z g)) ∈ Z1urD (latC C (locOC C M)) I → z ∈ Z1urD (Br.locLat D.nbr i w hw M) I := by
  intro D i w hw C k M I z hz
  obtain ⟨r, hrl, hr1, hrO⟩ :=
    GlobalTheory.CoefRetraction.exists_integral_retraction (D.nd.l i) (D.nbr i w hw).LL C.LL C.le
  have hri : ∀ a, r (IntermediateField.inclusion C.le a) = a := fun a => by
    have := hrl a 1
    simpa [hr1] using this
  obtain ⟨x', hx'⟩ := hz
  obtain ⟨v', rfl⟩ := Submodule.Quotient.mk_surjective _ x'
  refine ⟨Submodule.Quotient.mk (fun j => r (v' j)), fun g hg => ?_⟩
  have h : liftQ C.le k (z g) = actD (latC C (locOC C M)) g (Submodule.Quotient.mk v') - Submodule.Quotient.mk v' := hx' g hg
  obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective (Br.locLat D.nbr i w hw M).T (z g)
  rw [← hu] at h ⊢
  have h1 : (Submodule.Quotient.mk (p := stdG ↥(OL C.LL) ↥C.LL.1 k) (incV C.le k u)) =
      Submodule.Quotient.mk (p := stdG ↥(OL C.LL) ↥C.LL.1 k) ((repV C (locOC C M)) g v') -
        Submodule.Quotient.mk (p := stdG ↥(OL C.LL) ↥C.LL.1 k) v' := h
  rw [← Submodule.Quotient.mk_sub, Submodule.Quotient.eq] at h1
  show (Submodule.Quotient.mk (p := stdG ↥(OL (D.nbr i w hw).LL) ↥(D.nbr i w hw).LL.1 k) u) =
      Submodule.Quotient.mk (p := stdG ↥(OL (D.nbr i w hw).LL) ↥(D.nbr i w hw).LL.1 k) ((matRep (Br.loc D.nbr i w hw M)) g (fun j => r (v' j))) -
        Submodule.Quotient.mk (p := stdG ↥(OL (D.nbr i w hw).LL) ↥(D.nbr i w hw).LL.1 k) (fun j => r (v' j))
  rw [← Submodule.Quotient.mk_sub, Submodule.Quotient.eq]
  obtain ⟨t, ht⟩ := h1
  refine ⟨fun j => ⟨r (t j), hrO _ (t j).2⟩, ?_⟩
  funext j
  have hj := congrFun ht j
  have hrl' : ∀ a x, r (IntermediateField.inclusion C.le a * x) = a * r x := hrl
  have hj' : ((t j : ↥(OL C.LL)) : ↥C.LL.1) = IntermediateField.inclusion C.le (u j) -
      ((mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (locOC C M) g).mulVec v' j - v' j) := hj
  change r ((t j : ↥(OL C.LL)) : ↥C.LL.1) =
    u j - ((Br.loc D.nbr i w hw M g).mulVec (fun j => r (v' j)) j - r (v' j))
  rw [hj', map_sub, map_sub, hri]
  congr 2

  simp only [Matrix.mulVec, dotProduct, map_sum, descUr_entry, hrl']

end GlobalTheory.UseLoc
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CellDec

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

namespace ChangeVar

theorem locallyCompact_GA_chv : LocallyCompactSpace (GA E n) :=
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (Ad E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → Ad E))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem secondCountable_GA_chv : SecondCountableTopology (GA E n) :=
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Ad E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → Ad E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  Units.isEmbedding_embedProduct.secondCountableTopology

theorem isClosed_NA : IsClosed ((NA E n : Subgroup (GA E n)) : Set (GA E n)) := by
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  have hv : Continuous fun g : GA E n => (g : Matrix (Fin n) (Fin n) (Ad E)) := Units.continuous_val
  have : ((NA E n : Subgroup (GA E n)) : Set (GA E n)) =
      (⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_ : j < i), {g : GA E n | (g : Matrix (Fin n) (Fin n) (Ad E)) i j = 0}) ∩
      ⋂ i : Fin n, {g : GA E n | (g : Matrix (Fin n) (Fin n) (Ad E)) i i = 1} := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    exact GlobalTheory.SmGL.mem_unipB (Ad E)
  rw [this]
  refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => ?_)
    (isClosed_iInter fun i => ?_)
  · exact isClosed_eq (hv.matrix_elem i j) continuous_const
  · exact isClosed_eq (hv.matrix_elem i i) continuous_const

theorem NE_le_NA : NE E n ≤ NA E n := by
  rintro _ ⟨u, hu, rfl⟩
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB E).1 hu
  refine (GlobalTheory.SmGL.mem_unipB (Ad E)).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · change algebraMap E (Ad E) ((u : Matrix (Fin n) (Fin n) E) i j) = 0
    rw [h1 i j hij, map_zero]
  · change algebraMap E (Ad E) ((u : Matrix (Fin n) (Fin n) E) i i) = 1
    rw [h2 i, map_one]

theorem countable_NE : Countable (NE E n) := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (GL (Fin n) E) :=
    Function.Injective.countable (f := fun (g : GL (Fin n) E) (i j : Fin n) => (g : Matrix (Fin n) (Fin n) E) i j)
      fun _ _ h => Units.ext (Matrix.ext fun i j => congrFun (congrFun h i) j)
  exact ((Set.countable_range (ratGL E n)).mono (by rintro _ ⟨u, -, rfl⟩; exact ⟨u, rfl⟩)).to_subtype

theorem tl_inv_conj_mem (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) {u : GA E n} (hu : u ∈ NA E n) :
    (tl n ϖ l)⁻¹ * u * tl n ϖ l ∈ NA E n := by
  have h := diagT_conj_mem (n := n) (R := Ad E)
    (fun i => finId E (adl ϖ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l)))⁻¹ hu
  rw [map_inv, inv_inv, ← tl_eq_diagT] at h
  exact h

end ChangeVar

open ChangeVar

theorem lintegral_tl_inv_mul : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) [MeasurableSpace (GA E n)] [BorelSpace (GA E n)]
    (μ : Measure (GA E n)) [μ.IsHaarMeasure] (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ),
    (∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) → ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (𝓕 : Set (GA E n)),
    IsFundamentalDomain (GlobalTheory.CellDec.NE E n) 𝓕 μ → ∀ F : GA E n → ℝ≥0∞, Measurable F →
    (∀ u ∈ GlobalTheory.CellDec.NA E n, ∀ g, F (u * g) = F g) →
    ∫⁻ g in 𝓕, F ((GlobalTheory.CellDec.tl n ϖ l)⁻¹ * g) ∂μ = ENNReal.ofReal (GlobalTheory.CellDec.dinv n l) * ∫⁻ g in 𝓕, F g ∂μ := by
  intro E _ _ n _ _ μ _ ϖ hϖ l 𝓕 h𝓕 F hF hinv
  haveI : LocallyCompactSpace (GA E n) := locallyCompact_GA_chv
  haveI : SecondCountableTopology (GA E n) := secondCountable_GA_chv
  haveI : SigmaCompactSpace (GA E n) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SFinite μ := inferInstance
  haveI : MeasurableMul₂ (GA E n) := inferInstance
  haveI : MeasurableInv (GA E n) := inferInstance
  haveI : LocallyCompactSpace (NA E n) := isClosed_NA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (NA E n) :=
    isClosed_NA.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  haveI : SigmaCompactSpace (NA E n) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI := countable_NE (E := E) (n := n)
  set ν : Measure (NA E n) := Measure.haar with hν
  haveI : ν.IsInvInvariant := GlobalTheory.T.haar_measure_inverse_invariant E n ν
  set_option synthInstance.maxHeartbeats 200000 in
    haveI : SFinite ν := inferInstance
  obtain ⟨D, hD, hD0, hDtop⟩ := GlobalTheory.T.exists_fundamentalDomain_rational_upperUnitriangular E n ν
  set t := tl n ϖ l with ht

  let cM : NA E n ≃* NA E n :=
    { toFun := fun u => ⟨t * u * t⁻¹, tl_conj_mem ϖ l u.2⟩
      invFun := fun u => ⟨t⁻¹ * u * t, tl_inv_conj_mem ϖ l u.2⟩
      left_inv := fun u => Subtype.ext (by simp only; group)
      right_inv := fun u => Subtype.ext (by simp only; group)
      map_mul' := fun u v => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hcM : ∀ u : NA E n, ((cM u : NA E n) : GA E n) = t * u * t⁻¹ := fun _ => rfl
  let c : NA E n ≃ᵐ NA E n :=
    { toEquiv := cM.toEquiv
      measurable_toFun := ((measurable_mul_const _).comp ((measurable_const_mul _).comp measurable_subtype_coe)).subtype_mk
      measurable_invFun := ((measurable_mul_const _).comp ((measurable_const_mul _).comp measurable_subtype_coe)).subtype_mk }
  have hmod : ∀ A, MeasurableSet A → ν (c ⁻¹' A) = ENNReal.ofReal (dinv n l) * ν A := by
    intro A hA
    rw [← GlobalTheory.T.haar_measure_uniformizer_translate E n ν ϖ hϖ l A hA]
    congr 1
    ext u
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    constructor
    · intro h; exact ⟨_, h, rfl⟩
    · rintro ⟨a, ha, hau⟩
      convert ha
      exact Subtype.ext hau.symm
  have hmap : Measure.map c ν = ENNReal.ofReal (dinv n l) • ν := by
    ext A hA
    rw [Measure.map_apply c.measurable hA, hmod A hA, Measure.smul_apply, smul_eq_mul]
  have hmod' : ∀ A, ν (c ⁻¹' A) = ENNReal.ofReal (dinv n l) * ν A := fun A => by
    rw [← c.map_apply, hmap, Measure.smul_apply, smul_eq_mul]

  set Γ : Subgroup (NA E n) := (NE E n).subgroupOf (NA E n) with hΓ
  set Γ' : Subgroup (NA E n) := Γ.comap cM.toMonoidHom with hΓ'
  have hΓmap : Γ.map (NA E n).subtype = NE E n := by
    rw [hΓ, Subgroup.subgroupOf_map_subtype, inf_of_le_left NE_le_NA]
  have hmemΓ' : ∀ x : GA E n, x ∈ Γ'.map (NA E n).subtype ↔ t * x * t⁻¹ ∈ NE E n := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Subgroup.mem_subgroupOf.1 (Subgroup.mem_comap.1 hy)
    · intro hx
      have hxN : x ∈ NA E n := by
        have := tl_inv_conj_mem ϖ l (NE_le_NA hx)
        rwa [show t⁻¹ * (t * x * t⁻¹) * t = x by group] at this
      exact ⟨⟨x, hxN⟩, Subgroup.mem_comap.2 (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  haveI : Countable Γ := Function.Injective.countable (f := fun g : Γ => (⟨(g : NA E n), g.2⟩ : NE E n))
    fun a b h => Subtype.ext (Subtype.ext (congrArg (fun z : NE E n => (z : GA E n)) h))
  haveI : Countable Γ' := Function.Injective.countable (f := fun g : Γ' => (⟨cM g, g.2⟩ : Γ))
    fun a b h => Subtype.ext (cM.injective (congrArg (fun z : Γ => (z : NA E n)) h))

  have hD' : IsFundamentalDomain Γ' (c ⁻¹' D) ν := by
    have hsymm : ∀ u : NA E n, ((cM.symm u : NA E n) : GA E n) = t⁻¹ * u * t := fun _ => rfl
    have hc : ∀ u : NA E n, c u = cM u := fun _ => rfl
    refine hD.preimage_of_equiv (f := c) ⟨c.measurable.aemeasurable, by rw [hmap]; exact Measure.smul_absolutelyContinuous⟩
      (e := fun g : Γ => (⟨cM.symm g, Subgroup.mem_comap.2 (by
          rw [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]; exact g.2)⟩ : Γ'))
      ⟨fun a b h => Subtype.ext (cM.symm.injective (congrArg (fun z : Γ' => (z : NA E n)) h)),
        fun g => ⟨⟨cM g, g.2⟩, Subtype.ext (by simp only [MulEquiv.symm_apply_apply])⟩⟩ ?_
    intro g x
    apply Subtype.ext
    simp only [Subgroup.smul_def, smul_eq_mul, hc, hcM, hsymm, Subgroup.coe_mul]
    group
  have h𝓕Γ : IsFundamentalDomain (Γ.map (NA E n).subtype) 𝓕 μ := by rw [hΓmap]; exact h𝓕
  have h𝓕' : IsFundamentalDomain (Γ'.map (NA E n).subtype) ((fun g => t * g) ⁻¹' 𝓕) μ := by
    refine h𝓕.preimage_of_equiv (f := fun g => t * g) (measurePreserving_mul_left μ t).quasiMeasurePreserving
      (e := fun g : NE E n => (⟨t⁻¹ * g * t, (hmemΓ' _).2 (by convert g.2 using 1; group)⟩ : Γ'.map (NA E n).subtype))
      ⟨fun a b h => Subtype.ext (by
          have h' := congrArg (fun z : Γ'.map (NA E n).subtype => t * (z : GA E n) * t⁻¹) h
          simpa [mul_assoc] using h'),
        fun y => ⟨⟨t * y * t⁻¹, (hmemΓ' y).1 y.2⟩, Subtype.ext (by simp only; group)⟩⟩ ?_
    intro g x
    change t * ((t⁻¹ * g * t) * x) = (g : GA E n) * (t * x)
    group
  have key := GlobalTheory.T.lintegral_quotient_comparison_fundamentalDomains μ (NA E n) ν Γ Γ' D (c ⁻¹' D) hD hD' 𝓕 ((fun g => t * g) ⁻¹' 𝓕) h𝓕Γ h𝓕' F hF
    (fun h g => hinv h h.2 g)
  rw [hmod'] at key
  have hchg : ∫⁻ g in 𝓕, F (t⁻¹ * g) ∂μ = ∫⁻ g in (fun g => t * g) ⁻¹' 𝓕, F g ∂μ := by
    rw [← (measurePreserving_mul_left μ t).setLIntegral_comp_preimage_emb
      (MeasurableEquiv.mulLeft t).measurableEmbedding (fun b => F (t⁻¹ * b)) 𝓕]
    simp only [inv_mul_cancel_left]
  rw [hchg]
  refine ((ENNReal.mul_right_inj hD0.ne' hDtop.ne).1 ?_)
  rw [← key]
  ring

end GlobalTheory.CellDec
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan

theorem _root_.GlobalTheory.T.exists_goodRankinSelbergPlaceSet_superset_totallyComplex : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (T : Finset (HeightOneSpectrum (𝓞 E))), ∃ T' : Finset (HeightOneSpectrum (𝓞 E)), T ⊆ T' ∧ IsGood T' := by
  first | (exact @GlobalTheory.RSNonvan.exists_isGood_superset_all) | (exact GlobalTheory.RSNonvan.exists_isGood_superset_all) | (intros; apply GlobalTheory.RSNonvan.exists_isGood_superset_all  <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal

noncomputable section

namespace GlobalTheory.BKGal.HatVal

section IntegralSpan

variable {l : ℕ} [Fact l.Prime]

theorem one_mem_filD_zero : (1 : Per.BdR l) ∈ Per.FilD l 0 := by
  have h0 : (1 : Per.BdRp l) ∈ Per.FilP l 0 := by
    rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, ← map_one (algebraMap (Per.AinfP l) (Per.BdRp l)),
      GlobalTheory.RingIface.ev_alg, Ideal.Quotient.eq_zero_iff_mem]
    simp
  have h1 := GlobalTheory.RingIface.alg_mem_FilD_nat l h0
  rwa [map_one, Nat.cast_zero] at h1

theorem algebraMap_mem_filD_zero (u : Per.BdRp l) :
    algebraMap (Per.BdRp l) (Per.BdR l) u ∈ Per.FilD l 0 := by
  rw [← mul_one (algebraMap (Per.BdRp l) (Per.BdR l) u), ← Algebra.smul_def]
  exact Submodule.smul_mem _ u one_mem_filD_zero

theorem equivFinsuppOfBasisLeft_map_id {O B B' ι : Type} [CommRing O] [Algebra ℤ_[l] O]
    [CommRing B] [CommRing B'] [Algebra ℤ_[l] B] [Algebra ℤ_[l] B']
    [DecidableEq ι] (b : Module.Basis ι ℤ_[l] O) (g : B →ₐ[ℤ_[l]] B') (r : O ⊗[ℤ_[l]] B) (k : ι) :
    TensorProduct.equivFinsuppOfBasisLeft b (Algebra.TensorProduct.map (AlgHom.id O O) g r) k =
      g (TensorProduct.equivFinsuppOfBasisLeft b r k) := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul o β => simp [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

theorem equivFinsuppOfBasisRight_map_id {O R R' M κ : Type} [CommRing O] [CommRing R] [CommRing R']
    [Algebra O R] [Algebra O R'] [AddCommGroup M] [Module O M]
    [DecidableEq κ] (b : Module.Basis κ O M) (f : R →ₐ[O] R') (w : R ⊗[O] M) (j : κ) :
    TensorProduct.equivFinsuppOfBasisRight b (TensorProduct.map f.toLinearMap LinearMap.id w) j =
      f (TensorProduct.equivFinsuppOfBasisRight b w j) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => simp [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

theorem mem_span_filD_zero_of_iotaO_eq {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O]
    (C : GlobalTheory.MemLoc.Core l) (r : OB l O) (s : OD l O) (h : iotaO O C r = dRO l O s) :
    r ∈ Submodule.span O
      {u : OB l O | ∃ β : Per.Bcris l, C.ι β ∈ Per.FilD l 0 ∧ u = (1 : O) ⊗ₜ[ℤ_[l]] β} := by
  classical
  let b := Module.Free.chooseBasis ℤ_[l] O
  have hr : r = (TensorProduct.equivFinsuppOfBasisLeft b r).sum fun k β => b k ⊗ₜ[ℤ_[l]] β := by
    rw [← TensorProduct.equivFinsuppOfBasisLeft_symm_apply, LinearEquiv.symm_apply_apply]
  rw [hr, Finsupp.sum]
  refine Submodule.sum_mem _ (fun k _ => ?_)
  have hk : C.ι (TensorProduct.equivFinsuppOfBasisLeft b r k) ∈ Per.FilD l 0 := by
    have h1 := equivFinsuppOfBasisLeft_map_id b (iotaZ C) r k
    have h2 := equivFinsuppOfBasisLeft_map_id b (bdRpToBdR l) s k
    have h3 : Algebra.TensorProduct.map (AlgHom.id O O) (iotaZ C) r =
        Algebra.TensorProduct.map (AlgHom.id O O) (bdRpToBdR l) s := h
    rw [h3, h2] at h1
    have h4 : C.ι (TensorProduct.equivFinsuppOfBasisLeft b r k) =
        algebraMap (Per.BdRp l) (Per.BdR l) (TensorProduct.equivFinsuppOfBasisLeft b s k) := h1.symm
    rw [h4]
    exact algebraMap_mem_filD_zero _
  have h5 : b k ⊗ₜ[ℤ_[l]] (TensorProduct.equivFinsuppOfBasisLeft b r k) =
      b k • ((1 : O) ⊗ₜ[ℤ_[l]] (TensorProduct.equivFinsuppOfBasisLeft b r k)) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h5]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hk, rfl⟩)

end IntegralSpan

theorem mem_span_filD_zero_of_integral : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O]
    [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K]
    (T : LocLat (Gl l) ℚ_[l] K O) (C : GlobalTheory.MemLoc.Core l) (w : TW (OB l O) T),
    TWincl (iotaO O C) T w ∈ LinearMap.range (TWincl (dRO l O) T) →
      w ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T),
        C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  intro l _ O K _ _ _ _ _ _ _ T C w hw
  classical
  obtain ⟨z, hz⟩ := hw
  haveI := T.L.free
  let bT := Module.Free.chooseBasis O ↥T.L.T
  have hw' : w = (TensorProduct.equivFinsuppOfBasisRight bT w).sum fun j r => r ⊗ₜ[O] bT j := by
    rw [← TensorProduct.equivFinsuppOfBasisRight_symm_apply, LinearEquiv.symm_apply_apply]
  rw [hw', Finsupp.sum]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  have hj : iotaO O C (TensorProduct.equivFinsuppOfBasisRight bT w j) =
      dRO l O (TensorProduct.equivFinsuppOfBasisRight bT z j) := by
    rw [← equivFinsuppOfBasisRight_map_id, ← equivFinsuppOfBasisRight_map_id]
    exact (congrArg (fun y => TensorProduct.equivFinsuppOfBasisRight bT y j) hz).symm
  have hr := mem_span_filD_zero_of_iotaO_eq C _ _ hj
  have hm := Submodule.mem_map_of_mem (f := (TensorProduct.mk O (OB l O) ↥T.L.T).flip (bT j)) hr
  rw [Submodule.map_span] at hm
  refine Submodule.span_mono ?_ hm
  rintro _ ⟨u, ⟨β, hβ, rfl⟩, rfl⟩
  exact ⟨β, bT j, hβ, rfl⟩

end GlobalTheory.BKGal.HatVal
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.galoisMatrix_eq_crystal_changeOfBasis_value : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : Lat a O K ϖ) (I : Ident t ϖ P T), letI := zlLat T; ∀ (E : FCrys l ↥(OL (ϖ.field a))) (jA : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T)), Realises (ϖ.field a) E (ainfObj _) (ainfId _) ↥T.L.T (actZ T) jA → (∀ y : TW (OW l O) T, (∃ x : E.M (ϖ.prism a), y = kappa T (jA (E.tr (ϖ.toAinf a) x))) ↔ ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) → ∀ (oE : O → FHom E E), (∀ (c : O) (x : E.M (ainfObj (ϖ.field a))), jA ((oE c).u (ainfObj (ϖ.field a)) x) = (OfCrystal.mulZ T c).lTensor (WCb l) (jA x)) → ∀ (b : ι → E.M (ϖ.prism a)), (∀ j, ∃ hm : (bas j : Vec K a ι) ∈ P.M, kappa T (jA (E.tr (ϖ.toAinf a) (b j))) = I.j (toW t ϖ P ⟨bas j, mem_ME_of_mem_M hm⟩)) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP), ∀ (Q : Type) [Fintype Q] (c : ι → ι → Q → O) (y : ι → ι → Q → PP.A), (∀ j, E.tr p₁ (b j) = ∑ i, ∑ q, y i j q • (oE (c i j q)).u PP (E.tr p₀ (b i))) → ∀ (Cr : Obj l ↥(OL (ϖ.field a))) (eC : Cr.A ≃+* Per.Acris l) (h : GlobalTheory.Prism.Hom (ainfObj (ϖ.field a)) Cr), (∀ x : Ainf l, eC (h.f x) = ainfToAcris l (WittVector.frobenius x)) → ∀ (g : ↥(GK (ϖ.field a))) (ev : GlobalTheory.Prism.Hom PP Cr), ev.comp p₀ = h.comp (ϖ.toAinf a) → ev.comp p₁ = (h.comp (ainfHom (ϖ.field a) g)).comp (ϖ.toAinf a) → ∃ Γ, I.IsLMat (g : GQ l) g Γ ∧ ∀ i j, toOCr l O (Γ i j) = ∑ q, c i j q ⊗ₜ[ℤ_[l]] eC (ev.f (y i j q)) := by
  first | exact @GlobalTheory.CrysGalValue.main | exact GlobalTheory.CrysGalValue.main | (intros; apply GlobalTheory.CrysGalValue.main <;> assumption)
end
