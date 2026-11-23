module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle078
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle084
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle074
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle145
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle072
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle075
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle006
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1377
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzCoordinatesInInfiniteFamily
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexQuasiIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1296
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
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
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298

@[expose] public section

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.JacSubst

open GlobalTheory.ModuLR GlobalTheory.GaugeEx

theorem chi_AF_split (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ (AF F)) (hM : IsUnit M.det) :
    (addEquivAddHaarChar (mulVecCE M hM) : ℝ) =
      (modu (Ainf F) (fstA F M.det) : ℝ) * ∏ᶠ v, ‖evalV F v (sndA F M.det)‖ := by
  classical
  let Mi : Matrix κ κ (Ainf F) := (fstA F).toRingHom.mapMatrix M
  let Mf : Matrix κ κ (Af F) := (sndA F).toRingHom.mapMatrix M
  have hi : Mi.det = fstA F M.det := (RingHom.map_det _ _).symm
  have hf : Mf.det = sndA F M.det := (RingHom.map_det _ _).symm
  have hMi : IsUnit Mi.det := hi ▸ hM.map (fstA F)
  have hMf : IsUnit Mf.det := hf ▸ hM.map (sndA F)
  let j : (κ → Ainf F) × (κ → Af F) →+ (κ → AF F) := zipHom κ (Ainf F) (Af F)
  have hj : IsOpenEmbedding j := GlobalTheory.T.isOpenEmbedding_pairOfTuplesToTupleOfPairs κ (Ainf F) (Af F)
  have s1 : addEquivAddHaarChar (mulVecCE M hM) =
      addEquivAddHaarChar (prodCE (mulVecCE Mi hMi) (mulVecCE Mf hMf)) :=
    GlobalTheory.T.addEquivAddHaarChar_eq_of_isOpenEmbedding_restrict _ _ j hj (mulVecCE M hM) (prodCE (mulVecCE Mi hMi) (mulVecCE Mf hMf)) fun p => by
      funext i
      show (M *ᵥ j p) i = ((Mi *ᵥ p.1) i, (Mf *ᵥ p.2) i)
      have e1 : fstA F ((M *ᵥ j p) i) = (Mi *ᵥ p.1) i := by
        rw [show (fstA F) ((M *ᵥ j p) i) = (fstA F).toRingHom ((M *ᵥ j p) i) from rfl, RingHom.map_mulVec]
        rfl
      have e2 : sndA F ((M *ᵥ j p) i) = (Mf *ᵥ p.2) i := by
        rw [show (sndA F) ((M *ᵥ j p) i) = (sndA F).toRingHom ((M *ᵥ j p) i) from rfl, RingHom.map_mulVec]
        rfl
      rw [← e1, ← e2]
      rfl
  haveI : IsArtinianRing (Ainf F) := inferInstanceAs (IsArtinianRing (∀ v : InfinitePlace F, v.Completion))
  haveI : IsReduced (Ainf F) := inferInstanceAs (IsReduced (∀ v : InfinitePlace F, v.Completion))
  have s2 : addEquivAddHaarChar (mulVecCE Mi hMi) = modu (Ainf F) Mi.det :=
    GlobalTheory.T.addEquivAddHaarChar_mulVec_artinian_reduced (Ainf F) inferInstance inferInstance κ Mi hMi
  rw [s1, GlobalTheory.T.addEquivAddHaarChar_prodCongr, NNReal.coe_mul, s2, chi_Af F Mf hMf, hi, hf]

theorem chi_AF_det (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ (AF F)) (hM : IsUnit M.det) :
    addEquivAddHaarChar (mulVecCE M hM) = distribHaarChar (AF F) hM.unit := by
  classical
  let a : (AF F)ˣ := hM.unit
  let N : Matrix Unit Unit (AF F) := fun _ _ => (a : AF F)
  have hNd : N.det = M.det := by rw [Matrix.det_unique]; rfl
  have hN : IsUnit N.det := hNd ▸ hM
  have h1 : distribHaarChar (AF F) a = addEquivAddHaarChar (mulVecCE N hN) := by
    rw [GlobalTheory.ModuNorm.distribHaarChar_eq_addEquivAddHaarChar,
      ← addEquivAddHaarChar_transport (GlobalTheory.ModuNorm.evalUnitCE (AF F)) (mulVecCE N hN)]
    congr 1
    ext x
    show (a : AF F) * x = (N *ᵥ fun _ => x) ()
    simp [N, Matrix.mulVec, dotProduct]
  apply NNReal.coe_injective
  show (addEquivAddHaarChar (mulVecCE M hM) : ℝ) = (distribHaarChar (AF F) a : ℝ)
  rw [h1, chi_AF_split, chi_AF_split, hNd]

def colCE (R : Type) [AddCommGroup R] [TopologicalSpace R] (d : ℕ) : (Fin d → R) ≃ₜ+ Matrix (Fin d) (Fin 1) R where
  toFun u := Matrix.of fun i _ => u i
  invFun m i := m i 0
  left_inv u := rfl
  right_inv m := by
    ext i j
    rw [Fin.fin_one_eq_zero j]
    rfl
  map_add' u v := rfl
  continuous_toFun := continuous_pi fun i => continuous_pi fun _ => continuous_apply i
  continuous_invFun := continuous_pi fun i => (continuous_apply 0).comp (continuous_apply i)

def coordCE (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (b : Module.Basis (Fin n) F E) : AE F E ≃ₜ (Fin n → AF F) :=
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  { (Algebra.TensorProduct.basis (AF F) b).equivFun.toEquiv with
    continuous_toFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis (AF F) b).equivFun.toLinearMap
    continuous_invFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis (AF F) b).equivFun.symm.toLinearMap }

end GlobalTheory.JacSubst


open GlobalTheory.ModuLR GlobalTheory.GaugeEx GlobalTheory.JacSubst in
theorem GlobalTheory.JacSubst.integral_mulVec : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (t : GL (Fin d) (AE F E)),
    ∀ μ : @Measure (Fin d → AE F E) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ f : (Fin d → AE F E) → ℂ, ∫ u, f ((t : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ u) ∂μ =
      (((distribHaarChar (AF F) (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t)) : ℝ)⁻¹ : ℝ) : ℂ) *
        ∫ u, f u ∂μ := by
  intro F E _ _ _ _ _ d t μ hμ f
  letI mV : MeasurableSpace (Fin d → AE F E) := borel _
  haveI : BorelSpace (Fin d → AE F E) := ⟨rfl⟩
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  let e := coordCE F E (Module.finBasis F E)
  haveI : LocallyCompactSpace (AE F E) := e.isOpenEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : LocallyCompactSpace (Matrix (Fin d) (Fin 1) (AE F E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin d → Fin 1 → AE F E))
  haveI : SecondCountableTopology (Matrix (Fin d) (Fin 1) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin d → Fin 1 → AE F E))
  letI : MeasurableSpace (Matrix (Fin d) (Fin 1) (AE F E)) := borel _
  haveI : BorelSpace (Matrix (Fin d) (Fin 1) (AE F E)) := ⟨rfl⟩
  haveI : μ.Regular := inferInstance
  have hdt : IsUnit (t : Matrix (Fin d) (Fin d) (AE F E)).det := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.isUnit _
  let φ := mulVecCE (t : Matrix (Fin d) (Fin d) (AE F E)) hdt
  obtain ⟨κ, _, _, Λ, hΛ, hdet, hχ⟩ := @exists_matrix_restrictScalars_lrCE F E _ _ _ _ _ d (1 : ℕ) _ _ _ _ t (1 : GL (Fin 1) (AE F E))
  have hc : addEquivAddHaarChar φ =
      distribHaarChar (AF F) (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t)) := by
    have h1 : addEquivAddHaarChar φ = addEquivAddHaarChar (lrCE t (1 : GL (Fin 1) (AE F E))) := by
      rw [← addEquivAddHaarChar_transport (colCE (AE F E) d) φ]
      congr 1
      ext m i j
      rw [Fin.fin_one_eq_zero j]
      show ((t : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ (fun k => m k 0)) i =
        ((t : Matrix (Fin d) (Fin d) (AE F E)) * m * ((1 : GL (Fin 1) (AE F E)) : Matrix (Fin 1) (Fin 1) (AE F E))) i 0
      rw [Units.val_one, Matrix.mul_one]
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    rw [h1, hχ, chi_AF_det]
    congr 1
    ext
    simp only [IsUnit.unit_spec, hdet, Units.coe_map, MonoidHom.coe_coe, map_one, one_pow, mul_one, pow_one]
  have hmap : μ.map φ = (addEquivAddHaarChar φ)⁻¹ • μ := by
    have key := addEquivAddHaarChar_smul_map μ φ
    have hne : addEquivAddHaarChar φ ≠ 0 := (addEquivAddHaarChar_pos φ).ne'
    calc μ.map φ = ((addEquivAddHaarChar φ)⁻¹ * addEquivAddHaarChar φ) • μ.map φ := by
          rw [inv_mul_cancel₀ hne, one_smul]
      _ = (addEquivAddHaarChar φ)⁻¹ • μ := by rw [mul_smul, key]
  have hint : ∫ u, f u ∂(μ.map φ) = ∫ u, f ((t : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ u) ∂μ :=
    integral_map_equiv φ.toHomeomorph.toMeasurableEquiv f
  rw [← hint, hmap, integral_smul_nnreal_measure, hc, NNReal.smul_def, Complex.real_smul, NNReal.coe_inv]
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.MeanPeriodGenerator

theorem ellT_eq_span (D : D7) (cD : D.what₂.Tau → ℂ) (h : IsDgen D cD)
    (M : IntermediateField ℚ ℂ) [NumberField M] (hM : ∀ τ x, TaylorLogMetric.embT D τ x ∈ M)
    (τ : D.what₂.Tau) (hc : cD τ ∈ M) :
    TaylorLogMetric.ellT D M τ = Submodule.span (𝓞 M) {(⟨cD τ, hc⟩ : M)} := by
  obtain ⟨M₀, _, hM₀, hs⟩ := h
  obtain ⟨s, hsc, hs⟩ := hs τ
  have hs0 : s ≠ 0 := GlobalTheory.Glob.ne_zero_of_span_eq hM₀ hs.symm
  have hc0 : cD τ ≠ 0 := fun h => hs0 (Subtype.ext (hsc.trans h))
  haveI : NumberField (M ⊔ M₀ : IntermediateField ℚ ℂ) := NumberField.mk
  have hM' : ∀ τ x, TaylorLogMetric.embT D τ x ∈ (M ⊔ M₀ : IntermediateField ℚ ℂ) :=
    fun τ x => (le_sup_left : M ≤ M ⊔ M₀) (hM τ x)
  have h' := GlobalTheory.EigenlineBaseChange.ellT_eq_span_of_le D M₀ (M ⊔ M₀) le_sup_right hM₀ τ s hs
  apply le_antisymm
  · intro x hx
    have hx' : (⟨(x : ℂ), (le_sup_left : M ≤ M ⊔ M₀) x.2⟩ : (M ⊔ M₀ : IntermediateField ℚ ℂ)) ∈
        TaylorLogMetric.ellT D (M ⊔ M₀) τ := by
      rw [GlobalTheory.Glob.mem_ellT_iff hM']
      exact (GlobalTheory.Glob.mem_ellT_iff hM τ x).1 hx
    rw [h', Submodule.mem_span_singleton] at hx'
    obtain ⟨c, hcx⟩ := hx'
    have e : ((c : (M ⊔ M₀ : IntermediateField ℚ ℂ)) : ℂ) * (s : ℂ) = (x : ℂ) :=
      congrArg (fun a : (M ⊔ M₀ : IntermediateField ℚ ℂ) => (a : ℂ)) hcx
    have hi : IsIntegral ℤ ((c : (M ⊔ M₀ : IntermediateField ℚ ℂ)) : ℂ) :=
      (GlobalTheory.EigenlineBaseChange.isIntegral_coe_iff _).2 c.isIntegral_coe
    have e2 : ((c : (M ⊔ M₀ : IntermediateField ℚ ℂ)) : ℂ) = (x : ℂ) * (cD τ)⁻¹ := by
      rw [← e, hsc, mul_inv_cancel_right₀ hc0]
    rw [e2] at hi
    rw [Submodule.mem_span_singleton]
    refine ⟨⟨x * (⟨cD τ, hc⟩ : M)⁻¹, (GlobalTheory.EigenlineBaseChange.isIntegral_coe_iff _).1 hi⟩, ?_⟩
    exact inv_mul_cancel_right₀ (fun h => hc0 (congrArg (fun a : M => (a : ℂ)) h)) x
  · rw [Submodule.span_singleton_le_iff_mem, GlobalTheory.Glob.mem_ellT_iff hM]
    have := (GlobalTheory.Glob.mem_ellT_iff hM₀ τ s).1 (hs ▸ Submodule.mem_span_singleton_self s)
    rw [hsc] at this
    exact this

theorem mean_logMet_eq : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (cD : D.what₂.Tau → ℂ), StandardLatticesGL3.Crv D cc dl → GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriodAt D cc dl → IsDgen D cD → (∀ τ, cD τ ≠ 0) ∧ ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], TaylorLogMetric.DataIn D (TaylorLogMetric.tor0 D cc dl) M → (∀ τ, cD τ ∈ M) → ∀ τ, (∑ ρ : M →ₐ[ℚ] ℂ, -TaylorLogMetric.logMet M (TaylorLogMetric.lamOf D cc dl) ρ (TaylorLogMetric.liftM M (cD τ))) / (Module.finrank ℚ M : ℝ) = TaylorLogMetric.logOmVal D := by
  intro D cc dl cD hc hmean hgen
  have hne : ∀ τ, cD τ ≠ 0 := by
    intro τ h
    obtain ⟨M₀, _, hM₀, hs⟩ := hgen
    obtain ⟨s, hsc, hs⟩ := hs τ
    exact GlobalTheory.Glob.ne_zero_of_span_eq hM₀ hs.symm (Subtype.ext (hsc.trans h))
  refine ⟨hne, fun M _ hD hcM τ => ?_⟩
  haveI : NumberField M := NumberField.mk
  have hell := ellT_eq_span D cD hgen M hD.1 τ (hcM τ)
  have hl : TaylorLogMetric.liftM M (cD τ) = ⟨cD τ, hcM τ⟩ := dif_pos (hcM τ)
  rw [hl, ← hmean M hD τ, Finset.sum_neg_distrib]
  exact (GlobalTheory.Glob.meanLogOm_eq_of_gen hD.1 (GlobalTheory.Glob.area_lamConj_pos hc hD) hell.symm).symm

end GlobalTheory.MeanPeriodGenerator
end

section

open scoped TensorProduct ENNReal Matrix Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.schwartz_coordinates_in_infinite_family : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n d : ℕ) (ε : Module.Basis (Fin d) D.host.F D.host.E) (φ : WeilM.schA D.host.F (Fin m × Fin n × Fin d)), φ.1 ∘ coord ε ∈ GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ m n := by
  first | exact @GlobalTheory.SchwartzCoord.mem_schwartzA_comp_coord | exact GlobalTheory.SchwartzCoord.mem_schwartzA_comp_coord | (intros; apply GlobalTheory.SchwartzCoord.mem_schwartzA_comp_coord <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_free_complex_primitive_lineBundle_cech_fibres : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (B : Over (Spec (CommRingCat.of A))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ g : ℕ, SmoothOfRelativeDimension g B.hom → ∀ F : LB B.left, F.IsLB → (∃ u : LB.Gen (abelian₂ B F), u.IsGen) → ∀ P : Perf B.hom F, ∃ C : CochainComplex (ModuleCat.{0} A) ℕ, (∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i)) ∧ (∃ n, ∀ i, n < i → IsZero (C.X i)) ∧ Nonempty ((Module.Dual A (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) ≃ₗ[A] ((Fin P.a → A) ⧸ LinearMap.range P.D₀.transpose.mulVecLin)) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (φ : A →+* K) (X' : Scheme.{0}) (π : X' ⟶ B.left) (f' : X' ⟶ Spec (CommRingCat.of K)), IsPullback π f' B.hom (Spec.map (CommRingCat.ofHom φ)) → ∀ i, (g < i ∨ ¬ Triv (F.pull π)) → (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i) ∧ ∀ (K : Type) [Field K] (φ : A →+* K) (X' : Scheme.{0}) (π : X' ⟶ B.left) (f' : X' ⟶ Spec (CommRingCat.of K)), IsPullback π f' B.hom (Spec.map (CommRingCat.ofHom φ)) → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → X'.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → ∀ i, Nonempty ((((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).homology i ≃ₗ[K] (cechLB f' (F.pull π) D).homology i) := by
  first | exact @GlobalTheory.AbLaw.exists_free_complex_of_primitive_cech | exact GlobalTheory.AbLaw.exists_free_complex_of_primitive_cech | (intros; apply GlobalTheory.AbLaw.exists_free_complex_of_primitive_cech <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

noncomputable section

namespace GlobalTheory.CapTrace

variable {A : Type} [Ring A] [Algebra ℂ A]

def dprod (L : List (ℂ × A)) : ℂ := (L.map Prod.fst).prod

def sub1 (L : List (ℂ × A)) : A := List.rec 0 (fun p L s => dprod L • p.2 + p.1 • s) L

theorem sub1_nil : sub1 ([] : List (ℂ × A)) = 0 := rfl

theorem sub1_cons (p : ℂ × A) (L : List (ℂ × A)) : sub1 (p :: L) = dprod L • p.2 + p.1 • sub1 L := rfl

theorem prod_affine (L : List (ℂ × A)) : ∃ c : ℕ → A, (∀ k, L.length < k → c k = 0) ∧
    (∀ u : ℂ, (L.map fun p => (u * p.1) • (1 : A) + p.2).prod =
      ∑ k ∈ Finset.range (L.length + 1), u ^ k • c k) ∧
    c L.length = dprod L • (1 : A) ∧ (∀ j, j + 1 = L.length → c j = sub1 L) := by
  induction L with
  | nil => exact ⟨fun k => if k = 0 then 1 else 0, fun k hk => by simp at hk; simp [Nat.pos_iff_ne_zero.1 hk],
      fun u => by simp, by simp [dprod], fun j hj => by simp at hj⟩
  | cons p L ih =>
    obtain ⟨c, hc0, hcu, hctop, hcsub⟩ := ih
    refine ⟨fun k => (if k = 0 then 0 else p.1 • c (k - 1)) + p.2 * c k, ?_, ?_, ?_, ?_⟩
    · intro k hk
      simp only [List.length_cons] at hk
      have h1 : k ≠ 0 := by omega
      simp only [h1, if_false, hc0 k (by omega), hc0 (k - 1) (by omega), smul_zero, mul_zero, add_zero]
    · intro u
      have hS1 : ∑ k ∈ Finset.range (L.length + 1 + 1), u ^ k • (if k = 0 then (0:A) else p.1 • c (k - 1)) =
          ∑ k ∈ Finset.range (L.length + 1), (u * p.1) • (u ^ k • c k) := by
        rw [Finset.sum_range_succ']
        simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, if_true, smul_zero, add_zero]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [smul_smul, smul_smul, pow_succ]; ring_nf
      have hS2 : ∑ k ∈ Finset.range (L.length + 1 + 1), u ^ k • (p.2 * c k) =
          ∑ k ∈ Finset.range (L.length + 1), p.2 * (u ^ k • c k) := by
        rw [Finset.sum_range_succ, hc0 (L.length + 1) (by omega)]
        simp [mul_smul_comm]
      simp only [List.map_cons, List.prod_cons, hcu, List.length_cons, smul_add, Finset.sum_add_distrib, hS1, hS2,
        add_mul, Finset.mul_sum, smul_mul_assoc, one_mul]
    · simp only [List.length_cons, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, hctop,
        hc0 (L.length + 1) (by omega), mul_zero, add_zero, dprod, List.map_cons, List.prod_cons, smul_smul]
    · intro j hj
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hj
      subst hj
      beta_reduce
      rw [hctop, sub1_cons]
      rcases Nat.eq_zero_or_pos L.length with h | h
      · rw [if_pos h]
        have : L = [] := List.length_eq_zero_iff.1 h
        subst this
        simp [sub1_nil, dprod]
      · rw [if_neg (by omega), hcsub _ (by omega), mul_smul_comm, mul_one, add_comm]

end GlobalTheory.CapTrace

namespace GlobalTheory.CapTrace

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem coeff_mem (S : Submodule ℂ A) (n : ℕ) (c : ℕ → A)
    (h : ∀ u : ℂ, ∑ k ∈ Finset.range (n + 1), u ^ k • c k ∈ S) (m : ℕ) (hm : m ≤ n) : c m ∈ S := by
  let v : Fin (n + 1) → ℂ := fun j => ((j : ℕ) : ℂ)
  have hv : Function.Injective v := fun i j hij => Fin.ext (by simpa [v] using hij)
  have hdet : IsUnit (Matrix.vandermonde v).det :=
    isUnit_iff_ne_zero.2 (Matrix.det_vandermonde_ne_zero_iff.2 hv)
  have hW : (Matrix.vandermonde v)⁻¹ * Matrix.vandermonde v = 1 := Matrix.nonsing_inv_mul _ hdet
  set W := (Matrix.vandermonde v)⁻¹
  let m' : Fin (n + 1) := ⟨m, by omega⟩
  have key : c m = ∑ j, W m' j • ∑ k ∈ Finset.range (n + 1), v j ^ k • c k := by
    calc c m = ∑ k : Fin (n + 1), (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) m' k • c k := by
          rw [Finset.sum_eq_single m']
          · simp [m']
          · intro k _ hk; rw [Matrix.one_apply_ne (Ne.symm hk), zero_smul]
          · simp
      _ = ∑ k : Fin (n + 1), (W * Matrix.vandermonde v) m' k • c k := by rw [hW]
      _ = ∑ j, W m' j • ∑ k : Fin (n + 1), v j ^ (k : ℕ) • c k := by
          simp only [Matrix.mul_apply, Matrix.vandermonde_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
          exact Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_range (fun k => v j ^ k • c k)]
  rw [key]
  exact S.sum_mem fun j _ => S.smul_mem _ (h _)

theorem sub1_ones (L : List (ℂ × A)) (h : ∀ p ∈ L, p.1 = 1) : sub1 L = (L.map Prod.snd).sum ∧ dprod L = 1 := by
  induction L with
  | nil => simp [sub1_nil, dprod]
  | cons p L ih =>
    obtain ⟨h1, h2⟩ := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
    have hp := h p List.mem_cons_self
    refine ⟨?_, ?_⟩
    · rw [sub1_cons, h1, h2, hp]; simp
    · simp only [dprod, List.map_cons, List.prod_cons, hp, one_mul]; exact h2

theorem dprod_eq_zero (L : List (ℂ × A)) (p : ℂ × A) (hp : p ∈ L) (h : p.1 = 0) : dprod L = 0 :=
  List.prod_eq_zero (List.mem_map.2 ⟨p, hp, h⟩)

theorem sub1_ofFn_eq_zero : ∀ (n : ℕ) (d : Fin n → ℂ) (B : Fin n → A) (k₀ k₁ : Fin n), k₀ ≠ k₁ → d k₀ = 0 →
    d k₁ = 0 → sub1 (List.ofFn fun k => (d k, B k)) = 0 := by
  intro n
  induction n with
  | zero => intro d B k₀; exact k₀.elim0
  | succ n ih =>
    intro d B k₀ k₁ hne h₀ h₁
    rw [List.ofFn_succ, sub1_cons]
    have hmem : ∀ j : Fin n, d j.succ = 0 → dprod (List.ofFn fun k : Fin n => (d k.succ, B k.succ)) = 0 :=
      fun j hj => dprod_eq_zero _ (d j.succ, B j.succ) (List.mem_ofFn.2 ⟨j, rfl⟩) hj
    induction k₀ using Fin.cases with
    | zero =>
      induction k₁ using Fin.cases with
      | zero => exact absurd rfl hne
      | succ j₁ => simp [h₀, hmem j₁ h₁]
    | succ j₀ =>
      induction k₁ using Fin.cases with
      | zero => simp [h₁, hmem j₀ h₀]
      | succ j₁ =>
        rw [ih (fun k => d k.succ) (fun k => B k.succ) j₀ j₁ (fun e => hne (by rw [e])) h₀ h₁, hmem j₀ h₀]
        simp

end GlobalTheory.CapTrace

namespace GlobalTheory.CapTrace

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem trace_mem_of_qdet_mem {n : ℕ} (X : Fin n → Fin n → A) (S : Subalgebra ℂ A)
    (h : ∀ u : ℂ, Formalism.REAL.qdet X u ∈ S) : ∑ i, X i i ∈ S := by
  classical
  let d : Equiv.Perm (Fin n) → Fin n → ℂ := fun σ k => if σ k = k then 1 else 0
  let B : Equiv.Perm (Fin n) → Fin n → A := fun σ k =>
    (if σ k = k then algebraMap ℂ A (-((k : ℕ) : ℂ)) else 0) + X (σ k) k
  let L : Equiv.Perm (Fin n) → List (ℂ × A) := fun σ => List.ofFn fun k => (d σ k, B σ k)
  have hlen : ∀ σ, (L σ).length = n := fun σ => List.length_ofFn
  choose c hc0 hcu hctop hcsub using fun σ => prod_affine (L σ)
  have hfac : ∀ σ (u : ℂ), (List.ofFn fun k : Fin n => Formalism.REAL.Tm X (u - ((k : ℕ) : ℂ)) (id (σ k)) (id k)).prod =
      ((L σ).map fun p => (u * p.1) • (1 : A) + p.2).prod := by
    intro σ u
    simp only [L, List.map_ofFn]
    congr 1
    refine List.ofFn_inj.2 (funext fun k => ?_)
    simp only [Function.comp_apply, Formalism.REAL.Tm, id, d, B]
    split_ifs
    · rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, mul_one, sub_eq_add_neg, add_smul]; abel
    · simp
  let C : ℕ → A := fun k => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : A) * c σ k
  have hC : ∀ u : ℂ, Formalism.REAL.qdet X u = ∑ k ∈ Finset.range (n + 1), u ^ k • C k := by
    intro u
    simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, hfac, hcu, hlen, C, Finset.mul_sum, Finset.smul_sum, mul_smul_comm]
    exact Finset.sum_comm
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  have hmem : C (n - 1) ∈ S := coeff_mem (Subalgebra.toSubmodule S) n C (fun u => by
    rw [← hC]; exact h u) (n - 1) (by omega)
  have hsub : ∀ σ, c σ (n - 1) = sub1 (L σ) := fun σ => hcsub σ _ (by rw [hlen]; omega)
  have hCeq : C (n - 1) = ∑ k : Fin n, B 1 k := by
    simp only [C, hsub]
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
    · rw [(sub1_ones (L 1) ?_).1]
      · simp [L, List.map_ofFn, List.sum_ofFn]
      · intro p hp
        obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hp
        simp [d]
    · intro σ _ hσ
      obtain ⟨k₀, hk₀⟩ : ∃ k, σ k ≠ k := by
        by_contra hc; exact hσ (Equiv.ext fun k => not_not.1 fun hk => hc ⟨k, hk⟩)
      have hk₁ : σ (σ k₀) ≠ σ k₀ := fun e => hk₀ (σ.injective e)
      rw [sub1_ofFn_eq_zero n (d σ) (B σ) k₀ (σ k₀) (Ne.symm hk₀) (by simp [d, hk₀]) (by simp [d, hk₁]), mul_zero]
    · simp
  have hB : ∀ k : Fin n, B 1 k = algebraMap ℂ A (-((k : ℕ) : ℂ)) + X k k := fun k => by simp [B]
  simp only [hCeq, hB, Finset.sum_add_distrib] at hmem
  have hs : ∑ k : Fin n, algebraMap ℂ A (-((k : ℕ) : ℂ)) ∈ S := S.sum_mem fun k _ => S.algebraMap_mem _
  simpa using S.sub_mem hmem hs

end GlobalTheory.CapTrace

namespace GlobalTheory.CuspRep

theorem Eop_add_Eop_conj {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (τ : E →+* ℂ)
    (i : Fin a) : Eop τ i i + Eop (ComplexEmbedding.conjugate τ) i i = lieS E a i i (atEmb τ 1) := by
  have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by
    rw [atEmb_eq]; simp
  simp only [Eop, atEmb_conj, map_one, Complex.conj_I, e, map_neg, smul_neg, sub_neg_eq_add]
  rw [← smul_add]
  module

end GlobalTheory.CuspRep
end
end
