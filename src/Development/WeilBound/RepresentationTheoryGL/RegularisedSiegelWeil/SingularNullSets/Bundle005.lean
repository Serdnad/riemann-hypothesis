module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle004
import Formalism.LocalRingCardinality.DataHost
import GroundTheory.AutomorphicForms.Bundle012
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixWB
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

theorem kappa_real {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) {ε : AF F}
    (ν : Measure (fixE ε)) [SFinite ν] (τ : fixE ε → ℝ) (hτ0 : ∀ h, 0 ≤ τ h) (hτI : Integrable τ ν)
    (hτpos : 0 < ∫ h, τ h ∂ν) (M : ℝ) (hτM : ∀ h, τ h ≤ M) (A : fixE ε → ℂ)
    (hA : ∀ s, A s = ∫ h, (τ h : ℂ) * ψ (h.1 * s.1) ∂ν) (hAI : Integrable A ν) (κ : ℂ)
    (hκ : ∀ s : fixE ε, ∫ h, A h * ψ (h.1 * s.1) ∂ν = κ * τ (-s)) :
    κ.im = 0 ∧ 0 ≤ κ.re := by
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : SecondCountableTopology (fixE ε) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : OpensMeasurableSpace (fixE ε × fixE ε) := inferInstance
  have hψn : ∀ x, ‖ψ x‖ = 1 := hψ.2.1
  have hconj : ∀ x, (starRingEnd ℂ) (ψ x) = ψ (-x) := by
    intro x
    rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, hψn x]
    simp
  have hτC : Integrable (fun h => (τ h : ℂ)) ν := hτI.ofReal

  have hA' : ∀ h : fixE ε, (starRingEnd ℂ) (A h) = ∫ h', (τ h' : ℂ) * ψ (h.1 * (-h').1) ∂ν := by
    intro h
    rw [hA, ← integral_conj]
    congr 1
    funext h'
    rw [map_mul, Complex.conj_ofReal, hconj]
    congr 2
    change -(h'.1 * h.1) = h.1 * -h'.1
    ring

  set f : fixE ε → fixE ε → ℂ := fun h h' => A h * ((τ h' : ℂ) * ψ (h.1 * (-h').1)) with hf
  have hcont : Continuous fun z : fixE ε × fixE ε => ψ (z.1.1 * (-z.2).1) :=
    hψ.1.comp ((continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp
      (continuous_neg.comp continuous_snd)))
  have hfI : Integrable (Function.uncurry f) (ν.prod ν) := by
    refine Integrable.mono' (hAI.norm.mul_prod hτI) ?_ (Filter.Eventually.of_forall fun z => ?_)
    · exact hAI.aestronglyMeasurable.comp_fst.mul (hτC.aestronglyMeasurable.comp_snd.mul hcont.aestronglyMeasurable)
    · simp only [Function.uncurry, hf, norm_mul, hψn, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hτ0 _)]
      exact le_rfl
  have hsw := integral_integral_swap hfI
  have hL : ∫ h, A h * (starRingEnd ℂ) (A h) ∂ν = ∫ h, ∫ h', f h h' ∂ν ∂ν := by
    congr 1
    funext h
    rw [hA', ← integral_const_mul]
  have hR : ∫ h', ∫ h, f h h' ∂ν ∂ν = κ * ∫ h', ((τ h' * τ h' : ℝ) : ℂ) ∂ν := by
    rw [← integral_const_mul]
    congr 1
    funext h'
    have h1 : ∫ h, f h h' ∂ν = (τ h' : ℂ) * ∫ h, A h * ψ (h.1 * (-h').1) ∂ν := by
      rw [← integral_const_mul]
      congr 1
      funext h
      dsimp [f]
      ring
    rw [h1, hκ, neg_neg]
    push_cast
    ring

  have hLr : ∫ h, A h * (starRingEnd ℂ) (A h) ∂ν = ((∫ h, Complex.normSq (A h) ∂ν : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext h
    exact Complex.mul_conj _
  have hL0 : 0 ≤ ∫ h, Complex.normSq (A h) ∂ν := integral_nonneg fun h => Complex.normSq_nonneg _
  have hQI : Integrable (fun h => τ h * τ h) ν := by
    refine Integrable.mono' (hτI.const_mul M) (hτI.aestronglyMeasurable.mul hτI.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun h => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hτ0 h) (hτ0 h)), mul_comm M]
    exact mul_le_mul_of_nonneg_left (hτM h) (hτ0 h)
  have hQ0 : 0 < ∫ h, τ h * τ h ∂ν := by
    refine lt_of_le_of_ne (integral_nonneg fun h => mul_nonneg (hτ0 h) (hτ0 h)) fun h0 => ?_
    have hz := (integral_eq_zero_iff_of_nonneg (fun h => mul_nonneg (hτ0 h) (hτ0 h)) hQI).1 h0.symm
    have hz' : τ =ᵐ[ν] 0 := hz.mono fun h hh => by
      simpa using (mul_self_eq_zero.1 hh)
    rw [integral_congr_ae hz'] at hτpos
    simp at hτpos
  have hmain : ((∫ h, Complex.normSq (A h) ∂ν : ℝ) : ℂ) = κ * ((∫ h, τ h * τ h ∂ν : ℝ) : ℂ) := by
    rw [← hLr, hL, hsw, hR, integral_complex_ofReal]
  have hκe : κ = (((∫ h, Complex.normSq (A h) ∂ν) / ∫ h, τ h * τ h ∂ν : ℝ) : ℂ) := by
    have hq : ((∫ h, τ h * τ h ∂ν : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
    rw [Complex.ofReal_div, hmain, mul_div_assoc, div_self hq, mul_one]
  rw [hκe, Complex.ofReal_im, Complex.ofReal_re]
  exact ⟨rfl, div_nonneg hL0 hQ0.le⟩

end PositivityTheory.Rg.Rsw.L.LApproxId

end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

open scoped RestrictedProduct

theorem rp_nhds {ι : Type} {R : ι → Type} [∀ i, TopologicalSpace (R i)] {A : ∀ i, Set (R i)}
    (hA : ∀ i, IsOpen (A i)) (x : ∀ i, A i) (W : Set (Πʳ i, [R i, A i]))
    (hW : W ∈ 𝓝 (RestrictedProduct.structureMap R A cofinite x)) :
    ∃ V : ∀ i, Set (R i), (∀ i, V i ∈ 𝓝 (x i : R i)) ∧ ∀ z : Πʳ i, [R i, A i], (∀ i, z i ∈ V i) → z ∈ W := by
  rw [RestrictedProduct.nhds_eq_map_structureMap hA, Filter.mem_map, nhds_pi, Filter.mem_pi] at hW
  obtain ⟨I, -, t, ht, hIt⟩ := hW
  have ht' : ∀ i, ∃ u ∈ 𝓝 (x i : R i), Subtype.val ⁻¹' u ⊆ t i := fun i => mem_nhds_subtype _ _ _ |>.1 (ht i)
  choose u hu hut using ht'
  refine ⟨fun i => u i ∩ A i, fun i => Filter.inter_mem (hu i) ((hA i).mem_nhds (x i).2), fun z hz => ?_⟩
  let y : ∀ i, A i := fun i => ⟨z i, (hz i).2⟩
  have hyz : RestrictedProduct.structureMap R A cofinite y = z := Subtype.ext rfl
  rw [← hyz]
  exact hIt fun i _ => hut i (hz i).1

theorem af_nhds {F : Type} [Field F] [NumberField F] (W : Set (Af F)) (hW : W ∈ 𝓝 (0 : Af F)) :
    ∃ V : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v), (∀ v, V v ∈ 𝓝 (0 : Fv F v)) ∧
      ∀ z : Af F, (∀ v, z v ∈ V v) → z ∈ W := by
  have hA : ∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := fun v => Valued.isOpen_valuationSubring _
  have h0 : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite (fun _ => ⟨0, zero_mem _⟩) =
      (0 : Af F) := rfl
  rw [← h0] at hW
  exact rp_nhds hA _ W hW

theorem top1 {F : Type} [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F) (hε : IsIdF S ε)
    (A : ℕ → Set (Ainf F)) (U : ℕ → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v))
    (hA : Tendsto A atTop (𝓝 0).smallSets) (hU : ∀ v, Tendsto (fun k => U k v) atTop (𝓝 0).smallSets) :
    Tendsto (fun k => {a : AF F | ε * a = a ∧ fstA F a ∈ A k ∧ ∀ v ∈ S, (sndA F a) v ∈ U k v}) atTop
      (𝓝 (0 : AF F)).smallSets := by
  rw [Filter.tendsto_smallSets_iff]
  intro W hW
  obtain ⟨W1, hW1, W2, hW2, hsub⟩ := mem_nhds_prod_iff.1 (show W ∈ 𝓝 ((0, 0) : Ainf F × Af F) from hW)
  obtain ⟨V, hV, hVW⟩ := af_nhds W2 hW2
  have e1 := Filter.tendsto_smallSets_iff.1 hA W1 hW1
  have e2 : ∀ᶠ k in atTop, ∀ v ∈ S, U k v ⊆ V v :=
    (Filter.eventually_all_finset S).2 fun v _ => Filter.tendsto_smallSets_iff.1 (hU v) (V v) (hV v)
  filter_upwards [e1, e2] with k h1 h2
  rintro a ⟨hεa, haA, haU⟩
  apply hsub
  refine ⟨h1 haA, hVW (sndA F a) fun v => ?_⟩
  by_cases hv : v ∈ S
  · exact h2 v hv (haU v hv)
  · have h3 : sndA F a = sndA F ε * sndA F a := by rw [← map_mul, hεa]
    have h4 : (sndA F a) v = (sndA F ε) v * (sndA F a) v := congrArg (fun z : Af F => z v) h3
    rw [hε.2 v, if_neg hv, zero_mul] at h4
    rw [h4]
    exact mem_of_mem_nhds (hV v)

end PositivityTheory.Rg.Rsw.L.LApproxId

end
end

section

noncomputable section



open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LFixW.U2

variable {D : D7}

theorem norm_mem {v : Pl D} (hv : IsGood D.host.F D.host.E v) {x : Fv D.host.F v ⊗[D.host.F] D.host.E}
    (hx : x ∈ intLoc D.host.F D.host.E v) :
    Algebra.norm (Fv D.host.F v) x ∈ v.adicCompletionIntegers D.host.F := by
  classical
  rw [Algebra.norm_eq_matrix_det (bV (E := D.host.E) v), Matrix.det_apply]
  have hM : ∀ i j, Algebra.leftMulMatrix (bV (E := D.host.E) v) x i j ∈ v.adicCompletionIntegers D.host.F := by
    intro i j
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    have hb : bV (E := D.host.E) v j ∈ intLoc D.host.F D.host.E v := by
      rw [bV_apply]; exact one_tmul_b_mem hv j
    exact (mem_intLoc_iff hv _).1 (mul_mem hx hb) i
  refine sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (prod_mem fun i _ => hM _ _) _

theorem absEv_eq_one {v : Pl D} (hv : IsGood D.host.F D.host.E v) (x : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ)
    (h1 : (x : Fv D.host.F v ⊗[D.host.F] D.host.E) ∈ intLoc D.host.F D.host.E v)
    (h2 : ((x⁻¹ : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Fv D.host.F v ⊗[D.host.F] D.host.E) ∈
      intLoc D.host.F D.host.E v) :
    absEv D.host.F D.host.E v x = 1 := by
  have k : ∀ y : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ, (y : Fv D.host.F v ⊗[D.host.F] D.host.E) ∈
      intLoc D.host.F D.host.E v → absEv D.host.F D.host.E v y ≤ 1 := fun y hy => by
    rw [absEv_apply]
    exact_mod_cast Valued.toNormedField.norm_le_one_iff.2 (norm_mem hv hy)
  have a1 := k x h1
  have a2 := k _ h2
  have hm : absEv D.host.F D.host.E v x * absEv D.host.F D.host.E v x⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  refine le_antisymm a1 ?_
  calc (1 : ℝ≥0) = absEv D.host.F D.host.E v x * absEv D.host.F D.host.E v x⁻¹ := hm.symm
    _ ≤ absEv D.host.F D.host.E v x * 1 := mul_le_mul_of_nonneg_left a2 (by positivity)
    _ = absEv D.host.F D.host.E v x := mul_one _

def cN (D : D7) (N : ℕ) : AE D := algebraMap D.host.F (AF D.host.F) ((N : D.host.F)⁻¹) ⊗ₜ[D.host.F] (1 : D.host.E)

theorem cv_cN (v : Pl D) (N : ℕ) :
    cv D v (cN D N) = algebraMap D.host.F (Fv D.host.F v) ((N : D.host.F)⁻¹) ⊗ₜ[D.host.F] (1 : D.host.E) := by
  show evFin D.host.F v (algebraMap D.host.F (AF D.host.F) _) ⊗ₜ[D.host.F] (1 : D.host.E) = _
  rw [AlgHom.commutes]

theorem natCast_mul_gen {F E A : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [Algebra F A] {N : ℕ}
    (hN : (N : F) ≠ 0) : (N : A ⊗[F] E) * (algebraMap F A ((N : F)⁻¹) ⊗ₜ[F] (1 : E)) = 1 := by
  rw [(map_natCast (Algebra.TensorProduct.includeLeftRingHom (R := F) (A := A) (B := E)) N).symm]
  show ((N : A) ⊗ₜ[F] (1 : E)) * _ = 1
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← map_natCast (algebraMap F A) N, ← map_mul,
    mul_inv_cancel₀ hN, map_one]
  rfl

theorem natCast_mul_cN {N : ℕ} (hN : 0 < N) : (N : AE D) * cN D N = 1 :=
  natCast_mul_gen (by exact_mod_cast hN.ne')

end PositivityTheory.Rg.Rsw.L.LFixW.U2

end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)




namespace PositivityTheory.Rg.Rsw.L.LGenK

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]

def crd (R : Type) [CommRing R] [Algebra F R] (x : R ⊗[F] E) (k : Fin (Module.finrank F E)) : R :=
  (Algebra.TensorProduct.basis R (Module.finBasis F E)).repr x k

theorem crd_tmul (R : Type) [CommRing R] [Algebra F R] (r : R) (e : E) (k : Fin (Module.finrank F E)) :
    crd R (r ⊗ₜ[F] e) k = r * algebraMap F R ((Module.finBasis F E).repr e k) := by
  unfold crd
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp [Finsupp.mapRange_apply, smul_eq_mul]

theorem crd_add (R : Type) [CommRing R] [Algebra F R] (x y : R ⊗[F] E) (k : Fin (Module.finrank F E)) :
    crd R (x + y) k = crd R x k + crd R y k := by
  simp [crd]

theorem crd_neg (R : Type) [CommRing R] [Algebra F R] (x : R ⊗[F] E) (k : Fin (Module.finrank F E)) :
    crd R (-x) k = -crd R x k := by
  simp [crd]

theorem crd_zero (R : Type) [CommRing R] [Algebra F R] (k : Fin (Module.finrank F E)) :
    crd R (0 : R ⊗[F] E) k = 0 := by
  simp [crd]

theorem crd_map {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (x : R ⊗[F] E) (k : Fin (Module.finrank F E)) :
    crd R' (Algebra.TensorProduct.map f (AlgHom.id F E) x) k = f (crd R x k) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, crd_zero, crd_zero, map_zero]
  | tmul r e =>
    rw [Algebra.TensorProduct.map_tmul, crd_tmul, crd_tmul, map_mul, AlgHom.commutes]
    rfl
  | add x y hx hy => rw [map_add (f := _), crd_add, crd_add, hx, hy, map_add (f := _)]

theorem crd_ext (R : Type) [CommRing R] [Algebra F R] {x y : R ⊗[F] E}
    (h : ∀ k, crd R x k = crd R y k) : x = y :=
  (Algebra.TensorProduct.basis R (Module.finBasis F E)).repr.injective (Finsupp.ext h)

theorem sum_crd (R : Type) [CommRing R] [Algebra F R] (y : R ⊗[F] E) :
    ∑ k, crd R y k ⊗ₜ[F] (Module.finBasis F E) k = y := by
  conv_rhs => rw [← (Algebra.TensorProduct.basis R (Module.finBasis F E)).sum_repr y]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rfl

end Coord

variable {D : D7}

theorem cv_eq (v : Pl D) (x : AE D) :
    cv D v x = Algebra.TensorProduct.map (evFin D.host.F v) (AlgHom.id D.host.F D.host.E) x := rfl

theorem infPart_eq (x : AE D) :
    infPart D x = Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) x := rfl

theorem ext_comp {D : D7} {x y : AE D} (hf : ∀ v, cv D v x = cv D v y) (hi : infPart D x = infPart D y) : x = y := by
  refine crd_ext (AF D.host.F) fun k => ?_
  have hf' : ∀ v : Pl D, evFin D.host.F v (crd (AF D.host.F) x k) = evFin D.host.F v (crd (AF D.host.F) y k) := by
    intro v
    have := congrArg (fun z => crd (Fv D.host.F v) z k) (hf v)
    simpa only [cv_eq, crd_map] using this
  have hi' : fstA D.host.F (crd (AF D.host.F) x k) = fstA D.host.F (crd (AF D.host.F) y k) := by
    have := congrArg (fun z => crd (Ainf D.host.F) z k) hi
    simpa only [infPart_eq, crd_map] using this
  exact Prod.ext hi' (Subtype.ext (funext hf'))

theorem cv_cA {D : D7} (v : Pl D) (x : AE D) : cv D v (cA D x) = sigR (Fv D.host.F v) D.sp.cm.sig (cv D v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem infPart_cA {D : D7} (x : AE D) : infPart D (cA D x) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem crd_int_ev (k : Fin (Module.finrank D.host.F D.host.E)) :
    ∀ᶠ v in Filter.cofinite, ∀ y ∈ intLoc D.host.F D.host.E (v : Pl D),
      crd (Fv D.host.F v) y k ∈ (v : Pl D).adicCompletionIntegers D.host.F := by
  classical
  set b := Module.finBasis D.host.F D.host.E
  set B := NumberField.RingOfIntegers.basis D.host.E
  have hev : ∀ᶠ v in Filter.cofinite, ∀ j,
      algebraMap D.host.F (Fv D.host.F v) (b.repr ((B j : 𝓞 D.host.E) : D.host.E) k) ∈
        (v : Pl D).adicCompletionIntegers D.host.F := by
    rw [Filter.eventually_all]; intro j
    exact (algebraMap D.host.F (Af D.host.F) (b.repr ((B j : 𝓞 D.host.E) : D.host.E) k)).2
  filter_upwards [hev] with v hv
  intro y hy
  refine intLoc_induction (p := fun y => crd (Fv D.host.F v) y k ∈ (v : Pl D).adicCompletionIntegers D.host.F)
    ?_ ?_ ?_ ?_ hy
  · intro a ha o
    rw [crd_tmul]
    refine mul_mem ha ?_
    have ho : (o : D.host.E) = ∑ j, (B.repr o j) • ((B j : 𝓞 D.host.E) : D.host.E) := by
      conv_lhs => rw [← B.sum_repr o]
      push_cast
      rfl

    rw [ho, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, map_sum]
    refine sum_mem fun j _ => ?_
    rw [map_zsmul, Finsupp.smul_apply, map_zsmul]
    exact zsmul_mem (hv j) _
  · rw [crd_zero]; exact zero_mem _
  · intro y z hy hz; rw [crd_add]; exact add_mem hy hz
  · intro y hy; rw [crd_neg]; exact neg_mem hy

theorem glue_one (D : D7) (f : ∀ v : Pl D, Fv D.host.F v ⊗[D.host.F] D.host.E)
    (hf : ∀ v, f v ∈ intLoc D.host.F D.host.E v) :
    ∃ x : AE D, (∀ v, cv D v x = f v) ∧ infPart D x = 0 := by
  classical
  let c : Fin (Module.finrank D.host.F D.host.E) → (v : Pl D) → Fv D.host.F v := fun k v => crd (Fv D.host.F v) (f v) k
  have hc : ∀ k, ∀ᶠ v in Filter.cofinite, c k v ∈ (v : Pl D).adicCompletionIntegers D.host.F := by
    intro k
    filter_upwards [crd_int_ev (D := D) k] with v hv
    exact hv _ (hf v)
  let C : Fin (Module.finrank D.host.F D.host.E) → Af D.host.F := fun k => RestrictedProduct.mk (c k) (hc k)
  refine ⟨∑ k, pairA D.host.F 0 (C k) ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E) k, fun v => ?_, ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    conv_rhs => rw [← sum_crd (Fv D.host.F v) (f v)]
    rfl
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] _ = 0
    rw [TensorProduct.zero_tmul]

theorem glue_mat (D : D7) {m p : ℕ} (b : ∀ v : Pl D, Matrix (Fin m) (Fin p) (Fv D.host.F v ⊗[D.host.F] D.host.E))
    (hb : ∀ v i j, b v i j ∈ intLoc D.host.F D.host.E v) :
    ∃ x : Mx D m p, (∀ v i j, cv D v (x i j) = b v i j) ∧ ∀ i j, infPart D (x i j) = 0 := by
  choose g hg using fun i j => glue_one D (fun v => b v i j) (fun v => hb v i j)
  exact ⟨Matrix.of fun i j => g i j, fun v i j => (hg i j).1 v, fun i j => (hg i j).2⟩

theorem isUnit_of_comp (D : D7) (y : AE D) (hf : ∀ v, ∃ z ∈ intLoc D.host.F D.host.E v, cv D v y * z = 1)
    (hi : infPart D y = 1) : IsUnit y := by
  choose z hz hzy using hf
  obtain ⟨s, hs, hs0⟩ := glue_one D z hz
  set e : AE D := pairA D.host.F 1 0 ⊗ₜ[D.host.F] (1 : D.host.E) with he
  have hev : ∀ v, cv D v e = 0 := by
    intro v
    show (evFin D.host.F v (pairA D.host.F 1 0)) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    have : evFin D.host.F v (pairA D.host.F 1 0) = 0 := rfl
    rw [this, TensorProduct.zero_tmul]
  have hei : infPart D e = 1 := rfl
  have h1 : y * (s + e) = 1 := by
    refine ext_comp (fun v => ?_) ?_
    · rw [map_mul, map_add (f := _), hs, hev, add_zero, hzy, map_one]
    · rw [map_mul, map_add (f := _), hs0, hei, zero_add, hi, mul_one, map_one]
  exact ⟨⟨y, s + e, h1, by rw [mul_comm]; exact h1⟩, rfl⟩

end PositivityTheory.Rg.Rsw.L.LGenK
end
end
