module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle054
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle038
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle041
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle047
import GroundTheory.GlobalFields.TateThesis.IdeleMeasure
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Aesop.Main
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle050
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSKfOrb
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle002
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle058
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle053
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.BoxMass

theorem boxMass : ∀ (F : Type) [Field F] [NumberField F] (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v)) → ∀ lf : Measure (Af F), lf.IsAddHaarMeasure → lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)), (∀ v, MeasurableSet (A v)) → MeasurableSet (Coef.boxA S A) ∧ lf (Coef.boxA S A) = ∏ v ∈ S, lam v (A v) := by
  intro F _ _ lam hlam lf hlf h1 S A hA
  obtain ⟨-, hAfLC, hAfSC, hAfT2⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  have hloc := fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : ∀ v, IsTopologicalRing (Fv F v) := fun v => (hloc v).1
  haveI : ∀ v, LocallyCompactSpace (Fv F v) := fun v => (hloc v).2.1
  haveI : ∀ v, SecondCountableTopology (Fv F v) := fun v => (hloc v).2.2.1
  haveI : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  haveI : ∀ v, (lam v).IsAddHaarMeasure := fun v => (hlam v).1
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  let A' : ∀ v : HeightOneSpectrum (𝓞 F), Set (Unit → Fv F v) := fun v => {x | x () ∈ A v}
  have hA' : ∀ v, MeasurableSet (A' v) := fun v => measurable_pi_apply () (hA v)
  let T : Set (Unit → Af F) := {x | (∀ v ∈ S, (fun i => HeckeCharacterZeroLocus.SiegelWeilU.evalV F v (x i)) ∈ A' v) ∧
    ∀ v, v ∉ S → ∀ i, HeckeCharacterZeroLocus.SiegelWeilU.evalV F v (x i) ∈ v.adicCompletionIntegers F}
  have hT : T = (GlobalTheory.CompanionTheory.SW.AfBox.offS (F := F) Unit S : Set (Unit → Af F)) ∩
      GlobalTheory.CompanionTheory.SW.AfBox.compS Unit S ⁻¹' (Set.pi Set.univ fun v : S => A' v.1) := by
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      exact ⟨hx2, fun v _ => hx1 v.1 v.2⟩
    · rintro ⟨hx1, hx2⟩
      exact ⟨fun v hv => hx2 ⟨v, hv⟩ (Set.mem_univ _), hx1⟩
  have hTm : MeasurableSet T := by
    rw [hT]
    exact (GlobalTheory.CompanionTheory.SW.AfBox.isOpen_offS Unit S).measurableSet.inter
      ((GlobalTheory.CompanionTheory.SW.AfBox.continuous_compS Unit S).measurable (MeasurableSet.univ_pi fun v => hA' v.1))
  have hbox : Coef.boxA S A = (MeasurableEquiv.funUnique Unit (Af F)).symm ⁻¹' T := by
    ext y
    simp only [Coef.boxA, T, A', Set.mem_preimage, Set.mem_setOf_eq, MeasurableEquiv.funUnique_symm_apply]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun v hv => h1 v hv, fun v hv _ => h2 v hv⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun v hv => h1 v hv, fun v hv => h2 v hv ()⟩
  have hmeas : MeasurableSet (Coef.boxA S A) := by
    rw [hbox]
    exact (MeasurableEquiv.funUnique Unit (Af F)).symm.measurable hTm
  refine ⟨hmeas, ?_⟩
  have hpb := GlobalTheory.CompanionTheory.SW.AfBox.pi_box F lam hlam lf hlf h1 Unit S A' hA'
  have hmp := measurePreserving_funUnique lf Unit
  have hT' : T = (MeasurableEquiv.funUnique Unit (Af F)) ⁻¹' Coef.boxA S A := by
    rw [hbox, ← Set.preimage_comp]
    ext x
    simp only [Set.mem_preimage, Function.comp_apply]
    rw [show (MeasurableEquiv.funUnique Unit (Af F)).symm ((MeasurableEquiv.funUnique Unit (Af F)) x) = x
      from (MeasurableEquiv.funUnique Unit (Af F)).symm_apply_apply x]
  change (Measure.pi fun _ : Unit => lf) T = _ at hpb
  rw [hT', hmp.measure_preimage hmeas.nullMeasurableSet] at hpb
  rw [hpb]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hv : A' v = (MeasurableEquiv.funUnique Unit (Fv F v)) ⁻¹' A v := by
    ext x
    rfl
  rw [hv, (measurePreserving_funUnique (lam v) Unit).measure_preimage (hA v).nullMeasurableSet]

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.BoxMass
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test

theorem integrable_inf_mul_indicator_finiteMass : ∀ (F : Type) [Field F] [NumberField F] (db : Measure (AF F)) (laminf : Measure (Ainf F)) (lf : Measure (Af F)), laminf.IsAddHaarMeasure → lf.IsAddHaarMeasure → ∀ e : (Ainf F × Af F) ≃ᵐ AF F, (∀ p, e p = pairA F p.1 p.2) → MeasurePreserving e (laminf.prod lf) db → ∀ (g : Ainf F → ℂ) (B : Set (Af F)), Integrable g laminf → MeasurableSet B → lf B ≠ ⊤ → Integrable (fun y => g (fstA F y) * B.indicator (fun _ => (1 : ℂ)) (sndA F y)) db := by
  intro F _ _ db laminf lf _ _ e he hmp g B hg hB hfin
  have hind : Integrable (B.indicator (fun _ => (1 : ℂ))) lf :=
    (integrable_indicator_iff hB).mpr (integrableOn_const hfin)
  refine (hmp.integrable_comp_emb e.measurableEmbedding).mp ?_
  have hfun : ((fun y => g (fstA F y) * B.indicator (fun _ => (1 : ℂ)) (sndA F y)) ∘ e) =
      fun p : Ainf F × Af F => g p.1 * B.indicator (fun _ => (1 : ℂ)) p.2 := by
    funext p
    simp only [Function.comp_apply, he p]
    rfl
  rw [hfun]
  exact hg.mul_prod hind

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef

open Formalism.L2.SG.LocVol Formalism.L2.SG.Pf.NcS.KfOrbPf Formalism.L2.SG.Pf.NcS.IntWittPf

theorem trace_one_tmul_len {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (R : Type) [CommRing R] [Algebra F R] (e : E) :
    Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e) = algebraMap F R (Algebra.trace F E e) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

theorem sub_qR_mem_integers : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (t : F),
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ X ∈ (latV b v : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)),
        algebraMap F (Fv F v) t - qR (Fv F v) σ J (X 0) ∈ v.adicCompletionIntegers F := by
  intro F E _ _ _ _ _ σ _ M J _ d b t
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  have hb : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ k, inclR (F := F) (Fv F v) (b k) ∈ OEv (E := E) v :=
    Filter.eventually_all.2 fun k => ev_oev (b k)
  have hJ : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ i j, inclR (F := F) (Fv F v) (J i j) ∈ OEv (E := E) v :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ev_oev (J i j)
  have htr : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ k, algebraMap F (Fv F v) (Algebra.trace F E (b k)) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun k => ev_int (Algebra.trace F E (b k))
  filter_upwards [ev_int (F := F) t, ev_int (F := F) (1 / 2), hb, hJ, htr, ev_crd_oev (E := E) b]
    with v ht hh hbv hJv htrv hc X hX
  have hrepr : ∀ z : Fv F v ⊗[F] E,
      z = ∑ k, (Algebra.TensorProduct.basis (Fv F v) b).repr z k • ((1 : Fv F v) ⊗ₜ[F] b k) := by
    intro z
    conv_lhs => rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr z]
    simp only [Algebra.TensorProduct.basis_apply]
  have hx : ∀ i, X 0 i ∈ oevRing (E := E) v := by
    intro i
    rw [hrepr (X 0 i)]
    refine Subring.sum_mem _ fun k _ => ?_
    exact oev_smul' v (hX 0 i k) (hbv k)
  have hh' : hR (Fv F v) σ J (X 0) (X 0) ∈ oevRing (E := E) v := by
    show ∑ i, ∑ j, sigR (Fv F v) σ (X 0 i) * JR (Fv F v) J i j * X 0 j ∈ oevRing (E := E) v
    refine sum_mem fun i _ => sum_mem fun j _ => ?_
    exact mul_mem (mul_mem (oev_sigR v σ (hx i)) (hJv i j)) (hx j)
  have htrace : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (hR (Fv F v) σ J (X 0) (X 0)) ∈
      v.adicCompletionIntegers F := by

    rw [hrepr (hR (Fv F v) σ J (X 0) (X 0)), map_sum]
    refine sum_mem fun k _ => ?_
    rw [map_smul, trace_one_tmul_len, smul_eq_mul]
    exact mul_mem (hc _ hh' k) (htrv k)
  exact sub_mem ht (mul_mem hh htrace)

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef
end
end

end

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

theorem _root_.GlobalTheory.T.finite_adele_box_measure_product : ∀ (F : Type) [Field F] [NumberField F] (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v)) → ∀ lf : Measure (Af F), lf.IsAddHaarMeasure → lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)), (∀ v, MeasurableSet (A v)) → MeasurableSet (Coef.boxA S A) ∧ lf (Coef.boxA S A) = ∏ v ∈ S, lam v (A v) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.BoxMass.boxMass | exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.BoxMass.boxMass | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.BoxMass.boxMass <;> assumption)

end
end

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

theorem _root_.GlobalTheory.T.adelic_integrable_product_indicator : ∀ (F : Type) [Field F] [NumberField F] (db : Measure (AF F)) (laminf : Measure (Ainf F)) (lf : Measure (Af F)), laminf.IsAddHaarMeasure → lf.IsAddHaarMeasure → ∀ e : (Ainf F × Af F) ≃ᵐ AF F, (∀ p, e p = pairA F p.1 p.2) → MeasurePreserving e (laminf.prod lf) db → ∀ (g : Ainf F → ℂ) (B : Set (Af F)), Integrable g laminf → MeasurableSet B → lf B ≠ ⊤ → Integrable (fun y => g (fstA F y) * B.indicator (fun _ => (1 : ℂ)) (sndA F y)) db := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.integrable_inf_mul_indicator_finiteMass | exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.integrable_inf_mul_indicator_finiteMass | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.integrable_inf_mul_indicator_finiteMass <;> assumption)

end
end
