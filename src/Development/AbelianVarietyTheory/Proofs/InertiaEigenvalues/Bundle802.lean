module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle371
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle346
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle220
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle187
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle789
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle791
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle027
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle758
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle745
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle782
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle790
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle792
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaKernelGrowth
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.TypeRec GlobalTheory.TypeVec
attribute [local instance] GlobalTheory.TypeRec.factG Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowGood

open Matrix
open scoped TensorProduct

section Res

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def tr {F1 : Subfield E} (h : F1 = maximalRealSubfield E) : AL E →+* E ⊗[F1] Formalism.L2.Herm.Af F1 :=
  (GlobalTheory.LevSplit.swp F1 E).comp (GlobalTheory.Mem.R3.swapCast h).symm.toRingHom

theorem tr_rfl (z : AL E) : tr (rfl : maximalRealSubfield E = maximalRealSubfield E) z = z := by
  exact (Algebra.TensorProduct.comm _ _ _).apply_symm_apply z

theorem tr_int {F1 : Subfield E} (h : F1 = maximalRealSubfield E) {z : AL E} (hz : z ∈ ALint E) :
    tr h z ∈ Formalism.L2.Herm.intAf F1 E := by
  subst h
  rw [tr_rfl]
  have key : ReciprocityTheory.Aut.ALint E ≤ Formalism.L2.Herm.intAf (maximalRealSubfield E) E := by
    unfold ReciprocityTheory.Aut.ALint
    rw [Subring.closure_le]
    rintro x (⟨y, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact Subring.subset_closure (Or.inl ⟨⟨(y : E), y, rfl⟩, rfl⟩)
    · exact Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
  exact key hz

theorem proj_le_one (s : SplitPlace E) {z : AL E} (hz : z ∈ Formalism.L2.Herm.intAf (maximalRealSubfield E) E) :
    Valued.v (s.proj z) ≤ 1 := by
  have key : Formalism.L2.Herm.intAf (maximalRealSubfield E) E ≤
      (s.v.adicCompletionIntegers (maximalRealSubfield E)).toSubring.comap s.proj := by
    show Subring.closure _ ≤ _
    rw [Subring.closure_le]
    rintro x (⟨⟨_, b, rfl⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩)
    · rw [SetLike.mem_coe, Subring.mem_comap, ValuationSubring.mem_toSubring,
        IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
      simp only [ReciprocityTheory.Aut.SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      exact s.split_le_one b
    · rw [SetLike.mem_coe, Subring.mem_comap, ValuationSubring.mem_toSubring]
      simp only [ReciprocityTheory.Aut.SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      exact ha s.v
  have := key hz
  rwa [Subring.mem_comap, ValuationSubring.mem_toSubring,
    IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at this

theorem res_eq {F1 : Subfield E} (h : F1 = maximalRealSubfield E) (s : SplitPlace E) (z : AL E)
    (y : Formalism.L2.Herm.intAf F1 E) (hy : (y : E ⊗[F1] Formalism.L2.Herm.Af F1) = tr h z) (a : 𝓞 E)
    (ha : Valued.v (s.proj z - s.i (a : E)) < 1) : resS F1 s.w y = Ideal.Quotient.mk _ a := by
  subst h
  have key : ∀ (t : E ⊗[maximalRealSubfield E] Formalism.L2.Herm.Af (maximalRealSubfield E))
      (ht : t ∈ Formalism.L2.Herm.intAf (maximalRealSubfield E) E),
      ∃ c : 𝓞 E, Valued.v (s.proj t - s.i (c : E)) < 1 ∧
        resS (maximalRealSubfield E) s.w ⟨t, ht⟩ = Ideal.Quotient.mk _ c := by
    intro t ht
    refine Subring.closure_induction
      (p := fun t ht => ∃ c : 𝓞 E, Valued.v (s.proj t - s.i (c : E)) < 1 ∧
        resS (maximalRealSubfield E) s.w ⟨t, ht⟩ = Ideal.Quotient.mk _ c) ?_ ?_ ?_ ?_ ?_ ?_ ht
    · rintro x (⟨⟨_, b, rfl⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩)
      · refine ⟨b, ?_, ?_⟩
        · simp [ReciprocityTheory.Aut.SplitPlace.proj]
        · have e : (⟨_, Subring.subset_closure (Or.inl ⟨⟨_, b, rfl⟩, rfl⟩)⟩ : Formalism.L2.Herm.intAf (maximalRealSubfield E) E) =
              Formalism.L2.DIV.oToS (maximalRealSubfield E) E b :=
            Subtype.ext (Formalism.L2.DIV.oToS_coe (F := maximalRealSubfield E) b).symm
          rw [e, Formalism.L2.DIV.resS_oToS]
      · obtain ⟨D0, hD0, hD0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot s.v.ne_bot
        obtain ⟨r, hr⟩ := Formalism.UG.P.csApprox_local s.v D0 hD0ne (a s.v) (ha s.v)
        have hlt : s.v.intValuation D0 < 1 := by
          exact (s.v.intValuation_lt_one_iff_mem D0).mpr hD0
        have hi : s.i (((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) r : 𝓞 E)) : E) =
            algebraMap (𝓞 (maximalRealSubfield E)) (s.v.adicCompletion (maximalRealSubfield E)) r := by
          rw [ReciprocityTheory.Aut.split_coe_algebraMap, AlgHom.commutes,
            IsScalarTower.algebraMap_apply (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)
              (s.v.adicCompletion (maximalRealSubfield E)) r]
        refine ⟨algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) r, ?_, ?_⟩
        · have hp : s.proj ((1 : E) ⊗ₜ[maximalRealSubfield E] a) = a s.v := by
            simp only [ReciprocityTheory.Aut.SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
              Algebra.TensorProduct.lift_tmul, map_one, one_mul]
            rfl
          rw [hp, hi]
          exact hr.trans hlt
        · have hsplit : (⟨_, Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)⟩ : Formalism.L2.Herm.intAf (maximalRealSubfield E) E) =
              Formalism.L2.DIV.adS (maximalRealSubfield E) E (⟨a, ha⟩ - Formalism.L2.DIV.oToAd (maximalRealSubfield E) r) +
                Formalism.L2.DIV.oToS (maximalRealSubfield E) E (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) r) := by
            rw [← Formalism.L2.DIV.adS_oToAd, ← map_add (f := _), sub_add_cancel]
            exact Subtype.ext (Formalism.L2.DIV.adS_coe (E := E) ⟨a, ha⟩).symm
          rw [hsplit, map_add (f := _), Formalism.L2.DIV.resS_oToS, Formalism.L2.DIV.resS_adS_eq_zero s.w s.v s.w_under.symm, zero_add]
          show Valued.v (a s.v - algebraMap (𝓞 (maximalRealSubfield E)) (s.v.adicCompletion (maximalRealSubfield E)) r) < 1
          exact hr.trans hlt
    · refine ⟨0, by simp, ?_⟩
      change resS (maximalRealSubfield E) s.w 0 = _
      simp
    · refine ⟨1, by simp, ?_⟩
      change resS (maximalRealSubfield E) s.w 1 = _
      simp
    · rintro x y hx hy ⟨c1, h1, e1⟩ ⟨c2, h2, e2⟩
      refine ⟨c1 + c2, ?_, ?_⟩
      · have : s.proj (x + y) - s.i ((c1 + c2 : 𝓞 E) : E) = (s.proj x - s.i (c1 : E)) + (s.proj y - s.i (c2 : E)) := by
          push_cast
          rw [map_add (f := _), map_add (f := _)]
          ring
        rw [this]
        exact Valuation.map_add_lt _ h1 h2
      · change resS (maximalRealSubfield E) s.w (⟨x, hx⟩ + ⟨y, hy⟩) = _
        rw [map_add (f := _), e1, e2, map_add (f := _)]
    · rintro x hx ⟨c1, h1, e1⟩
      refine ⟨-c1, ?_, ?_⟩
      · have : s.proj (-x) - s.i ((-c1 : 𝓞 E) : E) = -(s.proj x - s.i (c1 : E)) := by
          push_cast
          rw [map_neg, map_neg]
          ring
        rw [this, Valuation.map_neg]
        exact h1
      · change resS (maximalRealSubfield E) s.w (-⟨x, hx⟩) = _
        rw [map_neg, e1, map_neg]
    · rintro x y hx hy ⟨c1, h1, e1⟩ ⟨c2, h2, e2⟩
      refine ⟨c1 * c2, ?_, ?_⟩
      · have : s.proj (x * y) - s.i ((c1 * c2 : 𝓞 E) : E) =
            s.proj x * (s.proj y - s.i (c2 : E)) + (s.proj x - s.i (c1 : E)) * s.i (c2 : E) := by
          push_cast
          rw [map_mul, map_mul]
          ring
        rw [this]
        have hx1 : Valued.v (s.proj x) ≤ 1 := proj_le_one s hx
        have hc2 : Valued.v (s.i (c2 : E)) ≤ 1 := s.split_le_one c2
        refine Valuation.map_add_lt _ ?_ ?_
        · rw [Valuation.map_mul]
          exact lt_of_le_of_lt (mul_le_of_le_one_left' hx1) h2
        · rw [Valuation.map_mul]
          exact lt_of_le_of_lt (mul_le_of_le_one_right' hc2) h1
      · change resS (maximalRealSubfield E) s.w (⟨x, hx⟩ * ⟨y, hy⟩) = _
        rw [map_mul, e1, e2, map_mul]
  obtain ⟨c, hc1, hc2⟩ := key y.1 y.2
  have hyz : (y : E ⊗[maximalRealSubfield E] Formalism.L2.Herm.Af (maximalRealSubfield E)) = z := by rw [hy, tr_rfl]
  rw [hyz] at hc1
  have hca : Valued.v (s.i ((c - a : 𝓞 E) : E)) < 1 := by
    have : s.i ((c - a : 𝓞 E) : E) = (s.proj z - s.i (a : E)) - (s.proj z - s.i (c : E)) := by
      push_cast
      rw [map_sub]
      ring
    rw [this]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ha hc1)
  have hmem : c - a ∈ s.w.asIdeal := (s.split_mem_ideal (c - a)).mpr hca
  have hyy : (⟨y.1, y.2⟩ : Formalism.L2.Herm.intAf (maximalRealSubfield E) E) = y := rfl
  rw [hyy] at hc2
  rw [hc2]
  exact Ideal.Quotient.eq.mpr hmem

end Res

section Padic

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {g : ℕ} [Fact g.Prime]

end Padic

end GlobalTheory.RowGood

end

noncomputable section

namespace GlobalTheory.RowGood

open Matrix
open scoped TensorProduct

end GlobalTheory.RowGood

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section
namespace GlobalTheory.DownLift.Sobolev₂

open GlobalTheory.Size GlobalTheory.Grow
open scoped ComplexOrder

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]



theorem integrableOn_extV (R : RealDat D A Ks) (hm : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    (l : (R.cV i).W →ₗ[ℂ] ℂ) : IntegrableOn (fun h => l (R.extV i t y h)) (R.fdV i t) (R.νV i t) := by
  have hp : (Vc D i).IsPosDef := hm.vpos i
  have hpd : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ =>
    GlobalTheory.RepsObj.gramAt_posDef hp (D.sp.V_sig ((i : ℕ) + 1)) τ
  have hc := GlobalTheory.definite_unitary_cocompact (Vc D i) hpd
  have hK := hc.choose_spec.1
  have hKc := hc.choose_spec.2
  have hx := (hm.HV i t).2.1.le (LinearMap.mem_range_self _ y)
  have hFc : Continuous (R.extV i t y) :=
    GlobalTheory.ThetaIntegrand.ext_continuous (R.cV i) (hm.cV i) (R.βV i) (R.datVt i t) hx
  have hFi : ∀ γ ∈ GQ (Vc D i), ∀ h, R.extV i t y (γ * h) = R.extV i t y h :=
    GlobalTheory.ThetaIntegrand.ext_invariant (R.cV i) hx
  have hlc : Continuous fun h => l (R.extV i t y h) := l.continuous_of_finiteDimensional.comp hFc
  have hH : (R.νV i t).IsHaarMeasure := (hm.νV i t).1.1
  have hfd : IsFundamentalDomain (GQ (Vc D i)) (R.fdV i t) (R.νV i t) := (hm.νV i t).2
  have : IsFiniteMeasure ((R.νV i t).restrict (R.fdV i t)) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol (Vc D i) (R.νV i t) (R.fdV i t)
      hH hfd).ne
  have hb := hK.exists_bound_of_continuousOn hlc.continuousOn
  have hbd : ∀ h, ‖l (R.extV i t y h)‖ ≤ hb.choose := by
    intro h
    obtain ⟨γ, hγ, c, hc, e⟩ := hKc h
    rw [e, hFi γ hγ c]
    exact hb.choose_spec c hc
  exact Integrable.of_bound hlc.aestronglyMeasurable hb.choose (.of_forall hbd)



theorem downInt_sobolev_cont : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)) (ε : ℝ), 0 < ε → ∃ (d : ℕ) (δ : ENNReal), 0 < δ ∧ ∀ P, GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d (f - R.ptP i t P) < δ → ‖downInt R i t y f l g - downInt R i t y (R.ptP i t P) l g‖ < ε := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t y μ 𝓕 hμ f hf l g ε hε
  have hm := hG.core.models
  have hθ : IsInfFam R.θ := hm.inf
  have hω := hG.core.thP.ωP i t
  have hψ := hω.std
  have hpt := hG.core.thP.pt_theta i t
  have hvP : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hpt 1
    rwa [RealDat.ptP, GlobalTheory.FiniteFock.pureTensorO_one] at this
  obtain ⟨U₀, hU₀, hl₀⟩ := isTheta_iff_level.1 hvP
  obtain ⟨U₁, hU₁, hl₁⟩ := isTheta_iff_level.1 hf
  have hUo : IsOpen ((U₁ ⊓ U₀ : AddSubgroup (WO (Vc D i) (Wc D i))) : Set (WO (Vc D i) (Wc D i))) := by
    rw [AddSubgroup.coe_inf]; exact hU₁.inter hU₀
  have hptl : ∀ P, R.ptP i t P ∈ _root_.GlobalTheory.Size.thetaLevel R.ψ (Vc D i) (Wc D i) U₀ := fun P =>
    ⟨hpt P, fun u hu h0 => by
      have e := ((GlobalTheory.FinTranslate.finite_translate D R.ψ R.θ _ _ hψ hθ _ hvP).2 u h0).2
      unfold RealDat.ptP
      rw [← e, hl₀.2 u hu h0]⟩
  have hfl : f ∈ _root_.GlobalTheory.Size.thetaLevel R.ψ (Vc D i) (Wc D i) (U₁ ⊓ U₀) := thetaLevel_anti inf_le_left hl₁
  have hpl : ∀ P, R.ptP i t P ∈ _root_.GlobalTheory.Size.thetaLevel R.ψ (Vc D i) (Wc D i) (U₁ ⊓ U₀) := fun P =>
    thetaLevel_anti inf_le_right (hptl P)
  have hml : ∀ P, f - R.ptP i t P ∈ _root_.GlobalTheory.Size.thetaLevel R.ψ (Vc D i) (Wc D i) (U₁ ⊓ U₀) := fun P => sub_mem hfl (hpl P)
  obtain ⟨Ae, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D (Vc D i).rank (Wc D i).rank
  obtain ⟨C, hC0, hC⟩ := (H (Vc D i) (Wc D i) rfl rfl).real R.ψ hθ hUo
  have hp : (Vc D i).IsPosDef := hm.vpos i
  have hpd : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ =>
    GlobalTheory.RepsObj.gramAt_posDef hp (D.sp.V_sig ((i : ℕ) + 1)) τ
  obtain ⟨K, hK, hKc⟩ := GlobalTheory.definite_unitary_cocompact (Vc D i) hpd
  obtain ⟨HK, hHK⟩ := hK.exists_bound_of_continuousOn (continuous_height (Vc D i)).continuousOn
  have hHK0 : 0 ≤ HK := by
    obtain ⟨γ, -, c, hc, -⟩ := hKc 1
    exact (norm_nonneg _).trans (hHK c hc)
  have hg0 := height_pos (Wc D i) g
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = C * (HK * height (Wc D i) g) ^ Ae := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := hB ▸ by positivity
  have hbound : ∀ φ ∈ _root_.GlobalTheory.Size.thetaLevel R.ψ (Vc D i) (Wc D i) (U₁ ⊓ U₀), ∀ h,
      ‖thetaKO (R.ωP i t) h g φ‖ ≤ B * (sobO R.ψ R.θ μ 𝓕 d φ).toReal := by
    intro φ hφ h
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hKc h
    rw [GlobalTheory.ChainOnto.ThetaSwap.thetaKO_left_fst hω hφ.1 γ hγ c g]
    have h1 := (hC _ _ (R.ωP i t) hω μ 𝓕 hμ φ hφ).2 c g
    have hc1 : height (Vc D i) c ≤ HK := (Real.le_norm_self _).trans (hHK c hc)
    have hc0 := height_pos (Vc D i) c
    have hs : 0 ≤ (sobO R.ψ R.θ μ 𝓕 d φ).toReal := ENNReal.toReal_nonneg
    have h2 : C * (sobO R.ψ R.θ μ 𝓕 d φ).toReal * (height (Vc D i) c * height (Wc D i) g) ^ Ae ≤
        C * (sobO R.ψ R.θ μ 𝓕 d φ).toReal * (HK * height (Wc D i) g) ^ Ae :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_pos hc0 hg0).le
        (mul_le_mul_of_nonneg_right hc1 hg0.le) Ae) (mul_nonneg hC0 hs)
    have h3 : C * (sobO R.ψ R.θ μ 𝓕 d φ).toReal * (HK * height (Wc D i) g) ^ Ae =
        B * (sobO R.ψ R.θ μ 𝓕 d φ).toReal := by rw [hB]; ring
    exact h1.trans (h2.trans_eq h3)
  have hl1 : IntegrableOn (fun h => l (R.extV i t y h)) (R.fdV i t) (R.νV i t) := integrableOn_extV R hm i t y l
  have hint : ∀ φ ∈ _root_.GlobalTheory.Size.thetaLevel R.ψ (Vc D i) (Wc D i) (U₁ ⊓ U₀),
      IntegrableOn (fun h => thetaKO (R.ωP i t) h g φ * l (R.extV i t y h)) (R.fdV i t) (R.νV i t) := fun φ hφ =>
    Integrable.bdd_mul hl1 ((hω.om_cont φ hφ.1 0).comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
      (.of_forall (hbound φ hφ))
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = ∫ h in R.fdV i t, ‖l (R.extV i t y h)‖ ∂(R.νV i t) := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := hMdef ▸ integral_nonneg fun _ => norm_nonneg _
  have hpos : 0 < B * M + 1 := by positivity
  refine ⟨d, ENNReal.ofReal (ε / (B * M + 1)), ENNReal.ofReal_pos.2 (by positivity), fun P hP => ?_⟩
  have hs := ENNReal.toReal_lt_of_lt_ofReal hP
  have hs0 : 0 ≤ (sobO R.ψ R.θ μ 𝓕 d (f - R.ptP i t P)).toReal := ENNReal.toReal_nonneg
  have e : downInt R i t y f l g - downInt R i t y (R.ptP i t P) l g =
      ∫ h in R.fdV i t, thetaKO (R.ωP i t) h g (f - R.ptP i t P) * l (R.extV i t y h) ∂(R.νV i t) := by
    have i1 := hint f hfl
    have i2 := hint (R.ptP i t P) (hpl P)
    have e1 := integral_sub i1 i2
    refine e1.symm.trans (integral_congr_ae (.of_forall fun h => ?_))
    have e2 : R.ωP i t (h, g) (f - R.ptP i t P) = R.ωP i t (h, g) f - R.ωP i t (h, g) (R.ptP i t P) :=
      LinearMap.map_sub _ _ _
    show thetaKO (R.ωP i t) h g f * l (R.extV i t y h) - thetaKO (R.ωP i t) h g (R.ptP i t P) * l (R.extV i t y h) =
      thetaKO (R.ωP i t) h g (f - R.ptP i t P) * l (R.extV i t y h)
    refine (sub_mul _ _ _).symm.trans (congrArg (· * l (R.extV i t y h)) ?_)
    exact (congrFun e2 0).symm
  rw [e]
  have hle := norm_integral_le_of_norm_le (μ := (R.νV i t).restrict (R.fdV i t))
    (f := fun h => thetaKO (R.ωP i t) h g (f - R.ptP i t P) * l (R.extV i t y h))
    (hl1.norm.const_mul (B * (sobO R.ψ R.θ μ 𝓕 d (f - R.ptP i t P)).toReal))
    (.of_forall fun h => by
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hbound _ (hml P) h) (norm_nonneg _)))
  rw [integral_const_mul, ← hMdef] at hle
  calc _ ≤ _ := hle
    _ ≤ (B * M + 1) * (sobO R.ψ R.θ μ 𝓕 d (f - R.ptP i t P)).toReal := by nlinarith
    _ < (B * M + 1) * (ε / (B * M + 1)) := by gcongr
    _ = ε := by field_simp

end GlobalTheory.DownLift.Sobolev₂
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.pow_dvd_galoisComparison_matrix : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → (∀ g, IsUnit (ρ g)) → ∀ (g : ↥(GK K)) (ε : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)), ht.Rel (B := ainfObj K) (BK.hf bk.ι X) bk.ι ((ainfHom K g).comp bk.ι) ε → ∀ (k : ℕ) (y : Matrix (Fin d) (Fin d) (Ainf l)), y.map bk.iA = ((l : ℕ) : bk.DA bk.ρ₀) ^ k • ε → ∀ i j, ((l : ℕ) : Ainf l) ^ k ∣ y i j := by
  first | exact @GlobalTheory.BSP.pow_dvd_of_rel_gal | exact GlobalTheory.BSP.pow_dvd_of_rel_gal | (intros; apply GlobalTheory.BSP.pow_dvd_of_rel_gal <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_beta_limit_bdRPlus_deRhamFrame : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ), F.IsDR → ∃ B : Matrix (Fin d) (Fin d) (Per.BdRp l), ∀ m : ℕ, ∃ (k : ℕ) (β : Matrix (Fin d) (Fin d) bk.S), F.IsBeta m k β ∧ ∀ i j, aDp l (bk.ev (β i j)) - (l : Per.BdRp l) ^ k * B i j ∈ Per.FilP l m := by
  first | exact @GlobalTheory.BKLim.exists_beta_limit | exact GlobalTheory.BKLim.exists_beta_limit | (intros; apply GlobalTheory.BKLim.exists_beta_limit <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_equivariantMap_breuilKisinMatrix : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N N' d d' : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') (ℤ_[l])) (F : Pre bk N d ρ) (F' : Pre bk N' d' ρ') (f : Matrix (Fin d') (Fin d) (ℤ_[l])), (∀ g, f * ρ g = ρ' g * f) → ∃ Y : Matrix (Fin d') (Fin d) (bk.S), F'.T * Y.map bk.evW = zW f * F.T := by
  first | exact @GlobalTheory.BKLim.EquivKisin.main | exact GlobalTheory.BKLim.EquivKisin.main | (intros; apply GlobalTheory.BKLim.EquivKisin.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.latticeBasis_frobenius_equation_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ Φ : bk.DS bk.ρ₀ →+* bk.DS bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) (frobS l bk.a) Φ → ((l : bk.DS bk.ρ₀) ^ s.c₁ * toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a bk.E) ^ s.N) • (ht.bas * ht.A.map (toDisc l (X : bk.S) bk.ρ₀)) = toDisc l (X : bk.S) bk.ρ₀ bk.E ^ (ht.a + 2 * s.N) • (s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * ht.bas.map Φ) := by
  first | exact @GlobalTheory.BSP.Height.bas_frob | exact GlobalTheory.BSP.Height.bas_frob | (intros; apply GlobalTheory.BSP.Height.bas_frob <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisin_beta_bounded_denominators : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (m : ℕ), ∃ c : ℕ, ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Frame bk N d ρ) (k : ℕ) (β : Matrix (Fin d) (Fin d) (bk.S)), F.IsBeta m k β → ∃ β', F.IsBeta m c β' := by
  first | (exact @GlobalTheory.BKLim.beta_bdd_denominators) | (exact GlobalTheory.BKLim.beta_bdd_denominators) | (intros; apply GlobalTheory.BKLim.beta_bdd_denominators  <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_etaleBasis_modPow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d d' n : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (ρ' : ↥(GK K) →* GL (Fin d') ℤ_[l]) (F' : Pre bk N d' fun g => (ρ' g).val) (Pi : Matrix (Fin d) (Fin d') (ℤ_[l])), 1 ≤ n → Onto (fun g => (ρ g).val) (fun g => (ρ' g).val) Pi n → ∃ (Tn : Matrix (Fin d) (Fin d) (WCb l)) (R : Matrix (Fin d) (Fin d') (WCb l)) (R' : Matrix (Fin d') (Fin d) (WCb l)), IsUnit Tn ∧ (∀ i j, R i j ∈ bk.OE) ∧ (∀ i j, R' i j ∈ bk.OE) ∧ (∀ i j, (l : WCb l) ^ n ∣ (zW Pi * F'.T - Tn * R) i j) ∧ (∀ i j, (l : WCb l) ^ n ∣ (zW Pi * F'.T * R' - Tn) i j) := by
  first | exact @GlobalTheory.BKLim.etBasis_modPow | exact GlobalTheory.BKLim.etBasis_modPow | (intros; apply GlobalTheory.BKLim.etBasis_modPow <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisin_comparison_unit_cocycle_every_prism : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (ε : Matrix (Fin d) (Fin d) En.Q.A), ht.Rel (BK.hf En.inl X) En.inl En.inr (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)) → ∀ (B : Obj l ↥(OL K)), (∀ k : Hom En.Q B, k.comp En.inl = k.comp En.inr → ε.map k.f = 1) ∧ ∀ k₁ k₂ k₃ : Hom En.Q B, k₁.comp En.inr = k₂.comp En.inl → k₁.comp En.inl = k₃.comp En.inl → k₂.comp En.inr = k₃.comp En.inr → ε.map k₁.f * ε.map k₂.f = ε.map k₃.f := by
  first | exact @GlobalTheory.BSP.StratCocycle.unit_cocycle | exact GlobalTheory.BSP.StratCocycle.unit_cocycle | (intros; apply GlobalTheory.BSP.StratCocycle.unit_cocycle <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.RawLift

theorem rallisConv_of_steps : ∀ D : D7, SWPair D → EisAbs D → KerAbs D → TermMove D → TermInv D → CuspKill D → RallisConv D := by
  intro D hSW hEis hKer hMove hInv hKill θ ψ V W χV χW om hθ hω hsig hpos hbig νV 𝓗 νW 𝓖 μ 𝓕 hνV h𝓗 hνW h𝓖
    hμ h𝓕 h1 f₁ f₂ φ₁ φ₂ hf₁ hf₂ hφ₁ hc₁ hφ₂ hc₂
  have hS : SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 (lagFrame W) :=
    { weil := hω, sigOK := hsig, pos := hpos, big := hbig, haarV := hνV, fdV := h𝓗, haarW := hνW, fdW := h𝓖,
      covol := ⟨hμ, h𝓕, h1⟩, frame := lagFrame_isLagFrame W }
  obtain ⟨K1, K2, K3⟩ := GlobalTheory.T.rallis_inner_product_kernel_identity D hKer hSW ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 _ hS θ hθ f₁ f₂ φ₁ φ₂ hf₁ hf₂ hφ₁ hc₁
    hφ₂ hc₂
  obtain ⟨-, E2, E3⟩ := GlobalTheory.T.siegelWeilSum_doubleIntegral_exchange_cuspForms D hEis ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 _ hS θ hθ f₁ f₂ φ₁ φ₂ hf₁ hf₂ hφ₁ hc₁ hφ₂ hc₂
  obtain ⟨G1, G2⟩ := GlobalTheory.T.lagrangianGraphs_sum_eq_matrixCoeff_integral D hEis hMove ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 _ hS θ hθ f₁ f₂ φ₁ φ₂ hf₁ hf₂ hφ₁ hc₁
    hφ₂ hc₂
  have N := GlobalTheory.T.rallis_nonGraphLagrangian_sum_eq_zero_cuspidal D hEis hMove hInv hKill (GlobalTheory.RawLift.TermCont.continuous_lagTerm D) ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 _ hS θ hθ f₁ f₂ φ₁ φ₂ hf₁ hf₂
    hφ₁ hc₁ hφ₂ hc₂
  refine ⟨K1, K2, G1, ?_⟩
  rw [K3, E3, ← E2.tsum_subtype_add_tsum_subtype_compl {Y : Lag W | Y.1.comap (LinearMap.inl D.host.E _ _) = ⊥}]
  erw [N, add_zero]
  rw [← G2]
  rfl

end GlobalTheory.RawLift

end
end
