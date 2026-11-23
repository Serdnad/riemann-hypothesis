module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlatSpaceComponents
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.TraceFormDualOneTraceFormDual
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle002
public import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle071
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle142
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle010
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle145
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NcardRationalPointsInTranslateLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle133
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfSymplZeroRight
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle144
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle143
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Twist.isCStable_inv_different_and_norm_ideal : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsCStable (D := D) ((D.host.ddE : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))⁻¹ ∧ GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsCStable (D := D) (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))⁻¹ * D.host.AA * D.host.AAbar) := by
  intro D
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have hs : ∀ x : D.host.E, star x = ReciprocityTheory.ChartRestriction.G.FD.cc x := fun _ => rfl
  have hcc : ∀ a : D.host.E, ReciprocityTheory.ChartRestriction.G.FD.cc a = D.host.conj a := fun a => bridge_star_holds D.R D.host a
  have key : ∀ nn : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E, nn ≠ 0 → GlobalTheory.conjFrac nn = nn →
      GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsCStable (D := D) nn := fun nn h0 h =>
    ⟨h0, fun x => by rw [hs, ← GlobalTheory.mem_conjFrac, h]⟩
  have hb : D.host.AAbar = GlobalTheory.conjFrac D.host.AA := by
    ext a
    rw [GlobalTheory.mem_conjFrac, hcc]
    exact ⟨Formalism.L2.Pj.conj_mem_AA D, fun ha => by
      simpa only [Formalism.L2.Pj.conj_conj] using Formalism.L2.Pj.conj_mem_AAbar D ha⟩
  have hA : D.host.AA ≠ 0 := Formalism.L2.Pj.AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D
  have hg : (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))⁻¹ ≠ 0 :=
    inv_ne_zero (Nat.cast_ne_zero.2 (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero))
  refine ⟨key _ (inv_ne_zero GlobalTheory.coe_different_ne_zero) ?_, key _ ?_ ?_⟩
  · rw [GlobalTheory.conjFrac_inv]
    exact congrArg _ GlobalTheory.conjFrac_different
  · rw [hb]
    exact mul_ne_zero (mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2 hg) hA) (GlobalTheory.conjFrac_ne_zero hA)
  · have hc : ReciprocityTheory.ChartRestriction.G.FD.cc (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))⁻¹ =
        (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))⁻¹ := by
      rw [hcc, map_inv₀, map_natCast]
    rw [hb, map_mul, map_mul, GlobalTheory.conjFrac_spanSingleton, GlobalTheory.conjFrac_conjFrac, hc, mul_right_comm]
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor.CompDecomp

open Filter Topology

theorem tendsto_one_sub_sum (F : Type) [Field F] [NumberField F] :
    Tendsto (fun Q : Finset (HeightOneSpectrum (𝓞 F)) => (1 : Af F) - ∑ v ∈ Q, singleV F v 1) atTop (𝓝 0) := by
  classical
  let A : (v : HeightOneSpectrum (𝓞 F)) → Set (v.adicCompletion F) :=
    fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  let y : Finset (HeightOneSpectrum (𝓞 F)) → (∀ v, A v) := fun Q v =>
    ⟨if v ∈ Q then 0 else 1, by
      by_cases h : v ∈ Q
      · rw [if_pos h]; exact (v.adicCompletionIntegers F).zero_mem
      · rw [if_neg h]; exact (v.adicCompletionIntegers F).one_mem⟩
  let z : ∀ v, A v := fun v => ⟨0, (v.adicCompletionIntegers F).zero_mem⟩
  have hy : Tendsto y atTop (𝓝 z) := by
    rw [tendsto_pi_nhds]
    intro v
    refine tendsto_nhds_of_eventually_eq ?_
    filter_upwards [Filter.eventually_ge_atTop {v}] with Q hQ
    have hv : v ∈ Q := Finset.singleton_subset_iff.mp hQ
    apply Subtype.ext
    show (if v ∈ Q then (0 : v.adicCompletion F) else 1) = 0
    rw [if_pos hv]
  have hc : Continuous (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      A Filter.cofinite) := RestrictedProduct.isEmbedding_structureMap.continuous
  have key : ∀ Q, (1 : Af F) - ∑ v ∈ Q, singleV F v 1 =
      RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) A Filter.cofinite (y Q) := by
    intro Q
    apply FiniteAdeleRing.ext
    intro w
    have hw : ((1 : Af F) - ∑ v ∈ Q, singleV F v 1) w = evalV F w ((1 : Af F) - ∑ v ∈ Q, singleV F v 1) := rfl

    rw [hw, map_sub, map_one, map_sum]
    show _ = (if w ∈ Q then (0 : w.adicCompletion F) else 1)
    by_cases h : w ∈ Q
    · rw [Finset.sum_eq_single_of_mem w h (fun b _ hb => GlobalTheory.LatVac.evalV_singleV_ne F b w (Ne.symm hb)),
        GlobalTheory.LatVac.evalV_singleV_same, if_pos h, sub_self]
    · rw [Finset.sum_eq_zero (fun b hb => GlobalTheory.LatVac.evalV_singleV_ne F b w (by rintro rfl; exact h hb)),
        if_neg h, sub_zero]
  have h0 : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) A
      Filter.cofinite z = (0 : Af F) :=
    by
      apply FiniteAdeleRing.ext
      intro w
      rfl
  have h1 : Tendsto (fun Q => (1 : Af F) - ∑ v ∈ Q, singleV F v 1) atTop
      (𝓝 (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) A
        Filter.cofinite z)) :=
    ((hc.tendsto z).comp hy).congr (fun Q => (key Q).symm)
  rw [h0] at h1
  exact h1

variable {D : D7}

private theorem infComponent_algebraMap_pairA {D : D7} (a : Ainf D.host.F) (b : Af D.host.F) :
    infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F a b)) = a ⊗ₜ[D.host.F] (1 : D.host.E) := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rfl

private theorem sum_sgW_plTau_eq_one (D : D7) :
    ∑ τ : D.what₂.Tau, GlobalTheory.AutFunCompare.sgW (plTau D τ) 1 = (1 : Ainf D.host.F) := by
  classical
  have hb := (GlobalTheory.CMTypePlaces.places_bijective D).sum_comp
    (fun w : InfinitePlace D.host.F => GlobalTheory.AutFunCompare.sgW w (1 : w.Completion))
  have h : ∑ w : InfinitePlace D.host.F, GlobalTheory.AutFunCompare.sgW w (1 : w.Completion) = (1 : Ainf D.host.F) := by
    have h' := Finset.univ_sum_single (1 : ∀ w : InfinitePlace D.host.F, w.Completion)
    simp only [Pi.one_apply] at h'
    simp only [GlobalTheory.AutFunCompare.sgW]
    exact h'
  exact hb.trans h

private theorem af_ext_of_fstA_sndA {F : Type} [Field F] [NumberField F] {x y : AF F}
    (h1 : fstA F x = fstA F y) (h2 : sndA F x = sndA F y) : x = y :=
  Prod.ext h1 h2

private theorem fstA_pairA_twisted_operators {F : Type} [Field F] [NumberField F] (a : Ainf F) (b : Af F) :
    fstA F (pairA F a b) = a := rfl

private theorem sndA_pairA_twisted_operators {F : Type} [Field F] [NumberField F] (a : Ainf F) (b : Af F) :
    sndA F (pairA F a b) = b := rfl

theorem one_sub_sum_idem (P : Finset (Place D)) (hP : P.toRight = Finset.univ) :
    1 - ∑ p ∈ P, idem D p = algebraMap (AF D.host.F) (AE D)
      (pairA D.host.F 0 (1 - ∑ v ∈ P.toLeft, singleV D.host.F v 1)) := by
  rw [Finset.sum_sum_eq_sum_toLeft_add_sum_toRight, hP]

  rw [show (1 : AE D) - (∑ v ∈ P.toLeft, idem D (.inl v) + ∑ τ : D.what₂.Tau, idem D (.inr τ)) =
    algebraMap (AF D.host.F) (AE D) (1 - (∑ v ∈ P.toLeft, pairA D.host.F 0 (singleV D.host.F v 1) +
      ∑ τ : D.what₂.Tau, pairA D.host.F (GlobalTheory.AutFunCompare.sgW (plTau D τ) 1) 0)) by
  rw [map_sub, map_add (f := _), map_one, map_sum, map_sum]
  rfl]
  congr 1
  apply af_ext_of_fstA_sndA

  · simp [fstA_pairA_twisted_operators, map_sum, sum_sgW_plTau_eq_one D]

  · simp [sndA_pairA_twisted_operators, map_sum]

theorem exists_eq_sum_wAt_add_two_smul : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ w : WO S T, ∃ P₀ : Finset (Place D), ∀ P : Finset (Place D), P₀ ⊆ P → ∃ u ∈ (latO S T ΛS ΛT fun _ => True), w = ∑ p ∈ P, wAt p w + 2 • u := by
  intro D S T ΛS ΛT hS hT w
  classical
  have hU := GlobalTheory.LatOpen.isOpen_nsmul_latO D S T ΛS ΛT hS hT 2 two_pos
  let g : Af D.host.F → WO S T := fun e => algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 e) • w
  have hg : Continuous g := by
    have h1 : Continuous fun e : Af D.host.F => pairA D.host.F 0 e :=
      (continuous_const.prodMk continuous_id : Continuous fun e : Af D.host.F => ((0 : Ainf D.host.F), e))
    have h2 : Continuous (algebraMap (AF D.host.F) (AE D)) := by
      have hs : (algebraMap (AF D.host.F) (AE D) : AF D.host.F → AE D) = fun r => r • (1 : AE D) := by
        funext r
        exact Algebra.algebraMap_eq_smul_one r
      rw [hs]
      exact Continuous.smul (f := fun r : AF D.host.F => r) (g := fun _ : AF D.host.F => (1 : AE D))
        continuous_id continuous_const
    exact (h2.comp h1).smul continuous_const
  have hg0 : g 0 = 0 := by
    show algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 0) • w = 0
    rw [show pairA D.host.F 0 0 = 0 from rfl, map_zero, zero_smul]
  have hlim : Tendsto (fun Q => g (1 - ∑ v ∈ Q, singleV D.host.F v 1)) atTop (𝓝 0) := by
    have h := (hg.tendsto 0).comp (tendsto_one_sub_sum D.host.F)
    rw [hg0] at h
    exact h
  have hmem : (0 : WO S T) ∈ {x : WO S T | ∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E))
      (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), (x - (2 : ℕ) • l).map (finPart D) = 0} := by
    simp only [Set.mem_ofPred_eq]
    refine ⟨0, zero_mem _, ?_⟩
    simp
  obtain ⟨Q₀, hQ₀⟩ := Filter.eventually_atTop.1 (hlim.eventually_mem (hU.mem_nhds hmem))
  refine ⟨Q₀.disjSum Finset.univ, fun P hP => ?_⟩
  have hR : P.toRight = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro τ
    rw [Finset.mem_toRight]
    exact hP (Finset.inr_mem_disjSum.2 (Finset.mem_univ τ))
  have hL : Q₀ ⊆ P.toLeft := by
    intro v hv
    rw [Finset.mem_toLeft]
    exact hP (Finset.inl_mem_disjSum.2 hv)
  obtain ⟨l, hl, hfin⟩ := hQ₀ _ hL
  refine ⟨l, hl, ?_⟩
  have hrest : w - ∑ p ∈ P, wAt p w = g (1 - ∑ v ∈ P.toLeft, singleV D.host.F v 1) := by
    show w - ∑ p ∈ P, wAt p w =
      algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (1 - ∑ v ∈ P.toLeft, singleV D.host.F v 1)) • w
    rw [← one_sub_sum_idem P hR, sub_smul, one_smul, Finset.sum_smul]
    congr 1
  have hl0 := GlobalTheory.SplitScalar.latO_fin hl
  have h2l : g (1 - ∑ v ∈ P.toLeft, singleV D.host.F v 1) = (2 : ℕ) • l := by
    ext i j
    apply GlobalTheory.SplitScalar.adele_ext
    · have hij := congrFun (congrFun hl0 i) j
      simp only [Matrix.map_apply, Matrix.zero_apply] at hij
      show infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (1 - ∑ v ∈ P.toLeft, singleV D.host.F v 1))
        * w i j) = infPart D ((2 : ℕ) • l i j)
      rw [map_mul, infComponent_algebraMap_pairA, TensorProduct.zero_tmul, zero_mul, map_nsmul, hij, smul_zero]
    · have hij := congrFun (congrFun hfin i) j
      simp only [Matrix.map_apply, Matrix.zero_apply, Matrix.sub_apply, map_sub] at hij
      exact sub_eq_zero.1 hij
  rw [← h2l, ← hrest]
  exact (add_sub_cancel _ _).symm

end GlobalTheory.PlaceTensor.CompDecomp
end

section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

theorem _root_.GlobalTheory.T.strictInterlace_ganGrossPrasad_big_small : ∀ (S : Sizes) (Q : Entries S), Q.Good → GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.Interlace Q.bigPar Q.smallPar := by
  first | exact @GlobalTheory.StrictInterlace.interlace_big_small | exact GlobalTheory.StrictInterlace.interlace_big_small | (intros; apply GlobalTheory.StrictInterlace.interlace_big_small <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.nonempty_algHom_completion_of_split_place : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
    ¬ GlobalTheory.WeilParts.NonSplitAt D v ε → Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F v) := by
  first | exact @GlobalTheory.SplitPlaceEmb.nonempty_algHom_of_not_nonSplitAt | exact GlobalTheory.SplitPlaceEmb.nonempty_algHom_of_not_nonSplitAt | (intros; apply GlobalTheory.SplitPlaceEmb.nonempty_algHom_of_not_nonSplitAt <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.LFun.ConjParam

section General

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {K : Subgroup G}

theorem conj_mem_hecke {h : G → ℂ} (hh : h ∈ Hecke ℂ K) : (fun g => starRingEnd ℂ (h g)) ∈ Hecke ℂ K := by
  obtain ⟨h1, S, hS⟩ := hh
  exact ⟨fun a b g => congrArg _ (h1 a b g), S, fun g hg => hS g fun h0 => hg (by simp [h0])⟩

theorem eigen_conj (hK : IsCommensurated K) (hinv : ∀ g : G, ∃ k₁ ∈ K, ∃ k₂ ∈ K, g⁻¹ = k₁ * g * k₂)
    {ρ : Representation ℂ G V} (hρ : GlobalTheory.LGrp.IsUnitarisable ρ) {x : V} (h0 : x ≠ 0) (hx : x ∈ fixed ρ K)
    {h : G → ℂ} (hh : h ∈ Hecke ℂ K) {a b : ℂ} (ha : heckeVec ρ K h x = a • x)
    (hb : heckeVec ρ K (fun g => starRingEnd ℂ (h g)) x = b • x) : starRingEnd ℂ b = a := by
  obtain ⟨B, hB, hpos, hinvB⟩ := hρ
  have hfix := GlobalTheory.LGrp.mem_fixed.1 hx
  have hreal : ∀ g, starRingEnd ℂ (B (ρ g x) x) = B (ρ g x) x := fun g => by
    obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := hinv g
    have e1 : B x (ρ g x) = B (ρ g⁻¹ x) x := by
      rw [← hinvB g (ρ g⁻¹ x) x, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    have e2 : B (ρ k₁ (ρ g x)) x = B (ρ g x) x := by
      rw [← hinvB k₁ (ρ g x) x, hfix k₁ hk₁]
    rw [← hB, e1, e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hfix k₂ hk₂, e2]
  have key : ∀ f ∈ Hecke ℂ K, B (heckeVec ρ K f x) x = ∑ᶠ c : G ⧸ K, f c.out * B (ρ c.out x) x := fun f hf => by
    refine ((B.flip x).toAddMonoidHom.map_finsum (finite_heckeVec hK hf ρ x)).trans (finsum_congr fun c => ?_)
    simp
  have hxx : starRingEnd ℂ (B x x) = B x x := (hB x x).symm
  have hne : B x x ≠ 0 := fun e => by simpa [e] using hpos x h0
  have e1 := key h hh
  have e2 := congrArg (starRingEnd ℂ) (key _ (conj_mem_hecke hh))
  rw [ha] at e1
  rw [hb, show ⇑(starRingEnd ℂ) = (starAddEquiv : ℂ ≃+ ℂ) from rfl, AddEquiv.map_finsum] at e2
  apply mul_right_cancel₀ hne
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at e1 e2
  rw [e1]
  refine Eq.trans ?_ (e2.trans (finsum_congr fun c => ?_))
  · change _ = starRingEnd ℂ _
    rw [map_mul, hxx]
  · change starRingEnd ℂ _ = _
    rw [map_mul, hreal]
    exact congrArg (· * _) (Complex.conj_conj _)

end General

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

theorem conj_satU {m : ℕ} (ϖ : L) (q : ℕ) (h : GU σ n → ℂ) (α : Fin m → ℂ) :
    starRingEnd ℂ (SatU ϖ q (fun g => starRingEnd ℂ (h g)) α) = SatU ϖ q h fun i => starRingEnd ℂ (α i) := by
  have hs : ∀ {ι : Type} (f : ι → ℂ), starRingEnd ℂ (∑ᶠ i, f i) = ∑ᶠ i, starRingEnd ℂ (f i) := fun f =>
    AddEquiv.map_finsum (starAddEquiv : ℂ ≃+ ℂ) f
  unfold SatU
  rw [hs]
  refine finsum_congr fun a => ?_
  rw [map_mul, hs, map_prod]
  congr 1
  · simp
  · refine finsum_congr fun c => ?_
    split_ifs <;> simp

theorem inv_mem {ϖ : L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (g : GU σ n) :
    ∃ k₁ ∈ KU σ n, ∃ k₂ ∈ KU σ n, g⁻¹ = k₁ * g * k₂ := by
  have hint : ∀ i j, antiJ L n i j ∈ intL L := by
    intro i j; unfold antiJ; split_ifs
    · exact one_mem _
    · exact zero_mem _
  obtain ⟨J, hJ, hJe⟩ := P.cartan_exists_glint (intL L) _ _
    (GlobalTheory.UnitarySwap.antiJ_mul_self (L := L) (n := n)) hint hint
  obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := GlobalTheory.UnitarySwap.inv_mem_doubleCoset hU hJ (g := (g : GL (Fin n) L)) (by
    intro i j
    rw [hJe]
    simp only [antiJ, add_comm i.val j.val]
    split_ifs <;> simp) (by rw [hJe]; exact g.2)
  rw [hJe] at hk₁ hk₂
  exact ⟨⟨k₁, hk₁.1⟩, hk₁, ⟨k₂, hk₂.1⟩, hk₂, Subtype.ext e⟩

theorem satU_star_eq : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V) (x : V) (α : Fin (n / 2) → ℂˣ), GlobalTheory.LGrp.IsUnitarisable ρ → IsSatVecU ϖ q ρ x α → ∀ h ∈ Hecke ℂ (KU σ n), SatU ϖ q h (fun i => ((star (α i) : ℂˣ) : ℂ)) = SatU ϖ q h (fun i => (α i : ℂ)) := by
  intro L _ _ _ ϖ σ q n hU V _ _ ρ x α hρ hx h hh
  exact (conj_satU ϖ q h fun i => (α i : ℂ)).symm.trans
    (eigen_conj (P.isCommensurated_integral_unitary_of_unramified hU n) (inv_mem hU) hρ hx.1 hx.2.1 hh (hx.2.2 h hh) (hx.2.2 _ (conj_mem_hecke hh)))

end GlobalTheory.LFun.ConjParam

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.addHaar_leftRightMul_adelicMatrices_module : ∀ (D : D7) (m n : ℕ) (μ : Measure (Mx D m n)), μ.IsAddHaarMeasure → ∀ (g : GL (Fin m) (AE D)) (a : GL (Fin n) (AE D)), μ = ((GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det g) : ENNReal) ^ n * (GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ENNReal) ^ m) • Measure.map (fun u : Mx D m n => (HMul.hMul (HMul.hMul g.val (u : Matrix (Fin m) (Fin n) (AE D))) a.val : Mx D m n)) μ := by
  first | exact @GlobalTheory.ModuLR.modu_lrMul | exact GlobalTheory.ModuLR.modu_lrMul | (intros; apply GlobalTheory.ModuLR.modu_lrMul <;> assumption)
end

section

open MeasureTheory NumberField Matrix Formalism.MainNotions.S GlobalTheory.Count Formalism.REAL Formalism.HN

theorem _root_.GlobalTheory.T.automorphicPoint_exists_isotropic_reduction_of_small_size : ∀ (I : AutInst) (x : I.GA) (g q : ℕ), 1 ≤ g → 1 ≤ q → 1 ≤ I.n → (∀ v, rkR (I.ε v) ≤ q) → least I x < 1 / 2 → ∃ W, I.IsIsot W ∧ ∀ m ∈ I.NA W, ∃ γ ∈ I.GFset, ∃ k ∈ I.Kg g, ∃ (u : I.Ginf) (A Z : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ), (∀ v, inG (I.ε v) (A v) ∧ inG (I.ε v) (Z v)) ∧ (∀ v, uMat (u v) = NormedSpace.exp (A v) * NormedSpace.exp (Z v)) ∧ m * x = γ * x * (u, k) ∧ Real.sqrt (∑ v, hs (A v)) + Real.sqrt (∑ v, hs (Z v)) ≤ (I.n : ℝ) ^ 2 * Real.sqrt I.f * g * I.rd * (2 * least I x) ^ ((1 : ℝ) / q) / 4 := by
  first | exact @GlobalTheory.DeepPoint.deep_point | exact GlobalTheory.DeepPoint.deep_point | (intros; apply GlobalTheory.DeepPoint.deep_point <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.ncard_rational_points_in_translate_le_height_pow : ∀ {D : D7} {V : HSp D} {Ω : Set (GA D V)}, IsCompact Ω → ∃ (A : ℕ) (C : ℝ), ∀ g x : GA D V, {γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω}.Finite ∧ ({γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω}.ncard : ℝ) ≤ C * GlobalTheory.Grow.height V g ^ (2 * A) := by
  first | exact @GlobalTheory.RatCount.ncard_rat_mem_translate_le | exact GlobalTheory.RatCount.ncard_rat_mem_translate_le | (intros; apply GlobalTheory.RatCount.ncard_rat_mem_translate_le <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField GlobalTheory.FinDecomp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinDecomp

theorem heisAvg_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (m : ℕ)
    (lam : WO S T → ℂ), (∀ x ∈ Λ, ∀ y ∈ Λ, lam (x + y) = lam x * lam y * ψ (symplOH S T x y)) →
    ∀ [Fintype (Qm m Λ)] (g : WO S T → ℂ), (∀ l ∈ Λ, lam (m • l) • heisO ψ S T (m • l) g = g) →
    ∀ b ∈ Λ, lam b • heisO ψ S T b (∑ q : Qm m Λ, lam (repm q) • heisO ψ S T (repm q) g) =
      ∑ q : Qm m Λ, lam (repm q) • heisO ψ S T (repm q) g := by
  intro D ψ S T Λ m lam hlam _ g hg b hb
  have hsm : ∀ (x : WO S T) (c : ℂ) (f : WO S T → ℂ), heisO ψ S T x (c • f) = c • heisO ψ S T x f := by
    intro x c f; funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
  have hsumlin : ∀ (x : WO S T) (F : Qm m Λ → WO S T → ℂ),
      heisO ψ S T x (∑ q, F q) = ∑ q, heisO ψ S T x (F q) := by
    intro x F; funext w; simp only [heisO, Finset.sum_apply, Finset.mul_sum]
  have hmul : ∀ x ∈ Λ, ∀ y ∈ Λ, lam x • heisO ψ S T x (lam y • heisO ψ S T y g) =
      lam (x + y) • heisO ψ S T (x + y) g := by
    intro x hx y hy
    rw [hsm, GlobalTheory.FinTranslate.heisO_heisO, smul_smul, smul_smul, hlam x hx y hy]
  have key : ∀ q : Qm m Λ, lam b • heisO ψ S T b (lam (repm q) • heisO ψ S T (repm q) g) =
      lam (repm ((QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ) + q)) •
        heisO ψ S T (repm ((QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ) + q)) g := by
    intro q
    have hbq : b + repm q ∈ Λ := Λ.add_mem hb (repm_mem q)
    rw [hmul b hb _ (repm_mem q)]
    have hmk : (QuotientAddGroup.mk (⟨b + repm q, hbq⟩ : Λ) : Qm m Λ) =
        (QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ) + q := by
      conv_rhs => rw [← mk_repm q]
      rfl
    have h1 := repm_mk_sub (m := m) hbq
    rw [hmk] at h1
    obtain ⟨l, hl, hl'⟩ := mem_mLat.1 h1
    have he : repm ((QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ) + q) = (b + repm q) + m • l := by
      rw [hl']; abel
    rw [he, ← hmul _ hbq _ (Λ.nsmul_mem hl m), hg l hl]
  calc lam b • heisO ψ S T b (∑ q : Qm m Λ, lam (repm q) • heisO ψ S T (repm q) g)
      = ∑ q : Qm m Λ, lam (repm ((QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ) + q)) •
          heisO ψ S T (repm ((QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ) + q)) g := by
        rw [hsumlin, Finset.smul_sum]
        exact Finset.sum_congr rfl fun q _ => key q
    _ = _ := Equiv.sum_comp (Equiv.addLeft (QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ))
          (fun q => lam (repm q) • heisO ψ S T (repm q) g)

end GlobalTheory.FinDecomp

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.symplectic_restriction_isotropic_part_eq_pairing : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ K : Matrix (Fin r) (Fin V.rank) D.host.E, K * C = 1 → ∀ a t : Mx D W.rank r, symplO V W (restEmb V W K t) (isoPart V W C a) = halfSympl W a t := by
  first | exact @GlobalTheory.HalfAverage.sympl_restEmb_isoPart | exact GlobalTheory.HalfAverage.sympl_restEmb_isoPart | (intros; apply GlobalTheory.HalfAverage.sympl_restEmb_isoPart <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_pos_integral_halfAdelicMatrix_leftMul_eq : ∀ (D : D7) (a : AE D) (m n : ℕ) (M M' : Matrix (Fin m) (Fin m) (AE D)), M * M' = 1 → M' * M = 1 → ∃ κ : ℝ, 0 < κ ∧ ∀ φ : halfMx a m n → ℂ, ∫ t, φ (leftMul a M t) ∂haarHalf a m n = κ * ∫ t, φ t ∂haarHalf a m n := by
  first | exact @GlobalTheory.HalfAverage.integral_leftMul_eq_smul | exact GlobalTheory.HalfAverage.integral_leftMul_eq_smul | (intros; apply GlobalTheory.HalfAverage.integral_leftMul_eq_smul <;> assumption)
end
