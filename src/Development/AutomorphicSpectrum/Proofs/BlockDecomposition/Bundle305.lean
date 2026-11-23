module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantOrbit
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle052
public import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.HlamStable
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.GenericPrincipalSeries.GenericPrincipalSeries
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Mathlib.RingTheory.PiTensorProduct
public import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle006
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.IntegrableOfContinuousCompact
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.KSchur
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle004
import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.MomB

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.IwahoriTraceProof

namespace GlobalTheory.CompanionTheory.IwahoriCount

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem finite_cosets {I : Subgroup G} (ho : IsOpen (I : Set G)) {D : Set G} (hD : IsCompact D) :
    {q : G ⧸ I | q.out ∈ D}.Finite := by
  haveI : DiscreteTopology (G ⧸ I) := QuotientGroup.discreteTopology ho
  have h : IsCompact ((QuotientGroup.mk : G → G ⧸ I) '' D) := hD.image QuotientGroup.continuous_mk
  exact h.finite_of_discrete.subset fun q hq => ⟨q.out, hq, QuotientGroup.out_eq' q⟩

theorem measure_eq_card_mul [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
    {I : Subgroup G} (ho : IsOpen (I : Set G)) {D : Set G} (hD : ∀ g ∈ D, ∀ i ∈ I, g * i ∈ D)
    (S : Finset (G ⧸ I)) (hS : ∀ q, q ∈ S ↔ q.out ∈ D) : μ D = S.card * μ I :=
  _root_.UpperTheory.Reformulated.B.Yla7.main μ ho hD S hS

end Abstract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem iwahoriCoset_mul {t : Fin n → kˣ} {g i : GL (Fin n) k} (hg : g ∈ iwahoriCoset t)
    (hi : i ∈ iwahori k (Fin n)) : g * i ∈ iwahoriCoset t := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hg
  exact ⟨a, ha, b * i, mul_mem hb hi, by simp only [mul_assoc]⟩

theorem mk_act {t : Fin n → kˣ} (ht : Contracts t) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) {v : V} (hv : v ∈ fixed π (iwahori k (Fin n)))
    {g : GL (Fin n) k} (hg : g ∈ iwahoriCoset t) :
    (Submodule.Quotient.mk (π g v) : Jacquet π (unipB k (Fin n))) = jacBU π t (Submodule.Quotient.mk v) := by
  obtain ⟨u, hu, -, i, hi, rfl⟩ := (mem_iwahoriCoset ht g).1 hg
  rw [jacBU_mk, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, IwahoriInj.mem_fixed.1 hv i hi]
  exact (Submodule.Quotient.eq _).2 (IwahoriInj.sub_mem_twKer hu _)

theorem card_cosets {t : Fin n → kˣ} (ht : Contracts t) (S : Finset (GL (Fin n) k ⧸ iwahori k (Fin n)))
    (hS : ∀ q, q ∈ S ↔ q.out ∈ iwahoriCoset t) : (S.card : ℝ) = (deltaB t)⁻¹ := by
  have ho := IwahoriOnto.isOpen_iwahori k (Fin n)
  have hc := IwahoriOnto.isCompact_iwahori k (Fin n)
  letI : MeasurableSpace (GL (Fin n) k) := _root_.borel _
  haveI : BorelSpace (GL (Fin n) k) := ⟨rfl⟩
  haveI : LocallyCompactSpace (GL (Fin n) k) :=
    hc.locallyCompactSpace_of_mem_nhds_of_group (ho.mem_nhds (one_mem _))
  let μ : Measure (GL (Fin n) k) := Measure.haar
  have h1 := measure_iwahoriCoset μ ht
  have h2 := measure_eq_card_mul μ ho (fun g hg i hi => iwahoriCoset_mul hg hi) S hS
  have h3 : μ.real (iwahoriCoset t) = S.card * μ.real (iwahori k (Fin n) : Set (GL (Fin n) k)) := by
    rw [measureReal_def, measureReal_def, h2, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have h4 : μ.real (iwahori k (Fin n) : Set (GL (Fin n) k)) ≠ 0 := by
    rw [measureReal_def]
    exact (ENNReal.toReal_pos (ho.measure_pos μ ⟨1, one_mem _⟩).ne' hc.measure_lt_top.ne).ne'
  rw [h3, mul_comm] at h1
  exact mul_left_cancel₀ h4 h1

theorem cosetCount : PositivityTheory.Rg.BcB.F.Tail.PExp.CosetCount := by
  intro k _ _ _ _ n t ht
  have hset : {q : GL (Fin n) k ⧸ iwahori k (Fin n) | cosetInd t q.out ≠ 0} =
      {q | q.out ∈ iwahoriCoset t} := by
    ext q
    simp [cosetInd]
  have hfin : {q : GL (Fin n) k ⧸ iwahori k (Fin n) | q.out ∈ iwahoriCoset t}.Finite :=
    finite_cosets (IwahoriOnto.isOpen_iwahori k (Fin n)) (isCompact_iwahoriCoset t)
  refine ⟨hset ▸ hfin, fun V _ _ π v hv => ?_⟩
  have hcard := card_cosets ht hfin.toFinset fun q => hfin.mem_toFinset
  have hsum : PositivityTheory.Rg.BcB.F.Tail.PExp.hkS π (iwahori k (Fin n)) (cosetInd t) v =
      ∑ q ∈ hfin.toFinset, cosetInd t q.out • π q.out v := by
    refine finsum_eq_sum_of_support_subset _ fun q hq => ?_
    rw [Set.Finite.coe_toFinset]
    by_contra h
    apply hq
    have h0 : cosetInd t q.out = 0 := by
      by_contra h'
      exact h (hset ▸ h')
    simp [h0]
  rw [hsum]
  have hterm : ∀ q ∈ hfin.toFinset, (Submodule.Quotient.mk (cosetInd t q.out • π q.out v) :
      Jacquet π (unipB k (Fin n))) = jacBU π t (Submodule.Quotient.mk v) := by
    intro q hq
    have hq' : q.out ∈ iwahoriCoset t := hfin.mem_toFinset.1 hq
    have h1 : cosetInd t q.out = 1 := by simp [cosetInd, hq']
    rw [h1, one_smul]
    exact mk_act ht π hv hq'
  have hmk : (Submodule.Quotient.mk (∑ q ∈ hfin.toFinset, cosetInd t q.out • π q.out v) :
      Jacquet π (unipB k (Fin n))) = ∑ q ∈ hfin.toFinset,
        (Submodule.Quotient.mk (cosetInd t q.out • π q.out v) : Jacquet π (unipB k (Fin n))) :=
    map_sum (Submodule.mkQ _) _ _
  rw [hmk, Finset.sum_congr rfl hterm, Finset.sum_const, ← hcard, Complex.ofReal_natCast,
    Nat.cast_smul_eq_nsmul]

end GlobalTheory.CompanionTheory.IwahoriCount

end
end

section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory.CompanionTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 PositivityTheory.RgFd

variable {n : ℕ}

theorem cont_triple {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] [Group B]
    [IsTopologicalGroup B] (F : A × B → ℝ) (c : B → ℝ) (hF : Continuous F) (hc : Continuous c) :
    Continuous fun z : A × (B × B) => F (z.1, z.2.1) * F (z.1, z.2.2) * c (z.2.1⁻¹ * z.2.2) ^ 2 := by
  have h1 : Continuous fun z : A × (B × B) => F (z.1, z.2.1) :=
    hF.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have h2 : Continuous fun z : A × (B × B) => F (z.1, z.2.2) :=
    hF.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
  have h3 : Continuous fun z : A × (B × B) => c (z.2.1⁻¹ * z.2.2) :=
    hc.comp (((continuous_fst.comp continuous_snd).inv).mul (continuous_snd.comp continuous_snd))
  exact (h1.mul h2).mul (h3.pow 2)

theorem cont_slice {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] (f : A × B → ℝ)
    (hf : Continuous f) (a : A) : Continuous fun b : B => f (a, b) :=
  hf.comp (continuous_const.prodMk continuous_id)

theorem cK_continuous {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) :
    Continuous (cK T) := by
  have h : Continuous fun k : KG ε => T.op k T.w :=
    (KType_continuous_op T).clm_apply continuous_const
  have h2 : Continuous fun k : KG ε => ‖⟪T.w, T.op k T.w⟫_ℂ‖ := (continuous_const.inner h).norm
  exact h2

theorem hI_continuous (hC : PhiCont) {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ)
    (μ : Fin n → ℤ) :
    Continuous fun z : UJ ε × (KG ε × KG ε) => hI T μ (pP (toM z.1)) z.2 :=
  cont_triple (fun z : UJ ε × KG ε => phiK μ (pP (toM z.1)) z.2) (cK T) (hC n ε μ) (cK_continuous T)

theorem hI_measurable (hC : PhiCont) {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ)
    (μ : Fin n → ℤ) :
    Measurable fun z : UJ ε × (KG ε × KG ε) => hI T μ (pP (toM z.1)) z.2 :=
  (hI_continuous hC T μ).measurable

theorem hI_nonneg (hMul : PhiMul) {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ)
    (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) (p : KG ε × KG ε) :
    0 ≤ hI T μ x p := by
  have a := (hMul n ε μ 0 x hx p.1).1
  have b := (hMul n ε μ 0 x hx p.2).1
  exact mul_nonneg (mul_pos a b).le (sq_nonneg _)

theorem hI_integrable (hC : PhiCont) {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ)
    (μ : Fin n → ℤ) (g : UJ ε) :
    Integrable (fun p : KG ε × KG ε => hI T μ (pP (toM g)) p) ((dk ε).prod (dk ε)) := by
  haveI : IsProbabilityMeasure (dk ε) := (dk_props ε).1
  have hc : Continuous fun p : KG ε × KG ε => hI T μ (pP (toM g)) p :=
    cont_slice (fun z : UJ ε × (KG ε × KG ε) => hI T μ (pP (toM z.1)) z.2)
      (hI_continuous hC T μ) g
  exact integrableOn_univ.mp (hc.continuousOn.integrableOn_compact isCompact_univ)

theorem hsInt : HsPs → HsPol → PhiMul → PhiCont → HsInt := by
  intro hPs hPol hMul hC n ε Λ T μ
  refine ⟨hI_measurable hC T μ, fun g => ?_⟩
  obtain ⟨⟨X, hX, hE⟩, hN⟩ := hPol n ε (toM g) g.2
  have hpd : (pP (toM g)).PosDef := by
    rw [hE]
    exact exp_noncompactPart_posDef hX
  rw [hN Λ T μ, hPs n ε Λ T μ _ hpd, ENNReal.ofReal_mul (by positivity),
    ofReal_integral_eq_lintegral_ofReal (hI_integrable hC T μ g)
      (Filter.Eventually.of_forall (hI_nonneg hMul T μ hpd))]

end GlobalTheory.CompanionTheory.RgFd
end
end

section

noncomputable section

open Finset MeasureTheory Matrix
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory.CompanionTheory.HsPsProof

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 PositivityTheory.RgFd

section General

variable {K V : Type*} [TopologicalSpace K] [T2Space K] [CompactSpace K] [SecondCountableTopology K]
  [MeasurableSpace K] [BorelSpace K] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V] [CompleteSpace V]

theorem hsOp_integral_rank_one (m : Measure K) [IsFiniteMeasure m] {u : K → V} (hu : Continuous u)
    {φ : K → ℝ} (hφ : Continuous φ) {P : K → V →L[ℂ] V} (hPc : Continuous P)
    (hP : ∀ k b, P k b = ⟪u k, b⟫_ℂ • u k) (d : ℝ) :
    hsOp ((d : ℂ) • ∫ k, ((φ k : ℝ) : ℂ) • P k ∂m) =
      d ^ 2 * ∫ p, φ p.1 * φ p.2 * ‖⟪u p.1, u p.2⟫_ℂ‖ ^ 2 ∂(m.prod m) := by
  have hφC : Continuous fun k => ((φ k : ℝ) : ℂ) := Complex.continuous_ofReal.comp hφ
  have hInt : Integrable (fun k => ((φ k : ℝ) : ℂ) • P k) m :=
    (integrableOn_univ).mp ((hφC.smul hPc).continuousOn.integrableOn_compact isCompact_univ)
  set A : V →L[ℂ] V := (d : ℂ) • ∫ k, ((φ k : ℝ) : ℂ) • P k ∂m with hA
  have hkey : ∀ y x : V, ⟪y, A x⟫_ℂ =
      (d : ℂ) * ∫ k, ((φ k : ℝ) : ℂ) * (⟪u k, x⟫_ℂ * ⟪y, u k⟫_ℂ) ∂m := by
    intro y x
    have hIx : Integrable (fun k => (((φ k : ℝ) : ℂ) • P k) x) m :=
      (ContinuousLinearMap.apply ℂ V x).integrable_comp hInt
    rw [hA, _root_.smul_apply, inner_smul_right, ContinuousLinearMap.integral_apply hInt,
      ← integral_inner hIx]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [_root_.smul_apply, inner_smul_right, hP]
  have hQ : ∀ v : V, ⟪v, A v⟫_ℂ = ((d * ∫ k, φ k * ‖⟪v, u k⟫_ℂ‖ ^ 2 ∂m : ℝ) : ℂ) := by
    intro v
    rw [hkey]
    have : ∀ k, ((φ k : ℝ) : ℂ) * (⟪u k, v⟫_ℂ * ⟪v, u k⟫_ℂ) =
        ((φ k * ‖⟪v, u k⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
      intro k
      rw [← inner_conj_symm (u k) v, Complex.conj_mul']
      push_cast; ring
    simp_rw [this]
    rw [integral_complex_ofReal]
    push_cast; ring
  have hQ' : ∀ v : V, ⟪A v, v⟫_ℂ = ((d * ∫ k, φ k * ‖⟪v, u k⟫_ℂ‖ ^ 2 ∂m : ℝ) : ℂ) := by
    intro v
    rw [← inner_conj_symm, hQ, Complex.conj_ofReal]
  set b := stdOrthonormalBasis ℂ V with hb
  have hsum : ∀ v : V, ∑ i, ⟪v, b i⟫_ℂ * ⟪A (b i), v⟫_ℂ = ⟪A v, v⟫_ℂ := by
    intro v
    simp_rw [← ContinuousLinearMap.adjoint_inner_right]
    rw [b.sum_inner_mul_inner]
  have hterm : ∀ i, ((‖A (b i)‖ ^ 2 : ℝ) : ℂ) =
      (d : ℂ) * ∫ k, ((φ k : ℝ) : ℂ) * (⟪u k, b i⟫_ℂ * ⟪A (b i), u k⟫_ℂ) ∂m := by
    intro i
    rw [← hkey, inner_self_eq_norm_sq_to_K]
    push_cast; rfl
  have hintg : ∀ i ∈ (Finset.univ : Finset _), Integrable
      (fun k => ((φ k : ℝ) : ℂ) * (⟪u k, b i⟫_ℂ * ⟪A (b i), u k⟫_ℂ)) m := by
    intro i _
    have hc : Continuous fun k => ((φ k : ℝ) : ℂ) * (⟪u k, b i⟫_ℂ * ⟪A (b i), u k⟫_ℂ) :=
      hφC.mul ((hu.inner continuous_const).mul (continuous_const.inner hu))
    exact (integrableOn_univ).mp (hc.continuousOn.integrableOn_compact isCompact_univ)
  have hC : ((hsOp A : ℝ) : ℂ) =
      ((d * ∫ k, φ k * (d * ∫ k', φ k' * ‖⟪u k, u k'⟫_ℂ‖ ^ 2 ∂m) ∂m : ℝ) : ℂ) := by
    calc ((hsOp A : ℝ) : ℂ) = ∑ i, ((‖A (b i)‖ ^ 2 : ℝ) : ℂ) := by
          simp only [hsOp, hb]; push_cast; rfl
      _ = ∑ i, (d : ℂ) * ∫ k, ((φ k : ℝ) : ℂ) * (⟪u k, b i⟫_ℂ * ⟪A (b i), u k⟫_ℂ) ∂m :=
          sum_congr rfl fun i _ => hterm i
      _ = (d : ℂ) * ∫ k, ∑ i, ((φ k : ℝ) : ℂ) * (⟪u k, b i⟫_ℂ * ⟪A (b i), u k⟫_ℂ) ∂m := by
          rw [← mul_sum, integral_finsetSum _ hintg]
      _ = (d : ℂ) * ∫ k, ((φ k * (d * ∫ k', φ k' * ‖⟪u k, u k'⟫_ℂ‖ ^ 2 ∂m) : ℝ) : ℂ) ∂m := by
          congr 1
          refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
          simp only []
          rw [← mul_sum, hsum, hQ']
          push_cast; rfl
      _ = ((d * ∫ k, φ k * (d * ∫ k', φ k' * ‖⟪u k, u k'⟫_ℂ‖ ^ 2 ∂m) ∂m : ℝ) : ℂ) := by
          rw [integral_complex_ofReal]
          push_cast; rfl
  have hR : hsOp A = d * ∫ k, φ k * (d * ∫ k', φ k' * ‖⟪u k, u k'⟫_ℂ‖ ^ 2 ∂m) ∂m := by
    exact_mod_cast hC
  have hF : Continuous fun p : K × K => φ p.1 * φ p.2 * ‖⟪u p.1, u p.2⟫_ℂ‖ ^ 2 :=
    ((hφ.comp continuous_fst).mul (hφ.comp continuous_snd)).mul
      (((hu.comp continuous_fst).inner (hu.comp continuous_snd)).norm.pow 2)
  have hFi : Integrable (fun p : K × K => φ p.1 * φ p.2 * ‖⟪u p.1, u p.2⟫_ℂ‖ ^ 2) (m.prod m) :=
    (integrableOn_univ).mp (hF.continuousOn.integrableOn_compact isCompact_univ)
  rw [hR, integral_prod _ hFi]
  have e1 : ∀ k, ∫ k', φ k * φ k' * ‖⟪u k, u k'⟫_ℂ‖ ^ 2 ∂m =
      φ k * ∫ k', φ k' * ‖⟪u k, u k'⟫_ℂ‖ ^ 2 ∂m := by
    intro k
    rw [← integral_const_mul]
    simp only [mul_assoc]
  have e2 : ∀ k, φ k * (d * ∫ k', φ k' * ‖⟪u k, u k'⟫_ℂ‖ ^ 2 ∂m) =
      d * (φ k * ∫ k', φ k' * ‖⟪u k, u k'⟫_ℂ‖ ^ 2 ∂m) := fun k => by ring
  simp_rw [e1, e2]
  rw [integral_const_mul]
  ring

end General

variable {n : ℕ} {ε : Fin n → Bool}

private lemma posDef_conj (k : KG ε) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    (toMK k⁻¹ * x * toMK k).PosDef := by
  rw [toMK_inv]
  refine hx.conjTranspose_mul_mul_same ?_
  intro a b hab
  have h := congrArg (fun y => (toMK k)ᴴ.mulVec y) hab
  simpa only [Matrix.mulVec_mulVec, (toMK_facts k).1, Matrix.one_mulVec] using h

private lemma cont_phiK (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    Continuous (phiK μ x : KG ε → ℝ) := by
  have hm : Continuous (fun k : KG ε => toMK k) :=
    (continuous_toM ε).comp continuous_subtype_val
  have hz : Continuous (fun k : KG ε => toMK k⁻¹ * x * toMK k) :=
    ((hm.comp continuous_inv).mul continuous_const).mul hm
  refine Complex.continuous_re.comp ?_
  exact (phiM_differentiableOn μ).continuousOn.comp_continuous hz
    (fun k => posSet_subset_omega (posDef_conj k hx))

private lemma cK_mul {Λ : Fin n → ℝ} (T : KType ε Λ) (a b : KG ε) :
    cK T (a⁻¹ * b) = ‖⟪T.op a T.w, T.op b T.w⟫_ℂ‖ := by
  rw [cK, CompactHaarProbability.op_mul, KType_op_inv_eq_adjoint, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.adjoint_inner_right]

theorem hsPs : HsPs := by
  intro n ε Λ T μ x hx
  have hφc : Continuous (phiK μ x : KG ε → ℝ) := cont_phiK μ hx
  have hφeq : ∀ k : KG ε, PhiM μ (toMK k⁻¹ * x * toMK k) = ((phiK μ x k : ℝ) : ℂ) := fun k =>
    Complex.ext (by simp [phiK]) (by simp [(phiM_posDef μ (posDef_conj k hx)).2])
  have hps : psM T μ x = ((Module.finrank ℂ T.V : ℝ) : ℂ) •
      ∫ k, ((phiK μ x k : ℝ) : ℂ) • (T.op k * projW T * T.op k⁻¹) ∂(dk ε) := by
    unfold psM
    delta dk
    simp_rw [hφeq]
    rw [integral_smul_measure, ENNReal.toReal_inv, ← Complex.coe_smul, smul_smul]
    congr 1
    push_cast
    ring
  have hu : Continuous fun k : KG ε => T.op k T.w :=
    (KType_continuous_op T).clm_apply continuous_const
  have hPc : Continuous fun k : KG ε => T.op k * projW T * T.op k⁻¹ :=
    ((KType_continuous_op T).mul continuous_const).mul ((KType_continuous_op T).comp continuous_inv)
  rw [hps, hsOp_integral_rank_one (dk ε) hu hφc hPc (conj_projection_apply T)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [hI, cK_mul]

end GlobalTheory.CompanionTheory.HsPsProof
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.CharTensor

theorem piTensor_detRep_apply {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} (ξ : Fin n → (kˣ →* ℂˣ)) (t : ∀ _ : Fin n, GL (Fin 1) k)
    (y : PiTensorProduct ℂ fun _ : Fin n => ℂ) :
    piTensor (fun a => detRep (Fin 1) (ξ a)) t y = PositivityTheory.Lbc.torusChar ξ t • y := by
  induction y using PiTensorProduct.induction_on with
  | add x y hx hy => rw [map_add (f := _), hx, hy, smul_add]
  | smul_tprod c x =>
    rw [map_smul, piTensor_tprod, PositivityTheory.Lbc.torusChar]
    simp [detRep]
    rw [smul_comm]
    have h := (PiTensorProduct.tprod ℂ).map_smul_univ
      (fun a => (↑(ξ a (Matrix.GeneralLinearGroup.det (t a))) : ℂ)) x
    simpa [smul_eq_mul] using congrArg (fun z => c • z) h

theorem tprod_one_ne_zero (n : ℕ) : PiTensorProduct.tprod ℂ (fun _ : Fin n => (1 : ℂ)) ≠ 0 := by
  intro h
  have h1 := congrArg (PiTensorProduct.constantBaseRingEquiv (Fin n) ℂ) h
  simp at h1

theorem exists_intertwiningMap_piTensor_ofChar {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) (ξ : Fin n → (kˣ →* ℂˣ)) (hξ : ∀ a, IsSmoothChar (ξ a))
    (hd : ∑ a, (IrrGL.ofChar (ξ a) (hξ a)).1 = n)
    (f : Jacquet π (unipRad k (stdBlocks (fun a => (IrrGL.ofChar (ξ a) (hξ a)).1) hd)) →ₗ[ℂ] ℂ) (hf : f ≠ 0)
    (hfe : ∀ t w, f (jac (stdBlocks (fun a => (IrrGL.ofChar (ξ a) (hξ a)).1) hd) π t w) =
      PositivityTheory.Lbc.torusChar ξ t * f w) :
    ∃ g : (jac (stdBlocks (fun a => (IrrGL.ofChar (ξ a) (hξ a)).1) hd) π).IntertwiningMap
        (piTensor fun a => (IrrGL.ofChar (ξ a) (hξ a)).rep), ∃ w, g w ≠ 0 := by
  let E : (piTensor fun a => detRep (Fin 1) (ξ a)).Equiv (piTensor fun a => (IrrGL.ofChar (ξ a) (hξ a)).rep) :=
    piTensorEquiv fun a => equivRep (IrrRep.det (Fin 1) (ξ a) (hξ a))
  let o : PiTensorProduct ℂ (fun _ : Fin n => ℂ) := PiTensorProduct.tprod ℂ fun _ => 1
  let g₀ : (jac (stdBlocks (fun a => (IrrGL.ofChar (ξ a) (hξ a)).1) hd) π).IntertwiningMap
      (piTensor fun a => detRep (Fin 1) (ξ a)) :=
    { toFun := fun w => f w • o
      map_add' := fun v w => by simp [add_smul]
      map_smul' := fun c w => by simp [mul_smul]
      isIntertwining' := fun t => LinearMap.ext fun w => by
        show f (jac _ π t w) • o = piTensor (fun a => detRep (Fin 1) (ξ a)) t (f w • o)
        rw [hfe]
        exact (mul_smul _ _ _).trans (piTensor_detRep_apply ξ t (f w • o)).symm }
  obtain ⟨w, hw⟩ : ∃ w, f w ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (LinearMap.ext h)
  refine ⟨E.toIntertwiningMap.comp g₀, w, fun h => ?_⟩
  have h1 : E.toLinearEquiv (f w • o) = 0 := h
  rw [LinearEquiv.map_eq_zero_iff] at h1
  exact (smul_ne_zero hw (tprod_one_ne_zero n)) h1

theorem chartotensor : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (ξ : Fin n → (kˣ →* ℂˣ)) (hξ : ∀ a, IsSmoothChar (ξ a)) (hd : ∑ a, (IrrGL.ofChar (ξ a) (hξ a)).1 = n) (f : Jacquet π (unipRad k (stdBlocks (fun a => (IrrGL.ofChar (ξ a) (hξ a)).1) hd)) →ₗ[ℂ] ℂ), f ≠ 0 → (∀ t w, f (jac (stdBlocks (fun a => (IrrGL.ofChar (ξ a) (hξ a)).1) hd) π t w) = PositivityTheory.Lbc.torusChar ξ t * f w) → ∃ g : (jac (stdBlocks (fun a => (IrrGL.ofChar (ξ a) (hξ a)).1) hd) π).IntertwiningMap (piTensor fun a => (IrrGL.ofChar (ξ a) (hξ a)).rep), ∃ w, g w ≠ 0 := by
  intro k _ _ _ _ n V _ _ π ξ hξ hd f hf hfe
  exact exists_intertwiningMap_piTensor_ofChar n π ξ hξ hd f hf hfe

end GlobalTheory.CompanionTheory.CharTensor

end
end

section

open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

theorem fe_of_parts (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (χ : HeckeCharacter F)
    (hD : χ.discrNormConductor = GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F)
    (hG : ∀ s : ℂ, χ.gammaFactor s = Complex.Gammaℝ s ^ Module.finrank ℚ F)
    (hG' : ∀ s : ℂ, (χ⁻¹).gammaFactor s = Complex.Gammaℝ s ^ Module.finrank ℚ F)
    (hR : χ.rootNumber = χ.coeff (differentIdeal ℤ (𝓞 F)))
    (s : ℂ) (h1 : ∀ n : ℕ, s ≠ -2 * n) (h2 : ∀ n : ℕ, 1 - s ≠ -2 * n) :
    (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ (s / 2) * Complex.Gammaℝ s ^ Module.finrank ℚ F * χ.continuedLFunction s =
      χ.coeff (differentIdeal ℤ (𝓞 F)) * ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ ((1 - s) / 2) *
        Complex.Gammaℝ (1 - s) ^ Module.finrank ℚ F * (χ⁻¹).continuedLFunction (1 - s)) := by
  have nz : ∀ t : ℂ, (∀ n : ℕ, t ≠ -2 * n) → Complex.Gammaℝ t ≠ 0 := by
    intro t ht h0
    obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.1 h0
    exact ht n (by rw [hn]; ring)
  have key := χ.continuedLFunction_functional_equation (s := s)
    (by rw [hG]; exact pow_ne_zero _ (nz s h1))
    (by rw [hG']; exact pow_ne_zero _ (nz _ h2))
  rw [hG, hG', hD, hR] at key
  exact key

end GlobalTheory.CompanionTheory.PartialZeta
end
