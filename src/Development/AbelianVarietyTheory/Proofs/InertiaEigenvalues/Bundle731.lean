module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle717
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle041
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle004
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohTop
public import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohTopEuler
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoExactAnnihilatorsPeriodDatum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle730
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle681
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle030
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle597
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle548
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle332
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle729
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesSubsetAdmissibleOfGoodO
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.T2SpaceLocLatV
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle486
public import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle020
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.BK

section Red

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K)

def evRed : bk.S →+* OCb l := (WittVector.constantCoeff (p := l) (R := OCb l)).comp bk.ev

theorem evRed_X : bk.evRed X = bk.flat := by
  simp [evRed, bk.ev_X, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]

theorem flat_ne_zero : bk.flat ≠ 0 := by
  intro h0
  have hX : bk.ev X = 0 := by rw [bk.ev_X, h0]; exact WittVector.teichmuller_zero l
  obtain ⟨w, hw⟩ := bk.coeff_zero
  have hE : bk.ev bk.E = (l : Ainf l) * wA l bk.a (w : Wq l bk.a) := by
    conv_lhs => rw [eq_X_mul_shift_add_const bk.E]
    rw [map_add (f := _), map_mul, hX, zero_mul, zero_add, bk.ev_C, Polynomial.constantCoeff_coe, hw, map_mul,
      map_natCast]
  have hl' : (l : Ainf l) ∈ RingHom.ker (Per.θ l) := by
    rw [← bk.span_ev, hE, Ideal.span_singleton_mul_right_unit ((w.isUnit).map (wA l bk.a))]
    exact Ideal.mem_span_singleton_self _
  rw [RingHom.mem_ker, map_natCast] at hl'
  exact Nat.cast_ne_zero.2 hl.out.ne_zero hl'

theorem dvd_of_evRed_eq_zero (x : bk.S) (hx : bk.evRed x = 0) : (l : bk.S) ∣ x := by
  set r := WittVector.constantCoeff (p := l) (R := Fq l bk.a) with hr
  by_cases h : PowerSeries.map r x = 0
  · exact dvd_of_map_eq_zero l bk.a x h
  exfalso
  set xb := PowerSeries.map r x with hxb
  set m := xb.order.toNat
  set vb := divXPowOrder xb
  have hvb : constantCoeff vb ≠ 0 := fun h' => h (constantCoeff_divXPowOrder_eq_zero_iff.1 h')
  let v : bk.S := PowerSeries.mk fun n => WittVector.teichmuller l (coeff n vb)
  have hv : PowerSeries.map r v = vb := by
    ext n
    simp [v, hr, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
  have hvu : IsUnit v := by
    rw [isUnit_iff_constantCoeff]
    have : constantCoeff v = WittVector.teichmuller l (constantCoeff vb) := by
      simp [v, ← coeff_zero_eq_constantCoeff]
    rw [this]
    exact (Ne.isUnit hvb).map _
  obtain ⟨y, hy⟩ := dvd_of_map_eq_zero l bk.a (x - X ^ m * v) (by
    rw [map_sub, map_mul, map_pow, PowerSeries.map_X, hv, X_pow_order_mul_divXPowOrder, sub_self])
  have h1 : bk.evRed x = bk.flat ^ m * bk.evRed v := by
    have : x = X ^ m * v + (l : bk.S) * y := by linear_combination hy
    rw [this, map_add (f := _), map_mul, map_mul, map_pow, evRed_X, map_natCast, CharP.cast_eq_zero, zero_mul, add_zero]
  rw [hx] at h1
  exact mul_ne_zero (pow_ne_zero _ bk.flat_ne_zero) (hvu.map bk.evRed).ne_zero h1.symm

theorem dvd_of_dvd_ev (x : bk.S) (h : (l : Ainf l) ∣ bk.ev x) : (l : bk.S) ∣ x := by
  apply bk.dvd_of_evRed_eq_zero
  obtain ⟨z, hz⟩ := h
  simp only [evRed, RingHom.comp_apply, hz, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

theorem eq_zero_of_forall_pow_dvd (w : Wq l bk.a) (h : ∀ n : ℕ, (l : Wq l bk.a) ^ n ∣ w) : w = 0 := by
  by_contra hw
  obtain ⟨m, b, hb0, hb⟩ := WittVector.exists_eq_pow_p_mul w hw
  obtain ⟨c, hc⟩ := h (m + 1)
  have hbc : b = (l : Wq l bk.a) * c := by
    apply mul_left_cancel₀ (pow_ne_zero m (WittVector.p_nonzero l (Fq l bk.a)))
    rw [← hb, hc]; ring
  apply hb0
  have := congrArg (WittVector.constantCoeff (p := l) (R := Fq l bk.a)) hbc
  rwa [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, WittVector.constantCoeff_apply] at this

theorem ev_injective : Function.Injective bk.ev := by
  apply GlobalTheory.BSP.BK.ev_injective_galPer <;> assumption

end Red

theorem evW_isUnit_injective_dvd : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K),
    IsUnit (bk.evW bk.E) ∧ Function.Injective bk.evW ∧
      ∀ x : bk.S, ((l : ℕ) : Ainf l) ∣ bk.ev x → ((l : ℕ) : bk.S) ∣ x :=
  fun _ _ _ bk => ⟨isUnit_inclW_of_span bk.span_ev, GlobalTheory.Prism.inclW_injective.comp bk.ev_injective,
    bk.dvd_of_dvd_ev⟩

end GlobalTheory.BSP.BK
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.CosetSum

open GlobalTheory.AutMult

theorem mem_realLevSet_iff {D : D7} {W : HSp D} {K : Subgroup (GA D W)} (hK : K ≤ GfC W) (h : GA D W) :
    (∃ u ∈ GinfC W, ∃ k ∈ K, h = u * k) ↔ toFin W h ∈ K.subgroupOf (GfC W) := by
  constructor
  · rintro ⟨u, hu, k, hk, rfl⟩
    have h1 : toFin W u = 1 := toFin_coe_inf (V := W) ⟨u, hu⟩
    have h2 : toFin W k = ⟨k, hK hk⟩ := toFin_coe (V := W) ⟨k, hK hk⟩
    rw [map_mul, h1, h2, one_mul, Subgroup.mem_subgroupOf]
    exact hk
  · intro h'
    exact ⟨toInf W h, (toInf W h).2, toFin W h, (Subgroup.mem_subgroupOf).1 h', (toInf_mul_toFin h).symm⟩

theorem integral_eq_sum_cosets : ∀ (D : D7) (W : HSp D) (ν : Measure (GA D W)) (K : Subgroup (GA D W)), ν.IsHaarMeasure → K ≤ GfC W → IsOpen {g : GfC W | (g : GA D W) ∈ K} → ∀ Φ : GA D W → ℂ, Integrable Φ ν → MeasurableSet {h : GA D W | ∃ u ∈ GinfC W, ∃ k ∈ K, h = u * k} ∧ HasSum (fun q : GfC W ⧸ K.subgroupOf (GfC W) => ∫ h in {h : GA D W | ∃ u ∈ GinfC W, ∃ k ∈ K, h = u * k}, Φ (((Quotient.out q : GfC W) : GA D W) * h) ∂ν) (∫ g, Φ g ∂ν) := by
  intro D W ν K hν hKf hKo Φ hΦ
  obtain ⟨i0, -, i2, -, i4, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D W
  haveI := i0; haveI := i2; haveI := i4
  set K' := K.subgroupOf (GfC W) with hK'
  set C : Set (GA D W) := {h : GA D W | ∃ u ∈ GinfC W, ∃ k ∈ K, h = u * k} with hCdef
  have hK'o : IsOpen (K' : Set (GfC W)) := hKo
  have hC : C = toFin W ⁻¹' (K' : Set (GfC W)) := Set.ext fun h => mem_realLevSet_iff hKf h
  have hCo : IsOpen C := hC ▸ hK'o.preimage (continuous_toFin W)
  have hCm : MeasurableSet C := hCo.measurableSet
  refine ⟨hCm, ?_⟩

  let s : GfC W ⧸ K' → Set (GA D W) := fun q => (fun g => ((Quotient.out q : GfC W) : GA D W)⁻¹ * g) ⁻¹' C
  have hmem : ∀ q g, g ∈ s q ↔ q = QuotientGroup.mk (toFin W g) := by
    intro q g
    show _ ∈ C ↔ _
    rw [hC, Set.mem_preimage, map_mul, map_inv, toFin_coe, SetLike.mem_coe]
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rw [QuotientGroup.eq]
  have hsm : ∀ q, MeasurableSet (s q) := fun q => (measurable_const_mul _) hCm
  have hd : Pairwise (Function.onFun Disjoint s) := by
    intro q q' hne
    exact Set.disjoint_left.2 fun g h1 h2 => hne (((hmem q g).1 h1).trans ((hmem q' g).1 h2).symm)
  have hU : (⋃ q, s q) = Set.univ := Set.eq_univ_of_forall fun g => Set.mem_iUnion.2 ⟨_, (hmem _ g).2 rfl⟩

  haveI : Countable (GfC W ⧸ K') := by
    have hpd : (Set.univ : Set (GfC W ⧸ K')).PairwiseDisjoint
        (fun q => (fun x => (Quotient.out q : GfC W)⁻¹ * x) ⁻¹' (K' : Set (GfC W))) := by
      intro q _ q' _ hne
      refine Set.disjoint_left.2 fun x h1 h2 => hne ?_
      have e1 : QuotientGroup.mk (Quotient.out q) = (QuotientGroup.mk x : GfC W ⧸ K') := QuotientGroup.eq.2 h1
      have e2 : QuotientGroup.mk (Quotient.out q') = (QuotientGroup.mk x : GfC W ⧸ K') := QuotientGroup.eq.2 h2
      rw [QuotientGroup.out_eq'] at e1 e2
      exact e1.trans e2.symm
    exact Set.countable_univ_iff.1 (hpd.countable_of_isOpen
      (fun q _ => hK'o.preimage (continuous_const.mul continuous_id))
      (fun q _ => ⟨Quotient.out q, by simp [K'.one_mem]⟩))
  have hsum := hasSum_integral_iUnion hsm hd (by rw [hU]; exact hΦ.integrableOn)
  rw [hU, Measure.restrict_univ] at hsum
  refine (funext fun q => ?_ : (fun q : GfC W ⧸ K' => ∫ h in C, Φ (((Quotient.out q : GfC W) : GA D W) * h) ∂ν) =
    fun q => ∫ x in s q, Φ x ∂ν) ▸ hsum
  have hpre : (fun h => ((Quotient.out q : GfC W) : GA D W) * h) ⁻¹' s q = C := by
    ext h; simp [s]
  rw [← hpre]
  exact ((measurePreserving_mul_left ν _).setIntegral_preimage_emb
    (measurableEmbedding_mulLeft _) Φ (s q))

end GlobalTheory.CosetSum

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module

namespace GlobalTheory.HyodoDef.Count

theorem finrank_blochKato_g_add_e_le_f_add_f_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [ContinuousAdd V'] [ContinuousConstSMul ℚ_[l] V'] (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), (∀ v, Continuous fun g => ρ g v) → (∀ y, Continuous fun g => ρ' g y) → IsDR (P.PD K) ρ → IsDR (P.PD K) ρ' → IsDual1 (P.PD K) ρ ρ' m → finrank ℚ_[l] ↥(geometricCocycles (P.PD K) ρ) + finrank ℚ_[l] ↥(crystallineCocycles (P.PD K) ρ') ≤ finrank ℚ_[l] ↥(finiteCocycles (P.PD K) ρ) + finrank ℚ_[l] ↥(finiteCocycles (P.PD K) ρ') := by
  intro l _ P AI hT K V _ _ _ _ _ _ _ ρ V' _ _ _ _ _ _ _ ρ' m hc hc' hdR hdR' hdual
  letI : Module ℤ_[l] V := Module.compHom V (algebraMap ℤ_[l] ℚ_[l])
  haveI : IsScalarTower ℤ_[l] ℚ_[l] V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : Module ℤ_[l] V' := Module.compHom V' (algebraMap ℤ_[l] ℚ_[l])
  haveI : IsScalarTower ℤ_[l] ℚ_[l] V' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hO := GlobalTheory.Published.BlochKato.goodO_padicInt (l := l)
  have hTD := CompanionTheory.LocalTateOrthogonality.Gcoh.top_tate
  have hEC := CompanionTheory.LocalTateOrthogonality.Gcoh.top_euler
  let A : GRep ↥(GK K) ℚ_[l] ℚ_[l] ℤ_[l] := { V := V, ρ := ρ, cont := hc }
  let A' : GRep ↥(GK K) ℚ_[l] ℚ_[l] ℤ_[l] := { V := V', ρ := ρ', cont := hc' }
  have hdual' : IsDual1 (P.PD K) ρ' ρ m.flip := by
    obtain ⟨h1, h2, h3, h4⟩ := hdual
    refine ⟨fun g y x => ?_, fun y hy => h3 y hy, fun x hx => h2 x hx, h4.symm⟩
    simp only [LinearMap.flip_apply]
    exact h1 g x y
  obtain ⟨hfin, -⟩ := GlobalTheory.T.finrank_H1_dual_pair hTD hEC l P K ℚ_[l] ℤ_[l] hO A A' m hdual
  obtain ⟨hfin', -⟩ := GlobalTheory.T.finrank_H1_dual_pair hTD hEC l P K ℚ_[l] ℤ_[l] hO A' A m.flip hdual'
  haveI : FiniteDimensional ℚ_[l] (continuousCocycles ρ) := GlobalTheory.BlochKatoAnn.finite_continuous_cocycles_localGaloisRep A hfin
  haveI : FiniteDimensional ℚ_[l] (continuousCocycles ρ') := GlobalTheory.BlochKatoAnn.finite_continuous_cocycles_localGaloisRep A' hfin'
  obtain ⟨β, hβ, -, hr⟩ : ∃ β : ↥(continuousCocycles ρ) →ₗ[ℚ_[l]] ↥(continuousCocycles ρ') →ₗ[ℚ_[l]] ℚ_[l],
      (∀ a b, β a b = 0 ↔ CobL (P.PD K) (cupL ρ' m a.1 b.1)) ∧
      (∀ a, (∀ b, β a b = 0) ↔ a.1 ∈ B1 ρ) ∧ ∀ b, (∀ a, β a b = 0) ↔ b.1 ∈ B1 ρ' :=
    GlobalTheory.T.tateDuality_degreeOne_continuous_cocycles hTD l P K ℚ_[l] ℤ_[l] hO A A' m hdual
  have hann : ∀ a ∈ continuousCocycles ρ, (a ∈ finiteCocycles (P.PD K) ρ ↔
      ∀ b ∈ finiteCocycles (P.PD K) ρ', CobL (P.PD K) (cupL ρ' m a b)) :=
    (GlobalTheory.T.blochKato_exact_annihilators_periodDatum hTD hEC l P AI hT K ℚ_[l] ℤ_[l] hO A A' m hdR hdual).1
  have horth := GlobalTheory.T.de_rham_cocycle_dimension_compare l P AI hT K V ρ V' ρ' m hc hc' hdR' hdual
  have hg : geometricCocycles (P.PD K) ρ ≤ continuousCocycles ρ := fun _ h => h.1
  have he : crystallineCocycles (P.PD K) ρ' ≤ continuousCocycles ρ' := fun _ h => h.1
  have hf : finiteCocycles (P.PD K) ρ ≤ continuousCocycles ρ := fun _ h => h.1
  have hf' : finiteCocycles (P.PD K) ρ' ≤ continuousCocycles ρ' := fun _ h => h.1
  have hBf : B1 ρ' ≤ finiteCocycles (P.PD K) ρ' := GlobalTheory.BlochKatoAnn.B1_le_Z1f (P.PD K) A'
  have hBe : B1 ρ' ≤ crystallineCocycles (P.PD K) ρ' := by
    intro c hcB
    refine ⟨hf' (hBf hcB), ?_⟩
    obtain ⟨x, rfl⟩ := hcB
    refine ⟨x ⊗ₜ[ℚ_[l]] 1, ?_, fun g => ?_⟩
    · simp [φVB]
    · simp [cob, actVB, sub_tmul]
  have key := GlobalTheory.HyodoDef.PairLin.finrank_add_le β
    ((geometricCocycles (P.PD K) ρ).comap (continuousCocycles ρ).subtype) ((finiteCocycles (P.PD K) ρ).comap (continuousCocycles ρ).subtype)
    ((crystallineCocycles (P.PD K) ρ').comap (continuousCocycles ρ').subtype) ((finiteCocycles (P.PD K) ρ').comap (continuousCocycles ρ').subtype)
    (fun b hb => ⟨hBe ((hr b).1 hb), hBf ((hr b).1 hb)⟩)
    (fun a ha b hb => (hβ a b).2 (horth a.1 ha b.1 hb))
    (fun a => by
      rw [Submodule.mem_comap, Submodule.subtype_apply, hann a.1 a.2]
      constructor
      · intro h b hb
        exact (hβ a b).2 (h b.1 hb)
      · intro h b hb
        exact (hβ a ⟨b, hf' hb⟩).1 (h ⟨b, hf' hb⟩ hb))
  rwa [(Submodule.comapSubtypeEquivOfLe hg).finrank_eq,
    (Submodule.comapSubtypeEquivOfLe he).finrank_eq,
    (Submodule.comapSubtypeEquivOfLe hf).finrank_eq,
    (Submodule.comapSubtypeEquivOfLe hf').finrank_eq] at key

end GlobalTheory.HyodoDef.Count
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.ExtClassKs

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem exists_ext [IsTopologicalRing LL] (hinj : Function.Injective (algebraMap O LL))
    (T Z : LocLat G Qp LL O) (htriv : ∀ g x, Z.ρ g x = x) (e₀ : ↥Z.L.T) (he₀ : (e₀ : Z.V) ≠ 0)
    (hone : Z.L.T = Submodule.span O {(e₀ : Z.V)}) (zc : ↥(latticeCocycles T.L)) :
    ∃ (Y : LocLat G Qp LL O) (ι : LatHom T.L Y.L) (π : LatHom Y.L Z.L) (et : ↥Y.L.T),
      IsSESLat (Qp := Qp) ι π ∧ π.f et = e₀ ∧ Module.finrank LL Y.V = Module.finrank LL T.V + 1 ∧
        ∀ g, ι.f ((zc : G → T.V) g) = Y.ρ g et - et := by
  let Yt : LocLat G Qp LL O := GlobalTheory.FiniteAdm.extLat hinj T zc
  let ι : LatHom T.L Yt.L :=
    { f := LinearMap.inl LL T.V LL
      equiv := fun g x => by
        change ((T.ρ g x, 0) : T.V × LL) = (T.ρ g x + (0 : LL) • (zc : G → T.V) g, 0)
        simp
      cont := by
        change Continuous fun x : T.V => ((x, 0) : T.V × LL)
        exact continuous_id.prodMk continuous_const
      T_le := fun x hx => ⟨hx, 0, map_zero _⟩ }
  haveI : ContinuousSMul LL Z.V := IsModuleTopology.toContinuousSMul LL Z.V
  let π : LatHom Yt.L Z.L :=
    { f := (LinearMap.toSpanSingleton LL Z.V (e₀ : Z.V)).comp (LinearMap.snd LL T.V LL)
      equiv := fun g x => by
        rw [htriv]
        rfl
      cont := by
        change Continuous fun x : T.V × LL => x.2 • (e₀ : Z.V)
        exact continuous_snd.smul continuous_const
      T_le := by
        rintro ⟨v, a⟩ ⟨-, o, rfl⟩
        change (algebraMap O LL o) • (e₀ : Z.V) ∈ Z.L.T
        rw [algebraMap_smul]
        exact Z.L.T.smul_mem o e₀.2 }
  refine ⟨Yt, ι, π, ⟨((0 : T.V), (1 : LL)), Submodule.zero_mem _, 1, map_one (algebraMap O LL)⟩,
    ⟨LinearMap.inl_injective, ?_, ?_, ?_, ?_⟩, one_smul LL (e₀ : Z.V), ?_, ?_⟩
  · intro w
    have hw : w ∈ Submodule.span LL {(e₀ : Z.V)} := by
      rw [← Submodule.span_span_of_tower O, ← hone, Z.L.span]; trivial
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
    exact ⟨((0 : T.V), a), rfl⟩
  · intro w hw
    rw [hone] at hw
    obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hw
    exact ⟨((0 : T.V), algebraMap O LL o), ⟨Submodule.zero_mem _, o, rfl⟩,
      algebraMap_smul LL o (e₀ : Z.V)⟩
  · rintro ⟨w, a⟩
    constructor
    · intro h0
      have ha : a = 0 := (smul_eq_zero.1 (show a • (e₀ : Z.V) = 0 from h0)).resolve_right he₀
      exact ⟨w, Prod.ext rfl ha.symm⟩
    · rintro ⟨y, hy⟩
      rw [← hy]
      exact zero_smul LL (e₀ : Z.V)
  · intro y hy
    exact hy.1
  · change Module.finrank LL (T.V × LL) = _
    rw [Module.finrank_prod, Module.finrank_self]
  · intro g
    change (((zc : G → T.V) g, 0) : T.V × LL) =
      ((T.ρ g 0 + (1 : LL) • (zc : G → T.V) g - 0, 1 - 1) : T.V × LL)
    simp

variable {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

theorem generic [T2Space LL] [IsTopologicalRing LL] (E : EtTie W RA RW inclR φR gR πA)
    (hinj : Function.Injective (algebraMap O LL)) (hR : Function.Injective (algebraMap O RW))
    (hdense : ∀ M : Submonoid ↥W.GKs, IsClosed (M : Set ↥W.GKs) →
      (∀ g : ↥W.GKs, W.resΓ (g : G) = 1 → g ∈ M) → (∀ g : ↥W.GKs, W.resΓ (g : G) = W.gam → g ∈ M) →
      ∀ g, g ∈ M)
    (T : LocLat G Qp LL O) (hGKs : W.GKs = ⊤) (M p : ℕ)
    (hBK : ∀ (Y : LocLat G Qp LL O) (ι : T.V →ₗ[LL] Y.V), (∀ g x, ι (T.ρ g x) = Y.ρ g (ι x)) →
      Function.Injective ι → Module.finrank LL Y.V = Module.finrank LL T.V + 1 →
      ∀ x : Y.V, x ∉ LinearMap.range ι → ∀ c : G → T.V, (∀ g, ι (c g) = Y.ρ g x - x) →
      (∃ y : T.V ⊗[Qp] B, ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD T.ρ g y - y) → IsCrys PD Y.ρ)
    (hlift : ∀ (Y : LocLat G Qp LL O) (ι : LatHom T.L Y.L) (π : LatHom Y.L W.one.L), IsCrys PD Y.ρ →
      IsSESLat (Qp := Qp) ι π →
      ∃ c : ℕ, ∀ z ∈ W.N W.one, ∃ y ∈ W.N Y, W.map π y = (p : LetA O n) ^ c • z)
    (hint : p8 W T M) (κ : LatticeCohomology (resLat T W.GKs)) (hκ : κ ∈ H1fIntegralCyclotomicLayer W T) :
    ∃ (c : ℕ) (y z : W.DD T) (hyz : (y, z) ∈ W.divisibleCocycles T), y ∈ invN W T (W.Q ^ M) ∧ z ∈ aN W T W.X ∧
      W.cl T ⟨(y, z), hyz⟩ = (p ^ c : ℕ) • κ := by
  obtain ⟨c₀, hc₀, rfl⟩ := hκ
  obtain ⟨xB, hxB⟩ : ∃ x : T.V ⊗[Qp] B, ∀ g : ↥W.GKs,
      (c₀ : ↥W.GKs → T.V) g ⊗ₜ[Qp] (1 : B) = actVB PD T.ρ (g : G) x - x := hc₀.2.2
  have hmem : ∀ g, g ∈ W.GKs := fun g => by rw [hGKs]; exact Subgroup.mem_top g
  have hz1 : (fun g => (c₀ : ↥W.GKs → T.V) ⟨g, hmem g⟩) ∈ latticeCocycles T.L :=
    ⟨⟨c₀.2.1.1.comp (Continuous.subtype_mk continuous_id hmem),
      fun g g' => c₀.2.1.2 ⟨g, hmem g⟩ ⟨g', hmem g'⟩⟩, fun g _ => c₀.2.2 ⟨g, hmem g⟩ (Set.mem_univ _)⟩
  obtain ⟨e, e₀, hspan, hje, hN⟩ := E.one_e
  have hone : W.one.L.T = Submodule.span O {(e₀ : W.one.V)} := by
    have h1 := congrArg (Submodule.map W.one.L.T.subtype) hspan
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, Set.image_singleton] at h1
    exact h1.symm
  have he₀ : (e₀ : W.one.V) ≠ 0 := by
    intro h0
    obtain ⟨e', he', hsp⟩ := W.one_line
    have : e' ∈ W.one.L.T := by rw [hsp]; exact Submodule.mem_span_singleton_self e'
    rw [hone, h0, Submodule.span_singleton_eq_bot.2 rfl] at this
    exact he' ((Submodule.mem_bot _).1 this)
  have hφe : W.φD W.one e = e := by
    apply E.jD_inj
    rw [E.jD_φ, hje]
    simp [TWmap]
  have hγe : ∀ g, W.γD W.one g e = e := by
    intro g
    obtain ⟨g, rfl⟩ := W.resΓ_onto g
    apply E.jD_inj
    have h1 : W.one.actT g e₀ = e₀ := Subtype.ext (W.one_triv g _)
    rw [E.jD_act, hje]
    simp [TWact, h1]
  have heN : e ∈ W.N W.one := by rw [hN]; exact Submodule.mem_span_singleton_self e
  obtain ⟨Y, ι, π, et, hS, hπ, hrk, hc⟩ := exists_ext hinj T W.one W.one_triv e₀ he₀ hone ⟨_, hz1⟩
  have hY : IsCrys PD Y.ρ := hBK Y ι.f ι.equiv hS.1 hrk et
    (fun hx => he₀ (by rw [← hπ]; exact (hS.2.2.2.1 _).2 hx)) _ hc ⟨xB, fun g => hxB ⟨g, hmem g⟩⟩
  obtain ⟨k, hk⟩ := hlift Y ι π hY hS
  obtain ⟨x, hxN, hxπ⟩ := hk e heN
  have hxπ' : W.map π x = ((p : O) ^ k) • e := by
    rw [hxπ, ← algebraMap_smul (LetA O n) ((p : O) ^ k) e, map_pow, map_natCast]
  obtain ⟨⟨y, hy, hyι⟩, ⟨z, hz, hzι⟩⟩ := hint Y ι π hS hY e heN hφe hγe x hxN _ hxπ'
  have hιinj : Function.Injective (W.map ι) := by
    intro a b hab
    apply E.jD_inj T
    apply GlobalTheory.Cyc.DictKs.lTensor_inj hS RW
    have h1 := congrArg (E.jD Y) hab
    rw [E.jD_map, E.jD_map] at h1
    exact h1
  have key : W.map ι ((W.γD T W.gam y - y) - (W.φD T z - z)) = W.map ι 0 := by
    rw [map_zero, map_sub, map_sub, map_sub, W.map_γ, W.map_φ, hyι, hzι, LocWach.γ, map_sub, map_sub,
      W.φγ_comm]
    abel
  have hyz : (y, z) ∈ W.divisibleCocycles T := by
    have h0 := hιinj key
    rw [sub_eq_add_neg] at h0
    exact h0
  refine ⟨k, y, z, hyz, hy, hz, ?_⟩
  refine (GlobalTheory.Cyc.DictKs.generic E hR hdense T Y W.one ι π hS (((p : O) ^ k) • et) (((p : O) ^ k) • e₀) x
    (by
      rw [Submodule.coe_smul, Submodule.coe_smul, ← hπ, ← algebraMap_smul LL ((p : O) ^ k) (et : Y.V),
        map_smul, algebraMap_smul])
    (by rw [hxπ', map_smul, hje, TensorProduct.tmul_smul]) ⟨(y, z), hyz⟩ hyι hzι (((p : O) ^ k) • c₀)
    (fun g => by
      have h1 := hc g
      change ι.f ((c₀ : ↥W.GKs → T.V) g) = _ at h1
      change ι.f (((p : O) ^ k) • (c₀ : ↥W.GKs → T.V) g) = _
      rw [Submodule.coe_smul, ← algebraMap_smul LL ((p : O) ^ k) (et : Y.V),
        ← algebraMap_smul LL ((p : O) ^ k) ((c₀ : ↥W.GKs → T.V) g), map_smul, map_smul, h1, smul_sub])).trans ?_
  rw [Submodule.Quotient.mk_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  rfl

end Generic



theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → W.GKs = ⊤ → ∀ (M hh : Let K → ℕ), JumpsLet W T M hh → ∀ κ ∈ H1fIntegralCyclotomicLayer W T, ∃ (c : ℕ) (y z : W.DD T) (hyz : (y, z) ∈ W.divisibleCocycles T), y ∈ invN W T (W.Q ^ mx M) ∧ z ∈ aN W T W.X ∧ W.cl T ⟨(y, z), hyz⟩ = (l ^ c : ℕ) • κ := by
  intro D HW F Cm l _ K s LL h W E C T hT hGKs M hh hJ κ hκ
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  refine generic E (fun a b hab => Subtype.ext hab) (GlobalTheory.Cyc.DictKs.algebraMap_RW_inj LL)
    (GlobalTheory.Cyc.DictKs.dense_gen (D.loc l) (D.locA l) K s LL h _ ((HW l).W_s K s LL h)) T hGKs (mx M) l
    ?_ ?_ (GlobalTheory.T.p8_of_cmpOf D HW F Cm l K s LL h T M hh hT hJ) κ hκ
  · intro Y ι h1 h2 h3 x h4 c h5
    exact (GlobalTheory.CrysExtCrit.coboundary_iff_isCrys l (D.loc l) (D.locA l) (D.locT l) K LL T.V T.ρ Y.V Y.ρ ι
      h1 h2 h3 hT x h4 c h5).1
  · intro Y ι π hY hS
    exact (GlobalTheory.T.wachN_cokernel_killed_by_power D HW F Cm l K s LL h T Y _ ι π hT hY (Formalism.MainNotions.LiftingTheory.gen_one_crys _) hS).imp
      fun c hc z hz => (hc z hz).1

end GlobalTheory.NL.ExtClassKs
end
end
