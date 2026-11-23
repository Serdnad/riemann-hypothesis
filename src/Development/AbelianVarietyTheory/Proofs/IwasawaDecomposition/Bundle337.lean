module

public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.BesselDatum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle330
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle320
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle333
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle008
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle047
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle325
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle306
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemberDatumOfFlagTie
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle193

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.BesselCoeffIndep

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G)
    [Countable Γ]

theorem haar_eq_of_covolume_one (μ μ' : Measure G) [μ.IsHaarMeasure] [μ'.IsHaarMeasure] {𝓕 𝓕' : Set G}
    (h : IsFundamentalDomain Γ 𝓕 μ) (h' : IsFundamentalDomain Γ 𝓕' μ') (h1 : μ 𝓕 = 1) (h1' : μ' 𝓕' = 1) :
    μ' = μ := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Γ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Γ μ'
  have e : μ' = (μ'.haarScalarFactor μ : ℝ≥0∞) • μ := Measure.isMulLeftInvariant_eq_smul μ' μ
  have h2 : IsFundamentalDomain Γ 𝓕 μ' := h.mono (by rw [e]; exact Measure.smul_absolutelyContinuous)
  have h3 : μ' 𝓕 = 1 := (h2.measure_eq h').trans h1'
  rw [e, Measure.smul_apply, h1, smul_eq_mul, mul_one] at h3
  rw [e, h3, one_smul]

theorem setIntegral_mul_right (μ : Measure G) [μ.IsHaarMeasure] {𝓕 : Set G} (h : IsFundamentalDomain Γ 𝓕 μ)
    (hfin : μ 𝓕 ≠ ⊤) (f : G → ℂ) (hf : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) (g : G) :
    ∫ x in 𝓕, f (x * g) ∂μ = ∫ x in 𝓕, f x ∂μ := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Γ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Γ μ
  have e : μ.map (· * g) = ((μ.map (· * g)).haarScalarFactor μ : ℝ≥0∞) • μ :=
    Measure.isMulLeftInvariant_eq_smul _ μ
  have h' : IsFundamentalDomain Γ ((· * g) ⁻¹' 𝓕) μ :=
    h.preimage_of_equiv (f := (· * g)) ⟨(measurable_mul_const g).aemeasurable, by rw [e]; exact Measure.smul_absolutelyContinuous⟩
      Function.bijective_id fun γ x => mul_assoc _ _ _
  have h1 : μ.map (· * g) 𝓕 = μ 𝓕 :=
    ((MeasurableEquiv.mulRight g).map_apply 𝓕).trans (h'.measure_eq h)
  rw [e, Measure.smul_apply, smul_eq_mul] at h1
  have h2 := (ENNReal.mul_left_inj (h.measure_ne_zero (NeZero.ne μ)) hfin).1 (h1.trans (one_mul _).symm)
  rw [h2, one_smul] at e
  have hp : MeasurePreserving (· * g) μ μ := ⟨measurable_mul_const g, e⟩
  rw [← hp.setIntegral_preimage_emb (MeasurableEquiv.mulRight g).measurableEmbedding f 𝓕]
  exact h.setIntegral_eq h' (f := fun x => f (x * g)) fun γ x => by
    show f ((γ : G) * x * g) = _
    rw [mul_assoc, hf _ γ.2]

end General

section Character

open GlobalTheory.BesselCompare (hA_add hA_smul hA_sum hA_vec hA_coeff hD_swap_zero co co_surj)

variable {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

theorem hA_act_e (d : BesselDatum A B ι) {n : GA D B} (hn : n ∈ d.NSet) {l i : Fin d.ρ} (h : l ≤ i) :
    hA B (actV B n (d.e l)) (vecA B (d.f i)) = if l = i then 1 else 0 := by
  obtain ⟨c, hc, e⟩ := hn.1 l
  rw [e, hA_add, hA_coeff B d.e d.f d.ef, hc i h, add_zero, hA_vec, d.ef]
  split_ifs
  · exact map_one _
  · exact map_zero _

theorem actE_eq_of_conj_related (d : BesselDatum A B ι) {n : GA D B} (hn : n ∈ d.NSet) (i : Fin d.ρ) :
    B.hD (d.aux i.succ) (d.f i) = 0 ∧ ∃ c : Fin d.ρ → AE D, (∀ l, i < l → c l = 0) ∧
      actV B n (d.aux i.succ) = vecA B (d.aux i.succ) + ∑ l, c l • vecA B (d.e l) := by
  unfold BesselDatum.aux
  by_cases hi : i.1 + 1 = d.ρ
  · have : i.succ = Fin.last d.ρ := Fin.ext hi
    rw [this, Fin.snoc_last]
    obtain ⟨c, e⟩ := hn.2 d.z fun j => hD_swap_zero (d.ez j)
    exact ⟨hD_swap_zero (d.fz i), c, fun l hl => absurd (show i.1 < l.1 from hl) (by have := l.2; omega), e⟩
  · have hlt : i.1 + 1 < d.ρ := by have := i.2; omega
    have : i.succ = Fin.castSucc (⟨i.1 + 1, hlt⟩ : Fin d.ρ) := Fin.ext rfl
    rw [this, Fin.snoc_castSucc]
    obtain ⟨c, hc, e⟩ := hn.1 ⟨i.1 + 1, hlt⟩
    refine ⟨?_, c, fun l hl => hc l (show i.1 + 1 ≤ l.1 from hl), e⟩
    rw [d.ef, if_neg (fun h => by have : i.1 + 1 = i.1 := congrArg Fin.val h; omega)]

theorem simpleSum_mul (d : BesselDatum A B ι) {n n' : GA D B} (hn : n ∈ d.NSet) (hn' : n' ∈ d.NSet) :
    d.simpleSum (n * n') = d.simpleSum n + d.simpleSum n' := by
  unfold BesselDatum.simpleSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨h0, c, hc, e⟩ := actE_eq_of_conj_related d hn' i
  have e1 : actV B (n * n') (d.aux i.succ) = actV B n (d.aux i.succ) + ∑ l, c l • actV B n (d.e l) := by
    have : actV B (n * n') (d.aux i.succ) = (mt B n).mulVec (actV B n' (d.aux i.succ)) := mulVec_mul _ _ _
    rw [this, e, Matrix.mulVec_add, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul]
    rfl
  rw [e1, e, hA_add, hA_add, hA_coeff B d.e d.f d.ef, hA_vec, h0, RingHom.map_zero, zero_add, hA_sum,
    Finset.sum_eq_single i]
  · rw [hA_smul, hA_act_e d hn le_rfl, if_pos rfl, mul_one]
  · intro l _ hl
    rw [hA_smul]
    rcases lt_or_ge i l with h | h
    · rw [hc l h, zero_mul]
    · rw [hA_act_e d hn h, if_neg hl, mul_zero]
  · exact fun h => absurd (Finset.mem_univ _) h

theorem psiN_mul (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ) {n n' : GA D B} (hn : n ∈ d.NSet)
    (hn' : n' ∈ d.NSet) : d.psiN ψ (n * n') = d.psiN ψ n * d.psiN ψ n' := by
  unfold BesselDatum.psiN
  rw [simpleSum_mul d hn hn', mul_add, LinearMap.map_add (f := _), AddChar.map_add_eq_mul]

theorem psiN_rat (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) {n : GA D B}
    (hn : n ∈ GQ B) : d.psiN ψ n = 1 := by
  obtain ⟨g, -, hg⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hn)
  have h1 : mt B n = (g : Matrix _ _ D.host.E).map (incA D) := (congrArg Units.val hg).symm
  have h2 : ∀ v, ∃ w, actV B n v = vecA B w := fun v => by
    obtain ⟨w, hw⟩ := co_surj B ((g : Matrix _ _ D.host.E).mulVec (co B v))
    refine ⟨w, funext fun k => ?_⟩
    have : vecA B w k = incA D (co B w k) := rfl
    rw [this, hw, RingHom.map_mulVec, actV, h1]
    rfl
  choose w hw using h2
  have h3 : ∀ e : D.host.E, Algebra.trace (AF D.host.F) (AE D) (incA D e) =
      algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E e) := fun e => by
    show Algebra.trace (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) (1 ⊗ₜ e) = _
    rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]
  unfold BesselDatum.psiN BesselDatum.simpleSum
  simp only [hw, hA_vec]

  rw [← map_sum (incA D), ← RingHom.map_mul, h3, hψ.2.2.1]

end Character

theorem coeff_indep_and_equivariant : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ F : GA D B → ℂ, (∀ γ ∈ GQ B, ∀ g, F (γ * g) = F g) → ∀ ν 𝓝, d.IsUnitPair ν 𝓝 → (∀ ν' 𝓝', d.IsUnitPair ν' 𝓝' → d.coeff ψ ν' 𝓝' F = d.coeff ψ ν 𝓝 F) ∧ ∀ n ∈ d.N, ∀ g, d.coeff ψ ν 𝓝 F (n * g) = d.psiN ψ n * d.coeff ψ ν 𝓝 F g := by
  intro D A B ι d ψ hψ F hF ν 𝓝 ⟨hν, h𝓝, h1⟩
  obtain ⟨i1, i2, i3, i4, i5, -, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  have hcl := (GlobalTheory.BesselClosed.N_eq_and_isClosed D A B ι d).2
  have : LocallyCompactSpace d.N := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology d.N := TopologicalSpace.Subtype.secondCountableTopology _
  have : BorelSpace d.N := Subtype.borelSpace _
  have : Countable d.NQ :=
    Function.Injective.countable (f := fun γ : d.NQ => (⟨γ.1.1, γ.2⟩ : GQ B)) fun a b hab =>
      Subtype.ext (Subtype.ext (congrArg (fun t : GQ B => (t : GA D B)) hab))
  have hS : ∀ n ∈ d.N, n ∈ d.NSet := fun n hn => (GlobalTheory.BesselClosed.N_eq_and_isClosed D A B ι d).1 ▸ SetLike.mem_coe.2 hn
  have hmul : ∀ n ∈ d.N, ∀ n' ∈ d.N, d.psiN ψ (n * n') = d.psiN ψ n * d.psiN ψ n' := fun n hn n' hn' =>
    psiN_mul d ψ (hS n hn) (hS n' hn')
  have hrat : ∀ n ∈ d.N, n ∈ GQ B → d.psiN ψ n = 1 := fun n _ hn' => psiN_rat d ψ hψ.1 hn'
  have hinv : ∀ g, ∀ γ ∈ d.NQ, ∀ x : d.N,
      F (((γ * x : d.N) : GA D B) * g) * star (d.psiN ψ ((γ * x : d.N) : GA D B)) =
        F ((x : GA D B) * g) * star (d.psiN ψ (x : GA D B)) := fun g γ hγ x => by
    rw [Subgroup.coe_mul, mul_assoc, hF (γ : GA D B) hγ, hmul _ γ.2 _ x.2, hrat _ γ.2 hγ, one_mul]
  refine ⟨fun ν' 𝓝' ⟨hν', h𝓝', h1'⟩ => ?_, fun n hn g => ?_⟩
  · obtain rfl := haar_eq_of_covolume_one d.NQ ν ν' h𝓝 h𝓝' h1 h1'
    have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup d.NQ
    have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup d.NQ ν'
    funext g
    exact h𝓝'.setIntegral_eq h𝓝 (f := fun x : d.N => F ((x : GA D B) * g) * star (d.psiN ψ (x : GA D B)))
      fun γ x => hinv g γ γ.2 x
  · have key := setIntegral_mul_right d.NQ ν h𝓝 (by rw [h1]; exact ENNReal.one_ne_top)
      (fun x : d.N => F ((x : GA D B) * g) * star (d.psiN ψ (x : GA D B))) (hinv g) ⟨n, hn⟩
    unfold BesselDatum.coeff
    rw [← key, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have hu : d.psiN ψ n * star (d.psiN ψ n) = 1 := by
      have : ‖d.psiN ψ n‖ = 1 := hψ.1.2.1 _
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, this]; simp
    simp only [Subgroup.coe_mul]
    rw [hmul _ x.2 _ hn, star_mul', mul_assoc (x : GA D B)]
    linear_combination (-(F (x * (n * g)) * star (d.psiN ψ x))) * hu

end GlobalTheory.Mem.BesselCoeffIndep
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SymFrame

theorem invMat_quot {Q ι : Type} [AddCommGroup Q] [Fintype ι] [DecidableEq ι] {g : ℕ} [NeZero g] [Fact (1 < g)]
    (T S : Q →+ Q) (hST : ∀ q, S (T q) = q) (β : ι → Q) (hβ : ∀ i, g • β i = 0)
    (N N' : Matrix ι ι (ZMod g)) (hNN' : N * N' = 1)
    (hT : ∀ i, T (β i) = ∑ j, (N j i).val • β j) (m : ι) :
    S (β m) = ∑ i, (N' i m).val • β i := by
  have e1 : T (∑ i, (N' i m).val • β i) = ∑ l, ((N * N') l m).val • β l := by

    rw [map_sum]
    simp only [map_nsmul, hT, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.mul_apply, val_mul_nsmul _ (hβ l)]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  have e2 : ∑ l, (((1 : Matrix ι ι (ZMod g))) l m).val • β l = β m := by
    rw [Finset.sum_eq_single m]
    · rw [Matrix.one_apply_eq, ZMod.val_one, one_smul]
    · intro l _ hl
      rw [Matrix.one_apply_ne hl, ZMod.val_zero, zero_smul]
    · intro h; exact absurd (Finset.mem_univ m) h
  rw [hNN', e2] at e1
  rw [← e1, hST]

end GlobalTheory.Mem.SymFrame

namespace GlobalTheory.Mem.SymFrame

theorem isMatIn_inv : ∀ (D : D7) (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ∀ (u : Fin D.R.r → VA X.B.I), (∀ i, u i ∈ X.B.I.Lf) → ∀ k ∈ X.B.I.Kset, ∀ N : GL (Fin D.R.r) (ZMod (D.host.g kv.1)), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) u k (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) → GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) u k⁻¹ ((N⁻¹ : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) := by
  intro D X kv hg u hu k hk N hN m
  haveI : NeZero (D.host.g kv.1) := ⟨(D.host.g_prime kv.1).ne_zero⟩
  haveI : Fact (1 < D.host.g kv.1) := ⟨(D.host.g_prime kv.1).one_lt⟩
  let W := (wLf X (D.naut.plGw kv.1 kv.2)).toAddSubgroup
  have hk' : k⁻¹ ∈ X.B.I.Kset := Formalism.L2.SG.Pf.unitaryCongruence.K_inv X.B.I hk
  let fT := (Matrix.mulVecLin (X.B.I.fmat k)).toAddMonoidHom
  let fS := (Matrix.mulVecLin (X.B.I.fmat k⁻¹)).toAddMonoidHom
  let T := QuotientAddGroup.map W W fT (fun v hv => fmat_mulVec_mem_wLf X _ hk hv)
  let S := QuotientAddGroup.map W W fS (fun v hv => fmat_mulVec_mem_wLf X _ hk' hv)
  have key : ∀ a b : VA X.B.I, a - b ∈ wLf X (D.naut.plGw kv.1 kv.2) ↔ QuotientAddGroup.mk' W a = QuotientAddGroup.mk' W b := fun a b => by
    show a - b ∈ W ↔ _
    rw [← sub_eq_zero, ← map_sub, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  have hST : ∀ q, S (T q) = q := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H v =>
      show QuotientAddGroup.mk' W (X.B.I.fmat k⁻¹ *ᵥ (X.B.I.fmat k *ᵥ v)) = QuotientAddGroup.mk' W v
      rw [Matrix.mulVec_mulVec, Formalism.L2.SG.Pf.unitaryCongruence.fmat_inv_mul X.B.I k, Matrix.one_mulVec]
  have hβ : ∀ i, D.host.g kv.1 • QuotientAddGroup.mk' W (u i) = 0 := fun i => by
    rw [← map_nsmul, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    have h1 := inclE_smul_mem_wLf X (D.naut.plGw kv.1 kv.2) ((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.E)
      ⟨_, hg, by simp⟩ (y := u i) (hu i)
    have e : Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.E) : X.B.I.E) =
        ((D.host.g kv.1 : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) := by
      simp [map_natCast]
    rw [e, Nat.cast_smul_eq_nsmul] at h1
    exact h1
  have hT : ∀ i, T (QuotientAddGroup.mk' W (u i)) =
      ∑ j, ((N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) j i).val • QuotientAddGroup.mk' W (u j) := by
    intro i
    have := (key _ _).1 (by simpa only [Nat.cast_smul_eq_nsmul] using hN i)

    rw [map_sum] at this
    simp only [map_nsmul] at this
    rw [← this]; rfl
  have h := invMat_quot T S hST (fun i => QuotientAddGroup.mk' W (u i)) hβ
    (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))
    ((N⁻¹ : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))
    (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]) hT m
  simp only [Nat.cast_smul_eq_nsmul]

  rw [key, map_sum]
  simp only [map_nsmul]
  rw [← h]; rfl

end GlobalTheory.Mem.SymFrame
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaLiftInfinityTypes_atRealPlace : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → ∀ (i : Fin D.R.m) (t : T) (τ : D.what₂.Tau), GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.InfTypesAt L i t τ := by
  first | exact @GlobalTheory.PairInfTypes.infTypesAt | exact GlobalTheory.PairInfTypes.infTypesAt | (intros; apply GlobalTheory.PairInfTypes.infTypesAt <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU.LocAdm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem continuous_finGL : Continuous (finGL E n) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sFin E : Af E → Ad E) :=
    (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))
  exact (continuous_const.add (continuous_id.matrix_map hs) :
    Continuous fun x : Matrix (Fin n) (Fin n) (Af E) => 1 - matN n (sFin E) 1 + x.map (sFin E))

theorem t2Space_finiteAdeleRing_cmField : T2Space (FiniteAdeleRing (𝓞 E) E) :=
  inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
    (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) Filter.cofinite))

theorem t2Space_adeleRing_cmField : T2Space (Ad E) :=
  haveI := t2Space_finiteAdeleRing_cmField (E := E)
  haveI : T2Space (InfiniteAdeleRing E) := inferInstanceAs (T2Space ((v : InfinitePlace E) → v.Completion))
  inferInstanceAs (T2Space (InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E))

theorem t2Space_adelicGL_cmField : T2Space (GA E n) :=
  haveI := t2Space_adeleRing_cmField (E := E)
  Units.isEmbedding_embedProduct.t2Space

theorem isClosed_UA : IsClosed ((UA E n : Subgroup (GA E n)) : Set (GA E n)) := by
  haveI := t2Space_adeleRing_cmField (E := E)
  show IsClosed {g : GA E n | ((g : Matrix (Fin n) (Fin n) (Ad E)).map (conjAd E))ᵀ * 1 * (g : Matrix (Fin n) (Fin n) (Ad E)) = 1}
  exact isClosed_eq (((Units.continuous_val.matrix_map GlobalTheory.ThetaPull.continuous_conjAd).matrix_transpose.matrix_mul
    continuous_const).matrix_mul Units.continuous_val) continuous_const

theorem locU_le_finU (w : HeightOneSpectrum (𝓞 E)) : locU n w ≤ finU (E := E) (n := n) := inf_le_left

theorem continuous_inclusion_locU (w : HeightOneSpectrum (𝓞 E)) :
    Continuous (Subgroup.inclusion (locU_le_finU (n := n) w)) :=
  Continuous.subtype_mk continuous_subtype_val _

theorem isClosed_of_retract (w : HeightOneSpectrum (𝓞 E)) (r : UA E n →* locU n w) (hr : Continuous r)
    (hx : ∀ x : locU n w, r x = x) : IsClosed ((locU n w : Subgroup (UA E n)) : Set (UA E n)) := by
  haveI := t2Space_adelicGL_cmField (E := E) (n := n)
  have e : ((locU n w : Subgroup (UA E n)) : Set (UA E n)) = {x | ((r x : locU n w) : UA E n) = x} := by
    ext x
    constructor
    · intro h
      exact congrArg Subtype.val (hx ⟨x, h⟩)
    · intro h
      change x ∈ locU n w
      rw [← show ((r x : locU n w) : UA E n) = x from h]
      exact (r x).2

  rw [e]
  exact isClosed_eq (continuous_subtype_val.comp hr) continuous_id

theorem isSmooth_loc (π : AutSub E n) (w : HeightOneSpectrum (𝓞 E)) :
    IsSmooth (π.rep.comp (locU n w).subtype) := fun v => by
  have h := (π.isAut.aut v.1 v.2).level
  convert h.preimage (continuous_inclusion_locU (n := n) w) using 1
  ext k
  exact Subtype.ext_iff

theorem exists_compact_open (w : HeightOneSpectrum (𝓞 E)) (r : UA E n →* locU n w) (hr : Continuous r)
    (hx : ∀ x : locU n w, r x = x) (L : Subgroup (finU (E := E) (n := n))) (hL : IsOpen (L : Set (finU (E := E) (n := n)))) :
    ∃ K : Subgroup (locU n w), IsOpen (K : Set (locU n w)) ∧ IsCompact (K : Set (locU n w)) ∧
      K ≤ L.comap (Subgroup.inclusion (locU_le_finU w)) := by
  obtain ⟨U0, hU0o, hU0c⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact E n
  let p : locU n w →* GL (Fin n) (Af E) :=
    (GeneralLinearGroup.map (pFin E)).comp ((UA E n).subtype.comp (locU n w).subtype)
  have hp : Continuous p := continuous_map_pFin.comp (continuous_subtype_val.comp continuous_subtype_val)
  let K : Subgroup (locU n w) := U0.comap p ⊓ L.comap (Subgroup.inclusion (locU_le_finU w))
  have hKo : IsOpen (K : Set (locU n w)) :=
    (hU0o.preimage hp).inter (hL.preimage (continuous_inclusion_locU w))
  have hι : Topology.IsClosedEmbedding (fun x : locU n w => ((x : UA E n) : GA E n)) :=
    isClosed_UA.isClosedEmbedding_subtypeVal.comp (isClosed_of_retract w r hr hx).isClosedEmbedding_subtypeVal
  refine ⟨K, hKo, IsCompact.of_isClosed_subset (hι.isCompact_preimage (hU0c.image continuous_finGL))
    (Subgroup.isClosed_of_isOpen K hKo) fun x hx => ⟨p x, (Subgroup.mem_inf.1 hx).1, ?_⟩, inf_le_right⟩
  have h1 : GeneralLinearGroup.map (pInf E) ((x : UA E n) : GA E n) = 1 := (Subgroup.mem_inf.1 x.2).1
  exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL]; rfl)

theorem exists_admissible_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n)
    (w : HeightOneSpectrum (𝓞 E)), ∃ σ : SmIrr (locU n w), IsAdmissible σ.ρ ∧
      IsCompAlong π.V (locU n w) (MonoidHom.id _) σ.ρ := by
  intro E _ _ _ n π w
  obtain ⟨r, hr, hrx, hrc⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints E n w
  have hadm := (GlobalTheory.T.definiteUnitary_admissible_finiteMultiplicity E n π).1
  let ρ : Representation ℂ (locU n w) π.V := π.rep.comp (locU n w).subtype
  let ρf : Representation ℂ (finU (E := E) (n := n)) π.V := π.rep.comp (finU (E := E) (n := n)).subtype
  have hρ : IsSmooth ρ := isSmooth_loc π w
  have hle := locU_le_finU (n := n) w
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.isAut.ne_bot
  let v0 : π.V := ⟨φ, hφ⟩
  have hv0 : v0 ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  let L : Subgroup (finU (E := E) (n := n)) := LocEx.stab ρf v0
  have hLo : IsOpen (L : Set (finU (E := E) (n := n))) := by
    convert (π.isAut.aut φ hφ).level using 1
    ext k
    exact Subtype.ext_iff
  have hLl : IsOpen ((L.comap (Subgroup.inclusion hle) : Subgroup (locU n w)) : Set (locU n w)) :=
    hLo.preimage (continuous_inclusion_locU w)
  obtain ⟨K, hKo, hKc, hKL⟩ := exists_compact_open w r hr hrx L hLo

  have hT : ∀ x : UA E n, ∀ (g : locU n w) (y : π.V),
      π.rep ((r x : UA E n)⁻¹ * x) (ρ g y) = ρ g (π.rep ((r x : UA E n)⁻¹ * x) y) := fun x g y => by
    change π.rep _ (π.rep (g : UA E n) y) = π.rep (g : UA E n) (π.rep _ y)
    rw [← Module.End.mul_apply, ← map_mul, (hrc x g).eq, map_mul, Module.End.mul_apply]
  have hst : ∀ x, ∀ y ∈ LocEx.nullPart ρ K, π.rep x y ∈ LocEx.nullPart ρ K := fun x y hy => by
    have h1 := LocEx.nullPart_act ρ K (r x) (LocEx.nullPart_comm ρ K (π.rep ((r x : UA E n)⁻¹ * x)) (hT x) hy)
    have e : π.rep x y = ρ (r x) (π.rep ((r x : UA E n)⁻¹ * x) y) := by
      change _ = π.rep (r x : UA E n) _
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
    rw [e]
    exact h1
  have hφK : v0 ∈ fixed ρ K := LocEx.mem_fix.2 fun k hk => hKL hk
  have h2 : ∀ W : Submodule ℂ π.V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W ⊓ fixed ρ K = ⊥ → W = ⊥ := by
    intro W hW h
    rcases ((CuspRep.isIrreducible_iff _).1 π.isIrreducible_rep).2 (LocEx.nullPart ρ K) hst with h1 | h1
    · exact le_bot_iff.1 (h1 ▸ LocEx.le_nullPart hρ hKc W hW h)
    · exact absurd (LocEx.eq_zero_of_mem_nullPart hρ hKc hφK (h1 ▸ Submodule.mem_top)) hv0

  let M : Subgroup (UA E n) := L.map (finU (E := E) (n := n)).subtype ⊓ r.ker
  have hcomm : ∀ k ∈ M, ∀ g : locU n w, Commute k (g : UA E n) := fun k hk g => by
    have h := hrc k g
    rwa [MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hk).2, OneMemClass.coe_one, inv_one, one_mul] at h
  have hU : ∀ g, ∀ v ∈ fixed π.rep M, ρ g v ∈ fixed π.rep M := fun g v hv => LocEx.mem_fix.2 fun k hk => by
    change π.rep k (π.rep (g : UA E n) v) = π.rep (g : UA E n) v
    rw [← Module.End.mul_apply, ← map_mul, (hcomm k hk g).eq, map_mul, Module.End.mul_apply,
      LocEx.mem_fix.1 hv k hk]
  have hU0 : fixed π.rep M ≠ ⊥ := (Submodule.ne_bot_iff _).2 ⟨v0, LocEx.mem_fix.2 fun k hk => by
    obtain ⟨k', hk', rfl⟩ := (Subgroup.mem_inf.1 hk).1
    exact hk', hv0⟩
  have hfin : ∀ K' : Subgroup (locU n w), IsOpen (K' : Set (locU n w)) →
      FiniteDimensional ℂ ↥(fixed π.rep M ⊓ fixed ρ K') := fun K' hK' => by
    let r' : finU (E := E) (n := n) →* locU n w := r.comp (finU (E := E) (n := n)).subtype
    let H : Subgroup (finU (E := E) (n := n)) := L ⊓ (K' ⊓ L.comap (Subgroup.inclusion hle)).comap r'
    have hHo : IsOpen (H : Set (finU (E := E) (n := n))) := hLo.inter ((hK'.inter hLl).preimage (hr.comp continuous_subtype_val))
    haveI := hadm H hHo
    refine Submodule.finiteDimensional_of_le (S₂ := fixed ρf H) fun v hv => LocEx.mem_fix.2 fun k hk => ?_
    obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.1 hv
    obtain ⟨hkL, hkK, hkL'⟩ := And.intro (Subgroup.mem_inf.1 hk).1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hk).2)
    have hcM : (r k : UA E n)⁻¹ * k ∈ M := by
      refine Subgroup.mem_inf.2 ⟨⟨(Subgroup.inclusion hle (r' k))⁻¹ * k, L.mul_mem (L.inv_mem hkL') hkL, rfl⟩, ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hrx (r k), inv_mul_cancel]
    have e1 := LocEx.mem_fix.1 hv1 _ hcM
    have e2 : π.rep (r k : UA E n) v = v := LocEx.mem_fix.1 hv2 _ hkK
    change π.rep (k : UA E n) v = v
    rw [← mul_inv_cancel_left (r k : UA E n) (k : UA E n), map_mul, Module.End.mul_apply, e1, e2]
  obtain ⟨σ, ⟨f, hf0, hf⟩, hσ⟩ := LocEx.exists_irred hρ hKo h2 (fixed π.rep M) hU hU0 hfin
  refine ⟨σ, hσ, σ.irred, π.V.subtype ∘ₗ f, fun e => hf0 (LinearMap.ext fun v => Subtype.ext ?_), fun v => (f v).2,
    fun x v => ?_⟩
  · exact LinearMap.congr_fun e v
  · change (f (σ.ρ x v)).1 = _
    rw [hf]
    rfl

end GlobalTheory.DefU.LocAdm
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

theorem _root_.GlobalTheory.T.cmTypeNorm_generator_of_kummerField_le : ∀ (P : Pre) (δ : FieldDat P) (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F] (j : ℕ), δ.KPsi j ≤ F → ∀ 𝔞 : Ideal (𝓞 P.host.E), 𝔞 ≠ ⊥ → ∃ β : F, β ≠ 0 ∧ Submodule.span (𝓞 F) {β} = ∏ g : Tau P.R, (Submodule.span (𝓞 F) {x : F | ∃ a ∈ 𝔞, (x : ℂ) = P.host.φ₀ (P.host.sigmaOf g (a : P.host.E))} ^ (P.R.sigW j).1 * Submodule.span (𝓞 F) {x : F | ∃ a ∈ 𝔞, (x : ℂ) = P.host.φ₀ (P.host.sigmaOf g (P.host.conj (a : P.host.E)))} ^ (P.R.sigW j).2) ∧ ∀ σ : F →+* ℂ, ‖σ β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ ((P.R.sigW j).1 + (P.R.sigW j).2) := by
  first | exact @GlobalTheory.Mem.KPsiGen.typeNorm_gen_of_kPsi_le | exact GlobalTheory.Mem.KPsiGen.typeNorm_gen_of_kPsi_le | (intros; apply GlobalTheory.Mem.KPsiGen.typeNorm_gen_of_kPsi_le <;> assumption)
end
