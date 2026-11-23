module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle073
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.HeisAvgCompact

theorem exists_average_of_compact {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
    (K : AddSubgroup X) (hK : IsCompact (K : Set X)) (f : X → X → ℂ)
    (hf : Continuous fun p : X × X => f p.1 p.2) :
    ∃ g : X → ℂ, Continuous g ∧
      (∀ (c : ℂ) (x y : X), (∀ u ∈ K, f x u = c * f y u) → g x = c * g y) ∧
      (∀ (c : ℂ) (x y : X), ∀ u₀ ∈ K, (∀ u ∈ K, c * f x u = f y (u₀ + u)) → c * g x = g y) ∧
      ∀ (δ : ℝ) (z : ℂ) (w : X), (∀ a ∈ K, ‖f w a - z‖ ≤ δ) → ‖g w - z‖ ≤ δ := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  letI mK : MeasurableSpace K := borel K
  haveI : BorelSpace K := ⟨rfl⟩
  let ν : Measure K := Measure.addHaarMeasure ⊤
  haveI : IsProbabilityMeasure ν := ⟨by
    have h := Measure.addHaarMeasure_self (G := K) (K₀ := ⊤)
    rwa [TopologicalSpace.PositiveCompacts.coe_top] at h⟩
  have hF : Continuous (Function.uncurry fun (w : X) (u : K) => f w u) :=
    hf.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hfw : ∀ w, Continuous fun u : K => f w u := fun w => hF.comp (Continuous.prodMk_right w)
  have hint : ∀ w, Integrable (fun u : K => f w u) ν := fun w =>
    integrableOn_univ.1 ((hfw w).continuousOn.integrableOn_compact isCompact_univ)
  refine ⟨fun w => ∫ u : K, f w u ∂ν, ?_, ?_, ?_, ?_⟩
  · have h := continuous_parametric_integral_of_continuous (μ := ν) hF isCompact_univ
    simpa only [Measure.restrict_univ] using h
  · intro c x y h
    show (∫ u : K, f x u ∂ν) = c * ∫ u : K, f y u ∂ν
    rw [← integral_const_mul]
    congr 1
    funext u
    exact h u u.2
  · intro c x y u₀ hu₀ h
    show c * (∫ u : K, f x u ∂ν) = ∫ u : K, f y u ∂ν
    rw [← integral_const_mul, ← integral_add_left_eq_self (fun u : K => f y u) (⟨u₀, hu₀⟩ : K)]
    congr 1
    funext u
    exact h u u.2
  · intro δ z w hδ
    have hc : (∫ _u : K, z ∂ν) = z := by
      rw [integral_const, probReal_univ, one_smul]
    show ‖(∫ u : K, f w u ∂ν) - z‖ ≤ δ
    rw [← hc, ← integral_sub (hint w) (integrable_const _)]
    have h := norm_integral_le_of_norm_le_const (μ := ν) (C := δ) (f := fun u : K => f w u - z)
      (Filter.Eventually.of_forall fun u : K => hδ u u.2)
    rwa [probReal_univ, mul_one] at h

theorem exists_average : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A T : HSp D) (K : AddSubgroup (WO A T)), IsCompact (K : Set (WO A T)) → (∀ u ∈ K, ∀ u' ∈ K, ψ (symplOH A T u u') = 1) → ∀ (q : WO A T → ℂ), Continuous q → (∀ (γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E) (u : WO A T), q (ratW T A γ + u) = ψ (-(symplOH A T (ratW T A γ) u)) * q u) → ∃ g : WO A T → ℂ, Continuous g ∧ (∀ (γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E) (u : WO A T), g (ratW T A γ + u) = ψ (-(symplOH A T (ratW T A γ) u)) * g u) ∧ (∀ u ∈ K, heisO ψ A T u g = g) ∧ ∀ δ : ℝ, (∀ a ∈ K, ∀ w, ‖heisO ψ A T a q w - q w‖ ≤ δ) → ∀ w, ‖g w - q w‖ ≤ δ := by
  intro D ψ hψ A T K hK hKψ q hq hquasi
  obtain ⟨hTG, hLC, hSC, hT2, -, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank A.rank
  have hψc : Continuous ψ := hψ.1.1
  have hadd : Continuous fun p : WO A T × WO A T => p.1 + p.2 := hTG.toContinuousAdd.continuous_add
  have hf : Continuous fun p : WO A T × WO A T => heisO ψ A T p.2 q p.1 :=
    (hψc.comp (GlobalTheory.OrientedHeis.continuous_symplOH continuous_fst continuous_snd)).mul (hq.comp hadd)
  obtain ⟨g, h1, h2, h3, h4⟩ := @exists_average_of_compact (WO A T) _ _ hTG hLC hSC hT2 K hK
    (fun w u => heisO ψ A T u q w) hf
  refine ⟨g, h1, fun γ w => h2 _ _ _ fun u _ => GlobalTheory.OrientedHeis.heisO_quasi u q hquasi γ w,
    fun u₀ hu₀ => funext fun w => h3 (ψ (symplOH A T w u₀)) (w + u₀) w u₀ hu₀ fun u hu => ?_,
    fun δ hδ w => h4 δ (q w) w fun a ha => hδ a ha w⟩
  have h := congrFun (GlobalTheory.OrientedHeis.heisO_heisO (ψ := ψ) u₀ u q) w
  rw [hKψ u₀ hu₀ u hu, one_smul] at h
  exact h

end GlobalTheory.HeisAvgCompact
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.HeisNearZero

theorem heisO_near_zero_unif : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A T : HSp D) (q : WO A T → ℂ), Continuous q → (∀ (γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E) (u : WO A T), q (ratW T A γ + u) = ψ (-(symplOH A T (ratW T A γ) u)) * q u) → ∀ ε : ℝ, 0 < ε → ∃ N ∈ 𝓝 (0 : WO A T), ∀ a ∈ N, ∀ w, ‖heisO ψ A T a q w - q w‖ ≤ ε := by
  intro D ψ hψ A T q hq hlaw ε hε
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank A.rank
  have hc : Continuous ψ := hψ.1.1
  have hn : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  let Φ : WO A T × WO A T → ℂ := fun p => heisO ψ A T p.1 q p.2 - q p.2
  have hΦ : Continuous Φ := by
    have h1 : Continuous fun p : WO A T × WO A T => symplOH A T p.2 p.1 :=
      GlobalTheory.OrientedHeis.continuous_symplOH continuous_snd continuous_fst
    exact ((hc.comp h1).mul (hq.comp (continuous_snd.add continuous_fst))).sub (hq.comp continuous_snd)
  have hΦ0 : ∀ w, Φ (0, w) = 0 := by
    intro w
    simp only [Φ, heisO, GlobalTheory.MixModel.symplOH_zero_right, AddChar.map_zero_eq_one, one_mul, add_zero, sub_self]
  have hev : ∀ᶠ a in 𝓝 (0 : WO A T), ∀ w ∈ K, ‖Φ (a, w)‖ < ε := by
    refine hK.eventually_forall_of_forall_eventually fun w _ => ?_
    have ht : Filter.Tendsto Φ (𝓝 ((0 : WO A T), w)) (𝓝 0) := by
      have := hΦ.tendsto ((0 : WO A T), w); rwa [hΦ0] at this
    exact (ht.norm.eventually (gt_mem_nhds (by simpa using hε))).mono fun z hz => by simpa using hz
  refine ⟨_, hev, fun a ha w => ?_⟩
  obtain ⟨g, hg, hgw⟩ := hKc w
  obtain ⟨γ, rfl⟩ := GlobalTheory.MixModel.mem_ratMx.1 hg
  have e : Φ (a, GlobalTheory.MixModel.rat γ + w) = ψ (-(symplOH A T (ratW T A γ) w)) * Φ (a, w) := by
    simp only [Φ]
    rw [← GlobalTheory.MixModel.ratW_eq, GlobalTheory.OrientedHeis.heisO_quasi a q hlaw γ w, hlaw γ w, mul_sub]
  have h := ha _ hgw
  rw [e, norm_mul, hn, one_mul] at h
  exact h.le

end GlobalTheory.HeisNearZero
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.SmallLevel

theorem exists_open_subgroup (F : Type) [Field F] [NumberField F] (V : Set (Af F)) (hV : V ∈ 𝓝 (0 : Af F)) :
    ∃ S : AddSubgroup (Af F), IsOpen (S : Set (Af F)) ∧ (S : Set (Af F)) ⊆ V := by
  obtain ⟨M, hM, hMV⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F V hV
  let S : AddSubgroup (Af F) :=
    { carrier := {c | ∃ a : Af F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ c = M • a}
      zero_mem' := ⟨0, fun v => zero_mem _, (smul_zero M).symm⟩
      add_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a + b, fun v => add_mem (ha v) (hb v), (smul_add M a b).symm⟩
      neg_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨-a, fun v => neg_mem (ha v), (smul_neg M a).symm⟩ }
  refine ⟨S, S.isOpen_of_mem_nhds (g := 0) (GlobalTheory.AdLat.OpenLat.nsmul_integral_mem_nhds F M hM), ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  exact hMV a ha

theorem infPart_smul_eq_zero {D : D7} (y : Af D.host.F) (x : AE D) : infPart D (pairA D.host.F 0 y • x) = 0 := by
  rw [Algebra.smul_def, map_mul]
  have : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 y)) = 0 := by
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    exact TensorProduct.zero_tmul _ _
  rw [this, zero_mul]

theorem exists_closed_level (D : D7) (m n : ℕ) (N : Set (Mx D m n)) (hN : N ∈ 𝓝 (0 : Mx D m n)) :
    ∃ K : AddSubgroup (Mx D m n), IsClosed (K : Set (Mx D m n)) ∧ (K : Set (Mx D m n)) ⊆ N ∧
      (∀ u ∈ K, u.map (infPart D) = 0) ∧
      ∃ U : AddSubgroup (Mx D m n), IsOpen (U : Set (Mx D m n)) ∧ ∀ u ∈ U, u.map (infPart D) = 0 → u ∈ K := by
  classical
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (AE D) := IsModuleTopology.topologicalAddGroup (AF D.host.F) _
  haveI : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul _ _
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : T2Space (InfiniteAdeleRing D.host.F) := inferInstanceAs (T2Space ((v : InfinitePlace D.host.F) → v.Completion))
  let b := Module.finBasis D.host.F D.host.E
  let B := Algebra.TensorProduct.basis (AF D.host.F) b
  let Φ : (Fin m × Fin n × Fin (Module.finrank D.host.F D.host.E) → Af D.host.F) → Mx D m n :=
    fun x i j => ∑ k, pairA D.host.F 0 (x (i, j, k)) • B k
  have hΦ : Continuous Φ := by
    refine continuous_pi fun i => continuous_pi fun j => continuous_finsetSum _ fun k _ => ?_
    have h1 : Continuous fun x : Fin m × Fin n × Fin (Module.finrank D.host.F D.host.E) → Af D.host.F =>
        pairA D.host.F 0 (x (i, j, k)) := continuous_const.prodMk (continuous_apply _)
    exact h1.smul continuous_const
  have h0 : Φ 0 = 0 := by
    funext i j
    refine Finset.sum_eq_zero fun k _ => ?_
    exact zero_smul (AF D.host.F) (B k)
  have h1 : Φ ⁻¹' N ∈ 𝓝 0 := hΦ.continuousAt.preimage_mem_nhds (h0 ▸ hN)
  rw [nhds_pi, Filter.mem_pi] at h1
  obtain ⟨I, -, t, ht, hsub⟩ := h1
  obtain ⟨S, hS, hSt⟩ := exists_open_subgroup D.host.F (⋂ p, t p) (Filter.iInter_mem.mpr ht)
  let c : Fin m × Fin n × Fin (Module.finrank D.host.F D.host.E) → Mx D m n →+ AF D.host.F := fun p =>
    { toFun := fun u => B.coord p.2.2 (u p.1 p.2.1)
      map_zero' := map_zero _
      map_add' := fun u u' => map_add _ _ _ }
  have hc : ∀ p, Continuous (c p) := fun p =>
    (IsModuleTopology.continuous_of_linearMap (B.coord p.2.2)).comp
      ((continuous_apply p.2.1).comp (continuous_apply p.1))
  let U : AddSubgroup (Mx D m n) := ⨅ p, S.comap ((sndA D.host.F).toRingHom.toAddMonoidHom.comp (c p))
  let Z : AddSubgroup (Mx D m n) := ⨅ p, ((fstA D.host.F).toRingHom.toAddMonoidHom.comp (c p)).ker
  have hU : ∀ u, u ∈ U ↔ ∀ p, (c p u).2 ∈ S := fun u => AddSubgroup.mem_iInf
  have hZ : ∀ u, u ∈ Z ↔ ∀ p, (c p u).1 = 0 := fun u => AddSubgroup.mem_iInf
  have hUe : (U : Set (Mx D m n)) = ⋂ p, (fun u => (c p u).2) ⁻¹' S := by
    ext u; rw [Set.mem_iInter]; exact hU u
  have hZe : (Z : Set (Mx D m n)) = ⋂ p, {u | (c p u).1 = 0} := by
    ext u; rw [Set.mem_iInter]; exact hZ u
  have hrec : ∀ u ∈ Z, Φ (fun p => (c p u).2) = u := by
    intro u hu
    funext i j
    conv_rhs => rw [← B.sum_repr (u i j)]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    exact Prod.ext ((hZ u).mp hu (i, j, k)).symm rfl
  refine ⟨U ⊓ Z, ?_, ?_, ?_, U, ?_, ?_⟩
  · rw [AddSubgroup.coe_inf, hUe, hZe]
    exact (isClosed_iInter fun p => (S.isClosed_of_isOpen hS).preimage (continuous_snd.comp (hc p))).inter
      (isClosed_iInter fun p => isClosed_eq (continuous_fst.comp (hc p)) continuous_const)
  · intro u hu
    have h4 : (fun p => (c p u).2) ∈ I.pi t := fun p _ => Set.mem_iInter.mp (hSt ((hU u).mp hu.1 p)) p
    have h5 := hsub h4
    rwa [Set.mem_preimage, hrec u hu.2] at h5
  · intro u hu
    funext i j
    have h4 : ∑ k, pairA D.host.F 0 (c (i, j, k) u).2 • B k = u i j := congrFun (congrFun (hrec u hu.2) i) j
    rw [Matrix.map_apply, ← h4]
    exact (infPart D).toAddMonoidHom.ker.sum_mem fun k _ => infPart_smul_eq_zero _ _
  · rw [hUe]
    exact isOpen_iInter_of_finite fun p => hS.preimage (continuous_snd.comp (hc p))
  · intro u hu hu'
    refine ⟨hu, (hZ u).mpr fun p => ?_⟩
    have h2 := GlobalTheory.FinTranslate.smul_eq_zero_of_inf (congrFun (congrFun hu' p.1) p.2.1)
    have h3 : GlobalTheory.FinTranslate.eInf D * c p u = 0 := by
      have := congrArg (B.coord p.2.2) h2
      rwa [map_smul, map_zero, smul_eq_mul] at this
    exact (one_mul _).symm.trans (congrArg Prod.fst h3)

theorem exists_small_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A T : HSp D), ∀ N ∈ 𝓝 (0 : WO A T), ∃ K : AddSubgroup (WO A T), IsCompact (K : Set (WO A T)) ∧ (K : Set (WO A T)) ⊆ N ∧ (∀ u ∈ K, u.map (infPart D) = 0) ∧ (∃ U : AddSubgroup (WO A T), IsOpen (U : Set (WO A T)) ∧ ∀ u ∈ U, u.map (infPart D) = 0 → u ∈ K) ∧ ∀ u ∈ K, ∀ u' ∈ K, ψ (symplOH A T u u') = 1 := by
  intro D ψ hψ A T N hN
  haveI : LocallyCompactSpace (WO A T) := (GlobalTheory.MixModel.lattice_Mx D T.rank A.rank).2.1
  obtain ⟨C, hC, hC0⟩ := exists_compact_mem_nhds (0 : WO A T)
  have hs : Continuous fun p : WO A T × WO A T => (symplOH A T p.1 p.2).2 :=
    continuous_snd.comp (GlobalTheory.OrientedHeis.continuous_symplOH continuous_fst continuous_snd)
  have h2 := hs.continuousAt.preimage_mem_nhds (x := (0, 0)) (t := {a | ψ (pairA D.host.F 0 a) = 1})
    (by
      have h0 : (symplOH A T (0 : WO A T) 0).2 = 0 := congrArg Prod.snd (GlobalTheory.FinTranslate.symplOH_zero_left A T 0)
      have h1 := GlobalTheory.FinTranslate.ker_mem_nhds hψ.1.1 hψ.1.2.1
      rwa [← h0] at h1)
  obtain ⟨P, hP, Q, hQ, hPQ⟩ := mem_nhds_prod_iff.mp h2
  obtain ⟨K, hK, hKN, hKf, hKU⟩ := exists_closed_level D T.rank A.rank (N ∩ C ∩ (P ∩ Q))
    (Filter.inter_mem (Filter.inter_mem hN hC0) (Filter.inter_mem hP hQ))
  refine ⟨K, hC.of_isClosed_subset hK fun u hu => (hKN hu).1.2, fun u hu => (hKN hu).1.1, hKf, hKU,
    fun u hu u' hu' => ?_⟩
  have h3 : GlobalTheory.FinTranslate.eInf D * symplOH A T u u' = 0 := by
    rw [← GlobalTheory.FinTranslate.symplOH_smul_right, GlobalTheory.FinTranslate.smul_fin (hKf u' hu'),
      GlobalTheory.FinTranslate.symplOH_zero_right]
  have h4 : symplOH A T u u' = pairA D.host.F 0 (symplOH A T u u').2 :=
    Prod.ext ((one_mul _).symm.trans (congrArg Prod.fst h3)) rfl
  rw [h4]
  have h5 := hPQ (Set.mk_mem_prod (hKN hu).2.1 (hKN hu').2.2)
  rw [Set.mem_preimage, Set.mem_setOf_eq] at h5
  exact h5

end GlobalTheory.SmallLevel

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.RatPartition

theorem finite_ratW_mem {D : D7} (A T : HSp D) {C : Set (WO A T)} (hC : IsCompact C) :
    {γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E | ratW T A γ ∈ C}.Finite := by
  obtain ⟨i1, -, -, i4, i5, -⟩ := lattice_Mx D T.rank A.rank
  haveI := i1; haveI := i4; haveI := i5
  haveI : T1Space (Mx D T.rank A.rank) := @T2Space.t1Space _ _ i4
  have hLc : IsClosed (ratMx D T.rank A.rank : Set (Mx D T.rank A.rank)) := AddSubgroup.isClosed_of_discrete
  let φ : Matrix (Fin T.rank) (Fin A.rank) D.host.E → ratMx D T.rank A.rank := fun γ => ⟨ratW T A γ, γ, rfl⟩
  have hφ : Function.Injective φ := fun a b h =>
    Matrix.map_injective GlobalTheory.MixModel.incA_injective (congrArg Subtype.val h)
  have hs : IsCompact ((↑) ⁻¹' C : Set (ratMx D T.rank A.rank)) := by
    rw [Subtype.isCompact_iff, Set.image_preimage_eq_inter_range, Subtype.range_coe_subtype]
    exact hC.inter_right hLc
  exact (hs.finite_of_discrete.preimage (f := φ) hφ.injOn : _)

theorem exists_partition_one : ∀ (D : D7) (A T : HSp D), ∃ χ : WO A T → ℝ, Continuous χ ∧ HasCompactSupport χ ∧
    (∀ u, 0 ≤ χ u) ∧ ∀ u, HasSum (fun γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E => χ (ratW T A γ + u)) 1 := by
  intro D A T
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := lattice_Mx D T.rank A.rank
  haveI := i1; haveI := i2; haveI := i4
  haveI : RegularSpace (Mx D T.rank A.rank) := IsTopologicalAddGroup.regularSpace _
  haveI : ContinuousSub (Mx D T.rank A.rank) := IsTopologicalAddGroup.to_continuousSub
  obtain ⟨f, hf1, -, hfc, hf01⟩ := exists_continuous_one_zero_of_isCompact hK isClosed_empty (Set.disjoint_empty K)
  have hS : IsCompact (tsupport f) := hfc
  let g : Matrix (Fin T.rank) (Fin A.rank) D.host.E → WO A T → ℝ := fun γ u => f (ratW T A γ + u)
  have hgc : ∀ γ, Continuous (g γ) := fun γ => f.continuous.comp (continuous_const_add (ratW T A γ : WO A T))
  have hfin : ∀ N : Set (WO A T), IsCompact N → {γ | (Function.support (g γ) ∩ N).Nonempty}.Finite := by
    intro N hN
    refine (finite_ratW_mem A T ((hS.prod hN).image (continuous_fst.sub continuous_snd))).subset ?_
    rintro γ ⟨u, hu, huN⟩
    exact ⟨(ratW T A γ + u, u), ⟨subset_tsupport _ hu, huN⟩, add_sub_cancel_right _ _⟩
  have hlf : LocallyFinite fun γ => Function.support (g γ) := by
    intro u
    obtain ⟨N, hNc, hN⟩ := exists_compact_mem_nhds u
    exact ⟨N, hN, hfin N hNc⟩
  have hpt : ∀ u, (Function.support fun γ => g γ u).Finite := by
    intro u
    refine (hfin {u} isCompact_singleton).subset ?_
    intro γ hγ
    exact ⟨u, hγ, rfl⟩
  let s : WO A T → ℝ := fun u => ∑ᶠ γ, g γ u
  have hs_cont : Continuous s := continuous_finsum hgc hlf
  have hg0 : ∀ γ u, 0 ≤ g γ u := fun γ u => (hf01 _).1
  have hs1 : ∀ u, 1 ≤ s u := by
    intro u
    obtain ⟨x, ⟨γ, rfl⟩, hx⟩ := hKc u
    have h1 : g γ u = 1 := hf1 hx
    rw [← h1]
    exact single_le_finsum γ (hpt u) (fun j => hg0 j u)
  have hs_inv : ∀ γ₀ u, s (ratW T A γ₀ + u) = s u := by
    intro γ₀ u
    have e : ∀ γ, g γ (ratW T A γ₀ + u) = g (γ + γ₀) u := by
      intro γ
      simp only [g, ratW]
      rw [Matrix.map_add _ (map_add (incA D)) γ γ₀, add_assoc]
    simp only [s, e]
    exact finsum_comp_equiv (Equiv.addRight γ₀) (f := fun γ => g γ u)
  have hpos : ∀ u, 0 < s u := fun u => zero_lt_one.trans_le (hs1 u)
  refine ⟨fun u => f u * (s u)⁻¹, f.continuous.mul (hs_cont.inv₀ fun u => (hpos u).ne'), hfc.mul_right,
    fun u => mul_nonneg (hf01 u).1 (inv_nonneg.2 (hpos u).le), fun u => ?_⟩
  have e : (fun γ => f (ratW T A γ + u) * (s (ratW T A γ + u))⁻¹) = fun γ => g γ u * (s u)⁻¹ := by
    funext γ
    rw [hs_inv]
  simp only [e]
  have h : HasSum (fun γ => g γ u) (∑ γ ∈ (hpt u).toFinset, g γ u) :=
    hasSum_sum_of_ne_finset_zero (fun γ hγ => by simpa using hγ)
  rw [← finsum_eq_sum _ (hpt u)] at h
  have h2 := h.mul_right (s u)⁻¹
  rwa [mul_inv_cancel₀ (hpos u).ne'] at h2

end GlobalTheory.RatPartition

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.PoincareLaw

variable {D : D7}

theorem ratW_inj (A T : HSp D) : Function.Injective (ratW T A) :=
  fun _ _ h => Matrix.map_injective GlobalTheory.MixModel.incA_injective h

theorem ratW_sub (A T : HSp D) (γ γ₀ : Matrix (Fin T.rank) (Fin A.rank) D.host.E) :
    ratW T A (γ - γ₀) = ratW T A γ - ratW T A γ₀ := by
  ext i j
  simp [ratW, map_sub]

theorem finite_ratW_mem (A T : HSp D) (K : Set (WO A T)) (hK : IsCompact K) :
    {γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E | ratW T A γ ∈ K}.Finite := by
  obtain ⟨hg, hlc, hsc, ht2, hdisc, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T A
  haveI : T1Space (WA T A) := @T2Space.t1Space _ _ ht2
  have hcl : IsClosed (ratL T A : Set (WA T A)) := AddSubgroup.isClosed_of_discrete
  have hS : IsCompact ((Subtype.val : ratL T A → WA T A) ⁻¹' K) :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hfin := (hS.finite_of_discrete.image Subtype.val).preimage (ratW_inj A T).injOn
  refine hfin.subset fun γ hγ => ?_
  exact ⟨⟨ratW T A γ, γ, rfl⟩, hγ, rfl⟩

theorem symplOH_neg_left (A T : HSp D) (y z : WO A T) : symplOH A T (-y) z = -symplOH A T y z := by
  have hadd := (GlobalTheory.OrientedFormLaws.symplOH_laws D A T).1
  have h0 : symplOH A T 0 z = 0 := by
    have := hadd 0 0 z
    rw [add_zero] at this
    exact left_eq_add.1 this
  have := hadd y (-y) z
  rw [add_neg_cancel, h0] at this
  exact (eq_neg_of_add_eq_zero_right this.symm)

theorem poincare_law : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A T : HSp D) (h : WO A T → ℂ), Continuous h → HasCompactSupport h → (∀ u, {γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E | h (ratW T A γ + u) ≠ 0}.Finite) ∧ Continuous (fun u => ∑' γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E, ψ (symplOH A T (ratW T A γ) u) * h (ratW T A γ + u)) ∧ ∀ (γ₀ : Matrix (Fin T.rank) (Fin A.rank) D.host.E) (u : WO A T), (∑' γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E, ψ (symplOH A T (ratW T A γ) (ratW T A γ₀ + u)) * h (ratW T A γ + (ratW T A γ₀ + u))) = ψ (-(symplOH A T (ratW T A γ₀) u)) * ∑' γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E, ψ (symplOH A T (ratW T A γ) u) * h (ratW T A γ + u) := by
  intro D ψ hψ A T h hc hs
  obtain ⟨hg, hlc, -, -, -, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T A
  haveI : IsTopologicalAddGroup (WO A T) := hg
  haveI : LocallyCompactSpace (WO A T) := hlc
  haveI : ContinuousSub (WO A T) := @IsTopologicalAddGroup.to_continuousSub _ _ _ hg
  have laws := GlobalTheory.OrientedFormLaws.symplOH_laws D A T

  have vanish : ∀ (U : Set (WO A T)) (u : WO A T), u ∈ U → ∀ γ,
      γ ∉ {γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E | ratW T A γ ∈ (fun p : WO A T × WO A T => p.1 - p.2) '' (tsupport h ×ˢ U)} →
      h (ratW T A γ + u) = 0 := by
    intro U u hu γ hγ
    by_contra hne
    exact hγ ⟨(ratW T A γ + u, u), ⟨subset_tsupport h hne, hu⟩, add_sub_cancel_right _ _⟩
  refine ⟨fun u => ?_, ?_, fun γ₀ u => ?_⟩
  · refine (finite_ratW_mem A T _ ((hs.isCompact.prod (isCompact_singleton (x := u))).image continuous_sub)).subset fun γ hγ => ?_
    by_contra hn
    exact hγ (vanish {u} u rfl γ hn)
  · refine continuous_iff_continuousAt.2 fun u₀ => ?_
    obtain ⟨U, hU, hUn⟩ := exists_compact_mem_nhds u₀
    have hF := finite_ratW_mem A T _ ((hs.isCompact.prod hU).image continuous_sub)
    have hcont : Continuous fun u => ∑ γ ∈ hF.toFinset, ψ (symplOH A T (ratW T A γ) u) * h (ratW T A γ + u) :=
      continuous_finsetSum _ fun γ _ =>
        (hψ.1.1.comp (laws.2.2.2.2.1.comp (continuous_const.prodMk continuous_id))).mul
          (hc.comp (continuous_const_add (ratW T A γ)))
    refine hcont.continuousAt.congr (Filter.eventually_of_mem hUn fun u hu => ?_)
    refine (tsum_eq_sum fun γ hγ => ?_).symm
    rw [vanish U u hu γ (fun h' => hγ (hF.mem_toFinset.2 h')), mul_zero]
  · rw [← (Equiv.subRight γ₀).tsum_eq, ← tsum_mul_left]
    congr 1
    funext γ
    change ψ (symplOH A T (ratW T A (γ - γ₀)) (ratW T A γ₀ + u)) *
      h (ratW T A (γ - γ₀) + (ratW T A γ₀ + u)) = _
    rw [ratW_sub]
    have e1 : ratW T A γ - ratW T A γ₀ + (ratW T A γ₀ + u) = ratW T A γ + u := by abel
    have e2 : symplOH A T (ratW T A γ - ratW T A γ₀) (ratW T A γ₀ + u) =
        symplOH A T (ratW T A γ) (ratW T A γ₀) + symplOH A T (ratW T A γ) u +
          -(symplOH A T (ratW T A γ₀) u) := by
      rw [sub_eq_add_neg, laws.1, laws.2.1, laws.2.1, symplOH_neg_left, symplOH_neg_left, laws.2.2.1]
      ring
    obtain ⟨c, hc'⟩ := laws.2.2.2.2.2.1 (ratW T A γ) ⟨γ, rfl⟩ (ratW T A γ₀) ⟨γ₀, rfl⟩
    rw [e1, e2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hc', hψ.1.2.2.1 c]
    ring

end GlobalTheory.PoincareLaw
end
end
