module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle041
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCompactLatticeStabilizerBoundedReal
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemberDatumOfFlagTie
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle110
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle482
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle411
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle320
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle318
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle319
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle322
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle003
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SmallSub

theorem eq_zero_of_pow_mul {K : Type} [NormedField K] {C : Set K} (hC : IsCompact C) {c x : K} (hc : ‖c‖ < 1)
    (h : ∀ n : ℕ, ∃ u ∈ C, x = c ^ n * u) : x = 0 := by
  obtain ⟨B, hB⟩ := hC.isBounded.exists_norm_le
  have ht : Filter.Tendsto (fun n : ℕ => ‖c‖ ^ n * B) Filter.atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg c) hc).mul_const B
  refine norm_le_zero_iff.1 (ge_of_tendsto' ht fun n => ?_)
  obtain ⟨u, hu, rfl⟩ := h n
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (hB u hu) (by positivity)

theorem finiteAdele_eq_zero (F : Type) [Field F] [NumberField F] {C : Set (Af F)} (hC : IsCompact C) {x : Af F}
    (h : ∀ M : ℕ, 0 < M → ∃ u ∈ C, x = M • u) : x = 0 := by
  refine Subtype.ext (funext fun v => ?_)
  change evalV F v x = 0
  have hv : Continuous (evalV F v) := RestrictedProduct.continuous_eval v
  have h1 := (NumberField.FinitePlace.norm_lt_one_iff_mem F v _).2 (Ideal.absNorm_mem v.asIdeal)
  rw [map_natCast, map_natCast] at h1
  have h0 : 0 < Ideal.absNorm v.asIdeal :=
    Nat.pos_of_ne_zero fun e => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 e)
  refine eq_zero_of_pow_mul (hC.image hv) h1 fun n => ?_
  obtain ⟨u, hu, rfl⟩ := h _ (pow_pos h0 n)
  exact ⟨_, ⟨u, hu, rfl⟩, by rw [map_nsmul, nsmul_eq_mul, Nat.cast_pow]⟩

theorem tensor_eq_zero (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {C : Set (Af F ⊗[F] E)} (hC : IsCompact C) {x : Af F ⊗[F] E}
    (h : ∀ M : ℕ, 0 < M → ∃ u ∈ C, x = M • u) : x = 0 := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  let b := Algebra.TensorProduct.basis (Af F) (Module.finBasis F E)
  refine b.ext_elem fun i => ?_
  have hc : Continuous (b.coord i) := IsModuleTopology.continuous_of_linearMap _
  rw [map_zero, Finsupp.zero_apply]
  change b.coord i x = 0
  refine finiteAdele_eq_zero F (hC.image hc) fun M hM => ?_
  obtain ⟨u, hu, rfl⟩ := h M hM
  exact ⟨_, ⟨u, hu, rfl⟩, map_nsmul _ _ _⟩

theorem mem_GinfC_of_cong {D : D7} (V : HSp D) (k : GA D V)
    (h : ∀ n : ℕ, GlobalTheory.Ker.CongK V (GlobalTheory.SW.stdL D.host.E V.rank) n.factorial k) : k ∈ GinfC V := by
  obtain ⟨C, hC, hLC⟩ := GlobalTheory.StabCompact.exists_compact_latHat D.host.F D.host.E (GlobalTheory.SW.stdL D.host.E V.rank)
    (Submodule.fg_span (Set.finite_range _))
  refine Units.ext ?_
  change GlobalTheory.Ker.fmt V k = 1
  ext i j
  have h1 : (1 : Af D.host.F) ∈ intAf D.host.F := fun w => by rw [map_one]; exact one_mem _
  have hy : (Pi.single j 1 : Fin V.rank → GlobalTheory.Ker.AfE D) ∈ GlobalTheory.Ker.hatV (D := D) (GlobalTheory.SW.stdL D.host.E V.rank) := by
    refine AddSubgroup.subset_closure ⟨1, h1, Pi.single j 1, Submodule.subset_span ⟨j, rfl⟩, ?_⟩
    funext a
    by_cases e : a = j
    · subst e
      simp only [Pi.single_eq_same]
      rfl
    · simp [Pi.single_eq_of_ne e]
  have key : (GlobalTheory.Ker.fmt V k *ᵥ Pi.single j 1 - (Pi.single j 1 : Fin V.rank → GlobalTheory.Ker.AfE D)) i = 0 := by
    refine tensor_eq_zero D.host.F D.host.E (hC.image (continuous_apply i)) fun M hM => ?_
    obtain ⟨u, hu, e⟩ := (h M).2 _ hy
    obtain ⟨c, hc⟩ := Nat.dvd_factorial hM le_rfl
    refine ⟨_, ⟨c • u, hLC _ (nsmul_mem hu c), rfl⟩, ?_⟩
    rw [e, hc, mul_smul]
    rfl
  rw [Pi.sub_apply, sub_eq_zero, Matrix.mulVec_single_one] at key
  rw [Matrix.one_apply, ← Pi.single_apply]
  exact key

theorem exists_open_subgroup_finite_subset : ∀ (D : D7) (V : HSp D), ∀ N ∈ 𝓝 (1 : GA D V), ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → k ∈ N := by
  intro D V N hN
  obtain ⟨i0, -, -, i3, -, -, hK⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V
  have hL : (GlobalTheory.SW.stdL D.host.E V.rank).FG ∧ Submodule.span D.host.E
      (GlobalTheory.SW.stdL D.host.E V.rank : Set (Fin V.rank → D.host.E)) = ⊤ := by
    refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
    rw [eq_top_iff, ← (Pi.basisFun D.host.E (Fin V.rank)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨a, rfl⟩
    apply Submodule.subset_span
    exact ⟨a, by simp⟩
  choose K hK1 hK2 hK3 _ using fun n : ℕ => hK _ n.factorial hL n.factorial_pos
  have hanti : Antitone fun n => (K n : Set (GA D V)) ∩ GfC V := by
    intro m n hmn k hk
    refine ⟨(hK1 m k).2 ⟨((hK1 n k).1 hk.1).1, fun u hu => ?_⟩, hk.2⟩
    obtain ⟨w, hw, e⟩ := ((hK1 n k).1 hk.1).2 u hu
    obtain ⟨c, hc⟩ := Nat.factorial_dvd_factorial hmn
    exact ⟨c • w, nsmul_mem hw c, by rw [e, hc, mul_smul]⟩
  obtain ⟨n, hn⟩ := exists_subset_nhds_of_isCompact' (U := N) hanti.directed_ge hK3 (fun n => (hK3 n).isClosed)
    (mem_nhdsSet_iff_forall.2 fun x hx => by
      rw [Set.mem_iInter] at hx
      rwa [GlobalTheory.AutFunCounterexample.GfC_inf_GinfC V (hx 0).2 (mem_GinfC_of_cong V x fun n => (hK1 n x).1 (hx n).1)])
  exact ⟨K n, hK2 n, fun k hk hf => hn ⟨hk, hf⟩⟩

end GlobalTheory.Mem.SmallSub
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BesselClosed

open GlobalTheory.BesselCompare (mt_mul mt_one hA_coeff closure_prop spanA)

variable {D : D7}

def spanLt (B : HSp D) {ρ : ℕ} (e : Fin ρ → B.V) (k : ℕ) : Submodule (AE D) (Fin B.rank → AE D) where
  carrier := {v | ∃ c : Fin ρ → AE D, (∀ l : Fin ρ, k ≤ l.1 → c l = 0) ∧ v = ∑ l, c l • vecA B (e l)}
  zero_mem' := ⟨0, fun _ _ => rfl, by simp⟩
  add_mem' := by
    rintro _ _ ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
    exact ⟨c + c', fun l hl => by simp [hc l hl, hc' l hl], by simp [add_smul, Finset.sum_add_distrib]⟩
  smul_mem' := by
    rintro a _ ⟨c, hc, rfl⟩
    exact ⟨a • c, fun l hl => by simp [hc l hl], by simp [Finset.smul_sum, smul_smul]⟩

variable {B : HSp D} {ρ : ℕ} {e : Fin ρ → B.V}

theorem spanLt_mono {k k' : ℕ} (h : k ≤ k') : spanLt B e k ≤ spanLt B e k' := by
  rintro _ ⟨c, hc, rfl⟩
  exact ⟨c, fun l hl => hc l (h.trans hl), rfl⟩

theorem vec_mem_spanLt {k : ℕ} {l : Fin ρ} (h : l.1 < k) : vecA B (e l) ∈ spanLt B e k := by
  classical
  refine ⟨Pi.single l 1, fun j hj => Pi.single_eq_of_ne (fun e => by subst e; omega) _, ?_⟩
  rw [Finset.sum_eq_single l] <;> simp +contextual

theorem mulVec_mem_spanLt {k : ℕ} (M : Matrix (Fin B.rank) (Fin B.rank) (AE D))
    (hM : ∀ l : Fin ρ, l.1 < k → M.mulVec (vecA B (e l)) - vecA B (e l) ∈ spanLt B e l.1)
    {v} (hv : v ∈ spanLt B e k) : M.mulVec v ∈ spanLt B e k := by
  obtain ⟨c, hc, rfl⟩ := hv

  rw [← Matrix.mulVecLin_apply, map_sum]
  refine Submodule.sum_mem _ fun l _ => ?_
  rcases lt_or_ge l.1 k with hl | hl
  · rw [map_smul]
    refine Submodule.smul_mem _ _ ?_
    have := add_mem (spanLt_mono hl.le (hM l hl)) (vec_mem_spanLt (B := B) (e := e) hl)
    rwa [sub_add_cancel] at this
  · simp [hc l hl]

theorem mem_NS_iff {n : GA D B} : n ∈ GlobalTheory.BesselCompare.NS B e ↔
    (∀ i : Fin ρ, actV B n (e i) - vecA B (e i) ∈ spanLt B e i.1) ∧
      ∀ x : B.V, (∀ i, B.hD x (e i) = 0) → actV B n x - vecA B x ∈ spanLt B e ρ := by
  refine and_congr (forall_congr' fun i => exists_congr fun c => and_congr Iff.rfl sub_eq_iff_eq_add'.symm)
    (forall_congr' fun x => forall_congr' fun _ => exists_congr fun c => ?_)
  rw [sub_eq_iff_eq_add']
  exact ⟨fun h => ⟨fun l hl => absurd l.2 (by omega), h⟩, fun h => h.2⟩

theorem closure_flag (n : GA D B) (hn : n ∈ Subgroup.closure (GlobalTheory.BesselCompare.NS B e)) :
    ∀ i : Fin ρ, actV B n (e i) - vecA B (e i) ∈ spanLt B e i.1 := by
  induction hn using Subgroup.closure_induction'' with
  | one => intro i; simp [actV, mt_one]
  | mem g hg => exact (mem_NS_iff.1 hg).1
  | inv_mem g hg =>
    intro i
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      have h := mulVec_mem_spanLt (mt B g⁻¹) (fun l hl => ih l hl) ((mem_NS_iff.1 hg).1 i)
      rw [Matrix.mulVec_sub, actV, mulVec_inv_cancel] at h
      have := neg_mem h
      rwa [neg_sub] at this
  | mul g h _ _ ihg ihh =>
    intro i
    have := add_mem (mulVec_mem_spanLt (mt B g) (fun l _ => ihg l) (ihh i)) (ihg i)
    rwa [Matrix.mulVec_sub, actV, ← mulVec_mul, actV, sub_add_sub_cancel] at this

theorem closure_NS : (Subgroup.closure (GlobalTheory.BesselCompare.NS B e) : Set (GA D B)) = GlobalTheory.BesselCompare.NS B e := by
  refine subset_antisymm (fun n hn => mem_NS_iff.2 ⟨closure_flag n hn, fun x hx => ?_⟩) Subgroup.subset_closure
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 ((closure_prop B e n hn).2 x hx)
  exact ⟨a, fun l hl => absurd l.2 (by omega), ha.symm⟩

theorem mem_spanLt_iff {f : Fin ρ → B.V} (ef : ∀ i j, B.hD (e i) (f j) = if i = j then 1 else 0) {k : ℕ} {v} :
    v ∈ spanLt B e k ↔ (∀ l : Fin ρ, k ≤ l.1 → hA B v (vecA B (f l)) = 0) ∧
      v = ∑ l, hA B v (vecA B (f l)) • vecA B (e l) := by
  refine ⟨?_, fun h => ⟨_, h⟩⟩
  rintro ⟨c, hc, rfl⟩
  simp only [hA_coeff B e f ef]
  exact ⟨hc, trivial⟩

theorem isClosed_NS {f : Fin ρ → B.V} (ef : ∀ i j, B.hD (e i) (f j) = if i = j then 1 else 0) :
    IsClosed (GlobalTheory.BesselCompare.NS B e) := by
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (AF D.host.F)
  have : T2Space (AE D) := e0.isEmbedding.t2Space
  have : IsTopologicalRing (AE D) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing
  have hm : Continuous (fun k : GA D B => mt B k) := Units.continuous_val.comp continuous_subtype_val
  have hh : ∀ y, Continuous fun v => hA B v y := fun y =>
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)
  have hc : ∀ k, IsClosed (spanLt B e k : Set (Fin B.rank → AE D)) := fun k => by
    have : (spanLt B e k : Set (Fin B.rank → AE D)) =
        (⋂ l : Fin ρ, ⋂ _ : k ≤ l.1, {v | hA B v (vecA B (f l)) = 0}) ∩
          {v | v = ∑ l, hA B v (vecA B (f l)) • vecA B (e l)} := by
      ext v
      simp only [SetLike.mem_coe, mem_spanLt_iff ef, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    rw [this]
    exact (isClosed_iInter fun l => isClosed_iInter fun _ => isClosed_eq (hh _) continuous_const).inter
      (isClosed_eq continuous_id (continuous_finsetSum _ fun l _ => (hh _).smul continuous_const))
  have : IsTopologicalAddGroup (AE D) := IsTopologicalRing.to_topologicalAddGroup
  have : ContinuousSub (AE D) := IsTopologicalAddGroup.to_continuousSub
  have ha : ∀ x, Continuous fun n : GA D B => actV B n x - vecA B x := fun x =>
    continuous_pi fun j => ((continuous_apply j).comp (hm.matrix_mulVec continuous_const)).sub continuous_const
  have : GlobalTheory.BesselCompare.NS B e =
      (⋂ i : Fin ρ, (fun n => actV B n (e i) - vecA B (e i)) ⁻¹' spanLt B e i.1) ∩
        ⋂ x : B.V, ⋂ _ : ∀ i, B.hD x (e i) = 0, (fun n => actV B n x - vecA B x) ⁻¹' spanLt B e ρ := by
    ext n
    simp only [mem_NS_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
  rw [this]
  exact (isClosed_iInter fun i => (hc _).preimage (ha _)).inter
    (isClosed_iInter fun x => isClosed_iInter fun _ => (hc _).preimage (ha _))

theorem N_eq_and_isClosed : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι), (d.N : Set (GA D B)) = d.NSet ∧ IsClosed (d.N : Set (GA D B)) := by
  intro D A B ι d
  have h : (d.N : Set (GA D B)) = GlobalTheory.BesselCompare.NS B d.e := closure_NS
  exact ⟨h, h ▸ isClosed_NS d.ef⟩

end GlobalTheory.BesselClosed

end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.L2
open Formalism.AUTREP (GAf)

namespace GlobalTheory.LocRelIndex

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (J : Subgroup (GAf L n)) (H : Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))), (∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ s.loc n κ ∈ H)) → J.relIndex (GlobalTheory.HeckeScalarSph.locK n s.v) = H.relIndex (Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) := by
  intro L _ _ _ n s J H hJH
  set K := GlobalTheory.HeckeScalarSph.locK (L := L) n s.v with hK
  set O := Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring with hO
  let φ : K →* O :=
    ((s.loc n).comp K.subtype).codRestrict O (fun κ => (GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s κ.2.2).2 κ.2.1)
  have hsurj : Function.Surjective φ := by
    intro A
    obtain ⟨x, hx, -⟩ := (GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s).2.2 A.1
    refine ⟨⟨x, ?_, hx.1⟩, ?_⟩
    · exact (GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s hx.1).1 (hx.2 ▸ A.2)
    · exact Subtype.ext hx.2
  have hcomap : J.subgroupOf K = (H.subgroupOf O).comap φ := by
    ext κ
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    exact hJH κ κ.2.2
  rw [Subgroup.relIndex, Subgroup.relIndex, hcomap, Subgroup.index_comap_of_surjective _ hsurj]

end GlobalTheory.LocRelIndex
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.HeckeEigConj

theorem proj_conjSplit {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (z : AL L) :
    (GlobalTheory.HeckeFrob.conjSplit s).proj z = s.proj (conjAL L z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]; rfl
  | tmul a b =>
    simp only [SplitPlace.proj, conjAL, GlobalTheory.HeckeFrob.conjSplit, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rfl
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]; rfl

theorem map_loc_conjSplit (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) {K' : Type}
    [Field K'] (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* K') (x : GAf L n) :
    Matrix.GeneralLinearGroup.map i.toRingHom ((GlobalTheory.HeckeFrob.conjSplit s).loc n x) =
      GlobalTheory.LFun.ConjPlace.invT i n (s.loc n x) := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [GlobalTheory.LFun.ConjPlace.invT_val, ← map_inv]
  have h := congrFun₂ (GlobalTheory.FinTypCount.inv_val x) b a
  change i ((GlobalTheory.HeckeFrob.conjSplit s).proj _) = i (s.proj ((((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix _ _ _) b a))
  rw [h, proj_conjSplit]
  rfl

theorem KO_eq_KGL (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n) = GlobalTheory.LFun.KGL w (n := n) := by
  ext g
  rw [GlobalTheory.SplitFlip.mem_KO_iff, GlobalTheory.HeckeScalarSph.mem_GLint_iff]
  have h : ∀ x : w.adicCompletion E, x ∈ 𝒪[w.adicCompletion E] ↔ x ∈ Formalism.UG.Ov E w := fun x =>
    (Valuation.mem_integer_iff _ _).trans (GlobalTheory.CuspRep.ParLaws.valuation_le_one_iff w x)
  simp only [h]

theorem heckeD_eq_sum_of_agree {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W]
    [Module ℂ W] (J : Subgroup (GAf L n)) {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))}
    (hJ : ∀ κ, TrivOutside {v} κ → (κ ∈ J ↔ κ ∈ Umax L n)) {D : Set (GAf L n)} (hD : ∀ x ∈ D, TrivOutside {v} x)
    {R : Finset (GAf L n)} (h1 : ∀ γ ∈ R, γ ∈ D) (h2 : ∀ x ∈ D, ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Umax L n)
    {f : GAf L n → W} (hf : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) :
    NG.heckeD J D f = ∑ γ ∈ R, NG.rt L n γ f := by
  classical
  have hmem : ∀ x ∈ D, ∀ y ∈ D, (x⁻¹ * y ∈ J ↔ x⁻¹ * y ∈ Umax L n) := fun x hx y hy =>
    hJ _ (GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_inv (hD x hx)) (hD y hy))
  funext g
  rw [Finset.sum_apply, NG.heckeD, finsum_eq_sum_of_support_subset (s := R.image fun x : GAf L n => (x : GAf L n ⧸ J)),
    Finset.sum_image]
  · refine Finset.sum_congr rfl fun γ hγ => ?_
    have hc : ∃ x ∈ D, (x : GAf L n ⧸ J) = γ := ⟨γ, h1 γ hγ, rfl⟩
    rw [dite_eq_left hc]
    have hu : γ⁻¹ * hc.choose ∈ Umax L n :=
      (hmem γ (h1 γ hγ) _ hc.choose_spec.1).1 (QuotientGroup.eq.1 hc.choose_spec.2.symm)
    have := congrFun (hf _ hu (GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_inv (hD γ (h1 γ hγ)))
      (hD _ hc.choose_spec.1))) (g * γ)
    refine Eq.trans ?_ this
    show f _ = f _
    congr 1
    group
  · intro γ hγ δ hδ e
    exact (h2 δ (h1 δ hδ)).unique ⟨hγ, (hmem γ (h1 γ hγ) δ (h1 δ hδ)).1 (QuotientGroup.eq.1 e)⟩
      ⟨hδ, by rw [inv_mul_cancel]; exact one_mem _⟩
  · intro c hc
    by_cases h : ∃ x ∈ D, (x : GAf L n ⧸ J) = c
    · obtain ⟨x, hx, rfl⟩ := h
      obtain ⟨γ, ⟨hγ, e⟩, -⟩ := h2 x hx
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨γ, hγ, QuotientGroup.eq.2 ((hmem γ (h1 γ hγ) x hx).2 e)⟩)
    · exact absurd (dif_neg h) hc

theorem norms_eq {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) :
    Formalism.UG.qV L (GlobalTheory.HeckeFrob.conjSplit s).w = normV (GlobalTheory.HeckeFrob.conjSplit s).w ∧
      s.q = normV (GlobalTheory.HeckeFrob.conjSplit s).w := by
  refine ⟨?_, ?_⟩
  · rw [Formalism.UG.qV, Ideal.absNorm_apply, Submodule.cardQuot_apply, normV]
  · rw [normV, (GlobalTheory.HeckeFrob.conjSplit s).card_quot]
    rfl

end GlobalTheory.HeckeEigConj

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.GroupLoc

variable {D : D7}

def ModW (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (S : Set (VA X.B.I)) (y : VA X.B.I) : Prop :=
  y ∈ Submodule.span (Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) S ⊔ wLf X w

def CondAt (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (x : X.B.I.Gf) : Prop :=
  (∀ a : Fin D.R.rS, ModW X w (X.e0 '' {b | b.1 < a.1}) ((X.B.I.fmat x - 1) *ᵥ X.e0 a)) ∧
    ModW X w (Set.range X.e0) ((X.B.I.fmat x - 1) *ᵥ X.z0) ∧
    ∀ i : Fin D.R.k, ModW X w (Set.range X.e0 ∪ X.bw '' {j | j.1 < i.1}) ((X.B.I.fmat x - 1) *ᵥ X.bw i)

def symAllowed (ρ k : ℕ) {r : ℕ} (i j : Fin r) : Prop :=
  j.1 < i.1 ∧ ¬ (ρ ≤ j.1 ∧ j.1 < ρ + k ∧ i.1 = ρ + k)

def ColCond (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (x : X.B.I.Gf) : Prop :=
  ∀ i : Fin D.R.r, ModW X w (GlobalTheory.Mem.SymFrame.symVec X w '' {j | symAllowed D.R.rS D.R.k i j})
    ((X.B.I.fmat x - 1) *ᵥ GlobalTheory.Mem.SymFrame.symVec X w i)

end GlobalTheory.Mem.GroupLoc

end
end

section

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

theorem _root_.GlobalTheory.T.upwardLevelMove_incidence_of_pairs : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (P : LvTied u A i hi) (K : ClsTied u i hi) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i) (z : ↥(Ld D u i hi c)) (γ : GL (Fin (D.R.N i)) D.host.E), (D.fm u).fv i v c (P.pr v c z) = 1 → loc (A.res v) (mulLat γ.1 (clsCrd D u i hi c')) = loc (A.res v) (Ld D u i hi c) → loc (A.res v) (mulLat γ.1 (Ld D u i hi c')) = loc (A.res v) (Ld D u i hi c ⊔ Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1}) → (∀ (x : ↥(Ld D u i hi c')) (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1 *ᵥ x.1) ∈ Ld D u i hi c), (D.fm u).fv i v c' (P.pr v c' x) = (D.fm u).fv i v c (P.pr v c ⟨_, hx⟩)) → ((pc P v c').act (glE γ)).IsKer (pc P v c).L ∧ ∃ e, ((pc P v c').act (glE γ)).f e = 1 ∧ locExt (A.res v) (Ld D u i hi c) (P.pr v c) ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • e) = P.pr v c z := by
  first | exact @GlobalTheory.LevelHecke.up_move_incidence | exact GlobalTheory.LevelHecke.up_move_incidence | (intros; apply GlobalTheory.LevelHecke.up_move_incidence <;> assumption)
end

section

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

theorem _root_.GlobalTheory.T.downwardLevelMove_reaches_kernelLattice : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (P : LvTied u A i hi) (K : ClsTied u i hi) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i) (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)) (γ : GL (Fin (D.R.N i)) D.host.E), loc (A.res v) (mulLat γ.1 (Ld D u i hi c')) = loc (A.res v) (clsCrd D u i hi c) → (∀ (x : ↥(Ld D u i hi c')) (hx : γ.1 *ᵥ x.1 ∈ Lk A i hi v c), (D.fm u).fv i v c' (P.pr v c' x) = g (P.prk v c ⟨_, hx⟩)) → ((pc P v c').act (glE γ)).L = loc (A.res v) (Lk A i hi v c) ∧ ∀ x ∈ loc (A.res v) (Lk A i hi v c), ((pc P v c').act (glE γ)).f x = g (locExt (A.res v) (Lk A i hi v c) (P.prk v c) x) := by
  first | exact @GlobalTheory.LevelHecke.pc_act_down | exact GlobalTheory.LevelHecke.pc_act_down | (intros; apply GlobalTheory.LevelHecke.pc_act_down <;> assumption)
end

section

namespace GlobalTheory.Published

theorem GlobalArtinReciprocity.heckeLAdicCharacter_and_principalIdealSt :
    GlobalArtinReciprocity → HeckeLAdicCharacter ∧ PrincipalIdealSt :=
  fun h => ⟨h.heckeLAdicCharacter, h.principalIdealSt⟩

end GlobalTheory.Published
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.existsUnique_normalizedHaarMeasure_adelicUnitary : ∀ (D : D7) (V : HSp D), V.SigOK → ∃! μ, IsVolMeasG D V (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) μ := by
  first | exact @GlobalTheory.Mem.VolMeasure.existsUnique_isVolMeasG | exact GlobalTheory.Mem.VolMeasure.existsUnique_isVolMeasG | (intros; apply GlobalTheory.Mem.VolMeasure.existsUnique_isVolMeasG <;> assumption)
end
