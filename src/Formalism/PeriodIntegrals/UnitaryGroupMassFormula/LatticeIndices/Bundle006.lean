module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle004
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Topology
open scoped ENNReal

theorem measOfRed (hH : HaarIdx) (hR : RedIdx) {G : Type} [Group G] [TopologicalSpace G]
    [MeasurableSpace G] (hT : ContinuousMul G ∧ BorelSpace G) (μ : Measure G) [μ.IsMulLeftInvariant]
    (K : Subgroup G) {Q : Type} [Group Q] [Finite Q] (ρ : K →* Q) (hρ : Function.Surjective ρ)
    (Kg : Set G) (hKg : IsOpen Kg) (hKgK : Kg ⊆ K) (hker : ∀ x : K, ρ x = 1 ↔ (x : G) ∈ Kg)
    (A : Subgroup K) (hA : ρ.ker ≤ A) :
    IsOpen (Subtype.val '' (A : Set K)) ∧ Subtype.val '' (A : Set K) ⊆ K ∧
      μ (K : Set G) = (A.index : ℝ≥0∞) * μ (Subtype.val '' (A : Set K)) ∧
      A.index * Nat.card (A.map ρ) = Nat.card Q := by
  obtain ⟨hcm, hbo⟩ := hT
  have hone : (1 : G) ∈ Kg := by
    have := (hker 1).1 (map_one ρ)
    simpa using this
  have hsub : Subtype.val '' (A : Set K) ⊆ K := by
    rintro _ ⟨a, _, rfl⟩
    exact a.2
  have hopen : IsOpen (Subtype.val '' (A : Set K)) := by
    have heq : Subtype.val '' (A : Set K) = ⋃ a ∈ (A : Set K), (fun y => (a : G) * y) '' Kg := by
      ext x
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact Set.mem_biUnion ha ⟨1, hone, by simp⟩
      · intro hx
        obtain ⟨a, ha, y, hy, rfl⟩ := Set.mem_iUnion₂.1 hx
        have hyK : y ∈ K := hKgK hy
        have hyA : (⟨y, hyK⟩ : K) ∈ A := hA ((hker ⟨y, hyK⟩).2 hy)
        exact ⟨a * ⟨y, hyK⟩, A.mul_mem ha hyA, rfl⟩
    rw [heq]
    refine isOpen_biUnion fun a _ => ?_
    exact (Homeomorph.mulLeft (a : G)).isOpenMap _ hKg
  refine ⟨hopen, hsub, ?_, hR K Q ρ hρ A hA⟩
  have hidx : A.index ≠ 0 := by
    haveI : Nonempty Q := ⟨1⟩
    have h1 : ρ.ker.index ≠ 0 := by
      rw [Subgroup.index_ker]
      exact Nat.card_pos.ne'
    exact fun h0 => h1 (Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.index_dvd_of_le hA))
  have hmap : ((A.map K.subtype : Subgroup G) : Set G) = Subtype.val '' (A : Set K) := by
    rw [Subgroup.coe_map]
    rfl
  have hrel : (A.map K.subtype).relIndex K = A.index := by
    rw [Subgroup.relIndex]
    show (Subgroup.comap K.subtype (A.map K.subtype)).index = _
    rw [Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
  have hle : A.map K.subtype ≤ K := by
    intro x hx
    rw [← SetLike.mem_coe, hmap] at hx
    exact hsub hx
  have key := hH G μ K (A.map K.subtype) hle (by rw [hmap]; exact hopen) (by rw [hrel]; exact hidx)
  rw [key, hrel, hmap]

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

theorem gOf_prime (p : TypX X) : (gOf p).Prime := by
  unfold gOf
  split_ifs
  · exact D.host.g_prime 0
  · exact D.host.g_prime 1

theorem finite_GL (p : TypX X) : Finite (GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) := by
  haveI : Fact (gOf p).Prime := ⟨gOf_prime X p⟩
  infer_instance

theorem kg_sub (p : TypX X) : KgX X p ⊆ KvX X p := fun _ hx => hx.1

theorem measA_of (hH : HaarIdx) (hR : RedIdx) (p : TypX X) (hT : StTop X p) (hK : StK X p)
    (hRed : StRed X p) (hIm : StImA X hb p) : StMeasA X hb p := by
  obtain ⟨K, hKv, -, -, hKgo⟩ := hK
  obtain ⟨ρ, hρs, hρk⟩ := hRed K hKv
  haveI := finite_GL X p
  obtain ⟨A, hAeq, hAker, hAcard⟩ := hIm K hKv ρ hρs hρk
  haveI : (muP X p).IsHaarMeasure := X.measG_norm.2.2.2.1 p.1
  have hKgK : KgX X p ⊆ (K : Set (HAp X p)) := hKv ▸ kg_sub X p
  obtain ⟨-, -, hmeas, hidx⟩ :=
    measOfRed hH hR hT (muP X p) K ρ hρs (KgX X p) hKgo hKgK hρk A hAker
  rw [hAcard] at hidx
  refine ⟨A.index, ?_, ?_, ?_⟩
  · have : (ggC D.R.rS D.R.k (gOf p) : ℝ) =
        ((A.index * (nnC D.R.rS D.R.k (gOf p) * ukC D.R.k (gOf p)) : ℕ) : ℝ) := by
      rw [hidx]; rfl
    rw [this]; push_cast; ring
  · have hpos : 0 < Nat.card (A.map ρ) := Nat.card_pos
    rw [hAcard] at hpos
    exact_mod_cast hpos.ne'
  · rw [← hKv, hmeas, hAeq]

theorem measB_of (hH : HaarIdx) (hR : RedIdx) (u : D.what₂.Word) (p : TypX X) (hT : StTop X p)
    (hK : StK X p) (hRed : StRed X p) (hIm : StImB X u p) : StMeasB X u p := by
  obtain ⟨K, hKv, -, hKc, hKgo⟩ := hK
  obtain ⟨ρ, hρs, hρk⟩ := hRed K hKv
  haveI := finite_GL X p
  obtain ⟨B, hBeq, hBker, hBcard⟩ := hIm K hKv ρ hρs hρk
  haveI : (muP X p).IsHaarMeasure := X.measG_norm.2.2.2.1 p.1
  have hKgK : KgX X p ⊆ (K : Set (HAp X p)) := hKv ▸ kg_sub X p
  obtain ⟨hBo, hBK, hmeas, hidx⟩ :=
    measOfRed hH hR hT (muP X p) K ρ hρs (KgX X p) hKgo hKgK hρk B hBker
  rw [hBcard] at hidx
  refine ⟨B.index, ?_, ?_, ?_, ?_, ?_⟩
  · have : (ggC D.R.rS D.R.k (gOf p) : ℝ) =
        ((B.index * (glkC D.R.k (gOf p) * nnC D.R.rS D.R.k (gOf p)) : ℕ) : ℝ) := by
      rw [hidx]; rfl
    rw [this]; push_cast; ring
  · have hpos : 0 < Nat.card (B.map ρ) := Nat.card_pos
    rw [hBcard] at hpos
    exact_mod_cast hpos.ne'
  · rw [← hKv, hmeas, hBeq]
  · rw [← hBeq]
    exact hBo.measure_ne_zero _ ⟨_, 1, B.one_mem, rfl⟩
  · rw [← hBeq]
    exact (measure_mono hBK).trans_lt hKc.measure_lt_top |>.ne

end MassDataIdxSteps
end
end

section

noncomputable section

namespace MassDataIdxSteps

open MeasureTheory
open scoped ENNReal Pointwise

theorem redIdx : RedIdx := by
  intro K Q _ _ _ ρ hρ A hA
  have h1 : A.index = (A.map ρ).index := by
    rw [← Subgroup.index_comap_of_surjective (A.map ρ) hρ, Subgroup.comap_map_eq, sup_eq_left.mpr hA]
  rw [h1, Subgroup.index_mul_card]

theorem haarIdx : HaarIdx := by
  intro G _ _ _ _ _ μ _ K A hAK hA hne
  have hcard : Nat.card (K ⧸ A.subgroupOf K) = A.relIndex K := rfl
  have : Finite (K ⧸ A.subgroupOf K) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hne)
  let := Fintype.ofFinite (K ⧸ A.subgroupOf K)
  let r : K ⧸ A.subgroupOf K → G := fun q => ((Quotient.out q : K) : G)
  have hr : ∀ q, r q ∈ K := fun q => (Quotient.out q).2
  have hmk : ∀ q, (QuotientGroup.mk (Quotient.out q) : K ⧸ A.subgroupOf K) = q :=
    fun q => QuotientGroup.out_eq' q
  have hunion : (K : Set G) = ⋃ q, r q • (A : Set G) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_smul_set, smul_eq_mul, SetLike.mem_coe]
    constructor
    · intro hx
      set q : K ⧸ A.subgroupOf K := QuotientGroup.mk ⟨x, hx⟩
      have hq : (Quotient.out q)⁻¹ * ⟨x, hx⟩ ∈ A.subgroupOf K := by
        rw [← QuotientGroup.eq, hmk]
      rw [Subgroup.mem_subgroupOf] at hq
      exact ⟨q, (r q)⁻¹ * x, by simpa [r] using hq, by simp⟩
    · rintro ⟨q, a, ha, rfl⟩
      exact K.mul_mem (hr q) (hAK ha)
  have hdisj : Pairwise (Function.onFun Disjoint fun q => r q • (A : Set G)) := by
    intro q q' hqq'
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    apply hqq'
    rw [← hmk q, ← hmk q', QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp only [smul_eq_mul] at hab
    have key : (r q)⁻¹ * r q' = a * b⁻¹ := by
      calc (r q)⁻¹ * r q' = (r q)⁻¹ * (r q' * b) * b⁻¹ := by group
        _ = (r q)⁻¹ * (r q * a) * b⁻¹ := by rw [hab]
        _ = a * b⁻¹ := by group
    have : (((Quotient.out q)⁻¹ * Quotient.out q' : K) : G) = (r q)⁻¹ * r q' := rfl
    rw [this, key]
    exact A.mul_mem ha (A.inv_mem hb)
  have hmeas : ∀ q, MeasurableSet (r q • (A : Set G)) := fun q => (hA.smul (r q)).measurableSet
  rw [hunion, measure_iUnion hdisj hmeas, tsum_fintype]
  simp only [measure_smul]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card, hcard]

end MassDataIdxSteps
end
end
