module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairCommonUnipotentStabiliserSummary
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummary
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExistsHasLeadingCoeffOfMemSpanBelow
public import Formalism.HyperbolicPlaceProducts.SecondLevelArithmeticNorm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLocalizedModuleSubtype
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MirabolicFunctionEqInducedDerivativeAddTail
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MirabolicInductionPhiPlusInductionFromBlockUni
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormFlagLatticesNearUnderStabiliser
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormIdealDivisibility
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivedModuleCoefficientsAndStableFlows
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle121
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle122
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAlgebrasMaxCompactAndLeviInter
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients

@[expose] public section

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermFramePairCommonUnipotentStabiliser_summary : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), (∀ s : V ≃ₗ[K] V, s ∈ N.R ↔ N.F.InN (s : V →ₗ[K] V) ∧ N.F'.InN (s : V →ₗ[K] V)) ∧ (∀ s ∈ N.R, ∀ y ∈ uPerp N.F N.F', s y - y ∈ II N.F N.F') ∧ (∀ s ∈ N.R, ∀ t ∈ N.R1, s * t * s⁻¹ ∈ N.R1) ∧ (∀ s ∈ N.R, ∀ t ∈ N.ZI, s * t * s⁻¹ ∈ N.ZI) ∧ ∀ s ∈ N.R, ((s : V →ₗ[K] V) - 1) ^ (2 * r + 1) = 0 := by
  first | exact @GlobalTheory.UnipStab.common_unipotent_stabiliser | exact GlobalTheory.UnipStab.common_unipotent_stabiliser | (intros; apply GlobalTheory.UnipStab.common_unipotent_stabiliser <;> assumption)
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open Formalism.HermitianLatticeCounting.P

noncomputable section

namespace GlobalTheory.DegCnt.ReflectionLatticeMembership

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ} (N : NF H r)

def Sg : Submodule K V := N.F.X ⊔ N.F'.X ⊔ N.Ist

theorem line_le {A : Submodule (𝓞 K) K} {v : V} {S : Submodule K V} (hv : v ∈ S) :
    line A v ≤ rs (𝓞 K) S := by
  rintro _ ⟨a, -, rfl⟩
  simpa using S.smul_mem a hv

theorem normalForm_baseLattice_le_dualSpan_sup_line : N.P0 ≤ rs (𝓞 K) (Sg N) ⊔ line 1 N.F.z := by
  unfold NF.P0
  refine sup_le (sup_le (sup_le ?_ ?_) le_sup_right) ?_
  · refine iSup_le fun a => le_sup_of_le_left (line_le ?_)
    exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨a, a.isLt, rfl⟩))
  · refine iSup_le fun a => iSup_le fun _ => le_sup_of_le_left (line_le ?_)
    exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span ⟨a, a.isLt, rfl⟩))
  · refine iSup_le fun a => iSup_le fun h => le_sup_of_le_left (line_le ?_)
    exact Submodule.mem_sup_right (Submodule.subset_span ⟨a, h, rfl⟩)

theorem Sg_le_Pi [FiniteDimensional K V] : Sg N ≤ N.Pi := by
  rw [NFGeom.Pi_eq]
  exact sup_le (sup_le (le_sup_of_le_left (le_sup_left.trans le_sup_left))
    (le_sup_of_le_left (le_sup_right.trans le_sup_left))) le_sup_right

theorem z_mem_Pi [FiniteDimensional K V] : N.F.z ∈ N.Pi := by
  rw [NFGeom.Pi_eq]
  exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span (by simp)))

theorem eq_zero [FiniteDimensional K V] {q : V} (hS : q ∈ Sg N) (hW : q ∈ N.Wn) : q = 0 := by
  rw [NFGeom.Wn_eq N] at hW
  obtain ⟨w, hw, m, hm, rfl⟩ := Submodule.mem_sup.1 hW
  obtain ⟨κ, rfl⟩ := Submodule.mem_span_singleton.1 hm
  have hwP : w ∈ N.Pi := by
    have e : w = (w + κ • N.F.z) - κ • N.F.z := by abel
    rw [e]
    exact Submodule.sub_mem _ (Sg_le_Pi N hS) (Submodule.smul_mem _ _ (z_mem_Pi N))
  have hw0 : w = 0 := NFGeom.Wt_inf_Pi N hw hwP
  subst hw0
  rw [zero_add] at hS ⊢
  have h1 : H.B N.F.z (κ • N.F.z) = 0 := (mem_perp_iff H (Sg N) _).1 (NFGeom.z_mem_Wn N) _ hS
  have h2 : H.B (κ • N.F.z) N.F.z = 0 := B_swap0 H h1
  have h3 : H.B N.F.z N.F.z = -N.F.T := N.F.zz
  rw [map_smul, LinearMap.smul_apply, h3, smul_eq_mul, mul_neg, neg_eq_zero] at h2
  rcases mul_eq_zero.1 h2 with h | h
  · simp [h]
  · exact absurd h N.F.hT

end GlobalTheory.DegCnt.ReflectionLatticeMembership

namespace GlobalTheory.DegCnt

theorem NF.ref_mem_of_mem_Wn : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : GlobalTheory.DegCnt.NF H r) (L : Submodule (𝓞 K) V), N.F.z ∈ L → ∀ v ∈ N.Ref L, v ∈ N.Wn → v ∈ L := by
  intro K V _ _ _ _ _ _ _ _ H _ r N L hz v hv hvW
  obtain ⟨p, hp, l, hl, rfl⟩ := Submodule.mem_sup.1 hv
  obtain ⟨q, hq, m, hm, rfl⟩ := Submodule.mem_sup.1 (ReflectionLatticeMembership.normalForm_baseLattice_le_dualSpan_sup_line N hp)
  obtain ⟨γ, hγ, rfl⟩ := hm
  obtain ⟨x, rfl⟩ := Submodule.mem_one.1 hγ
  have hm' : ((LinearMap.toSpanSingleton K V N.F.z).restrictScalars (𝓞 K)) (algebraMap (𝓞 K) K x) = x • N.F.z := by
    simp [algebraMap_smul]
  rw [hm'] at hvW ⊢
  have hmW : x • N.F.z ∈ N.Wn := by
    rw [← algebraMap_smul K x N.F.z]
    exact N.Wn.smul_mem _ (NFGeom.z_mem_Wn N)
  have hlW : l ∈ N.Wn := hl.2
  have hq0 : q = 0 := ReflectionLatticeMembership.eq_zero N hq (by
    have h := N.Wn.sub_mem (N.Wn.sub_mem hvW hlW) hmW
    convert h using 1
    abel)
  subst hq0
  rw [zero_add]
  exact L.add_mem (L.smul_mem x hz) hl.1

end GlobalTheory.DegCnt
end
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt

theorem count_index_fg {K Q : Type} [Field K] [NumberField K] [AddCommGroup Q] [Module K Q]
    [Module (𝓞 K) Q] [IsScalarTower (𝓞 K) K Q] [FiniteDimensional K Q] (M : Submodule (𝓞 K) Q) (hM : M.FG)
    (S : Submodule K Q) (hS : M ≤ S.restrictScalars (𝓞 K)) (k : ℕ) (hk : Module.finrank K S ≤ k)
    (x : ℕ) (hx : 1 ≤ x) :
    {N : Submodule (𝓞 K) M | N.toAddSubgroup.index = x}.Finite ∧
      (({N : Submodule (𝓞 K) M | N.toAddSubgroup.index = x}.ncard : ℕ) : ℝ) ≤ (x : ℝ) ^ ((k : ℝ) + cf K) := by
  have : Module.Finite (𝓞 K) M := Module.Finite.iff_fg.2 hM
  have : Module.IsTorsionFree (𝓞 K) Q := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K Q
  have : Module.FinitePresentation (𝓞 K) M := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) M := Module.Flat.projective_of_finitePresentation
  obtain ⟨h1, h2⟩ := Formalism.SLP.Final.submoduleIndexCountO K M x hx
  refine ⟨h1, ?_⟩
  have hr : Module.finrank (𝓞 K) M ≤ k := by
    refine le_trans ?_ hk
    apply Module.finrank_le_of_rank_le
    have h3 : Module.rank (𝓞 K) M ≤ Module.rank (𝓞 K) S := Submodule.rank_mono hS
    have h5 : Module.rank K S = Module.rank (𝓞 K) S := IsLocalization.rank_eq K (nonZeroDivisors (𝓞 K)) le_rfl
    rw [Module.finrank_eq_rank, h5]
    exact h3
  have hn : 1 ≤ Module.finrank ℚ K := Module.finrank_pos
  have hx1 : (1:ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0:ℝ) < x := by linarith
  have h4 := Formalism.SLP.Final.omegaPow (Module.finrank ℚ K) x hn hx
  have h3 : (({N : Submodule (𝓞 K) M | N.toAddSubgroup.index = x}.ncard : ℕ) : ℝ) ≤
      ((Module.finrank ℚ K : ℕ) : ℝ) ^ (Nat.primeFactorsList x).length *
        (x : ℝ) ^ Module.finrank (𝓞 K) M := by exact_mod_cast h2
  have hr' : (Module.finrank (𝓞 K) M : ℝ) ≤ k := by exact_mod_cast hr
  calc _ ≤ _ := h3
    _ ≤ (x : ℝ) ^ Real.logb 2 (Module.finrank ℚ K) * (x : ℝ) ^ Module.finrank (𝓞 K) M :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = (x : ℝ) ^ ((Module.finrank (𝓞 K) M : ℝ) + Real.logb 2 (Module.finrank ℚ K)) := by
        rw [Real.rpow_add hx0, Real.rpow_natCast, mul_comm]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by unfold cf; linarith)

theorem count_index_latMod {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] (W I : Submodule K V)
    (La : Submodule (𝓞 K) V) (h : IsLatMod La (W ⊔ I) I) (x : ℕ) (hx : 1 ≤ x) :
    ((({Th : Submodule (𝓞 K) V | rs (𝓞 K) I ≤ Th ∧ Th ≤ La ∧ idx La Th = x}).encard : ℕ∞) : ℝ≥0∞) ≤
      ENNReal.ofReal ((x : ℝ) ^ ((Module.finrank K W : ℝ) + cf K)) := by
  obtain ⟨⟨N, hN, hLa⟩, hsp⟩ := h
  let q : V →ₗ[𝓞 K] (V ⧸ I) := I.mkQ.restrictScalars (𝓞 K)
  have hker : LinearMap.ker q = rs (𝓞 K) I := by
    ext v; simp [q]
  have hM : (La.map q).FG := by
    have : (rs (𝓞 K) I).map q = ⊥ := by
      rw [← hker]; exact LinearMap.le_ker_iff_map.1 le_rfl
    rw [hLa, Submodule.map_sup, this, sup_bot_eq]
    exact hN.map q
  have hS : La.map q ≤ (W.map I.mkQ).restrictScalars (𝓞 K) := by
    rintro _ ⟨v, hv, rfl⟩
    have : v ∈ W ⊔ I := hsp ▸ Submodule.subset_span hv
    obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.1 this
    refine ⟨w, hw, ?_⟩
    have : I.mkQ u = 0 := by simpa using hu
    change I.mkQ w = I.mkQ (w + u)
    rw [map_add (f := _), this, add_zero]
  obtain ⟨h1, h2⟩ := count_index_fg (La.map q) hM (W.map I.mkQ) hS _ (Submodule.finrank_map_le _ _) x hx
  have hle : {Th : Submodule (𝓞 K) V | rs (𝓞 K) I ≤ Th ∧ Th ≤ La ∧ idx La Th = x}.encard ≤
      {N : Submodule (𝓞 K) (La.map q) | N.toAddSubgroup.index = x}.encard := by
    refine Set.encard_le_encard_of_injOn (f := fun Th => (Th.map q).comap (La.map q).subtype) ?_ ?_
    · rintro Th ⟨hI, hL, hi⟩
      have e : (Th.map q).comap q = Th := Submodule.comap_map_eq_self (hker ▸ hI)
      have e2 : idx La ((Th.map q).comap q) = idx (La.map q) (Th.map q) :=
        AddSubgroup.relIndex_comap (Th.map q).toAddSubgroup q.toAddMonoidHom La.toAddSubgroup
      rw [e, hi] at e2
      exact e2.symm
    · rintro Th ⟨hI, hL, -⟩ Th' ⟨hI', hL', -⟩ he
      have he2 : Th.map q = Th'.map q := by
        have := congrArg (Submodule.map (La.map q).subtype) he
        simp only [Submodule.map_comap_subtype] at this
        rwa [inf_eq_right.2 (Submodule.map_mono hL), inf_eq_right.2 (Submodule.map_mono hL')] at this
      rw [← Submodule.comap_map_eq_self (f := q) (p := Th) (hker ▸ hI), he2,
        Submodule.comap_map_eq_self (hker ▸ hI')]
  refine le_trans (ENat.toENNReal_le.2 hle) ?_
  rw [← h1.cast_ncard_eq, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal h2

theorem count_sublattices_definite : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (La : Submodule (𝓞 K) V) (i : ℕ), 1 ≤ i → IsLatMod La (wSp N.F N.F') (II N.F N.F') → ((({Th : Submodule (𝓞 K) V | rs (𝓞 K) (II N.F N.F') ≤ Th ∧ Th ≤ La ∧ idx La Th = i}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((i : ℝ) ^ ((Module.finrank K N.Wt : ℝ) + cf K)) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N La i hi h
  have hw := (GlobalTheory.DegCnt.NF.geometry K V H hK r N).2.2.2.2.2.2.1
  rw [hw] at h
  exact count_index_latMod N.Wt _ La h i hi

end GlobalTheory.DegCnt
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open scoped nonZeroDivisors

namespace GlobalTheory.DegCnt.IdealPow

variable {K : Type} [Field K] [NumberField K] {𝔡 : Ideal (𝓞 K)}

theorem ipow_zero (𝔡 : Ideal (𝓞 K)) : ipow 𝔡 0 = 1 := by
  simp [ipow]

theorem ipow_mul (h : 𝔡 ≠ ⊥) (m n : ℤ) : ipow 𝔡 m * ipow 𝔡 n = ipow 𝔡 (m + n) := by
  have h0 : (𝔡 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h
  unfold ipow
  rw [zpow_add₀ h0, FractionalIdeal.coe_mul]

theorem mul_mem (h : 𝔡 ≠ ⊥) {m n k : ℤ} (hk : m + n = k) {x y : K} (hx : x ∈ ipow 𝔡 m) (hy : y ∈ ipow 𝔡 n) :
    x * y ∈ ipow 𝔡 k := by
  rw [← hk, ← ipow_mul h]
  exact Submodule.mul_mem_mul hx hy

theorem mul_mem_one (h : 𝔡 ≠ ⊥) {m n : ℤ} (hk : m + n = 0) {x y : K} (hx : x ∈ ipow 𝔡 m) (hy : y ∈ ipow 𝔡 n) :
    x * y ∈ (1 : Submodule (𝓞 K) K) := by
  rw [← ipow_zero 𝔡]
  exact mul_mem h hk hx hy

theorem pow_mem (h : 𝔡 ≠ ⊥) {m : ℤ} {x : K} (hx : x ∈ ipow 𝔡 m) (s : ℕ) : x ^ s ∈ ipow 𝔡 (s * m) := by
  induction s with
  | zero => simp only [pow_zero, Nat.cast_zero, zero_mul, ipow_zero]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
  | succ s ih => rw [pow_succ]; exact mul_mem h (by push_cast; ring) ih hx

theorem mem_of_forall (h : 𝔡 ≠ ⊥) {m n : ℤ} (hk : m + n = 0) {x : K}
    (hx : ∀ y ∈ ipow 𝔡 n, x * y ∈ (1 : Submodule (𝓞 K) K)) : x ∈ ipow 𝔡 m := by
  have h1 : (1 : K) ∈ ipow 𝔡 n * ipow 𝔡 m := by
    rw [ipow_mul h, add_comm, hk, ipow_zero]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
  have h2 : ∀ z ∈ ipow 𝔡 n * ipow 𝔡 m, x * z ∈ ipow 𝔡 m := by
    intro z hz
    refine Submodule.mul_induction_on hz (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · obtain ⟨c, hc⟩ := Submodule.mem_one.1 (hx a ha)
      rw [← mul_assoc, ← hc, ← Algebra.smul_def]
      exact Submodule.smul_mem _ c hb
    · rw [mul_add]; exact add_mem ha hb
  simpa using h2 1 h1

theorem prod_ipow (h : 𝔡 ≠ ⊥) {ι : Type} (s : Finset ι) (n : ι → ℤ) :
    ∏ i ∈ s, ipow 𝔡 (n i) = ipow 𝔡 (∑ i ∈ s, n i) := by
  induction s using Finset.induction_on with
  | empty => simp [ipow_zero]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, ipow_mul h]

theorem ipow_sum_le (h : 𝔡 ≠ ⊥) {ι : Type} [Fintype ι] (n : ι → ℤ) (J : Submodule (𝓞 K) K)
    (hJ : ∀ α : ι → K, (∀ i, α i ∈ ipow 𝔡 (n i)) → ∏ i, α i ∈ J) : ipow 𝔡 (∑ i, n i) ≤ J := by
  rw [← prod_ipow h]
  have : ∏ i, ipow 𝔡 (n i) = ∏ i, Submodule.span (𝓞 K) (ipow 𝔡 (n i) : Set K) := by simp
  rw [this, Submodule.prod_span, Submodule.span_le]
  intro x hx
  obtain ⟨α, hα, rfl⟩ := (Set.mem_fintype_prod _ _).1 hx
  exact hJ α hα

variable [StarRing K]

theorem star_mem_nat (h : 𝔡 ≠ ⊥) (hs : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) (n : ℕ) {x : K}
    (hx : x ∈ ipow 𝔡 n) : star x ∈ ipow 𝔡 n := by
  induction n generalizing x with
  | zero =>
    rw [Nat.cast_zero, ipow_zero] at hx ⊢
    exact GlobalTheory.UnimodQuot.star_mem_one hx
  | succ n ih =>
    rw [Nat.cast_succ, ← ipow_mul h] at hx ⊢
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · rw [star_mul']
      refine Submodule.mul_mem_mul (ih ha) ?_
      simp only [ipow, zpow_one, FractionalIdeal.mem_coe, FractionalIdeal.mem_coeIdeal] at hb ⊢
      obtain ⟨y, hy, rfl⟩ := hb
      exact hs y hy
    · rw [star_add]; exact add_mem ha hb

theorem star_mem (h : 𝔡 ≠ ⊥) (hs : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) {n : ℤ} {x : K}
    (hx : x ∈ ipow 𝔡 n) : star x ∈ ipow 𝔡 n := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · exact star_mem_nat h hs m hx
  · refine mem_of_forall h (neg_add_cancel _) fun y hy => ?_
    have := GlobalTheory.UnimodQuot.star_mem_one (mul_mem_one h (neg_add_cancel _) hx (star_mem_nat h hs m hy))
    rwa [star_mul', star_star] at this

end GlobalTheory.DegCnt.IdealPow
end

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

theorem _root_.GlobalTheory.T.mirabolic_function_eq_induced_derivative_add_tail : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) , ψ ≠ 1 → ∀ (m : ℕ) (F : Gn g (m + 1) → ℂ), 1 ≤ m → IsMirClass F → ∀ p : Gn g (m + 1), InMir (p : Mt g (m + 1)) → F p = indR ψ m (m + 1) (der ψ m F) p + indV ψ m (tail ψ m F) p := by
  first | exact @GlobalTheory.GLm.MirStep.mir_step | exact GlobalTheory.GLm.MirStep.mir_step | (intros; apply GlobalTheory.GLm.MirStep.mir_step <;> assumption)
end

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

theorem _root_.GlobalTheory.T.mirabolicInductionPhiPlus_inductionFromBlockUni : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (i m : ℕ) (ρ : Gn g i → ℂ), i < m → ∀ x : Gn g (m + 1), InMir (x : Mt g (m + 1)) → indV ψ m (indR ψ i m ρ) x = indR ψ i (m + 1) ρ x := by
  first | exact @GlobalTheory.GLm.indV_indR | exact GlobalTheory.GLm.indV_indR | (intros; apply GlobalTheory.GLm.indV_indR <;> assumption)
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.normalForm_flag_lattices_near_under_stabiliser : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → ∃ s ∈ N.Rs, (∀ y ∈ II N.F N.F' ⊔ Submodule.span K {N.F.z} ⊔ N.Ist, s y = y) ∧ ∀ Λ' : Submodule (𝓞 K) V, Λ' = s • Λ → 𝔠 ^ (2 * r + 2) • (N.P0 ⊓ rs (𝓞 K) (N.F.Xa N.j)) ≤ Λ' ∧ 𝔠 ^ (2 * r + 2) • (N.P0 ⊓ rs (𝓞 K) (N.F'.Xa N.j)) ≤ Λ' ∧ 𝔠 ^ (2 * r + 2) • (Λ' ⊓ rs (𝓞 K) (N.F.Xa N.j)) ≤ N.P0 ∧ 𝔠 ^ (2 * r + 2) • (Λ' ⊓ rs (𝓞 K) (N.F'.Xa N.j)) ≤ N.P0 := by
  first | exact @GlobalTheory.DegCnt.PosJ.main | exact GlobalTheory.DegCnt.PosJ.main | (intros; apply GlobalTheory.DegCnt.PosJ.main <;> assumption)
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.normal_form_ideal_divisibility : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → ∃ s ∈ N.Rs, (∀ y ∈ N.F.Xa N.j ⊔ N.F'.Xa N.j, s y = y) ∧ ∀ Λ' : Submodule (𝓞 K) V, Λ' = s • Λ → 𝔠 ^ 2 • (N.P0 ⊓ rs (𝓞 K) (II N.F N.F')) ≤ Λ' ∧ Λ' ⊓ rs (𝓞 K) (II N.F N.F') ≤ N.P0 ∧ 𝔠 • line 1 N.F.z ≤ Λ' := by
  first | exact @GlobalTheory.DegCnt.PosIso.normal_position | exact GlobalTheory.DegCnt.PosIso.normal_position | (intros; apply GlobalTheory.DegCnt.PosIso.normal_position <;> assumption)
end

section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

theorem _root_.GlobalTheory.T.derivedModule_coefficients_and_stable_flows : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V), IsURepOn (UJset ε) σ → IsDer ε σ V E → (∀ (w : List (Fin n × Fin n)) (v : V) (y : H), ∀ g ∈ UJset ε, Eword ε w (fun x => ⟪y, σ x (v : H)⟫_ℂ) g = ⟪y, σ g (ew E w v : V)⟫_ℂ) ∧ (∀ W : Submodule ℂ V, FiniteDimensional ℂ W → (KStable ε E W ↔ IsKStableOn ε σ (W.map V.subtype))) ∧ ∀ (μ : Fin n → ℝ) (v : V), IsWeight E μ v ↔ IsWtOn (Kset ε) σ μ (v : H) := by
  first | exact @GlobalTheory.Jet.Coef.coef_flow | exact GlobalTheory.Jet.Coef.coef_flow | (intros; apply GlobalTheory.Jet.Coef.coef_flow <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.unitarySphereVolumeProduct_ratio_and_inv_bounds : (∀ q j : ℕ, j ≤ q → Real.log (sphV q / sphV (q - j)) ≤ 3.49 * j) ∧ ∀ J : ℕ, 0 < sphV J ∧ (sphV J)⁻¹ ≤ (J : ℝ) ^ (J * (J - 1) / 2) := by
  first | exact @GlobalTheory.sphV_ratio_and_inv_bounds | exact GlobalTheory.sphV_ratio_and_inv_bounds | (intros; apply GlobalTheory.sphV_ratio_and_inv_bounds <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.one_le_dedekindZetaRealValue_and_le_zeta_pow : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ), 2 ≤ l → 1 ≤ zetaE E l ∧ zetaE E l ≤ (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ l) ^ Module.finrank ℚ E := by
  first | exact @GlobalTheory.DedekindZetaBound.one_le_zetaE_and_le | exact GlobalTheory.DedekindZetaBound.one_le_zetaE_and_le | (intros; apply GlobalTheory.DedekindZetaBound.one_le_zetaE_and_le <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.exists_algebras_maxCompact_and_levi_inter : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ (p q : ℕ), (univ.filter fun a => ε a = true).card = p → (univ.filter fun a => ε a = false).card = q → (∃ (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (E : Fin (p ^ 2 + q ^ 2) → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) ∧ (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) ∧ (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) ∧ maxK ε = {g | uMat g - 1 ∈ A}) ∧ ∃ (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (E : Fin ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2) → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) ∧ (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) ∧ (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) ∧ maxK ε ∩ flagM ε W = {g | uMat g - 1 ∈ A} := by
  first | exact @GlobalTheory.FlagMeas.CompactAlg.compact_algebras | exact GlobalTheory.FlagMeas.CompactAlg.compact_algebras | (intros; apply GlobalTheory.FlagMeas.CompactAlg.compact_algebras <;> assumption)
end
