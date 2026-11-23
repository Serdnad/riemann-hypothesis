module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle219
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle238
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle204
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle143
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IdxSupRight
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLocalizedModuleSubtype
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeOfLatMod
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapConjLebesgueCommonStabilizerNormalForm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormFlagZeroMiddleInverseMinorOrthogonal
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerHaarUnimodularNormal
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle239
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle242
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianMovePreservesFrameLatticeLevels
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordinateLatticeUniqueTermAlmostAllPlaces
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle241
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients

@[expose] public section

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors

namespace GlobalTheory.DegCnt

theorem mem_ipow_one_iff_exists {K : Type} [Field K] [NumberField K] (𝔞 : Ideal (𝓞 K)) (t : K) :
    t ∈ ipow 𝔞 1 ↔ ∃ a ∈ 𝔞, algebraMap (𝓞 K) K a = t := by
  unfold ipow
  rw [zpow_one]
  exact FractionalIdeal.mem_coeIdeal _

theorem exists_ideal_coeff {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L M : Submodule (𝓞 K) V) (z : V) (hML : M ≤ L)
    (hidx : idx L M ≠ 0) (hz : ∀ t : K, t • z ∈ L ↔ t ∈ (1 : Submodule (𝓞 K) K)) :
    ∃ 𝔞 : Ideal (𝓞 K), 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ idx L M ∧ ∀ t : K, t ∈ ipow 𝔞 1 ↔ t • z ∈ M := by
  let f : 𝓞 K →ₗ[𝓞 K] V := LinearMap.toSpanSingleton (𝓞 K) V z
  have hf : ∀ a : 𝓞 K, f a = (algebraMap (𝓞 K) K a) • z := fun a => by
    simp only [f, LinearMap.toSpanSingleton_apply, algebraMap_smul]
  let 𝔞 : Ideal (𝓞 K) := M.comap f
  have hr : f.toAddMonoidHom.range ≤ L.toAddSubgroup := by
    rintro _ ⟨a, rfl⟩
    show f a ∈ L
    rw [hf, hz]
    exact Submodule.mem_one.2 ⟨a, rfl⟩
  have hN : Ideal.absNorm 𝔞 = M.toAddSubgroup.relIndex f.toAddMonoidHom.range := by
    rw [← AddSubgroup.index_comap, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  have hle : Ideal.absNorm 𝔞 ≤ idx L M := by
    rw [hN]; exact AddSubgroup.relIndex_le_of_le_right hr hidx
  have hne : Ideal.absNorm 𝔞 ≠ 0 := by
    rw [hN]
    exact fun h => hidx (AddSubgroup.relIndex_eq_zero_of_le_right hr h)
  refine ⟨𝔞, fun h => hne (by rw [h, Ideal.absNorm_bot]), hle, fun t => ?_⟩
  rw [mem_ipow_one_iff_exists]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [← hf]; exact ha
  · intro ht
    obtain ⟨a, rfl⟩ := Submodule.mem_one.1 ((hz t).1 (hML ht))
    refine ⟨a, ?_, rfl⟩
    show f a ∈ M
    rw [hf]; exact ht

theorem c_eq_quot_ideals : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∃ 𝔞 𝔞' : Ideal (𝓞 K), 𝔞 ≠ ⊥ ∧ 𝔞' ≠ ⊥ ∧ (Ideal.absNorm 𝔞 : ℝ) ≤ N.Del ∧ (Ideal.absNorm 𝔞' : ℝ) ≤ N.Del ∧ ∀ t : K, t * N.c ∈ ipow 𝔞 1 ↔ t ∈ ipow 𝔞' 1 := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ
  obtain ⟨-, -, hz, hz', -⟩ := GlobalTheory.T.hermFramePair_innerLattices_unimodular_primitive K V H hK r N g Λ hg hΛ
  obtain ⟨hb, -, hD, h1⟩ := GlobalTheory.T.normal_form_terminal_determinant K V H hK r N g Λ hg hΛ
  obtain ⟨hi, hi', hle, -⟩ := GlobalTheory.T.flagPairInnerLattice_indices_and_generators K V H hK r N g Λ hg hΛ
  set i := idx (latL N.F N.F' Λ) (lamOne N.F N.F' Λ) with hidef
  have hi0 : i ≠ 0 := by
    intro h; rw [h] at hi; simp at hi; linarith
  have hB : cardB N.F N.F' Λ ≠ 0 := by
    intro h; rw [h] at hi; simp at hi; linarith
  have hiD : (i : ℝ) ≤ N.Del := by
    have hB1 : (1 : ℝ) ≤ cardB N.F N.F' Λ := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hB
    have hb1 : (1 : ℝ) ≤ N.bI Λ := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hb
    have hb2 : (1 : ℝ) ≤ (N.bI Λ : ℝ) ^ 2 := one_le_pow₀ hb1
    have hi1 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    calc (i : ℝ) ≤ i * cardB N.F N.F' Λ := le_mul_of_one_le_right hi1 hB1
      _ = delBar N.F N.F' Λ := hi
      _ ≤ delBar N.F N.F' Λ * (N.bI Λ : ℝ) ^ 2 := le_mul_of_one_le_right (by linarith) hb2
      _ = N.Del := hD
  obtain ⟨𝔞, h0, hn, hm⟩ := exists_ideal_coeff _ _ N.F.z (hle.trans inf_le_left) hi0 hz
  obtain ⟨𝔞', h0', hn', hm'⟩ := exists_ideal_coeff _ _ N.F'.z (hle.trans inf_le_right) (hi' ▸ hi0) hz'
  refine ⟨𝔞, 𝔞', h0, h0', le_trans (by exact_mod_cast hn) hiD,
    le_trans (by exact_mod_cast hi' ▸ hn') hiD, fun t => ?_⟩
  have hzz : N.F'.z = N.c • N.F.z := N.same (Fin.last r) (by simpa using N.j_le)
  rw [hm, hm', hzz, mul_smul]

end GlobalTheory.DegCnt
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.PrimPerp

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]


omit [StarRing K] [FiniteDimensional K V] in
theorem equiv_of_gen {D M : Submodule (𝓞 K) V} {w : V} (hw : w ∈ D) (J : Ideal (𝓞 K))
    (h1 : ∀ a : 𝓞 K, a • w ∈ M ↔ a ∈ J) (h2 : ∀ y ∈ D, ∃ a : 𝓞 K, y - a • w ∈ M) :
    Nonempty ((↥D ⧸ M.comap D.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ J)) := by
  let φ : 𝓞 K →ₗ[𝓞 K] (↥D ⧸ M.comap D.subtype) :=
    (M.comap D.subtype).mkQ ∘ₗ LinearMap.toSpanSingleton (𝓞 K) D ⟨w, hw⟩
  have hs : Function.Surjective φ := by
    intro q
    obtain ⟨y, rfl⟩ := (M.comap D.subtype).mkQ_surjective q
    obtain ⟨a, ha⟩ := h2 y y.2
    exact ⟨a, ((Submodule.Quotient.eq (M.comap D.subtype)).2 (show y - a • (⟨w, hw⟩ : D) ∈ M.comap D.subtype from ha)).symm⟩
  have hk : LinearMap.ker φ = J := by
    ext a
    rw [LinearMap.mem_ker, ← h1]
    exact Submodule.Quotient.mk_eq_zero _
  exact ⟨(φ.quotKerEquivOfSurjective hs).symm.trans (Submodule.quotEquivOfEq _ _ hk)⟩

theorem perp_prim (H : HermSpace K V) [_root_.NumberField.IsTotallyComplex K] {M : Submodule (𝓞 K) V} {S I W : Submodule K V}
    (hIS : I ≤ S) (hrad : ∀ x ∈ S, (∀ y ∈ S, H.B x y = 0) ↔ x ∈ I) (hM : IsUnimodMod H M S I)
    {z : V} {T : ℕ} (hT : 1 ≤ T) (hz : H.B z z = -(T : K))
    (hp : ∀ t : K, t • z ∈ M ↔ t ∈ (1 : Submodule (𝓞 K) K))
    (hW : ∀ y, y ∈ W ↔ y ∈ S ∧ H.B y z = 0) :
    _root_.GlobalTheory.HermLat.del H (M ⊓ rs (𝓞 K) W) = (T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K ∧
      GenBy (dual H (M ⊓ rs (𝓞 K) W)) (M ⊓ rs (𝓞 K) W) 1 ∧ IsLatMod (M ⊓ rs (𝓞 K) W) W I ∧
      Nonempty ((↥(dual H (M ⊓ rs (𝓞 K) W)) ⧸ (M ⊓ rs (𝓞 K) W).comap (dual H (M ⊓ rs (𝓞 K) W)).subtype) ≃ₗ[𝓞 K]
        (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)})) := by
  obtain ⟨a, b⟩ := DelScale.le_of_latMod hM.1
  have hT0 : (T : K) ≠ 0 := by exact_mod_cast (by omega : T ≠ 0)
  have hzM : z ∈ M := by simpa using (hp 1).2 (Submodule.mem_one.2 ⟨1, map_one _⟩)
  have hzS : z ∈ S := b hzM
  have o1 : ∀ i ∈ I, ∀ y ∈ S, H.B i y = 0 := fun i hi => (hrad i (hIS hi)).2 hi
  have o2 : ∀ i ∈ I, ∀ y ∈ S, H.B y i = 0 := fun i hi y hy => by rw [← H.herm, o1 i hi y hy, star_zero]
  have hint : ∀ x ∈ M, ∀ y ∈ M, H.B x y ∈ (1 : Submodule (𝓞 K) K) := fun x hx =>
    ((mem_dual_iff H M x).1 (hM.2.symm ▸ hx)).2
  set U : Submodule K V := Submodule.span K {z} ⊔ I with hU
  have hmU : ∀ u, u ∈ U ↔ ∃ t : K, ∃ i ∈ I, u = t • z + i := fun u => by
    rw [hU, Submodule.mem_sup]
    constructor
    · rintro ⟨x, hx, i, hi, rfl⟩
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hx
      exact ⟨t, i, hi, rfl⟩
    · rintro ⟨t, i, hi, rfl⟩
      exact ⟨_, Submodule.mem_span_singleton.2 ⟨t, rfl⟩, i, hi, rfl⟩
  have hUS : U ≤ S := sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 hzS) hIS
  have hWU : S ⊓ perp H U = W := by
    ext y
    rw [hW, Submodule.mem_inf, mem_perp_iff]
    refine and_congr_right fun hy => ⟨fun h => h z ((hmU z).2 ⟨1, 0, I.zero_mem, by simp⟩), fun h x hx => ?_⟩
    obtain ⟨t, i, hi, rfl⟩ := (hmU x).1 hx
    simp [h, o2 i hi y hy]
  have hWS : W ≤ S := fun y hy => ((hW y).1 hy).1
  have hIW : I ≤ W := fun i hi => (hW i).2 ⟨hIS hi, o1 i hi z hzS⟩
  obtain ⟨k1, k2⟩ := Compl.key H hIS hrad hM (le_sup_right : I ≤ U) hUS
  obtain ⟨k3, -⟩ := Compl.key H hIS hrad hM hIW hWS
  rw [hWU] at k1 k2
  rw [k2] at k3
  rw [← hU] at k1 k3
  have hzU : (T : K)⁻¹ • z ∈ U := (hmU _).2 ⟨_, 0, I.zero_mem, (add_zero _).symm⟩
  have hd : (T : K)⁻¹ • z ∈ dual H (M ⊓ rs (𝓞 K) U) := by
    rw [mem_dual_iff, Compl.span_inf (hM.1.2 ▸ hUS)]
    refine ⟨hzU, fun x hx => ?_⟩
    obtain ⟨t, i, hi, rfl⟩ := (hmU x).1 hx.2
    have ht : t • z ∈ M := by simpa using M.sub_mem hx.1 (a hi)
    have e : H.B ((T : K)⁻¹ • z) (t • z + i) = - star t := by
      simp [hz, o2 i hi z hzS]
      field_simp
      try rfl
    rw [e]
    exact Submodule.neg_mem _ (UnimodQuot.star_mem_one ((hp t).1 ht))
  rw [k1] at hd
  obtain ⟨m, hm, w, hw, e⟩ := Submodule.mem_sup.1 hd.2
  have hw' : w ∈ W := hw
  have hwD : w ∈ dual H (M ⊓ rs (𝓞 K) W) := by
    rw [k3]
    exact ⟨hw, Submodule.mem_sup.2 ⟨-m, M.neg_mem hm, _, hzU, by rw [← e]; abel⟩⟩
  have h1 : ∀ c : 𝓞 K, c • w ∈ M ⊓ rs (𝓞 K) W ↔ c ∈ Ideal.span {(T : 𝓞 K)} := by
    intro c
    have e1 : c • w = (algebraMap (𝓞 K) K c * (T : K)⁻¹) • z - c • m := by
      rw [mul_smul, algebraMap_smul, ← e, smul_add]; abel
    rw [Submodule.mem_inf, and_iff_left (Submodule.smul_mem _ c hw), e1,
      M.sub_mem_iff_left (M.smul_mem c hm), hp, Submodule.mem_one, Ideal.mem_span_singleton']
    refine exists_congr fun d => ?_
    rw [eq_mul_inv_iff_mul_eq₀ hT0, ← map_natCast (algebraMap (𝓞 K) K), ← map_mul]
    exact (IsFractionRing.injective (𝓞 K) K).eq_iff
  have h2 : ∀ y ∈ dual H (M ⊓ rs (𝓞 K) W), ∃ c : 𝓞 K, y - c • w ∈ M ⊓ rs (𝓞 K) W := by
    intro y hy
    rw [k3] at hy
    obtain ⟨m', hm', u, hu, e'⟩ := Submodule.mem_sup.1 hy.2
    obtain ⟨t, i, hi, rfl⟩ := (hmU u).1 hu
    have h0 := ((hW y).1 hy.1).2
    obtain ⟨c, hc⟩ := Submodule.mem_one.1 (hint m' hm' z hzM)
    rw [← e'] at h0
    simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, hz, o1 i hi z hzS, smul_eq_mul, ← hc] at h0
    have ht : t = algebraMap (𝓞 K) K c * (T : K)⁻¹ := by
      field_simp
      linear_combination -h0
    refine ⟨c, ?_, Submodule.sub_mem _ hy.1 (Submodule.smul_mem _ c hw)⟩
    have : y - c • w = m' + c • m + i := by
      rw [← e', ht, mul_smul, algebraMap_smul, ← e, smul_add]; abel
    rw [this]
    exact M.add_mem (M.add_mem hm' (M.smul_mem c hm)) (a hi)
  have hle : M ⊓ rs (𝓞 K) W ≤ dual H (M ⊓ rs (𝓞 K) W) := by
    rw [k3]
    exact le_inf inf_le_right (inf_le_left.trans le_sup_left)
  obtain ⟨E⟩ := equiv_of_gen hwD _ h1 h2
  refine ⟨?_, ⟨{w}, by simp, ?_⟩, ⟨?_, Compl.span_inf (hM.1.2 ▸ hWS)⟩, ⟨E⟩⟩
  · have i1 : idx (M ⊓ rs (𝓞 K) W) (dual H (M ⊓ rs (𝓞 K) W)) = 1 := AddSubgroup.relIndex_eq_one.2 hle
    have i2 : idx (dual H (M ⊓ rs (𝓞 K) W)) (M ⊓ rs (𝓞 K) W) = T ^ (2 * Formalism.HermitianLatticesTheory.fDeg K) := by
      have : idx (dual H (M ⊓ rs (𝓞 K) W)) (M ⊓ rs (𝓞 K) W) = Nat.card (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)}) :=
        Nat.card_congr E.toEquiv
      rw [this, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_natCast, RingOfIntegers.rank,
        IsTotallyComplex.finrank, Formalism.HermitianLatticesTheory.fDeg, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
        IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
    rw [_root_.GlobalTheory.HermLat.del, gidx, i1, i2, mul_comm, pow_mul]
    simp
  · apply le_antisymm
    · intro y hy
      obtain ⟨c, hc⟩ := h2 y hy
      exact Submodule.mem_sup.2 ⟨_, hc, c • w, Submodule.smul_mem _ c (Submodule.subset_span (by simp)), by abel⟩
    · exact sup_le hle (Submodule.span_le.2 (by simpa using hwD))
  · obtain ⟨N, hN, rfl⟩ := hM.1.1
    refine ⟨N ⊓ rs (𝓞 K) W, hN.of_le inf_le_left, ?_⟩
    rw [sup_comm N, sup_inf_assoc_of_le N (show rs (𝓞 K) I ≤ rs (𝓞 K) W from hIW), sup_comm]

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → _root_.GlobalTheory.HermLat.del H (flagPairDefinitePartLattice N.F N.F' Λ) = N.NT ∧ _root_.GlobalTheory.HermLat.del H (flagPairDefinitePartLattice N.F' N.F Λ) = N.NT ∧ GenBy (dual H (flagPairDefinitePartLattice N.F N.F' Λ)) (flagPairDefinitePartLattice N.F N.F' Λ) 1 ∧ IsLatMod (flagPairDefinitePartLattice N.F N.F' Λ) (wSp N.F N.F') (II N.F N.F') ∧ IsLatMod (flagPairDefinitePartLattice N.F' N.F Λ) (wSp N.F N.F') (II N.F N.F') ∧ Nonempty ((↥(dual H (flagPairDefinitePartLattice N.F N.F' Λ)) ⧸ (flagPairDefinitePartLattice N.F N.F' Λ).comap (dual H (flagPairDefinitePartLattice N.F N.F' Λ)).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {(N.T : 𝓞 K)})) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ
  haveI := hK.1
  obtain ⟨hNF, -, -, -, -, -, -, hww, -, hT, -⟩ := GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
  obtain ⟨hL, hL', hp, hp', -⟩ := GlobalTheory.T.hermFramePair_innerLattices_unimodular_primitive K V H hK r N g Λ hg hΛ
  have hV := hNF.2.2.2.1
  have hc : N.c ≠ 0 := hNF.1.1
  have hzz : N.F'.z = N.c • N.F.z := N.same (Fin.last r) N.j_le
  have hzS : N.F.z ∈ uPerp N.F N.F' := by
    have := (hp 1).2 (Submodule.mem_one.2 ⟨1, map_one _⟩)
    rw [one_smul] at this
    exact this.1
  have hXV : N.F.X ⊔ N.F'.X ≤ V0 N.F N.F' := le_sup_left
  have hW : ∀ y, y ∈ wSp N.F N.F' ↔ y ∈ uPerp N.F N.F' ∧ H.B y N.F.z = 0 := by
    intro y
    rw [wSp, uPerp, mem_perp_iff, mem_perp_iff]
    refine ⟨fun h => ⟨fun x hx => h x (hXV hx), h _ (Submodule.mem_sup_right (Submodule.subset_span (by simp)))⟩,
      fun h x hx => ?_⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.1 hv
    simp [hzz, h.1 u hu, h.2]
  have hW' : ∀ y, y ∈ wSp N.F N.F' ↔ y ∈ uPerp N.F N.F' ∧ H.B y N.F'.z = 0 := by
    intro y
    rw [hW, hzz]
    simp [hc]
  have hIX : II N.F N.F' ≤ N.F.X ⊔ N.F'.X := inf_le_left.trans le_sup_left
  have hIS : II N.F N.F' ≤ uPerp N.F N.F' := fun i hi =>
    (mem_perp_iff H _ i).2 fun x hx => (hV i (hXV (hIX hi))).2 hi x (hXV hx)
  have hrad : ∀ x ∈ uPerp N.F N.F', (∀ y ∈ uPerp N.F N.F', H.B x y = 0) ↔ x ∈ II N.F N.F' := by
    intro x hx
    constructor
    · intro h
      have h1 : x ∈ N.F.X ⊔ N.F'.X := UnimodQuot.mem_of_perp_perp H _ fun y hy => by
        rw [← H.herm, h y hy, star_zero]
      exact (hV x (hXV h1)).1 ((mem_perp_iff H _ x).1 ((hW x).2 ⟨hx, h _ hzS⟩))
    · intro h y hy
      rw [← H.herm, (mem_perp_iff H _ y).1 hy x (hIX h), star_zero]
  obtain ⟨a1, a2, a3, a4⟩ := perp_prim H hIS hrad hL hT (N.hT ▸ N.F.zz) hp hW
  obtain ⟨b1, -, b3, -⟩ := perp_prim H hIS hrad hL' hT (N.hT' ▸ N.F'.zz) hp' hW'
  have e : flagPairDefinitePartLattice N.F' N.F Λ = latL N.F' N.F Λ ⊓ rs (𝓞 K) (wSp N.F N.F') := by rw [flagPairDefinitePartLattice, hww]
  rw [e]
  exact ⟨a1, b1, a2, a3, b3, a4⟩

end GlobalTheory.DegCnt.PrimPerp
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.StabNormal

variable {k r : ℕ}

theorem xstJ_self : XstJ k r r = Xst k r := by
  unfold XstJ Xst
  congr 1
  ext v
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.1, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨a, a.2⟩, rfl⟩

theorem isNormal0_iff {β : Fin r → ℕ} {g : Mat k r} (z' : Fin (2 * r + k + 1) → ℂ) :
    IsNormal0 k r le_rfl β 1 (g *ᵥ z') z' g ↔ IsNormal k r β g := by
  constructor
  · rintro ⟨hg, -, -, -, -, hX, -, hB⟩
    refine ⟨hg, fun a => ?_, hB⟩
    rw [← xstJ_self]
    exact hX a a.2
  · rintro ⟨hg, hX, hB⟩
    refine ⟨hg, by simp, by simp, hB.1, fun a b hb => absurd b.2 (not_lt.2 hb), fun a _ => ?_,
      fun a ha => absurd a.2 (not_lt.2 ha), hB⟩
    rw [xstJ_self]
    exact hX a

theorem pTop_self (q : PTop k r r) : pTop k r r q = 1 := by
  have h1 : (fun a : Fin r => if h : r ≤ a.val then q.1 ⟨a, h⟩ else 0) = 0 :=
    funext fun a => dif_neg (not_le.2 a.2)
  have h2 : (fun p : UT r => if h : r ≤ p.1.1.val then q.2.1 ⟨p, h⟩ else 0) = 0 :=
    funext fun p => dif_neg (not_le.2 p.1.1.2)
  have h3 : (fun a : Fin r => if h : r ≤ a.val then q.2.2 ⟨a, h⟩ else 0) = 0 :=
    funext fun a => dif_neg (not_le.2 a.2)
  have hs : skewM (0 : UT r → ℂ) (0 : Fin r → ℝ) = 0 := by
    ext a b
    simp only [skewM]
    split_ifs <;> simp
  show pEl k r (fun a : Fin r => if h : r ≤ a.val then q.1 ⟨a, h⟩ else 0)
      (skewM (fun p : UT r => if h : r ≤ p.1.1.val then q.2.1 ⟨p, h⟩ else 0)
        (fun a : Fin r => if h : r ≤ a.val then q.2.2 ⟨a, h⟩ else 0)) = 1
  rw [h1, h2, h3, hs]
  exact Rad.pEl_zero

theorem rEl_self (β : Fin r → ℕ) (q : (UTin β → ℂ) × PTop k r r) : rEl k r r β q = uEmb k r (upperIn β q.1) := by
  show uEmb k r (upperIn β q.1) * pTop k r r q.2 = _
  rw [pTop_self, mul_one]

theorem range_rEl (β : Fin r → ℕ) :
    Set.range (rEl k r r β) = Set.range fun x : UTin β → ℂ => uEmb k r (upperIn β x) := by
  ext m
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q.1, (rEl_self β q).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨(x, 0), rEl_self β (x, 0)⟩

theorem volume_pTop : (volume : Measure (PTop k r r)) Set.univ = 1 := by
  haveI : IsEmpty {a : Fin r // r ≤ a.val} := ⟨fun a => absurd a.2 (not_le.2 a.1.2)⟩
  haveI : IsEmpty {p : UT r // r ≤ p.1.1.val} := ⟨fun p => absurd p.2 (not_le.2 p.1.1.1.2)⟩
  rw [← Set.univ_prod_univ, Measure.volume_eq_prod, Measure.prod_prod, ← Set.univ_prod_univ,
    Measure.volume_eq_prod, Measure.prod_prod]
  simp [volume_pi, Measure.pi_univ]

theorem lebesgueCommonStabilizerNormalForm_full_eq (β : Fin r → ℕ) : lebR0 k r r β = lebR k r β := by
  have hc : Continuous fun x : UTin β → ℂ => Matrix.of.symm (uEmb k r (upperIn β x)) := by
    have h := (RConj.continuous_rEl (k := k) (r := r) r β).comp
      (continuous_id.prodMk (continuous_const : Continuous fun _ : UTin β → ℂ => (0 : PTop k r r)))
    refine continuous_pi fun i => continuous_pi fun j => ?_
    have := h.matrix_elem i j
    simpa [Function.comp_def, rEl_self] using this
  have hf : (fun q : (UTin β → ℂ) × PTop k r r => Matrix.of.symm (rEl k r r β q)) =
      (fun x : UTin β → ℂ => Matrix.of.symm (uEmb k r (upperIn β x))) ∘ Prod.fst := by
    funext q
    simp [rEl_self]
  rw [lebR0, lebR, hf, ← Measure.map_map hc.measurable measurable_fst, Measure.volume_eq_prod,
    Measure.map_fst_prod, volume_pTop, one_smul]

theorem tz_last : 0 < Tz k r (bvec (wI k r (Fin.last k))) := by
  have hv : (wI k r (Fin.last k)).val = r + k := rfl
  have hH : Hpk k r (wI k r (Fin.last k)) (wI k r (Fin.last k)) = -1 := by
    unfold Hpk
    rw [hv]
    simp
  have he : herm (Hpk k r) (bvec (wI k r (Fin.last k))) (bvec (wI k r (Fin.last k))) =
      Hpk k r (wI k r (Fin.last k)) (wI k r (Fin.last k)) := by
    simp [herm, bvec, Matrix.mulVec_single, dotProduct, Pi.single_apply]
  unfold Tz
  rw [he, hH]
  norm_num

theorem stabiliser_normal : ∀ (k r : ℕ) (g₀ : Mat k r) (β : Fin r → ℕ), IsNormal k r β g₀ → Rset k r g₀ = Set.range (fun x : UTin β → ℂ => uEmb k r (upperIn β x)) ∧ IsClosedSub k r (Rset k r g₀) ∧ IsHaarOn (Rset k r g₀) (lebR k r β) ∧ IsUnimod (Rset k r g₀) (lebR k r β) ∧ IsNormal k r β g₀⁻¹ ∧ (lebR k r β).map (conjM g₀) = lebR k r β := by
  intro k r g₀ β hN
  obtain ⟨w, hw⟩ : ∃ w : Fin (2 * r + k + 1) → ℂ, w = bvec (wI k r (Fin.last k)) := ⟨_, rfl⟩
  have h0 : IsNormal0 k r le_rfl β 1 (g₀ *ᵥ w) w g₀ := (isNormal0_iff w).2 hN
  have hwW : inWb k r w := hw ▸ NfMid.inWb_bvec _
  have hzW : inWb k r (g₀ *ᵥ w) := NfMid.inWb_mulVec h0 hwW
  have hT : 0 < Tz k r (g₀ *ᵥ w) := by
    rw [← NfMid.tz_eq h0, hw]
    exact tz_last
  obtain ⟨hR, hC⟩ := GlobalTheory.T.commonStabilizerSet_eq_range_normalForm k r r le_rfl (g₀ *ᵥ w) w g₀ β 1 hzW hwW hT h0
  obtain ⟨hH, hU⟩ := GlobalTheory.T.stabilizer_haar_unimodular_normal k r r le_rfl (g₀ *ᵥ w) w g₀ β 1 hzW hwW hT h0
  have hM := RConj.lebR0_map_conjM_eq_of_isNormalZero k r r le_rfl (g₀ *ᵥ w) w g₀ β 1 hzW hwW hT h0
  rw [lebesgueCommonStabilizerNormalForm_full_eq] at hH hU hM
  rw [range_rEl] at hR
  refine ⟨hR, hC, hH, hU, ?_, hM⟩
  have hi := NfMid.isNormal0_inv h0
  rw [inv_one] at hi
  have hback : g₀⁻¹ *ᵥ (g₀ *ᵥ w) = w := NfMid.inv_mul_vec hN.1 w
  have hi' : IsNormal0 k r le_rfl β 1 (g₀⁻¹ *ᵥ (g₀ *ᵥ w)) (g₀ *ᵥ w) g₀⁻¹ := by
    rw [hback]
    exact hi
  exact (isNormal0_iff (g₀ *ᵥ w)).1 hi'

end GlobalTheory.Amp.StabNormal
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitianDoubleCoset_mass_le_and_finite : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 1 ≤ k → ∀ d : S.Datum, (∀ j : ℕ, (S.mass d fun Λ => S.cardI d Λ = j) ≤ ENNReal.ofReal (S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (j : ℝ) ^ (k - 1))) ∧ {o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V) | S.IsTerm d o.out}.Finite := by
  first | exact @GlobalTheory.HL.MassGlue.mass_le_and_finite | exact GlobalTheory.HL.MassGlue.mass_le_and_finite | (intros; apply GlobalTheory.HL.MassGlue.mass_le_and_finite <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitianMove_preserves_frameLattice_levels : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x x' u s, S.IsMove (j + 1) d Λ x x' u s → ∀ Λ₁ : Submodule L.O S.V, (Λ₁ : Set S.V) = S.moved Λ x u s → S.IsTerm d Λ₁ ∧ ∀ y ∈ (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)), (y ∈ Λ → y ∈ Λ₁) ∧ (y ∈ S.M d Λ₁ ↔ y ∈ S.M d Λ) ∧ S.lev (S.fr d Λ₁) (S.fr' d Λ₁) y = S.lev (S.fr d Λ) (S.fr' d Λ) y := by
  first | exact @GlobalTheory.HL.MoveSame.move_same | exact GlobalTheory.HL.MoveSame.move_same | (intros; apply GlobalTheory.HL.MoveSame.move_same <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.coordinateLattice_unique_term_almost_all_places : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k → {p | ¬ ((G.S p).gg = false ∧ (G.S p).Hp = 1 ∧ (G.S p).St ⊓ MulAction.stabilizer (G.S p).GLV (Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V))) = (G.S p).K0 ∧ ∃ d₀, (G.S p).IsTermW d₀ (Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V))) 1 1 ∧ (G.S p).om d₀ (Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V))) = 1 ∧ (G.S p).H0 ⊓ MulAction.stabilizer (G.S p).GLV d₀ = (G.S p).complementReferenceCompactSubgroup ∧ (∀ Λ, (G.S p).IsTerm d₀ Λ → ∃ h ∈ (G.S p).St, Λ = h • (Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V)))) ∧ (∀ Λ, (G.S p).IsTerm d₀ Λ → (G.S p).Fr d₀ Λ = (G.S p).frameCls (G.S p).f (G.S p).f' → Λ = (Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V)))) ∧ ∀ d Λ, (G.S p).IsTerm d Λ → ∃ h ∈ (G.S p).H0, d = h • d₀)}.Finite := by
  first | exact @GlobalTheory.HL.StdPlace.coordinate_lattice_standard | exact GlobalTheory.HL.StdPlace.coordinate_lattice_standard | (intros; apply GlobalTheory.HL.StdPlace.coordinate_lattice_standard <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.cuspidal_of_convolution_fixed_moderate_growth : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → (∀ (v : InfinitePlace B.I.F) (Wv : Submodule ℂ (Fin B.I.n → ℂ)), IsIsoC (B.I.ε v) Wv → ∀ ν : Measure (UJ (B.I.ε v)), IsHaarSub (NW (B.I.ε v) Wv) ν → ∀ x y : B.I.GA, ∫ m, phe B d (x * (open Classical in ((Pi.mulSingle v m, 1) : B.I.GA)) * y) ∂ν = 0) → LocDec B h → HBig B 40 h → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → ∀ (y : B.I.L2 B.μf B.fund) (f : B.I.GA → ℂ) (C : ℝ), T y = y → IsContRep B y f → (∀ x, ‖f x‖ ≤ C * (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f)) → (∀ W, B.I.IsIsot W → ∀ ν : Measure B.I.GA, B.I.IsNQuotMeas W ν → ∀ x, ∫ m, f (m * x) ∂ν = 0) ∧ B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext y) := by
  first | exact @GlobalTheory.CuspFixed.cusp_of_fixed | exact GlobalTheory.CuspFixed.cusp_of_fixed | (intros; apply GlobalTheory.CuspFixed.cusp_of_fixed <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.besselForm_coeff_product_fubini_integrable : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ v₁ ∈ DD σ w, Integrable (fun p : Mt k r × Mt k r => coef σ u v (Matrix.of p.1) * star (coef σ u₁ v₁ (Matrix.of p.2 * Matrix.of p.1))) (μG.prod μS) := by
  first | exact @GlobalTheory.SgInf.fubini_bound | exact GlobalTheory.SgInf.fubini_bound | (intros; apply GlobalTheory.SgInf.fubini_bound <;> assumption)
end
