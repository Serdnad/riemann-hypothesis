module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1253
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1294
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1232
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1336
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle082
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle002
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1337
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

noncomputable section

namespace GlobalTheory.UniformTranslateBound

open Filter Topology
open scoped Classical

theorem schwartz_translate_decay {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : SchwartzMap E ℂ) (k : ℕ)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x y : E, ‖y‖ ≤ R → ‖f (x + y)‖ ≤ D * ((1 + ‖x‖) ^ k)⁻¹ := by
  set M := 2 ^ k * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f with hM
  have h0 : ∀ w : E, (1 + ‖w‖) ^ k * ‖f w‖ ≤ M := fun w => by
    have h1 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) le_rfl le_rfl f w
    rwa [norm_iteratedFDeriv_zero] at h1
  have hM0 : 0 ≤ M := le_trans (by positivity) (h0 0)
  refine ⟨(1 + R) ^ k * M, by positivity, fun x y hy => ?_⟩
  have hx : 0 < (1 + ‖x‖) ^ k := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hx]
  have h2 : 1 + ‖x‖ ≤ (1 + R) * (1 + ‖x + y‖) := by
    have : ‖x‖ ≤ ‖x + y‖ + ‖y‖ := by simpa using norm_sub_le (x + y) y
    nlinarith [norm_nonneg (x + y), norm_nonneg y, mul_nonneg hR (norm_nonneg (x + y))]
  calc ‖f (x + y)‖ * (1 + ‖x‖) ^ k ≤ ‖f (x + y)‖ * ((1 + R) * (1 + ‖x + y‖)) ^ k := by gcongr
    _ = (1 + R) ^ k * ((1 + ‖x + y‖) ^ k * ‖f (x + y)‖) := by rw [mul_pow]; ring
    _ ≤ (1 + R) ^ k * M := by gcongr; exact h0 _

theorem summable_one_add_norm_inv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] :
    Summable fun z : L => ((1 + ‖(z : E)‖) ^ (Module.finrank ℤ L + 1))⁻¹ := by
  refine Summable.of_norm_bounded_eventually (ZLattice.summable_norm_pow_inv L _ (Nat.lt_succ_self _)) ?_
  refine (Set.finite_singleton (0 : L)).subset fun z hz => ?_
  by_contra h0
  apply hz
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 h0
  show ‖((1 + ‖(z : E)‖) ^ (Module.finrank ℤ L + 1))⁻¹‖ ≤ ‖z‖⁻¹ ^ (Module.finrank ℤ L + 1)
  rw [norm_inv, norm_pow, Real.norm_of_nonneg (by positivity), ← inv_pow]
  gcongr
  show ‖z‖ ≤ 1 + ‖z‖
  linarith

variable (F : Type) [Field F] [NumberField F]

theorem mixed_algebraMap_fst (x : F) :
    InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (AdeleRing (𝓞 F) F) x).1 = mixedEmbedding F x := by
  rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  rfl

theorem pureA_bound {κ : Type} [Fintype κ] (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F))
    {K : Set (κ → AdeleRing (𝓞 F) F)} (hK : IsCompact K) :
    ∃ B : ℝ, ∀ z ∈ K, ∀ s : Finset (κ → F),
      ∑ ξ ∈ s, ‖GlobalTheory.WeilM.pureA F f g ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) + z)‖ ≤ B := by
  let zi : (κ → AdeleRing (𝓞 F) F) → (κ → mixedEmbedding.mixedSpace F) :=
    fun z i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1
  let zf : (κ → AdeleRing (𝓞 F) F) → (κ → FiniteAdeleRing (𝓞 F) F) := fun z i => (z i).2
  have hzi : Continuous zi :=
    continuous_pi fun i => (GlobalTheory.ThetaTransformMeas.continuous_mixed F).comp (continuous_fst.comp (continuous_apply i))
  have hzf : Continuous zf := continuous_pi fun i => continuous_snd.comp (continuous_apply i)
  obtain ⟨R, hR⟩ := (hK.image hzi).isBounded.subset_closedBall 0
  obtain ⟨Bg, hBg⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  have hBg0 : 0 ≤ Bg := (norm_nonneg _).trans (hBg 0)
  let C : Set (κ → FiniteAdeleRing (𝓞 F) F) := (fun p => p.1 - p.2) '' (tsupport g ×ˢ (zf '' K))
  have hC : IsCompact C := (hg.2.isCompact.prod (hK.image hzf)).image (continuous_fst.sub continuous_snd)
  obtain ⟨N, hN, hNC⟩ := GlobalTheory.WeilM.exists_nat_mul_integral_of_isCompact F hC
  haveI := GlobalTheory.WeilM.discreteTopology_denomLattice F κ hN
  let e : (κ → F) → (κ → mixedEmbedding.mixedSpace F) := fun ξ i => mixedEmbedding F (ξ i)
  let S : Set (κ → F) := {ξ | e ξ ∈ GlobalTheory.WeilM.denomLattice F κ N}
  obtain ⟨D, hD0, hD⟩ := schwartz_translate_decay f (Module.finrank ℤ (GlobalTheory.WeilM.denomLattice F κ N) + 1)
    (max R 0) (le_max_right _ _)
  let h : (κ → F) → ℝ := S.indicator fun ξ =>
    D * ((1 + ‖e ξ‖) ^ (Module.finrank ℤ (GlobalTheory.WeilM.denomLattice F κ N) + 1))⁻¹ * Bg
  have hh : ∀ ξ, 0 ≤ h ξ := fun ξ => Set.indicator_nonneg (fun _ _ => by positivity) ξ
  have hsum : Summable h := by
    rw [← summable_subtype_iff_indicator]
    let j : S → GlobalTheory.WeilM.denomLattice F κ N := fun ξ => ⟨_, ξ.2⟩
    have hj : Function.Injective j := fun a b hab => Subtype.ext (funext fun i =>
      mixedEmbedding_injective F (congrFun (congrArg Subtype.val hab) i))
    exact (((summable_one_add_norm_inv _).comp_injective hj).mul_left D).mul_right Bg
  refine ⟨∑' ξ, h ξ, fun z hz s => ?_⟩
  refine le_trans (Finset.sum_le_sum fun ξ _ => ?_) (hsum.sum_le_tsum s fun ξ _ => hh ξ)
  have hsplit : GlobalTheory.WeilM.pureA F f g ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) + z) =
      f (e ξ + zi z) * g ((fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) + zf z) := by
    unfold GlobalTheory.WeilM.pureA
    congr 2
    funext i
    show InfiniteAdeleRing.ringEquiv_mixedSpace F ((algebraMap F (AdeleRing (𝓞 F) F) (ξ i)).1 + (z i).1) = _
    rw [map_add (f := _), mixed_algebraMap_fst]
    rfl
  rw [hsplit, norm_mul]
  by_cases hg0 : g ((fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) + zf z) = 0
  · rw [hg0, norm_zero, mul_zero]; exact hh ξ
  have hmem : (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ C :=
    ⟨(_, zf z), ⟨subset_tsupport _ hg0, z, hz, rfl⟩, add_sub_cancel_right _ _⟩
  have hξS : ξ ∈ S := by
    show ∀ i, (N : ℝ) • e ξ i ∈ mixedEmbedding.integerLattice F
    intro i
    obtain ⟨y, hy⟩ := (IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((N : F) * ξ i) fun v => by
      rw [map_mul, map_natCast]
      exact hNC _ hmem i v
    refine ⟨y, ?_⟩
    have h2 := congrArg (mixedEmbedding F) hy
    rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
    exact h2.symm
  show _ ≤ S.indicator _ ξ
  rw [Set.indicator_of_mem hξS]
  have hzR : ‖zi z‖ ≤ max R 0 := le_max_of_le_left (mem_closedBall_zero_iff.1 (hR ⟨z, hz, rfl⟩))
  exact mul_le_mul (hD _ _ hzR) (hBg _) (norm_nonneg _) (by positivity)

theorem schA_bound_compact {κ : Type} [Fintype κ] {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ)
    {K : Set (κ → AdeleRing (𝓞 F) F)} (hK : IsCompact K) :
    ∃ B : ℝ, ∀ z ∈ K, ∀ s : Finset (κ → F),
      ∑ ξ ∈ s, ‖Φ ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) + z)‖ ≤ B := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact pureA_bound F f hg hK
  | zero => exact ⟨0, fun z _ s => by simp⟩
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨B1, hB1⟩ := h1
    obtain ⟨B2, hB2⟩ := h2
    refine ⟨B1 + B2, fun z hz s => ?_⟩
    refine le_trans (Finset.sum_le_sum fun ξ _ => norm_add_le (Φ _) (Ψ _)) ?_
    rw [Finset.sum_add_distrib]
    exact add_le_add (hB1 z hz s) (hB2 z hz s)
  | smul c Φ _ h =>
    obtain ⟨B, hB⟩ := h
    refine ⟨‖c‖ * B, fun z hz s => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hB z hz s) (norm_nonneg c)

theorem tsum_norm_translate_le : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι],
    ∀ Φ ∈ GlobalTheory.WeilM.schA F ι,
    ∃ B : ℝ, ∀ z : ι → AF F, ∑' ξ : ι → F, ‖Φ ((fun i => algebraMap F (AF F) (ξ i)) + z)‖ ≤ B := by
  intro F _ _ ι _ Φ hΦ
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.RatVecDomain.exists_compact_cover_ratVec F ι
  obtain ⟨B, hB⟩ := schA_bound_compact F hΦ hK
  refine ⟨B, fun z => ?_⟩
  obtain ⟨γ, hγ, hγK⟩ := hcov z
  obtain ⟨η, rfl⟩ := (GlobalTheory.ThetaParseval.mem_ratVec_iff _).1 hγ
  let G : (ι → F) → ℝ := fun ξ =>
    ‖Φ ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) + ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (η i)) + z))‖
  have hG : ∀ ξ : ι → F, ‖Φ ((fun i => algebraMap F (AF F) (ξ i)) + z)‖ = G (Equiv.subRight η ξ) := by
    intro ξ
    show _ = ‖Φ _‖
    congr 2
    ext i
    simp only [Pi.add_apply, Equiv.subRight_apply, Pi.sub_apply, map_sub]
    abel
  calc ∑' ξ : ι → F, ‖Φ ((fun i => algebraMap F (AF F) (ξ i)) + z)‖ = ∑' ξ, G (Equiv.subRight η ξ) := tsum_congr hG
    _ = ∑' ξ, G ξ := (Equiv.subRight η).tsum_eq G
    _ ≤ B := Real.tsum_le_of_sum_le (fun _ => norm_nonneg _) (hB _ hγK)

end GlobalTheory.UniformTranslateBound
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CptCent

theorem mem_GLint_of_entries' {K : Type} [Field K] {n : ℕ} (O : Subring K) (g : GL (Fin n) K)
    (h1 : ∀ a b, g.val a b ∈ O) (h2 : ∀ a b, (g⁻¹).val a b ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have inj : Function.Injective (O.subtype.mapMatrix (m := Fin n)) :=
    fun A B h => by ext i j; exact congrFun (congrFun h i) j
  let A : Matrix (Fin n) (Fin n) O := fun i j => ⟨g.val i j, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) O := fun i j => ⟨(g⁻¹).val i j, h2 i j⟩
  have hA : O.subtype.mapMatrix A = g.val := rfl
  have hB : O.subtype.mapMatrix B = (g⁻¹).val := rfl
  refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext rfl⟩
  · rw [map_mul, hA, hB, map_one, Units.mul_inv]
  · rw [map_mul, hA, hB, map_one, Units.inv_mul]

theorem entry_mem_of_mem_GLint' {K : Type} [Field K] {n : ℕ} (O : Subring K) {g : GL (Fin n) K}
    (hg : g ∈ Formalism.UG.GLint (Fin n) O) (a b : Fin n) : g.val a b ∈ O := by
  obtain ⟨h, rfl⟩ := hg
  exact (h.val a b).2

theorem conj_zpow' {G : Type} [Group G] (g t : G) (k : ℤ) : (g⁻¹ * t * g) ^ k = g⁻¹ * t ^ k * g := by
  have := map_zpow (MulAut.conj g⁻¹) t k
  simpa [MulAut.conj_apply] using this.symm

theorem cptPart_le_conj_KL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E)
    (P₀ : (w.adicCompletionIntegers E)[X]), IsCoprime P₀ (derivative P₀) →
    ∀ γ : UL n w, γ.1.val.charpoly = P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) →
    ∀ g : UL n w, g⁻¹ * γ * g ∈ KL n w →
    cptPart (twCent (MonoidHom.id (UL n w)) γ) ≤ (KL n w).map (MulAut.conj g).toMonoidHom := by
  intro E _ _ _ n w P₀ hP₀ γ hγ g hg
  have hgK : ((g⁻¹ * γ * g : UL n w) : GLw n w) ∈ GlobalTheory.LFun.KGL w (n := n) := (Subgroup.mem_subgroupOf).1 hg
  set A : Matrix (Fin n) (Fin n) (w.adicCompletion E) := ((g⁻¹ * γ * g : UL n w) : GLw n w).val with hAdef
  have hA : ∀ i j, A i j ∈ w.adicCompletionIntegers E := fun i j => entry_mem_of_mem_GLint' _ hgK i j
  have hAc : A.charpoly = P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) := by
    rw [← hγ, hAdef]
    have : ((g⁻¹ * γ * g : UL n w) : GLw n w).val = ((g : GLw n w)⁻¹).val * (γ : GLw n w).val * (g : GLw n w).val := by
      simp
    rw [this, Matrix.coe_units_inv]
    exact Matrix.charpoly_units_conj' (g : GLw n w) ((γ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))
  show Subgroup.closure _ ≤ _
  rw [Subgroup.closure_le]
  rintro t ⟨ht, hcpt⟩
  have htγ : t * γ = γ * t := by simpa [twCent] using ht
  obtain ⟨B, hB⟩ := GlobalTheory.T.conj_zpowers_entries_valued_bounded_of_compact_closure E n w t g hcpt
  set x : UL n w := g⁻¹ * t * g with hx
  have hxA : x * (g⁻¹ * γ * g) = (g⁻¹ * γ * g) * x := by
    simp only [hx, mul_assoc, mul_inv_cancel_left]
    rw [← mul_assoc t, htγ, mul_assoc]
  have val_pow : ∀ (y : UL n w) (k : ℕ), ((y ^ k : UL n w) : GLw n w).val = ((y : GLw n w).val) ^ k := by
    intro y k; simp
  have entries : ∀ (y : UL n w), y * (g⁻¹ * γ * g) = (g⁻¹ * γ * g) * y →
      (∀ k : ℕ, ∃ m : ℤ, y ^ k = g⁻¹ * t ^ m * g) → ∀ i j, (y : GLw n w).val i j ∈ w.adicCompletionIntegers E := by
    intro y hy hpow
    refine GlobalTheory.T.mem_integral_of_commute_separable_reduction E w n P₀ hP₀ A _ hA hAc ?_ ⟨B, fun k i j => ?_⟩
    · have := congrArg (fun z : UL n w => (z : GLw n w).val) hy
      simpa [Commute, SemiconjBy, hAdef] using this
    · obtain ⟨m, hm⟩ := hpow k
      rw [← val_pow, hm]
      exact hB m i j
  have hxO := entries x hxA (fun k => ⟨k, by rw [hx, ← conj_zpow']; simp⟩)
  have hxiO := entries x⁻¹ (by
      have := congrArg (fun z => x⁻¹ * z * x⁻¹) hxA
      simpa [mul_assoc] using this.symm)
    (fun k => ⟨-(k : ℤ), by rw [hx, ← conj_zpow', _root_.zpow_neg, zpow_natCast, inv_pow]⟩)
  refine ⟨x, ?_, ?_⟩
  · show x ∈ KL n w
    refine (Subgroup.mem_subgroupOf).2 (mem_GLint_of_entries' _ _ hxO fun a b => ?_)
    have := hxiO a b
    simpa using this
  · simp [hx, MulAut.conj_apply, mul_assoc]

end GlobalTheory.CptCent
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTw.Comm

open GlobalTheory.EulerTw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem thF_thF (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) : thF E n (thF E n g) = g :=
  GlobalTheory.ThetaPull.thetaGL_thetaGL _ GlobalTheory.ThetaPull.cFin_cFin g

theorem thF_ratF (g : GL (Fin n) E) : ratF E n (thE E n g) = thF E n (ratF E n g) :=
  GlobalTheory.ThetaPull.map_thetaGL _ _ _ (fun x => (conjFin_algebraMap (IsCMField.complexConj E).toRingEquiv x).symm) g

end GlobalTheory.EulerTw.Comm

namespace GlobalTheory.EulerTw

end GlobalTheory.EulerTw
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovolCong

theorem smul_mem_hat (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    (S T : Set (Fin n → E)) (b : E) (hb : ∀ x ∈ S, b • x ∈ T) :
    ∀ z ∈ GlobalTheory.AdLat.hat F S, ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] b) • z ∈ GlobalTheory.AdLat.hat F T := by
  intro z hz
  let φ : (Fin n → GlobalTheory.AdLat.RA F E) →+ (Fin n → GlobalTheory.AdLat.RA F E) :=
    DistribSMul.toAddMonoidHom _ ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] b)
  have hle : GlobalTheory.AdLat.hat F S ≤ (GlobalTheory.AdLat.hat F T).comap φ := by
    unfold GlobalTheory.AdLat.hat
    rw [AddSubgroup.closure_le]
    rintro _ ⟨a, ha, x, hx, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap]
    refine AddSubgroup.subset_closure ⟨a, ha, b • x, hb x hx, ?_⟩
    funext i
    simp only [φ, DistribSMul.toAddMonoidHom_apply, Pi.smul_apply, smul_eq_mul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  exact hle hz

theorem inv_smul_mem {D : D7} (V : HSp D) (I : Ideal (𝓞 D.host.E)) (b : D.host.E)
    (hb : b ∈ (D.host.AA⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))
    (y : Fin V.rank → D.host.E)
    (hy : y ∈ (I • Formalism.L2.Pj.latG V 1 : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))) :
    b • y ∈ (I • GlobalTheory.Member.latC V : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) := by
  have hA : D.host.AA ≠ 0 := AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D
  have hsub := (GlobalTheory.Member.latG_lattice_and_completion D V 1).2.2.2.2.2
  let f : (Fin V.rank → D.host.E) →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) :=
    (b • LinearMap.id : (Fin V.rank → D.host.E) →ₗ[D.host.E] (Fin V.rank → D.host.E)).restrictScalars (𝓞 D.host.E)
  have hf : (Formalism.L2.Pj.latG V 1).map f ≤ GlobalTheory.Member.latC V := by
    rw [hsub, Submodule.map_span_le]
    rintro _ ⟨a, ha, x, hx, rfl⟩
    have hba : b * a ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
      rw [← inv_mul_cancel₀ hA]
      exact FractionalIdeal.mul_mem_mul hb ha
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 hba
    have : f (a • x) = r • x := by
      simp only [f, LinearMap.restrictScalars_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
      rw [← hr, algebraMap_smul]
    rw [this]
    exact Submodule.smul_mem _ r hx
  have h1 : f y ∈ (I • Formalism.L2.Pj.latG V 1).map f := Submodule.mem_map_of_mem hy
  rw [Submodule.map_smul''] at h1
  exact Submodule.smul_mono le_rfl hf h1

theorem gen_mem {D : D7} (V : HSp D) (K : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA D.host.F D.host.E))
    (I : Ideal (𝓞 D.host.E))
    (h : ∀ z ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.Pj.latG V 1 : Set (Fin V.rank → D.host.E)), K *ᵥ z - z ∈
      GlobalTheory.AdLat.hat D.host.F ((I • Formalism.L2.Pj.latG V 1 : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
        Set (Fin V.rank → D.host.E)))
    (c : FiniteAdeleRing (𝓞 D.host.F) D.host.F)
    (hc : ∀ v : HeightOneSpectrum (𝓞 D.host.F), c v ∈ HeightOneSpectrum.adicCompletionIntegers D.host.F v)
    (x : Fin V.rank → D.host.E) (hx : x ∈ GlobalTheory.Member.latC V) :
    K *ᵥ (fun i => c ⊗ₜ[D.host.F] x i) - (fun i => c ⊗ₜ[D.host.F] x i) ∈
      GlobalTheory.AdLat.hat D.host.F ((I • GlobalTheory.Member.latC V : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
        Set (Fin V.rank → D.host.E)) := by
  have hA : D.host.AA ≠ 0 := AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D
  have hsub := (GlobalTheory.Member.latG_lattice_and_completion D V 1).2.2.2.2.2
  let ψ : (Fin V.rank → GlobalTheory.AdLat.RA D.host.F D.host.E) →+ (Fin V.rank → GlobalTheory.AdLat.RA D.host.F D.host.E) :=
    AddMonoidHom.mk' (fun z => K *ᵥ z - z) (fun x y => by rw [Matrix.mulVec_add]; abel)
  have hψs : ∀ (s : GlobalTheory.AdLat.RA D.host.F D.host.E) z, ψ (s • z) = s • ψ z := by
    intro s z
    simp only [ψ, AddMonoidHom.mk'_apply, Matrix.mulVec_smul, smul_sub]
  have h1 : (1 : D.host.E) ∈ ((D.host.AA : Submodule (𝓞 D.host.E) D.host.E) *
      ((D.host.AA⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E)) := by
    rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hA]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩
  have key := Submodule.mul_induction_on (C := fun t : D.host.E => ψ (fun i => c ⊗ₜ[D.host.F] (t * x i)) ∈
      GlobalTheory.AdLat.hat D.host.F ((I • GlobalTheory.Member.latC V : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
        Set (Fin V.rank → D.host.E))) h1 ?_ ?_
  · simp only [one_mul] at key
    exact key
  · intro m hm b hb
    have hw : (fun i => c ⊗ₜ[D.host.F] (m * x i)) ∈
        GlobalTheory.AdLat.hat D.host.F (Formalism.L2.Pj.latG V 1 : Set (Fin V.rank → D.host.E)) := by
      refine AddSubgroup.subset_closure ⟨c, hc, m • x, ?_, rfl⟩
      rw [hsub]
      exact Submodule.subset_span ⟨m, hm, x, hx, rfl⟩
    have h2 := smul_mem_hat D.host.F _ _ b (fun y hy => inv_smul_mem V I b hb y hy) _ (h _ hw)
    have e : ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] b) • (K *ᵥ (fun i => c ⊗ₜ[D.host.F] (m * x i)) -
        (fun i => c ⊗ₜ[D.host.F] (m * x i))) = ψ (fun i => c ⊗ₜ[D.host.F] (m * b * x i)) := by
      have : (fun i => c ⊗ₜ[D.host.F] (m * b * x i)) =
          ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] b) • (fun i => c ⊗ₜ[D.host.F] (m * x i)) := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        congr 1
        ring
      rw [this, hψs]
      rfl
    rw [← e]
    exact h2
  · intro t t' ht ht'
    have : (fun i => c ⊗ₜ[D.host.F] ((t + t') * x i)) =
        (fun i => c ⊗ₜ[D.host.F] (t * x i)) + (fun i => c ⊗ₜ[D.host.F] (t' * x i)) := by
      funext i
      simp only [Pi.add_apply, add_mul, TensorProduct.tmul_add]
    beta_reduce at ht ht' ⊢
    rw [this, AddMonoidHom.map_add ψ]
    exact (GlobalTheory.AdLat.hat _ _).add_mem ht ht'

end GlobalTheory.CovolCong


open GlobalTheory.CovolCong in
theorem GlobalTheory.CovolCong.cong_latC_of_cong_latG : ∀ {D : D7} (V : HSp D) (K : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA D.host.F D.host.E)) (I : Ideal (𝓞 D.host.E)), (∀ z ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.Pj.latG V 1 : Set (Fin V.rank → D.host.E)), K *ᵥ z - z ∈ GlobalTheory.AdLat.hat D.host.F ((I • Formalism.L2.Pj.latG V 1 : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E))) → ∀ z ∈ GlobalTheory.AdLat.hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)), K *ᵥ z - z ∈ GlobalTheory.AdLat.hat D.host.F ((I • GlobalTheory.Member.latC V : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E)) := by
  intro D V K I h
  let ψ : (Fin V.rank → GlobalTheory.AdLat.RA D.host.F D.host.E) →+ (Fin V.rank → GlobalTheory.AdLat.RA D.host.F D.host.E) :=
    AddMonoidHom.mk' (fun z => K *ᵥ z - z) (fun x y => by rw [Matrix.mulVec_add]; abel)
  have hle : GlobalTheory.AdLat.hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) ≤
      (GlobalTheory.AdLat.hat D.host.F ((I • GlobalTheory.Member.latC V : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
        Set (Fin V.rank → D.host.E))).comap ψ := by
    unfold GlobalTheory.AdLat.hat
    rw [AddSubgroup.closure_le]
    rintro _ ⟨c, hc, x, hx, rfl⟩
    exact gen_mem V K I h c hc x hx
  intro z hz
  exact hle hz
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
open scoped ENNReal

theorem _root_.GlobalTheory.T.lintegral_affine_abs_pow_bound : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (μ : Measure k) [μ.IsAddHaarMeasure] (s : ℝ), s < 0 → ∀ a b : k,
    ∫⁻ x, (𝒪[k] : Set k).indicator (fun y => ENNReal.ofReal (if h : a * y + b = 0 then 0 else nabs k (Units.mk0 (a * y + b) h)) ^ s) x ∂μ ≤
      ENNReal.ofReal (if h : a = 0 then 0 else nabs k (Units.mk0 a h)) ^ s *
        (∫⁻ x, (𝒪[k] : Set k).indicator (fun y => ENNReal.ofReal (if h : y = 0 then 0 else nabs k (Units.mk0 y h)) ^ s) x ∂μ + μ (𝒪[k] : Set k)) := by
  first | exact @GlobalTheory.KSplit.lintegral_absPow_affine_le | exact GlobalTheory.KSplit.lintegral_absPow_affine_le | (intros; apply GlobalTheory.KSplit.lintegral_absPow_affine_le <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
open scoped ENNReal

theorem _root_.GlobalTheory.T.lintegral_matrix_first_row_column : ∀ (k : Type) [MeasurableSpace k] (ν : Measure k) [SigmaFinite ν] (n : ℕ) (F : Matrix (Fin (n + 1)) (Fin (n + 1)) k → ℝ≥0∞),
    ∫⁻ X, F X ∂(volM ν (Fin (n + 1)) (Fin (n + 1))) ≤
      ∫⁻ M, ∫⁻ v, ∫⁻ u, ∫⁻ x, F (Matrix.of (Fin.cons (Fin.cons x u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k))))
        ∂ν ∂(Measure.pi fun _ : Fin n => ν) ∂(Measure.pi fun _ : Fin n => ν) ∂(volM ν (Fin n) (Fin n)) := by
  first | exact @GlobalTheory.KSplit.CornerFubini.lintegral_volM_le_corner | exact GlobalTheory.KSplit.CornerFubini.lintegral_volM_le_corner | (intros; apply GlobalTheory.KSplit.CornerFubini.lintegral_volM_le_corner <;> assumption)
end
