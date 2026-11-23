module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Mathlib.Algebra.Module.ZLattice.Summable
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle462
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle667
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle652
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle655
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle654
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCocycleFirstChernClassTateTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle422
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle002

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

namespace GlobalTheory.SchwartzDecay

open NumberField.InfinitePlace.Completion

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

theorem continuous_mixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

theorem norm_le_mixed (x : InfiniteAdeleRing F) (v : InfinitePlace F) :
    ‖x v‖ ≤ ‖InfiniteAdeleRing.ringEquiv_mixedSpace F x‖ := by
  set e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  rcases v.isReal_or_isComplex with hv | hv
  · calc ‖x v‖ = ‖(e x).1 ⟨v, hv⟩‖ :=
          ((isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero (map_zero _) (x v)).symm
      _ ≤ ‖e x‖ := (norm_le_pi_norm (e x).1 ⟨v, hv⟩).trans (norm_fst_le (e x))
  · calc ‖x v‖ = ‖(e x).2 ⟨v, hv⟩‖ :=
          ((isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) (x v)).symm
      _ ≤ ‖e x‖ := (norm_le_pi_norm (e x).2 ⟨v, hv⟩).trans (norm_snd_le (e x))

theorem abs_re_le (x : Ainf F) (v : InfinitePlace F) :
    |re x v| ≤ ‖InfiniteAdeleRing.ringEquiv_mixedSpace F x‖ := by
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [(isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) (x v)]
  exact norm_le_mixed x v

theorem sz_nonneg (u : Fin N → AF F) : 0 ≤ sz u :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem sz_le (u : Fin N → AF F) :
    sz u ≤ (N * Fintype.card (InfinitePlace F) : ℝ) *
      ‖fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (u i).1‖ := by
  set t : Fin N → mixedEmbedding.mixedSpace F := fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (u i).1
  calc sz u ≤ ∑ _l : Fin N, ∑ _w : InfinitePlace F, ‖t‖ :=
        Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun w _ =>
          (abs_re_le (inf u l) w).trans (norm_le_pi_norm t l)
    _ = _ := by simp [mul_assoc]

theorem decay_add {Φ Ψ : (Fin N → AF F) → ℂ} (h : Decay Φ) (h' : Decay Ψ) : Decay (Φ + Ψ) := by
  obtain ⟨hc, ⟨K, hK, hK0⟩, hd⟩ := h
  obtain ⟨hc', ⟨K', hK', hK0'⟩, hd'⟩ := h'
  refine ⟨hc.add hc', ⟨K ∪ K', hK.union hK', fun u hu => ?_⟩, fun k => ?_⟩
  · rw [Set.mem_union, not_or] at hu
    simp [hK0 u hu.1, hK0' u hu.2]
  · obtain ⟨C, hC⟩ := hd k
    obtain ⟨C', hC'⟩ := hd' k
    refine ⟨C + C', fun u => ?_⟩
    have h0 : 0 ≤ (1 + sz u) ^ k := pow_nonneg (by linarith [sz_nonneg u]) k
    calc ‖(Φ + Ψ) u‖ * (1 + sz u) ^ k ≤ (‖Φ u‖ + ‖Ψ u‖) * (1 + sz u) ^ k :=
          mul_le_mul_of_nonneg_right (norm_add_le _ _) h0
      _ ≤ C + C' := by rw [add_mul]; exact add_le_add (hC u) (hC' u)

theorem decay_smul (a : ℂ) {Φ : (Fin N → AF F) → ℂ} (h : Decay Φ) : Decay (a • Φ) := by
  obtain ⟨hc, ⟨K, hK, hK0⟩, hd⟩ := h
  refine ⟨hc.const_smul a, ⟨K, hK, fun u hu => by simp [hK0 u hu]⟩, fun k => ?_⟩
  obtain ⟨C, hC⟩ := hd k
  refine ⟨‖a‖ * C, fun u => ?_⟩
  rw [Pi.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC u) (norm_nonneg a)

theorem schwartz_bound {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) (k : ℕ) :
    ∃ C : ℝ, ∀ t, (1 + ‖t‖) ^ k * ‖f t‖ ≤ C := by
  have := fun t => SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) (k := k) (n := 0) le_rfl le_rfl f t
  simp only [norm_iteratedFDeriv_zero] at this
  exact ⟨_, this⟩

theorem decay_pure (f : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ) (g : (Fin N → Af F) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin N → Af F)) : Decay (GlobalTheory.WeilM.pureA F f g) := by
  obtain ⟨hg1, hg2⟩ := hg
  refine ⟨?_, ⟨tsupport g, hg2, fun u hu => ?_⟩, fun k => ?_⟩
  · refine Continuous.mul (f.continuous.comp (continuous_pi fun i => ?_))
      (hg1.continuous.comp (continuous_pi fun i => ?_))
    · exact continuous_mixed.comp (continuous_fst.comp (continuous_apply i))
    · exact continuous_snd.comp (continuous_apply i)
  · exact mul_eq_zero_of_right _ (image_eq_zero_of_notMem_tsupport hu)
  · obtain ⟨B, hB⟩ := hg1.continuous.bounded_above_of_compact_support hg2
    obtain ⟨C, hC⟩ := schwartz_bound f k
    set c : ℝ := N * Fintype.card (InfinitePlace F)
    have hc : 0 ≤ c := by positivity
    refine ⟨(1 + c) ^ k * C * B, fun u => ?_⟩
    set t : Fin N → mixedEmbedding.mixedSpace F := fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (u i).1
    have h1 : 1 + sz u ≤ (1 + c) * (1 + ‖t‖) := by
      have : sz u ≤ c * ‖t‖ := sz_le u
      nlinarith [norm_nonneg t]
    have h2 : (1 + sz u) ^ k ≤ (1 + c) ^ k * (1 + ‖t‖) ^ k := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by linarith [sz_nonneg u]) h1 k
    have hC0 : 0 ≤ C := le_trans (by positivity) (hC 0)
    calc ‖GlobalTheory.WeilM.pureA F f g u‖ * (1 + sz u) ^ k
        = ‖f t‖ * ‖g fun i => (u i).2‖ * (1 + sz u) ^ k := by rw [← norm_mul]; rfl
      _ ≤ ‖f t‖ * ‖g fun i => (u i).2‖ * ((1 + c) ^ k * (1 + ‖t‖) ^ k) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (1 + c) ^ k * ((1 + ‖t‖) ^ k * ‖f t‖) * ‖g fun i => (u i).2‖ := by ring
      _ ≤ (1 + c) ^ k * C * B :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hC t) (by positivity)) (hB _) (norm_nonneg _) (by positivity)

theorem decay_of_mem_schA (F : Type) [Field F] [NumberField F] (N : ℕ) :
    ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin N), Decay Φ := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    exact decay_pure f g hg
  | zero => exact decay_zero
  | add x y _ _ hx hy => exact decay_add hx hy
  | smul a x _ hx => exact decay_smul a hx

end GlobalTheory.SchwartzDecay
end

section

open NumberField IsDedekindDomain

noncomputable section
open scoped Classical

namespace GlobalTheory.WeilM

variable (F : Type) [Field F] [NumberField F]

theorem thetaSum_pureA_bound {κ : Type} [Fintype κ] {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) : ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧
    ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      ‖thetaSum F (pureA F f g)‖ ≤ C * (s.sup (schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)) f := by
  obtain ⟨B, hB⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  obtain ⟨N, hN, hK⟩ := exists_nat_mul_integral_of_isCompact F hg.2.isCompact
  haveI := discreteTopology_denomLattice F κ hN
  have hw := ZLattice.summable_norm_pow_inv (denomLattice F κ N) (Module.finrank ℤ (denomLattice F κ N) + 1)
    (Nat.lt_succ_self _)
  set k := Module.finrank ℤ (denomLattice F κ N) + 1 with hkdef
  set W := ∑' z : denomLattice F κ N, ‖z‖⁻¹ ^ k with hWdef
  have hW0 : 0 ≤ W := tsum_nonneg fun _ => by positivity
  refine ⟨{(0, 0), (k, 0)}, max B 0 * (1 + W), mul_nonneg (le_max_right _ _) (by linarith), fun f => ?_⟩
  set M := (({(0, 0), (k, 0)} : Finset (ℕ × ℕ)).sup
    (schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)) f with hMdef
  have h00 : ∀ x, ‖f x‖ ≤ M := fun x => (SchwartzMap.norm_le_seminorm ℂ f x).trans
    (Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)
      (i := (0, 0)) (by simp))
  have hk0 : ∀ x, ‖x‖ ^ k * ‖f x‖ ≤ M := fun x => by
    have := SchwartzMap.le_seminorm ℂ k 0 f x
    rw [norm_iteratedFDeriv_zero] at this
    exact this.trans (Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)
      (i := (k, 0)) (by simp))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (h00 0)
  have hpt : ∀ z : denomLattice F κ N, ‖f z‖ ≤ (if z = 0 then M else 0) + ‖z‖⁻¹ ^ k * M := fun z => by
    by_cases hz : z = 0
    · subst hz; simp only [if_true]
      have := h00 0
      have h2 : 0 ≤ ‖(0 : denomLattice F κ N)‖⁻¹ ^ k * M := by positivity
      simpa using (show ‖f 0‖ ≤ M + ‖(0 : denomLattice F κ N)‖⁻¹ ^ k * M by linarith)
    · rw [if_neg hz, zero_add]
      have hz0 : 0 < ‖z‖ := norm_pos_iff.2 hz
      rw [inv_pow, ← div_eq_inv_mul, le_div_iff₀ (pow_pos hz0 _), mul_comm]
      exact hk0 z
  have hs1 : HasSum (fun z : denomLattice F κ N => if z = 0 then M else 0) M := by
    convert hasSum_ite_eq (0 : denomLattice F κ N) M
  have hsumL : Summable fun z : denomLattice F κ N => (if z = 0 then M else 0) + ‖z‖⁻¹ ^ k * M :=
    hs1.summable.add (hw.mul_right M)
  have hfL : Summable fun z : denomLattice F κ N => ‖f z‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hsumL
  have hLbound : ∑' z : denomLattice F κ N, ‖f z‖ ≤ (1 + W) * M := by
    refine (hfL.tsum_le_tsum hpt hsumL).trans (le_of_eq ?_)
    rw [hs1.summable.tsum_add (hw.mul_right M), hs1.tsum_eq, tsum_mul_right]
    ring

  have hmem : pureA F f g ∈ schA F κ := Submodule.subset_span ⟨f, g, hg, rfl⟩
  let S : Set (κ → F) := {ξ | (fun i => mixedEmbedding F (ξ i)) ∈ denomLattice F κ N}
  have hsupp : Function.support (fun ξ : κ → F => ‖pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))‖)
      ⊆ S := by
    intro ξ hξ
    rw [Function.mem_support, norm_ne_zero_iff, pureA_algebraMap] at hξ
    have h0 := right_ne_zero_of_mul hξ
    show ∀ i, _
    intro i
    obtain ⟨y, hy⟩ := (IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((N : F) * ξ i) fun v => by
      rw [map_mul, map_natCast]
      exact hK _ (subset_tsupport _ h0) i v
    refine ⟨y, ?_⟩
    have h2 := congrArg (mixedEmbedding F) hy
    rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
    exact h2.symm
  let j : S → denomLattice F κ N := fun ξ => ⟨_, ξ.2⟩
  have hj : Function.Injective j := fun a b h => Subtype.ext (funext fun i =>
    mixedEmbedding_injective F (congrFun (congrArg Subtype.val h) i))
  have hterm : ∀ ξ : S, ‖pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ.1 i))‖ ≤
      max B 0 * ((fun z : denomLattice F κ N => ‖f z‖) ∘ j) ξ := fun ξ => by
    rw [pureA_algebraMap, norm_mul, mul_comm, Function.comp_apply]
    exact mul_le_mul (le_max_of_le_left (hB _)) le_rfl (norm_nonneg _) (le_max_right _ _)
  have hsumS : Summable ((fun z : denomLattice F κ N => ‖f z‖) ∘ j) := hfL.comp_injective hj
  calc ‖thetaSum F (pureA F f g)‖
      ≤ ∑' ξ : κ → F, ‖pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))‖ :=
        norm_tsum_le_tsum_norm (summable_norm_of_mem_schA F hmem)
    _ = ∑' ξ : S, ‖pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ.1 i))‖ :=
        (tsum_subtype_eq_of_support_subset hsupp).symm
    _ ≤ ∑' ξ : S, max B 0 * ((fun z : denomLattice F κ N => ‖f z‖) ∘ j) ξ :=
        ((summable_norm_of_mem_schA F hmem).subtype (fun x => x ∈ S)).tsum_le_tsum hterm (hsumS.mul_left _)
    _ = max B 0 * ∑' ξ : S, ((fun z : denomLattice F κ N => ‖f z‖) ∘ j) ξ := tsum_mul_left
    _ ≤ max B 0 * ∑' z : denomLattice F κ N, ‖f z‖ :=
        mul_le_mul_of_nonneg_left (tsum_comp_le_tsum_of_inj hfL (fun _ => norm_nonneg _) hj) (le_max_right _ _)
    _ ≤ max B 0 * ((1 + W) * M) := mul_le_mul_of_nonneg_left hLbound (le_max_right _ _)
    _ = max B 0 * (1 + W) * M := by ring

theorem exists_adm_eq_thetaSum_of_locallyCompact (F : Type) [Field F] [NumberField F] [LocallyCompactSpace (AdeleRing (𝓞 F) F)]
    (κ : Type) [Fintype κ] : ∃ l : ((κ → AdeleRing (𝓞 F) F) → ℂ) →ₗ[ℂ] ℂ, l ∈ (adeleClass F).adm κ ∧
      ∀ Φ ∈ schA F κ, l Φ = thetaSum F Φ := by
  obtain ⟨l, hl⟩ := LinearMap.exists_extend (thetaLin F κ)
  have hl' : ∀ Φ ∈ schA F κ, l Φ = thetaSum F Φ := fun Φ h => by
    have := LinearMap.congr_fun hl ⟨Φ, h⟩
    simpa using this
  refine ⟨l, fun g hg => ?_, hl'⟩
  have hmem : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, pureA F f g ∈ schA F κ :=
    fun f => Submodule.subset_span ⟨f, g, hg, rfl⟩
  have hadd : ∀ f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      pureA F (f + f') g = pureA F f g + pureA F f' g := fun f f' => by
    funext x; simp [pureA, add_mul]
  have hsmul : ∀ (a : ℂ) (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ),
      pureA F (a • f) g = a • pureA F f g := fun a f => by
    funext x; simp [pureA, mul_assoc]
  let T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ :=
    SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (fun f => thetaSum F (pureA F f g))
      (fun f f' => by rw [hadd]; exact thetaSum_add F (hmem f) (hmem f'))
      (fun a f => by rw [hsmul, thetaSum_smul]; rfl) (thetaSum_pureA_bound F hg)
  exact ⟨T, fun f => hl' _ (hmem f)⟩

end GlobalTheory.WeilM
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

open GlobalTheory.EtC.ClsSpec in

theorem _root_.GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive :
    ∀ (q : ℕ) [NeZero q],
      (∀ {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
        ∃ γ : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2,
          CohomologyClass.mk γ = c1 q L ∧
          (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev (R := ZMod q) γ.1 0 2 (by simp) U x = 0) ∧
          (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
            ev (R := ZMod q) γ.1 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧
          ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ),
            v ^ q = lineUnit L (x.sub 0 1 (by omega)) → w ^ q = lineUnit L (x.sub 1 1 (by omega)) →
            ev (R := ZMod q) γ.1 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)) ∧
      (∀ {E E' : Spc} (f : E ⟶ E') (L : E' ⟶ ofCat (glCat 1)), Inv q E' →
        pull _ f _ _ (c1 q L) = c1 q (f ≫ L)) ∧
      ∀ {E : Spc} (L M N : E ⟶ ofCat (glCat 1)), Inv q E →
        (∀ (U : Scheme.{0}) (x : Sx E 1 U), lineUnit N x = lineUnit L x * lineUnit M x) →
        c1 q N = c1 q L + c1 q M := by
  intro q _
  refine ⟨?_, fun f L hE => ChernSpec.firstChernClassTateTwist_pullback q f L hE,
    fun L M N hE hN => ChernSpec.isOneCochain_add q L M N hE hN⟩
  have exists_single {E : Spc} {I : Cx (ZMod q)} {n : ℤ} (p₀ : ℕ) (s₀ : ℤ) (h₀ : -(p₀ : ℤ) + n = s₀)
      (b : ∀ U : Scheme.{0}, Sx E p₀ U → Sec (I.X s₀) U)
      (hb : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p₀ U), Sec.res g (b U x) = b V (x.res g)) :
      ∃ α : Cochain ((chains (ZMod q)).obj E) I n, (∀ U x, ev (R := ZMod q) α p₀ s₀ h₀ U x = b U x) ∧
        ∀ p s h U x, p ≠ p₀ → ev (R := ZMod q) α p s h U x = 0 := by
    subst h₀
    obtain ⟨α, hα⟩ := exists_cochain_ev_eq_of_natural (ZMod q) (E := E) (I := I) (n := n)
      (fun p s h U x => if hp : p = p₀ then (by subst hp; subst h; exact b U x) else 0) (by
        intro p s h V U g x
        by_cases hp : p = p₀
        · subst hp; subst h
          simp only [dite_eq_left]
          exact hb V U g x
        · simp only [dite_eq_right hp]
          exact map_zero _)
    refine ⟨α, fun U x => ?_, fun p s h U x hp => ?_⟩
    · rw [hα]
      simp only [dite_eq_left]
    · rw [hα]
      simp only [dite_eq_right hp]
  have differential_eq_zero {E : Spc} {I : Cx (ZMod q)} {n m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains (ZMod q)).obj E) I n)
      (h₀ : ∀ (U : Scheme.{0}) (x : Sx E 0 U), Sec.map (I.d n m) (ev (R := ZMod q) α 0 n (by simp) U x) = 0)
      (h₁ : ∀ (U : Scheme.{0}) (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -(p : ℤ) + n = t) (x : Sx E (p + 1) U),
        Sec.map (I.d s t) (ev (R := ZMod q) α (p + 1) s hs U x) +
          m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev (R := ZMod q) α p t ht U (x.face i) = 0) : δ n m α = 0 := by
    refine CupSpec.ev_ext _ _ fun p t ht U x => ?_
    rw [CupSpec.ev_zero]
    cases p with
    | zero =>
      obtain rfl : m = t := by simpa using ht
      exact (CupSpec.ev_δ_zero hm α U n m (by simp) (by simp) x).trans (h₀ U x)
    | succ p => exact (CupSpec.ev_δ_succ hm α U p _ t rfl ht x).trans (h₁ U p _ t rfl _ x)
  have exists_cocycle {t : ∀ U : Scheme.{0}, (Γ(U, ⊤))ˣ → Sec ((res _ (tw q 1)).X 0) U} (ht : IsKum q t)
      {E : Spc} (hE : Inv q E) (L : E ⟶ ofCat (glCat 1)) :
      ∃ γ : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2,
      (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev (R := ZMod q) γ.1 0 2 (by simp) U x = 0) ∧
      (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
        ev (R := ZMod q) γ.1 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (t U v)) ∧
      ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.face 2) →
        w ^ q = lineUnit L (x.face 0) →
        ev (R := ZMod q) γ.1 2 0 (by simp) U x = t U v + t U w - t U (v * w) := by
    have hq₁ : ∀ (U : Scheme.{0}) (_ : Sx E 1 U), IsUnit (q : Γ(U, ⊤)) := fun U x => hE U ⟨x.face 0⟩
    have hq₂ : ∀ (U : Scheme.{0}) (_ : Sx E 2 U), IsUnit (q : Γ(U, ⊤)) := fun U x => hq₁ U (x.face 0)
    have hf : ∀ (i : Fin 3) (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 2 U),
        lineUnit L ((x.res g).face i) = umap g (lineUnit L (x.face i)) := fun i _ _ g x => ChernSpec.lineUnit_face_res L g x i
    obtain ⟨b, hb, hd, hv⟩ := exists_d_family ht hq₁ (fun U x => lineUnit L x) (fun V U g x => lineUnit_res L g x)
    obtain ⟨e, he, hw⟩ := exists_two_family ht hq₂ (fun U x => lineUnit L (x.face 2)) (fun U x => lineUnit L (x.face 0))
      (hf 2) (hf 0)
    have h₂ : ∀ (U : Scheme.{0}) (y : Sx E 2 U),
        Sec.map ((res _ (tw q 1)).d 0 1) (e U y) = b U (y.face 0) - b U (y.face 1) + b U (y.face 2) := by
      intro U y
      refine sep (loc_mono (loc_and (root_loc (hq₂ U y) (lineUnit L (y.face 2))) (root_loc (hq₂ U y) (lineUnit L (y.face 0)))) ?_)
      rintro V g ⟨⟨v, h⟩, w, h'⟩
      rw [← hf] at h h'
      rw [res_map, res_add, res_sub, he, hb, hb, hb, face_res, face_res, face_res, hw V _ v w h h', hv V _ v h, hv V _ w h',
        hv V _ (v * w) (by rw [mul_pow, h, h', lineUnit_face]), smap_sub, smap_add]
      abel
    have h₃ : ∀ (U : Scheme.{0}) (y : Sx E 3 U),
        e U (y.face 0) - e U (y.face 1) + e U (y.face 2) - e U (y.face 3) = 0 := by
      intro U y
      have hU := hq₂ U (y.face 0)
      refine sep (loc_mono (loc_and (root_loc hU (lineUnit L ((y.face 3).face 2)))
        (loc_and (root_loc hU (lineUnit L ((y.face 0).face 2))) (root_loc hU (lineUnit L ((y.face 0).face 0))))) ?_)
      rintro V g ⟨⟨u, h⟩, ⟨v, h'⟩, w, h''⟩
      rw [← hf, face_res] at h h' h''
      rw [res_sub, res_add, res_sub, he, he, he, he, face_res, face_res, face_res, face_res, res_zero]
      generalize y.res g = z at h h' h'' ⊢
      have e₁ : (z.face 1).face 0 = (z.face 0).face 0 := face_face z _ _ _ _ (by decide)
      have e₂ : (z.face 1).face 2 = (z.face 3).face 1 := face_face z _ _ _ _ (by decide)
      have e₃ : (z.face 2).face 2 = (z.face 3).face 2 := face_face z _ _ _ _ (by decide)
      have e₄ : (z.face 2).face 0 = (z.face 0).face 1 := face_face z _ _ _ _ (by decide)
      have e₅ : (z.face 3).face 0 = (z.face 0).face 2 := face_face z _ _ _ _ (by decide)
      rw [hw V _ v w h' h'', hw V (z.face 1) (u * v) w (by rw [e₂, lineUnit_face, e₅, mul_pow, h, h']) (by rw [e₁, h'']),
        hw V (z.face 2) u (v * w) (by rw [e₃, h]) (by rw [e₄, lineUnit_face, mul_pow, h', h'']),
        hw V (z.face 3) u v h (by rw [e₅, h']), mul_assoc]
      abel
    obtain ⟨α, a₁, a₂⟩ := exists_single (I := res _ (tw q 1)) (n := 2) 1 1 (by simp) b hb
    obtain ⟨β, b₁, b₂⟩ := exists_single (I := res _ (tw q 1)) (n := 2) 2 0 (by simp) e he
    have c₀ : ∀ p s h U x, p ≠ 1 → p ≠ 2 → ev (R := ZMod q) (α + β) p s h U x = 0 := fun p s h U x h₁ h₂ => by
      rw [CupSpec.ev_add, a₂ _ _ _ _ _ h₁, b₂ _ _ _ _ _ h₂, add_zero]
    have c₁ : ∀ h U x, ev (R := ZMod q) (α + β) 1 1 h U x = b U x := fun h U x => by
      rw [CupSpec.ev_add, a₁, b₂ _ _ _ _ _ (by decide), add_zero]
    have c₂ : ∀ h U x, ev (R := ZMod q) (α + β) 2 0 h U x = e U x := fun h U x => by
      rw [CupSpec.ev_add, b₁, a₂ _ _ _ _ _ (by decide), zero_add]
    have hs : (3 : ℤ).negOnePow = -1 := rfl
    refine ⟨Cocycle.mk (α + β) 3 rfl (differential_eq_zero (m := 3) rfl _ (fun U x => ?_) (fun U p s t hs' ht' x => ?_)),
      fun U x => c₀ 0 2 _ U x (by decide) (by decide), fun U x v h => (c₁ _ U x).trans (hv U x v h),
      fun U x v w h h' => (c₂ _ U x).trans (hw U x v w h h')⟩
    · rw [c₀ _ _ _ _ _ (by decide) (by decide), smap_zero]
    · match p with
      | 0 =>
        obtain rfl : s = 1 := by omega
        obtain rfl : t = 2 := by omega
        rw [Finset.sum_eq_zero fun i _ => by rw [c₀ _ _ _ _ _ (by decide) (by decide), smul_zero], smul_zero, add_zero]
        exact (congrArg _ (c₁ _ U x)).trans (hd U x)
      | 1 =>
        obtain rfl : s = 0 := by omega
        obtain rfl : t = 1 := by omega
        rw [Fin.sum_univ_three, c₁, c₁, c₁, c₂, h₂, hs]
        simp
        abel
      | 2 =>
        obtain rfl : t = 0 := by omega
        rw [Fin.sum_univ_four, c₂, c₂, c₂, c₂, c₀ _ _ _ _ _ (by decide) (by decide), smap_zero, zero_add]
        convert smul_zero _
        rw [← h₃ U x]
        norm_num
        abel
      | p + 3 =>
        rw [c₀ _ _ _ _ _ (by omega) (by omega), smap_zero, zero_add,
          Finset.sum_eq_zero fun i _ => by rw [c₀ _ _ _ _ _ (by omega) (by omega), smul_zero], smul_zero]
  intro E L hE
  refine pick_spec (P := fun c : Ht q E 2 1 => ∃ γ : Cocycle _ _ 2, CohomologyClass.mk γ = c ∧
    (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev (R := ZMod q) γ.1 0 2 (by simp) U x = 0) ∧
    (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      ev (R := ZMod q) γ.1 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) →
      w ^ q = lineUnit L (x.sub 1 1 (by omega)) →
      ev (R := ZMod q) γ.1 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)) ?_
  rcases kumT_cases q with h | h
  · obtain ⟨γ, h₀, h₁, h₂⟩ := exists_cocycle h hE L
    exact ⟨_, γ, rfl, h₀, h₁, fun U x v w hv hw => h₂ U x v w (by rw [hv, sub_zero_one]) (by rw [hw, sub_one_one])⟩
  · refine ⟨_, 0, rfl, fun U x => CupSpec.ev_zero _ _ _ _ _, fun U x v _ => (CupSpec.ev_zero _ _ _ _ _).trans ?_,
      fun U x v w _ _ => (CupSpec.ev_zero _ _ _ _ _).trans ?_⟩
    · rw [h]
      exact (smap_zero _).symm
    · rw [h]
      simp
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

theorem _root_.GlobalTheory.T.tateTwistCohomology_laurent_vanishing_finite_algebra : ∀ (q : ℕ) [NeZero q] (n : ℤ), (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
    ∀ m i : ℤ, 2 ≤ m → m < n → Subsingleton (Ht q (sp (LaurentPolynomial A)) m i)) →
  ∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ (T : Type) [CommRing T] [Algebra A T],
  Module.Finite A T → ∀ s i : ℤ, 2 ≤ s → s < n → Subsingleton (Ht q (sp (LaurentPolynomial T)) s i) := by
  first | (exact @GlobalTheory.EtC.laurent_vanishing_finite) | (exact GlobalTheory.EtC.laurent_vanishing_finite) | (intros; apply GlobalTheory.EtC.laurent_vanishing_finite <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.mulP_mem_sq_counit_ker : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O], (p : O) ≠ 0 → ¬IsUnit (p : O) → (∀ a : O, ∃ b : O, b ^ p = a) → ∀ (G : GlobalTheory.PDivGroup p O) (n : ℕ) (b : G.A n), G.mulP n b ∈ RingHom.ker (Bialgebra.counitAlgHom O (G.A (n + 1))) ^ 2 → b ∈ RingHom.ker (Bialgebra.counitAlgHom O (G.A n)) ^ 2 := by
  first | exact @GlobalTheory.PDivGroup.mulP_mem_sq_counit | exact GlobalTheory.PDivGroup.mulP_mem_sq_counit | (intros; apply GlobalTheory.PDivGroup.mulP_mem_sq_counit <;> assumption)
end

section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.pDivGroup_residueField_tate_level_section : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] [IsLocalRing O], v.Integers O → ∀ G : PDivGroup p O, (∀ (n : ℕ) (c : G.A n →ₐ[O] IsLocalRing.ResidueField O), ∃ t : G.TateOver (IsLocalRing.ResidueField O), t.pt n = c) ∧ ∃ s : G.TateOver (IsLocalRing.ResidueField O) →ₗ[ℤ_[p]] G.Tate, (∀ t, G.tatePush (Algebra.ofId O (IsLocalRing.ResidueField O)) (s t) = t) ∧ ∀ (n : ℕ) (t t' : G.TateOver (IsLocalRing.ResidueField O)), t.pt n = t'.pt n → (s t).pt n = (s t').pt n := by
  first | exact @GlobalTheory.TateResidue.main | exact GlobalTheory.TateResidue.main | (intros; apply GlobalTheory.TateResidue.main <;> assumption)
end

section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

theorem _root_.GlobalTheory.T.formalGroupDeterminantPowDepth_bounds : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ (i d c : ℕ) (G : LogFGL v d) (u : Fin i → Fin d → C), IsSatFrame v u → 0 ≤ detDepth G u c ∧ detDepth G u c ≤ content v (detPow C i c) ∧ detDepth G u c ≤ (((i * c : ℝ) / (p - 1) : ℝ) : EReal) := by
  first | exact @GlobalTheory.FGDepth.detDepth_bounds | exact GlobalTheory.FGDepth.detDepth_bounds | (intros; apply GlobalTheory.FGDepth.detDepth_bounds <;> assumption)
end
