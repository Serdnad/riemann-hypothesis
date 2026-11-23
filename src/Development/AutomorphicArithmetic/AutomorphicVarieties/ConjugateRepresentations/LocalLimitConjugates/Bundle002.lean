module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.Bundle001
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.ConjugateCuspidalReps.IsConjRepRefl

@[expose] public section

section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

open scoped ENNReal in
private theorem sq_on_le {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    {S : Set G} (hS : MeasurableSet S) (N : ℕ) (hN : ∀ x : G, {γ : Γ | (γ : G) * x ∈ S}.encard ≤ N)
    (F : GlobalTheory.AutomorphicL2Unitary.L2 Γ μ) :
    eLpNorm (GlobalTheory.AutomorphicL2Unitary.lift Γ F) 2 (μ.restrict S) ≤ N * eLpNorm F 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) := by
  have hmeasF : AEStronglyMeasurable (GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ)) μ :=
    GlobalTheory.AutomorphicL2Unitary.aestronglyMeasurable_quotMeasure_iff_lift.mp (Lp.aestronglyMeasurable F)
  have key : ∫⁻ x, ‖GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) x‖ₑ ^ (2 : ℝ) ∂(μ.restrict S) ≤
      (N : ℝ≥0∞) * ∫⁻ q, ‖(F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) q‖ₑ ^ (2 : ℝ) ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) := by
    rw [← lintegral_indicator hS, GlobalTheory.AutomorphicL2Unitary.lintegral_eq_lintegral_tsum (Γ := Γ) ((hmeasF.enorm.pow_const _).indicator hS),
      ← lintegral_const_mul' _ _ (ENNReal.natCast_ne_top N)]
    refine lintegral_mono (fun q => ?_)
    have hq : ∀ γ : Γ, S.indicator (fun x => ‖GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) x‖ₑ ^ (2 : ℝ))
        ((γ : G) * Quotient.out q) = {γ : Γ | (γ : G) * Quotient.out q ∈ S}.indicator
          (fun _ => ‖(F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) q‖ₑ ^ (2 : ℝ)) γ := by
      intro γ
      have hl : GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) ((γ : G) * Quotient.out q) =
          (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) q := by
        rw [GlobalTheory.AutomorphicL2Unitary.lift, GlobalTheory.AutomorphicL2Unitary.mk_mul]
        exact congrArg _ (Quotient.out_eq q)
      by_cases h : (γ : G) * Quotient.out q ∈ S
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show γ ∈ {γ : Γ | (γ : G) * Quotient.out q ∈ S} from h), hl]
      · rw [Set.indicator_of_notMem h,
          Set.indicator_of_notMem (show γ ∉ {γ : Γ | (γ : G) * Quotient.out q ∈ S} from h)]
    rw [tsum_congr hq, ← tsum_subtype, ENNReal.tsum_set_const]
    gcongr
    have h1 := ENat.toENNReal_le.mpr (hN (Quotient.out q))
    simpa using h1
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  have hN2 : (N : ℝ≥0∞) ^ (1 / 2 : ℝ) ≤ N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0
      simp
    · calc (N : ℝ≥0∞) ^ (1 / 2 : ℝ) ≤ (N : ℝ≥0∞) ^ (1 : ℝ) :=
            ENNReal.rpow_le_rpow_of_exponent_le (by exact_mod_cast h0) (by norm_num)
        _ = N := ENNReal.rpow_one _
  calc (∫⁻ x, ‖GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) x‖ₑ ^ (2 : ℝ) ∂(μ.restrict S)) ^ (1 / 2 : ℝ)
      ≤ ((N : ℝ≥0∞) * ∫⁻ q, ‖(F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) q‖ₑ ^ (2 : ℝ) ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow key (by norm_num)
    _ = (N : ℝ≥0∞) ^ (1 / 2 : ℝ) *
        (∫⁻ q, ‖(F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) q‖ₑ ^ (2 : ℝ) ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) ^ (1 / 2 : ℝ) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    _ ≤ _ := by gcongr
  all_goals first | exact Lp.aestronglyMeasurable F | exact hmeasF.restrict

theorem UpperTheory.V.Cj.H.cvCount :
    UpperTheory.V.Cj.H.CvCount := by
  open scoped Pointwise in
    intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ ψ hψ hψc
    obtain ⟨C0, hC0⟩ := hψ.bounded_above_of_compact_support hψc
    have hC : ∀ z, ‖ψ z‖ ≤ max C0 0 := fun z => (hC0 z).trans (le_max_left _ _)
    have hC' : 0 ≤ max C0 0 := le_max_right _ _
    have hMfin : μ (tsupport ψ)⁻¹ ≠ ⊤ := (hψc.isCompact.inv).measure_lt_top.ne
    refine ⟨max C0 0 * (μ (tsupport ψ)⁻¹).toReal ^ (1 / 2 : ℝ), by positivity, ?_⟩
    intro x N hN F
    have hS : MeasurableSet {y : G | ψ (y⁻¹ * x) ≠ 0} :=
      (isOpen_ne_fun (hψ.comp (continuous_inv.mul continuous_const)) continuous_const).measurableSet
    have hSK : μ {y : G | ψ (y⁻¹ * x) ≠ 0} ≤ μ (tsupport ψ)⁻¹ := by
      calc μ {y : G | ψ (y⁻¹ * x) ≠ 0} ≤ μ ((fun y => x⁻¹ * y) ⁻¹' (tsupport ψ)⁻¹) := by
            refine measure_mono (fun y hy => ?_)
            show (x⁻¹ * y)⁻¹ ∈ tsupport ψ
            rw [_root_.mul_inv_rev, inv_inv]
            exact subset_tsupport _ hy
        _ = μ (tsupport ψ)⁻¹ := measure_preimage_mul μ x⁻¹ _
    have hF := sq_on_le Γ μ hS N hN F
    have hmeas : AEStronglyMeasurable (GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ)) μ :=
      GlobalTheory.AutomorphicL2Unitary.aestronglyMeasurable_quotMeasure_iff_lift.mp (Lp.aestronglyMeasurable F)
    have hH := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num)
      (hmeas.restrict (s := {y : G | ψ (y⁻¹ * x) ≠ 0}))
    rw [show (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal) = (1 / 2 : ℝ) by norm_num,
      Measure.restrict_apply_univ] at hH
    have hE : ‖cv ψ F x‖ₑ ≤ (N * eLpNorm F 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) * μ (tsupport ψ)⁻¹ ^ (1 / 2 : ℝ)) *
        ENNReal.ofReal (max C0 0) := by
      calc ‖cv ψ F x‖ₑ ≤ ∫⁻ y, ‖GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) y * ψ (y⁻¹ * x)‖ₑ ∂μ :=
            enorm_integral_le_lintegral_enorm _
        _ ≤ ∫⁻ y, {y : G | ψ (y⁻¹ * x) ≠ 0}.indicator
              (fun y => ‖GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) y‖ₑ) y * ENNReal.ofReal (max C0 0) ∂μ := by
            refine lintegral_mono (fun y => ?_)
            by_cases hy : y ∈ {y : G | ψ (y⁻¹ * x) ≠ 0}
            · rw [Set.indicator_of_mem hy, enorm_mul]
              gcongr
              rw [← ofReal_norm]
              exact ENNReal.ofReal_le_ofReal (hC _)
            · have h0 : ψ (y⁻¹ * x) = 0 := not_not.mp hy
              rw [h0, mul_zero, enorm_zero]
              exact bot_le
        _ = (∫⁻ y in {y : G | ψ (y⁻¹ * x) ≠ 0}, ‖GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) y‖ₑ ∂μ) *
              ENNReal.ofReal (max C0 0) := by
            rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_indicator hS]
        _ = eLpNorm (GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ)) 1 (μ.restrict {y : G | ψ (y⁻¹ * x) ≠ 0}) *
              ENNReal.ofReal (max C0 0) := by
            rw [eLpNorm_one_eq_lintegral_enorm]
            exact hmeas.restrict
        _ ≤ _ := by
            gcongr
            calc _ ≤ _ := hH
              _ ≤ _ := by gcongr
    have hRfin : (N * eLpNorm F 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) * μ (tsupport ψ)⁻¹ ^ (1 / 2 : ℝ)) *
        ENNReal.ofReal (max C0 0) ≠ ⊤ := by
      have h1 : eLpNorm F 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) ≠ ⊤ := Lp.eLpNorm_ne_top F
      have h2 : μ (tsupport ψ)⁻¹ ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hMfin
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top N) h1) h2)
        ENNReal.ofReal_ne_top
    calc ‖cv ψ F x‖ = ‖cv ψ F x‖ₑ.toReal := (toReal_enorm _).symm
      _ ≤ _ := ENNReal.toReal_mono hRfin hE
      _ = max C0 0 * (μ (tsupport ψ)⁻¹).toReal ^ (1 / 2 : ℝ) * N * ‖F‖ := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hC',
          ENNReal.toReal_rpow, ENNReal.toReal_natCast, Lp.norm_def]
        ring
end

section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem exists_orthogonal_decomposition_of_isPos {W : Type} [AddCommGroup W] [Module ℂ W] (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ)
    (M : Submodule ℂ W) (hB : IsPos B M) (F K : Submodule ℂ W) (hF : F ≤ M) (hK : K ≤ F)
    [FiniteDimensional ℂ F] (v : W) (hv : v ∈ F) :
    ∃ a ∈ K, ∃ b ∈ F, v = a + b ∧ ∀ x ∈ K, B x b = 0 := by
  letI core : InnerProductSpace.Core ℂ F :=
    { inner := fun x y => B x y
      conj_inner_symm := fun x y => by
        show (starRingEnd ℂ) (B y x) = B x y
        rw [hB.herm]; simp
      re_inner_nonneg := fun x => hB.nonneg x (hF x.2)
      add_left := fun x y z => by
        show B (x + y : F) z = B x z + B y z
        simp
      smul_left := fun x y r => by
        show B (r • x : F) y = (starRingEnd ℂ) r * B x y
        simp
      definite := fun x hx => Subtype.ext (hB.definite x (hF x.2) hx) }
  letI : NormedAddCommGroup F := InnerProductSpace.Core.toNormedAddCommGroup (cd := core)
  letI : InnerProductSpace ℂ F := InnerProductSpace.ofCore (𝕜 := ℂ) (F := F) inferInstance
  let K' : Submodule ℂ F := K.comap F.subtype
  haveI : CompleteSpace K' := FiniteDimensional.complete ℂ K'
  obtain ⟨y, hy, z, hz, hyz⟩ := K'.exists_add_mem_mem_orthogonal ⟨v, hv⟩
  refine ⟨y, hy, z, z.2, congrArg Subtype.val hyz, fun x hx => ?_⟩
  have := (Submodule.mem_orthogonal K' z).1 hz ⟨x, hK hx⟩ hx
  exact this

private theorem orbit_of_compact_finite_of_open_stabilizer {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (n : W) (U V : Subgroup G)
    (hUc : IsCompact (U : Set G)) (hVo : IsOpen (V : Set G)) (hVn : ∀ u ∈ V, ρ u n = n) :
    ((fun u => ρ u n) '' (U : Set G)).Finite := by
  obtain ⟨t, ht⟩ := hUc.elim_finite_subcover (fun u : U => (fun g => (u : G)⁻¹ * g) ⁻¹' (V : Set G))
    (fun u => hVo.preimage (continuous_const.mul continuous_id))
    (fun g hg => Set.mem_iUnion.2 ⟨⟨g, hg⟩, by simp [V.one_mem]⟩)
  apply ((t : Set U).toFinite.image (fun u : U => ρ (u : G) n)).subset
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨u, hu, hgu⟩ := Set.mem_iUnion₂.1 (ht hg)
  refine ⟨u, hu, ?_⟩
  have hg' : g = (u : G) * ((u : G)⁻¹ * g) := by group
  show ρ (u : G) n = ρ g n
  rw [hg', map_mul, Module.End.mul_apply, hVn _ hgu]

theorem UpperTheory.V.Cj.H.absSS :
    UpperTheory.V.Cj.H.AbsSS := by
  intro G W _ _ _ _ _ ρ M B hB hM hc hsm hfd N hNM hN
  have hρ : ∀ (g h : G) (x : W), ρ g (ρ h x) = ρ (g * h) x := by
    intro g h x
    rw [map_mul, Module.End.mul_apply]
  let N' : Submodule ℂ W :=
    { carrier := {w | w ∈ M ∧ ∀ n ∈ N, B n w = 0}
      add_mem' := fun {a b} ha hb => ⟨M.add_mem ha.1 hb.1, fun n hn => by simp [ha.2 n hn, hb.2 n hn]⟩
      zero_mem' := ⟨M.zero_mem, fun n _ => by simp⟩
      smul_mem' := fun r w hw => ⟨M.smul_mem r hw.1, fun n hn => by simp [hw.2 n hn]⟩ }
  have memN' : ∀ w, w ∈ N' ↔ w ∈ M ∧ ∀ n ∈ N, B n w = 0 := fun w => Iff.rfl
  refine ⟨N', fun w hw => ((memN' w).1 hw).1, ?_, ?_, ?_⟩
  · intro g w hw
    rw [memN'] at hw ⊢
    refine ⟨hM g w hw.1, fun n hn => ?_⟩
    obtain ⟨c, hcg⟩ := hc g
    have hn' : ρ g⁻¹ n ∈ N := hN _ _ hn
    have h1 : ρ g (ρ g⁻¹ n) = n := by rw [hρ, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [← h1, hcg _ (hNM hn') _ hw.1, hw.2 _ hn', mul_zero]
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxN, hxN'⟩ := Submodule.mem_inf.1 hx
    rw [memN'] at hxN'
    exact (Submodule.mem_bot ℂ).2 (hB.definite x (hNM hxN) (hxN'.2 x hxN))
  · refine le_antisymm (sup_le hNM fun w hw => ((memN' w).1 hw).1) ?_
    intro v hv
    obtain ⟨U, hUo, hUc, hUv⟩ := hsm v hv
    haveI := hfd U hUo
    have hFM : Submodule.span ℂ {x | x ∈ M ∧ ∀ u ∈ U, ρ u x = x} ≤ M :=
      Submodule.span_le.2 fun x hx => hx.1
    have hFfix : ∀ x ∈ Submodule.span ℂ {x | x ∈ M ∧ ∀ u ∈ U, ρ u x = x}, ∀ u ∈ U, ρ u x = x := by
      intro x hx u hu
      induction hx using Submodule.span_induction with
      | mem y hy => exact hy.2 u hu
      | zero => simp
      | add y z _ _ hy hz => simp [hy, hz]
      | smul r y _ hy => simp [hy]
    have hvF : v ∈ Submodule.span ℂ {x | x ∈ M ∧ ∀ u ∈ U, ρ u x = x} :=
      Submodule.subset_span ⟨hv, hUv⟩
    obtain ⟨a, haK, b, hbF, hvab, hb⟩ :=
      exists_orthogonal_decomposition_of_isPos B M hB _ (N ⊓ Submodule.span ℂ {x | x ∈ M ∧ ∀ u ∈ U, ρ u x = x}) hFM inf_le_right v hvF
    rw [hvab]
    refine Submodule.add_mem_sup (Submodule.mem_inf.1 haK).1 ((memN' b).2 ⟨hFM hbF, fun n hn => ?_⟩)
    have hinv : ∀ u ∈ U, ∀ x ∈ M, B (ρ u x) b = B x b := by
      intro u hu x hx
      obtain ⟨c, hcu⟩ := hc u
      have h1 := hcu x hx b (hFM hbF)
      rw [hFfix b hbF u hu] at h1
      by_cases hb0 : b = 0
      · simp [hb0]
      have h2 := hcu b (hFM hbF) b (hFM hbF)
      rw [hFfix b hbF u hu] at h2
      have hbb : B b b ≠ 0 := fun h => hb0 (hB.definite b (hFM hbF) h)
      have hc1 : c = 1 := by
        have h3 : (c - 1) * B b b = 0 := by rw [sub_mul, ← h2]; ring
        rcases mul_eq_zero.1 h3 with h | h
        · exact sub_eq_zero.1 h
        · exact absurd h hbb
      rw [h1, hc1, one_mul]
    obtain ⟨V, hVo, -, hVn⟩ := hsm n (hNM hn)
    have hfin := orbit_of_compact_finite_of_open_stabilizer ρ n U V hUc hVo hVn
    have hmemS : ∀ x, x ∈ hfin.toFinset ↔ ∃ g ∈ U, ρ g n = x := by
      intro x
      rw [Set.Finite.mem_toFinset]
      rfl
    have hSN : ∀ x ∈ hfin.toFinset, x ∈ N ∧ B x b = B n b := by
      intro x hx
      obtain ⟨g, hg, rfl⟩ := (hmemS x).1 hx
      exact ⟨hN g n hn, hinv g hg n (hNM hn)⟩
    have hsN : (∑ x ∈ hfin.toFinset, x) ∈ N := Submodule.sum_mem _ fun x hx => (hSN x hx).1
    have hsfix : ∀ u ∈ U, ρ u (∑ x ∈ hfin.toFinset, x) = ∑ x ∈ hfin.toFinset, x := by
      intro u hu

      rw [map_sum]
      refine Finset.sum_nbij' (fun x => ρ u x) (fun x => ρ u⁻¹ x) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
      · intro x hx
        obtain ⟨g, hg, rfl⟩ := (hmemS x).1 hx
        exact (hmemS _).2 ⟨u * g, U.mul_mem hu hg, (hρ u g n).symm⟩
      · intro x hx
        obtain ⟨g, hg, rfl⟩ := (hmemS x).1 hx
        exact (hmemS _).2 ⟨u⁻¹ * g, U.mul_mem (U.inv_mem hu) hg, (hρ u⁻¹ g n).symm⟩
      · intro x _
        rw [hρ, inv_mul_cancel, map_one, Module.End.one_apply]
      · intro x _
        rw [hρ, mul_inv_cancel, map_one, Module.End.one_apply]
    have hsF : (∑ x ∈ hfin.toFinset, x) ∈ Submodule.span ℂ {x | x ∈ M ∧ ∀ u ∈ U, ρ u x = x} :=
      Submodule.subset_span ⟨hNM hsN, hsfix⟩
    have hzero := hb _ (Submodule.mem_inf.2 ⟨hsN, hsF⟩)

    rw [map_sum, LinearMap.sum_apply, Finset.sum_congr rfl fun x hx => (hSN x hx).2,
    Finset.sum_const, nsmul_eq_mul] at hzero
    have hcard : (hfin.toFinset.card : ℂ) ≠ 0 := by
      have : n ∈ hfin.toFinset := (hmemS n).2 ⟨1, U.one_mem, by simp⟩
      exact_mod_cast (Finset.card_pos.2 ⟨n, this⟩).ne'
    exact (mul_eq_zero.1 hzero).resolve_left hcard
end

section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.ropComm :
    UpperTheory.V.Cj.H.RopComm := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ T hT f hf F
  have hF := GlobalTheory.AutomorphicL2Unitary.isRepOp_Rop (Γ := Γ) (μ := μ) hf F
  have hTF := GlobalTheory.AutomorphicL2Unitary.isRepOp_Rop (Γ := Γ) (μ := μ) hf (T F)
  rw [hF.2, hTF.2]
  refine (T.integral_comp_comm hF.1).symm.trans ?_
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show T (f g • (GlobalTheory.AutomorphicL2Unitary.R Γ μ g) F) = f g • (GlobalTheory.AutomorphicL2Unitary.R Γ μ g) (T F)
  rw [map_smul, hT g F]
end

section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem UpperTheory.V.Cj.H.absInv_low {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (x v : H) (s : ℝ)
    (h : inner ℂ x v = inner ℂ v x) : |s| * ‖v‖ ≤ ‖x + (Complex.I * s) • v‖ := by
  have hre : (inner ℂ x v).im = 0 := by
    have e := congrArg Complex.im h
    rw [← inner_conj_symm v x, Complex.conj_im] at e
    linarith
  have hsq : ‖x + (Complex.I * s) • v‖ ^ 2 = ‖x‖ ^ 2 + (|s| * ‖v‖) ^ 2 := by
    rw [@norm_add_sq ℂ, inner_smul_right, norm_smul]
    have hn : ‖Complex.I * (s : ℂ)‖ = |s| := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [hn]
    simp [Complex.mul_re, hre]
  have h0 : 0 ≤ |s| * ‖v‖ := mul_nonneg (abs_nonneg s) (norm_nonneg v)
  nlinarith [norm_nonneg (x + (Complex.I * s) • v), sq_nonneg ‖x‖]

theorem UpperTheory.V.Cj.H.absInv :
    UpperTheory.V.Cj.H.AbsInv := by
  intro H _ _ _ D A hA s hs hd
  let L : D →ₗ[ℂ] H := D.subtype.comp A + (Complex.I * s) • D.subtype
  have hL : ∀ v, L v = ↑(A v) + (Complex.I * s) • (v : H) := fun v => rfl
  have hs' : 0 < |s| := abs_pos.mpr hs
  have hlow : ∀ v : D, |s| * ‖(v : H)‖ ≤ ‖L v‖ := by
    intro v
    rw [hL]
    exact UpperTheory.V.Cj.H.absInv_low _ _ s (hA v v)
  have hinj : Function.Injective L := by
    intro a b hab
    have h1 := hlow (a - b)
    rw [map_sub, hab, sub_self, norm_zero] at h1
    have h2 : ‖((a - b : D) : H)‖ = 0 :=
      le_antisymm (le_of_mul_le_mul_left (by simpa using h1) hs') (norm_nonneg _)
    rw [norm_eq_zero, Submodule.coe_sub, sub_eq_zero] at h2
    exact Subtype.ext h2
  let R := LinearMap.range L
  let e := LinearEquiv.ofInjective L hinj
  have he : ∀ x : D, ((e x : R) : H) = L x := fun x => LinearEquiv.ofInjective_apply L (h := hinj) x
  let g : R →ₗ[ℂ] H := D.subtype.comp e.symm.toLinearMap
  have hg : ∀ y : R, |s| * ‖g y‖ ≤ ‖(y : H)‖ := by
    intro y
    have h1 : L (e.symm y) = y := by
      have h2 := he (e.symm y)
      rw [LinearEquiv.apply_symm_apply] at h2
      exact h2.symm
    have h3 := hlow (e.symm y)
    rw [h1] at h3
    exact h3
  let gc : R →L[ℂ] H := g.mkContinuous (|s|⁻¹) (fun y => by
    rw [inv_mul_eq_div, le_div_iff₀ hs']
    have := hg y
    change ‖g y‖ * |s| ≤ ‖(y : H)‖
    linarith)
  have hdense : Dense (R : Set H) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top, ← Submodule.orthogonal_orthogonal_eq_closure]
    have hb : Rᗮ = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro w hw
      apply hd w
      intro v
      exact (Submodule.mem_orthogonal' R w).1 hw _ (LinearMap.mem_range_self L v)
    rw [hb, Submodule.bot_orthogonal_eq_top]
  have hdr : DenseRange (R.subtypeL : R → H) := hdense.denseRange_val
  have hui : IsUniformInducing (R.subtypeL : R → H) := isUniformEmbedding_subtype_val.isUniformInducing
  refine ⟨gc.extend R.subtypeL, ?_, ?_⟩
  · intro v
    have h1 := ContinuousLinearMap.extend_eq gc hdr hui ⟨L v, LinearMap.mem_range_self L v⟩
    have h2 : e.symm ⟨L v, LinearMap.mem_range_self L v⟩ = v := by
      rw [LinearEquiv.symm_apply_eq]
      exact Subtype.ext (he v).symm
    calc gc.extend R.subtypeL (↑(A v) + (Complex.I * ↑s) • ↑v)
        = gc ⟨L v, LinearMap.mem_range_self L v⟩ := h1
      _ = ↑v := by
        show ((e.symm ⟨L v, LinearMap.mem_range_self L v⟩ : D) : H) = v
        rw [h2]
  · intro w
    refine hdense.induction (P := fun w => |s| * ‖gc.extend R.subtypeL w‖ ≤ ‖w‖) ?_ ?_ w
    · intro y hy
      have h1 : gc.extend R.subtypeL y = gc ⟨y, hy⟩ :=
        ContinuousLinearMap.extend_eq gc hdr hui ⟨y, hy⟩
      show |s| * ‖gc.extend R.subtypeL y‖ ≤ ‖y‖
      rw [h1]
      exact hg ⟨y, hy⟩
    · exact isClosed_le (continuous_const.mul (continuous_norm.comp (gc.extend R.subtypeL).continuous))
        continuous_norm
end

section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem inf_cont (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) :
    Continuous (infGL E a) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sInf E : Cinf E → Ad E) := (GlobalTheory.CuspRep.continuous_infEq E).prodMk continuous_const
  exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)

private theorem unit_cont (E : Type) [Field E] [NumberField E] (a : ℕ) {X : Type} [TopologicalSpace X]
    (u : X → GL (Fin a) (Cinf E)) (hu : Continuous fun x => (u x).val) : Continuous u := by
  refine Units.continuous_iff.2 ⟨hu, ?_⟩
  simp only [Matrix.coe_units_inv]
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨d, hd⟩ := (Matrix.isUnit_iff_isUnit_det _).1 (u x).isUnit
  refine ContinuousAt.comp (f := fun x => (u x).val) (continuousAt_matrix_inv _ ?_) hu.continuousAt
  rw [← hd]
  exact NormedRing.inverse_continuousAt d

theorem UpperTheory.V.Cj.H.smDiv :
    UpperTheory.V.Cj.H.SmDiv := by
  intro E _ _ _ a φ u w
  refine ⟨fun g => ?_, fun Z hZ h0 hw g x hx => ?_⟩
  · refine ((φ.2 g).mul (u.2 g)).congr fun x hx => ?_
    have h : IsUnit (Matrix.of x) := hx
    simp only [chart, dif_pos h]
  · have h : IsUnit (Matrix.of x) := hx
    have e : ∀ y ∈ invSet E a, chart (fun g => φ.1 g / w.1 g) g y = chart φ.1 g y * (chart w.1 g y)⁻¹ := by
      intro y hy
      have h' : IsUnit (Matrix.of y) := hy
      simp only [chart, dif_pos h', div_eq_mul_inv]
    by_cases hz : g * infGL E a h.unit ∈ Z
    · have hne : chart w.1 g x ≠ 0 := by
        rw [chart, dif_pos h]
        exact hw _ hz
      exact ((φ.2 g x hx).mul ((w.2 g x hx).inv hne)).congr e (e x hx)
    · let v : invSet E a → GL (Fin a) (Cinf E) := fun y => (show IsUnit (Matrix.of y.1) from y.2).unit
      have hv : Continuous v := unit_cont E a v continuous_subtype_val
      have hc : Continuous fun y : invSet E a => g * infGL E a (v y) :=
        continuous_const.mul ((inf_cont E a).comp hv)
      have ho : IsOpen {y : invSet E a | g * infGL E a (v y) ∉ Z} := hZ.isOpen_compl.preimage hc
      have hn : ∀ᶠ y : invSet E a in 𝓝 ⟨x, hx⟩, g * infGL E a (v y) ∉ Z := ho.mem_nhds hz
      have hv : ∀ᶠ y in 𝓝[invSet E a] x, chart (fun g => φ.1 g / w.1 g) g y = 0 := by
        rw [nhdsWithin_eq_map_subtype_coe hx, eventually_map]
        filter_upwards [hn] with y hy
        have h' : IsUnit (Matrix.of y.1) := y.2
        rw [chart, dif_pos h', h0 _ hy, zero_div]
      exact (contDiffWithinAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hv (hv.self_of_nhdsWithin hx)
end

section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.hdHd :
    UpperTheory.V.Cj.H.HdHd := by
  intro Γ M _ _ _ ρ k b hb
  refine ⟨?_, fun x _ => UpperTheory.V.Cj.A.hdFacts.1 Γ M b x⟩
  exact UpperTheory.V.Cj.A.hdFacts.2.2.2.2.2 Γ Γ M ρ k b hb
end
