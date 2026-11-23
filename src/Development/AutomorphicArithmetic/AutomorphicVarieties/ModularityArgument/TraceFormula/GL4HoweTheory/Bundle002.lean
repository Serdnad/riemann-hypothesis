module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle004

@[expose] public section

section

open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

open Topology Filter in
private theorem lowFix_emb (E : Type) [Field E] [TopologicalSpace E] [IsTopologicalDivisionRing E] (n : ℕ) :
    IsEmbedding (Units.val : GL (Fin n) E → Matrix (Fin n) (Fin n) E) := by
  refine Units.isEmbedding_val_mk' (f := fun A : Matrix (Fin n) (Fin n) E => A⁻¹) ?_ ?_
  · intro A hA
    refine (continuousAt_matrix_inv A ?_).continuousWithinAt
    have hd : A.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det A).1 hA).ne_zero
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hd
  · intro u
    exact (Matrix.coe_units_inv u).symm

open Topology Filter in
private theorem lowFix_ball (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    (γ : ValueGroupWithZero E) (hγ : γ < 1) (W : Set E) (hW : W ∈ nhds (0 : E)) :
    ∃ m : ℕ, ∀ x : E, valuation E x ≤ γ ^ m → x ∈ W := by
  obtain ⟨δ, hδ⟩ := (IsValuativeTopology.mem_nhds_zero_iff W).1 hW
  obtain ⟨m, hm⟩ := exists_pow_lt₀ hγ δ
  exact ⟨m, fun x hx => hδ (lt_of_le_of_lt hx hm)⟩

open Topology Filter in
theorem UpperTheory.V.Z.Tf.L4.lowFix :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (ϖ : Eˣ), valuation E (ϖ : E) = uniformizer E → ∀ (d : ℤ) (U : Set (GL (Fin n) E)), U ∈ nhds (1 : GL (Fin n) E) →
      ∃ a₀ : ℤ, ∀ a ≥ a₀, ∀ b ∈ howeSet n ϖ a (2 * a - d), (∀ i j : Fin n, i < j → (b : Matrix (Fin n) (Fin n) E) i j = 0) → b ∈ U := by
  intro E _ _ _ _ n ϖ hϖ d U hU
  have hlt : valuation E (ϖ : E) < 1 := hϖ ▸ uniformizer_lt_one
  have hpos : 0 < valuation E (ϖ : E) := zero_lt_iff.2 (by simp)
  rw [(lowFix_emb E n).nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨T, hT, hTU⟩ := hU
  have hc : Continuous (fun A : Fin n → Fin n → E => (Matrix.of A + 1 : Matrix (Fin n) (Fin n) E)) :=
    Continuous.add (f := fun A : Fin n → Fin n → E => (Matrix.of A : Matrix (Fin n) (Fin n) E)) continuous_id continuous_const
  have h0 : (fun A : Fin n → Fin n → E => (Matrix.of A + 1 : Matrix (Fin n) (Fin n) E)) ⁻¹' T ∈ nhds (0 : Fin n → Fin n → E) := by
    refine hc.continuousAt.preimage_mem_nhds ?_
    simpa using hT
  have key : ∃ m : ℕ, ∀ A : Fin n → Fin n → E, (∀ i j, valuation E (A i j) ≤ valuation E (ϖ : E) ^ m) →
      Matrix.of A + 1 ∈ T := by
    rw [nhds_pi, Filter.mem_pi'] at h0
    obtain ⟨I, t, ht, htI⟩ := h0
    have h1 : ∀ i, ∃ s : Fin n → Set E, (∀ j, s j ∈ nhds (0 : E)) ∧ Set.pi Set.univ s ⊆ t i := by
      intro i
      have := ht i
      rw [nhds_pi, Filter.mem_pi'] at this
      obtain ⟨J, s, hs, hsJ⟩ := this
      exact ⟨s, hs, fun x hx => hsJ fun j _ => hx j (Set.mem_univ _)⟩
    choose s hs hst using h1
    have hW : (⋂ i, ⋂ j, s i j) ∈ nhds (0 : E) :=
      Filter.iInter_mem.2 fun i => Filter.iInter_mem.2 fun j => hs i j
    obtain ⟨m, hm⟩ := lowFix_ball E _ hlt _ hW
    refine ⟨m, fun A hA => htI fun i _ => hst i fun j _ => ?_⟩
    have := hm _ (hA i j)
    simp only [Set.mem_iInter] at this
    exact this i j
  obtain ⟨m, hm⟩ := key
  refine ⟨max (m : ℤ) |d|, fun a ha b hb hlow => hTU ?_⟩
  have ham : (m : ℤ) ≤ a := le_trans (le_max_left _ _) ha
  have had : |d| ≤ a := le_trans (le_max_right _ _) ha
  have hc0 : 0 ≤ 2 * a - d := by
    have := le_abs_self d
    have := abs_nonneg d
    omega
  have := hm (fun i j => (b : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) (by
    intro i j
    rcases lt_or_ge i j with hij | hij
    · simp [hlow i j hij, Matrix.one_apply_ne hij.ne]
    · refine le_trans (hb i j) ?_
      rw [Units.val_zpow_eq_zpow_val, map_zpow₀, ← zpow_natCast]
      refine zpow_le_zpow_right_of_le_one₀ hpos hlt.le ?_
      have hji : ((j : ℕ) : ℤ) ≤ ((i : ℕ) : ℤ) := by exact_mod_cast hij
      have := mul_nonneg hc0 (sub_nonneg.2 hji)
      omega)
  have e : (Matrix.of (fun i j => (b : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) + 1 : Matrix (Fin n) (Fin n) E) = (b : Matrix (Fin n) (Fin n) E) := by
    ext i j
    simp
  rw [e] at this
  exact this
end

section

open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.V.Z.Tf.L4.howeBall :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (ϖ : Eˣ), valuation E (ϖ : E) = uniformizer E → ∀ (c : ℤ) (ρ : ValueGroupWithZero E), 0 < ρ →
      ∃ a₀ : ℤ, ∀ a ≥ a₀, howeSet n ϖ a c ⊆ ball n ρ := by
  intro E _ _ _ _ n ϖ hϖ c ρ hρ
  have h1 : valuation E (ϖ : E) < 1 := by rw [hϖ]; exact uniformizer_lt_one
  have h0 : 0 < valuation E (ϖ : E) := by rw [hϖ]; exact uniformizer_pos
  haveI : MulArchimedean (ValueGroupWithZero E) := isRankLeOne_iff_mulArchimedean.1 inferInstance
  obtain ⟨N, hN⟩ := exists_pow_lt₀ h1 (Units.mk0 ρ hρ.ne')
  refine ⟨N + |c| * n, fun a ha g hg i j => (hg i j).trans ?_⟩
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀]
  refine le_trans ?_ hN.le
  rw [← zpow_natCast]
  refine zpow_le_zpow_right_of_le_one₀ h0 h1.le ?_
  have hi := i.2
  have hj := j.2
  have h2 : |((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| ≤ n := by
    rw [abs_le]; constructor <;> omega
  have h3 : |c * (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))| ≤ |c| * n := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  have h4 := (abs_le.1 h3).1
  linarith
end

section

open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

namespace UpperTheory.V.Z.Tf.L4

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]

private theorem hc_triv {ψ : AddChar E Circle} {d : Eˣ} (h : HasConductor ψ d) {y : E}
    (hy : valuation E y ≤ valuation E (d : E)) : ψ y = 1 :=
  (h d).2 le_rfl y hy

private theorem hc_lc {ψ : AddChar E Circle} {d : Eˣ} (h : HasConductor ψ d) :
    IsLocallyConstant (fun t : E => (ψ t : ℂ)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro t
  have hd : valuation E (d : E) ≠ 0 := by simp
  have hm : {z : E | valuation E (z - t) < valuation E (d : E)} ∈ nhds t :=
    IsValuativeTopology.mem_nhds_iff'.2 ⟨Units.mk0 _ hd, fun z hz => hz⟩
  filter_upwards [hm] with z hz
  have h1 : ψ (z - t) = 1 := hc_triv h (le_of_lt hz)
  have h2 : ψ z = ψ (z - t) * ψ t := by rw [← AddChar.map_add_eq_mul, sub_add_cancel]
  rw [h2, h1, one_mul]

private theorem hc_cont {n : ℕ} : Continuous (fun x : GL (Fin n) E => GlobalTheory.Whittaker.superDiag x) := by
  unfold GlobalTheory.Whittaker.superDiag
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (Units.continuous_val).matrix_elem i j

private theorem hc_cross {n : ℕ} {ϖ : Eˣ} {a c : ℤ} {x y : GL (Fin n) E} (hx : x ∈ howeSet n ϖ a c)
    (hy : y ∈ howeSet n ϖ a c) {i j : Fin n} (hij : j.val = i.val + 1) :
    valuation E ((((x : Matrix (Fin n) (Fin n) E) - 1) * ((y : Matrix (Fin n) (Fin n) E) - 1)) i j) ≤
      valuation E ((ϖ ^ (2 * a - c) : Eˣ) : E) := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [map_mul, Matrix.sub_apply, Matrix.sub_apply]
  refine (mul_le_mul' (hx i k) (hy k j)).trans (le_of_eq ?_)
  rw [← map_mul, ← Units.val_mul, ← zpow_add]
  congr 3
  rw [hij]
  push_cast
  ring

end UpperTheory.V.Z.Tf.L4

theorem UpperTheory.V.Z.Tf.L4.howeChar :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (ϖ : Eˣ), valuation E (ϖ : E) = uniformizer E → ∀ a c : ℤ, 1 ≤ a →
      ∀ ψ : AddChar E Circle, HasConductor ψ (ϖ ^ (2 * a - c)) →
        IsLocallyConstant (fun x : GL (Fin n) E => (ψ (GlobalTheory.Whittaker.superDiag x) : ℂ)) ∧
        ∀ x ∈ howeSet n ϖ a c, ∀ y ∈ howeSet n ϖ a c,
          ψ (GlobalTheory.Whittaker.superDiag (x * y)) = ψ (GlobalTheory.Whittaker.superDiag x) * ψ (GlobalTheory.Whittaker.superDiag y) := by
  intro E _ _ _ _ n ϖ _ a c _ ψ hψ
  refine ⟨(UpperTheory.V.Z.Tf.L4.hc_lc hψ).comp_continuous UpperTheory.V.Z.Tf.L4.hc_cont, fun x hx y hy => ?_⟩
  set M := ((x : Matrix (Fin n) (Fin n) E) - 1) * ((y : Matrix (Fin n) (Fin n) E) - 1) with hM
  set r : E := ∑ i : Fin n, ∑ j : Fin n with j.val = i.val + 1, M i j with hr
  have hr1 : ψ r = 1 := by
    refine UpperTheory.V.Z.Tf.L4.hc_triv hψ ?_
    refine Valuation.map_sum_le _ fun i _ => Valuation.map_sum_le _ fun j hj => ?_
    exact UpperTheory.V.Z.Tf.L4.hc_cross hx hy (Finset.mem_filter.1 hj).2
  have hs : GlobalTheory.Whittaker.superDiag (x * y) =
      GlobalTheory.Whittaker.superDiag x + GlobalTheory.Whittaker.superDiag y + r := by
    simp only [GlobalTheory.Whittaker.superDiag, hr, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
    have hij : i ≠ j := by
      have := (Finset.mem_filter.1 hj).2
      rintro rfl
      omega
    have e : ((x * y : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
        (x : Matrix (Fin n) (Fin n) E) + (y : Matrix (Fin n) (Fin n) E) + M - 1 := by
      rw [hM, Units.val_mul]
      noncomm_ring
    rw [e, Matrix.sub_apply, Matrix.one_apply_ne hij, sub_zero, Matrix.add_apply, Matrix.add_apply]
  rw [hs, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hr1, mul_one]
end

section

open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

private noncomputable def dg {E : Type} [Field E] (n : ℕ) (β : Eˣ) : GL (Fin n) E :=
  ⟨Matrix.diagonal fun i => ((β ^ (-((i : ℕ) : ℤ)) : Eˣ) : E), Matrix.diagonal fun i => ((β ^ ((i : ℕ) : ℤ) : Eˣ) : E),
    by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext i
      rw [← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one],
    by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext i
      rw [← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one]⟩

private theorem dg_conj {E : Type} [Field E] {n : ℕ} (β : Eˣ) (x : GL (Fin n) E) (i j : Fin n) :
    ((dg n β * x * (dg n β)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j =
      ((β ^ (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : Eˣ) : E) * (x : Matrix (Fin n) (Fin n) E) i j := by
  change (Matrix.diagonal (fun i : Fin n => ((β ^ (-((i : ℕ) : ℤ)) : Eˣ) : E)) * (x : Matrix (Fin n) (Fin n) E) *
    Matrix.diagonal (fun i : Fin n => ((β ^ ((i : ℕ) : ℤ) : Eˣ) : E))) i j = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, sub_eq_add_neg, zpow_add, Units.val_mul]
  ring

theorem UpperTheory.V.Z.Tf.L4.howeConj :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) E) V) (ϖ β : Eˣ) (a c t : ℤ),
      valuation E (β : E) = valuation E ((ϖ ^ t : Eˣ) : E) → ∀ ψ₀ ψ : AddChar E Circle, (∀ x, ψ x = ψ₀ (β * x)) →
      howeSpace π ψ₀ (howeSet n ϖ a (c - t)) ≠ ⊥ → howeSpace π ψ (howeSet n ϖ a c) ≠ ⊥ := by
  intro E _ _ _ _ n V _ _ π ϖ β a c t hβ ψ₀ ψ hψ h
  obtain ⟨w, hw, h0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨π (dg n β)⁻¹ w, fun x hx => ?_, fun e => h0 ?_⟩
  · have hy : dg n β * x * (dg n β)⁻¹ ∈ howeSet n ϖ a (c - t) := fun i j => by
      have e : ((dg n β * x * (dg n β)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j =
          ((β ^ (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : Eˣ) : E) *
            ((x : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) := by
        rw [dg_conj, mul_sub]
        congr 1
        by_cases hij : i = j
        · subst hij; simp
        · simp [Matrix.one_apply_ne hij]
      have e2 : valuation E ((β ^ (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : Eˣ) : E) =
          valuation E ((ϖ ^ (t * (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ))) : Eˣ) : E) := by
        rw [zpow_mul, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val (ϖ ^ t), map_zpow₀, map_zpow₀, hβ]
      rw [e, map_mul, e2, show a + (c - t) * (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) =
        t * (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) + (a + c * (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))) by ring, zpow_add, Units.val_mul, map_mul]
      exact mul_le_mul_right (hx i j) _
    have hs : GlobalTheory.Whittaker.superDiag (dg n β * x * (dg n β)⁻¹) = β * GlobalTheory.Whittaker.superDiag x := by
      simp only [GlobalTheory.Whittaker.superDiag, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
      rw [dg_conj, (Finset.mem_filter.1 hj).2]
      simp
    have h1 := hw _ hy
    rw [hs, ← hψ] at h1
    rw [← map_smul, ← h1, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 2
    group
  · have := congrArg (π (dg n β)) e
    rwa [map_zero, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
end

section

open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

namespace UpperTheory.V.Z.Tf.L4

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}

omit [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem mul_bd {X Y : Matrix (Fin n) (Fin n) E} {s : ValueGroupWithZero E}
    (hX : ∀ i j, valuation E (X i j) ≤ s) (hY : ∀ i j, valuation E (Y i j) ≤ 1) (i j : Fin n) :
    valuation E ((X * Y) i j) ≤ s := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul]
  simpa using mul_le_mul' (hX i l) (hY l j)

omit [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem one_bd (i j : Fin n) : valuation E ((1 : Matrix (Fin n) (Fin n) E) i j) ≤ 1 := by
  rw [Matrix.one_apply]
  split_ifs <;> simp

omit [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem val_bd {g : GL (Fin n) E} (h : ∀ i j, valuation E ((g.val - 1) i j) < 1) (i j : Fin n) :
    valuation E (g.val i j) ≤ 1 := by
  have e : g.val i j = (g.val - 1) i j + (1 : Matrix (Fin n) (Fin n) E) i j := by simp
  rw [e]
  exact Valuation.map_add_le _ (h i j).le (one_bd i j)

omit [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem inv_bd {g : GL (Fin n) E} (h : ∀ i j, valuation E ((g.val - 1) i j) < 1) (i j : Fin n) :
    valuation E ((g⁻¹).val i j) ≤ 1 := by
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ (fun i => valuation E ((g⁻¹).val i j)) ⟨i, Finset.mem_univ _⟩
  refine (hm i (Finset.mem_univ _)).trans ?_
  by_contra hlt
  rw [not_le] at hlt
  have h0 : 0 < valuation E ((g⁻¹).val m j) := lt_of_le_of_lt zero_le hlt
  have e0 : (g⁻¹).val = 1 - (g.val - 1) * (g⁻¹).val := by
    rw [sub_mul, Units.mul_inv]; noncomm_ring
  have e : (g⁻¹).val m j = (1 : Matrix (Fin n) (Fin n) E) m j - ((g.val - 1) * (g⁻¹).val) m j :=
    congrFun (congrFun e0 m) j
  have h1 : valuation E (((g.val - 1) * (g⁻¹).val) m j) < valuation E ((g⁻¹).val m j) := by
    rw [Matrix.mul_apply]
    refine Valuation.map_sum_lt _ h0.ne' fun l _ => ?_
    rw [map_mul]
    calc _ ≤ valuation E ((g.val - 1) m l) * valuation E ((g⁻¹).val m j) :=
          mul_le_mul' le_rfl (hm l (Finset.mem_univ _))
      _ < 1 * valuation E ((g⁻¹).val m j) := mul_lt_mul_of_pos_right (h _ _) h0
      _ = _ := one_mul _
  have h2 := Valuation.map_sub_lt (valuation E) ((one_bd m j).trans_lt hlt) h1
  rw [← e] at h2
  exact lt_irrefl _ h2

private def cg (n : ℕ) (c : Eˣ) (hc : valuation E (c : E) < 1) : Subgroup (GL (Fin n) E) where
  carrier := {g | ∀ i j, valuation E ((g.val - 1) i j) ≤ valuation E (c : E)}
  one_mem' := fun i j => by simp
  mul_mem' := by
    intro x y hx hy i j
    have e : (x * y).val - 1 = (x.val - 1) * y.val + (y.val - 1) := by
      rw [Units.val_mul]; noncomm_ring
    rw [e, Matrix.add_apply]
    exact Valuation.map_add_le _ (mul_bd hx (val_bd fun i j => (hy i j).trans_lt hc) i j) (hy i j)
  inv_mem' := by
    intro x hx i j
    have e : (x⁻¹).val - 1 = -((x.val - 1) * (x⁻¹).val) := by
      rw [sub_mul, Units.mul_inv]; noncomm_ring
    rw [e, Matrix.neg_apply, Valuation.map_neg]
    exact mul_bd hx (inv_bd fun i j => (hx i j).trans_lt hc) i j

private theorem isOpen_cg (n : ℕ) (c : Eˣ) (hc : valuation E (c : E) < 1) :
    IsOpen (cg n c hc : Set (GL (Fin n) E)) := by
  have e : (cg n c hc : Set (GL (Fin n) E)) =
      (fun g : GL (Fin n) E => ((c⁻¹ : Eˣ) : E) • (g.val - 1)) ⁻¹' {A : Matrix (Fin n) (Fin n) E | ∀ i j, A i j ∈ 𝒪[E]} := by
    ext g
    refine forall_congr' fun i => forall_congr' fun j => ?_
    change _ ↔ valuation E (((c⁻¹ : Eˣ) : E) * (g.val - 1) i j) ≤ 1
    rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀,
      inv_mul_le_one₀ ((Valuation.pos_iff _).2 c.ne_zero)]
  rw [e]
  have hc : Continuous fun g : GL (Fin n) E => ((c⁻¹ : Eˣ) : E) • (g.val - 1) :=
    (Units.continuous_val.sub continuous_const).const_smul ((c⁻¹ : Eˣ) : E)
  exact GlobalTheory.SplitFlip.isOpen_intMatrix.preimage hc

private theorem isCompact_cg (n : ℕ) (c : Eˣ) (hc : valuation E (c : E) < 1) :
    IsCompact (cg n c hc : Set (GL (Fin n) E)) :=
  GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ (isOpen_cg n c hc)) fun g hg =>
    (GlobalTheory.SplitFlip.mem_KO_iff g).2
      ⟨val_bd fun i j => (hg i j).trans_lt hc, inv_bd fun i j => (hg i j).trans_lt hc⟩

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem conj_entry (t : Fin n → Eˣ) (g : GL (Fin n) E) (i j : Fin n) :
    ((GlobalTheory.SplitFlip.diagGL t * g * (GlobalTheory.SplitFlip.diagGL t)⁻¹).val - 1) i j =
      (g.val i j - (1 : Matrix (Fin n) (Fin n) E) i j) * ((t i * (t j)⁻¹ : Eˣ) : E) := by
  have e : (GlobalTheory.SplitFlip.diagGL t * g * (GlobalTheory.SplitFlip.diagGL t)⁻¹).val =
      (Matrix.diagonal fun i => (t i : E)) * g.val * Matrix.diagonal fun i => (((t i)⁻¹ : Eˣ) : E) := rfl
  rw [e, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : i = j
  · subst h
    simp [sub_mul, mul_right_comm]
  · simp [Matrix.one_apply_ne h]
    ring

end UpperTheory.V.Z.Tf.L4

theorem UpperTheory.V.Z.Tf.L4.howeGroup :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (ϖ : Eˣ), valuation E (ϖ : E) = uniformizer E → ∀ a c : ℤ, 1 ≤ a →
      ∃ J : Subgroup (GL (Fin n) E), (J : Set (GL (Fin n) E)) = howeSet n ϖ a c ∧ IsOpen (J : Set (GL (Fin n) E)) ∧ IsCompact (J : Set (GL (Fin n) E)) := by
  intro E _ _ _ _ n ϖ hϖ a c ha
  have hlt : valuation E ((ϖ ^ a : Eˣ) : E) < 1 := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ]
    exact zpow_lt_one₀ (by rw [← hϖ]; exact (Valuation.pos_iff _).2 ϖ.ne_zero) uniformizer_lt_one (by omega)
  let t : Fin n → Eˣ := fun i => ϖ ^ (-(c * ((i : ℕ) : ℤ)))
  let d : GL (Fin n) E := GlobalTheory.SplitFlip.diagGL t
  let φ : GL (Fin n) E ≃ₜ GL (Fin n) E := (Homeomorph.mulLeft d).trans (Homeomorph.mulRight d⁻¹)
  refine ⟨(cg n (ϖ ^ a) hlt).comap (MulAut.conj d).toMonoidHom, ?_, (isOpen_cg n _ hlt).preimage φ.continuous,
    φ.isCompact_preimage.2 (isCompact_cg n _ hlt)⟩
  ext g
  change (∀ i j, valuation E (((d * g * d⁻¹).val - 1) i j) ≤ valuation E ((ϖ ^ a : Eˣ) : E)) ↔ _
  refine forall_congr' fun i => forall_congr' fun j => ?_
  have e : (ϖ ^ a : Eˣ) = ϖ ^ (a + c * (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))) * (t i * (t j)⁻¹) := by
    simp only [t]
    rw [← zpow_neg, ← zpow_add, ← zpow_add]
    congr 1
    ring
  rw [conj_entry, e, Units.val_mul (ϖ ^ (a + _)), map_mul, map_mul]
  exact mul_le_mul_iff_left₀ ((Valuation.pos_iff (valuation E)).2 (t i * (t j)⁻¹).ne_zero)
end
