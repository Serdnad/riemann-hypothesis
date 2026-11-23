module

public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle031
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.IsSimpleTriv

@[expose] public section

section

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.ZuckCasSplit

open Formalism.FourierDecayAlt.ThreeDimData CompanionTheory.D.Upq.Sm
open PI.UpqRep (InLieHpk)

variable {k r : ℕ}

theorem hpk_herm (k r : ℕ) : (Formalism.QuantumDeterminants.Hpk k r)ᴴ = Formalism.QuantumDeterminants.Hpk k r := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
  split_ifs <;> first | omega | simp

theorem hpk_row (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    ∃ (j₀ : Fin (2 * r + k + 1)) (s : ℂ), s * s = 1 ∧ (∀ j, Formalism.QuantumDeterminants.Hpk k r i j = if j = j₀ then s else 0) ∧
      ∀ j, Formalism.QuantumDeterminants.Hpk k r j₀ j = if j = i then s else 0 := by
  have hi := i.2
  by_cases h : r ≤ i.1 ∧ i.1 ≤ r + k
  · refine ⟨i, if i.1 = r + k then -1 else 1, by split_ifs <;> simp, fun j => ?_, fun j => ?_⟩ <;>
    · have hj := j.2
      simp only [Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
      split_ifs <;> first | rfl | omega
  · refine ⟨⟨2 * r + k - i.1, by omega⟩, 1, by simp, fun j => ?_, fun j => ?_⟩ <;>
    · have hj := j.2
      simp only [Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
      split_ifs <;> first | rfl | omega

theorem hpk_sq (k r : ℕ) : Formalism.QuantumDeterminants.Hpk k r * Formalism.QuantumDeterminants.Hpk k r = 1 := by
  ext i j
  obtain ⟨j₀, s, hs, h1, h2⟩ := hpk_row k r i
  simp only [Matrix.mul_apply, h1, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, h2,
    Matrix.one_apply]
  by_cases hij : i = j
  · simp [hij, hs]
  · simp [hij, Ne.symm hij]

theorem flip_facts {n : ℕ} (Hm Y : Matrix (Fin n) (Fin n) ℂ) (h1 : Hmᴴ = Hm) (h2 : Hm * Hm = 1) :
    (Hm * Yᴴ * Hm)ᴴ * Hm = Hm * Y ∧ Hm * (Hm * Yᴴ * Hm) = Yᴴ * Hm := by
  constructor
  · simp only [Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, h2,
      Matrix.mul_one]
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem reH_lie (Y : Mx k r) : InLieHpk k r (reH k r Y) := by
  obtain ⟨h3, h4⟩ := flip_facts _ Y (hpk_herm k r) (hpk_sq k r)
  show (reH k r Y)ᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * reH k r Y = 0
  simp only [reH, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_neg, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg, h3, h4]
  have : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [this, ← smul_add]
  abel_nf
  simp

theorem imH_lie (Y : Mx k r) : InLieHpk k r (imH k r Y) := by
  obtain ⟨h3, h4⟩ := flip_facts _ Y (hpk_herm k r) (hpk_sq k r)
  show (imH k r Y)ᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * imH k r Y = 0
  simp only [imH, sub_neg_eq_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, h3, h4]
  have : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by
    simp
  rw [this, neg_smul, add_comm (Yᴴ * _), neg_add_cancel]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem diff_entry {F : FRep k r} (hF : F.OK) {X : Mx k r} (hX : InLieHpk k r X) (c d : F.ι) :
    HasDerivAt (fun t : ℝ => F.ρ (NormedSpace.exp ((t : ℂ) • X)) c d) (F.dR X c d) 0 := by
  have h1 : PI.UpqRep.inUH (PI.UpqRep.Hpk k r) 1 := by simp [PI.UpqRep.inUH]
  obtain ⟨U, G, hU, h1U, hG, hfG⟩ := hF.smooth c d 1 h1
  have hd : HasDerivAt (fun t => ex X t) X 0 := by
    simpa using hasDerivAt_mul_ex 1 X
  exact (hasDerivAt_local (A := {g | PI.UpqRep.inUH (PI.UpqRep.Hpk k r) g}) (f := fun g => F.ρ g c d)
    (ex_mem_of_lie hX) (ex_zero X) hd hU h1U hG hfG).differentiableAt.hasDerivAt

theorem dR_tens {F F' : FRep k r} (hF : F.OK) (hF' : F'.OK) {X : Mx k r} (hX : InLieHpk k r X) :
    (F.tens F').dR X = F.dR X ⊗ₖ (1 : Matrix F'.ι F'.ι ℂ) + (1 : Matrix F.ι F.ι ℂ) ⊗ₖ F'.dR X := by
  ext ⟨c, c'⟩ ⟨d, d'⟩
  have h := ((diff_entry hF hX c d).mul (diff_entry hF' hX c' d')).deriv
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hF.one, hF'.one] at h
  exact h

theorem dC_tens {F F' : FRep k r} (hF : F.OK) (hF' : F'.OK) (Y : Mx k r) :
    (F.tens F').dC Y = F.dC Y ⊗ₖ (1 : Matrix F'.ι F'.ι ℂ) + (1 : Matrix F.ι F.ι ℂ) ⊗ₖ F'.dC Y := by
  simp only [FRep.dC, dR_tens hF hF' (reH_lie Y), dR_tens hF hF' (imH_lie Y), Matrix.add_kronecker,
    Matrix.kronecker_add, Matrix.smul_kronecker, Matrix.kronecker_smul, smul_add]
  abel

section Lin

set_option linter.unusedSectionVars false

variable {ι κ V : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [AddCommGroup V] [Module ℂ V]

theorem mAct_apply (A : Matrix κ ι ℂ) (x : ι → V) (c : κ) : mAct A x c = ∑ d, A c d • x d := by
  simp [mAct]

theorem mAct_add (A B : Matrix ι ι ℂ) : (mAct (A + B) : Module.End ℂ (ι → V)) = mAct A + mAct B := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp [mAct_apply, add_smul, Finset.sum_add_distrib]

theorem mAct_sum {α : Type} (s : Finset α) (A : α → Matrix ι ι ℂ) :
    (mAct (∑ a ∈ s, A a) : Module.End ℂ (ι → V)) = ∑ a ∈ s, mAct (A a) := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp only [mAct_apply, Matrix.sum_apply, LinearMap.sum_apply, Finset.sum_apply, Finset.sum_smul]
  exact Finset.sum_comm

theorem mAct_mul (A B : Matrix ι ι ℂ) : (mAct A * mAct B : Module.End ℂ (ι → V)) = mAct (A * B) := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp only [Module.End.mul_apply, mAct_apply, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

theorem dOp_mul (S T : Module.End ℂ V) : (dOp ι (S * T) : Module.End ℂ (ι → V)) = dOp ι S * dOp ι T := rfl

theorem dOp_sum {α : Type} (s : Finset α) (T : α → Module.End ℂ V) :
    (dOp ι (∑ a ∈ s, T a) : Module.End ℂ (ι → V)) = ∑ a ∈ s, dOp ι (T a) := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp [dOp]

theorem left_factor_action_mul (f g : Module.End ℂ (ι → V)) :
    (on1 (f * g) : Module.End ℂ (ι × κ → V)) = on1 f * on1 g := rfl

theorem right_factor_action_mul (f g : Module.End ℂ (κ → V)) :
    (on2 (f * g) : Module.End ℂ (ι × κ → V)) = on2 f * on2 g := rfl

theorem left_factor_action_add (f g : Module.End ℂ (ι → V)) :
    (on1 (f + g) : Module.End ℂ (ι × κ → V)) = on1 f + on1 g := rfl

theorem right_factor_action_add (f g : Module.End ℂ (κ → V)) :
    (on2 (f + g) : Module.End ℂ (ι × κ → V)) = on2 f + on2 g := rfl

theorem left_factor_action_sum {α : Type} (s : Finset α) (T : α → Module.End ℂ (ι → V)) :
    (on1 (∑ a ∈ s, T a) : Module.End ℂ (ι × κ → V)) = ∑ a ∈ s, on1 (T a) := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp [on1]

theorem right_factor_action_sum {α : Type} (s : Finset α) (T : α → Module.End ℂ (κ → V)) :
    (on2 (∑ a ∈ s, T a) : Module.End ℂ (ι × κ → V)) = ∑ a ∈ s, on2 (T a) := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp [on2]

theorem left_factor_action_diag_op (T : Module.End ℂ V) : (on1 (dOp ι T) : Module.End ℂ (ι × κ → V)) = dOp (ι × κ) T := rfl

theorem right_factor_action_diag_op (T : Module.End ℂ V) : (on2 (dOp κ T) : Module.End ℂ (ι × κ → V)) = dOp (ι × κ) T := rfl

theorem left_factor_action_kronecker (A : Matrix ι ι ℂ) :
    (on1 (mAct A) : Module.End ℂ (ι × κ → V)) = mAct (A ⊗ₖ (1 : Matrix κ κ ℂ)) := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp [on1, mAct_apply, Fintype.sum_prod_type, Matrix.one_apply, LinearMap.funLeft_apply, kroneckerMap]

theorem right_factor_action_kronecker (A : Matrix κ κ ℂ) :
    (on2 (mAct A) : Module.End ℂ (ι × κ → V)) = mAct ((1 : Matrix ι ι ℂ) ⊗ₖ A) := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp [on2, mAct_apply, Fintype.sum_prod_type, Matrix.one_apply, LinearMap.funLeft_apply, kroneckerMap]

theorem expand {R α : Type} [Ring R] [Fintype α] (E A B : α → α → R) (Q : R)
    (h1 : ∑ a, ∑ b, A a b * B b a = Q) (h2 : ∑ a, ∑ b, B a b * A b a = Q) :
    ∑ a, ∑ b, (E a b + (A a b + B a b)) * (E b a + (A b a + B b a)) =
      ∑ a, ∑ b, (E a b + A a b) * (E b a + A b a) + ∑ a, ∑ b, (E a b + B a b) * (E b a + B b a)
        - ∑ a, ∑ b, E a b * E b a + (Q + Q) := by
  nth_rewrite 1 [← h1]
  rw [← h2]
  simp only [mul_add, add_mul, Finset.sum_add_distrib]
  abel

end Lin

theorem casSplit : CasSplit := by
  intro k r F F' U hF hF'
  simp only [cas, cas1, cas2, casR, L, left_factor_action_sum, right_factor_action_sum, left_factor_action_mul, right_factor_action_mul, left_factor_action_add, right_factor_action_add, left_factor_action_diag_op, right_factor_action_diag_op,
    left_factor_action_kronecker, right_factor_action_kronecker, dC_tens hF hF', mAct_add, dOp_sum, dOp_mul, two_smul]
  refine expand (fun a b => dOp (F.ι × F'.ι) (U.dC (Matrix.single a b 1)))
    (fun a b => mAct (F.dC (Matrix.single a b 1) ⊗ₖ (1 : Matrix F'.ι F'.ι ℂ)))
    (fun a b => mAct ((1 : Matrix F.ι F.ι ℂ) ⊗ₖ F'.dC (Matrix.single a b 1))) _ ?_ ?_
  · simp only [mAct_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul, qMat, mAct_sum]
  · rw [Finset.sum_comm]
    simp only [mAct_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul, qMat, mAct_sum]

end GlobalTheory.CompanionTheory.ZuckCasSplit

end
end

section

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.ZuckHomCat

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData CompanionTheory.D.Upq.Sm

variable {k r : ℕ}

theorem sn_nonneg (X : Obj k r) (W : List (Mx k r)) (x : M X) : 0 ≤ sn X W x :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem sn_add_le (X : Obj k r) {W : List (Mx k r)} (hW : LieWd k r W) (x y : M X) :
    sn X W (x + y) ≤ sn X W x + sn X W y := by
  unfold sn
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun c _ => ?_
  simp only [dsigW_eq', Pi.add_apply, Submodule.coe_add]
  rw [dsW_add X.2.repOn (x c).2 (y c).2 (fun Y hY t => ex_mem_of_lie (hW Y hY) t)]
  exact norm_add_le _ _

theorem sn_smul (X : Obj k r) {W : List (Mx k r)} (hW : LieWd k r W) (a : ℂ) (x : M X) :
    sn X W (a • x) = ‖a‖ * sn X W x := by
  unfold sn
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [dsigW_eq', Pi.smul_apply, Submodule.coe_smul]
  rw [dsW_smul X.2.repOn (x c).2 a (fun Y hY t => ex_mem_of_lie (hW Y hY) t)]
  exact norm_smul _ _

theorem sum_nonneg' (X : Obj k r) (Ws : List (List (Mx k r))) (x : M X) :
    0 ≤ (Ws.map fun W' => sn X W' x).sum :=
  List.sum_nonneg fun t ht => by
    obtain ⟨W, -, rfl⟩ := List.mem_map.1 ht
    exact sn_nonneg X W x

def Dom (X : Obj k r) (φ : M X → ℝ) : Prop :=
  ∃ (C : ℝ) (Ws : List (List (Mx k r))), (∀ W' ∈ Ws, LieWd k r W') ∧
    ∀ x, φ x ≤ C * (Ws.map fun W' => sn X W' x).sum

theorem Dom.mono {X : Obj k r} {φ ψ : M X → ℝ} (h : Dom X ψ) (hle : ∀ x, φ x ≤ ψ x) : Dom X φ := by
  obtain ⟨C, Ws, hW, hb⟩ := h
  exact ⟨C, Ws, hW, fun x => (hle x).trans (hb x)⟩

theorem Dom.zero (X : Obj k r) : Dom X fun _ => 0 :=
  ⟨0, [], by simp, fun _ => by simp⟩

theorem Dom.add {X : Obj k r} {φ ψ : M X → ℝ} (h : Dom X φ) (h' : Dom X ψ) :
    Dom X fun x => φ x + ψ x := by
  obtain ⟨C, Ws, hW, hb⟩ := h
  obtain ⟨C', Ws', hW', hb'⟩ := h'
  refine ⟨|C| + |C'|, Ws ++ Ws', fun W hm => (List.mem_append.1 hm).elim (hW W) (hW' W), fun x => ?_⟩
  rw [List.map_append, List.sum_append]
  have h1 := sum_nonneg' X Ws x
  have h2 := sum_nonneg' X Ws' x
  have h3 := hb x
  have h4 := hb' x
  have h5 := mul_le_mul_of_nonneg_right (le_abs_self C) h1
  have h6 := mul_le_mul_of_nonneg_right (le_abs_self C') h2
  have h7 := mul_nonneg (abs_nonneg C) h2
  have h8 := mul_nonneg (abs_nonneg C') h1
  nlinarith

theorem Dom.mul {X : Obj k r} {φ : M X → ℝ} (h : Dom X φ) {a : ℝ} (ha : 0 ≤ a) :
    Dom X fun x => a * φ x := by
  obtain ⟨C, Ws, hW, hb⟩ := h
  refine ⟨a * C, Ws, hW, fun x => ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hb x) ha

theorem Dom.listSum {X : Obj k r} {ι : Type} (φ : ι → M X → ℝ) :
    ∀ l : List ι, (∀ i ∈ l, Dom X (φ i)) → Dom X fun x => (l.map fun i => φ i x).sum
  | [], _ => by simpa using Dom.zero X
  | i :: l, h => by
    simpa using (h i List.mem_cons_self).add
      (Dom.listSum φ l fun j hj => h j (List.mem_cons_of_mem _ hj))

theorem homCat : HomCat := by
  intro k r
  refine ⟨fun X Y => ⟨fun W hW => ?_, fun g _ => ?_⟩, fun X Y f f' hf hf' => ⟨fun W hW => ?_, fun g hg => ?_⟩,
    fun X Y c f hf => ⟨fun W hW => ?_, fun g hg => ?_⟩, fun X => ⟨fun W hW => ?_, fun g _ => ?_⟩,
    fun X Y Z f f' hf hf' => ⟨fun W hW => ?_, fun g hg => ?_⟩⟩
  · refine (Dom.zero X).mono fun x => ?_
    have := sn_smul Y hW 0 0
    rw [zero_smul, norm_zero, zero_mul] at this
    exact this.le
  · rw [LinearMap.zero_comp, LinearMap.comp_zero]
  · exact (Dom.add (hf.cont W hW) (hf'.cont W hW)).mono fun x => sn_add_le Y hW _ _
  · rw [LinearMap.add_comp, LinearMap.comp_add, hf.equiv g hg, hf'.equiv g hg]
  · exact (Dom.mul (hf.cont W hW) (norm_nonneg c)).mono fun x => (sn_smul Y hW _ _).le
  · rw [LinearMap.smul_comp, LinearMap.comp_smul, hf.equiv g hg]
  · exact ⟨1, [W], by simpa using hW, fun x => by simp⟩
  · rw [LinearMap.id_comp, LinearMap.comp_id]
  · obtain ⟨C, Ws, hWs, hb⟩ := hf'.cont W hW
    refine ((Dom.listSum (X := X) (fun W' x => sn Y W' (f x)) Ws
      fun W' h' => hf.cont W' (hWs W' h')).mul (abs_nonneg C)).mono fun x => ?_
    exact (hb (f x)).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (sum_nonneg' Y Ws _))
  · rw [LinearMap.comp_assoc, hf.equiv g hg, ← LinearMap.comp_assoc, hf'.equiv g hg, LinearMap.comp_assoc]

end GlobalTheory.CompanionTheory.ZuckHomCat

end
end

section

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.ZuckUIso

open CompanionTheory.D.Upq.Sm
open PI.UpqRep (InLieHpk dsigW)

section Gen

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {H H' : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [NormedAddCommGroup H'] [NormedSpace ℂ H']
  {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)} {σ' : Mat n → (H' →L[ℂ] H')}

theorem isSm_map (e : H →L[ℂ] H') (he : ∀ g ∈ G, ∀ x, e (σ g x) = σ' g (e x)) {v : H} (hv : IsSm G σ v) :
    IsSm G σ' (e v) :=
  (SmOn.clm hv (e.restrictScalars ℝ)).congr fun g hg => (he g hg v).symm

theorem ds_map (h : RepOn G σ) (e : H →L[ℂ] H') (he : ∀ g ∈ G, ∀ x, e (σ g x) = σ' g (e x)) {X : Mat n}
    (hX : ∀ t, ex X t ∈ G) {v : H} (hv : IsSm G σ v) : ds σ' X (e v) = e (ds σ X v) := by
  have h1 := (e.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hv.differentiableAt h hX).hasDerivAt
  have h2 : (fun t => σ' (ex X t) (e v)) = (e.restrictScalars ℝ) ∘ fun t => σ (ex X t) v := by
    ext t; exact (he _ (hX t) v).symm
  unfold ds
  rw [h2, h1.deriv]; rfl

theorem dsW_map (h : RepOn G σ) (e : H →L[ℂ] H') (he : ∀ g ∈ G, ∀ x, e (σ g x) = σ' g (e x))
    {v : H} (hv : IsSm G σ v) : ∀ {W : List (Mat n)}, LieW G W → dsW σ' W (e v) = e (dsW σ W v)
  | [], _ => rfl
  | X :: W, hW => by
    have hW' : LieW G W := fun Y hY => hW Y (List.mem_cons_of_mem _ hY)
    rw [dsW_cons, dsW_cons, dsW_map h e he hv hW',
      ds_map h e he (hW X List.mem_cons_self) (hv.dsW h hW')]

end Gen

variable {k r : ℕ}

def res (U U' : URep k r) (e : U.R.H →L[ℂ] U'.R.H) (he : ∀ g ∈ GG k r, ∀ x, e (U.R.σ g x) = U'.R.σ g (e x)) :
    U.R.smSub →ₗ[ℂ] U'.R.smSub :=
  (e : U.R.H →ₗ[ℂ] U'.R.H).restrict fun v hv => isSm_map (G := GG k r) e he (v := v) hv

theorem res_coe (U U' : URep k r) (e : U.R.H →L[ℂ] U'.R.H)
    (he : ∀ g ∈ GG k r, ∀ x, e (U.R.σ g x) = U'.R.σ g (e x)) (v : U.R.smSub) :
    (res U U' e he v : U'.R.H) = e v := rfl

theorem isHom_res (F : FRep k r) (U U' : URep k r) (e : U.R.H →L[ℂ] U'.R.H)
    (he : ∀ g ∈ GG k r, ∀ x, e (U.R.σ g x) = U'.R.σ g (e x)) (hn : ∀ x, ‖e x‖ = ‖x‖) :
    IsHom (F, U) (F, U') (dOp F.ι (res U U' e he)) := by
  constructor
  · intro W hW
    refine ⟨1, [W], by simpa using hW, fun x => le_of_eq ?_⟩
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul, sn]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [dsigW_eq', dsigW_eq']
    change ‖dsW U'.R.σ W (e (x c : U.R.H))‖ = _
    rw [dsW_map U.repOn e he (v := (x c : U.R.H)) (x c).2 (fun X hX t => ex_mem_of_lie (hW X hX) t), hn]
  · intro g hg
    have h1 : res U U' e he ∘ₗ U.sig g = U'.sig g ∘ₗ res U U' e he := by
      ext v
      simp only [LinearMap.comp_apply, res_coe, URep.sig_coe _ hg, he g hg]
    refine LinearMap.ext fun x => funext fun c => ?_
    have h2 : ∀ d, res U U' e he (U.sig g (x d)) = U'.sig g (res U U' e he (x d)) :=
      fun d => LinearMap.congr_fun h1 (x d)
    simp [CompanionTheory.Zuck.act, mAct, dOp, h2]

theorem uIso : UIso := by
  rintro k r F U U' ⟨e, he⟩
  have he' : ∀ g ∈ GG k r, ∀ x, e.symm (U'.R.σ g x) = U.R.σ g (e.symm x) := fun g hg x => by
    apply e.injective
    rw [he g hg, e.apply_symm_apply, e.apply_symm_apply]
  refine ⟨dOp F.ι (res U U' (e.toContinuousLinearEquiv : U.R.H →L[ℂ] U'.R.H) he),
    dOp F.ι (res U' U (e.symm.toContinuousLinearEquiv : U'.R.H →L[ℂ] U.R.H) he'),
    isHom_res F U U' _ he e.norm_map, isHom_res F U' U _ he' e.symm.norm_map, ?_, ?_⟩
  · exact LinearMap.ext fun x => funext fun c => Subtype.ext (e.symm_apply_apply _)
  · exact LinearMap.ext fun x => funext fun c => Subtype.ext (e.apply_symm_apply _)

end GlobalTheory.CompanionTheory.ZuckUIso

end
end

section

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

namespace GlobalTheory.CompanionTheory.ZuckTens

open scoped Matrix.Norms.Elementwise

theorem okTens : OKTens := by
  intro k r F F' hF hF'
  refine ⟨?_, ?_, ?_, ?_⟩
  · show F.ρ 1 ⊗ₖ F'.ρ 1 = 1
    rw [hF.one, hF'.one, Matrix.one_kronecker_one]
  · intro g hg h hh
    show F.ρ (g * h) ⊗ₖ F'.ρ (g * h) = (F.ρ g ⊗ₖ F'.ρ g) * (F.ρ h ⊗ₖ F'.ρ h)
    rw [hF.mul g hg h hh, hF'.mul g hg h hh, Matrix.mul_kronecker_mul]
  · rintro ⟨c, c'⟩ ⟨d, d'⟩ g₀ hg₀
    obtain ⟨U, f, hU, hgU, hf, hfe⟩ := hF.smooth c d g₀ hg₀
    obtain ⟨U', f', hU', hgU', hf', hfe'⟩ := hF'.smooth c' d' g₀ hg₀
    refine ⟨U ∩ U', fun x => f x * f' x, hU.inter hU', ⟨hgU, hgU'⟩,
      (hf.mono Set.inter_subset_left).mul (hf'.mono Set.inter_subset_right), ?_⟩
    intro g hg hin
    have h1 := hfe g hg.1 hin
    have h2 := hfe' g hg.2 hin
    show F.ρ g c d * F'.ρ g c' d' = f g * f' g
    simp only at h1 h2
    rw [h1, h2]
  · obtain ⟨C, hC⟩ := hF.growth
    obtain ⟨C', hC'⟩ := hF'.growth
    refine ⟨C * C', ?_⟩
    rintro g hg ⟨c, c'⟩ ⟨d, d'⟩
    show ‖F.ρ g c d * F'.ρ g c' d'‖ ≤ C * C' * Formalism.FourierDecayAlt.B.gN g ^ (F.deg + F'.deg)
    have h1 := hC g hg c d
    have h2 := hC' g hg c' d'
    rw [norm_mul, pow_add]
    calc _ ≤ (C * Formalism.FourierDecayAlt.B.gN g ^ F.deg) * (C' * Formalism.FourierDecayAlt.B.gN g ^ F'.deg) :=
          mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
      _ = _ := by ring

end GlobalTheory.CompanionTheory.ZuckTens
end

section

open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.creation_product_single_basis : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (l : List (Pos n)) (S : Finset (Pos n)) (w : V),
    l.Nodup → (∀ i ∈ l, i ∉ S) → ∃ c : ℂ, c ≠ 0 ∧
      ((l.map cre).prod : Module.End ℂ (Cn n V)) (Pi.single S w : Cn n V) = c • (Pi.single (S ∪ l.toFinset) w : Cn n V) := by
  first | exact @GlobalTheory.CompanionTheory.Chains.prod_cre_single | exact GlobalTheory.CompanionTheory.Chains.prod_cre_single | (intros; apply GlobalTheory.CompanionTheory.Chains.prod_cre_single <;> assumption)
end

end

section

@[expose] public section

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

theorem _root_.GlobalTheory.T.CasimirSplitting : CasSplit := by
  first | exact @GlobalTheory.CompanionTheory.ZuckCasSplit.casSplit | exact GlobalTheory.CompanionTheory.ZuckCasSplit.casSplit | (intros; apply GlobalTheory.CompanionTheory.ZuckCasSplit.casSplit <;> assumption)

end
end

section

@[expose] public section

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

theorem _root_.GlobalTheory.T.HomCategory : HomCat := by
  first | exact @GlobalTheory.CompanionTheory.ZuckHomCat.homCat | exact GlobalTheory.CompanionTheory.ZuckHomCat.homCat | (intros; apply GlobalTheory.CompanionTheory.ZuckHomCat.homCat <;> assumption)

end
end

section

@[expose] public section

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

theorem _root_.GlobalTheory.T.TensorPowerIntegral : OKTens := by
  first | exact @GlobalTheory.CompanionTheory.ZuckTens.okTens | exact GlobalTheory.CompanionTheory.ZuckTens.okTens | (intros; apply GlobalTheory.CompanionTheory.ZuckTens.okTens <;> assumption)

end
end

section

@[expose] public section

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

theorem _root_.GlobalTheory.T.UnitaryIso : UIso := by
  first | exact @GlobalTheory.CompanionTheory.ZuckUIso.uIso | exact GlobalTheory.CompanionTheory.ZuckUIso.uIso | (intros; apply GlobalTheory.CompanionTheory.ZuckUIso.uIso <;> assumption)

end
end
