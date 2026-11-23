module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle554
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle555
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle534
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle528
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle559
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
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle137

@[expose] public section

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NMulEndo

variable {R : Type} [CommRing R] {d : ℕ}

theorem hasSubst_elim {τ : Type} {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    HasSubst (Sum.elim u v) :=
  hasSubst_of_constantCoeff_zero (by rintro (j | j); exacts [hu j, hv j])

theorem constantCoeff_op (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) {τ : Type} {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) :
    constantCoeff (op μ u v i) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_elim hu hv) (by rintro (j | j); exacts [hu j, hv j]) (hμ i)

theorem subst_op (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) {σ τ : Type}
    {u v : Fin d → MvPowerSeries σ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    {w : σ → MvPowerSeries τ R} (hw : HasSubst w) :
    (fun i => subst w (op μ u v i)) = op μ (fun i => subst w (u i)) (fun i => subst w (v i)) := by
  funext i
  simp only [op, at2]
  rw [subst_comp_subst_apply (hasSubst_elim hu hv) hw]
  congr 1
  funext j
  rcases j with j | j <;> rfl

theorem op_comm {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (hμ : IsLaw μ) {τ : Type}
    {a b : Fin d → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) :
    op μ b a = op μ a b := by
  funext i
  have hs : HasSubst (Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) R))
      (fun j => X (Sum.inl j))) :=
    hasSubst_elim (fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _)
  have hab := hasSubst_elim ha hb
  have h := congrArg (subst (Sum.elim a b)) (hμ.comm i)
  simp only [swap, at2] at h
  rw [subst_comp_subst_apply hs hab] at h
  have e : (fun s => subst (Sum.elim a b) (Sum.elim (fun j => (X (Sum.inr j) :
      MvPowerSeries (Fin d ⊕ Fin d) R)) (fun j => X (Sum.inl j)) s)) = Sum.elim b a := by
    funext s
    rcases s with s | s <;> simp [subst_X hab]
  rw [e] at h
  exact h

theorem op_assoc {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (hμ : IsLaw μ) {τ : Type}
    {a b c : Fin d → MvPowerSeries τ R} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) (hc : ∀ i, constantCoeff (c i) = 0) :
    op μ (op μ a b) c = op μ a (op μ b c) := by
  have hW : HasSubst (Sum.elim a (Sum.elim b c)) :=
    hasSubst_of_constantCoeff_zero (by rintro (j | j | j); exacts [ha j, hb j, hc j])
  have h1 : ∀ i, constantCoeff ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => constantCoeff_X _
  have h2 : ∀ i, constantCoeff ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => constantCoeff_X _
  have h3 : ∀ i, constantCoeff ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => constantCoeff_X _
  have h := congrArg (fun F : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R =>
    fun i => subst (Sum.elim a (Sum.elim b c)) (F i)) hμ.assoc
  try simp only at h
  rw [subst_op μ (constantCoeff_op μ hμ.const h1 h2) h3 hW, subst_op μ h1 h2 hW,
    subst_op μ h1 (constantCoeff_op μ hμ.const h2 h3) hW, subst_op μ h2 h3 hW] at h
  simpa [x1, x2, x3, subst_X hW] using h

theorem op_interchange {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (hμ : IsLaw μ) {τ : Type}
    {a b c e : Fin d → MvPowerSeries τ R} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) (hc : ∀ i, constantCoeff (c i) = 0)
    (he : ∀ i, constantCoeff (e i) = 0) :
    op μ (op μ a b) (op μ c e) = op μ (op μ a c) (op μ b e) := by
  rw [op_assoc hμ ha hb (constantCoeff_op μ hμ.const hc he), ← op_assoc hμ hb hc he,
    op_comm hμ hc hb, op_assoc hμ hc hb he,
    ← op_assoc hμ ha hc (constantCoeff_op μ hμ.const hb he)]

theorem op_zero_zero {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (hμ : IsLaw μ) (τ : Type) :
    op μ (fun _ => (0 : MvPowerSeries τ R)) (fun _ => 0) = fun _ => 0 := by
  have hw : HasSubst (fun _ : Fin d => (0 : MvPowerSeries τ R)) :=
    hasSubst_of_constantCoeff_zero fun _ => map_zero _
  have hz : subst (fun _ : Fin d => (0 : MvPowerSeries τ R)) (0 : MvPowerSeries (Fin d) R) = 0 := by
    rw [← coe_substAlgHom hw, map_zero]
  have h := congrArg (fun F : Fin d → MvPowerSeries (Fin d) R =>
    fun i => subst (fun _ : Fin d => (0 : MvPowerSeries τ R)) (F i)) hμ.unit
  try simp only at h
  rw [subst_op μ (fun i => constantCoeff_X i) (fun _ => map_zero _) hw] at h
  simpa [subst_X hw, hz] using h

theorem subst_nmul_zero {τ : Type} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    {a : Fin d → MvPowerSeries τ R} (ha : ∀ i, constantCoeff (a i) = 0) :
    (fun j => subst a (nmul μ 0 j)) = fun _ => 0 := by
  funext j
  show subst a (0 : MvPowerSeries (Fin d) R) = 0
  rw [← coe_substAlgHom (hasSubst_of_constantCoeff_zero ha), map_zero]

theorem subst_nmul_succ {τ : Type} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) {a : Fin d → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) (k : ℕ) :
    (fun j => subst a (nmul μ (k + 1) j)) = op μ (fun j => subst a (nmul μ k j)) a := by
  have hs := hasSubst_of_constantCoeff_zero ha
  rw [QLogDefect.nmul_succ, subst_op μ (QLogDefect.constantCoeff_nmul hμ k)
    (fun i => constantCoeff_X i) hs]
  congr 1
  funext i
  exact subst_X hs i

theorem constantCoeff_subst_nmul {τ : Type} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) {a : Fin d → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) (k : ℕ) (j : Fin d) :
    constantCoeff (subst a (nmul μ k j)) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero ha) ha
    (QLogDefect.constantCoeff_nmul hμ k j)

theorem subst_nmul_op {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (hμ : IsLaw μ) (k : ℕ)
    {τ : Type} {a b : Fin d → MvPowerSeries τ R} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) :
    (fun j => subst (op μ a b) (nmul μ k j)) =
      op μ (fun j => subst a (nmul μ k j)) (fun j => subst b (nmul μ k j)) := by
  have hab := constantCoeff_op μ hμ.const ha hb
  induction k with
  | zero =>
    rw [subst_nmul_zero μ hab, subst_nmul_zero μ ha, subst_nmul_zero μ hb, op_zero_zero hμ]
  | succ k ih =>
    rw [subst_nmul_succ μ hμ.const hab, ih, subst_nmul_succ μ hμ.const ha,
      subst_nmul_succ μ hμ.const hb,
      op_interchange hμ (constantCoeff_subst_nmul μ hμ.const ha k)
        (constantCoeff_subst_nmul μ hμ.const hb k) ha hb]

theorem isHom_nmul : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R),
    IsLaw μ → ∀ k : ℕ, IsHom μ μ (nmul μ k) := by
  intro R _ d μ hμ k
  refine ⟨QLogDefect.constantCoeff_nmul hμ.const k, fun j => ?_⟩
  have hL : ∀ i, constantCoeff ((fun i => X (Sum.inl i) : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) i) = 0 :=
    fun _ => constantCoeff_X _
  have hR : ∀ i, constantCoeff ((fun i => X (Sum.inr i) : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) i) = 0 :=
    fun _ => constantCoeff_X _
  have hxy : op μ (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R))
      (fun i => X (Sum.inr i)) = μ := by
    funext i
    have e : (Sum.elim (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R))
        (fun i => X (Sum.inr i))) = X := by
      funext s; rcases s with s | s <;> rfl
    show subst _ (μ i) = μ i
    rw [e, subst_self]; rfl
  have h := congrFun (subst_nmul_op hμ k hL hR) j
  rw [hxy] at h
  exact h

end GlobalTheory.NMulEndo
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLogDefect

theorem constantCoeff_defect : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ f : MvPowerSeries (Fin d) Q, QL μ ⊤ f → ∀ n : ℕ, constantCoeff (defect μ n f) = 0 := by
  intro p _ B O Q _ _ _ _ θ _ d μ hμ f hf n
  have hU : ∀ j, constantCoeff (up Q (nmul μ n) j) = 0 := by
    intro j
    simp only [up]
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_nmul hμ.const n j, map_zero]
  unfold defect
  rw [map_sub, constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hU) hU hf.1, sub_zero]
  simp [hf.1]

end GlobalTheory.QLogDefect
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.diffCoeffsInIdeal_subst_of_constantCoeff_zero : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ τ : Type) [Fintype σ] (N : Ideal B) (f : MvPowerSeries σ Q) (u : σ → MvPowerSeries τ B), DIn N f → (∀ i, constantCoeff (u i) = 0) → DIn N (subst (up Q u) f) ∧ (In N f → In N (subst (up Q u) f)) := by
  first | exact @GlobalTheory.QLog.dIn_subst_up | exact GlobalTheory.QLog.dIn_subst_up | (intros; apply GlobalTheory.QLog.dIn_subst_up <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.frobenius_linearCombination_zero_left_ainfFrame : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) (F : BFrame ε) (d k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B), (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → ∀ b : Fin k → F.B, In (⊤ : Ideal F.B) (frob p F.s (comb (Sum.elim (fun _ => 0) b) e) - comb (U.mulVec (fun j => F.σ ((Sum.elim (fun _ => 0) b : Fin d ⊕ Fin k → F.B) j))) e) := by
  first | exact @GlobalTheory.frob_comb_zero_left | exact GlobalTheory.frob_comb_zero_left | (intros; apply GlobalTheory.frob_comb_zero_left <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.coeffsInIdeal_solution_of_unipotent_series_matrix : ∀ {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {d : ℕ} (N : Ideal B) (M : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin d) B)), (∀ i j, constantCoeff (M i j) = if i = j then 1 else 0) → ∀ (v g : Fin d → MvPowerSeries (Fin d) Q), (∀ i, ∑ j, v j * map (algebraMap B Q) (M j i) = g i) → (∀ i, In N (g i)) → ∀ j, In N (v j) := by
  first | exact @GlobalTheory.InvSolve.solve | exact GlobalTheory.InvSolve.solve | (intros; apply GlobalTheory.InvSolve.solve <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.powerSeriesFrobeniusTwist_linearCombination_mod_integral : ∀ (p : ℕ) [Fact p.Prime] (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (σ : B →+* B) (s : Q →+* Q), (∀ b, s (algebraMap B Q b) = algebraMap B Q (σ b)) → ∀ (d : ℕ) (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) Q) (M : Matrix ι ι B), (∀ i, In (⊤ : Ideal B) (frob p s (e i) - comb (fun l => M l i) e)) → ∀ w : ι → B, In (⊤ : Ideal B) (frob p s (comb w e) - comb (M.mulVec fun j => σ (w j)) e) := by
  first | exact @GlobalTheory.FrobStep.frob_comb_step | exact GlobalTheory.FrobStep.frob_comb_step | (intros; apply GlobalTheory.FrobStep.frob_comb_step <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.quasiLogarithmBasis_transitionMatrices_inverse : ∀ {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (e : ι → MvPowerSeries (Fin d) Q) (f : κ → MvPowerSeries (Fin d) Q), IsBasis μ e → IsBasis μ f → ∀ (P : ι → κ → B) (P' : κ → ι → B), (∀ i, In (⊤ : Ideal B) (e i - comb (P i) f)) → (∀ j, In (⊤ : Ideal B) (f j - comb (P' j) e)) → Matrix.of P * Matrix.of P' = 1 ∧ Matrix.of P' * Matrix.of P = 1 := by
  first | exact @GlobalTheory.BasisTrans.trans_inverse | exact GlobalTheory.BasisTrans.trans_inverse | (intros; apply GlobalTheory.BasisTrans.trans_inverse <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.swapVariableGroups_formalGroupLawCoboundaryOne_comm : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), (∀ i, constantCoeff (μ i) = 0) → (∀ i, swap (μ i) = μ i) → ∀ g : MvPowerSeries (Fin d) Q, swap (cob1 (up Q μ) g) = cob1 (up Q μ) g := by
  first | exact @GlobalTheory.CobSwap.swap_cob1_eq_of_swap_eq | exact GlobalTheory.CobSwap.swap_cob1_eq_of_swap_eq | (intros; apply GlobalTheory.CobSwap.swap_cob1_eq_of_swap_eq <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

theorem _root_.GlobalTheory.T.exists_cartierDual_lift_linearCoefficients_mod : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (m : Ideal O), (p : O) ∈ m → ∃ n : ℕ, ∀ u : Fin d → O, ∃ φ : G.dual.A n, ∀ F, φ (c.ev n F) - ∑ i, u i * lin F i ∈ m := by
  first | exact @GlobalTheory.QLog.Chart.exists_dual_lift_lin | exact GlobalTheory.QLog.Chart.exists_dual_lift_lin | (intros; apply GlobalTheory.QLog.Chart.exists_dual_lift_lin <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

theorem _root_.GlobalTheory.T.isNilpotent_dualFrobenius_of_block : ∀ (B O : Type) [CommRing B] [CommRing O] (θ : B →+* O) (σ : B →+* B) (p : ℕ) (m : Ideal O), θ (p : B) ∈ m → m ≠ ⊤ → (∀ b, ∃ c, σ b - b ^ p = p * c) → ∀ (d k : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) B) (c : Fin d → Fin d → B), (∀ a j, ∃ b, c a j - U⁻¹ (Sum.inl j) (Sum.inl a) = p * b) → (∃ N : ℕ, ∀ w : Fin d → O ⧸ m, (fun w : Fin d → O ⧸ m => fun a => ∑ j, Ideal.Quotient.mk m (θ (c a j)) * w j ^ p)^[N] w = 0) → IsNil θ σ (U.transpose⁻¹ * blk d k 1 (p : B)) := by
  first | exact @GlobalTheory.DualFrobNilMat.isNil_of_block | exact GlobalTheory.DualFrobNilMat.isNil_of_block | (intros; apply GlobalTheory.DualFrobNilMat.isNil_of_block <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLog.Chart

theorem coeff_mem_of_mem_smul_top {O σ : Type} [CommRing O] (I : Ideal O)
    {h : MvPowerSeries σ O} (hh : h ∈ I • (⊤ : Submodule O (MvPowerSeries σ O))) (α : σ →₀ ℕ) :
    coeff α h ∈ I := by
  refine Submodule.smul_induction_on hh (fun a ha x _ => ?_) (fun x y hx hy => ?_)
  · rw [MvPowerSeries.coeff_smul]
    exact I.mul_mem_right _ ha
  · rw [map_add (f := _)]
    exact I.add_mem hx hy

theorem presents_quotient :
    ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ)
      (c : QLog.Chart G d), ∀ (I : Ideal O) (m : ℕ), (p : O) ^ m ∈ I →
      ∃ hx : ∀ n i, IsNilpotent ((1 : O ⧸ I) ⊗ₜ[O] c.x n i),
        (∀ n f, evA (O ⧸ I) (fun i => (1 : O ⧸ I) ⊗ₜ[O] c.x n i) (hx n)
          (map (Ideal.Quotient.mk I) f) = 1 ⊗ₜ[O] c.ev n f) ∧
        Presents (O ⧸ I) (B := fun n => (O ⧸ I) ⊗[O] G.A n) (fun n i => 1 ⊗ₜ[O] c.x n i) hx := by
  intro p _ O _ G d c I m hm
  have hp : ∀ n, ((p : (O ⧸ I) ⊗[O] G.A n)) ^ m = 0 := fun n => by
    have h0 : ((p : O ⧸ I)) ^ m = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk I), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact hm
    rw [← map_natCast (algebraMap (O ⧸ I) ((O ⧸ I) ⊗[O] G.A n)), ← map_pow, h0, map_zero]
  have hx : ∀ n i, IsNilpotent ((1 : O ⧸ I) ⊗ₜ[O] c.x n i) := fun n i => by
    obtain ⟨N, y, hy⟩ := c.nil n i
    refine ⟨N * m, ?_⟩
    have : (1 : O ⧸ I) ⊗ₜ[O] c.x n i = Algebra.TensorProduct.includeRight (R := O) (A := O ⧸ I)
      (c.x n i) := rfl
    rw [this, ← map_pow, pow_mul, hy, mul_pow, map_mul, map_pow, map_natCast, hp, zero_mul]
  have hev : ∀ n f, evA (O ⧸ I) (fun i => (1 : O ⧸ I) ⊗ₜ[O] c.x n i) (hx n)
      (map (Ideal.Quotient.mk I) f) = 1 ⊗ₜ[O] c.ev n f := fun n f =>
    (GlobalTheory.algHom_eval_comp_eq_evA_map p m O (G.A n) (O ⧸ I) ((O ⧸ I) ⊗[O] G.A n) (Fin d) (c.x n) (c.ev n) (c.isEval n)
      (Ideal.Quotient.mk I)
      (Algebra.TensorProduct.includeRight (R := O) (A := O ⧸ I)).toRingHom
      (fun a => by
        change Algebra.TensorProduct.includeRight (R := O) (A := O ⧸ I) (algebraMap O (G.A n) a) = _
        rw [AlgHom.commutes]
        exact IsScalarTower.algebraMap_apply O (O ⧸ I) ((O ⧸ I) ⊗[O] G.A n) a)
      (hp n) (hx n) f).symm
  refine ⟨hx, hev, fun n y => ?_, fun N => ?_⟩
  · obtain ⟨b, rfl⟩ := (GlobalTheory.PDiv.one_tmul_quot_reduction O (G.A n) I).1 y
    obtain ⟨f, rfl⟩ := c.surj n b
    exact ⟨_, hev n f⟩
  · obtain ⟨n, hn⟩ := c.ker m N
    refine ⟨n, fun g hg α hα => ?_⟩
    obtain ⟨f, rfl, -⟩ := (GlobalTheory.mvPowerSeries_lift_quotient O (Fin d) I).1 g
    rw [hev] at hg
    have h1 : c.ev n f ∈ I • (⊤ : Submodule O (G.A n)) := ((GlobalTheory.PDiv.one_tmul_quot_reduction O (G.A n) I).2.1 _).1 hg
    have h2 : c.ev n f ∈ (I • (⊤ : Submodule O (MvPowerSeries (Fin d) O))).map
        (c.ev n).toLinearMap := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 (c.surj n)]
      exact h1
    obtain ⟨h, hh, he⟩ := h2
    have h3 : c.ev n (f - h) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact he.symm
    have h4 : coeff α (f - h) ∈ I := by
      obtain ⟨z, hz⟩ := hn (f - h) h3 α hα
      rw [hz]
      exact I.mul_mem_right _ hm
    have h5 : coeff α f ∈ I := by
      have := I.add_mem h4 (coeff_mem_of_mem_smul_top I hh α)
      rwa [map_sub, sub_add_cancel] at this
    rw [coeff_map, Ideal.Quotient.eq_zero_iff_mem]
    exact h5

end GlobalTheory.QLog.Chart
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.cob2_cob1_eq_zero_of_isLaw : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLaw μ → ∀ g : MvPowerSeries (Fin d) Q, cob2 (up Q μ) (cob1 (up Q μ) g) = 0 := by
  first | exact @GlobalTheory.formalGroupLawCoboundaryTwo_coboundaryOne_fractions | exact GlobalTheory.formalGroupLawCoboundaryTwo_coboundaryOne_fractions | (intros; apply GlobalTheory.formalGroupLawCoboundaryTwo_coboundaryOne_fractions <;> assumption)
end
