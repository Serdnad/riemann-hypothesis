module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle211
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConnPhiExtensionGeneratorEqZeta
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle214
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle212
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle199
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsEqAlgebraMapAddPowMul
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TameDescentExtendedActionExtraVector
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle057
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle213
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

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.ramificationJumpSum_le_add : ∀ (G : Type) [Group G] (R : ℕ → Subgroup G) (A B C : Subgroup G), Antitone R → (∃ m, R m = ⊥) → B ≤ A → jumpSum R A C ≤ jumpSum R A B + jumpSum R B C := by
  first | exact @GlobalTheory.PMon.Ram.jumpSum_le_add | exact GlobalTheory.PMon.Ram.jumpSum_le_add | (intros; apply GlobalTheory.PMon.Ram.jumpSum_le_add <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.BK

open PowerSeries Matrix

theorem PhiMod.mem_MM_of_series (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] (P : PhiMod O K l e a ι) :
    ∀ (w : Vec K a ι) (t : ℕ → Vec K a ι), (∀ n, ∃ v ∈ P.MM, t n = (l : K) ^ n • v) →
      (∀ m, w - ∑ n ∈ Finset.range m, t n ∈ uPow (K := K) (a := a) (ι := ι) m) → w ∈ P.MM := by
  intro w t ht hw
  choose v hv htv using ht
  have h2 (k : ℕ) : ∃ s ∈ P.MM, ∀ m, ∃ g ∈ P.MM,
      w - (s + (l : K) ^ k • g) ∈ uPow (K := K) (a := a) (ι := ι) m := by
    refine ⟨∑ n ∈ Finset.range k, t n,
      sum_mem fun n _ => (htv n) ▸ P.l_pow_smul_mem_MM n (hv n), fun m => ?_⟩
    refine ⟨∑ n ∈ Finset.range m, (l : K) ^ n • v (k + n),
      sum_mem fun n _ => P.l_pow_smul_mem_MM n (hv _), uPow_anti (Nat.le_add_left m k) ?_⟩
    have := hw (k + m)
    rw [Finset.sum_range_add] at this
    simpa only [Finset.smul_sum, smul_smul, ← pow_add, ← htv] using this
  have hext {τ : ZMod a} {v : ι → K⟦X⟧} :
      v ∈ P.extc (S O K e) τ ↔ P.mxInv τ *ᵥ v ∈ vecs ι (S O K e) := by
    have hmem {v : ι → K⟦X⟧} : v ∈ P.extc (S O K e) τ ↔
        ∃ m ∈ vecs ι (S O K e), v = P.mx τ *ᵥ m := by
      rw [PhiMod.extc, Submodule.mem_span_range_iff_exists_fun]
      have key (c : ι → S O K e) : ∑ i, c i • (P.mx τ).col i =
          P.mx τ *ᵥ fun i => (c i : K⟦X⟧) := by
        ext1 j
        simp [Matrix.mulVec, dotProduct, Subalgebra.smul_def, mul_comm]
      constructor
      · rintro ⟨c, rfl⟩
        exact ⟨_, fun i => (c i).2, key c⟩
      · rintro ⟨m, hm, rfl⟩
        exact ⟨fun i => ⟨m i, hm i⟩, key _⟩
    rw [hmem]
    constructor
    · rintro ⟨m, hm, rfl⟩
      rwa [Matrix.mulVec_mulVec, P.mxInv_mul_mx, Matrix.one_mulVec]
    · intro h
      exact ⟨_, h, by rw [Matrix.mulVec_mulVec, P.mx_mul_mxInv, Matrix.one_mulVec]⟩
  refine mem_tot.2 fun τ => hext.2 fun i => mem_S_of_approx (l := l) fun k => ?_
  obtain ⟨s, hs, H⟩ := h2 k
  refine ⟨_, hext.1 (mem_tot.1 hs τ) i, fun m => ?_⟩
  obtain ⟨g, hg, H'⟩ := H m
  refine ⟨_, hext.1 (mem_tot.1 hg τ) i, ?_⟩
  have := dvd_mulVec (P.mxInv τ) (H' τ) i
  simpa only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Matrix.mulVec_sub, Matrix.mulVec_add,
    Matrix.mulVec_smul] using this

end GlobalTheory.BK
end
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.eulerE_add_smul_mem_eisenstein_shift_graded : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H) (j : ℤ) (x : Vec K a ι), x ∈ shiftE l e j (D.ext (Rpi O K l e)) → D.EN x + ((j * e * l : ℤ) : K) • x ∈ shiftE l e (j + 1) (D.ext (Rpi O K l e)) := by
  first | exact @GlobalTheory.Proof.eulerE_add_smul_mem_eisenstein_shift_graded.EN_add_smul_mem_shiftE | exact GlobalTheory.Proof.eulerE_add_smul_mem_eisenstein_shift_graded.EN_add_smul_mem_shiftE | (intros; apply GlobalTheory.Proof.eulerE_add_smul_mem_eisenstein_shift_graded.EN_add_smul_mem_shiftE <;> assumption)
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.monodromy_mem_range_of_invariant_vector : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ y ∈ D.Yl, (∃ s ∈ D.MMl, s ∈ D.desc.inv ∧ D.conn s = D.zeta y ∧ ∃ d : D.D, (∀ g, D.desc.actD g d = d) ∧ D.phi s - s - D.phi y = D.xi d) ∧ ∃ w ∈ D.Zl, D.Lc w = D.Mon y := by
  first | exact @GlobalTheory.BK.BKDat.Mon_mem_range_Lc | exact GlobalTheory.BK.BKDat.Mon_mem_range_Lc | (intros; apply GlobalTheory.BK.BKDat.Mon_mem_range_Lc <;> assumption)
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.phi_mem_invertedLattice : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ v ∈ D.MMl, D.phi v ∈ D.MMl := by
  first | exact @GlobalTheory.BK.BKDat.phi_mem_MMl | exact GlobalTheory.BK.BKDat.phi_mem_MMl | (intros; apply GlobalTheory.BK.BKDat.phi_mem_MMl <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.BK

open PowerSeries

theorem padicValNat_factorial_le_sub (l i j : ℕ) [hp : Fact l.Prime] (hji : j ≤ i) (hjl : j < l) :
    padicValNat l i.factorial ≤ i - j := by
  have hL : (l - 1) * padicValNat l i.factorial = i - (l.digits i).sum := by
    simpa only [Nat.padicValNat_def] using (Nat.Prime.sub_one_mul_multiplicity_factorial (n := i) hp.out)
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [_root_.Nat.padicValNat_def (n := 1)]
  have hpos : 0 < (l.digits i).sum := by
    rcases Nat.eq_zero_or_pos (l.digits i).sum with h0 | h0
    · exfalso
      have hne : l.digits i ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hi.ne'
      have h1 := Nat.getLast_digit_ne_zero l hi.ne'
      have h2 := List.sum_eq_zero_iff.1 h0 _ (List.getLast_mem hne)
      exact h1 h2
    · exact h0
  have hsum : (l.digits i).sum ≤ i := Nat.digit_sum_le l i
  have hl2 := hp.out.two_le
  set v := padicValNat l i.factorial
  rcases Nat.eq_zero_or_pos v with hv | hv
  · omega
  · have : (l - 1) * v ≤ i - 1 := by omega
    clear_value v
    have h3 : v + (l - 1) ≤ (l - 1) * v + 1 := by
      obtain ⟨L, hLe⟩ : ∃ L, l - 1 = L + 1 := ⟨l - 2, by omega⟩
      obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
      rw [hLe]
      nlinarith
    omega

section Padic

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]


omit [IsUltrametricDist K] in
theorem norm_pow_sub_le_norm_factorial {i j : ℕ} (hji : j ≤ i) (hjl : j < l) :
    ‖(l : K)‖ ^ (i - j) ≤ ‖(i.factorial : K)‖ := by
  rw [norm_l, norm_natCast_eq l, Padic.norm_eq_zpow_neg_valuation (by
    exact_mod_cast i.factorial_ne_zero), Padic.valuation_natCast, inv_pow, zpow_neg, zpow_natCast]
  have h1 : (1 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).one_le
  exact inv_anti₀ (by positivity)
    (pow_le_pow_right₀ h1 (by
      simpa only [Nat.padicValNat_def] using padicValNat_factorial_le_sub l i j hji hjl))

theorem C_mem_S {e : ℕ} {c : K} (hc : ‖c‖ ≤ 1) : C c ∈ S O K e := by
  rw [← monomial_zero_eq_C_apply]
  exact monomial_mem_S (mul_le_one₀ hc (wS_nonneg _ _) (wS_le_one _ _))

theorem exists_frob_E_eq (e : ℕ) [NeZero e] : ∃ d ∈ S O K e, frob K l (E K l e) = C (l : K) * d := by
  refine ⟨1 + monomial (e * l) ((l : K)⁻¹), add_mem (one_mem _) (monomial_mem_S ?_), ?_⟩
  · rw [wS, Nat.mul_div_cancel_left _ (NeZero.pos e), norm_inv]
    have h0 : 0 < ‖(l : K)‖ := norm_pos_iff.2 (l_ne_zero l)
    rw [inv_mul_le_one₀ h0]
    exact norm_natCast_le_of_dvd (Nat.dvd_factorial (Fact.out : l.Prime).pos le_rfl)
  · rw [E, map_add (f := _), map_pow, frob_X, map_natCast, monomial_eq_C_mul_X_pow, mul_add, mul_one,
      ← mul_assoc, ← map_mul, mul_inv_cancel₀ (l_ne_zero l), map_one, one_mul, ← pow_mul,
      mul_comm l e, add_comm, map_natCast]

theorem exists_frob_Ediv_eq (e : ℕ) [NeZero e] {i j : ℕ} (hji : j ≤ i) (hjl : j < l) :
    ∃ s ∈ S O K e, frob K l (Ediv K l e i) = C ((l : K) ^ j) * s := by
  obtain ⟨d, hd, hE⟩ := exists_frob_E_eq (O := O) (K := K) l e
  have hf : (i.factorial : K) ≠ 0 := natCast_ne_zero' l i.factorial_ne_zero
  refine ⟨C ((l : K) ^ (i - j) / (i.factorial : K)) * d ^ i, mul_mem (C_mem_S ?_) (pow_mem hd i), ?_⟩
  · rw [norm_div, norm_pow]
    exact div_le_one_of_le₀ (norm_pow_sub_le_norm_factorial l hji hjl) (norm_nonneg _)
  · have key : (i.factorial : K)⁻¹ * (l : K) ^ i = (l : K) ^ j * ((l : K) ^ (i - j) / (i.factorial : K)) := by
      rw [mul_div_assoc', ← pow_add, Nat.add_sub_cancel' hji, div_eq_inv_mul]
    rw [Ediv, map_mul, frob_C, map_pow, hE, mul_pow, ← map_pow, ← mul_assoc, ← map_mul, key,
      map_mul, mul_assoc]

theorem exists_frob_eq_of_mem_Fil (e : ℕ) [NeZero e] {j : ℕ} (hjl : j < l) {r : S O K e}
    (hr : r ∈ Fil O K l e j) : ∃ s ∈ S O K e, frob K l (r : K⟦X⟧) = C ((l : K) ^ j) * s := by
  obtain ⟨g, hg, h, rfl⟩ := (mem_Fil l).1 hr j
  have key : ∀ x ∈ FilPre O K l e j, ∃ s ∈ S O K e, frob K l (x : K⟦X⟧) = C ((l : K) ^ j) * s := by
    intro x hx
    have hx' : x ∈ Submodule.span (S O K e) {x : S O K e | ∃ i, j ≤ i ∧ (x : K⟦X⟧) = Ediv K l e i} := hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, hxi⟩ := hx
      rw [hxi]
      exact exists_frob_Ediv_eq l e hi hjl
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs, h1⟩ := hx
      obtain ⟨t, ht, h2⟩ := hy
      exact ⟨s + t, add_mem hs ht, by rw [Subalgebra.coe_add, map_add (f := _), h1, h2, mul_add]⟩
    | smul c x _ hx =>
      obtain ⟨s, hs, h1⟩ := hx
      exact ⟨frob K l c * s, mul_mem (frob_mem_S l c.2) hs, by
        rw [smul_eq_mul, Subalgebra.coe_mul, map_mul, h1]; ring⟩
  obtain ⟨s, hs, h1⟩ := key g hg
  refine ⟨s + frob K l h, add_mem hs (frob_mem_S l h.2), ?_⟩
  rw [Subalgebra.coe_add, Subalgebra.coe_mul, map_add (f := _), map_mul, h1, mul_add]
  congr 2
  simp

end Padic

theorem phi_FilMM_mem : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H) (j : ℕ), j < l → ∀ v ∈ D.FilMM j, ∃ v' ∈ D.MM, (l : K) ^ η • D.phi v = (l : K) ^ j • v' := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D j hjl v hv
  refine Submodule.smul_induction_on (p := fun v => ∃ v' ∈ D.MM, (l : K) ^ η • D.phi v = (l : K) ^ j • v')
    hv (fun r hr n hn => ?_) (fun x y hx hy => ?_)
  · obtain ⟨s, hs, hfs⟩ := exists_frob_eq_of_mem_Fil l e hjl hr
    have h3 := D.l_pow_smul_phi_mem_MM (k := η) (D.smul_mem_Mext (A_le_S l e) hn)
    refine ⟨s • ((l : K) ^ η • D.phi n), PhiMod.smul_mem_MM _ hs h3, ?_⟩
    rw [Subalgebra.smul_def, PhiMod.phi_smul, hfs, ← smul_eq_C_mul, smul_assoc,
      smul_comm ((l : K) ^ η) ((l : K) ^ j), smul_comm ((l : K) ^ η) s]
  · obtain ⟨v₁, h₁, e₁⟩ := hx
    obtain ⟨v₂, h₂, e₂⟩ := hy
    exact ⟨v₁ + v₂, add_mem h₁ h₂, by rw [map_add (f := _), smul_add, e₁, e₂, smul_add]⟩

end GlobalTheory.BK
end
end

section

open PowerSeries GlobalTheory.BK

namespace GlobalTheory.BK

theorem phi_mem_MMl_of_mem_Y : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ y ∈ D.Y, D.phi y ∈ D.MMl := by
  intro O K _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D y hy
  have hl : (l : K) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[l] K)]
    exact (map_ne_zero (algebraMap ℚ_[l] K)).2
      (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero : (l : ℚ_[l]) ≠ 0)
  have hE : E K l e ^ η • y ∈ D.M := hy.1
  have h0 : (l : K) ^ η • D.phi y ∈ D.MM := D.l_pow_smul_phi_mem_MM (D.Mext_mono (A_le_S l e) hE)
  have h1 : (l : K) ^ η • D.phi y ∈ D.MMl := D.ext_mono (le_away _ _) h0
  have hc : (C ((l : K)⁻¹ ^ η) : K⟦X⟧) ∈ invL l (S O K e) := by
    refine ⟨η, ?_⟩
    have : ((l : S O K e) : K⟦X⟧) ^ η * C ((l : K)⁻¹ ^ η) = 1 := by
      rw [show ((l : S O K e) : K⟦X⟧) = C (l : K) by simp, ← map_pow, ← map_mul, ← mul_pow,
        mul_inv_cancel₀ hl, one_pow, map_one]
    rw [this]; exact one_mem _
  have h2 := D.MMl.smul_mem ⟨_, hc⟩ h1
  convert h2 using 1
  rw [Subalgebra.smul_def]
  funext τ i
  simp only [Pi.smul_apply, smul_eq_mul, Subtype.coe_mk]
  rw [PowerSeries.smul_eq_C_mul, ← mul_assoc, ← map_mul, ← mul_pow, inv_mul_cancel₀ hl, one_pow,
    map_one, one_mul]

end GlobalTheory.BK
end

section

open PowerSeries GlobalTheory.BK

namespace GlobalTheory.BK

theorem lphi_pow_conn_X_pow_smul_mem : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ (y₀ : Vec K a ι), 1 ≤ η → E K l e ^ η • y₀ ∈ D.M → ∀ n : ℕ, ∃ w ∈ D.MM, (l : K) ^ (H + 2 * η + n * (η - 1)) • (D.lphi ^ (n + 1)) (D.conn ((X : K⟦X⟧) ^ e • y₀)) = (X : K⟦X⟧) ^ (e * l ^ (n + 1)) • w := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D y₀ hη hy n
  have key (w : Vec K a ι) (hw : w ∈ D.MM) : (l : K) ^ η • D.phi w ∈ D.MM :=
    PhiMod.pow_smul_phi_mem_MM O K l e a ι D.toPhiMod η D.upper w hw
  induction n with
  | zero =>
    have hE : E K l e ∈ S O K e := E_mem l e _
    have hNE : N K (E K l e) ∈ S O K e := by
      rw [N_apply]; exact mul_mem HasU.X_mem (derivative_mem_S hE)

    have h0 : (l : K) ^ η • D.phi y₀ ∈ D.MM :=
      D.l_pow_smul_phi_mem_MM (D.Mext_mono (A_le_S l e) hy)
    have hA : (l : K) ^ (H + 2 * η + 1) • D.phi y₀ ∈ D.MM := by
      have := D.l_pow_smul_mem_MM (H + η + 1) h0
      rwa [smul_smul, ← pow_add, show H + η + 1 + η = H + 2 * η + 1 by ring] at this

    have hk : E K l e ^ (H + η) • y₀ ∈ D.MM := by
      rw [pow_add, mul_smul]
      exact D.ext_mono (A_le_S l e) (D.lower _ hy)
    have h1 : E K l e ^ (H + η + 1) • D.conn y₀ ∈ D.MM := by
      have h2 := sub_mem (D.smul_mem_MM hE (D.conn_mem_MM hk))
        (D.smul_mem_MM (mul_mem (natCast_mem _ (H + η)) hNE) hk)
      convert h2 using 1
      rw [PhiMod.conn_smul, N_apply, derivative_pow]
      generalize H + η = k
      ext τ i : 2
      simp only [smul_eq_mul, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, N_apply]
      cases k with
      | zero => simp
      | succ k => simp only [Nat.add_sub_cancel]; ring
    have h3 := D.smul_mem_Mext (A_le_S l e) h1
    rw [smul_smul, ← pow_add] at h3
    have hB := D.l_pow_smul_phi_mem_MM h3
    rw [show η + (H + η + 1) = H + 2 * η + 1 by ring] at hB
    refine ⟨(e : K⟦X⟧) • ((l : K) ^ (H + 2 * η + 1) • D.phi y₀) +
      (l : K) ^ (H + 2 * η + 1) • D.phi (D.conn y₀),
      add_mem (D.smul_mem_MM (natCast_mem _ e) hA) hB, ?_⟩
    have hc : D.conn ((X : K⟦X⟧) ^ e • y₀) = (X : K⟦X⟧) ^ e • ((e : K⟦X⟧) • y₀ + D.conn y₀) := by
      rw [PhiMod.conn_smul, smul_add, smul_smul]
      congr 2
      ext n
      rw [coeff_N, ← map_natCast (C : K →+* K⟦X⟧), coeff_mul_C, coeff_X_pow]
      split_ifs with h <;> simp [h]
    rw [zero_mul, add_zero, zero_add, pow_one, pow_one, hc, PhiMod.lphi_apply, PhiMod.phi_smul, map_add (f := _),
      PhiMod.phi_smul, map_pow, frob_X, ← pow_mul, map_natCast, mul_comm l e]
    simp only [smul_add, smul_smul, pow_succ]
    congr 1 <;> exact smul_comm _ _ _
  | succ n ih =>
    obtain ⟨w, hw, h⟩ := ih
    refine ⟨_, key w hw, ?_⟩
    rw [show H + 2 * η + (n + 1) * (η - 1) = (η - 1) + (H + 2 * η + n * (η - 1)) by ring, pow_add,
      mul_smul, pow_succ', Module.End.mul_apply, ← map_smul, h, PhiMod.lphi_apply, PhiMod.phi_smul,
      map_pow, frob_X, ← pow_mul, smul_smul, ← pow_succ, Nat.sub_add_cancel hη, smul_comm]
    congr 2
    ring

end GlobalTheory.BK
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.mem_analytic_filtration_iff_lattice_filtration_add : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι) (i : ℤ) (x : Vec K a ι), x ∈ (P.ext (Rpi O K l e) ⊓ shiftE l e i (P.Mext (Rpi O K l e))) ⊔ shiftE l e 1 (P.ext (Rpi O K l e)) ↔ ∃ y ∈ P.filL i, x - y ∈ shiftE l e 1 (P.ext (Rpi O K l e)) := by
  first | exact @GlobalTheory.BK.PhiMod.mem_analytic_filtration_iff | exact GlobalTheory.BK.PhiMod.mem_analytic_filtration_iff | (intros; apply GlobalTheory.BK.PhiMod.mem_analytic_filtration_iff <;> assumption)
end

section

namespace GlobalTheory.TopWindow

open GlobalTheory.AdmLoc

def InWin (typ : Bool) (h η : ℕ) (u : ℤ) : Prop :=
  if typ then u ≤ (η : ℤ) else (h : ℤ) - η ≤ u

instance (typ : Bool) (h η : ℕ) : DecidablePred (InWin typ h η) := fun u => by
  unfold InWin; infer_instance

theorem count_block (w : ℤ) (t : ℕ) (a : ℤ) :
    (block w t).count a = if w ≤ a ∧ a < w + t then 1 else 0 := by
  split_ifs with ha
  · exact Multiset.count_eq_one_of_mem (Finset.Ico _ _).nodup (mem_block.2 ha)
  · exact Multiset.count_eq_zero.2 fun hm => ha (mem_block.1 hm)

def ofWindow {n r : ℕ} (t : ℕ) (h η : ZMod n → ℕ) (typ : ZMod n → Bool) (w : ZMod n → ℤ)
    (U : ZMod n → Multiset ℤ) (hh : ∀ i, 2 ≤ h i) (hη : ∀ i, 1 ≤ η i) (ht : 1 ≤ t)
    (hc : ∀ i, Multiset.card (U i) = r) (hU : ∀ i, ∀ u ∈ U i, 1 ≤ u ∧ u ≤ (h i : ℤ) - 1)
    (hB : ∀ i (β : ℤ), w i ≤ β → β < w i + t →
      1 ≤ β ∧ β ≤ (h i : ℤ) - 1 ∧ InWin (typ i) (h i) (η i) β) : TopData n r where
  h := h
  η := η
  ty := fun i => if typ i then LType.G else LType.Bd
  w := w
  t := t
  lows := fun i => (U i).filter (InWin (typ i) (h i) (η i))
  cloud := fun i => (U i).filter fun u => ¬ InWin (typ i) (h i) (η i) u
  two_le_h := hh
  one_le_η := hη
  one_le_letterBlockLength := ht
  card_eq := fun i => by rw [Multiset.filter_add_not, hc]
  range := fun i u hu => by
    rw [Multiset.filter_add_not, Multiset.mem_add, mem_block] at hu
    rcases hu with hu | hu
    · exact hU i u hu
    · exact ⟨(hB i u hu.1 hu.2).1, (hB i u hu.1 hu.2).2.1⟩
  lowG := fun i hi u hu => by
    have hi' : typ i = true := by by_contra hn; simp [hn] at hi
    rw [Multiset.mem_add, mem_block, Multiset.mem_filter] at hu
    rcases hu with hu | hu
    · exact ⟨(hU i u hu.1).1, by simpa [InWin, hi'] using hu.2⟩
    · exact ⟨(hB i u hu.1 hu.2).1, by simpa [InWin, hi'] using (hB i u hu.1 hu.2).2.2⟩
  cloudG := fun i hi u hu => by
    have hi' : typ i = true := by by_contra hn; simp [hn] at hi
    rw [Multiset.mem_filter] at hu
    simpa [InWin, hi'] using hu.2
  lowBd := fun i hi u hu => by
    have hi' : typ i = false := by by_contra hn; simp at hn; simp [hn] at hi
    rw [Multiset.mem_add, mem_block, Multiset.mem_filter] at hu
    rcases hu with hu | hu
    · exact ⟨by simpa [InWin, hi'] using hu.2, (hU i u hu.1).2⟩
    · exact ⟨by simpa [InWin, hi'] using (hB i u hu.1 hu.2).2.2, (hB i u hu.1 hu.2).2.1⟩
  cloudBd := fun i hi u hu => by
    have hi' : typ i = false := by by_contra hn; simp at hn; simp [hn] at hi
    rw [Multiset.mem_filter] at hu
    have := hu.2
    simp only [InWin, hi', Bool.false_eq_true, if_false, not_le] at this
    exact this

theorem exists_topData (l n t r : ℕ) (h η : ZMod n → ℕ) (typ : ZMod n → Bool) (w : ZMod n → ℤ)
    (U : ZMod n → Multiset ℤ) (hh : ∀ i, 2 ≤ h i) (hη : ∀ i, 1 ≤ η i) (ht : 1 ≤ t)
    (hc : ∀ i, Multiset.card (U i) = r) (hU : ∀ i, ∀ u ∈ U i, 1 ≤ u ∧ u ≤ (h i : ℤ) - 1)
    (hB : ∀ i (β : ℤ), w i ≤ β → β < w i + t →
      1 ≤ β ∧ β ≤ (h i : ℤ) - 1 ∧ InWin (typ i) (h i) (η i) β)
    (h1 : ∀ i, η i + 4 * GlobalTheory.PhiGam.sg l h i + 6 < l)
    (h2 : ∀ i, ∀ u ∈ U i, InWin (typ i) (h i) (η i) u → ∀ β : ℤ, w i ≤ β → β < w i + t →
      (GlobalTheory.PhiGam.sg l h i : ℤ) + 2 < |u - β|)
    (h3 : ∀ i, ∀ u ∈ U i, ¬ InWin (typ i) (h i) (η i) u → ∀ y : ℤ,
      -2 * (GlobalTheory.PhiGam.sg l h i : ℤ) - 2 ≤ y → y ≤ (η i : ℤ) + 2 * GlobalTheory.PhiGam.sg l h i + 3 →
        ¬ (if typ i then u else (h i : ℤ) - u) ≡ y [ZMOD l]) :
    ∃ Dt : TopData n r, Dt.t = t ∧
      (∀ i, Dt.w i = w i ∧ Dt.U i = U i ∧ ∀ a, ((Dt.Ut i).count a : ℤ) =
        ((U i).count a : ℤ) + if w i ≤ a ∧ a < w i + t then 1 else 0) ∧
      Dt.T1 l ∧ Dt.T2 l ∧ Dt.T3 l := by
  have hUeq : ∀ i, (ofWindow t h η typ w U hh hη ht hc hU hB).U i = U i := fun i =>
    Multiset.filter_add_not _ _
  refine ⟨ofWindow t h η typ w U hh hη ht hc hU hB, rfl, fun i => ⟨rfl, hUeq i, fun a => ?_⟩,
    h1, fun i u hu β hβ => ?_, fun i u hu y hy1 hy2 => ?_⟩
  · rw [TopData.Ut, hUeq, Multiset.count_add]
    change (((U i).count a + (block (w i) t).count a : ℕ) : ℤ) = _
    rw [count_block]
    push_cast
    rfl
  · have hu' := Multiset.mem_filter.1 hu
    have hβ' := mem_block.1 hβ
    exact h2 i u hu'.1 hu'.2 β hβ'.1 hβ'.2
  · have hu' := Multiset.mem_filter.1 hu
    have := h3 i u hu'.1 hu'.2 y hy1 hy2
    have he : (ofWindow t h η typ w U hh hη ht hc hU hB).cloudRes i u =
        if typ i then u else (h i : ℤ) - u := by
      cases hi : typ i <;> simp [TopData.cloudRes, ofWindow, hi]
    rw [he]
    exact this

end GlobalTheory.TopWindow
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.exists_preimage_invertedPrime_breuil_of_exactTriple : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] [NeZero e] [NormedAlgebra ℚ_[l] K] (ι κ μ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (T : PhiMod O K l e a μ) (F : Hom P Q) (G : Hom Q T), IsExactTriple F G → ∀ v ∈ Q.ext (invL l (S O K e)), G.app v = 0 → ∃ w ∈ P.ext (invL l (S O K e)), F.app w = v := by
  first | exact @GlobalTheory.BK.exists_preimage_invL_S_of_exactTriple | exact GlobalTheory.BK.exists_preimage_invL_S_of_exactTriple | (intros; apply GlobalTheory.BK.exists_preimage_invL_S_of_exactTriple <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.unitaryAct_liftHermitianBlock_mem_integralUnitary_mul_embedding : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] {r : ℕ} (X : Hn r F E) (ν : E) (l : F), ‖ν‖ = 1 → ∀ g : Matrix.unitaryGroup (Fin (r + 1)) E, unitU (r + 1) F E (actU g (GlobalTheory.JR.Step.liftH X ν l)) ≠ 0 → ∃ k ∈ uO (r + 1) E, ∃ s, g = k * GlobalTheory.JR.Step.uEmb r E s := by
  first | exact @GlobalTheory.JR.Step.actU_liftH_mem_uO_mul_uEmb | exact GlobalTheory.JR.Step.actU_liftH_mem_uO_mul_uEmb | (intros; apply GlobalTheory.JR.Step.actU_liftH_mem_uO_mul_uEmb <;> assumption)
end
