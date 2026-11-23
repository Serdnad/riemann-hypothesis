module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle503
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffEdgesMemOfCoboundaryTwoCoeffsInIdeal
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

@[expose] public section

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLogDefect

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]

theorem in_zero {σ : Type} (N : Ideal B) : In N (0 : MvPowerSeries σ Q) :=
  fun α => ⟨0, N.zero_mem, by simp⟩

theorem in_sub {σ : Type} {N : Ideal B} {f g : MvPowerSeries σ Q} (hf : In N f) (hg : In N g) :
    In N (f - g) := fun α => by
  obtain ⟨a, ha, hfa⟩ := hf α
  obtain ⟨b, hb, hgb⟩ := hg α
  exact ⟨a - b, N.sub_mem ha hb, by rw [map_sub, hfa, hgb, map_sub]⟩

theorem in_subst {σ τ : Type} [Finite σ] {N : Ideal B} {g : MvPowerSeries σ Q}
    (u : σ → MvPowerSeries τ B) (hu : ∀ i, constantCoeff (u i) = 0) (hg : In N g) :
    In N (subst (up Q u) g) := by
  choose c hcN hc using hg
  set G : MvPowerSeries σ B := fun α => c α with hG
  have hgG : g = map (algebraMap B Q) G := by
    ext α; rw [coeff_map, hc α]; rfl
  have hsu : HasSubst u := hasSubst_of_constantCoeff_zero hu
  have key : subst (up Q u) g = map (algebraMap B Q) (subst u G) := by
    rw [map_subst hsu, hgG]; rfl
  intro e
  refine ⟨coeff e (subst u G), ?_, by rw [key, coeff_map]⟩
  rw [coeff_subst hsu]
  refine finsum_induction (fun x => x ∈ N) N.zero_mem (fun x y hx hy => N.add_mem hx hy) ?_
  intro d
  rw [smul_eq_mul]
  exact N.mul_mem_right _ (hcN d)

variable {d : ℕ}

theorem nmul_succ {R : Type} [CommRing R] (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (n : ℕ) :
    nmul μ (n + 1) = op μ (nmul μ n) fun i => X i := by
  unfold nmul; rw [Function.iterate_succ_apply']

theorem constantCoeff_nmul {R : Type} [CommRing R] {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) (i : Fin d) : constantCoeff (nmul μ n i) = 0 := by
  induction n generalizing i with
  | zero => simp [nmul]
  | succ n ih =>
    rw [nmul_succ]
    have h0 : ∀ j, constantCoeff (Sum.elim (nmul μ n) (fun i => (X i : MvPowerSeries (Fin d) R)) j) = 0 := by
      rintro (j | j)
      · exact ih j
      · simp
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h0) h0 (hμ i)

theorem up_nmul_succ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) :
    up Q (nmul μ (n + 1)) = op (up Q μ) (up Q (nmul μ n)) fun i => X i := by
  funext i
  have h0 : ∀ j, constantCoeff (Sum.elim (nmul μ n) (fun i => (X i : MvPowerSeries (Fin d) B)) j) = 0 := by
    rintro (j | j)
    · exact constantCoeff_nmul hμ n j
    · simp
  rw [nmul_succ]
  simp only [up, op, at2]
  rw [map_subst (hasSubst_of_constantCoeff_zero h0)]
  congr 1
  funext j
  rcases j with j | j
  · rfl
  · simp

theorem defect_succ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) (f : MvPowerSeries (Fin d) Q) :
    defect μ (n + 1) f = defect μ n f -
      subst (Sum.elim (up Q (nmul μ n)) fun i => (X i : MvPowerSeries (Fin d) Q)) (cob1 (up Q μ) f) := by
  have hU : ∀ j, constantCoeff (up Q (nmul μ n) j) = 0 := by
    intro j
    simp only [up]
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_nmul hμ n j, map_zero]
  have hE : ∀ j, constantCoeff (Sum.elim (up Q (nmul μ n)) (fun i => (X i : MvPowerSeries (Fin d) Q)) j) = 0 := by
    rintro (j | j)
    · exact hU j
    · simp
  have hM : ∀ j, constantCoeff (up Q μ j) = 0 := by
    intro j
    simp only [up]
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hμ j, map_zero]
  have hsE := hasSubst_of_constantCoeff_zero hE
  have hsM := hasSubst_of_constantCoeff_zero hM
  have hsL : HasSubst (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hsR : HasSubst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have e1 : subst (Sum.elim (up Q (nmul μ n)) fun i => (X i : MvPowerSeries (Fin d) Q)) (subst (up Q μ) f)
      = subst (up Q (nmul μ (n + 1))) f := by
    rw [subst_comp_subst_apply hsM hsE, up_nmul_succ μ hμ n]; rfl
  have e2 : subst (Sum.elim (up Q (nmul μ n)) fun i => (X i : MvPowerSeries (Fin d) Q)) (inL f)
      = subst (up Q (nmul μ n)) f := by
    unfold inL
    rw [subst_comp_subst_apply hsL hsE]
    congr 1; funext j; rw [subst_X hsE]; rfl
  have e3 : subst (Sum.elim (up Q (nmul μ n)) fun i => (X i : MvPowerSeries (Fin d) Q)) (inR f) = f := by
    unfold inR
    rw [subst_comp_subst_apply hsR hsE]
    have : (fun j => subst (Sum.elim (up Q (nmul μ n)) fun i => (X i : MvPowerSeries (Fin d) Q))
        (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) Q)) = fun j => X j := by
      funext j; rw [subst_X hsE]; rfl
    rw [this, subst_self]; rfl
  have hc : subst (Sum.elim (up Q (nmul μ n)) fun i => (X i : MvPowerSeries (Fin d) Q)) (cob1 (up Q μ) f)
      = subst (up Q (nmul μ (n + 1))) f - subst (up Q (nmul μ n)) f - f := by
    unfold cob1
    rw [← coe_substAlgHom hsE, map_sub, map_sub, coe_substAlgHom, e1, e2, e3]
  rw [hc]
  unfold defect
  push_cast
  rw [add_smul, one_smul]
  abel

theorem main : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (N : Ideal B) (f : MvPowerSeries (Fin d) Q), QL μ N f → ∀ n, In N (defect μ n f) ∧ ∀ i, constantCoeff (nmul μ n i) = 0 := by
  intro p _ B O Q _ _ _ _ θ _ d μ hμ N f hf n
  refine ⟨?_, constantCoeff_nmul hμ.const n⟩
  induction n with
  | zero =>
    have h0 : up Q (nmul μ 0) = 0 := by funext i; simp [up, nmul]
    simp only [defect, h0, Nat.cast_zero, zero_smul, zero_sub]
    rw [subst_zero_of_constantCoeff_zero hf.1, neg_zero]
    exact in_zero N
  | succ n ih =>
    rw [defect_succ μ hμ.const n f]
    refine in_sub ih ?_
    have hv : ∀ j, constantCoeff (Sum.elim (nmul μ n) (fun i => (X i : MvPowerSeries (Fin d) B)) j) = 0 := by
      rintro (j | j)
      · exact constantCoeff_nmul hμ.const n j
      · simp
    have : (Sum.elim (up Q (nmul μ n)) fun i => (X i : MvPowerSeries (Fin d) Q)) =
        up Q (Sum.elim (nmul μ n) fun i => (X i : MvPowerSeries (Fin d) B)) := by
      funext j; rcases j with j | j
      · rfl
      · simp [up]
    rw [this]
    exact in_subst _ hv hf.2.2

end GlobalTheory.QLogDefect
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLog.SubstDiff

variable {τ B : Type} [CommRing B]

def euler (j : τ) (g : MvPowerSeries τ B) : MvPowerSeries τ B :=
  fun γ => (γ j : B) * coeff γ g

theorem coeff_euler (j : τ) (g : MvPowerSeries τ B) (γ : τ →₀ ℕ) :
    coeff γ (euler j g) = (γ j : B) * coeff γ g := rfl

theorem euler_mul (j : τ) (x y : MvPowerSeries τ B) :
    euler j (x * y) = euler j x * y + x * euler j y := by
  classical
  ext γ
  rw [coeff_euler, map_add (f := _), coeff_mul, coeff_mul, coeff_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq' : q.1 + q.2 = γ := Finset.HasAntidiagonal.mem_antidiagonal.1 hq
  rw [coeff_euler, coeff_euler, ← hq', Finsupp.add_apply]
  push_cast
  ring

theorem euler_one (j : τ) : euler j (1 : MvPowerSeries τ B) = 0 := by
  classical
  ext γ
  rw [coeff_euler, coeff_one, map_zero]
  split_ifs with h
  · subst h; simp
  · simp

theorem euler_pow (j : τ) (x : MvPowerSeries τ B) (n : ℕ) :
    euler j (x ^ (n + 1)) = ((n + 1 : ℕ) : MvPowerSeries τ B) * x ^ n * euler j x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ x (n + 1), euler_mul, ih]
    push_cast
    ring

theorem euler_prod_mem {σ : Type} (j : τ) (u : σ → MvPowerSeries τ B) (α : σ → ℕ)
    (s : Finset σ) :
    euler j (∏ i ∈ s, u i ^ α i) ∈
      Ideal.span (Set.range fun i => ((α i : ℕ) : MvPowerSeries τ B)) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, euler_one]; exact Ideal.zero_mem _
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, euler_mul]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ ?_) (Ideal.mul_mem_left _ _ ih)
    rcases h : α a with _ | n
    · rw [pow_zero, euler_one]; exact Ideal.zero_mem _
    · rw [euler_pow]
      refine Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨a, ?_⟩))
      simp only [h]

variable {Q : Type} [CommRing Q] [Algebra B Q]

theorem smul_mem_of_mem_span {σ : Type} (N : Submodule B Q) (α : σ → ℕ) (c : Q)
    (hc : ∀ i, (α i : Q) * c ∈ N) (h : MvPowerSeries τ B)
    (hh : h ∈ Ideal.span (Set.range fun i => ((α i : ℕ) : MvPowerSeries τ B))) :
    ∀ e, coeff e h • c ∈ N := by
  induction hh using Submodule.span_induction with
  | mem x hx =>
    classical
    obtain ⟨i, rfl⟩ := hx
    intro e
    dsimp only
    rw [← map_natCast (C (σ := τ) (R := B)), coeff_C]
    split_ifs
    · rw [Algebra.smul_def, map_natCast]; exact hc i
    · rw [zero_smul]; exact N.zero_mem
  | zero => intro e; rw [map_zero, zero_smul]; exact N.zero_mem
  | add x y _ _ hx hy => intro e; rw [map_add (f := _), add_smul]; exact N.add_mem (hx e) (hy e)
  | smul r x _ hx =>
    classical
    intro e
    rw [smul_eq_mul, coeff_mul, Finset.sum_smul]
    refine N.sum_mem fun q _ => ?_
    rw [mul_smul]
    exact N.smul_mem _ (hx q.2)

end GlobalTheory.QLog.SubstDiff

open GlobalTheory.QLog.SubstDiff in
theorem GlobalTheory.QLog.dIn_subst_up :
    ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O]
      [Algebra B Q] (θ : B →+* O), IsFrame p Q θ →
      ∀ (σ τ : Type) [Fintype σ] (N : Ideal B) (f : MvPowerSeries σ Q)
        (u : σ → MvPowerSeries τ B), DIn N f → (∀ i, constantCoeff (u i) = 0) →
        DIn N (MvPowerSeries.subst (QLog.up Q u) f) ∧
          (In N f → In N (MvPowerSeries.subst (QLog.up Q u) f)) := by
  intro p _ B O Q _ _ _ _ θ _ σ τ _ N f u hD hu
  set NQ : Submodule B Q := Submodule.map (Algebra.linearMap B Q) N with hNQ
  have memNQ : ∀ q : Q, q ∈ NQ ↔ ∃ b ∈ N, q = algebraMap B Q b := by
    intro q
    rw [hNQ, Submodule.mem_map]
    constructor
    · rintro ⟨b, hb, rfl⟩; exact ⟨b, hb, rfl⟩
    · rintro ⟨b, hb, rfl⟩; exact ⟨b, hb, rfl⟩
  have ha : HasSubst (QLog.up Q u) :=
    hasSubst_of_constantCoeff_zero fun i => by
      simp only [QLog.up]
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hu i,
        map_zero]

  have hprod : ∀ d : σ →₀ ℕ, (d.prod fun s e => (QLog.up Q u s) ^ e) =
      map (algebraMap B Q) (∏ i, u i ^ d i) := by
    intro d
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), map_prod]
    simp only [QLog.up, map_pow]
  have hcoeff : ∀ e, coeff e (MvPowerSeries.subst (QLog.up Q u) f) =
      ∑ d ∈ (coeff_subst_finite ha f e).toFinset,
        algebraMap B Q (coeff e (∏ i, u i ^ d i)) * coeff d f := by
    intro e
    rw [coeff_subst ha, finsum_eq_sum _ (coeff_subst_finite ha f e)]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hprod, coeff_map, smul_eq_mul, mul_comm]
  refine ⟨fun e j => ?_, fun hI e => ?_⟩
  · rw [← memNQ, hcoeff, Finset.mul_sum]
    refine NQ.sum_mem fun d _ => ?_
    have key := smul_mem_of_mem_span NQ (fun i => d i) (coeff d f)
      (fun i => (memNQ _).2 (by obtain ⟨b, hb, h⟩ := hD d i; exact ⟨b, hb, h⟩))
      _ (euler_prod_mem j u (fun i => d i) Finset.univ) e
    convert key using 1
    rw [coeff_euler, Algebra.smul_def, map_mul, map_natCast]
    ring
  · rw [← memNQ, hcoeff]
    refine NQ.sum_mem fun d _ => ?_
    rw [← Algebra.smul_def]
    exact NQ.smul_mem _ ((memNQ _).2 (by obtain ⟨b, hb, h⟩ := hI d; exact ⟨b, hb, h⟩))
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrobComb

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {σ : Type}

theorem in_top_sum {ι : Type} [Fintype ι] (c : ι → B) (g : ι → MvPowerSeries σ Q)
    (hg : ∀ i, In (⊤ : Ideal B) (g i)) :
    In (⊤ : Ideal B) (∑ i, algebraMap B Q (c i) • g i) := by
  choose t ht using fun i => In.top_iff.1 (hg i)
  refine In.top_iff.2 ⟨∑ i, c i • t i, ?_⟩

  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_C_mul, map_mul, map_C, ht i, smul_eq_C_mul]

theorem frob_sum (p : ℕ) (hp : p ≠ 0) (s : Q →+* Q) {ι : Type} [Fintype ι] (c : ι → Q)
    (f : ι → MvPowerSeries σ Q) :
    frob p s (∑ i, c i • f i) = ∑ i, s (c i) • frob p s (f i) := by
  have hX : HasSubst (fun i : σ => (X i : MvPowerSeries σ Q) ^ p) := HasSubst.X_pow hp

  simp only [frob, ← coe_substAlgHom hX, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul, map_smul]

end GlobalTheory.FrobComb

open GlobalTheory.FrobComb

theorem GlobalTheory.frob_comb_zero_left : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) (F : BFrame ε) (d k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B), (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → ∀ b : Fin k → F.B, In (⊤ : Ideal F.B) (frob p F.s (comb (Sum.elim (fun _ => 0) b) e) - comb (U.mulVec (fun j => F.σ ((Sum.elim (fun _ => 0) b : Fin d ⊕ Fin k → F.B) j))) e) := by
  intro p _ O _ _ _ ε F d k e U he b
  set b' : Fin d ⊕ Fin k → F.B := Sum.elim (fun _ => 0) b with hb'
  set c : Fin d ⊕ Fin k → F.B := fun j => F.σ (b' j) with hc
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have key : ∀ l i, (U * blk d k (p : F.B) 1) l i * c i = U l i * c i := by
    intro l i
    rcases i with i | i
    · simp [hc, hb']
    · simp [blk, Matrix.mul_diagonal]
  have hf : frob p F.s (comb b' e) = ∑ i, algebraMap F.B F.Q (c i) • frob p F.s (e i) := by
    rw [comb, frob_sum p hp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [F.s_alg]
  have hsplit : frob p F.s (comb b' e) - comb (U.mulVec c) e =
      ∑ i, algebraMap F.B F.Q (c i) •
        (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) := by
    rw [hf]
    simp only [smul_sub, Finset.sum_sub_distrib]
    congr 1

    simp only [comb, Matrix.mulVec, dotProduct, Finset.smul_sum, smul_smul, ← map_mul,
    map_sum, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm (c _), key]
  rw [hsplit]
  exact in_top_sum c _ he
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.SmallSecond

theorem map_formalGroupLawCoboundaryOne_eq {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (f : MvPowerSeries (Fin d) R) :
    map φ (cob1 μ f) = cob1 (fun i => map φ (μ i)) (map φ f) := by
  unfold cob1 inL inR
  rw [map_sub, map_sub, map_subst (hasSubst_of_constantCoeff_zero hμ),
    map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _),
    map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
  simp only [map_X]

end GlobalTheory.SmallSecond

namespace GlobalTheory.SmallSecond

variable {B O Q C : Type} [CommRing B] [CommRing O] [CommRing Q] [CommRing C] [Algebra B Q]
  [Algebra O C] {θ : B →+* O} {Θ : Q →+* C}

theorem map_up {d : ℕ} (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))
    (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) :
    (fun i => map Θ (up Q μ' i)) = up C (fun i => map θ (μ' i)) := by
  funext i; ext α; simp [up, coeff_map, hΘ]

theorem map_formalGroupLawCoboundaryOne_square {d : ℕ} (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))
    (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) (hμ : ∀ i, constantCoeff (μ' i) = 0)
    (f : MvPowerSeries (Fin d) Q) :
    map Θ (cob1 (up Q μ') f) = cob1 (up C (fun i => map θ (μ' i))) (map Θ f) := by
  rw [map_formalGroupLawCoboundaryOne_eq Θ _ (fun i => by simp [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map,
    coeff_zero_eq_constantCoeff_apply, hμ]), map_up hΘ]

theorem map_comb {σ ι : Type} [Fintype ι] (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))
    (b : ι → B) (e : ι → MvPowerSeries σ Q) :
    map Θ (comb b e) = comb (fun i => θ (b i)) (fun i => map Θ (e i)) := by
  unfold comb

  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ext α
  rw [coeff_map, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_smul, coeff_map, map_mul, hΘ]

theorem ql_map {d : ℕ} (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))
    (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) (hμ : ∀ i, constantCoeff (μ' i) = 0)
    {f : MvPowerSeries (Fin d) Q} (hf : QL μ' ⊤ f) :
    QL (fun i => map θ (μ' i)) ⊤ (map Θ f) := by
  obtain ⟨h0, h1, h2⟩ := hf
  refine ⟨?_, fun i => ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h0,
      map_zero]
  · obtain ⟨b, -, hb⟩ := h1 i
    exact ⟨θ b, trivial, by simp only [lin, coeff_map] at hb ⊢; rw [hb, hΘ]⟩
  · rw [← map_formalGroupLawCoboundaryOne_square hΘ μ' hμ]
    intro α
    obtain ⟨b, -, hb⟩ := h2 α
    exact ⟨θ b, trivial, by rw [coeff_map, hb, hΘ]⟩

theorem formalGroupLawCoboundaryOne_map_eq_zero {d : ℕ} (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))
    (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) (hμ : ∀ i, constantCoeff (μ' i) = 0)
    {f : MvPowerSeries (Fin d) Q} (hf : In (RingHom.ker θ) (cob1 (up Q μ') f)) :
    cob1 (up C (fun i => map θ (μ' i))) (map Θ f) = 0 := by
  rw [← map_formalGroupLawCoboundaryOne_square hΘ μ' hμ]
  ext α
  obtain ⟨b, hb0, hb⟩ := hf α
  rw [coeff_map, hb, hΘ, RingHom.mem_ker.1 hb0, map_zero, map_zero]

end GlobalTheory.SmallSecond
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.subst_formalGroupLawNatMultiple_eq_coboundary_sum : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ (g : MvPowerSeries (Fin d) R) (n : ℕ), subst (nmul μ n) g = C (constantCoeff g) + (n : R) • g + ∑ k ∈ Finset.range n, at2 (cob1 μ g) (nmul μ k) (fun i => X i) := by
  first | exact @GlobalTheory.QLog.subst_nmul_eq | exact GlobalTheory.QLog.subst_nmul_eq | (intros; apply GlobalTheory.QLog.subst_nmul_eq <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.coeff_edges_mem_of_coboundaryTwo_coeffsInIdeal : ∀ (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (N : Ideal B) (c : MvPowerSeries (Fin d ⊕ Fin d) Q), constantCoeff c = 0 → In N (cob2 (up Q μ) c) → ∀ a : Fin d →₀ ℕ, (∃ b ∈ N, coeff (Finsupp.sumElim a 0) c = algebraMap B Q b) ∧ (∃ b ∈ N, coeff (Finsupp.sumElim 0 a) c = algebraMap B Q b) := by
  first | exact @GlobalTheory.CobEdges.coeff_edges_mem | exact GlobalTheory.CobEdges.coeff_edges_mem | (intros; apply GlobalTheory.CobEdges.coeff_edges_mem <;> assumption)
end
