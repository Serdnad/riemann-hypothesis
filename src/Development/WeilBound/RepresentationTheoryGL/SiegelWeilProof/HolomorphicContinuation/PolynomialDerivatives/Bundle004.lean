module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.BfSmulRight
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.CoreSt
import Aesop.BuiltinRules
import Aesop.Frontend.Tactic
import Aesop.Main
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.IntegrableRpowGauss
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
import Std.Tactic.BVDecide.Normalize.Bool
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open MvPolynomial Finsupp

namespace PositivityTheory.Rg.Sw.LC

namespace CoreC

open PositivityTheory.Rg.Sw G

variable {m n : ℕ}

theorem fform_eq_gf (c : ℝ) (p q : PX m n) : fform c p q = gf (fun s => (wt c s : ℂ)) p q := rfl

theorem wt_univ (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) :
    wt c s = ∏ k, ((s k).factorial : ℝ) * (2 * c) ^ (s k) := by
  unfold wt
  refine Finset.prod_subset (Finset.subset_univ _) fun k _ hk => ?_
  have : s k = 0 := by simpa [Finsupp.mem_support_iff] using hk
  simp [this]

theorem wt_pos {c : ℝ} (hc : 0 < c) (s : Fin m × Fin n × Bool →₀ ℕ) : 0 < wt c s := by
  rw [wt_univ]
  exact Finset.prod_pos fun k _ => mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (pow_pos (by linarith) _)

theorem wt_step (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) (k : Fin m × Fin n × Bool) :
    (wt c (Finsupp.single k 1 + s) : ℂ) = ((2 * c : ℝ) : ℂ) * ((s k : ℂ) + 1) * (wt c s : ℂ) := by
  have h : wt c (Finsupp.single k 1 + s) = (2 * c) * ((s k : ℝ) + 1) * wt c s := by
    rw [wt_univ, wt_univ, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k),
      ← Finset.mul_prod_erase Finset.univ (fun j => ((s j).factorial : ℝ) * (2 * c) ^ (s j)) (Finset.mem_univ k)]
    have hrest : ∏ j ∈ Finset.univ.erase k, (((Finsupp.single k 1 + s : Fin m × Fin n × Bool →₀ ℕ) j).factorial : ℝ) *
          (2 * c) ^ ((Finsupp.single k 1 + s : Fin m × Fin n × Bool →₀ ℕ) j) =
        ∏ j ∈ Finset.univ.erase k, ((s j).factorial : ℝ) * (2 * c) ^ (s j) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      have hjk : j ≠ k := Finset.ne_of_mem_erase hj
      simp [Finsupp.single_apply, Ne.symm hjk]
    rw [hrest]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    rw [add_comm 1 (s k), Nat.factorial_succ, pow_succ]
    push_cast; ring
  rw [h]; push_cast; ring

theorem KopL_apply (ε : Fin m → Bool) (i j : Fin n) (p : PX m n) :
    KopL ε i j p = ∑ a ∈ Finset.univ.filter (fun a => ε a = true), X (a, i, false) * pderiv (a, j, false) p -
      ∑ a ∈ Finset.univ.filter (fun a => ε a = false), X (a, j, true) * pderiv (a, i, true) p := by
  simp [KopL, LinearMap.sub_apply, LinearMap.sum_apply]

theorem rdeg_add (ε : Fin m → Bool) (s t : Fin m × Fin n × Bool →₀ ℕ) : rdeg ε (s + t) = rdeg ε s + rdeg ε t := by
  funext a; simp [rdeg, Finset.sum_add_distrib]

theorem rdeg_single (ε : Fin m → Bool) (k : Fin m × Fin n × Bool) (hk : inF1 ε k) :
    rdeg ε (Finsupp.single k 1) = fun a => if a = k.1 then 1 else 0 := by
  funext a
  unfold rdeg
  obtain ⟨a0, i0, b0⟩ := k
  simp only [inF1] at hk
  subst hk
  by_cases ha : a = a0
  · subst ha
    rw [if_pos rfl, Finset.sum_eq_single i0]
    · simp
    · intro i _ hi; simp [Finsupp.single_apply, Ne.symm hi]
    · simp
  · rw [if_neg ha]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro h; exact ha (congrArg Prod.fst h).symm

theorem term_mem_box (ε : Fin m → Bool) (R : Set (Fin m → ℕ)) (k l : Fin m × Fin n × Bool)
    (hk : inF1 ε k) (hl : inF1 ε l) (hkl : k.1 = l.1) (s : Fin m × Fin n × Bool →₀ ℕ)
    (hs : ∀ k ∈ s.support, inF1 ε k) (hR : rdeg ε s ∈ R) :
    X k * pderiv l (monomial s (1 : ℂ)) ∈ box ε R := by
  rw [pderiv_monomial, X, monomial_mul, one_mul, one_mul]
  by_cases h0 : s l = 0
  · simp [h0]
  · rw [show (monomial (Finsupp.single k 1 + (s - Finsupp.single l 1)) ((s l : ℕ) : ℂ) : PX m n) =
        ((s l : ℕ) : ℂ) • monomial (Finsupp.single k 1 + (s - Finsupp.single l 1)) (1 : ℂ) by
        rw [smul_monomial, smul_eq_mul, mul_one]]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, fun k' hk' => ?_, ?_, rfl⟩)
    · rcases Finset.mem_union.mp (Finsupp.support_add hk') with h | h
      · rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at h; rw [h]; exact hk
      · exact hs k' (Finsupp.support_tsub h)
    · have hle : Finsupp.single l 1 ≤ s := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h0)
      have e1 : rdeg ε (Finsupp.single k 1) = rdeg ε (Finsupp.single l 1) := by
        rw [rdeg_single ε k hk, rdeg_single ε l hl, hkl]
      rw [rdeg_add, e1, ← rdeg_add, add_tsub_cancel_of_le hle]
      exact hR

theorem gen_stable (ε : Fin m → Bool) (i j : Fin n) (R : Set (Fin m → ℕ)) (s : Fin m × Fin n × Bool →₀ ℕ)
    (hs : ∀ k ∈ s.support, inF1 ε k) (hR : rdeg ε s ∈ R) : KopL ε i j (monomial s (1 : ℂ)) ∈ box ε R := by
  rw [KopL_apply]
  refine Submodule.sub_mem _ (Submodule.sum_mem _ fun a ha => ?_) (Submodule.sum_mem _ fun a ha => ?_)
  · have ha' : ε a = true := (Finset.mem_filter.mp ha).2
    exact term_mem_box ε R (a, i, false) (a, j, false) (by simp [inF1, ha']) (by simp [inF1, ha']) rfl s hs hR
  · have ha' : ε a = false := (Finset.mem_filter.mp ha).2
    exact term_mem_box ε R (a, j, true) (a, i, true) (by simp [inF1, ha']) (by simp [inF1, ha']) rfl s hs hR

theorem box_stable (ε : Fin m → Bool) (i j : Fin n) (R : Set (Fin m → ℕ)) :
    ∀ f ∈ box (n := n) ε R, KopL ε i j f ∈ box ε R := by
  intro f hf
  refine Submodule.span_induction (p := fun x _ => KopL ε i j x ∈ box ε R) ?_ ?_ ?_ ?_ hf
  · rintro x ⟨s, hs, hR, rfl⟩
    exact gen_stable ε i j R s hs hR
  · simp
  · intro x y _ _ hx hy; rw [map_add]; exact add_mem hx hy
  · intro r x _ hx; rw [map_smul]; exact Submodule.smul_mem _ r hx

def symW (u : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ) : ℂ := ∏ k ∈ u.support, ((u k).factorial : ℂ)

theorem symW_step (u : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ) (k) :
    symW (Finsupp.single k 1 + u) = 1 * ((u k : ℂ) + 1) * symW u := by
  have hu : ∀ v : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ,
      symW v = ∏ k, ((v k).factorial : ℂ) := fun v => by
    unfold symW
    refine Finset.prod_subset (Finset.subset_univ _) fun k _ hk => ?_
    have : v k = 0 := by simpa [Finsupp.mem_support_iff] using hk
    simp [this]
  rw [hu, hu, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k),
    ← Finset.mul_prod_erase Finset.univ (fun j => ((u j).factorial : ℂ)) (Finset.mem_univ k)]
  have hrest : ∏ j ∈ Finset.univ.erase k,
      (((Finsupp.single k 1 + u : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ) j).factorial : ℂ) =
      ∏ j ∈ Finset.univ.erase k, ((u j).factorial : ℂ) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    have hjk : j ≠ k := Finset.ne_of_mem_erase hj
    simp [Finsupp.single_apply, Ne.symm hjk]
  rw [hrest]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same]
  rw [add_comm 1 (u k), Nat.factorial_succ]
  push_cast; ring

theorem coeff_smul_X {τ : Type} [DecidableEq τ] (c : ℂ) (w0 u : τ) :
    (c • X w0 : MvPolynomial τ ℂ).coeff (Finsupp.single u 1) = if w0 = u then c else 0 := by
  rw [MvPolynomial.coeff_smul, coeff_X']
  by_cases h : w0 = u
  · subst h; simp
  · rw [if_neg (fun e => h ((Finsupp.single_left_inj one_ne_zero).mp e)), if_neg h]; simp

theorem expand_lin {τ : Type} [Fintype τ] [DecidableEq τ] (c : ℂ) (w0 : τ) :
    (c • X w0 : MvPolynomial τ ℂ) = ∑ u, (c • X w0 : MvPolynomial τ ℂ).coeff (Finsupp.single u 1) • X u := by
  simp_rw [coeff_smul_X, ite_smul, zero_smul]
  rw [Finset.sum_ite_eq]; simp

theorem symK_lin (ε : Fin m → Bool) (i j : Fin n) (v) :
    ∃ (c : ℂ) (w0 : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool)), symK ε i j (X v : Sym m n) = c • X w0 := by
  rcases v with ⟨a, i', b⟩ | ⟨a, i', b⟩ <;> simp only [symK, mkDerivation_X, Sum.elim_inl, Sum.elim_inr] <;>
    split_ifs <;>
    first
    | exact ⟨1, _, (one_smul _ _).symm⟩
    | exact ⟨-1, _, by rw [neg_smul, one_smul]⟩
    | exact ⟨0, Sum.inl (a, i', b), (zero_smul _ _).symm⟩

theorem symK_hlin (ε : Fin m → Bool) (i j : Fin n) (v) :
    symK ε i j (X v : Sym m n) = ∑ u, (symK ε i j (X v : Sym m n)).coeff (Finsupp.single u 1) • X u := by
  obtain ⟨c, w0, h⟩ := symK_lin ε i j v
  rw [h]; exact expand_lin c w0

theorem symK_tr (ε : Fin m → Bool) (i j : Fin n) (v u) :
    (symK ε j i (X u : Sym m n)).coeff (Finsupp.single v 1) = star ((symK ε i j (X v : Sym m n)).coeff (Finsupp.single u 1)) := by
  rcases v with ⟨a, i', b⟩ | ⟨a, i', b⟩ <;> rcases u with ⟨a', i'', b'⟩ | ⟨a', i'', b'⟩ <;>
    simp only [symK, mkDerivation_X, Sum.elim_inl, Sum.elim_inr] <;>
    split_ifs <;> simp_all [coeff_X', Finsupp.single_left_inj, MvPolynomial.coeff_neg] <;> aesop

end CoreC

open CoreC CoreC.G in
theorem formFacts : FormFacts := by
  intro m n ε c hc
  have hw : ∀ (s : Fin m × Fin n × Bool →₀ ℕ) k, (fun s => (wt c s : ℂ)) (Finsupp.single k 1 + s) =
      ((2 * c : ℝ) : ℂ) * ((s k : ℂ) + 1) * (fun s => (wt c s : ℂ)) s := fun s k => wt_step c s k
  have hst : ∀ s : Fin m × Fin n × Bool →₀ ℕ, star ((fun s => (wt c s : ℂ)) s) = (fun s => (wt c s : ℂ)) s :=
    fun s => Complex.conj_ofReal _
  have hpos : ∀ s : Fin m × Fin n × Bool →₀ ℕ, 0 < ((fun s => (wt c s : ℂ)) s).re := fun s => by
    simpa using wt_pos hc s
  refine ⟨fun p q => gf_herm _ hst p q, fun p hp => gf_pos _ hst hpos p hp, fun i j p q => ?_,
    fun i j R f hf => box_stable ε i j R f hf, fun i j s t => ⟨by simp [fform], ?_⟩⟩
  · rw [fform_eq_gf, fform_eq_gf, KopL_apply, KopL_apply, gf_sub_left, gf_sub_right, gf_sum_left, gf_sum_left,
      gf_sum_right, gf_sum_right]
    congr 1 <;> exact Finset.sum_congr rfl fun a _ => gf_adj _ hw _ _ _ _
  · exact der_adj (w := symW) 1 symW_step (symK ε i j) (symK ε j i) (symK_hlin ε i j) (symK_hlin ε j i)
      (symK_tr ε i j) s t

end PositivityTheory.Rg.Sw.LC
end
end

section

noncomputable section

open MvPolynomial MeasureTheory

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

theorem momLin : MomLin := by
  intro m n c hc P Q r
  have hP := NullS.integrable_pg c hc P
  have hQ := NullS.integrable_pg c hc Q
  constructor
  · unfold mom
    rw [← integral_add hP hQ]
    congr 1
    funext x
    simp [evX]
    ring
  · unfold mom
    rw [← integral_const_mul]
    congr 1
    funext x
    simp [evX]
    ring

end PositivityTheory.Rg.Sw.LC
end
end

section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

theorem fockMono_zero (c : ℝ) : fockMono c (0 : Fin m × Fin n × Bool →₀ ℕ) = (1 : PX m n) := by
  simp [fockMono]

theorem fock_C (c : ℝ) (r : ℂ) : fock c (C r : PX m n) = C r := by
  classical
  by_cases hr : r = 0
  · subst hr; simp [fock]
  · rw [fock, ← monomial_zero', support_monomial, if_neg hr, Finset.sum_singleton, coeff_monomial, if_pos rfl,
      fockMono_zero, smul_eq_C_mul, mul_one, monomial_zero']

theorem deg_lt (s : Fin m × Fin n × Bool →₀ ℕ) (k : Fin m × Fin n × Bool) (hk : s k ≠ 0)
    (t : Fin m × Fin n × Bool →₀ ℕ) (ht : ∀ x, t x ≤ (s - Finsupp.single k 1 : Fin m × Fin n × Bool →₀ ℕ) x) : ∑ x, t x < ∑ x, s x := by
  refine lt_of_le_of_lt (Finset.sum_le_sum fun x _ => ht x) ?_
  refine Finset.sum_lt_sum (fun x _ => by simp) ⟨k, Finset.mem_univ _, ?_⟩
  simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]
  omega

variable (hB : FockBasic)

include hB in
theorem pderiv_fock (c : ℝ) (hc : 0 < c) (k : Fin m × Fin n × Bool) (p : PX m n) :
    pderiv k (fock c p) = (2 * c : ℂ) • fock c (pderiv (flip k) p) := by
  classical
  obtain ⟨hL, -, hX⟩ := hB m n c hc
  induction p using MvPolynomial.induction_on with
  | C r => rw [fock_C, pderiv_C, pderiv_C, hL.map_zero, smul_zero]
  | add p q hp hq => rw [hL.map_add (f := _), map_add (f := _), hp, hq, map_add (f := _), hL.map_add (f := _), smul_add]
  | mul_X p j hp =>
    rw [mul_comm, hX, pderiv_cr, hp, map_smul, pderiv_mul, pderiv_X, hL.map_add (f := _), hX, Pi.single_apply]
    by_cases h : k = flip j
    · have h' : j = flip k := by rw [h, flip_flip]
      rw [if_pos h, if_pos h', one_mul, smul_add, add_comm]
    · have h' : ¬ j = flip k := fun e => h (by rw [e, flip_flip])
      rw [if_neg h, if_neg h', zero_mul, hL.map_zero, zero_smul, add_zero, zero_add]

variable (hM : OneMom)

include hB hM in
theorem mom_fock_X (c : ℝ) (hc : 0 < c) (k : Fin m × Fin n × Bool) (p : PX m n) :
    mom c (fock c (X k * p)) = (2 * c : ℂ) * mom c (fock c (pderiv (flip k) p)) := by
  obtain ⟨hL, -, hX⟩ := hB m n c hc
  have e1 := mom_pderiv hM c hc k (fock c p)
  have e2 : mom c (pderiv k (fock c p)) = (2 * c : ℂ) * mom c (fock c (pderiv (flip k) p)) := by
    rw [pderiv_fock hB c hc, mom_smul]
  rw [hX, cr_apply, mom_add hM c hc, ← neg_one_smul ℂ (pderiv k (fock c p)), mom_smul, mom_smul, ← e2, e1]
  ring

include hB hM in
theorem fockMom_of : FockMom := by
  intro m n c hc
  obtain ⟨hL, -, -⟩ := hB m n c hc
  have h1 : mom c (1 : PX m n) ≠ 0 := by
    rw [← C_1, ← monomial_zero', mom_monomial hM c hc, one_mul, phi]
    refine Finset.prod_ne_zero_iff.2 fun a _ => Finset.prod_ne_zero_iff.2 fun i _ => ?_
    simp only [Finsupp.coe_zero, Pi.zero_apply, g1, Nat.factorial_zero, Nat.cast_one, mul_one, zero_add,
      pow_one, if_true]
    exact_mod_cast (div_pos Real.pi_pos hc).ne'
  refine ⟨h1, ?_⟩
  let D : PX m n → ℂ := fun p => mom c (fock c p) - mom c (1 : PX m n) * contr c p
  have hDadd : ∀ p q, D (p + q) = D p + D q := by
    intro p q; simp only [D]; rw [hL.map_add (f := _), mom_add hM c hc, contr_add]; ring
  have hDC : ∀ r, D (C r) = 0 := by
    intro r; simp only [D]
    rw [fock_C, contr_C, C_eq_smul_one, mom_smul]; ring
  have hDX : ∀ k p, D (X k * p) = (2 * c : ℂ) * D (pderiv (flip k) p) := by
    intro k p; simp only [D]; rw [mom_fock_X hB hM c hc, contr_X_mul]; ring
  have hmono : ∀ N, ∀ s : Fin m × Fin n × Bool →₀ ℕ, ∑ x, s x = N → ∀ r, D (monomial s r) = 0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro s hs r
      by_cases h0 : s = 0
      · subst h0; rw [monomial_zero']; exact hDC r
      · obtain ⟨k, hk⟩ := Finsupp.ne_iff.1 h0
        have hk' : s k ≠ 0 := by simpa using hk
        have hs' : Finsupp.single k 1 + (s - Finsupp.single k 1) = s := by
          ext x
          simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
          split_ifs with hx
          · subst hx; omega
          · simp
        have hXm : monomial s r = (X k : PX m n) * monomial (s - Finsupp.single k 1) r := by
          rw [X, monomial_mul, one_mul, hs']
        rw [hXm, hDX, pderiv_monomial]
        have hlt : ∑ x, ((s - Finsupp.single k 1 - Finsupp.single (flip k) 1 : Fin m × Fin n × Bool →₀ ℕ) x) < N :=
          hs ▸ deg_lt s k hk' _ (fun x => by simp only [Finsupp.coe_tsub, Pi.sub_apply]; exact tsub_le_self)
        rw [ih _ hlt _ rfl, mul_zero]
  intro p
  have hD0 : D p = 0 := by
    induction p using MvPolynomial.induction_on' with
    | monomial s r => exact hmono _ s rfl r
    | add p q hp hq => rw [hDadd, hp, hq, add_zero]
  exact sub_eq_zero.1 hD0

theorem fockMom_of_basic (hB : FockBasic) : FockMom := fockMom_of hB oneMom

end PositivityTheory.Rg.Sw.LC
end
end

section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC.Core

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ}

theorem pderiv_eq_zero_of_supported {S : Set (Fin m × Fin n × Bool)} {g : PX m n} (hg : g ∈ supported ℂ S)
    {k : Fin m × Fin n × Bool} (hk : k ∉ S) : pderiv k g = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro h
  exact hk ((mem_supported.mp hg) h)

theorem pderiv_mem_supported {S : Set (Fin m × Fin n × Bool)} {g : PX m n} (hg : g ∈ supported ℂ S)
    (k : Fin m × Fin n × Bool) : pderiv k g ∈ supported ℂ S := by
  rw [supported_eq_adjoin_X] at hg
  induction hg using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, -, rfl⟩ := hx
    rw [pderiv_X]
    rcases eq_or_ne i k with rfl | h
    · simp only [Pi.single_eq_same]; exact Subalgebra.one_mem _
    · rw [Pi.single_eq_of_ne h]; exact Subalgebra.zero_mem _
  | algebraMap r => simp [Subalgebra.zero_mem]
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Subalgebra.add_mem _ hx hy
  | mul x y hx' hy' hx hy =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    have hx'' : x ∈ supported ℂ S := by rw [supported_eq_adjoin_X]; exact hx'
    have hy'' : y ∈ supported ℂ S := by rw [supported_eq_adjoin_X]; exact hy'
    exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ hx'' hy) (Subalgebra.mul_mem _ hy'' hx)

theorem mem_F1_iff_supported (ε : Fin m → Bool) (f : PX m n) : f ∈ F1 ε ↔ f ∈ supported ℂ {k | inF1 ε k} := Iff.rfl

theorem variable_mem_first_family (ε : Fin m → Bool) {k : Fin m × Fin n × Bool} (hk : inF1 ε k) : (X k : PX m n) ∈ F1 ε :=
  (mem_F1_iff_supported ε _).2 (X_mem_supported.2 hk)

theorem compact_operator_mul_second_family (ε : Fin m → Bool) (i j : Fin n) (f g : PX m n) (hg : g ∈ F2 ε) :
    KopL ε i j (f * g) = KopL ε i j f * g := by
  have h0 : ∀ k : Fin m × Fin n × Bool, inF1 ε k → pderiv k g = 0 := fun k hk =>
    pderiv_eq_zero_of_supported hg (by simpa using hk)
  have hK : ∀ h : PX m n, KopL ε i j h = ∑ a ∈ Finset.univ.filter (fun a => ε a = true), X (a, i, false) * pderiv (a, j, false) h -
      ∑ a ∈ Finset.univ.filter (fun a => ε a = false), X (a, j, true) * pderiv (a, i, true) h := by
    intro h; simp [KopL, LinearMap.sum_apply]
  rw [hK, hK]
  simp only [Derivation.leibniz, smul_eq_mul]
  have e1 : ∀ a ∈ Finset.univ.filter (fun a => ε a = true),
      X (a, i, false) * (f * pderiv (a, j, false) g + g * pderiv (a, j, false) f) =
        X (a, i, false) * pderiv (a, j, false) f * g := by
    intro a ha
    rw [h0 (a, j, false) (by simp [inF1, (Finset.mem_filter.mp ha).2])]; ring
  have e2 : ∀ a ∈ Finset.univ.filter (fun a => ε a = false),
      X (a, j, true) * (f * pderiv (a, i, true) g + g * pderiv (a, i, true) f) =
        X (a, j, true) * pderiv (a, i, true) f * g := by
    intro a ha
    rw [h0 (a, i, true) (by simp [inF1, (Finset.mem_filter.mp ha).2])]; ring
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, ← Finset.sum_mul, ← Finset.sum_mul, sub_mul]

theorem compact_algebra_mul_second_family (ε : Fin m → Bool) (w : Module.End ℂ (PX m n)) (hw : w ∈ kAlg ε) (f g : PX m n) (hg : g ∈ F2 ε) :
    w (f * g) = w f * g := by
  induction hw using Algebra.adjoin_induction generalizing f with
  | mem x hx =>
    obtain ⟨ij, rfl⟩ := hx
    exact compact_operator_mul_second_family ε ij.1 ij.2 f g hg
  | algebraMap r => simp [Algebra.algebraMap_eq_smul_one, smul_mul_assoc]
  | add x y _ _ hx hy => simp [hx, hy, add_mul]
  | mul x y _ _ hx hy => simp only [Module.End.mul_apply, hy, hx]

theorem first_operator_preserves_first_family (ε : Fin m → Bool) (c : ℝ) (a b : Fin m) (f : PX m n) (hf : f ∈ F1 ε) : D1 ε c a b f ∈ F1 ε := by
  have hp : ∀ k (g : PX m n), g ∈ F1 ε → pderiv k g ∈ F1 ε := fun k g hg => pderiv_mem_supported hg k
  have hm : ∀ g h : PX m n, g ∈ F1 ε → h ∈ F1 ε → g * h ∈ F1 ε := fun g h hg hh => Subalgebra.mul_mem _ hg hh
  unfold D1
  split_ifs with h1 h2 h2
  · refine Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ => hm _ _ (variable_mem_first_family ε ?_) (hp _ _ hf))
    simp [inF1, h2]
  · refine Submodule.sum_mem _ fun i _ => hm _ _ (variable_mem_first_family ε ?_) (hp _ _ hf)
    simp [inF1, ← h1]; simpa using h2
  · refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ =>
      hm _ _ (hm _ _ (variable_mem_first_family ε ?_) (variable_mem_first_family ε ?_)) hf)
    · simp [inF1, h2]
    · simp [inF1]; cases hb : ε b <;> simp_all
  · refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => hp _ _ (hp _ _ hf))

theorem adjoin_first_operators_preserves_family (ε : Fin m → Bool) (c : ℝ) (B : Module.End ℂ (PX m n)) (hBF : ∀ f ∈ F1 ε, B f ∈ F1 ε)
    (hB : ∀ a b, ∀ f ∈ F1 ε, B (D1 ε c a b f) = D1 ε c a b (B f)) (w : Module.End ℂ (PX m n))
    (hw : w ∈ Algebra.adjoin ℂ (Set.range fun ab : Fin m × Fin m => firstFamilyOperatorEnd (n := n) ε c ab.1 ab.2)) :
    (∀ f ∈ F1 ε, w f ∈ F1 ε) ∧ ∀ f ∈ F1 ε, B (w f) = w (B f) := by
  induction hw using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨ab, rfl⟩ := hx
    exact ⟨fun f hf => first_operator_preserves_first_family ε c ab.1 ab.2 f hf, fun f hf => hB ab.1 ab.2 f hf⟩
  | algebraMap r =>
    refine ⟨fun f hf => by simpa [Algebra.algebraMap_eq_smul_one] using Submodule.smul_mem _ r hf, fun f _ => ?_⟩
    simp [Algebra.algebraMap_eq_smul_one]
  | add x y _ _ hx hy =>
    exact ⟨fun f hf => by simpa using Submodule.add_mem _ (hx.1 f hf) (hy.1 f hf),
      fun f hf => by simp [hx.2 f hf, hy.2 f hf]⟩
  | mul x y _ _ hx hy =>
    exact ⟨fun f hf => hx.1 _ (hy.1 f hf), fun f hf => by
      simp only [Module.End.mul_apply]; rw [hx.2 _ (hy.1 f hf), hy.2 f hf]⟩

end PositivityTheory.Rg.Sw.LC.Core
end
end
