module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
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
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Lean.Meta.Basic
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Polynomial.Vieta

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

noncomputable section

open MvPolynomial

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms.Comb

open MvPolynomial Finset Equiv

noncomputable section

open scoped Classical

variable {m : ℕ}

def pcnt {n : ℕ} (w : Fin n → Fin m) (t : ℕ) (i : Fin m) : ℕ :=
  (univ.filter (fun s : Fin n => (s : ℕ) < t ∧ w s = i)).card

def IsLattice {n : ℕ} (w : Fin n → Fin m) : Prop :=
  ∀ t ≤ n, ∀ i j : Fin m, i ≤ j → pcnt w t j ≤ pcnt w t i

def latticeWords (n : ℕ) (lam : Fin m → ℕ) : Finset (Fin n → Fin m) :=
  univ.filter (fun w => IsLattice w ∧ ∀ i, pcnt w n i = lam i)

theorem pcnt_castSucc_snoc {n : ℕ} (w : Fin n → Fin m) (a : Fin m) (t : ℕ) (ht : t ≤ n) (i : Fin m) :
    pcnt (Fin.snoc w a : Fin (n + 1) → Fin m) t i = pcnt w t i := by
  unfold pcnt
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.val_castSucc, Fin.snoc_last, Fin.val_last]
  rw [if_neg (by omega), add_zero]

theorem pcnt_snoc_last {n : ℕ} (w : Fin n → Fin m) (a : Fin m) (i : Fin m) :
    pcnt (Fin.snoc w a : Fin (n + 1) → Fin m) (n + 1) i = pcnt w n i + if a = i then 1 else 0 := by
  unfold pcnt
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.val_castSucc, Fin.snoc_last, Fin.val_last]
  congr 1
  · refine Finset.sum_congr rfl fun s _ => ?_
    have := s.isLt
    by_cases h : w s = i <;> simp [h, this, Nat.lt_succ_of_lt this]
  · simp

theorem pcnt_zero {n : ℕ} (w : Fin n → Fin m) (i : Fin m) : pcnt w 0 i = 0 := by
  unfold pcnt; simp

theorem pcnt_le_of_le {n : ℕ} (w : Fin n → Fin m) {t t' : ℕ} (h : t ≤ t') (i : Fin m) :
    pcnt w t i ≤ pcnt w t' i := by
  unfold pcnt
  exact Finset.card_le_card (fun s => by simp only [mem_filter, mem_univ, true_and]; omega)

theorem sum_pcnt {n : ℕ} (w : Fin n → Fin m) : ∑ i, pcnt w n i = n := by
  unfold pcnt
  rw [← Finset.card_biUnion]
  · have : (univ : Finset (Fin m)).biUnion (fun i => univ.filter (fun s : Fin n => (s : ℕ) < n ∧ w s = i))
        = univ := by
      ext s; simp
    rw [this, Finset.card_univ, Fintype.card_fin]
  · intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_filter]
    rintro s _ ⟨_, h1⟩ ⟨_, h2⟩
    exact hij (h1 ▸ h2)

theorem update_pred_sub (lam : Fin m → ℕ) (a i : Fin m) (h : 1 ≤ lam a) :
    Function.update lam a (lam a - 1) i + (if a = i then 1 else 0) = lam i := by
  by_cases hai : a = i
  · subst hai; simp; omega
  · simp [Function.update_of_ne (Ne.symm hai), hai]

theorem card_latticeWords_succ (n : ℕ) (lam : Fin m → ℕ) (hlam : Antitone lam) :
    (latticeWords (n + 1) lam).card =
      ∑ a : Fin m, if 1 ≤ lam a then (latticeWords n (Function.update lam a (lam a - 1))).card else 0 := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun w => w (Fin.last n)) (t := univ)
    (fun _ _ => mem_univ _)]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with ha
  · refine Finset.card_nbij' (fun w => Fin.init w) (fun w => Fin.snoc w a) ?_ ?_ ?_ ?_
    · intro w hw
      simp only [coe_filter, Set.mem_ofPred_eq, latticeWords, mem_filter, mem_univ, true_and] at hw ⊢
      obtain ⟨⟨hlat, hcont⟩, hlast⟩ := hw
      have hw' : w = Fin.snoc (Fin.init w) a := by
        rw [← hlast]; exact (Fin.snoc_init_self w).symm
      refine ⟨fun t ht i j hij => ?_, fun i => ?_⟩
      · have := hlat t (by omega) i j hij
        rwa [hw', pcnt_castSucc_snoc _ _ _ ht, pcnt_castSucc_snoc _ _ _ ht] at this
      · have := hcont i
        rw [hw', pcnt_snoc_last] at this
        have h2 := update_pred_sub lam a i ha
        omega
    · intro w hw
      simp only [coe_filter, Set.mem_ofPred_eq, latticeWords, mem_filter, mem_univ, true_and] at hw ⊢
      obtain ⟨hlat, hcont⟩ := hw
      refine ⟨⟨fun t ht i j hij => ?_, fun i => ?_⟩, by simp⟩
      · rcases Nat.lt_or_ge t (n + 1) with htn | htn
        · rw [pcnt_castSucc_snoc _ _ _ (by omega), pcnt_castSucc_snoc _ _ _ (by omega)]
          exact hlat t (by omega) i j hij
        · have ht' : t = n + 1 := by omega
          subst ht'
          rw [pcnt_snoc_last, pcnt_snoc_last, hcont, hcont, update_pred_sub lam a i ha,
            update_pred_sub lam a j ha]
          exact hlam hij
      · rw [pcnt_snoc_last, hcont, update_pred_sub lam a i ha]
    · intro w hw
      simp only [coe_filter, Set.mem_ofPred_eq] at hw
      rw [← hw.2]; exact Fin.snoc_init_self w
    · intro w hw
      simp
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro w hw hlast
    simp only [latticeWords, mem_filter, mem_univ, true_and] at hw
    have := hw.2 a
    have h1 : 1 ≤ pcnt w (n + 1) a := by
      unfold pcnt
      exact Finset.card_pos.mpr ⟨Fin.last n, by simp [hlast]⟩
    omega

theorem latticeWords_eq_empty_of_sum_ne (n : ℕ) (lam : Fin m → ℕ) (h : ∑ i, lam i ≠ n) :
    latticeWords n lam = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro w hw
  simp only [latticeWords, mem_filter, mem_univ, true_and] at hw
  apply h
  rw [← sum_pcnt w]
  exact Finset.sum_congr rfl fun i _ => (hw.2 i).symm

theorem latticeWords_eq_empty_of_not_antitone (n : ℕ) (lam : Fin m → ℕ) (h : ¬ Antitone lam) :
    latticeWords n lam = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro w hw
  simp only [latticeWords, mem_filter, mem_univ, true_and] at hw
  apply h
  intro i j hij
  rw [← hw.2 i, ← hw.2 j]
  exact hw.1 n le_rfl i j hij

end

end GroundTheory.Heights₂.Heights.RestTerms.Comb
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms.Coinv

open MvPolynomial Finset

noncomputable section

variable (K : Type*) [Field K] (f n : ℕ)

def bps (m : ℕ) (b : Fin f) : MvPolynomial (Fin f × Fin n) K := ∑ i : Fin n, X (b, i) ^ m

def psumIdeal : Ideal (MvPolynomial (Fin f × Fin n) K) :=
  Ideal.span {P | ∃ m b, 1 ≤ m ∧ m ≤ n ∧ P = bps K f n m b}

variable {K f n}

theorem bps_mem_psumIdeal {m : ℕ} (b : Fin f) (h1 : 1 ≤ m) (h2 : m ≤ n) :
    bps K f n m b ∈ psumIdeal K f n :=
  Ideal.subset_span ⟨m, b, h1, h2, rfl⟩

theorem rename_psum (b : Fin f) (m : ℕ) :
    rename (fun i : Fin n => (b, i)) (psum (Fin n) K m) = bps K f n m b := by
  simp [psum, bps]

variable [CharZero K]

theorem rename_esymm_mem {m : ℕ} (b : Fin f) (h1 : 1 ≤ m) (h2 : m ≤ n) :
    rename (fun i : Fin n => (b, i)) (esymm (Fin n) K m) ∈ psumIdeal K f n := by
  have hN := congrArg (rename (fun i : Fin n => (b, i))) (mul_esymm_eq_sum (Fin n) K m)

  simp only [map_mul, map_pow, map_neg, map_one, map_natCast, map_sum] at hN
  have hmem : ((m : ℕ) : MvPolynomial (Fin f × Fin n) K) *
      rename (fun i : Fin n => (b, i)) (esymm (Fin n) K m) ∈ psumIdeal K f n := by
    rw [hN]
    refine Ideal.mul_mem_left _ _ (Ideal.sum_mem _ fun a ha => ?_)
    rw [Finset.mem_filter] at ha
    have ha1 : a.1 + a.2 = m := by simpa using ha.1
    rw [rename_psum]
    exact Ideal.mul_mem_left _ _ (bps_mem_psumIdeal b (by have := ha.2; omega) (by omega))
  have hm : (m : K) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have : rename (fun i : Fin n => (b, i)) (esymm (Fin n) K m) =
      C ((m : K)⁻¹) * (((m : ℕ) : MvPolynomial (Fin f × Fin n) K) *
        rename (fun i : Fin n => (b, i)) (esymm (Fin n) K m)) := by
    rw [← mul_assoc, ← map_natCast C, ← C_mul, inv_mul_cancel₀ hm, C_1, one_mul]
  rw [this]
  exact Ideal.mul_mem_left _ _ hmem

theorem prod_X_add_eq_pow (b : Fin f) :
    (∏ i : Fin n, (Polynomial.X + Polynomial.C
      (Ideal.Quotient.mk (psumIdeal K f n) (X (b, i))))) = Polynomial.X ^ n := by
  set φ : MvPolynomial (Fin n) K →+* MvPolynomial (Fin f × Fin n) K ⧸ psumIdeal K f n :=
    (Ideal.Quotient.mk (psumIdeal K f n)).comp (rename (fun i : Fin n => (b, i))).toRingHom
  have hV := congrArg (Polynomial.map φ) (MvPolynomial.prod_C_add_X_eq_sum_esymm K (Fin n))

  simp only [Polynomial.map_prod, Polynomial.map_add (f := _), Polynomial.map_X, Polynomial.map_C,
  Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, Fintype.card_fin] at hV
  have hφX : ∀ i : Fin n, φ (X i) = Ideal.Quotient.mk (psumIdeal K f n) (X (b, i)) := by
    intro i; simp [φ]
  simp only [hφX] at hV
  rw [hV, Finset.sum_range_succ']
  have hz : ∀ j ∈ range n, Polynomial.C (φ (esymm (Fin n) K (j + 1))) *
      (Polynomial.X : Polynomial (MvPolynomial (Fin f × Fin n) K ⧸ psumIdeal K f n)) ^ (n - (j + 1)) = 0 := by
    intro j hj
    rw [Finset.mem_range] at hj
    have : φ (esymm (Fin n) K (j + 1)) = 0 := by
      simp only [φ, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (rename_esymm_mem b (by omega) (by omega))
    rw [this, map_zero, zero_mul]
  rw [Finset.sum_eq_zero hz, zero_add]
  simp [esymm_zero]

variable (K) in
omit [CharZero K] in
theorem psumIdeal_le_ker :
    psumIdeal K f n ≤ RingHom.ker (constantCoeff : MvPolynomial (Fin f × Fin n) K →+* K) := by
  refine Ideal.span_le.mpr ?_
  rintro P ⟨m, b, h1, -, rfl⟩
  simp [bps, constantCoeff_X, zero_pow (show m ≠ 0 by omega)]

theorem psumIdeal_ne_top : psumIdeal K f n ≠ ⊤ := by
  intro h
  have h1 : (1 : MvPolynomial (Fin f × Fin n) K) ∈ RingHom.ker constantCoeff :=
    psumIdeal_le_ker K (h ▸ Submodule.mem_top)
  simp at h1

theorem exists_reduction (b : Fin f) (k : Fin n) :
    ∃ c : ℕ → MvPolynomial ↥(Finset.Ioi k) K,
      X (b, k) ^ ((k : ℕ) + 1) + ∑ j ∈ range ((k : ℕ) + 1),
        rename (fun s : ↥(Finset.Ioi k) => (b, (s : Fin n))) (c j) * X (b, k) ^ j ∈
        psumIdeal K f n := by
  classical
  set ψ := rename (R := K) (fun s : ↥(Finset.Ioi k) => (b, (s : Fin n))) with hψ
  have hinj : Function.Injective (fun s : ↥(Finset.Ioi k) => (b, (s : Fin n))) := by
    intro s t h
    exact Subtype.ext (Prod.ext_iff.mp h).2
  set A' : Polynomial (MvPolynomial ↥(Finset.Ioi k) K) :=
    ∏ s : ↥(Finset.Ioi k), (Polynomial.X + Polynomial.C (X s)) with hA'
  have hA'm : A'.Monic := Polynomial.monic_prod_of_monic _ _ (fun s _ => Polynomial.monic_X_add_C _)
  have hA'deg : A'.natDegree = n - 1 - k := by
    rw [hA', Polynomial.natDegree_prod_of_monic _ _ (fun s _ => Polynomial.monic_X_add_C _)]
    simp [Fin.card_Ioi]
  set Sh' := (Polynomial.X ^ n : Polynomial (MvPolynomial ↥(Finset.Ioi k) K)) /ₘ A' with hSh'
  have hk : (k : ℕ) < n := k.isLt
  have hSdeg : Sh'.natDegree = (k : ℕ) + 1 := by
    rw [hSh', Polynomial.natDegree_divByMonic _ hA'm, Polynomial.natDegree_X_pow, hA'deg]
    omega
  have hSlead : Sh'.leadingCoeff = 1 := by
    rw [hSh', Polynomial.leadingCoeff_divByMonic_of_monic hA'm]
    · simp
    · rw [Polynomial.degree_eq_natDegree hA'm.ne_zero, Polynomial.degree_X_pow, hA'deg]
      exact_mod_cast (by omega : n - 1 - (k : ℕ) ≤ n)

  set I := psumIdeal K f n
  have : Nontrivial (MvPolynomial (Fin f × Fin n) K ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr psumIdeal_ne_top
  set π := Ideal.Quotient.mk I
  have hsplit := prod_X_add_eq_pow (K := K) (f := f) (n := n) b
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : Fin n => k < i)] at hsplit
  have hfilt : Finset.univ.filter (fun i : Fin n => k < i) = Finset.Ioi k := by
    ext i; simp
  rw [hfilt] at hsplit
  have hmapA : A'.map (π.comp ψ.toRingHom) =
      ∏ i ∈ Finset.Ioi k, (Polynomial.X + Polynomial.C (π (X (b, i)))) := by
    rw [hA', Polynomial.map_prod, ← Finset.prod_coe_sort (Finset.Ioi k)]
    simp [hψ, π]
  have key : Sh'.map (π.comp ψ.toRingHom) =
      ∏ i ∈ Finset.univ.filter (fun i : Fin n => ¬ k < i),
        (Polynomial.X + Polynomial.C (π (X (b, i)))) := by
    rw [hSh', Polynomial.map_divByMonic _ hA'm, Polynomial.map_pow, Polynomial.map_X]
    refine (Polynomial.div_modByMonic_unique _ (0 : Polynomial (MvPolynomial (Fin f × Fin n) K ⧸ I))
      (hA'm.map (π.comp ψ.toRingHom)) ⟨?_, ?_⟩).1
    · rw [zero_add, hmapA, hsplit]
    · rw [Polynomial.degree_zero]
      exact bot_lt_iff_ne_bot.mpr (fun h => (hA'm.map (π.comp ψ.toRingHom)).ne_zero
        (Polynomial.degree_eq_bot.mp h))
  have hev : π (Polynomial.eval (-X (b, k)) (Sh'.map ψ.toRingHom)) = 0 := by
    rw [← Polynomial.eval₂_at_apply π, ← Polynomial.eval_map, Polynomial.map_map, key,
      Polynomial.eval_prod]
    refine Finset.prod_eq_zero (i := k) (by simp) ?_
    simp
  have hmem : Polynomial.eval (-X (b, k)) (Sh'.map ψ.toRingHom) ∈ I :=
    Ideal.Quotient.eq_zero_iff_mem.mp hev

  refine ⟨fun j => (-1) ^ ((k : ℕ) + 1 + j) * Sh'.coeff j, ?_⟩
  have hdegmap : (Sh'.map ψ.toRingHom).natDegree = (k : ℕ) + 1 := by
    rw [Polynomial.natDegree_map_eq_of_injective (rename_injective _ hinj), hSdeg]
  rw [Polynomial.eval_eq_sum_range, hdegmap, Finset.sum_range_succ] at hmem
  have htop : (Sh'.map ψ.toRingHom).coeff ((k : ℕ) + 1) = 1 := by
    rw [Polynomial.coeff_map, ← hSdeg]
    change ψ (Sh'.leadingCoeff) = 1
    rw [hSlead, map_one]
  rw [htop, one_mul] at hmem
  have := Ideal.mul_mem_left I ((-1) ^ ((k : ℕ) + 1)) hmem
  convert this using 1
  rw [mul_add, Finset.mul_sum, neg_pow (X (b, k) : MvPolynomial (Fin f × Fin n) K), ← mul_assoc, ← pow_add, ← two_mul,
    pow_mul, neg_one_sq, one_pow, one_mul, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.coeff_map, neg_pow (X (b, k) : MvPolynomial (Fin f × Fin n) K)]
  simp only [map_mul, map_pow, map_neg, map_one, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  ring

end

end GroundTheory.Heights₂.Heights.RestTerms.Coinv
end
