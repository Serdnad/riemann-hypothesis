module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.HilbertNinetyNorms.OrdLEqNegLog
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.HilbertNinetyNorms.Hilbert90NormOneUnitsOfUnrOfNotSplit
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.CosetMap
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.OneCoset
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle397
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.HilbertNinetyNorms.IwFacts
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

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Bc.ArchbcB.B.M4

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem TO_diagT (w : Pl E) (a : ℕ) (g : GLw a w) (hg : g ∈ TO a w) :
    ∃ d : Fin a → (w.adicCompletion E)ˣ, (∀ i, Valued.v (d i : w.adicCompletion E) = 1) ∧
      g = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin a) d := by
  obtain ⟨h0, h1⟩ := hg
  have hne : ∀ i, g.val i i ≠ 0 := fun i h => by
    have := h1 i; rw [h, map_zero] at this; exact zero_ne_one this
  refine ⟨fun i => Units.mk0 _ (hne i), fun i => h1 i, Units.ext ?_⟩
  rw [GlobalTheory.SmGL.val_diagT]
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · rw [diagonal_apply_ne _ hij, h0 i j hij]

theorem ordL_of_v_one {w : Pl E} {x : w.adicCompletion E} (hx : Valued.v x = 1) : ordL x = 0 := by
  rw [ordL_eq_neg_log', hx, ← WithZero.exp_zero, WithZero.log_exp, neg_zero]

def nEnt (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) {a : ℕ} (y : Fin a → ℤ) (d : Fin a → (w.adicCompletion E)ˣ)
    (i : Fin a) : (w.adicCompletion E)ˣ :=
  ϖ ^ y i * d i * (cjU w (ϖ ^ y i.rev * d i.rev))⁻¹

theorem nrm_tdiag (w : Pl E) (hw : ¬ IsSplitAt w) (ϖ : (w.adicCompletion E)ˣ) (a : ℕ) (y : Fin a → ℤ)
    (d : Fin a → (w.adicCompletion E)ˣ) :
    nrmL a w (tdiag ϖ y * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin a) d) =
      GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin a) (nEnt w ϖ y d) := by
  rw [nrmL_eq w hw, show tdiag ϖ y = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin a) (fun i => ϖ ^ y i) from rfl,
    ← map_mul, thL_diagT w hw, ← map_mul]
  rfl

theorem ordL_nEnt (hU : Unr E) (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) {a : ℕ} (y : Fin a → ℤ)
    (d : Fin a → (w.adicCompletion E)ˣ) (hd : ∀ i, Valued.v (d i : w.adicCompletion E) = 1) (i : Fin a) :
    ordL (nEnt w ϖ y d i : w.adicCompletion E) = nv y i := by
  have hP : ∀ j, ordL (((ϖ ^ y j : (w.adicCompletion E)ˣ)) : w.adicCompletion E) = y j := fun j => by
    rw [ordL_zpow_units, hϖ.1, mul_one]
  simp only [nEnt, Units.val_mul, Units.val_inv_eq_inv_val, cjU_val]
  rw [ordL_mul'' (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _))
      (inv_ne_zero ((_root_.map_ne_zero _).2 (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)))),
    ordL_mul'' (Units.ne_zero _) (Units.ne_zero _),
    ordL_inv'' ((_root_.map_ne_zero _).2 (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _))), ordL_cj hU,
    ordL_mul'' (Units.ne_zero _) (Units.ne_zero _), hP, hP, ordL_of_v_one (hd i), ordL_of_v_one (hd i.rev), nv]
  ring

theorem unq_diag (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ)
    (a : ℕ) (y : Fin a → ℤ) (hy : StrictAnti y) (τ τ' : GLw a w) (hτ : τ ∈ TO a w) (hτ' : τ' ∈ TO a w)
    (h : (nrmL a w (tdiag ϖ y * τ)).val.charpoly = (nrmL a w (tdiag ϖ y * τ')).val.charpoly) :
    ∃ g : GLw a w, g ∈ TO a w ∧ g⁻¹ * (tdiag ϖ y * τ) * thL a w g = tdiag ϖ y * τ' := by
  obtain ⟨d, hd, rfl⟩ := TO_diagT w a τ hτ
  obtain ⟨d', hd', rfl⟩ := TO_diagT w a τ' hτ'
  rw [nrm_tdiag w hw, nrm_tdiag w hw, GlobalTheory.SmGL.val_diagT, GlobalTheory.SmGL.val_diagT, charpoly_diagonal,
    charpoly_diagonal] at h
  have hcϖ : cjU w ϖ = ϖ := Units.ext hϖ.2
  have hee : ∀ i, nEnt w ϖ y d i = nEnt w ϖ y d' i := by
    intro i
    have hr : (∏ j, (X - C ((nEnt w ϖ y d' j : (w.adicCompletion E)ˣ) : w.adicCompletion E))).eval
        ((nEnt w ϖ y d i : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 0 := by
      rw [← h, eval_prod]; exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    rw [eval_prod, Finset.prod_eq_zero_iff] at hr
    obtain ⟨j, -, hj⟩ := hr
    rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hj
    have hvij : nv y i = nv y j := by
      rw [← ordL_nEnt hU w ϖ hϖ y d hd i, hj, ordL_nEnt hU w ϖ hϖ y d' hd' j]
    have hij := (nv_strictAnti hy).injective hvij
    subst hij
    exact Units.ext hj
  have hsplit : ∀ (e : Fin a → (w.adicCompletion E)ˣ) i, nEnt w ϖ y e i =
      (ϖ ^ y i * (cjU w (ϖ ^ y i.rev))⁻¹) * (e i * (cjU w (e i.rev))⁻¹) := fun e i => by
    simp only [nEnt, map_mul, mul_inv]; rw [mul_mul_mul_comm]
  set r : Fin a → (w.adicCompletion E)ˣ := fun i => d i * (d' i)⁻¹ with hrdef
  have hrr : ∀ i, r i = cjU w (r i.rev) := by
    intro i
    have h1 := hee i
    rw [hsplit, hsplit] at h1
    have h2 := mul_left_cancel h1
    simp only [hrdef, map_mul, map_inv]
    apply Units.ext
    have h3 := congrArg Units.val h2
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, cjU_val] at h3 ⊢
    field_simp at h3 ⊢
    linear_combination h3
  have hrv : ∀ i, Valued.v (r i : w.adicCompletion E) = 1 := fun i => by
    simp [hrdef, Units.val_mul, Units.val_inv_eq_inv_val, map_inv₀, hd, hd']
  have hmid : ∀ i, i.rev = i → ∃ Z : (w.adicCompletion E)ˣ, Valued.v (Z : w.adicCompletion E) = 1 ∧
      Z * cjU w Z = r i := fun i hi => by
    have hfix : cj w (r i : w.adicCompletion E) = r i := by
      have := congrArg Units.val (hrr i); rw [hi] at this; exact this.symm
    obtain ⟨z, hz, hz'⟩ := (hilbert90_norm_one_units_of_unr_of_not_split hU w hw).1 _ (hrv i) hfix
    have hz0 : z ≠ 0 := by intro h; rw [h, map_zero] at hz; exact zero_ne_one hz
    exact ⟨Units.mk0 z hz0, hz, Units.ext (by simpa using hz')⟩
  let hh : Fin a → (w.adicCompletion E)ˣ := fun i =>
    if h : i < i.rev then r i else if h' : i.rev = i then Classical.choose (hmid i h') else 1
  have hhv : ∀ i, Valued.v (hh i : w.adicCompletion E) = 1 := fun i => by
    simp only [hh]
    split_ifs with h h'
    · exact hrv i
    · exact (Classical.choose_spec (hmid i h')).1
    · simp
  have hk : ∀ i, hh i * cjU w (hh i.rev) = r i := by
    intro i
    rcases lt_trichotomy i i.rev with h | h | h
    · have e1 : hh i = r i := by simp only [hh, dif_pos h]
      have e2 : hh i.rev = 1 := by
        have hn : ¬ i.rev < i.rev.rev := by rw [Fin.rev_rev]; exact not_lt.2 h.le
        have hn' : ¬ i.rev.rev = i.rev := by rw [Fin.rev_rev]; exact h.ne
        simp only [hh, dif_neg hn, dif_neg hn']
      rw [e1, e2, map_one, mul_one]
    · have hi : i.rev = i := h.symm
      have hn : ¬ i < i.rev := by rw [hi]; exact lt_irrefl i
      have e1 : hh i = Classical.choose (hmid i hi) := by simp only [hh, dif_neg hn, dif_pos hi]
      rw [hi, e1]
      exact (Classical.choose_spec (hmid i hi)).2
    · have hn : ¬ i < i.rev := not_lt.2 h.le
      have hn' : ¬ i.rev = i := h.ne
      have e1 : hh i = 1 := by simp only [hh, dif_neg hn, dif_neg hn']
      have hp : i.rev < i.rev.rev := by rw [Fin.rev_rev]; exact h
      have e2 : hh i.rev = r i.rev := by simp only [hh, dif_pos hp]
      rw [e1, e2, one_mul, hrr i]
  refine ⟨GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin a) hh, ⟨fun i j hij => ?_, fun i => ?_⟩, ?_⟩
  · rw [GlobalTheory.SmGL.val_diagT, diagonal_apply_ne _ hij]
  · rw [GlobalTheory.SmGL.val_diagT, diagonal_apply_eq]; exact hhv i
  rw [thL_diagT w hw, show tdiag ϖ y = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin a) (fun i => ϖ ^ y i) from rfl,
    ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
  congr 1
  funext i
  have hki := congrArg Units.val (hk i)
  apply Units.ext
  simp only [Pi.mul_apply, Pi.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, cjU_val, hrdef] at hki ⊢
  field_simp at hki ⊢
  linear_combination -hki

end PositivityTheory.Rg.Bc.ArchbcB.B.M4
end
end

section

noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Bc.ArchbcB.B.M4

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mem_dcos_of_ne (w : Pl E) (n : ℕ) (t δ : GLw n w) (hδ : dcos n w t δ ≠ 0) :
    δ ∈ PositivityTheory.Lbc.dcos (iwGL n w) t := by
  unfold dcos at hδ
  split_ifs at hδ with h
  · exact h
  · exact absurd rfl hδ

private theorem apply_eq_zero_of_mem_tor_of_ne {k : Type} [Field k] (N : ℕ) (x : GL (Fin N) k) (hx : x ∈ PositivityTheory.Lbc.Tor k N)
    (i j : Fin N) (h : i ≠ j) : (x : Matrix (Fin N) (Fin N) k) i j = 0 := by
  obtain ⟨s, rfl⟩ := hx
  simp [PositivityTheory.Lbc.torEmb, GlobalTheory.SmGL.leviEmb, Matrix.reindex_apply, Matrix.submatrix_apply]
  have hne : ((GlobalTheory.SmGL.stdBlocks (PositivityTheory.Lbc.ones N) (PositivityTheory.Lbc.sum_ones N)).symm i).1 ≠ ((GlobalTheory.SmGL.stdBlocks (PositivityTheory.Lbc.ones N) (PositivityTheory.Lbc.sum_ones N)).symm j).1 := by
    intro hfst
    apply h
    have hs : (GlobalTheory.SmGL.stdBlocks (PositivityTheory.Lbc.ones N) (PositivityTheory.Lbc.sum_ones N)).symm i = (GlobalTheory.SmGL.stdBlocks (PositivityTheory.Lbc.ones N) (PositivityTheory.Lbc.sum_ones N)).symm j := by
      refine Sigma.ext hfst ?_
      apply (Fin.heq_ext_iff (congrArg _ hfst)).2
      have h1 : (((GlobalTheory.SmGL.stdBlocks (PositivityTheory.Lbc.ones N) (PositivityTheory.Lbc.sum_ones N)).symm i).2 : ℕ) < 1 :=
        ((GlobalTheory.SmGL.stdBlocks (PositivityTheory.Lbc.ones N) (PositivityTheory.Lbc.sum_ones N)).symm i).2.isLt
      have h2 : (((GlobalTheory.SmGL.stdBlocks (PositivityTheory.Lbc.ones N) (PositivityTheory.Lbc.sum_ones N)).symm j).2 : ℕ) < 1 :=
        ((GlobalTheory.SmGL.stdBlocks (PositivityTheory.Lbc.ones N) (PositivityTheory.Lbc.sum_ones N)).symm j).2.isLt
      omega
    simpa using congrArg (GlobalTheory.SmGL.stdBlocks (PositivityTheory.Lbc.ones N) (PositivityTheory.Lbc.sum_ones N)) hs
  convert Matrix.blockDiagonal'_apply_ne (fun (a : Fin N) ↦ (s a).val) _ _ hne

private theorem mem_TO_of_mem_iwGL_inf_tor (w : Pl E) (n : ℕ) (κ : GLw n w)
    (hκ : κ ∈ iwGL n w ⊓ PositivityTheory.Lbc.Tor (w.adicCompletion E) n) : κ ∈ TO n w := by
  refine ⟨fun i j hij => apply_eq_zero_of_mem_tor_of_ne n κ hκ.2 i j hij, fun i => ?_⟩
  have hmul : κ.val i i * (κ⁻¹ : GLw n w).val i i = 1 := by
    have h1 : (κ * κ⁻¹ : GLw n w).val i i = 1 := by simp
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i] at h1
    · exact h1
    · intro b _ hb
      rw [apply_eq_zero_of_mem_tor_of_ne n κ hκ.2 i b (Ne.symm hb), zero_mul]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have ha := iw_entry_le hκ.1 i i
  have hb := iw_entry_le (inv_mem hκ.1) i i
  have hv : ValuativeRel.valuation _ (κ.val i i) = 1 := by
    have hm := congrArg (ValuativeRel.valuation (w.adicCompletion E)) hmul
    rw [map_mul, map_one] at hm
    refine le_antisymm ha ?_
    calc (1 : ValuativeRel.ValueGroupWithZero _) = _ := hm.symm
      _ ≤ _ * 1 := by gcongr
      _ = _ := mul_one _
  haveI := Valuation.Compatible.ofValuation (Valued.v : Valuation (w.adicCompletion E) _)
  exact (ValuativeRel.isEquiv (Valued.v : Valuation (w.adicCompletion E) _)
    (ValuativeRel.valuation _)).eq_one_iff_eq_one.2 hv

theorem contr_id_pf (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (n : ℕ) (y : Fin n → ℤ)
    (hy : StrictAnti y) (δ : GLw n w) (hδ : dcos n w (tdiag ϖ y) δ ≠ 0) :
    ∃ m ∈ iwGL n w, ∃ τ ∈ TO n w, m⁻¹ * δ * m = tdiag ϖ y * τ := by
  obtain ⟨j, hj, κ, hκ, he⟩ := GlobalTheory.T.twisted_iwahori_first_identity n (iwGL n w) 1 1 (tdiag ϖ y) (iwahori_GL_trivial_admissible w n)
    (goodT_id w ϖ hϖ n y hy) δ (mem_dcos_of_ne w n _ δ hδ)
  refine ⟨j⁻¹, inv_mem hj, κ, mem_TO_of_mem_iwGL_inf_tor w n κ hκ, ?_⟩
  simp only [inv_inv, MulAut.one_apply] at he ⊢
  rw [he]
  group

end PositivityTheory.Rg.Bc.ArchbcB.B.M4
end
end
