module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle403
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle141
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle126
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle125
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle144
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle080

@[expose] public section

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.UnipFlip

theorem longElt_conj_apply {R : Type} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    ((longElt n R : Matrix (Fin n) (Fin n) R) * A * (longElt n R : Matrix (Fin n) (Fin n) R)) i j
      = A i.rev j.rev := by
  simp only [Matrix.mul_apply, longElt, Matrix.of_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_eq_single j.rev]
  · simp
  · intro b _ hb; rw [if_neg]; intro e; exact hb (by rw [e, Fin.rev_rev])
  · simp

theorem inv_apply_succ {R : Type} [CommRing R] {n : ℕ} {u : GL (Fin n) R} (hu : u ∈ unipB R (Fin n))
    (p q : Fin n) (h : (q : ℕ) = p + 1) :
    ((u⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) p q = - (u : Matrix (Fin n) (Fin n) R) p q := by
  have hv : u⁻¹ ∈ unipB R (Fin n) := inv_mem hu
  rw [mem_unipB] at hu hv
  have hpq : p ≠ q := by intro e; subst e; omega
  have key := congrFun (congrFun (congrArg (fun g : GL (Fin n) R => (g : Matrix (Fin n) (Fin n) R)) (mul_inv_cancel u)) p) q
  simp only [Units.val_mul, Units.val_one, Matrix.mul_apply, Matrix.one_apply_ne hpq] at key
  rw [Fintype.sum_eq_add p q hpq] at key
  · rw [hu.2 p, hv.2 q, one_mul, mul_one] at key
    linear_combination key
  · intro c ⟨hcp, hcq⟩
    rcases lt_or_gt_of_ne hcp with hlt | hgt
    · rw [hu.1 p c hlt, zero_mul]
    · have : q < c := by
        have h1 : (p : ℕ) < c := hgt
        have h2 : (c : ℕ) ≠ q := fun e => hcq (Fin.ext e)
        show (q : ℕ) < c
        omega
      rw [hv.1 c q this, mul_zero]

theorem longElt_invT_conj_unipB : ∀ (R : Type) [CommRing R] (n : ℕ) (u : GL (Fin n) R), u ∈ unipB R (Fin n) →
    longElt n R * GlobalTheory.CuspRep.invT n R u * longElt n R ∈ unipB R (Fin n) ∧
      superDiag (longElt n R * GlobalTheory.CuspRep.invT n R u * longElt n R) = -superDiag u := by
  intro R _ n u hu
  have hv : u⁻¹ ∈ unipB R (Fin n) := inv_mem hu
  have hval : ∀ i j : Fin n,
      ((longElt n R * GlobalTheory.CuspRep.invT n R u * longElt n R : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j
        = ((u⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) j.rev i.rev := by
    intro i j
    rw [Units.val_mul, Units.val_mul]
    rw [longElt_conj_apply]
    rfl
  rw [mem_unipB] at hv
  refine ⟨?_, ?_⟩
  · rw [mem_unipB]
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [hval]; exact hv.1 _ _ (Fin.rev_lt_rev.2 hij)
    · rw [hval]; exact hv.2 _
  · simp only [superDiag, Finset.sum_filter]
    simp_rw [hval]
    rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Fintype.sum_equiv Fin.revPerm _ _ fun p => ?_
    rw [← Finset.sum_neg_distrib]
    refine Fintype.sum_equiv Fin.revPerm _ _ fun q => ?_
    simp only [Fin.revPerm_apply, Fin.rev_rev]

    have hiff : ((q.rev : Fin n) : ℕ) = (p.rev : ℕ) + 1 ↔ (p : ℕ) = q + 1 := by
      simp only [Fin.val_rev]; have := p.isLt; have := q.isLt; omega
    by_cases h : (p : ℕ) = q + 1
    · rw [if_pos h, if_pos (hiff.2 h), inv_apply_succ hu p.rev q.rev (hiff.2 h)]
    · rw [if_neg h, if_neg (mt hiff.1 h), neg_zero]

end GlobalTheory.UnipFlip
end
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ThetaRad

theorem mem_unipRad_iff_entries {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
    {e : (Σ a, m a) ≃ n} {g : GL n R} :
    g ∈ unipRad R e ↔ ∀ i j, blk e j ≤ blk e i → (g : Matrix n n R) i j = (1 : Matrix n n R) i j := by
  rw [mem_unipRad]
  constructor
  · rintro ⟨hp, hd⟩ i j hij
    obtain ⟨⟨c, i⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨d, j⟩, rfl⟩ := e.surjective j
    simp only [blk_apply] at hij
    rcases hij.lt_or_eq with hlt | rfl
    · rw [mem_parab_iff.1 hp c d i j hlt, Matrix.one_apply_ne]
      intro hh
      have := congrArg Sigma.fst (e.injective hh)
      exact hlt.ne' this
    · rw [hd]
      simp only [Matrix.one_apply, e.injective.eq_iff, Sigma.mk.inj_iff, heq_eq_eq, true_and]
  · intro h
    refine ⟨mem_parab.2 fun i j hij => ?_, fun c i j => ?_⟩
    · rw [h i j hij.le, Matrix.one_apply_ne]
      rintro rfl
      exact lt_irrefl _ hij
    · rw [h _ _ (by simp)]
      simp only [Matrix.one_apply, e.injective.eq_iff, Sigma.mk.inj_iff, heq_eq_eq, true_and]

theorem blk_stdBlocks_two {a b n : ℕ} (h : ∑ i, ![a, b] i = n) (p : Fin n) :
    blk (stdBlocks ![a, b] h) p = if (p : ℕ) < a then 0 else 1 := by
  obtain ⟨⟨c, i⟩, rfl⟩ := (stdBlocks ![a, b] h).surjective p
  rw [blk_apply, stdBlocks_val]
  fin_cases c
  · simpa using i.2
  · simp

theorem longElt_conj_apply {R : Type} [CommRing R] (n : ℕ) (g : GL (Fin n) R) (i j : Fin n) :
    ((longElt n R * g * longElt n R : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j =
      (g : Matrix (Fin n) (Fin n) R) i.rev j.rev := by
  simp only [longElt, Units.val_mul, Matrix.mul_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_eq_single j.rev (fun x _ hx => by rw [if_neg (fun hh => hx (by rw [hh, Fin.rev_rev])), mul_zero]) (by simp)]
  simp

end GlobalTheory.ThetaRad

theorem GlobalTheory.ThetaRad.longElt_invT_conj_mem_unipRad : ∀ (R : Type) [CommRing R] (n a b : ℕ) (h : ∑ i, ![a, b] i = n) (h' : ∑ i, ![b, a] i = n) (u : GL (Fin n) R), u ∈ unipRad R (stdBlocks ![a, b] h) → longElt n R * GlobalTheory.CuspRep.invT n R u * longElt n R ∈ unipRad R (stdBlocks ![b, a] h') := by
  intro R _ n a b h h' u hu
  have hn : a + b = n := by simpa [Fin.sum_univ_two] using h
  have hv := GlobalTheory.ThetaRad.mem_unipRad_iff_entries.1 (inv_mem hu)
  refine GlobalTheory.ThetaRad.mem_unipRad_iff_entries.2 fun i j hij => ?_
  rw [GlobalTheory.ThetaRad.longElt_conj_apply]
  change ((u⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)ᵀ i.rev j.rev = _
  rw [Matrix.transpose_apply]
  rw [hv j.rev i.rev ?_]
  · simp [Matrix.one_apply, Fin.rev_inj, eq_comm]
  · rw [GlobalTheory.ThetaRad.blk_stdBlocks_two, GlobalTheory.ThetaRad.blk_stdBlocks_two] at *
    have hi := i.2; have hj := j.2
    simp only [Fin.val_rev] at *
    split_ifs at hij ⊢ <;> first | exact le_refl _ | decide | (exfalso; omega) | (exfalso; revert hij; decide)
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CornerUnip

theorem corner_symm_castSucc {m : ℕ} (i : Fin m) :
    (stdSum (rfl : m + 1 = m + 1)).symm (Fin.castSucc i) = Sum.inl i := by
  rw [Equiv.symm_apply_eq]; ext; simp [stdSum_inl]

theorem corner_symm_last (m : ℕ) :
    (stdSum (rfl : m + 1 = m + 1)).symm (Fin.last m) = Sum.inr 0 := by
  rw [Equiv.symm_apply_eq]; ext; simp [stdSum_inr]

variable {R : Type} [CommRing R] {m : ℕ}

theorem corner_cc (u : GL (Fin m) R) (i j : Fin m) :
    (corner u : Matrix (Fin (m+1)) (Fin (m+1)) R) (Fin.castSucc i) (Fin.castSucc j) = (u : Matrix _ _ R) i j := by
  have val_emb₂ (g : GL (Fin m) R × GL (Fin 1) R) :
      (emb₂ R (stdSum (rfl : m + 1 = m + 1)) g : Matrix (Fin (m+1)) (Fin (m+1)) R) =
        Matrix.reindex (stdSum (rfl : m + 1 = m + 1)) (stdSum (rfl : m + 1 = m + 1)) (Matrix.fromBlocks g.1.val 0 0 g.2.val) := by
    ext i j
    simp [emb₂, leviEmb, leviTwo, two, Matrix.reindex_apply, Matrix.blockDiagonal']
    rcases (stdSum (rfl : m + 1 = m + 1)).symm i with a | a <;>
      rcases (stdSum (rfl : m + 1 = m + 1)).symm j with b | b <;> simp
  rw [corner, val_emb₂]
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, corner_symm_castSucc]

theorem corner_cl (u : GL (Fin m) R) (i : Fin m) :
    (corner u : Matrix (Fin (m+1)) (Fin (m+1)) R) (Fin.castSucc i) (Fin.last m) = 0 := by
  have val_emb₂ (g : GL (Fin m) R × GL (Fin 1) R) :
      (emb₂ R (stdSum (rfl : m + 1 = m + 1)) g : Matrix (Fin (m+1)) (Fin (m+1)) R) =
        Matrix.reindex (stdSum (rfl : m + 1 = m + 1)) (stdSum (rfl : m + 1 = m + 1)) (Matrix.fromBlocks g.1.val 0 0 g.2.val) := by
    ext i j
    simp [emb₂, leviEmb, leviTwo, two, Matrix.reindex_apply, Matrix.blockDiagonal']
    rcases (stdSum (rfl : m + 1 = m + 1)).symm i with a | a <;>
      rcases (stdSum (rfl : m + 1 = m + 1)).symm j with b | b <;> simp
  rw [corner, val_emb₂]
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, corner_symm_castSucc, corner_symm_last]

theorem corner_lc (u : GL (Fin m) R) (j : Fin m) :
    (corner u : Matrix (Fin (m+1)) (Fin (m+1)) R) (Fin.last m) (Fin.castSucc j) = 0 := by
  have val_emb₂ (g : GL (Fin m) R × GL (Fin 1) R) :
      (emb₂ R (stdSum (rfl : m + 1 = m + 1)) g : Matrix (Fin (m+1)) (Fin (m+1)) R) =
        Matrix.reindex (stdSum (rfl : m + 1 = m + 1)) (stdSum (rfl : m + 1 = m + 1)) (Matrix.fromBlocks g.1.val 0 0 g.2.val) := by
    ext i j
    simp [emb₂, leviEmb, leviTwo, two, Matrix.reindex_apply, Matrix.blockDiagonal']
    rcases (stdSum (rfl : m + 1 = m + 1)).symm i with a | a <;>
      rcases (stdSum (rfl : m + 1 = m + 1)).symm j with b | b <;> simp
  rw [corner, val_emb₂]
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, corner_symm_castSucc, corner_symm_last]

theorem corner_ll (u : GL (Fin m) R) :
    (corner u : Matrix (Fin (m+1)) (Fin (m+1)) R) (Fin.last m) (Fin.last m) = 1 := by
  have val_emb₂ (g : GL (Fin m) R × GL (Fin 1) R) :
      (emb₂ R (stdSum (rfl : m + 1 = m + 1)) g : Matrix (Fin (m+1)) (Fin (m+1)) R) =
        Matrix.reindex (stdSum (rfl : m + 1 = m + 1)) (stdSum (rfl : m + 1 = m + 1)) (Matrix.fromBlocks g.1.val 0 0 g.2.val) := by
    ext i j
    simp [emb₂, leviEmb, leviTwo, two, Matrix.reindex_apply, Matrix.blockDiagonal']
    rcases (stdSum (rfl : m + 1 = m + 1)).symm i with a | a <;>
      rcases (stdSum (rfl : m + 1 = m + 1)).symm j with b | b <;> simp
  rw [corner, val_emb₂]
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, corner_symm_last]

end GlobalTheory.CornerUnip

open GlobalTheory.CornerUnip in
theorem GlobalTheory.CornerUnip.corner_unipB_superDiag : ∀ (R : Type) [CommRing R] (m : ℕ) (u : GL (Fin m) R), u ∈ unipB R (Fin m) → corner u ∈ unipB R (Fin (m + 1)) ∧ superDiag (corner u) = superDiag u := by
  intro R _ m u hu
  rw [mem_unipB] at hu
  obtain ⟨hl, hd⟩ := hu
  refine ⟨?_, ?_⟩
  · rw [mem_unipB]
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (lt_irrefl _)
        | cast j => exact corner_lc u j
      | cast i =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (not_lt.2 (Fin.le_last _))
        | cast j =>
          rw [corner_cc]
          exact hl i j (Fin.castSucc_lt_castSucc_iff.1 hij)
    · induction i using Fin.lastCases with
      | last => exact corner_ll u
      | cast i => rw [corner_cc]; exact hd i
  · unfold superDiag
    simp only [Finset.sum_filter]
    simp [Fin.sum_univ_castSucc, corner_cc, corner_cl, corner_lc, corner_ll]
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

theorem corner_diagT (R : Type) [CommRing R] (m : ℕ) (t : Fin m → Rˣ) :
    corner (diagT R (Fin m) t) = diagT R (Fin (m + 1)) (Fin.snoc t 1) := by
  apply Units.ext
  change (emb₂ R (stdSum (rfl : m + 1 = m + 1)) (diagT R (Fin m) t, 1) : Matrix (Fin (m + 1)) (Fin (m + 1)) R) = (diagT R (Fin (m + 1)) (Fin.snoc t 1) : Matrix (Fin (m + 1)) (Fin (m + 1)) R)
  rw [val_emb₂, val_diagT, val_diagT]
  ext i j
  obtain ⟨i, rfl⟩ := (stdSum (rfl : m + 1 = m + 1)).surjective i
  obtain ⟨j, rfl⟩ := (stdSum (rfl : m + 1 = m + 1)).surjective j
  have hl : ∀ a : Fin m, stdSum (rfl : m + 1 = m + 1) (Sum.inl a) = Fin.castSucc a := fun a => Fin.ext rfl
  have hr : ∀ a : Fin 1, stdSum (rfl : m + 1 = m + 1) (Sum.inr a) = Fin.last m := fun a => by
    apply Fin.ext; simp [stdSum, Subsingleton.elim a 0]
  simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j
  · rw [hl, hl, fromBlocks_apply₁₁]
    simp only [diagonal_apply, Fin.snoc_castSucc, Fin.castSucc_inj]
  · rw [hl, hr, fromBlocks_apply₁₂, diagonal_apply_ne _ (Fin.castSucc_lt_last i).ne, Matrix.zero_apply]
  · rw [hl, hr, fromBlocks_apply₂₁, diagonal_apply_ne _ (Fin.castSucc_lt_last j).ne', Matrix.zero_apply]
  · rw [hr, hr, fromBlocks_apply₂₂, diagonal_apply_eq, Fin.snoc_last, Subsingleton.elim i j]
    simp

end GlobalTheory.LocLanglands
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem longElt_invT_involution : ∀ (R : Type) [CommRing R] (n : ℕ) (g : GL (Fin n) R), longElt n R * GlobalTheory.CuspRep.invT n R (longElt n R * GlobalTheory.CuspRep.invT n R g * longElt n R) * longElt n R = g := by
  intro R _ n g
  have hw : longElt n R * longElt n R = 1 := Units.ext (antidiag_mul_self n R)
  have hii : ∀ h : GL (Fin n) R, GlobalTheory.CuspRep.invT n R (GlobalTheory.CuspRep.invT n R h) = h := fun h => by
    apply Units.ext
    show (h.valᵀ)ᵀ = h.val
    exact Matrix.transpose_transpose _
  have hwT : GlobalTheory.CuspRep.invT n R (longElt n R) = longElt n R := by
    apply Units.ext
    show (Matrix.of fun i j : Fin n => if j = i.rev then (1 : R) else 0)ᵀ = Matrix.of fun i j : Fin n => if j = i.rev then (1 : R) else 0
    ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    congr 1
    exact propext ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [h, Fin.rev_rev]⟩
  rw [map_mul, map_mul, hii, hwT, ← mul_assoc, ← mul_assoc, hw, one_mul, mul_assoc, hw, mul_one]

end GlobalTheory
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.TiedTheta

variable {l : ℕ} [Fact l.Prime]


open Classical in
def thetaExt (x : Per.BdR l) : ℂ_[l] :=
  if h : ∃ y : Per.BdRp l, algebraMap (Per.BdRp l) (Per.BdR l) y = x then Per.θD l h.choose else 0

theorem thetaExt_alg (y : Per.BdRp l) :
    thetaExt (algebraMap (Per.BdRp l) (Per.BdR l) y) = Per.θD l y := by
  have h : ∃ z : Per.BdRp l, algebraMap (Per.BdRp l) (Per.BdR l) z =
      algebraMap (Per.BdRp l) (Per.BdR l) y := ⟨y, rfl⟩
  rw [thetaExt, dite_eq_left h, (BdRField.bdR_isField l).2.1 h.choose_spec]

theorem exists_of_mem_FilD_zero {x : Per.BdR l} (hx : x ∈ Per.FilD l 0) :
    ∃ y : Per.BdRp l, x = algebraMap (Per.BdRp l) (Per.BdR l) y := by
  obtain ⟨e, he⟩ := FilLaws.exists_isEps l
  obtain ⟨y, hy⟩ := (mem_FilD_iff_xi_pow l e he 0 x).1 hx
  exact ⟨y, by simpa using hy⟩

theorem actC_eq {P : LocPrime l} (AI : LocAinf l P) (g : GQ l) (c : ℂ_[l]) :
    AI.actC g c = Per.σC g c := by
  have h1 : Continuous (AI.actC g) :=
    (AddMonoidHomClass.isometry_of_norm (AI.actC g) (AI.actC_norm g)).continuous
  have h2 : Continuous (Per.σC g) :=
    (AddMonoidHomClass.isometry_of_norm (Per.σC g) (GlobalTheory.RingBasics.norm_σC g)).continuous
  induction c using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq h1 h2
  | ih a => exact (AI.actC_ext g a).trans (GlobalTheory.RingBasics.σC_coe g a).symm

theorem norm_untilt_sub (x : Per.Fl l) (y : Per.OC l)
    (h : PreTilt.coeff 0 x = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : Per.OC l)}) y) :
    ‖((x.untilt : Per.OC l) : ℂ_[l]) - (y : ℂ_[l])‖ ≤ ‖(l : ℂ_[l])‖ := by
  rw [← PreTilt.mk_untilt_eq_coeff_zero, Ideal.Quotient.eq] at h
  have h1 := (GlobalTheory.RingBasics.mem_span_pow_OC 1 (x.untilt - y)).1 (by rwa [pow_one])
  rw [pow_one] at h1
  exact h1

theorem nonempty_thetaL : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    LocTied l P AI → Nonempty (Formalism.MainNotions.LocalSituation.ThetaL P AI) := by
  intro l _ P AI T
  have hex : ∀ x ∈ (P.PD (MainNotions.LocalSituation.botExt l)).Fil 0,
      ∃ y : Per.BdRp l, T.eD x = algebraMap (Per.BdRp l) (Per.BdR l) y :=
    fun x hx => exists_of_mem_FilD_zero ((T.fil _ _ _).1 hx)
  have hU := TiedUnif.tied_uniformiser l P AI T
  refine ⟨{
    θ := fun x => thetaExt (T.eD x)
    θ_one := ?_
    θ_add := fun x hx y hy => ?_
    θ_mul := fun x hx y hy => ?_
    θ_onto := fun c => ?_
    θ_ker := fun x hx => ?_
    θ_act := fun g x hx => ?_
    θ_Om := fun x => ?_
    θ_int := fun a => ?_
    θ_teich := fun x y h => ?_
    fil_succ_iff_mul_t := hU.2.2 _
    t_μ := hU.1 _ }⟩
  · rw [map_one, ← map_one (algebraMap (Per.BdRp l) (Per.BdR l)), thetaExt_alg, map_one]
  · obtain ⟨u, hu⟩ := hex x hx
    obtain ⟨v, hv⟩ := hex y hy
    rw [map_add (f := _), hu, hv, ← map_add (f := _), thetaExt_alg, thetaExt_alg, thetaExt_alg, map_add (f := _)]
  · obtain ⟨u, hu⟩ := hex x hx
    obtain ⟨v, hv⟩ := hex y hy
    rw [map_mul, hu, hv, ← map_mul, thetaExt_alg, thetaExt_alg, thetaExt_alg, map_mul]
  · obtain ⟨y, rfl⟩ := (thetaD_props l).1 c
    refine ⟨T.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) y), ?_, ?_⟩
    · rw [T.fil, RingEquiv.apply_symm_apply]
      exact TiedUnif.alg_mem_FilD_zero y
    · rw [RingEquiv.apply_symm_apply, thetaExt_alg]
  · obtain ⟨u, hu⟩ := hex x hx
    rw [T.fil, hu, thetaExt_alg, (thetaD_props l).2.1]
    exact ((filD_laws l).2.2.2.2.2.2 1 u).symm
  · obtain ⟨u, hu⟩ := hex x hx
    rw [T.actD, hu, (ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.1, thetaExt_alg, thetaExt_alg,
      (thetaD_props l).2.2.2.2, actC_eq]
  · obtain ⟨y, hy, hθ⟩ := T.om x
    rw [hy, thetaExt_alg, hθ]
  · rw [TiedUnif.eD_ιA T, thetaExt_alg, (thetaD_props l).2.2.2.1]
    exact (GlobalTheory.RingBasics.mem_OC _).1 (Per.θ l a).2
  · rw [TiedUnif.eD_ιA T, thetaExt_alg, (thetaD_props l).2.2.2.1,
      WittVector.fontaineTheta_teichmuller]
    exact norm_untilt_sub x y h

end GlobalTheory.MemLoc.TiedTheta
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.inertia_fixes_abelianPart_of_torsionPoint : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult →
    ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (O : ValuationSubring F) (φ : R →+* O),
    (∀ r, (φ r : F) = algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r)) →
    ∀ (k : ℕ), IsUnit (k : O) → ∀ (σ : F →ₐ[FractionRing R] F), (∀ x ∈ O, O.valuation (σ x - x) < 1) →
    ∀ p : QkPt D F k, spMap σ.toRingHom ≫ p.g.b.left = p.g.b.left := by
  first | exact @GlobalTheory.InertiaFix.sigma_fixes_abelianPart | exact GlobalTheory.InertiaFix.sigma_fixes_abelianPart | (intros; apply GlobalTheory.InertiaFix.sigma_fixes_abelianPart <;> assumption)
end
