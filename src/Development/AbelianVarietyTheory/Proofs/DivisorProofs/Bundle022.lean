module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Adjugate
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.IsTensorProduct

@[expose] public section

section

open MvPolynomial

namespace GlobalTheory

theorem coeff_allOnes_prod_one_add_mul {σ : Type} {L : ℕ} (m : Fin L → MvPolynomial σ ℂ)
    (a : MvPolynomial σ ℂ) :
    AddMonoidAlgebra.coeff (MvPolynomial.sumAlgEquiv ℂ (Fin L) σ ((∏ i, (1 + MvPolynomial.X (Sum.inl i) *
        MvPolynomial.rename Sum.inr (m i))) * MvPolynomial.rename Sum.inr a))
      (Finsupp.equivFunOnFinite.symm fun _ : Fin L => (1 : ℕ)) = (∏ i, m i) * a := by
  have hr : ∀ q : MvPolynomial σ ℂ, sumAlgEquiv ℂ (Fin L) σ (rename Sum.inr q) = C q := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C r => simp [sumAlgEquiv_C_inl]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p c hp => rw [map_mul, map_mul, hp, rename_X, sumAlgEquiv_X_inr, map_mul]
  have hx : ∀ i : Fin L, sumAlgEquiv ℂ (Fin L) σ (X (Sum.inl i)) = X i := fun i =>
    sumAlgEquiv_X_inl ℂ (Fin L) σ i
  have cmC : ∀ {τ : Type} (n : τ →₀ ℕ) (p : MvPolynomial τ (MvPolynomial σ ℂ)) (c : MvPolynomial σ ℂ),
      AddMonoidAlgebra.coeff (p * C c) n = AddMonoidAlgebra.coeff p n * c := by
    intro τ n p c; rw [mul_comm, coeff_C_mul, mul_comm]
  set e : Fin L →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ : Fin L => (1 : ℕ) with he
  have hmono : ∀ t : Finset (Fin L),
      AddMonoidAlgebra.coeff (∏ i ∈ t, (X i * C (m i) : MvPolynomial (Fin L) (MvPolynomial σ ℂ))) e =
        if t = Finset.univ then ∏ i, m i else 0 := by
    intro t
    rw [Finset.prod_mul_distrib, ← map_prod, cmC]
    have hX : (∏ i ∈ t, (X i : MvPolynomial (Fin L) (MvPolynomial σ ℂ))) =
        monomial (∑ i ∈ t, Finsupp.single i 1) 1 := by
      rw [monomial_sum_one]; rfl
    rw [hX, coeff_monomial]
    by_cases ht : t = Finset.univ
    · subst ht
      have : (∑ i ∈ (Finset.univ : Finset (Fin L)), Finsupp.single i 1) = e := by
        ext j; simp [he, Finsupp.finsetSum_apply, Finsupp.single_apply]
      simp [this]
    · obtain ⟨j, hj⟩ : ∃ j, j ∉ t := by
        by_contra h; push_neg at h; exact ht (Finset.eq_univ_iff_forall.mpr h)
      have : (∑ i ∈ t, Finsupp.single i 1) ≠ e := by
        intro h
        have := congrArg (fun f => f j) h
        simp [he, Finsupp.finsetSum_apply, Finsupp.single_apply, hj] at this
      simp [this, ht]
  rw [map_mul, hr, cmC, map_prod]
  simp_rw [map_add (f := _), map_one, map_mul, hr, hx]
  rw [Finset.prod_one_add, coeff_sum, Finset.sum_eq_single Finset.univ]
  · rw [hmono]; simp
  · intro t _ ht; rw [hmono, if_neg ht]
  · intro h; exact absurd (Finset.mem_powerset.mpr (Finset.Subset.refl _)) h

end GlobalTheory
end

section

open MvPolynomial

namespace GlobalTheory

theorem pencil_optionEquivLeft_rename_some {τ : Type} (a : MvPolynomial τ ℂ) :
    MvPolynomial.optionEquivLeft ℂ τ (MvPolynomial.rename some a) = Polynomial.C a := by
  induction a using MvPolynomial.induction_on with
  | C r => simp [MvPolynomial.optionEquivLeft_C]
  | add p q hp hq => simp [map_add (f := _), hp, hq]
  | mul_X p x hp => simp [map_mul, hp, MvPolynomial.optionEquivLeft_X_some]

theorem pencil_natDegree_det_le_rowSum {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (Polynomial R)) (d : ι → ℕ) (h : ∀ i j, (M i j).natDegree ≤ d i) :
    M.det.natDegree ≤ ∑ i, d i := by
  rw [Matrix.det_apply]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro g _
  calc (Equiv.Perm.sign g • ∏ i, M (g i) i).natDegree ≤ (∏ i, M (g i) i).natDegree := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign g) with sg | sg
        · rw [sg, one_smul]
        · rw [sg, Units.neg_smul, one_smul, Polynomial.natDegree_neg]
    _ ≤ ∑ i, (M (g i) i).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ i, d (g i) := Finset.sum_le_sum fun i _ => h _ _
    _ = ∑ i, d i := Equiv.sum_comp g d

theorem pencil_map_entry {τ : Type} (a b : MvPolynomial τ ℂ) :
    MvPolynomial.optionEquivLeft ℂ τ
      (MvPolynomial.X none * MvPolynomial.rename some a + MvPolynomial.rename some b) =
      Polynomial.X * Polynomial.C a + Polynomial.C b := by
  simp [map_add (f := _), map_mul, MvPolynomial.optionEquivLeft_X_none, pencil_optionEquivLeft_rename_some]

theorem pencil_det_adjugate_coeff :
    ∀ {τ : Type} {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι (MvPolynomial τ ℂ)),
      let Z : Matrix ι ι (MvPolynomial (Option τ) ℂ) := fun i j =>
        MvPolynomial.X none * MvPolynomial.rename some (A i j) + MvPolynomial.rename some (B i j);
      (∀ k, Fintype.card ι < k → (MvPolynomial.optionEquivLeft ℂ τ (Z.det)).coeff k = 0) ∧
      (MvPolynomial.optionEquivLeft ℂ τ (Z.det)).coeff (Fintype.card ι) = A.det ∧
      ∀ k i j, Fintype.card ι ≤ k →
        (MvPolynomial.optionEquivLeft ℂ τ (Z.adjugate j i)).coeff k = 0 := by
  intro τ ι _ _ A B Z
  set e : MvPolynomial (Option τ) ℂ →+* Polynomial (MvPolynomial τ ℂ) :=
    (MvPolynomial.optionEquivLeft ℂ τ).toRingEquiv.toRingHom with he
  have hZ : e.mapMatrix Z = (Polynomial.X : Polynomial (MvPolynomial τ ℂ)) • A.map Polynomial.C +
      B.map Polynomial.C := by
    refine Matrix.ext fun i j => ?_
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Z, he]
    exact pencil_map_entry (A i j) (B i j)
  have hdet : MvPolynomial.optionEquivLeft ℂ τ Z.det =
      ((Polynomial.X : Polynomial (MvPolynomial τ ℂ)) • A.map Polynomial.C + B.map Polynomial.C).det := by
    rw [← hZ, ← RingHom.map_det]; rfl
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    rw [hdet]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      ((Polynomial.natDegree_det_X_add_C_le A B).trans_lt hk)
  · rw [hdet, Polynomial.coeff_det_X_add_C_card]
  · intro k i j hk
    have hadj : MvPolynomial.optionEquivLeft ℂ τ (Z.adjugate j i) =
        (((Polynomial.X : Polynomial (MvPolynomial τ ℂ)) • A.map Polynomial.C +
          B.map Polynomial.C).updateRow i (Pi.single j 1)).det := by
      have := congrFun (congrFun (RingHom.map_adjugate e Z) j) i
      rw [RingHom.mapMatrix_apply, Matrix.map_apply] at this
      change e (Z.adjugate j i) = _
      rw [this, hZ, Matrix.adjugate_apply]
    rw [hadj]
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hcard : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
    refine lt_of_le_of_lt (pencil_natDegree_det_le_rowSum _ (fun r => if r = i then 0 else 1) ?_) ?_
    · intro r c
      by_cases hr : r = i
      · subst hr
        simp only [Matrix.updateRow_self, if_true]
        by_cases hc : c = j
        · subst hc; simp
        · simp [Pi.single_apply, hc]
      · simp only [Matrix.updateRow_ne hr, if_neg hr, Matrix.add_apply, Matrix.smul_apply,
          Matrix.map_apply, smul_eq_mul]
        compute_degree
    · have : (∑ r, if r = i then 0 else 1 : ℕ) = Fintype.card ι - 1 := by
        rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul, mul_one,
          Finset.filter_ne' , Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
      omega

end GlobalTheory
end

section

open scoped TensorProduct

namespace GlobalTheory

theorem ker_aeval_truncated : ∀ (n : ℕ), 0 < n → ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra B A] (d : ℕ) (x : Fin d → A) (b : Fin d → B), (∀ i, x i ^ n = algebraMap B A (b i)) → LinearIndependent B (fun a : Fin d → Fin n => ∏ i, x i ^ (a i : ℕ)) → RingHom.ker (MvPolynomial.aeval x : MvPolynomial (Fin d) B →ₐ[B] A) = Ideal.span (Set.range fun i : Fin d => (MvPolynomial.X i ^ n - MvPolynomial.C (b i) : MvPolynomial (Fin d) B)) := by
  intro n hn B A _ _ _ d x b hx hli
  set J : Ideal (MvPolynomial (Fin d) B) := Ideal.span (Set.range fun i : Fin d =>
    (MvPolynomial.X i ^ n - MvPolynomial.C (b i) : MvPolynomial (Fin d) B)) with hJ
  have hJker : J ≤ RingHom.ker (MvPolynomial.aeval x : MvPolynomial (Fin d) B →ₐ[B] A) := by
    rw [hJ, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp [RingHom.mem_ker, hx]
  refine le_antisymm ?_ hJker
  let q : MvPolynomial (Fin d) B →ₐ[B] (MvPolynomial (Fin d) B ⧸ J) := Ideal.Quotient.mkₐ B J
  have hq : ∀ F G, q F = q G ↔ F - G ∈ J := fun F G => by
    simp only [q, Ideal.Quotient.mkₐ_eq_mk]; exact Ideal.Quotient.eq
  let y : Fin d → (MvPolynomial (Fin d) B ⧸ J) := fun i => q (MvPolynomial.X i)
  let v : (Fin d → Fin n) → (MvPolynomial (Fin d) B ⧸ J) := fun a => ∏ i, y i ^ (a i : ℕ)
  have hqv : ∀ a, q (∏ i, MvPolynomial.X i ^ (a i : ℕ)) = v a := fun a => by
    simp [v, y, map_prod, map_pow]
  have hyn : ∀ i, y i ^ n = algebraMap B _ (b i) := by
    intro i
    have h1 : q (MvPolynomial.X i ^ n) = q (MvPolynomial.C (b i)) :=
      (hq _ _).mpr (Ideal.subset_span ⟨i, rfl⟩)
    simp only [y]
    rw [← map_pow, h1, ← MvPolynomial.algebraMap_eq, q.commutes]
  have hsplit : ∀ (a : Fin d → Fin n) (i : Fin d) (k : Fin n),
      v (Function.update a i k) = y i ^ (k : ℕ) * ∏ j ∈ Finset.univ.erase i, y j ^ (a j : ℕ) := by
    intro a i k
    simp only [v]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    congr 1
    · simp
    · exact Finset.prod_congr rfl fun j hj => by simp [Finset.ne_of_mem_erase hj]
  have hsplit0 : ∀ (a : Fin d → Fin n) (i : Fin d),
      v a = y i ^ (a i : ℕ) * ∏ j ∈ Finset.univ.erase i, y j ^ (a j : ℕ) := by
    intro a i
    have := hsplit a i (a i)
    rwa [Function.update_eq_self] at this
  let S := Submodule.span B (Set.range v)
  have hgen : ∀ (a : Fin d → Fin n) (i : Fin d), v a * y i ∈ S := by
    intro a i
    by_cases h : (a i : ℕ) + 1 < n
    · have : v a * y i = v (Function.update a i ⟨a i + 1, h⟩) := by
        rw [hsplit, hsplit0 a i, pow_succ]; ring
      rw [this]; exact Submodule.subset_span ⟨_, rfl⟩
    · have h' : (a i : ℕ) + 1 = n := by have := (a i).isLt; omega
      have : v a * y i = b i • v (Function.update a i ⟨0, hn⟩) := by
        have hp : y i ^ n = y i ^ ((a i : ℕ) + 1) := by rw [h']
        rw [hsplit, hsplit0 a i, Algebra.smul_def, ← hyn, hp, pow_succ]; simp; ring
      rw [this]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  have hmulX : ∀ i, ∀ s ∈ S, s * y i ∈ S := by
    intro i s hs
    induction hs using Submodule.span_induction with
    | mem s hs => obtain ⟨a, rfl⟩ := hs; exact hgen a i
    | zero => simp
    | add s t _ _ hs ht => rw [add_mul]; exact add_mem hs ht
    | smul c s _ hs => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hs
  have hall : ∀ F, q F ∈ S := by
    intro F
    induction F using MvPolynomial.induction_on with
    | C c =>
      have : q (MvPolynomial.C c) = c • v (fun _ => ⟨0, hn⟩) := by
        rw [← MvPolynomial.algebraMap_eq, q.commutes, Algebra.algebraMap_eq_smul_one]
        simp [v]
      rw [this]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    | add p r hp hr => rw [map_add]; exact add_mem hp hr
    | mul_X p i hp => rw [map_mul]; exact hmulX i _ hp
  intro F hF
  rw [RingHom.mem_ker] at hF
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun B).mp (hall F)
  set G : MvPolynomial (Fin d) B := ∑ a, c a • ∏ i, MvPolynomial.X i ^ (a i : ℕ) with hG
  have hqG : q G = q F := by

    rw [← hc, hG, map_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [map_smul, hqv]
  have hFG : F - G ∈ J := (hq F G).mp hqG.symm
  have hevG : MvPolynomial.aeval x G = 0 := by
    have h0 := hJker hFG
    rw [RingHom.mem_ker, map_sub, hF] at h0
    simpa using h0
  have hsum : ∑ a, c a • ∏ i, x i ^ (a i : ℕ) = 0 := by

    rw [← hevG, hG, map_sum]
    exact Finset.sum_congr rfl fun a _ => by simp [map_prod, map_pow]
  have hc0 := Fintype.linearIndependent_iff.mp hli c hsum
  have hG0 : G = 0 := by rw [hG]; simp [hc0]
  simpa [hG0] using hFG

end GlobalTheory
end

section

open MvPolynomial

namespace GlobalTheory
namespace GaussContentLinearForms

variable {V : Type} [CommRing V] {σ : Type}

theorem span_coeff_C_mul (a : V) (f : MvPolynomial σ V) :
    Ideal.span (Set.range fun s => (C a * f).coeff s) =
      Ideal.span {a} * Ideal.span (Set.range fun s => f.coeff s) := by
  rw [Ideal.span_mul_span]
  congr 1
  ext x
  simp only [coeff_C_mul, Set.mem_range, Set.mem_mul, Set.mem_singleton_iff]
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨a, rfl, _, ⟨s, rfl⟩, rfl⟩
  · rintro ⟨b, rfl, y, ⟨s, rfl⟩, rfl⟩
    exact ⟨s, rfl⟩

theorem span_coeff_eq_top_iff [IsLocalRing V] (f : MvPolynomial σ V) :
    Ideal.span (Set.range fun s => f.coeff s) = ⊤ ↔
      MvPolynomial.map (IsLocalRing.residue V) f ≠ 0 := by
  have h1 : MvPolynomial.map (IsLocalRing.residue V) f = 0 ↔
      Ideal.span (Set.range fun s => f.coeff s) ≤ IsLocalRing.maximalIdeal V := by
    rw [Ideal.span_le, Set.range_subset_iff, MvPolynomial.ext_iff]
    refine forall_congr' fun s => ?_
    rw [coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply,
      IsLocalRing.residue_eq_zero_iff]
    rfl
  rw [ne_eq, h1]
  constructor
  · intro h h'
    rw [h, top_le_iff] at h'
    exact (IsLocalRing.maximalIdeal.isMaximal V).ne_top h'
  · intro h
    by_contra h'
    exact h (IsLocalRing.le_maximalIdeal h')

theorem span_coeff_one :
    Ideal.span (Set.range fun s => (1 : MvPolynomial σ V).coeff s) = ⊤ := by
  classical
  rw [Ideal.eq_top_iff_one]
  exact Ideal.subset_span ⟨0, by simp⟩

theorem exists_primitive_part [IsDomain V] [IsDiscreteValuationRing V] (f : MvPolynomial σ V) :
    ∃ (a : V) (g : MvPolynomial σ V), f = C a * g ∧
      Ideal.span (Set.range fun s => g.coeff s) = ⊤ := by
  obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal
    (Ideal.span (Set.range fun s => f.coeff s))).principal
  have ha' : Ideal.span (Set.range fun s => f.coeff s) = Ideal.span {a} := ha
  have hd : C a ∣ f := by
    rw [C_dvd_iff_dvd_coeff]
    intro s
    rw [← Ideal.mem_span_singleton, ← ha']
    exact Ideal.subset_span ⟨s, rfl⟩
  obtain ⟨g, rfl⟩ := hd
  by_cases h0 : a = 0
  · exact ⟨0, 1, by simp [h0], span_coeff_one⟩
  · refine ⟨a, g, rfl, ?_⟩
    rw [span_coeff_C_mul] at ha'
    have hne : Ideal.span {a} ≠ (0 : Ideal V) := by
      rw [Ideal.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]
      exact h0
    apply mul_left_cancel₀ hne
    rw [ha', Ideal.mul_top]

theorem span_coeff_mul [IsDomain V] [IsDiscreteValuationRing V] (f g : MvPolynomial σ V) :
    Ideal.span (Set.range fun s => (f * g).coeff s) =
      Ideal.span (Set.range fun s => f.coeff s) * Ideal.span (Set.range fun s => g.coeff s) := by
  obtain ⟨a, f', rfl, hf⟩ := exists_primitive_part f
  obtain ⟨b, g', rfl, hg⟩ := exists_primitive_part g
  have hfg : Ideal.span (Set.range fun s => (f' * g').coeff s) = ⊤ := by
    rw [span_coeff_eq_top_iff] at hf hg ⊢
    rw [map_mul]
    exact mul_ne_zero hf hg
  have e : C a * f' * (C b * g') = C (a * b) * (f' * g') := by
    rw [map_mul]; ring
  rw [e, span_coeff_C_mul, span_coeff_C_mul, span_coeff_C_mul, hf, hg, hfg, Ideal.mul_top,
    Ideal.mul_top, Ideal.mul_top, Ideal.span_singleton_mul_span_singleton]

theorem span_coeff_prod [IsDomain V] [IsDiscreteValuationRing V] {ι : Type} (t : Finset ι)
    (f : ι → MvPolynomial σ V) :
    Ideal.span (Set.range fun s => (∏ j ∈ t, f j).coeff s) =
      ∏ j ∈ t, Ideal.span (Set.range fun s => (f j).coeff s) := by
  classical
  induction t using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, span_coeff_one, Ideal.one_eq_top]
  | insert j t hj ih => rw [Finset.prod_insert hj, Finset.prod_insert hj, span_coeff_mul, ih]

theorem span_coeff_linear {m : ℕ} (c : Fin m → V) :
    Ideal.span (Set.range fun s => (∑ i, C (c i) * X i : MvPolynomial (Fin m) V).coeff s) =
      Ideal.span (Set.range c) := by
  classical
  apply le_antisymm
  · rw [Ideal.span_le, Set.range_subset_iff]
    intro s
    simp only [coeff_sum, coeff_C_mul, SetLike.mem_coe]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · apply Ideal.span_mono
    rintro _ ⟨i, rfl⟩
    refine ⟨Finsupp.single i 1, ?_⟩
    simp only [coeff_sum, coeff_C_mul, coeff_X]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [ite_eq_right, mul_zero]
      intro h
      exact hj (Finsupp.single_left_injective one_ne_zero h)
    · simp

theorem span_coeff_prod_linear (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (d m : ℕ) (c : Fin d → Fin m → V) :
    Ideal.span (Set.range fun s =>
        (∏ j, ∑ i, C (c j i) * X i : MvPolynomial (Fin m) V).coeff s) =
      ∏ j, Ideal.span (Set.range (c j)) := by
  rw [span_coeff_prod]
  exact Finset.prod_congr rfl fun j _ => span_coeff_linear (c j)

end GaussContentLinearForms
end GlobalTheory
end

section

open IsLocalRing TensorProduct

namespace GlobalTheory

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem mvPolynomial_tensor_baseChange_ringEquiv :
    ∀ (S B K τ : Type) [CommRing S] [CommRing B] [CommRing K] [Algebra S B] [Algebra S K]
      [Algebra (MvPolynomial τ S) K] [IsScalarTower S (MvPolynomial τ S) K],
      Nonempty (MvPolynomial τ B ⊗[MvPolynomial τ S] K ≃+* B ⊗[S] K) := by
  intro S B K τ _ _ _ _ _ _ _
  let e : MvPolynomial τ S ⊗[S] B ≃ₐ[MvPolynomial τ S] MvPolynomial τ B :=
    Algebra.IsPushout.equiv S (MvPolynomial τ S) B (MvPolynomial τ B)
  exact ⟨(Algebra.TensorProduct.comm (MvPolynomial τ S) (MvPolynomial τ B) K).toRingEquiv.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[MvPolynomial τ S] K) e.symm).toRingEquiv.trans
      ((Algebra.TensorProduct.cancelBaseChange S (MvPolynomial τ S) (MvPolynomial τ S) K B).toRingEquiv.trans
        (Algebra.TensorProduct.comm S K B).toRingEquiv))⟩

end GlobalTheory
end

section

open MvPolynomial

namespace GlobalTheory

theorem optionEquivLeft_pderiv_none_gen {τ : Type} [DecidableEq τ]
    (p : MvPolynomial (Option τ) ℂ) :
    optionEquivLeft ℂ τ (pderiv none p) = Polynomial.derivative (optionEquivLeft ℂ τ p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [optionEquivLeft_C]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rcases i with _ | j
    · simp [Derivation.leibniz, hp, optionEquivLeft_X_none, mul_comm]
    · simp [Derivation.leibniz, hp, optionEquivLeft_X_some, pderiv_X, mul_comm]

theorem optionEquivLeft_pderiv_none_coeff :
    ∀ {τ : Type} [DecidableEq τ] (k : ℕ) (s : MvPolynomial (Option τ) ℂ),
      (MvPolynomial.optionEquivLeft ℂ τ (MvPolynomial.pderiv none s)).coeff k =
        ((k : ℂ) + 1) • (MvPolynomial.optionEquivLeft ℂ τ (s)).coeff (k + 1) := by
  intro τ _ k s
  rw [optionEquivLeft_pderiv_none_gen, Polynomial.coeff_derivative, MvPolynomial.smul_eq_C_mul,
    mul_comm]
  congr 1
  simp

end GlobalTheory
end
