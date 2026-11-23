module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle296
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalB
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle138
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolarCoordinatesUnitaryPQDoubleCover
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply

@[expose] public section

section

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open Formalism.REAL (fockF)
open scoped DirectSum TensorProduct Kronecker Matrix

namespace GlobalTheory.GLDuality

theorem rename_swap_matRep_one_right {n n' : ℕ} (g : GL (Fin n) ℂ) (v : MvPolynomial (Fin n' × Fin n) ℂ) :
    rename Prod.swap (matRep n n' (g, 1) v) =
      rowAct ℂ (g : Matrix (Fin n) (Fin n) ℂ)ᵀ (rename Prod.swap v) := by
  have : (rename (R := ℂ) (Prod.swap : Fin n' × Fin n → Fin n × Fin n')).comp
      (sub (((1 : GL (Fin n') ℂ) : Matrix (Fin n') (Fin n') ℂ) ⊗ₖ (g : Matrix (Fin n) (Fin n) ℂ))ᵀ) =
      (rowAct ℂ (g : Matrix (Fin n) (Fin n) ℂ)ᵀ).comp (rename Prod.swap) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    simp [sub, rowAct, Fintype.sum_prod_type, Matrix.one_apply, apply_ite C]
  rw [matRep_apply]
  exact DFunLike.congr_fun this v

theorem rename_swap_colAdd {n n' : ℕ} (l j : Fin n) (c : ℂ) (v : MvPolynomial (Fin n' × Fin n) ℂ) :
    rename Prod.swap (colAdd ℂ l j c v) =
      Polynomial.eval (C c) (rowGen ℂ l j (rename Prod.swap v)) := by
  induction v using MvPolynomial.induction_on with
  | C a => simp [colAdd, rowGen]
  | add p q hp hq => simp only [map_add (f := _), hp, hq, Polynomial.eval_add]
  | mul_X p v hp =>
    obtain ⟨a, s⟩ := v
    simp only [map_mul, hp, Polynomial.eval_mul]
    congr 1
    by_cases h : s = j <;> simp [colAdd, rowGen, h, mul_comm (C c)]

theorem rowGen_coeff_zero_eq {r n : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) ℂ) :
    (rowGen ℂ a b f).coeff 0 = f := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  induction f using MvPolynomial.induction_on with
  | C a => simp [rowGen]
  | add p q hp hq => simp only [map_add (f := _), hp, hq, Polynomial.eval_add]
  | mul_X p v hp =>
    simp only [map_mul, hp, Polynomial.eval_mul]
    congr 1
    by_cases h : v.1 = b <;> simp [rowGen, h]

theorem exists_colAdd_fixed_of_stable (n n' : ℕ) (N : Submodule ℂ (MvPolynomial (Fin n' × Fin n) ℂ)) (hN : N ≠ ⊥)
    (hst : ∀ g : GL (Fin n) ℂ, ∀ v ∈ N, matRep n n' (g, 1) v ∈ N) :
    ∃ v ∈ N, v ≠ 0 ∧ ∀ l j : Fin n, l < j → ∀ c : ℂ, colAdd ℂ l j c v = v := by
  have hinj : Function.Injective
      (rename (R := ℂ) (Prod.swap : Fin n' × Fin n → Fin n × Fin n')) :=
    rename_injective _ Prod.swap_injective
  let M : Submodule ℂ (MvPolynomial (Fin n × Fin n') ℂ) :=
    N.map (rename (R := ℂ) (Prod.swap : Fin n' × Fin n → Fin n × Fin n')).toLinearMap
  have hU : ∀ u ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ f ∈ M, rowAct ℂ u f ∈ M := by
    rintro u hu _ ⟨f, hf, rfl⟩
    let t : Matrix.unitaryGroup (Fin n) ℂ := Matrix.UnitaryGroup.transpose ⟨u, hu⟩
    exact ⟨_, hst (unitaryIncl n t) f hf, rename_swap_matRep_one_right (unitaryIncl n t) f⟩
  have hcl := rowDivClosed_of_rowAct_stable M (rowAct_mem_of_unitary_stable M hU)
  have hne : M ≠ ⊥ := fun e => hN (Submodule.map_injective_of_injective hinj
    (e.trans (Submodule.map_bot _).symm))
  obtain ⟨_, ⟨v, hv, rfl⟩, hv0, hkill⟩ := exists_killed_of_rowDivClosed M hcl hne
  refine ⟨v, hv, fun e => hv0 (by rw [e, map_zero]), fun l j hlj c => hinj ?_⟩
  have hC : rowGen ℂ l j (rename Prod.swap v) = Polynomial.C (rename Prod.swap v) := by
    apply Polynomial.ext
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [rowGen_coeff_zero_eq, Polynomial.coeff_C_zero]
    · rw [Polynomial.coeff_C_of_ne_zero hk.ne']
      exact hkill l j hlj k hk
  rw [rename_swap_colAdd, hC, Polynomial.eval_C]

end GlobalTheory.GLDuality
end

section

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open Formalism.REAL (fockF)
open scoped DirectSum TensorProduct Kronecker Matrix

namespace GlobalTheory.GLDuality.HighestLine

theorem weight_mapDomain {r m n : ℕ} (h : m ≤ n) (u : Fin r × Fin m →₀ ℕ) (i : Fin m) :
    Finsupp.weight (colW r n) (Finsupp.mapDomain (Prod.map id (Fin.castLE h)) u) (Fin.castLE h i) =
      Finsupp.weight (colW r m) u i := by
  classical
  simp only [Finsupp.weight_apply]
  rw [Finsupp.sum_mapDomain_index (h := fun (x : Fin r × Fin n) (c : ℕ) => c • colW r n x)
    (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  rw [Finsupp.sum, Finsupp.sum, Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [colW, Pi.single_apply, Fin.castLE_inj]

theorem le_weight {r n : ℕ} (u : Fin r × Fin n →₀ ℕ) (x : Fin r × Fin n) :
    u x ≤ Finsupp.weight (colW r n) u x.2 := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
  by_cases hx : u x = 0
  · rw [hx]; exact Nat.zero_le _
  · refine le_trans ?_ (Finset.single_le_sum (f := fun y => (u y • colW r n y) x.2)
      (fun y _ => Nat.zero_le _) (Finsupp.mem_support_iff.mpr hx))
    simp [colW]

theorem colAdd_rename {r m n : ℕ} (h : m ≤ n) (l j : Fin m) (c : ℂ) (f : MvPolynomial (Fin r × Fin m) ℂ) :
    colAdd ℂ (Fin.castLE h l) (Fin.castLE h j) c (rename (Prod.map id (Fin.castLE h)) f) =
      rename (Prod.map id (Fin.castLE h)) (colAdd ℂ l j c f) := by
  have key : (colAdd ℂ (Fin.castLE h l) (Fin.castLE h j) c).comp (rename (Prod.map id (Fin.castLE h))) =
      (rename (Prod.map id (Fin.castLE h))).comp (colAdd ℂ (r := r) l j c) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    simp only [AlgHom.comp_apply, rename_X, colAdd, aeval_X, Prod.map_apply, id_eq, Fin.castLE_inj]
    split_ifs <;> simp [rename_X]
  exact DFunLike.congr_fun key f

theorem rowDiv_rename {r m n : ℕ} (h : m ≤ n) (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin m) ℂ) :
    rowDiv ℂ a b k (rename (Prod.map id (Fin.castLE h)) f) =
      rename (Prod.map id (Fin.castLE h)) (rowDiv ℂ a b k f) := by
  have key : (rowGen ℂ (n := n) a b).comp (rename (Prod.map id (Fin.castLE h))) =
      (Polynomial.mapAlgHom (rename (Prod.map id (Fin.castLE h)))).comp (rowGen ℂ (n := m) a b) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨x, s⟩
    simp only [AlgHom.comp_apply, rename_X, rowGen, aeval_X, Prod.map_apply, id_eq]
    split_ifs <;> simp [rename_X, Polynomial.coe_mapAlgHom]
  have hf := DFunLike.congr_fun key f
  simp only [AlgHom.comp_apply] at hf
  simp only [rowDiv]
  rw [hf]
  simp [Polynomial.coe_mapAlgHom, Polynomial.coeff_map]

theorem wide {r n : ℕ} (h : r ≤ n) (ν : Fin n → ℕ) (hν : Antitone ν) (h0 : ∀ s : Fin n, r ≤ s.val → ν s = 0)
    (f : MvPolynomial (Fin r × Fin n) ℂ) (hf : f ∈ dualWeyl ℂ r n ν)
    (hk : ∀ a b : Fin r, a < b → ∀ k : ℕ, 1 ≤ k → rowDiv ℂ a b k f = 0) :
    ∃ c : ℂ, f = c • rename (Prod.map id (Fin.castLE h)) (hw ℂ le_rfl fun i => ν (Fin.castLE h i)) := by
  classical
  have hφi : Function.Injective (Prod.map id (Fin.castLE h) : Fin r × Fin r → Fin r × Fin n) :=
    Function.Injective.prodMap Function.injective_id (Fin.castLE_injective h)
  have hpt := (dualWeylPoint ℂ r n ν f).1 hf
  have hvars : (f.vars : Set (Fin r × Fin n)) ⊆
      Set.range (Prod.map id (Fin.castLE h) : Fin r × Fin r → Fin r × Fin n) := by
    intro x hx
    rw [Finset.mem_coe, MvPolynomial.mem_vars_iff_mem_support] at hx
    obtain ⟨u, hu, hxu⟩ := hx
    have hwu : Finsupp.weight (colW r n) u = ν := hpt.1 (MvPolynomial.mem_support_iff.mp hu)
    have hx2 : x.2.val < r := by
      by_contra hlt
      have h1 := le_weight u x
      rw [hwu, h0 x.2 (not_lt.mp hlt)] at h1
      exact (Finsupp.mem_support_iff.mp hxu) (Nat.le_zero.mp h1)
    exact ⟨(x.1, ⟨x.2.val, hx2⟩), Prod.ext rfl (Fin.ext rfl)⟩
  obtain ⟨g, rfl⟩ := exists_rename_eq_of_vars_subset_range f _ hφi hvars
  have hgw : IsWeightedHomogeneous (colW r r) g (fun i => ν (Fin.castLE h i)) := by
    intro u hu
    have hu' : AddMonoidAlgebra.coeff (rename (Prod.map id (Fin.castLE h)) g)
        (Finsupp.mapDomain (Prod.map id (Fin.castLE h)) u) ≠ 0 := by
      rwa [coeff_rename_mapDomain _ hφi]
    have hwu := hpt.1 hu'
    funext i
    rw [← weight_mapDomain h u i, hwu]
  have hgc : ∀ l j : Fin r, l < j → ∀ c : ℂ, colAdd ℂ l j c g = g := by
    intro l j hlj c
    apply rename_injective _ hφi
    rw [← colAdd_rename h]
    exact hpt.2 _ _ (show Fin.castLE h l < Fin.castLE h j from hlj) c
  have hg : g ∈ dualWeyl ℂ r r (fun i => ν (Fin.castLE h i)) :=
    (dualWeylPoint ℂ r r _ g).2 ⟨hgw, hgc⟩
  have hgk : ∀ a b : Fin r, a < b → ∀ k : ℕ, 1 ≤ k → rowDiv ℂ a b k g = 0 := by
    intro a b hab k hk1
    apply rename_injective _ hφi
    rw [← rowDiv_rename h, map_zero]
    exact hk a b hab k hk1
  have hant : Antitone (fun i : Fin r => ν (Fin.castLE h i)) := fun i j hij =>
    hν (show Fin.castLE h i ≤ Fin.castLE h j from hij)
  obtain ⟨c, hc⟩ := hwLine ℂ r r le_rfl _ hant g hg hgk
  exact ⟨c, by rw [hc, map_smul]⟩

theorem highest_line : ∀ (r n : ℕ) (ν : Fin n → ℕ) (v : MvPolynomial (Fin r × Fin n) ℂ), v ∈ dualWeyl ℂ r n ν → (∀ a b : Fin r, a < b → ∀ k : ℕ, 1 ≤ k → rowDiv ℂ a b k v = 0) → v ≠ 0 → (∃ a : Part (min n r), ν = rowNu (r := n) a.1) ∧ ∀ w ∈ dualWeyl ℂ r n ν, (∀ a b : Fin r, a < b → ∀ k : ℕ, 1 ≤ k → rowDiv ℂ a b k w = 0) → ∃ c : ℂ, w = c • v := by
  intro r n ν v hv hkv hv0
  have hant : Antitone ν := by
    intro i j hij
    by_contra hlt
    push Not at hlt
    have hij' : i < j := lt_of_le_of_ne hij (by rintro rfl; exact lt_irrefl _ hlt)
    have hbot := dualWeylNonDom ℂ r n ν ⟨i, j, hij', hlt⟩
    rw [hbot] at hv
    exact hv0 ((Submodule.mem_bot ℂ).mp hv)
  have h0 : ∀ s : Fin n, r ≤ s.val → ν s = 0 := by
    intro s hs
    by_contra hne
    exact hv0 (hwLineTall ℂ r n ν ⟨s, hs, Nat.pos_of_ne_zero hne⟩ v hv hkv)
  have hline : ∃ H : MvPolynomial (Fin r × Fin n) ℂ, ∀ w ∈ dualWeyl ℂ r n ν,
      (∀ a b : Fin r, a < b → ∀ k : ℕ, 1 ≤ k → rowDiv ℂ a b k w = 0) → ∃ c : ℂ, w = c • H := by
    rcases le_total n r with hnr | hrn
    · exact ⟨hw ℂ hnr ν, fun w hw' hk => hwLine ℂ r n hnr ν hant w hw' hk⟩
    · exact ⟨_, fun w hw' hk => wide hrn ν hant h0 w hw' hk⟩
  obtain ⟨H, hH⟩ := hline
  refine ⟨⟨⟨fun i => ν (Fin.castLE (min_le_left n r) i), fun i j hij =>
    hant (show Fin.castLE (min_le_left n r) i ≤ Fin.castLE (min_le_left n r) j from hij)⟩, ?_⟩, ?_⟩
  · funext s
    simp only [rowNu]
    split_ifs with hs
    · exact congrArg ν (Fin.ext rfl)
    · have hsn := s.isLt
      exact h0 s (by omega)
  · intro w hw' hkw
    obtain ⟨c₀, hc₀⟩ := hH v hv hkv
    obtain ⟨c₁, hc₁⟩ := hH w hw' hkw
    have hc0 : c₀ ≠ 0 := by
      rintro rfl
      exact hv0 (by rw [hc₀, zero_smul])
    refine ⟨c₁ / c₀, ?_⟩
    rw [hc₁, hc₀, smul_smul, div_mul_cancel₀ _ hc0]

end GlobalTheory.GLDuality.HighestLine
end

section

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open Formalism.REAL (fockF)
open scoped DirectSum TensorProduct Kronecker Matrix

namespace GlobalTheory.GLDuality

theorem matRep_diagGL_monomial_colChar {n n' : ℕ} (t : Fin n → ℂˣ) (d : Fin n' × Fin n →₀ ℕ) (c : ℂ) :
    matRep n n' (diagGL ℂ n t, 1) (monomial d c) =
      monomial d ((d.prod fun x e => (t x.2 : ℂ) ^ e) * c) := by
  have h : sub (((1 : GL (Fin n') ℂ) : Matrix (Fin n') (Fin n') ℂ) ⊗ₖ
      ((diagGL ℂ n t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))ᵀ =
      aeval (fun x : Fin n' × Fin n => C (t x.2 : ℂ) * (X x : MvPolynomial (Fin n' × Fin n) ℂ)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    simp [sub, diagGL, Fintype.sum_prod_type, Matrix.one_apply, Matrix.diagonal_apply, apply_ite C]
  rw [matRep_apply, h, aeval_monomial, monomial_eq]
  simp only [mul_pow, Finsupp.prod, Finset.prod_mul_distrib, map_mul, map_prod, map_pow, algebraMap_eq]
  ring

theorem coeff_matRep_diagGL_colChar {n n' : ℕ} (t : Fin n → ℂˣ) (v : MvPolynomial (Fin n' × Fin n) ℂ)
    (d : Fin n' × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (matRep n n' (diagGL ℂ n t, 1) v) d = (d.prod fun x e => (t x.2 : ℂ) ^ e) * AddMonoidAlgebra.coeff v d := by
  classical
  induction v using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [matRep_diagGL_monomial_colChar, coeff_monomial, coeff_monomial]
    split_ifs with h
    · rw [h]
    · simp
  | add p q hp hq => rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

theorem colAdd_eq_matRep_of_transvection {n n' : ℕ} (l j : Fin n) (c : ℂ) (g : GL (Fin n) ℂ)
    (hg : (g : Matrix (Fin n) (Fin n) ℂ) = Matrix.transvection l j c)
    (v : MvPolynomial (Fin n' × Fin n) ℂ) : colAdd ℂ l j c v = matRep n n' (g, 1) v := by
  have h : sub (((1 : GL (Fin n') ℂ) : Matrix (Fin n') (Fin n') ℂ) ⊗ₖ
      (g : Matrix (Fin n) (Fin n) ℂ))ᵀ = colAdd ℂ (r := n') l j c := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    rw [hg]
    by_cases hs : s = j
    · subst hs
      simp [sub, colAdd, Fintype.sum_prod_type, Matrix.one_apply, Matrix.transvection, Matrix.single_apply,
        apply_ite C, add_mul, Finset.sum_add_distrib]
    · have hs' : ¬ j = s := fun e => hs e.symm
      simp [sub, colAdd, Fintype.sum_prod_type, Matrix.one_apply, Matrix.transvection, Matrix.single_apply,
        apply_ite C, hs, hs']
  rw [matRep_apply, h]

theorem mem_dualWeyl_of_unitriangular_fixed :
    ∀ (n n' : ℕ) (ν : Fin n → ℕ) (v : MvPolynomial (Fin n' × Fin n) ℂ), (∀ g : GL (Fin n) ℂ, (g : Matrix (Fin n) (Fin n) ℂ).BlockTriangular id → (∀ a, (g : Matrix (Fin n) (Fin n) ℂ) a a = 1) → matRep n n' (g, 1) v = v) → (∀ t : Fin n → ℂˣ, matRep n n' (diagGL ℂ n t, 1) v = (∏ a, (t a : ℂ) ^ ν a) • v) → v ∈ dualWeyl ℂ n' n ν := by
  intro n n' ν v hU hT
  rw [Formalism.GradedWeylDivisibility.dualWeylPoint ℂ n' n ν v]
  refine ⟨fun d hd => ?_, fun l j hlj c => ?_⟩
  · funext i
    let t : Fin n → ℂˣ := fun s => if s = i then Units.mk0 2 two_ne_zero else 1
    have h1 := congrArg (AddMonoidAlgebra.coeff · d) (hT t)
    rw [coeff_matRep_diagGL_colChar, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at h1
    have h2 := mul_right_cancel₀ hd h1
    have h3 : (∏ a, (t a : ℂ) ^ ν a) = 2 ^ ν i := by
      rw [Finset.prod_eq_single i]
      · simp [t]
      · intro b _ hb
        simp [t, hb]
      · simp
    have h4 : (d.prod fun x e => (t x.2 : ℂ) ^ e) = 2 ^ (Finsupp.weight (colW n' n) d i) := by
      rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, ← Finset.prod_pow_eq_pow_sum, Finsupp.prod]
      refine Finset.prod_congr rfl fun x _ => ?_
      by_cases hx : x.2 = i
      · simp [t, colW, hx]
      · simp [t, colW, hx]
    rw [h3, h4] at h2
    have h5 : (2 : ℕ) ^ (Finsupp.weight (colW n' n) d i) = 2 ^ ν i := by exact_mod_cast h2
    exact Nat.pow_right_injective le_rfl h5
  · have hne : l ≠ j := hlj.ne
    let g : GL (Fin n) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection l j c)
      (by rw [Matrix.det_transvection_of_ne l j hne]; exact one_ne_zero)
    have hg : (g : Matrix (Fin n) (Fin n) ℂ) = Matrix.transvection l j c := rfl
    rw [colAdd_eq_matRep_of_transvection l j c g hg]
    refine hU g ?_ ?_
    · intro a b hab
      have hab' : b < a := hab
      have h1 : ¬ (l = a ∧ j = b) := by
        rintro ⟨rfl, rfl⟩
        exact lt_asymm hlj hab'
      rw [hg]
      simp [Matrix.transvection, h1, Matrix.one_apply_ne hab'.ne']
    · intro a
      have h1 : ¬ (l = a ∧ j = a) := by
        rintro ⟨rfl, rfl⟩
        exact hne rfl
      rw [hg]
      simp [Matrix.transvection, h1]

end GlobalTheory.GLDuality
end

section

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open Formalism.REAL (fockF)
open scoped DirectSum TensorProduct Kronecker Matrix

noncomputable section

namespace GlobalTheory.GLDuality

def pairLmul {n n' k : ℕ} (x : Matrix (Fin n') (Fin n) ℂ) :
    MvPolynomial (Fin n' × Fin k) ℂ →ₐ[ℂ] MvPolynomial (Fin n × Fin k) ℂ :=
  aeval (fun v : Fin n' × Fin k => ∑ t : Fin n, C (x v.1 t) * (X (t, v.2) : MvPolynomial (Fin n × Fin k) ℂ))

theorem pairLmul_rowAct {n n' k : ℕ} (x : Matrix (Fin n') (Fin n) ℂ) (h : Matrix (Fin n') (Fin n') ℂ)
    (f : MvPolynomial (Fin n' × Fin k) ℂ) : pairLmul x (rowAct ℂ h f) = pairLmul (h * x) f := by
  have : (pairLmul x).comp (rowAct ℂ (n := k) h) = pairLmul (h * x) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩

    simp only [pairLmul, rowAct, AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq,
    Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [← this]; rfl

theorem rowAct_pairLmul {n n' k : ℕ} (x : Matrix (Fin n') (Fin n) ℂ) (g : Matrix (Fin n) (Fin n) ℂ)
    (f : MvPolynomial (Fin n' × Fin k) ℂ) : rowAct ℂ g (pairLmul x f) = pairLmul (x * g) f := by
  have : (rowAct ℂ (n := k) g).comp (pairLmul x) = pairLmul (x * g) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩

    simp only [pairLmul, rowAct, AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq,
    Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [← this]; rfl

theorem pair_map_conj_rowAct {n k : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (p : MvPolynomial (Fin n × Fin k) ℂ) :
    map (starRingEnd ℂ) (rowAct ℂ g p) = rowAct ℂ (gᵀ)ᴴ (map (starRingEnd ℂ) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [rowAct]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1

    simp [rowAct, map_sum]

theorem pair_map_conj_hw {n k : ℕ} (hn : k ≤ n) (ν : Fin k → ℕ) :
    map (starRingEnd ℂ) (hw ℂ hn ν) = hw ℂ hn ν := by
  simp only [hw, map_prod, map_pow, lpMinor]
  refine Finset.prod_congr rfl fun s _ => ?_
  congr 1
  rw [RingHom.map_det]
  congr 1
  ext p q : 1
  simp

theorem pairLmul_hw {n n' k : ℕ} (hn : k ≤ n) (hn' : k ≤ n') (ν : Fin k → ℕ) :
    pairLmul (Matrix.of fun (a : Fin n') (t : Fin n) => if a.val = t.val then (1 : ℂ) else 0) (hw ℂ hn' ν) =
      hw ℂ hn ν := by
  simp only [hw, map_prod, map_pow, lpMinor]
  refine Finset.prod_congr rfl fun s _ => ?_
  congr 1
  rw [AlgHom.map_det]
  congr 1
  ext p q : 1
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, pairLmul, aeval_X]
  rw [Finset.sum_eq_single (Fin.castLE (by have := s.2; omega) p)]
  · simp
  · intro b _ hb
    rw [if_neg]
    · simp
    · intro e
      exact hb (Fin.ext (by simpa using e.symm))
  · simp

theorem pairing_equivariant_and_ne_zero : ∀ (n n' k : ℕ) (T : MvPolynomial (Fin n × Fin k) ℂ →ₗ[ℂ] MvPolynomial (Fin n' × Fin k) ℂ →ₗ[ℂ] MvPolynomial (Fin n' × Fin n) ℂ), (∀ (φ : MvPolynomial (Fin n × Fin k) ℂ) (f : MvPolynomial (Fin n' × Fin k) ℂ) (x : Matrix (Fin n') (Fin n) ℂ), eval (fun v => x v.1 v.2) (T φ f) = fockF φ (map (starRingEnd ℂ) (aeval (fun v : Fin n' × Fin k => ∑ t : Fin n, C (x v.1 t) * (X (t, v.2) : MvPolynomial (Fin n × Fin k) ℂ)) f))) → (∀ (g : GL (Fin n) ℂ) (h : GL (Fin n') ℂ) (φ : MvPolynomial (Fin n × Fin k) ℂ) (f : MvPolynomial (Fin n' × Fin k) ℂ), T (rowAct ℂ (g : Matrix (Fin n) (Fin n) ℂ)ᵀ φ) (rowAct ℂ (h : Matrix (Fin n') (Fin n') ℂ)ᵀ f) = matRep n n' (g, h) (T φ f)) ∧ ∀ (hn : k ≤ n) (hn' : k ≤ n') (ν : Fin k → ℕ), T (hw ℂ hn ν) (hw ℂ hn' ν) ≠ 0 := by
  intro n n' k T hT
  have hT' : ∀ φ f (x : Matrix (Fin n') (Fin n) ℂ),
      eval (fun v => x v.1 v.2) (T φ f) = fockF φ (map (starRingEnd ℂ) (pairLmul x f)) := hT
  refine ⟨fun g h φ f => ?_, fun hn hn' ν h0 => ?_⟩
  · apply MvPolynomial.funext
    intro p
    have hp : p = fun v => (Matrix.of fun a t => p (a, t)) v.1 v.2 := rfl
    rw [hp, eval_matRep, hT', hT', fockRowAdj, pairLmul_rowAct, ← pair_map_conj_rowAct, rowAct_pairLmul]
  · have h1 := hT' (hw ℂ hn ν) (hw ℂ hn' ν)
      (Matrix.of fun (a : Fin n') (t : Fin n) => if a.val = t.val then (1 : ℂ) else 0)
    rw [h0, map_zero, pairLmul_hw hn hn', pair_map_conj_hw] at h1
    have h2 := (fockPos _ _ (hwNe ℂ n k hn ν)).1
    rw [← h1] at h2
    simp at h2

end GlobalTheory.GLDuality
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mul_comm_of_mem_GfC_of_mem_GinfC : ∀ {D : D7} (V : HSp D) (a b : GA D V), a ∈ GfC V → b ∈ GinfC V → a * b = b * a := by
  first | exact @GlobalTheory.FinRealComm.finite_real_points_commute | exact GlobalTheory.FinRealComm.finite_real_points_commute | (intros; apply GlobalTheory.FinRealComm.finite_real_points_commute <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

theorem _root_.GlobalTheory.T.polarCoordinates_unitaryPQ_doubleCover : ∀ X : ProvA, CoverHaarIntegration X := by
  first | exact @GlobalTheory.PolarU.polar_coordinates | exact GlobalTheory.PolarU.polar_coordinates | (intros; apply GlobalTheory.PolarU.polar_coordinates <;> assumption)
end
