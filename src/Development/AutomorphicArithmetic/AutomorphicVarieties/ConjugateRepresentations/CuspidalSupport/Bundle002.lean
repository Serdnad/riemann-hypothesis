module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

@[expose] public section

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

namespace UpperTheory.V.Cj.S

section SlopeTestRemainingChoices

variable {X Y V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

private noncomputable def sl1 (jW : W →ₗ[ℂ] (Y → ℂ)) (y : Y) : V ⊗[ℂ] W →ₗ[ℂ] V :=
  (TensorProduct.rid ℂ V).toLinearMap ∘ₗ LinearMap.lTensor V (LinearMap.proj y ∘ₗ jW)

private theorem slice_first_tmul (jW : W →ₗ[ℂ] (Y → ℂ)) (y : Y) (v : V) (w : W) : sl1 jW y (v ⊗ₜ[ℂ] w) = jW w y • v := by
  simp [sl1]

end SlopeTestRemainingChoices

end UpperTheory.V.Cj.S

private theorem tensor_exists_finBasis_expansion {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ V] (t : V ⊗[ℂ] W) :
    ∃ m : Fin (Module.finrank ℂ V) → W, t = ∑ a, Module.finBasis ℂ V a ⊗ₜ[ℂ] m a := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul v w =>
    refine ⟨fun a => (Module.finBasis ℂ V).repr v a • w, ?_⟩
    conv_lhs => rw [← (Module.finBasis ℂ V).sum_repr v]
    rw [TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    exact TensorProduct.smul_tmul _ _ _
  | add t1 t2 h1 h2 =>
    obtain ⟨m1, rfl⟩ := h1
    obtain ⟨m2, rfl⟩ := h2
    exact ⟨m1 + m2, by simp [TensorProduct.tmul_add, Finset.sum_add_distrib]⟩

private theorem tensor_eq_zero_of_sl1_vanishing {V W Y : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ V] (jW : W →ₗ[ℂ] (Y → ℂ)) (hjW : Function.Injective jW) (t : V ⊗[ℂ] W)
    (ht : ∀ y, UpperTheory.V.Cj.S.sl1 jW y t = 0) : t = 0 := by
  obtain ⟨m, rfl⟩ := tensor_exists_finBasis_expansion (V := V) (W := W) t
  have hm : ∀ a, m a = 0 := by
    intro a
    apply hjW
    rw [map_zero]
    funext y
    have hy := ht y

    simp only [map_sum, UpperTheory.V.Cj.S.slice_first_tmul] at hy
    have := (Fintype.linearIndependent_iff.mp (Module.finBasis ℂ V).linearIndependent) (fun a => jW (m a) y) hy a
    simpa using this
  simp [hm]

private theorem exists_vec_of_dual_apply_col {X Y V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ V] (jV : V →ₗ[ℂ] (X → ℂ)) (hjV : Function.Injective jV)
    (jW : W →ₗ[ℂ] (Y → ℂ)) (col : Y → V) (hrow : ∀ x, ∃ w : W, jW w = fun y => jV (col y) x)
    (φ : Module.Dual ℂ V) : ∃ w : W, jW w = fun y => φ (col y) := by
  let P : Submodule ℂ (Module.Dual ℂ V) :=
    { carrier := {ψ | ∃ w : W, jW w = fun y => ψ (col y)}
      add_mem' := by
        rintro ψ χ ⟨w1, h1⟩ ⟨w2, h2⟩
        exact ⟨w1 + w2, by rw [map_add (f := _), h1, h2]; rfl⟩
      zero_mem' := ⟨0, by rw [map_zero]; rfl⟩
      smul_mem' := by
        rintro c ψ ⟨w, h⟩
        exact ⟨c • w, by rw [map_smul, h]; rfl⟩ }
  have hev : ∀ x, (LinearMap.proj x ∘ₗ jV) ∈ P := by
    intro x
    obtain ⟨w, h⟩ := hrow x
    exact ⟨w, h⟩
  have hco : P.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_dualCoannihilator] at hv
    rw [Submodule.mem_bot]
    apply hjV
    funext x
    simpa using hv _ (hev x)
  have htop : P = ⊤ := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := P), hco, Submodule.dualAnnihilator_bot]
  have hφ : φ ∈ P := by
    rw [htop]
    exact Submodule.mem_top
  exact hφ

theorem UpperTheory.V.Cj.S.twoVar :
    UpperTheory.V.Cj.S.TensEig → UpperTheory.V.Cj.S.TwoVar := by
  intro hT X Y M N V W hVf hWf ι κ A B hAV hBW hAc hBc F hF hcol hrow
  let jV : V →ₗ[ℂ] (X → ℂ) := M.subtype ∘ₗ V.subtype
  let jW : W →ₗ[ℂ] (Y → ℂ) := N.subtype ∘ₗ W.subtype
  have hjV : Function.Injective jV := Subtype.val_injective.comp Subtype.val_injective
  have hjW : Function.Injective jW := Subtype.val_injective.comp Subtype.val_injective
  choose col hcolV hcolF using hcol
  let colV : Y → V := fun y => ⟨col y, hcolV y⟩
  have hjcol : ∀ y, jV (colV y) = fun x => F x y := fun y => hcolF y
  have hrow' : ∀ x, ∃ w : W, jW w = fun y => jV (colV y) x := by
    intro x
    obtain ⟨f, hfW, hf⟩ := hrow x
    refine ⟨⟨f, hfW⟩, ?_⟩
    funext y
    rw [hjcol]
    show (f : Y → ℂ) y = F x y
    rw [hf]
  let bV := Module.finBasis ℂ V
  choose w hw using fun a => exists_vec_of_dual_apply_col jV hjV jW colV hrow' (bV.coord a)
  let z : V ⊗[ℂ] W := ∑ a, bV a ⊗ₜ[ℂ] w a
  have hz : ∀ y, UpperTheory.V.Cj.S.sl1 jW y z = colV y := by
    intro y

    simp only [z, map_sum, UpperTheory.V.Cj.S.slice_first_tmul, hw]
    simpa [Module.Basis.coord_apply] using bV.sum_repr (colV y)
  have hFz : ∀ x y, jV (UpperTheory.V.Cj.S.sl1 jW y z) x = F x y := by
    intro x y
    rw [hz, hjcol]
  have hz0 : z ≠ 0 := by
    obtain ⟨x0, y0, h0⟩ := hF
    intro h
    apply h0
    rw [← hFz, h]
    simp
  let A' : ι → Module.End ℂ V := fun i => (A i).restrict (hAV i)
  let B' : κ → Module.End ℂ W := fun k => (B k).restrict (hBW k)
  have hA' : ∀ i (v : V), ((A' i v : V) : M) = A i v := fun i v => rfl
  have hB' : ∀ k (w : W), ((B' k w : W) : N) = B k w := fun k w => rfl
  have cA : ∀ i i', Commute (A' i) (A' i') := by
    intro i i'
    exact LinearMap.ext fun v => Subtype.ext (hAc i i' v v.2)
  have cB : ∀ k k', Commute (B' k) (B' k') := by
    intro k k'
    exact LinearMap.ext fun w => Subtype.ext (hBc k k' w w.2)
  obtain ⟨v, w', l, m, hv, hw', hAv, hBw, hprop⟩ := hT V W ι κ A' B' cA cB z hz0
  refine ⟨v, v.2, w', w'.2, l, m, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hv (Subtype.ext h)
  · intro h
    exact hw' (Subtype.ext h)
  · intro i
    have := congrArg Subtype.val (hAv i)
    simpa [hA'] using this
  · intro k
    have := congrArg Subtype.val (hBw k)
    simpa [hB'] using this
  · intro σ _ c ip kp G e hAct hsum
    have hsumV : ∀ y', (∑ a, jW (w a) y' • bV a) = colV y' := by
      intro y'
      simpa [hw, Module.Basis.coord_apply] using bV.sum_repr (colV y')
    have key : ∀ i k (Gp : X → Y → ℂ), Act2 (A i) (B k) F Gp → ∀ x y,
        jV (UpperTheory.V.Cj.S.sl1 jW y (TensorProduct.map (A' i) (B' k) z)) x = Gp x y := by
      intro i k Gp hG x y
      obtain ⟨H, h1, h2⟩ := hG
      have hH : ∀ x' y', H x' y' = ∑ a, jW (w a) y' * jV (A' i (bV a)) x' := by
        intro x' y'
        obtain ⟨f, hf1, hf2⟩ := h1 y'
        have hf : f = ((∑ a, jW (w a) y' • bV a : V) : M) := by
          apply Subtype.val_injective
          rw [hf1, hsumV]
          exact (hjcol y').symm
        have := congrFun hf2 x'
        rw [← this, hf]

        simp [map_sum, jV, hA']
      obtain ⟨f', hf'1, hf'2⟩ := h2 x
      have hf' : f' = ((∑ a, jV (A' i (bV a)) x • w a : W) : N) := by
        apply Subtype.val_injective
        rw [hf'1]
        funext y'
        rw [hH]
        simp [jW, jV, Finset.sum_apply, mul_comm]
      rw [← hf'2, hf']

      simp [z, map_sum, TensorProduct.map_tmul, UpperTheory.V.Cj.S.slice_first_tmul, jV, jW, hB', mul_comm]
    apply hprop σ c ip kp e
    rw [← sub_eq_zero]
    apply tensor_eq_zero_of_sl1_vanishing jW hjW
    intro y
    apply hjV
    rw [map_zero]
    funext x
    have key' : ∀ p, jV (UpperTheory.V.Cj.S.sl1 jW y (TensorProduct.map (A' (ip p)) (B' (kp p)) z)) x = G p x y :=
      fun p => key _ _ _ (hAct p) x y
    have hval : jV (UpperTheory.V.Cj.S.sl1 jW y
        (∑ p, c p • TensorProduct.map (A' (ip p)) (B' (kp p)) z - e • z)) x = ∑ p, c p * G p x y - e * F x y := by

      simp only [map_sub, map_sum, map_smul, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, key', hFz]
    rw [hval, hsum, sub_self]
    rfl
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem es_zero (A : Multiset ℂ) : A.esymm 0 = 1 := by simp [Multiset.esymm]

private theorem es_cons (a : ℂ) (A : Multiset ℂ) (k : ℕ) :
    (a ::ₘ A).esymm (k + 1) = A.esymm (k + 1) + a * A.esymm k := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.sum_map_mul_left]

private theorem es_big (A : Multiset ℂ) {k : ℕ} (h : A.card < k) : A.esymm k = 0 := by
  simp [Multiset.esymm, Multiset.powersetCard_eq_empty k h]

private theorem es_add (A C : Multiset ℂ) (j : ℕ) :
    (A + C).esymm j = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal j, A.esymm p.1 * C.esymm p.2 := by
  induction A using Multiset.induction_on generalizing j with
  | empty =>
    rw [Finset.sum_eq_single (0, j)]
    · simp [es_zero]
    · rintro ⟨i, k⟩ hp hne
      have : 0 < i := by
        rcases Nat.eq_zero_or_pos i with rfl | h
        · simp at hp; simp [hp] at hne
        · exact h
      rw [es_big 0 (by simpa using this), zero_mul]
    · simp
  | cons a A ih =>
    cases j with
    | zero => simp [es_zero]
    | succ j =>
      rw [Multiset.cons_add, es_cons, ih, ih, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ]
      simp only [es_cons, es_zero, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, add_assoc]

private theorem es_add_fin (A C : Multiset ℂ) {r s : ℕ} (hA : A.card = r) (hC : C.card = s) (j : ℕ) :
    (A + C).esymm j =
      ∑ p : Fin (r + 1) × Fin (s + 1), if (p.1 : ℕ) + p.2 = j then A.esymm p.1 * C.esymm p.2 else 0 := by
  rw [es_add, ← Finset.sum_filter]
  symm
  refine Finset.sum_of_injOn (fun p => ((p.1 : ℕ), (p.2 : ℕ))) ?_ ?_ ?_ fun _ _ => rfl
  · rintro ⟨a, b⟩ - ⟨c, d⟩ - h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)
  · intro p hp
    simpa using hp
  · rintro ⟨i, k⟩ hp hn
    by_cases hi : r < i
    · rw [es_big A (hA ▸ hi), zero_mul]
    by_cases hk : s < k
    · rw [es_big C (hC ▸ hk), mul_zero]
    exact absurd ⟨(⟨i, by omega⟩, ⟨k, by omega⟩), by simpa using hp, rfl⟩ hn

private theorem es_scale (A : Multiset ℂˣ) (c : ℂˣ) (k : ℕ) :
    ((A.map (· * c)).map fun b : ℂˣ => (b : ℂ)).esymm k = (c : ℂ) ^ k * (A.map fun b : ℂˣ => (b : ℂ)).esymm k := by
  rw [← smul_eq_mul, Multiset.pow_smul_esymm]
  simp [Multiset.map_map, mul_comm]

theorem UpperTheory.V.Cj.S.satArith :
    UpperTheory.V.Cj.S.SatArith := by
  intro q r s hq B B₁ B₂ hB h₁ h₂ h α β hα hβ
  refine eq_of_satEig_eq hq hB (by simp [h₁, h₂]) fun j hj => ?_
  rw [← h j hj, satEig, Multiset.map_add (f := _), es_add_fin (r := r) (s := s) _ _ (by simpa using h₁) (by simpa using h₂),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold coef
  split_ifs with hp
  swap
  · simp
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have hk : (p.2 : ℕ) ≤ s := Nat.lt_succ_iff.1 p.2.2
  have key : (q : ℂ) ^ ((p.1 : ℕ) * (s - p.2)) * (q : ℂ) ^ ((((p.1 : ℕ) : ℂ) * ((r : ℂ) - (p.1 : ℕ))) / 2) *
      (q : ℂ) ^ ((((p.2 : ℕ) : ℂ) * ((s : ℂ) - (p.2 : ℕ))) / 2) =
      (q : ℂ) ^ (((j : ℂ) * (((r + s : ℕ) : ℂ) - j)) / 2) * (α : ℂ) ^ (p.1 : ℕ) * (β : ℂ) ^ (p.2 : ℕ) := by
    rw [hα, hβ, ← Complex.cpow_nat_mul, ← Complex.cpow_nat_mul, ← Complex.cpow_natCast, ← Complex.cpow_add _ _ hq',
      ← Complex.cpow_add _ _ hq', ← Complex.cpow_add _ _ hq', ← Complex.cpow_add _ _ hq', ← hp]
    congr 1
    push_cast [hk]
    ring
  rw [es_scale, es_scale, satEig, satEig]
  linear_combination ((B₁.map fun b : ℂˣ => (b : ℂ)).esymm p.1 * (B₂.map fun b : ℂˣ => (b : ℂ)).esymm p.2) * key
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

section SlopeTestRemainingChoices

open UpperTheory.V.Af.Fin GroundTheory.Automorphic.AutomorphicForm

private theorem cn_ne {r s : ℕ} (i : Fin r) (j : Fin s) : Fin.castAdd s i ≠ Fin.natAdd r j := fun h => by
  have := congrArg Fin.val h
  simp at this
  omega

private theorem block_embedding_first_val {R : Type} [CommRing R] {r s : ℕ} (m : GL (Fin r) R) :
    (emb (e1 r s) m).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks m.val 0 0 1) := by
  ext i j
  rw [coe_emb, Matrix.add_apply]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · have := matrixExtendByZero_apply (e1 r s) (m.val - 1) i j
    simp only [orderedCechToCatCochainsOne_apply_valueAtSubset] at this
    rw [this]
    simp [Matrix.one_apply]
  · rw [matrixExtendByZero_apply_of_outside_col _ _ _ fun k => (cn_ne k j).symm]
    simp [Matrix.one_apply_ne (cn_ne i j)]
  · rw [extendByZero_apply_eq_zero_of_row_not_mem _ _ fun k => (cn_ne k i).symm]
    simp [Matrix.one_apply_ne (cn_ne j i).symm]
  · rw [extendByZero_apply_eq_zero_of_row_not_mem _ _ fun k => (cn_ne k i).symm]
    simp [Matrix.one_apply]

private theorem block_embedding_second_val {R : Type} [CommRing R] {r s : ℕ} (m : GL (Fin s) R) :
    (emb (e2 r s) m).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 0 0 m.val) := by
  ext i j
  rw [coe_emb, Matrix.add_apply]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [extendByZero_apply_eq_zero_of_row_not_mem _ _ fun k => (cn_ne i k)]
    simp [Matrix.one_apply]
  · rw [extendByZero_apply_eq_zero_of_row_not_mem _ _ fun k => (cn_ne i k)]
    simp [Matrix.one_apply_ne (cn_ne i j)]
  · rw [matrixExtendByZero_apply_of_outside_col _ _ _ fun k => (cn_ne j k)]
    simp [Matrix.one_apply_ne (cn_ne j i).symm]
  · have := matrixExtendByZero_apply (e2 r s) (m.val - 1) i j
    simp only [alternatingToOrderedCechDegreeTwo_apply_valueAtSubset] at this
    rw [this]
    simp [Matrix.one_apply]

private theorem unip_val {R : Type} [CommRing R] {r s : ℕ} (Y : Matrix (Fin r) (Fin s) R) :
    ∃ X : UPos (r + s) r → R,
      unipMatrix X = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 Y 0 1) := by
  refine ⟨fun p => Y ⟨p.1.1, p.2.1⟩ ⟨p.1.2 - r, by have := p.2.2; have := p.1.2.2; omega⟩, ?_⟩
  ext i j
  rw [unipMatrix, Matrix.add_apply, blockEntry_apply]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp [Matrix.one_apply]
  · simp [Matrix.one_apply_ne (cn_ne i j)]
  · simp [Matrix.one_apply_ne (cn_ne j i).symm]
  · simp [Matrix.one_apply]

private theorem block_form {R : Type} [CommRing R] {r s : ℕ} (b : GL (Fin (r + s)) R) (m₁ : GL (Fin r) R)
    (m₂ : GL (Fin s) R) (h₁ : ∀ i j, b.val (Fin.castAdd s i) (Fin.castAdd s j) = m₁.val i j)
    (h₂ : ∀ i j, b.val (Fin.natAdd r i) (Fin.natAdd r j) = m₂.val i j)
    (h₀ : ∀ i j, b.val (Fin.natAdd r i) (Fin.castAdd s j) = 0) :
    ∃ X : UPos (r + s) r → R, b = unipGL X * blk m₁ m₂ := by
  let B : Matrix (Fin r) (Fin s) R := b.val.submatrix (Fin.castAdd s) (Fin.natAdd r)
  have hb' : b.val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks m₁.val B 0 m₂.val) := by
    ext i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp [h₁]
    · simp [B]
    · simp [h₀]
    · simp [h₂]
  obtain ⟨X, hX⟩ := unip_val (B * (m₂⁻¹).val)
  refine ⟨X, Units.ext ?_⟩
  rw [blk, Units.val_mul, Units.val_mul, coe_unipGL, hX, block_embedding_first_val, block_embedding_second_val, hb']
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp [Matrix.mul_assoc]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Cj.S.matBlock :
    UpperTheory.V.Cj.S.MatBlock := by
  intro L _ O r s π hπ S c
  refine block_form _ _ _ (fun i j => ?_) (fun i j => ?_) fun i j => ?_
  · have hm : ∀ k, k ∈ sub1 S ↔ Fin.castAdd s k ∈ S := fun k => by simp [sub1]
    have hN : satakeN O S c (Fin.castAdd s i) (Fin.castAdd s j) = satakeN O (sub1 S) (c ∘ pair1 S) i j := by
      unfold satakeN
      by_cases h : i ∈ sub1 S ∧ j ∉ sub1 S ∧ i < j
      · rw [dite_eq_left h, dite_eq_left ⟨(hm i).1 h.1, fun h' => h.2.1 ((hm j).2 h'), h.2.2⟩]
        rfl
      · rw [dite_eq_right h, dite_eq_right fun h' => h ⟨(hm i).2 h'.1, fun h'' => h'.2.1 ((hm j).1 h''), h'.2.2⟩]
    rw [satakeGL_apply, satakeGL_apply, hN]
    simp [Matrix.one_apply, hm]
  · have hm : ∀ k, k ∈ sub2 S ↔ Fin.natAdd r k ∈ S := fun k => by simp [sub2]
    have hN : satakeN O S c (Fin.natAdd r i) (Fin.natAdd r j) = satakeN O (sub2 S) (c ∘ pair2 S) i j := by
      unfold satakeN
      by_cases h : i ∈ sub2 S ∧ j ∉ sub2 S ∧ i < j
      · rw [dite_eq_left h, dite_eq_left ⟨(hm i).1 h.1, fun h' => h.2.1 ((hm j).2 h'), Nat.add_lt_add_left h.2.2 r⟩]
        rfl
      · rw [dite_eq_right h, dite_eq_right fun h' => h ⟨(hm i).2 h'.1, fun h'' => h'.2.1 ((hm j).1 h''),
          Nat.lt_of_add_lt_add_left h'.2.2⟩]
    rw [satakeGL_apply, satakeGL_apply, hN]
    simp [Matrix.one_apply, hm]
  · apply satakeGL_lower
    change (Fin.castAdd s j).val < (Fin.natAdd r i).val
    simp
    omega
end

section

namespace UpperTheory.V.Cj.S

theorem suppAdd : SuppAdd := by
  intro E _ _ _ r s k l m₁ m₂ B₁ B₂ h₁ h₂
  obtain ⟨ι, _, n, π, μ, hk, hn, hs, hi, hm, hB⟩ := h₁
  obtain ⟨κ, _, n', π', μ', hk', hn', hs', hi', hm', hB'⟩ := h₂
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim n n', fun i => Sum.rec (fun i => π i) (fun i => π' i) i, Sum.elim μ μ',
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Fintype.card_sum]
    exact Nat.add_le_add hk hk'
  · rintro (i | i)
    · exact hn i
    · exact hn' i
  · rw [Fintype.sum_sum_type, ← hs, ← hs']
    rfl
  · rintro (i | i) t
    · exact hi i t
    · exact hi' i t
  · intro t
    rw [Fintype.sum_sum_type]
    show ∑ i, μ i t + ∑ i, μ' i t = m₁ t + m₂ t
    rw [hm t, hm' t]
  · filter_upwards [hB, hB'] with w hw hw'
    obtain ⟨C, hC, hCs⟩ := hw
    obtain ⟨C', hC', hCs'⟩ := hw'
    refine ⟨Sum.elim C C', ?_, ?_⟩
    · rintro (i | i)
      · exact hC i
      · exact hC' i
    · rw [Fintype.sum_sum_type]
      show ∑ i, C i + ∑ i, C' i = B₁ w + B₂ w
      rw [hCs, hCs']

end UpperTheory.V.Cj.S
end
