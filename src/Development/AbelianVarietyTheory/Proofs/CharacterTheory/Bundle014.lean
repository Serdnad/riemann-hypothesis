module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RepresentationTheory.Basic
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
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt

@[expose] public section

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem sum_roots_charpoly_eq_finsum_eigenspace (k : Type) [Field k] [IsAlgClosed k] (V : Type)
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] (g : Module.End k V) (N : ℕ)
    (hN : (N : k) ≠ 0) (hg : g ^ N = 1) (h : k → ℂ) :
    ((LinearMap.charpoly g).roots.map h).sum =
      ∑ᶠ μ ∈ {μ : k | μ ^ N = 1}, (Module.finrank k (Module.End.eigenspace g μ) : ℂ) * h μ := by
  classical
  have hsep : (X ^ N - C (1 : k) : k[X]).Separable := separable_X_pow_sub_C 1 hN one_ne_zero
  have hss : g.IsSemisimple :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree (by simp [hg])
  have hdim : ∀ μ, Module.finrank k (Module.End.eigenspace g μ) =
      (LinearMap.charpoly g).roots.count μ := by
    intro μ
    rw [← hss.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ,
      LinearMap.finrank_maxGenEigenspace_eq, count_roots]
  rw [Finset.sum_multiset_map_count]
  rw [finsum_mem_eq_sum_of_inter_support_eq _ (t := (LinearMap.charpoly g).roots.toFinset)]
  · refine Finset.sum_congr rfl fun μ _ => ?_
    rw [hdim, nsmul_eq_mul]
  · ext μ
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Function.mem_support, Finset.mem_coe,
      Multiset.mem_toFinset]
    constructor
    · rintro ⟨-, h2⟩
      refine ⟨?_, h2⟩
      by_contra hc
      apply h2
      rw [hdim, Multiset.count_eq_zero_of_notMem hc]
      simp
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      have hev : g.HasEigenvalue μ := by
        rw [Module.End.hasEigenvalue_iff_isRoot_charpoly]
        exact isRoot_of_mem_roots h1
      have h3 := hev.pow N
      rw [hg] at h3
      obtain ⟨v, hv⟩ := h3.exists_hasEigenvector
      have h4 := hv.apply_eq_smul
      have h5 : (μ ^ N - 1) • v = 0 := by
        rw [sub_smul, ← h4]; simp
      exact sub_eq_zero.mp ((smul_eq_zero.mp h5).resolve_right hv.2)

end GlobalTheory.CuspGL
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CharpolyPow

variable {k : Type} [Field k] [IsAlgClosed k] {n : ℕ}

lemma card_roots_charpoly (M : Matrix (Fin n) (Fin n) k) : Multiset.card M.charpoly.roots = n := by
  rw [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

lemma det_scalar_sub (M : Matrix (Fin n) (Fin n) k) (t : k) :
    (Matrix.scalar (Fin n) t - M).det = (M.charpoly.roots.map (fun z => t - z)).prod := by
  have hroots : Multiset.card M.charpoly.roots = M.charpoly.natDegree := by
    rw [card_roots_charpoly, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  rw [← Matrix.eval_charpoly,
    ← prod_multiset_X_sub_C_of_monic_of_roots_card_eq (Matrix.charpoly_monic M) hroots,
    eval_multiset_prod, Multiset.map_map]
  simp

lemma det_aeval_prod (M : Matrix (Fin n) (Fin n) k) (s : Multiset k) :
    (aeval M (s.map (fun a => C a - X)).prod).det
      = (M.charpoly.roots.map (fun z => eval z (s.map (fun a => C a - X)).prod)).prod := by
  have key : ∀ a : k, (aeval M (C a - X)).det = (M.charpoly.roots.map (fun z => a - z)).prod := by
    intro a
    rw [← det_scalar_sub]
    congr 1
    simp [Matrix.scalar, Algebra.algebraMap_eq_smul_one, Matrix.smul_one_eq_diagonal]
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, map_mul, Matrix.det_mul, key, ih,
      ← Multiset.prod_map_mul]
    congr 1
    apply Multiset.map_congr rfl
    intro z _
    simp

lemma det_aeval (M : Matrix (Fin n) (Fin n) k) (q : k[X]) :
    (aeval M q).det = (M.charpoly.roots.map (fun z => eval z q)).prod := by
  set m := Multiset.card q.roots
  set c := q.leadingCoeff * (-1) ^ m
  have hq : q = C c * (q.roots.map (fun a => C a - X)).prod := by
    have hsplit := C_leadingCoeff_mul_prod_multiset_X_sub_C (p := q) IsAlgClosed.card_roots_eq_natDegree
    have hneg : (q.roots.map (fun a => C a - X)).prod
        = (-1) ^ m * (q.roots.map (fun a => X - C a)).prod := by
      have : (fun a : k => C a - X) = fun a => (-1) * (X - C a) := by
        funext a; ring
      rw [this, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate]
    rw [hneg, C_mul, C_pow, C_neg, C_1]
    calc q = C q.leadingCoeff * (q.roots.map (fun a => X - C a)).prod := hsplit.symm
      _ = C q.leadingCoeff * (-1) ^ m * ((-1) ^ m * (q.roots.map (fun a => X - C a)).prod) := by
        rw [← mul_assoc, mul_assoc (C q.leadingCoeff), ← pow_add, ← two_mul, pow_mul]
        simp
  have hcard : Multiset.card M.charpoly.roots = n := card_roots_charpoly M
  conv_lhs => rw [hq]
  conv_rhs => rw [hq]
  rw [map_mul, aeval_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, Matrix.det_smul,
    Fintype.card_fin, det_aeval_prod]
  simp only [eval_mul, eval_C]
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hcard]

theorem roots_charpoly_pow (k : Type) [Field k] [IsAlgClosed k] (n r : ℕ)
    (M : Matrix (Fin n) (Fin n) k) :
    (Matrix.charpoly (M ^ r)).roots = (Matrix.charpoly M).roots.map (· ^ r) := by
  have hinf : Infinite k := IsAlgClosed.instInfinite
  have hcard : Multiset.card (Matrix.charpoly (M ^ r)).roots = (Matrix.charpoly (M ^ r)).natDegree := by
    exact IsAlgClosed.card_roots_eq_natDegree
  have hfac := prod_multiset_X_sub_C_of_monic_of_roots_card_eq (Matrix.charpoly_monic (M ^ r)) hcard
  suffices h : Matrix.charpoly (M ^ r) = (((Matrix.charpoly M).roots.map (· ^ r)).map fun a => X - C a).prod by
    rw [h, roots_multiset_prod_X_sub_C]
  apply Polynomial.funext
  intro t
  rw [Matrix.eval_charpoly, eval_multiset_prod, Multiset.map_map, Multiset.map_map]
  have h1 : Matrix.scalar (Fin n) t - M ^ r = aeval M (C t - X ^ r) := by
    simp [Matrix.scalar, Algebra.algebraMap_eq_smul_one, Matrix.smul_one_eq_diagonal]
  rw [h1, GlobalTheory.CharpolyPow.det_aeval]
  simp [Function.comp_def]

end GlobalTheory.CharpolyPow
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem exists_monomial_basis_of_imprimitive (k : Type) [Field k] (G : Type) [Group G] [Finite G]
    (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k G V)
    (T : Subgroup G) (W : Submodule k V)
    (hind : iSupIndep (fun q : G ⧸ T => W.map (ρ q.out)))
    (hsup : ⨆ q : G ⧸ T, W.map (ρ q.out) = ⊤)
    (hW : ∃ (n : ℕ) (b : Module.Basis (Fin n) k W), ∀ t ∈ T, ∀ i : Fin n,
      ∃ (j : Fin n) (c : k), ρ t (b i : V) = c • (b j : V)) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) k V), ∀ (g : G) (i : Fin n),
      ∃ (j : Fin n) (c : k), ρ g (b i) = c • b j := by
  classical
  obtain ⟨n, b, hb⟩ := hW
  have hinj : ∀ g : G, Function.Injective (ρ g) := by
    intro g x y h
    have h2 := congrArg (ρ g⁻¹) h
    simpa [← Module.End.mul_apply, ← map_mul] using h2
  have hint : DirectSum.IsInternal (fun q : G ⧸ T => W.map (ρ q.out)) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind hsup
  let bq : ∀ q : G ⧸ T, Module.Basis (Fin n) k (W.map (ρ q.out)) := fun q =>
    b.map (Submodule.equivMapOfInjective (ρ q.out) (hinj _) W)
  let B := hint.collectedBasis bq
  have hB : ∀ (q : G ⧸ T) (i : Fin n), B ⟨q, i⟩ = ρ q.out (b i : V) := by
    intro q i
    simp [B, bq]
  haveI : Fintype (G ⧸ T) := Fintype.ofFinite _
  let e := Fintype.equivFin (Σ _ : G ⧸ T, Fin n)
  refine ⟨_, B.reindex e, fun g i => ?_⟩
  obtain ⟨⟨q, i⟩, rfl⟩ := e.surjective i
  obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul T (g * q.out)
  obtain ⟨j, c, hj⟩ := hb (t⁻¹ : T) (t⁻¹).2 i
  refine ⟨e ⟨(QuotientGroup.mk (g * q.out) : G ⧸ T), j⟩, c, ?_⟩
  simp only [Module.Basis.reindex_apply, Equiv.symm_apply_apply, hB]
  rw [← map_smul, ← hj, ht, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  simp

end GlobalTheory.CuspGL
end

end

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

theorem _root_.GlobalTheory.T.roots_charpoly_pow_eq_map_pow : ∀ (k : Type) [Field k] [IsAlgClosed k] (n r : ℕ) (M : Matrix (Fin n) (Fin n) k), (Matrix.charpoly (M ^ r)).roots = (Matrix.charpoly M).roots.map (· ^ r) := by
  first | exact @GlobalTheory.CharpolyPow.roots_charpoly_pow | exact GlobalTheory.CharpolyPow.roots_charpoly_pow | (intros; apply GlobalTheory.CharpolyPow.roots_charpoly_pow <;> assumption)

end
end
