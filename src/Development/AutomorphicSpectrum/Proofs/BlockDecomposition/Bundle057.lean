module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.GroupTheory.Index
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle017
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.Topology.Algebra.Group.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle013
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle018
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle100
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.Order.CompletePartialOrder
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle019
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle020
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle015
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle001

@[expose] public section

section

open Matrix GlobalTheory.CompanionTheory.Jp

namespace GlobalTheory.CompanionTheory.Jp.CntCols

variable {k : Type} [Field k]

theorem rank_fromCols_eq_iff {n : ℕ} (C D : Matrix (Fin n) (Fin n) k) :
    (Matrix.fromCols C D).rank = n ↔ ∀ y : Fin n → k, y ᵥ* C = 0 → y ᵥ* D = 0 → y = 0 := by
  have h1 : (Matrix.fromCols C D).rank = Module.finrank k (LinearMap.range (Matrix.fromCols C D)ᵀ.mulVecLin) := by
    rw [Matrix.finrank_range_mulVecLin, Matrix.rank_transpose]
  have h2 := LinearMap.finrank_range_add_finrank_ker (Matrix.fromCols C D)ᵀ.mulVecLin
  rw [← h1, Module.finrank_fin_fun] at h2
  constructor
  · intro h y hC hD
    have h3 : Module.finrank k (LinearMap.ker (Matrix.fromCols C D)ᵀ.mulVecLin) = 0 := by omega
    have h4 := Submodule.finrank_eq_zero.mp h3
    have h5 : y ∈ LinearMap.ker (Matrix.fromCols C D)ᵀ.mulVecLin := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose, Matrix.vecMul_fromCols, hC, hD]
      ext i; cases i <;> simp
    rw [h4] at h5
    simpa using h5
  · intro h
    have h3 : LinearMap.ker (Matrix.fromCols C D)ᵀ.mulVecLin = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro y hy
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose, Matrix.vecMul_fromCols] at hy
      refine h y ?_ ?_
      · ext i; simpa using congrFun hy (Sum.inl i)
      · ext i; simpa using congrFun hy (Sum.inr i)
    rw [h3] at h2
    simpa using h2

theorem finrank_leftKer {n : ℕ} (D : Matrix (Fin n) (Fin n) k) :
    Module.finrank k (LinearMap.ker Dᵀ.mulVecLin) = n - D.rank := by
  have h1 : D.rank = Module.finrank k (LinearMap.range Dᵀ.mulVecLin) := by
    rw [Matrix.finrank_range_mulVecLin, Matrix.rank_transpose]
  have h2 := LinearMap.finrank_range_add_finrank_ker Dᵀ.mulVecLin
  rw [← h1, Module.finrank_fin_fun] at h2
  omega

theorem li_iff {V Z ι : Type} [AddCommGroup V] [Module k V] [AddCommGroup Z] [Module k Z] [Fintype ι]
    (b : Module.Basis ι k Z) (g : Z →ₗ[k] V) :
    LinearIndependent k (fun i => g (b i)) ↔ ∀ y, g y = 0 → y = 0 := by
  constructor
  · intro h y hy
    have h1 := Fintype.linearIndependent_iff.mp h (fun i => b.repr y i) (by
      have := congrArg g (b.sum_repr y)

      rw [map_sum, hy] at this
      simpa using this)
    rw [← b.sum_repr y]
    simp [h1]
  · intro h
    have : LinearMap.ker g = ⊥ := by
      rw [Submodule.eq_bot_iff]; intro y hy; exact h y hy
    exact b.linearIndependent.map' g this

theorem card_completions : ∀ (k : Type) [Field k] [Fintype k] (n ρ : ℕ) (D : Matrix (Fin n) (Fin n) k), D.rank = ρ →
    Nat.card {C : Matrix (Fin n) (Fin n) k // (Matrix.fromCols C D).rank = n} =
      Fintype.card k ^ (n * ρ) * ∏ j ∈ Finset.range (n - ρ), (Fintype.card k ^ n - Fintype.card k ^ j) := by
  intro k _ _ n ρ D hD
  have hρ : ρ ≤ n := by simpa [hD] using D.rank_le_width
  have hZ : Module.finrank k (LinearMap.ker Dᵀ.mulVecLin) = n - ρ := by rw [finrank_leftKer, hD]
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (LinearMap.ker Dᵀ.mulVecLin)
  have hWf : Module.finrank k W = ρ := by
    have := Submodule.finrank_add_eq_of_isCompl hW
    rw [hZ, Module.finrank_fin_fun] at this
    omega
  let bZ := Module.finBasisOfFinrankEq k _ hZ
  let bW := Module.finBasisOfFinrankEq k _ hWf
  let bV := (bZ.prod bW).map (Submodule.prodEquivOfIsCompl _ W hW)
  let E : Matrix (Fin n) (Fin n) k ≃ (Fin (n - ρ) → Fin n → k) × (Fin ρ → Fin n → k) :=
    ((Matrix.transposeLinearEquiv (Fin n) (Fin n) k k).toEquiv.trans
      (Matrix.toLin' (R := k) (m := Fin n) (n := Fin n)).toEquiv).trans
      ((bV.constr k).symm.toEquiv.trans (Equiv.sumArrowEquivProdArrow _ _ _))
  have hE : ∀ C i, (E C).1 i = (bZ i : Fin n → k) ᵥ* C := by
    intro C i
    simp [E, bV, Equiv.sumArrowEquivProdArrow, Module.Basis.constr, Matrix.mulVec_transpose]
  have hp : ∀ C, (Matrix.fromCols C D).rank = n ↔ LinearIndependent k (E C).1 := by
    intro C
    have h1 : (E C).1 = fun i => (Cᵀ.mulVecLin ∘ₗ (LinearMap.ker Dᵀ.mulVecLin).subtype) (bZ i) := by
      funext i
      rw [hE]
      simp [Matrix.mulVec_transpose]
    rw [h1, li_iff, rank_fromCols_eq_iff]
    constructor
    · intro h y hy
      have h2 : (y : Fin n → k) ᵥ* D = 0 := by
        have := y.2
        rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose] at this
      have h3 : (y : Fin n → k) ᵥ* C = 0 := by simpa [Matrix.mulVec_transpose] using hy
      exact Subtype.ext (h _ h3 h2)
    · intro h y hC hD'
      have hy : y ∈ LinearMap.ker Dᵀ.mulVecLin := by
        rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose]
      have := h ⟨y, hy⟩ (by simpa [Matrix.mulVec_transpose] using hC)
      simpa using congrArg Subtype.val this
  rw [Nat.card_congr ((Equiv.subtypeEquiv (q := fun x => LinearIndependent k x.1) E hp).trans
      (Equiv.prodSubtypeFstEquivSubtypeProd (p := fun s : Fin (n - ρ) → Fin n → k => LinearIndependent k s))), Nat.card_prod,
    card_linearIndependent (K := k) (V := Fin n → k) (by rw [Module.finrank_fin_fun]; omega), Module.finrank_fin_fun,
    Finset.prod_range (fun j => Fintype.card k ^ n - Fintype.card k ^ j), mul_comm]
  congr 1
  simp [Nat.card_fun, pow_mul]

end GlobalTheory.CompanionTheory.Jp.CntCols
end

section

open Matrix

theorem _root_.GlobalTheory.T.card_coset_reps_eq_relIndex : ∀ (X : Type) [AddCommGroup X] (A L : AddSubgroup X) (T : Finset X), L ≤ A → (∀ t ∈ T, t ∈ A) → (∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ L) → T.card = L.relIndex A := by
  first | exact @GlobalTheory.CompanionTheory.Transversal.card_eq_relIndex | exact GlobalTheory.CompanionTheory.Transversal.card_eq_relIndex | (intros; apply GlobalTheory.CompanionTheory.Transversal.card_eq_relIndex <;> assumption)
end

section

open Matrix
open scoped Topology

theorem _root_.GlobalTheory.T.haar_measure_subgroup_relIndex_mul : ∀ (G : Type) [AddGroup G] [MeasurableSpace G] [MeasurableAdd G] (μ : MeasureTheory.Measure G) [μ.IsAddLeftInvariant] (H K : AddSubgroup G), H ≤ K → MeasurableSet (H : Set G) → H.relIndex K ≠ 0 → μ (K : Set G) = (H.relIndex K : ENNReal) * μ (H : Set G) := by
  first | exact @GlobalTheory.CompanionTheory.HaarIndex.measure_eq_relIndex_mul | exact GlobalTheory.CompanionTheory.HaarIndex.measure_eq_relIndex_mul | (intros; apply GlobalTheory.CompanionTheory.HaarIndex.measure_eq_relIndex_mul <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.relIndex_open_compact_ne_zero : ∀ {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] (A H : AddSubgroup X), IsCompact (A : Set X) → IsOpen (H : Set X) → H ≤ A → H.relIndex A ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.RelIndex.relIndex_ne_zero_of_isCompact_of_isOpen | exact GlobalTheory.CompanionTheory.RelIndex.relIndex_ne_zero_of_isCompact_of_isOpen | (intros; apply GlobalTheory.CompanionTheory.RelIndex.relIndex_ne_zero_of_isCompact_of_isOpen <;> assumption)
end

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.Dblock.AmiBc

theorem leftComm_lTensor_natural {A B C M N : Type} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup C] [Module A C] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (d : M →ₗ[A] N) (c : C) (w : B ⊗[A] M) :
    (d.lTensor C).lTensor B (TensorProduct.leftComm A C B M (c ⊗ₜ[A] w)) =
      TensorProduct.leftComm A C B N (c ⊗ₜ[A] (d.lTensor B w)) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul b m => simp [TensorProduct.leftComm_tmul]
  | add x y hx hy =>
    simp only [TensorProduct.tmul_add, map_add (f := _), hx, hy]

theorem contraction_lTensor :
    ∀ (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (C : Type) [AddCommGroup C] [Module A C] (K : ℕ → Type) [∀ n, AddCommGroup (K n)] [∀ n, Module A (K n)] (d : ∀ n, K n →ₗ[A] K (n + 1)) (H : ∀ n, K (n + 1) →ₗ[A] B ⊗[A] K n), ((∀ z, H 0 (d 0 z) = (1 : B) ⊗ₜ[A] z) ∧ ∀ n z, (d n).lTensor B (H n z) + H (n + 1) (d (n + 1) z) = (1 : B) ⊗ₜ[A] z) → ∃ H₁ : ∀ n, C ⊗[A] K (n + 1) →ₗ[A] B ⊗[A] (C ⊗[A] K n), (∀ z, H₁ 0 ((d 0).lTensor C z) = (1 : B) ⊗ₜ[A] z) ∧ ∀ n z, ((d n).lTensor C).lTensor B (H₁ n z) + H₁ (n + 1) ((d (n + 1)).lTensor C z) = (1 : B) ⊗ₜ[A] z := by
  intro A _ B _ _ C _ _ K _ _ d H ⟨h0, hS⟩
  refine ⟨fun n => (TensorProduct.leftComm A C B (K n)).toLinearMap ∘ₗ (H n).lTensor C, ?_, ?_⟩
  · intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul c k =>
      simp [h0, TensorProduct.leftComm_tmul]
    | add x y hx hy =>
      simp only [map_add (f := _), hx, hy, TensorProduct.tmul_add]
  · intro n z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul c k =>
      have key := congrArg (fun t => TensorProduct.leftComm A C B (K (n + 1)) (c ⊗ₜ[A] t)) (hS n k)
      simp only [TensorProduct.tmul_add, map_add (f := _)] at key
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.lTensor_tmul]
      rw [leftComm_lTensor_natural, key, TensorProduct.leftComm_tmul]
    | add x y hx hy =>
      simp only [map_add (f := _), TensorProduct.tmul_add]
      rw [← hx, ← hy]
      abel

end GlobalTheory.CompanionTheory.Dblock.AmiBc
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.tensor_ideal_map_injective : ∀ (O O' R : Type) [CommRing O] [CommRing O'] [Nontrivial O'] [Algebra O O'] [Module.Free O O'] [CommRing R] [Algebra O R] (I : Ideal R) (x : R), (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) x ∈ Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) I → x ∈ I := by
  first | exact @GlobalTheory.CompanionTheory.Descent.mem_of_includeRight_mem_map | exact GlobalTheory.CompanionTheory.Descent.mem_of_includeRight_mem_map | (intros; apply GlobalTheory.CompanionTheory.Descent.mem_of_includeRight_mem_map <;> assumption)
end

section

open Matrix
open scoped Topology

theorem _root_.GlobalTheory.T.exists_GL_last_basis_vecMul_eq : ∀ (k : Type) [Field k] (m : ℕ) (ξ : Fin (m + 1) → k), ξ ≠ 0 → ∃ h : GL (Fin (m + 1)) k, (Pi.single (Fin.last m) 1 : Fin (m + 1) → k) ᵥ* (h : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = ξ := by
  first | exact @GlobalTheory.CompanionTheory.RowSect.exists_GL_last_row | exact GlobalTheory.CompanionTheory.RowSect.exists_GL_last_row | (intros; apply GlobalTheory.CompanionTheory.RowSect.exists_GL_last_row <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.exists_GL_vecMul_eq_last_basis : ∀ {k : Type} [Field k] (n : ℕ) (ξ : Fin (n + 1) → k), ξ ≠ 0 → ∃ g : GL (Fin (n + 1)) k, Matrix.vecMul ξ (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = Pi.single (Fin.last n) 1 := by
  first | exact @GlobalTheory.CompanionTheory.Matrixlemmas.exists_GL_vecMul_eq_single_last | exact GlobalTheory.CompanionTheory.Matrixlemmas.exists_GL_vecMul_eq_single_last | (intros; apply GlobalTheory.CompanionTheory.Matrixlemmas.exists_GL_vecMul_eq_single_last <;> assumption)
end

section

open Matrix GlobalTheory.CompanionTheory.Jp

namespace GlobalTheory.CompanionTheory.Jp.CountRank

open Module

variable {k : Type} [Field k] [Fintype k]

theorem card_injective {U V : Type} [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
    [FiniteDimensional k U] [FiniteDimensional k V] {e n : ℕ}
    (hU : finrank k U = e) (hV : finrank k V = n) (he : e ≤ n) :
    Nat.card {g : U →ₗ[k] V // Function.Injective g} =
      ∏ j ∈ Finset.range e, (Fintype.card k ^ n - Fintype.card k ^ j) := by
  classical
  have : Finite V := Module.finite_of_finite k
  let b : Module.Basis (Fin e) k U := Module.finBasisOfFinrankEq k U hU
  have key : ∀ g : U →ₗ[k] V, Function.Injective g ↔ LinearIndependent k (g ∘ b) := by
    intro g
    constructor
    · intro hg
      exact b.linearIndependent.map' g (LinearMap.ker_eq_bot.mpr hg)
    · intro hli
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro x hx
      rw [LinearMap.mem_ker] at hx
      have hsum : ∑ i, (b.repr x i) • (g ∘ b) i = 0 := by
        have h0 : g (∑ i, (b.repr x i) • b i) = 0 := by rw [b.sum_repr]; exact hx

        rw [map_sum] at h0
        simpa only [Function.comp_apply, map_smul] using h0
      have hc := Fintype.linearIndependent_iff.mp hli _ hsum
      apply b.repr.injective
      ext i
      simp [hc i]
  have E : {g : U →ₗ[k] V // Function.Injective g} ≃ {s : Fin e → V // LinearIndependent k s} :=
    { toFun := fun g => ⟨g.1 ∘ b, (key g.1).mp g.2⟩
      invFun := fun s => ⟨b.constr k s.1, (key _).mpr (by
          have hs : (b.constr k s.1 : U → V) ∘ b = s.1 := by
            funext i
            simp
          rw [hs]
          exact s.2)⟩
      left_inv := fun g => Subtype.ext (b.ext fun i => by simp)
      right_inv := fun s => Subtype.ext (funext fun i => by simp) }
  rw [Nat.card_congr E, card_linearIndependent (K := k) (V := V) (k := e) (by omega), hV,
    Finset.prod_range (fun j => Fintype.card k ^ n - Fintype.card k ^ j)]

theorem card_ker_eq {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {n ρ : ℕ} (hV : finrank k V = n) (hρ : ρ ≤ n) (K : Submodule k V)
    (hK : finrank k K = n - ρ) :
    Nat.card {f : V →ₗ[k] V // LinearMap.ker f = K} =
      ∏ j ∈ Finset.range ρ, (Fintype.card k ^ n - Fintype.card k ^ j) := by
  classical
  have hQ : finrank k (V ⧸ K) = ρ := by
    have := Submodule.finrank_quotient_add_finrank K
    omega
  have E : {f : V →ₗ[k] V // LinearMap.ker f = K} ≃
      {g : (V ⧸ K) →ₗ[k] V // Function.Injective g} :=
    { toFun := fun f => ⟨K.liftQ f.1 (le_of_eq f.2.symm),
        LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ (le_of_eq f.2))⟩
      invFun := fun g => ⟨g.1.comp K.mkQ, by
        rw [LinearMap.ker_comp, LinearMap.ker_eq_bot.mpr g.2, Submodule.comap_bot,
          Submodule.ker_mkQ]⟩
      left_inv := fun f => Subtype.ext (Submodule.liftQ_mkQ K f.1 _)
      right_inv := fun g => Subtype.ext (Submodule.linearMap_qext K (Submodule.liftQ_mkQ K _ _)) }
  rw [Nat.card_congr E]
  exact card_injective hQ hV (by omega)

theorem card_rank_eq {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {n ρ : ℕ} (hV : finrank k V = n) (hρ : ρ ≤ n) :
    Nat.card {f : V →ₗ[k] V // finrank k (LinearMap.range f) = ρ} =
      Nat.card {K : Submodule k V // finrank k K = n - ρ} *
        ∏ j ∈ Finset.range ρ, (Fintype.card k ^ n - Fintype.card k ^ j) := by
  classical
  have : Finite V := Module.finite_of_finite k
  have : Finite (V →ₗ[k] V) := Module.finite_of_finite k
  have : Finite (Submodule k V) :=
    Finite.of_injective (fun K : Submodule k V => (K : Set V)) SetLike.coe_injective
  letI : Fintype {K : Submodule k V // finrank k K = n - ρ} := Fintype.ofFinite _
  have E : {f : V →ₗ[k] V // finrank k (LinearMap.range f) = ρ} ≃
      Σ K : {K : Submodule k V // finrank k K = n - ρ},
        {f : V →ₗ[k] V // LinearMap.ker f = K.1} :=
    { toFun := fun f => ⟨⟨LinearMap.ker f.1, by
          have h1 := LinearMap.finrank_range_add_finrank_ker f.1
          have h2 := f.2
          omega⟩, ⟨f.1, rfl⟩⟩
      invFun := fun p => ⟨p.2.1, by
          have h1 := LinearMap.finrank_range_add_finrank_ker p.2.1
          have h2 := p.1.2
          have h3 := p.2.2
          rw [h3] at h1
          omega⟩
      left_inv := fun f => rfl
      right_inv := by
        rintro ⟨⟨K, hK⟩, ⟨f, hf⟩⟩
        dsimp only at hf
        subst hf
        rfl }
  rw [Nat.card_congr E, Nat.card_sigma,
    Finset.sum_congr rfl (fun a _ => card_ker_eq hV hρ a.1 a.2), Finset.sum_const,
    Finset.card_univ, smul_eq_mul,
    Nat.card_eq_fintype_card (α := {K : Submodule k V // finrank k K = n - ρ})]

theorem card_sub_le {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {n : ℕ} (hV : finrank k V = n) (d : ℕ) (hd : d ≤ n) :
    Nat.card {K : Submodule k V // finrank k K = d} ≤
      Nat.card {K : Submodule k V // finrank k K = n - d} := by
  classical
  have : Finite V := Module.finite_of_finite k
  have : Finite (Submodule k V) :=
    Finite.of_injective (fun K : Submodule k V => (K : Set V)) SetLike.coe_injective
  let eV : Module.Dual k V ≃ₗ[k] V := ((Module.finBasis k V).toDualEquiv).symm
  have hDual : ∀ K : Submodule k V,
      finrank k (K.dualAnnihilator) = finrank k V - finrank k K := by
    intro K
    have := Subspace.finrank_add_finrank_dualAnnihilator_eq K
    omega
  let F : {K : Submodule k V // finrank k K = d} → {K : Submodule k V // finrank k K = n - d} :=
    fun K => ⟨(K.1.dualAnnihilator).map (eV : Module.Dual k V →ₗ[k] V), by
      rw [LinearEquiv.finrank_map_eq, hDual, hV, K.2]⟩
  apply Nat.card_le_card_of_injective F
  intro K₁ K₂ h
  apply Subtype.ext
  have h1 : (K₁.1.dualAnnihilator).map (eV : Module.Dual k V →ₗ[k] V) =
      (K₂.1.dualAnnihilator).map (eV : Module.Dual k V →ₗ[k] V) := congrArg Subtype.val h
  have h2 := Submodule.map_injective_of_injective eV.injective h1
  exact Subspace.dualAnnihilator_inj.mp h2

theorem card_sub_symm {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {n : ℕ} (hV : finrank k V = n) (d : ℕ) (hd : d ≤ n) :
    Nat.card {K : Submodule k V // finrank k K = d} =
      Nat.card {K : Submodule k V // finrank k K = n - d} := by
  apply le_antisymm (card_sub_le hV d hd)
  have := card_sub_le hV (n - d) (Nat.sub_le n d)
  rwa [Nat.sub_sub_self hd] at this

theorem card_matrix_rank (n ρ : ℕ) :
    Nat.card {D : Matrix (Fin n) (Fin n) k // D.rank = ρ} =
      Nat.card {f : (Fin n → k) →ₗ[k] (Fin n → k) // finrank k (LinearMap.range f) = ρ} := by
  apply Nat.card_congr
  exact Equiv.subtypeEquiv
    (Matrix.toLin' : Matrix (Fin n) (Fin n) k ≃ₗ[k] ((Fin n → k) →ₗ[k] (Fin n → k))).toEquiv
    (fun D => by
      show D.rank = ρ ↔ finrank k (LinearMap.range (Matrix.toLin' D)) = ρ
      rw [Matrix.toLin'_apply', Matrix.finrank_range_mulVecLin])

theorem rank_symm (k : Type) [Field k] [Fintype k] (n ρ : ℕ) (h : ρ ≤ n) :
    Nat.card {D : Matrix (Fin n) (Fin n) k // D.rank = ρ} *
        ∏ j ∈ Finset.range (n - ρ), (Fintype.card k ^ n - Fintype.card k ^ j) =
      Nat.card {D : Matrix (Fin n) (Fin n) k // D.rank = n - ρ} *
        ∏ j ∈ Finset.range ρ, (Fintype.card k ^ n - Fintype.card k ^ j) := by
  have hV : finrank k (Fin n → k) = n := Module.finrank_fin_fun k
  rw [card_matrix_rank, card_matrix_rank, card_rank_eq hV h, card_rank_eq hV (Nat.sub_le n ρ),
    Nat.sub_sub_self h, card_sub_symm hV ρ h]
  ring

end GlobalTheory.CompanionTheory.Jp.CountRank
end

section

namespace GlobalTheory.CompanionTheory.Jp

theorem rank_residue_map_le_rank_fraction_map :
    ∀ (O L : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Field L] [Algebra O L]
      [IsFractionRing O L] (n : ℕ) (T : Matrix (Fin n) (Fin n) O),
      (T.map (IsLocalRing.residue O)).rank ≤ (T.map (algebraMap O L)).rank := by
  intro O L _ _ _ _ _ _ n T
  obtain ⟨S, τ, hdet⟩ := GlobalTheory.exists_submatrix_det_ne_zero_of_le_rank (IsLocalRing.ResidueField O)
    (Fin n) (Fin n) _ (T.map (IsLocalRing.residue O)) le_rfl
  have hres : IsLocalRing.residue O (T.submatrix S τ).det =
      ((T.map (IsLocalRing.residue O)).submatrix S τ).det := by
    rw [RingHom.map_det]
    rfl
  have hfrac : algebraMap O L (T.submatrix S τ).det =
      ((T.map (algebraMap O L)).submatrix S τ).det := by
    rw [RingHom.map_det]
    rfl
  have hO : (T.submatrix S τ).det ≠ 0 := by
    intro h
    apply hdet
    rw [← hres, h, map_zero]
  have hL : ((T.map (algebraMap O L)).submatrix S τ).det ≠ 0 := by
    rw [← hfrac]
    intro h
    exact hO (IsFractionRing.injective O L (h.trans (map_zero _).symm))
  calc (T.map (IsLocalRing.residue O)).rank
      = ((T.map (algebraMap O L)).submatrix S τ).rank := by
        rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hL)),
          Fintype.card_fin]
    _ ≤ (T.map (algebraMap O L)).rank := Matrix.rank_submatrix_le _ _ _

end GlobalTheory.CompanionTheory.Jp
end

section


theorem _root_.GlobalTheory.T.not_mem_Lp_of_growth : ∀ {X : Type} [MeasurableSpace X] (μ : MeasureTheory.Measure X) (f : X → ℝ) (p : ℝ), 0 < p → MeasureTheory.MemLp f (ENNReal.ofReal p) μ → ∀ (E : ℕ → Set X), (∀ j, MeasurableSet (E j)) → Pairwise (Function.onFun Disjoint E) → ∀ (c D B r : ℝ), 0 < c → 0 < B → 0 ≤ r → (∀ j : ℕ, ENNReal.ofReal (c * D ^ j) ≤ μ (E j)) → (∀ j : ℕ, ∀ x ∈ E j, B * r ^ j ≤ |f x|) → D * r ^ p < 1 := by
  first | exact @GlobalTheory.CompanionTheory.Casselman.mul_rpow_lt_one_of_memLp_geometric | exact GlobalTheory.CompanionTheory.Casselman.mul_rpow_lt_one_of_memLp_geometric | (intros; apply GlobalTheory.CompanionTheory.Casselman.mul_rpow_lt_one_of_memLp_geometric <;> assumption)
end

section

open MeasureTheory Topology
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.quotient_measure_by_invariant_subgroup : ∀ (V A : Type) [AddCommGroup V] [AddCommGroup A] [MeasurableSpace V] [MeasurableSpace A] [MeasurableAdd₂ V] [MeasurableAdd₂ A] [MeasurableNeg A] [MeasurableNeg V] (μ : Measure V) (lam : Measure A) [SFinite μ] [SFinite lam] [μ.IsAddRightInvariant] [lam.IsAddRightInvariant] (j : A →+ V), Measurable j → ∀ f : V → A, Measurable f → (∀ v a, f (v + j a) = f v) → ∀ K : Set A, MeasurableSet K → lam K ≠ 0 → lam K ≠ ⊤ → ∀ ψ : V → ℝ≥0∞, Measurable ψ → ∫⁻ v, ψ (v + j (f v)) ∂μ = ∫⁻ v, ψ v ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.Shear.lintegral_shear_eq | exact GlobalTheory.CompanionTheory.Shear.lintegral_shear_eq | (intros; apply GlobalTheory.CompanionTheory.Shear.lintegral_shear_eq <;> assumption)
end
