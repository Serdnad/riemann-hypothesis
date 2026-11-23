module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
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
public import Mathlib.LinearAlgebra.Matrix.Rank
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

section

noncomputable def UpperTheory.Reformulated.B.CharpolyPowersRatios.FreeRatios :
    {κ ι : Type} → [inst : Field κ] → (ι → κˣ) → Prop :=
    fun {κ ι : Type} [Field κ] (α : ι → κˣ) ↦ ∀ (i j : ι), i ≠ j → ∀ (m : ℕ), (0 : ℕ) < m → α i ^ m ≠ α j ^ m

theorem UpperTheory.Reformulated.B.CharpolyPowersRatios.charpoly_pow :
    ∀ {K : Type} [inst : Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (a : Fin n → Kˣ),
      M.charpoly = ∏ i : Fin n, (Polynomial.X - (Polynomial.C : K → Polynomial K) (↑(a i) : K)) →
        UpperTheory.Reformulated.B.CharpolyPowersRatios.FreeRatios a →
          ∀ (d : ℕ),
            (0 : ℕ) < d →
              (M ^ d).charpoly = ∏ i : Fin n, (Polynomial.X - (Polynomial.C : K → Polynomial K) ((↑(a i) : K) ^ d)) := by
  intro K _ n M a hM hfree d _
  have hinj : Function.Injective (fun i => (a i : K)) := by
    intro i j hij
    by_contra hne
    exact hfree i j hne 1 one_pos (by simpa using Units.ext hij)
  have hev : ∀ i, Module.End.HasEigenvalue (Matrix.toLin' M) (a i : K) := by
    intro i
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', hM,
      Polynomial.IsRoot.def, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  choose v hv using fun i => (hev i).exists_hasEigenvector
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' _ (fun i => (a i : K)) hinj v hv
  let b : Module.Basis (Fin n) K (Fin n → K) :=
    basisOfLinearIndependentOfCardEqFinrank' v hli (by simp)
  have hb : ⇑b = v := coe_basisOfLinearIndependentOfCardEqFinrank' v hli _
  have hpow : ∀ j, Matrix.toLin' (M ^ d) (v j) = ((a j : K) ^ d) • v j := by
    intro j
    rw [Matrix.toLin'_pow]
    exact (hv j).pow_apply d
  have hmat : LinearMap.toMatrix b b (Matrix.toLin' (M ^ d)) =
      Matrix.diagonal (fun i => (a i : K) ^ d) := by
    ext i j
    rw [LinearMap.toMatrix_apply, hb, hpow, map_smul, ← hb]
    simp only [Module.Basis.repr_self, Matrix.diagonal_apply, Finsupp.smul_single, Finsupp.single_apply, smul_eq_mul, mul_one]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [← Matrix.charpoly_toLin', ← LinearMap.charpoly_toMatrix _ b, hmat, Matrix.charpoly_diagonal]
end

section

theorem UpperTheory.Reformulated.B.Qh2.diagz :
    ∀ {K : Type} [inst : Field K]
    (M : Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) K) (a : Fin (4 : ℕ) → K),
    Function.Injective a →
      M.charpoly = ∏ i : Fin (4 : ℕ), (Polynomial.X - (Polynomial.C : K → Polynomial K) (a i)) →
        ∃ (P : Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) K) (Q : Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) K),
          P * Q = (1 : Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) K) ∧
            Q * P = (1 : Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) K) ∧ Q * M * P = Matrix.diagonal a := by
  intro K _ M a ha hM
  have hev : ∀ i, Module.End.HasEigenvalue (Matrix.toLin' M) (a i) := by
    intro i
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', hM,
      Polynomial.IsRoot.def, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  choose v hv using fun i => (hev i).exists_hasEigenvector
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' M) a ha v hv
  let P : Matrix (Fin 4) (Fin 4) K := Matrix.of fun r c => v c r
  have hP : IsUnit P := Matrix.linearIndependent_cols_iff_isUnit.mp hli
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hMP : M * P = P * Matrix.diagonal a := by
    ext r c
    have h := congrFun (hv c).apply_eq_smul r
    rw [Matrix.toLin'_apply] at h
    rw [Matrix.mul_diagonal, mul_comm]
    exact h
  refine ⟨P, P⁻¹, Matrix.mul_nonsing_inv P hdet, Matrix.nonsing_inv_mul P hdet, ?_⟩
  rw [Matrix.mul_assoc, hMP, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul P hdet, Matrix.one_mul]
end

section

namespace UpperTheory.Reformulated.B.OrderedFlagDiagonal
abbrev M4 (R : Type) : Type := Matrix (Fin 4) (Fin 4) R

variable {K : Type} [Field K]

theorem ordFlag_diag (c : Fin 4 → K) (hc : Function.Injective c) (X : M4 K)
    (hX : X.charpoly = ∏ j, (Polynomial.X - Polynomial.C (c j))) :
    ∃ P : (M4 K)ˣ, X * (P : M4 K) = (P : M4 K) * Matrix.diagonal c := by
  have hev : ∀ j, Module.End.HasEigenvalue (Matrix.toLin' X) (c j) := by
    intro j
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', hX,
      Polynomial.IsRoot, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp)
  choose v hv using fun j => (hev j).exists_hasEigenvector
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' X) c hc v hv
  have hU : IsUnit (Matrix.of fun i j => v j i : Matrix (Fin 4) (Fin 4) K) :=
    Matrix.linearIndependent_cols_iff_isUnit.mp hli
  obtain ⟨P, hP⟩ := hU
  refine ⟨P, ?_⟩
  rw [hP]
  ext i j
  have h := congrFun (hv j).apply_eq_smul i
  rw [Matrix.toLin'_apply] at h
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  simpa [Matrix.mulVec, dotProduct, mul_comm] using h

end UpperTheory.Reformulated.B.OrderedFlagDiagonal
end

section

theorem UpperTheory.Reformulated.B.DiagonalizationExistence.exists_diag :
    ∀ {κ : Type} [inst : Field κ] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) κ) (a : Fin n → κ),
    Function.Injective a →
      M.charpoly = ∏ i : Fin n, (Polynomial.X - (Polynomial.C : κ → Polynomial κ) (a i)) →
        ∃ (P : GL (Fin n) κ),
          M * (↑P : Matrix (Fin n) (Fin n) κ) = (↑P : Matrix (Fin n) (Fin n) κ) * Matrix.diagonal a := by
  intro κ _ n M a ha hM
  have hev : ∀ i, Module.End.HasEigenvalue (Matrix.toLin' M) (a i) := by
    intro i
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', hM,
      Polynomial.IsRoot.def, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  choose v hv using fun i => (hev i).exists_hasEigenvector
  have hli : LinearIndependent κ v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' M) a ha v hv
  have hU : IsUnit (Matrix.of fun r c => v c r : Matrix (Fin n) (Fin n) κ) :=
    Matrix.linearIndependent_cols_iff_isUnit.mp hli
  obtain ⟨P, hP⟩ := hU
  refine ⟨P, ?_⟩
  rw [hP]
  ext r c
  have h := congrFun (hv c).apply_eq_smul r
  rw [Matrix.toLin'_apply] at h
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  simpa [Matrix.mulVec, dotProduct, mul_comm] using h
end

section

theorem UpperTheory.Reformulated.B.DiagonalizeThreeByThree.diagonalize_three_by_three_split :
    ∀ {K : Type} [inst : Field K] (d : Fin (3 : ℕ) → K),
    Function.Injective d →
      ∀ (M : Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) K),
        M.charpoly = ∏ a : Fin (3 : ℕ), (Polynomial.X - (Polynomial.C : K → Polynomial K) (d a)) →
          ∃ (h : GL (Fin (3 : ℕ)) K),
            (↑h⁻¹ : Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) K) * M * (↑h : Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) K) =
              Matrix.diagonal d := by
  intro K _ d hd M hM
  have hev : ∀ a, Module.End.HasEigenvalue (Matrix.toLin' M) (d a) := by
    intro a
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', hM,
      Polynomial.IsRoot.def, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp)
  choose v hv using fun a => (hev a).exists_hasEigenvector
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' M) d hd v hv
  let P : Matrix (Fin 3) (Fin 3) K := Matrix.of fun i j => v j i
  have hP : IsUnit P := Matrix.linearIndependent_cols_iff_isUnit.mp hli
  have hMP : M * P = P * Matrix.diagonal d := by
    ext i j
    have h := congrFun (hv j).apply_eq_smul i
    rw [Matrix.toLin'_apply] at h
    rw [Matrix.mul_diagonal, mul_comm]
    exact h
  obtain ⟨u, hu⟩ := hP
  refine ⟨u, ?_⟩
  rw [Matrix.mul_assoc, hu, hMP, ← hu, ← Matrix.mul_assoc]
  rw [Units.inv_mul, Matrix.one_mul]
end

section

theorem UpperTheory.Reformulated.B.DetMulExpand.det_mul_expand :
    ∀ {F : Type} [inst : CommRing F] {k r : ℕ} (A : Matrix (Fin k) (Fin r) F) (B : Matrix (Fin r) (Fin k) F),
      (A * B).det = ∑ f : Fin k → Fin r, (∏ a : Fin k, A a (f a)) * (B.submatrix f id).det := by
  intro F _ k r A B
  have h1 : (A * B) = (fun a => ∑ j, (A a j • B j : Fin k → F)) := by
    ext a c
    simp [Matrix.mul_apply, Finset.sum_apply]
  have h2 : (A * B).det
      = (Matrix.detRowAlternating (R := F) (n := Fin k)).toMultilinearMap
          (fun a => ∑ j, (A a j • B j : Fin k → F)) := by
    rw [← h1]
    rfl

  rw [h2, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [MultilinearMap.map_smul_univ]
  rfl
end

section

theorem UpperTheory.Reformulated.B.Yoa2.mul_left_cancel_of_det_ne_zero.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] [IsDomain R] {n : ℕ} {A X Y : Matrix (Fin n) (Fin n) R},
      A.det ≠ (0 : R) → A * X = A * Y → X = Y := by
  intro R _ _ n A X Y hA h
  have h2 : A.det • X = A.det • Y := by
    have h3 : A.adjugate * (A * X) = A.adjugate * (A * Y) := by rw [h]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.one_mul, Matrix.one_mul] at h3
    exact h3
  ext i j
  have h4 : A.det * X i j = A.det * Y i j := congrFun (congrFun h2 i) j
  exact mul_left_cancel₀ hA h4
end

section

noncomputable def UpperTheory.Reformulated.B.Qm12.vandermondeOf.{u_1} :
    {R : Type u_1} → [CommRing R] → {m : ℕ} → (Fin m → R) → R :=
    fun {R : Type u_1} [CommRing R] {m : ℕ} (v : Fin m → R) ↦ ∏ i : Fin m, ∏ j > i, (v i - v j)

theorem UpperTheory.Reformulated.B.Qm12.vandermondeOf_eq_det.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (v : Fin m → R),
      UpperTheory.Reformulated.B.Qm12.vandermondeOf v =
        ((Matrix.of : (Fin m → Fin m → R) → Matrix (Fin m) (Fin m) R) fun (i j : Fin m) ↦
            v i ^ (m - (1 : ℕ) - (↑j : ℕ))).det := by
  intro m R _ v
  have hM : ((Matrix.of : (Fin m → Fin m → R) → Matrix (Fin m) (Fin m) R) fun (i j : Fin m) ↦
      v i ^ (m - (1 : ℕ) - (↑j : ℕ))) = Matrix.projVandermonde (fun _ ↦ (1 : R)) v := by
    ext i j
    rw [Matrix.of_apply, Matrix.projVandermonde_apply, one_pow, one_mul, Fin.val_rev,
      Nat.sub_sub, Nat.add_comm]
  rw [hM, Matrix.det_projVandermonde]
  unfold UpperTheory.Reformulated.B.Qm12.vandermondeOf
  refine Finset.prod_congr rfl fun i _ ↦ Finset.prod_congr ?_ fun j _ ↦ ?_
  · ext j
    simp
  · rw [one_mul, one_mul]
end

section

theorem UpperTheory.Reformulated.B.Yra1.main.{u_1} :
    ∀ {F : Type u_1} [inst : Field F] {r a : ℕ} (M : Matrix (Fin r) (Fin a) F),
      (∀ (z : Fin a → F), M.mulVec z = (0 : Fin r → F) → z = (0 : Fin a → F)) →
        ∃ (e : Fin a → Fin r), (M.submatrix e id).det ≠ (0 : F) := by
  intro F _ r a M hM
  have hinj : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_eq_bot_iff]
    exact hM
  have hrank : M.rank = a := by
    rw [← Matrix.finrank_range_mulVecLin, LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]
  obtain ⟨κ, f, hf, hsp, hli⟩ := exists_linearIndependent' F M.row
  haveI : Finite κ := Finite.of_injective f hf
  letI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = a := by
    rw [← finrank_span_eq_card hli, hsp, ← Matrix.rank_eq_finrank_span_row, hrank]
  let eqv : κ ≃ Fin a := Fintype.equivFinOfCardEq hcard
  refine ⟨f ∘ eqv.symm, ?_⟩
  have hli2 : LinearIndependent F (M.submatrix (f ∘ eqv.symm) id).row := by
    have := hli.comp eqv.symm eqv.symm.injective
    have h : (M.submatrix (f ∘ eqv.symm) id).row = (M.row ∘ f) ∘ eqv.symm := by
      ext i j; rfl
    rw [h]; exact this
  have hu := Matrix.linearIndependent_rows_iff_isUnit.mp hli2
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
end

section

private theorem UpperTheory.Reformulated.B.IntertwinerDiagonalization.of_intertwine {K : Type} [Field K]
    (M : GL (Fin 2) K) (D P : Matrix (Fin 2) (Fin 2) K) (hP : P.det ≠ 0)
    (h : (↑M : Matrix (Fin 2) (Fin 2) K) * P = P * D) :
    ∃ (g : GL (Fin 2) K), (↑(g * M * g⁻¹) : Matrix (Fin 2) (Fin 2) K) = D := by
  let u : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero P hP
  have hu : (↑u : Matrix (Fin 2) (Fin 2) K) = P := rfl
  refine ⟨u⁻¹, ?_⟩
  rw [inv_inv, Units.val_mul, Units.val_mul, mul_assoc, hu, h, ← hu, ← mul_assoc,
    Units.inv_mul, one_mul]

theorem UpperTheory.Reformulated.B.IntertwinerDiagonalization.exists_diag :
    ∀ {K : Type} [inst : Field K]
    (M : GL (Fin (2 : ℕ)) K) {x : K},
    x ≠ (1 : K) →
      (↑M : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) K).trace = (1 : K) + x →
        (↑M : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) K).det = x →
          ∃ (g : GL (Fin (2 : ℕ)) K),
            (↑(g * M * g⁻¹) : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) K) = Matrix.diagonal ![(1 : K), x] := by
  intro K _ M x hx ht hd
  have hx' : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  rw [Matrix.trace_fin_two] at ht
  rw [Matrix.det_fin_two] at hd
  obtain ⟨a, b, c, d, hM⟩ : ∃ a b c d : K, (↑M : Matrix (Fin 2) (Fin 2) K) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hD : (Matrix.diagonal ![(1 : K), x] : Matrix (Fin 2) (Fin 2) K) = !![1, 0; 0, x] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hM] at ht hd
  have ht' : a + d = 1 + x := by simpa using ht
  have hd' : a * d - b * c = x := by simpa using hd
  by_cases hc : c = 0
  · by_cases hb : b = 0
    · have hq : (a - 1) * (a - x) = 0 := by
        rw [hb] at hd'
        linear_combination a * ht' - hd'
      rcases mul_eq_zero.mp hq with h | h
      · have ha : a = 1 := sub_eq_zero.mp h
        have hdx : d = x := by linear_combination ht' - ha
        refine UpperTheory.Reformulated.B.IntertwinerDiagonalization.of_intertwine M _ 1 (by simp) ?_
        rw [hM, hD, ha, hb, hc, hdx, mul_one, one_mul]
      · have ha : a = x := sub_eq_zero.mp h
        have hdx : d = 1 := by linear_combination ht' - ha
        refine UpperTheory.Reformulated.B.IntertwinerDiagonalization.of_intertwine M _ !![0, 1; 1, 0] (by simp) ?_
        rw [hM, hD, ha, hb, hc, hdx, Matrix.mul_fin_two, Matrix.mul_fin_two]
        simp
    · refine UpperTheory.Reformulated.B.IntertwinerDiagonalization.of_intertwine M _ !![b, b; 1 - a, x - a] ?_ ?_
      · have : (!![b, b; 1 - a, x - a] : Matrix (Fin 2) (Fin 2) K).det = b * (x - 1) := by
          rw [Matrix.det_fin_two_of]; ring
        rw [this]
        exact mul_ne_zero hb hx'
      · rw [hM, hD, Matrix.mul_fin_two, Matrix.mul_fin_two]
        have e1 : a * b + b * (1 - a) = b * 1 + b * 0 := by ring
        have e2 : a * b + b * (x - a) = b * 0 + b * x := by ring
        have e3 : c * b + d * (1 - a) = (1 - a) * 1 + (x - a) * 0 := by
          linear_combination ht' - hd'
        have e4 : c * b + d * (x - a) = (1 - a) * 0 + (x - a) * x := by
          linear_combination x * ht' - hd'
        rw [e1, e2, e3, e4]
  · refine UpperTheory.Reformulated.B.IntertwinerDiagonalization.of_intertwine M _ !![1 - d, x - d; c, c] ?_ ?_
    · have : (!![1 - d, x - d; c, c] : Matrix (Fin 2) (Fin 2) K).det = -(c * (x - 1)) := by
        rw [Matrix.det_fin_two_of]; ring
      rw [this]
      exact neg_ne_zero.mpr (mul_ne_zero hc hx')
    · rw [hM, hD, Matrix.mul_fin_two, Matrix.mul_fin_two]
      have e1 : a * (1 - d) + b * c = (1 - d) * 1 + (x - d) * 0 := by
        linear_combination ht' - hd'
      have e2 : a * (x - d) + b * c = (1 - d) * 0 + (x - d) * x := by
        linear_combination x * ht' - hd'
      have e3 : c * (1 - d) + d * c = c * 1 + c * 0 := by ring
      have e4 : c * (x - d) + d * c = c * 0 + c * x := by ring
      rw [e1, e2, e3, e4]
end

section

noncomputable def UpperTheory.Reformulated.B.IrreducibleInvariant.IsInv :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      ∀ (g : Γ), ∀ v ∈ W, (↑((ρ : Γ → GL (Fin a) k) g) : Matrix (Fin a) (Fin a) k).mulVec v ∈ W

noncomputable def UpperTheory.Reformulated.B.IrreducibleInvariant.IsIrrSub :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      W ≠ ⊥ ∧ UpperTheory.Reformulated.B.IrreducibleInvariant.IsInv ρ W ∧ ∀ W' ≤ W, UpperTheory.Reformulated.B.IrreducibleInvariant.IsInv ρ W' → W' = ⊥ ∨ W' = W

noncomputable def UpperTheory.Reformulated.B.IrreducibleInvariant.IsIrr :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → Prop :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) ↦ UpperTheory.Reformulated.B.IrreducibleInvariant.IsIrrSub r ⊤

theorem UpperTheory.Reformulated.B.IrreducibleInvariant.exists_ne :
    ∀ {Γ k : Type} [inst : Group Γ] [inst_1 : Field k] (ρ : Γ →* GL (Fin (2 : ℕ)) k),
      UpperTheory.Reformulated.B.IrreducibleInvariant.IsIrr ρ →
        ∀ (g : GL (Fin (2 : ℕ)) k),
          ∃ (s : Γ),
            (↑(g * (ρ : Γ → GL (Fin (2 : ℕ)) k) s * g⁻¹) : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) k) (0 : Fin (2 : ℕ))
                (1 : Fin (2 : ℕ)) ≠
              (0 : k) := by
  intro Γ k _ _ ρ hirr g
  by_contra hcon
  push Not at hcon
  obtain ⟨-, -, hmin⟩ := hirr
  let L : Submodule k (Fin 2 → k) :=
    LinearMap.ker ((LinearMap.proj (0 : Fin 2) : (Fin 2 → k) →ₗ[k] k) ∘ₗ
      Matrix.mulVecLin (g : Matrix (Fin 2) (Fin 2) k))
  have hL : ∀ v, v ∈ L ↔ ((g : Matrix (Fin 2) (Fin 2) k).mulVec v) 0 = 0 := fun v => Iff.rfl
  have hg : ∀ w : Fin 2 → k, (g : Matrix (Fin 2) (Fin 2) k).mulVec
      (((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).mulVec w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hinv : UpperTheory.Reformulated.B.IrreducibleInvariant.IsInv ρ L := by
    intro s v hv
    rw [hL] at hv ⊢
    have key : (g : Matrix (Fin 2) (Fin 2) k).mulVec
        (((ρ s : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).mulVec v) =
        ((g * ρ s * g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).mulVec
          ((g : Matrix (Fin 2) (Fin 2) k).mulVec v) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
        inv_mul_cancel_right]
    rw [key]
    generalize (g : Matrix (Fin 2) (Fin 2) k).mulVec v = w at hv
    have h01 := hcon s
    generalize ((g * ρ s * g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = M at h01
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hv, h01]
  rcases hmin L le_top hinv with h | h
  · have h1 : ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).mulVec (Pi.single 1 1) ∈ L := by
      rw [hL, hg]
      simp
    rw [h, Submodule.mem_bot] at h1
    have h2 := hg (Pi.single 1 1)
    rw [h1, Matrix.mulVec_zero] at h2
    have h3 := congrFun h2 1
    simp at h3
  · have h1 : ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).mulVec (Pi.single 0 1) ∈ L := by
      rw [h]
      exact Submodule.mem_top
    rw [hL, hg] at h1
    simp at h1
end

section

theorem UpperTheory.mirabolic_row_congruence :
    ∀ {R : Type} [CommRing R] (I J : Ideal R) (g : GL (Fin 2) R), I ≤ J →
        Matrix.vecMul ![0, 1] ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) g : GL (Fin 2) (R ⧸ I)) : Matrix (Fin 2) (Fin 2) (R ⧸ I)) = ![0, 1] →
        Matrix.vecMul ![0, 1] ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk J) g : GL (Fin 2) (R ⧸ J)) : Matrix (Fin 2) (Fin 2) (R ⧸ J)) = ![0, 1] := by
  intro R _ I J g hIJ h
  have key : ∀ (K : Ideal R) (j : Fin 2),
      Matrix.vecMul ![0, 1] ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk K) g :
        GL (Fin 2) (R ⧸ K)) : Matrix (Fin 2) (Fin 2) (R ⧸ K)) j
        = Ideal.Quotient.mk K ((g : Matrix (Fin 2) (Fin 2) R) 1 j) := by
    intro K j
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.GeneralLinearGroup.map]
  funext j
  have hj := congrArg (Ideal.Quotient.factor hIJ) ((key I j).symm.trans (congrFun h j))
  rw [Ideal.Quotient.factor_mk] at hj
  rw [key J j, hj]
  fin_cases j <;> simp
end
