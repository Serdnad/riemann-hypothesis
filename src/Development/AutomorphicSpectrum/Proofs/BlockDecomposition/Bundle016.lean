module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
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
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

@[expose] public section

section

namespace GlobalTheory.CompanionTheory.EigenLift

theorem exists_eigenvector_of_surjective_intertwiner
    (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    [FiniteDimensional ℂ W] (T : W →ₗ[ℂ] W) (S : W' →ₗ[ℂ] W') (f : W →ₗ[ℂ] W')
    (hf : Function.Surjective f) (hfT : f ∘ₗ T = S ∘ₗ f)
    (c : ℂ) (w' : W') (hw' : w' ≠ 0) (hS : S w' = c • w') :
    ∃ w : W, w ≠ 0 ∧ T w = c • w := by
  by_contra hne
  push_neg at hne
  haveI : FiniteDimensional ℂ W' := Module.Finite.of_surjective (R := ℂ) f hf
  set A : W →ₗ[ℂ] W := T - c • LinearMap.id with hA
  set B : W' →ₗ[ℂ] W' := S - c • LinearMap.id with hB
  have hinj : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    by_contra h0
    apply hne w h0
    simpa [hA, sub_eq_zero] using hw
  have hsurjT : Function.Surjective A := LinearMap.injective_iff_surjective.1 hinj
  have hcomm : ∀ z, f (A z) = B (f z) := by
    intro z
    have h1 := LinearMap.congr_fun hfT z
    simp only [LinearMap.comp_apply] at h1
    simp [hA, hB, map_sub, map_smul, h1]
  have hsurjS : Function.Surjective B := by
    intro y
    obtain ⟨x, rfl⟩ := hf y
    obtain ⟨z, rfl⟩ := hsurjT x
    exact ⟨f z, (hcomm z).symm⟩
  have hinjS := LinearMap.injective_iff_surjective.2 hsurjS
  apply hw'
  apply hinjS
  simp [hB, hS]

theorem nonzero_eigenvalue_lifts :
    ∀ (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
      [FiniteDimensional ℂ W] (T : W →ₗ[ℂ] W) (S : W' →ₗ[ℂ] W') (f : W →ₗ[ℂ] W'),
      Function.Surjective f → f ∘ₗ T = S ∘ₗ f →
      ∀ (c : ℂ) (w' : W'), w' ≠ 0 → S w' = c • w' → c ≠ 0 → ∃ w : W, w ≠ 0 ∧ T w = c • w := by
  intro W W' _ _ _ _ _ T S f hf hfT c w' hw' hS _
  exact exists_eigenvector_of_surjective_intertwiner W W' T S f hf hfT c w' hw' hS

end GlobalTheory.CompanionTheory.EigenLift
end

section

namespace GlobalTheory.CompanionTheory.SimpleDensity

theorem exists_smul_eq_on_finset {R ι : Type} [Ring R] [Fintype ι] (M : ι → Type)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, IsSimpleModule R (M i)]
    (hne : ∀ i j, i ≠ j → ∀ φ : M i →ₗ[R] M j, φ = 0)
    (f : ∀ i, M i →+ M i)
    (hf : ∀ i (φ : M i →ₗ[R] M i) x, f i (φ x) = φ (f i x))
    (s : Finset (∀ i, M i)) :
    ∃ r : R, ∀ m ∈ s, ∀ i, f i (m i) = r • m i := by
  classical
  have key : ∀ (φ : Module.End R (∀ i, M i)) (m : ∀ i, M i) (i : ι),
      φ m i = ((LinearMap.proj i) ∘ₗ φ ∘ₗ LinearMap.single R M i) (m i) := by
    intro φ m i
    have hm : m = ∑ j, Pi.single j (m j) := (Finset.univ_sum_single m).symm
    conv_lhs => rw [hm]

    rw [map_sum, Finset.sum_apply, Finset.sum_eq_single i]
    · rfl
    · intro j _ hj
      have := hne j i hj ((LinearMap.proj i) ∘ₗ φ ∘ₗ LinearMap.single R M j)
      exact LinearMap.congr_fun this (m j)
    · simp
  let F : Module.End (Module.End R (∀ i, M i)) (∀ i, M i) :=
    { toFun := fun m i => f i (m i)
      map_add' := fun a b => by ext i; simp
      map_smul' := fun φ m => by
        ext i
        simp only [Module.End.smul_def, RingHom.id_apply]
        rw [key φ m i, key φ _ i, hf] }
  obtain ⟨r, hr⟩ := jacobson_density F s
  exact ⟨r, fun m hm i => congrFun (hr m hm) i⟩

theorem exists_scalar_of_simple {A N : Type} [Ring A] [Algebra ℂ A] [AddCommGroup N] [Module ℂ N] [Module A N]
    [IsScalarTower ℂ A N] [FiniteDimensional ℂ N] [IsSimpleModule A N] (φ : N →ₗ[A] N) :
    ∃ c : ℂ, ∀ x, φ x = c • x := by
  haveI : Nontrivial N := IsSimpleModule.nontrivial A N
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (φ.restrictScalars ℂ : Module.End ℂ N)
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  refine ⟨c, ?_⟩
  have hw1 : φ w = c • w := hw.apply_eq_smul
  let ψ : N →ₗ[A] N := φ - c • LinearMap.id
  rcases LinearMap.injective_or_eq_zero ψ with hi | h0
  · exfalso
    have hz : ψ w = 0 := by simp [ψ, hw1]
    exact hw.2 (hi (by rw [hz, map_zero]))
  · intro x
    have := LinearMap.congr_fun h0 x
    simpa [ψ, sub_eq_zero] using this

theorem exists_smul_eq_end : ∀ (A : Type) [Ring A] [Algebra ℂ A] (J : Type) [Fintype J] (M : J → Type)
    [∀ j, AddCommGroup (M j)] [∀ j, Module ℂ (M j)] [∀ j, Module A (M j)] [∀ j, IsScalarTower ℂ A (M j)]
    [∀ j, FiniteDimensional ℂ (M j)] [∀ j, IsSimpleModule A (M j)],
    (∀ i j, Nonempty (M i ≃ₗ[A] M j) → i = j) →
      ∀ f : ∀ j, Module.End ℂ (M j), ∃ a : A, ∀ j (x : M j), a • x = f j x := by
  intro A _ _ J _ M _ _ _ _ _ _ hiso f
  classical
  have hne : ∀ i j, i ≠ j → ∀ φ : M i →ₗ[A] M j, φ = 0 := by
    intro i j hij φ
    by_contra h
    exact hij (hiso i j ⟨LinearEquiv.ofBijective φ (LinearMap.bijective_of_ne_zero h)⟩)
  have hf : ∀ i (φ : M i →ₗ[A] M i) x,
      (f i).toAddMonoidHom (φ x) = φ ((f i).toAddMonoidHom x) := by
    intro i φ x
    obtain ⟨c, hc⟩ := exists_scalar_of_simple φ
    simp [hc]
  let b : ∀ j, Module.Basis (Module.Free.ChooseBasisIndex ℂ (M j)) ℂ (M j) := fun j => Module.Free.chooseBasis ℂ (M j)
  haveI : ∀ j, Fintype (Module.Free.ChooseBasisIndex ℂ (M j)) := fun j => inferInstance
  let s : Finset (∀ j, M j) :=
    Finset.univ.biUnion fun j => Finset.univ.image fun k => (Pi.single j (b j k) : ∀ j, M j)
  obtain ⟨r, hr⟩ := exists_smul_eq_on_finset M hne (fun j => (f j).toAddMonoidHom) hf s
  refine ⟨r, fun j x => ?_⟩
  have hlin : (Algebra.lsmul ℂ ℂ (M j) r : Module.End ℂ (M j)) = f j := by
    refine (b j).ext fun k => ?_
    have hm : (Pi.single j (b j k) : ∀ j, M j) ∈ s :=
      Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, Finset.mem_image.2 ⟨k, Finset.mem_univ _, rfl⟩⟩
    have := hr _ hm j
    simpa using this.symm
  exact LinearMap.congr_fun hlin x

end GlobalTheory.CompanionTheory.SimpleDensity
end

section

open Matrix

namespace GlobalTheory.CompanionTheory.QR

theorem exists_unitary_mul_blockTriangular {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) (_hg : IsUnit g) :
    ∃ k ∈ Matrix.unitaryGroup (Fin m) ℂ, ∃ b : Matrix (Fin m) (Fin m) ℂ,
      g = k * b ∧ b.BlockTriangular id := by
  let e := EuclideanSpace.basisFun (Fin m) ℂ
  let f : Fin m → EuclideanSpace ℂ (Fin m) := fun j => WithLp.toLp 2 fun i => g i j
  have h : Module.finrank ℂ (EuclideanSpace ℂ (Fin m)) = Fintype.card (Fin m) := by simp
  let o := InnerProductSpace.gramSchmidtOrthonormalBasis h f
  refine ⟨e.toBasis.toMatrix o, e.toMatrix_orthonormalBasis_mem_unitary o, o.toBasis.toMatrix f, ?_,
    InnerProductSpace.gramSchmidtOrthonormalBasis_inv_isUpperTriangular h f⟩
  have hmul := Module.Basis.toMatrix_mul_toMatrix e.toBasis o.toBasis f
  rw [OrthonormalBasis.coe_toBasis] at hmul
  rw [hmul]
  ext i j
  rw [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr]

end GlobalTheory.CompanionTheory.QR
end

section

open Matrix

namespace GlobalTheory.CompanionTheory.WittFrame

abbrev FrameIdx (D m : ℕ) := Fin D ⊕ₗ (Fin m ⊕ₗ (Fin D)ᵒᵈ)

def frameEquiv (D m : ℕ) : FrameIdx D m ≃ Fin D ⊕ (Fin m ⊕ Fin D) :=
  ofLex.trans (Equiv.sumCongr (Equiv.refl _)
    (ofLex.trans (Equiv.sumCongr (Equiv.refl _) OrderDual.ofDual)))

theorem block_zero {D m : ℕ} (b b' : Matrix (Fin D) (Fin D) ℂ) (t : Matrix (Fin m) (Fin m) ℂ)
    (hb : b.BlockTriangular id) (ht : t.BlockTriangular id)
    (hb' : ∀ x y, x < y → b' x y = 0) (p q : FrameIdx D m) (hqp : q < p) :
    (fromBlocks b 0 0 (fromBlocks t 0 0 b')) (frameEquiv D m p) (frameEquiv D m q) = 0 := by
  obtain ⟨p, rfl⟩ := toLex.surjective p
  obtain ⟨q, rfl⟩ := toLex.surjective q
  rcases p with a | u <;> rcases q with c | v
  · have h : c < a := Sum.Lex.inl_lt_inl_iff.1 hqp
    simpa [frameEquiv] using hb h
  · exact absurd hqp Sum.Lex.not_inr_lt_inl
  · simp [frameEquiv]
  · have h : v < u := Sum.Lex.inr_lt_inr_iff.1 hqp
    obtain ⟨u, rfl⟩ := toLex.surjective u
    obtain ⟨v, rfl⟩ := toLex.surjective v
    rcases u with a | u <;> rcases v with c | v
    · have h' : c < a := Sum.Lex.inl_lt_inl_iff.1 h
      simpa [frameEquiv] using ht h'
    · exact absurd h Sum.Lex.not_inr_lt_inl
    · simp [frameEquiv]
    · have h' : v < u := Sum.Lex.inr_lt_inr_iff.1 h
      have h'' : OrderDual.ofDual u < OrderDual.ofDual v := h'
      simpa [frameEquiv] using hb' _ _ h''

theorem unitary_of_blocks {n D m : ℕ} (C H : Matrix (Fin n) (Fin D) ℂ)
    (G : Matrix (Fin n) (Fin m) ℂ)
    (hCC : Cᴴ * C = 1) (hCG : Cᴴ * G = 0) (hCH : Cᴴ * H = 0) (hGG : Gᴴ * G = 1)
    (hGH : Gᴴ * H = 0) (hHH : Hᴴ * H = 1) (hcard : D + (m + D) = n) :
    ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ (s : Matrix (Fin n) (Fin n) ℂ)
      (b b' : Matrix (Fin D) (Fin D) ℂ) (t : Matrix (Fin m) (Fin m) ℂ),
      s * C = C * b → s * G = G * t → s * H = H * b' → b.BlockTriangular id →
      t.BlockTriangular id → (∀ x y, x < y → b' x y = 0) → (Uᴴ * s * U).BlockTriangular id := by
  have hGC : Gᴴ * C = 0 := by
    have := congrArg conjTranspose hCG
    simpa [conjTranspose_mul] using this
  have hHC : Hᴴ * C = 0 := by
    have := congrArg conjTranspose hCH
    simpa [conjTranspose_mul] using this
  have hHG : Hᴴ * G = 0 := by
    have := congrArg conjTranspose hGH
    simpa [conjTranspose_mul] using this
  set E : Matrix (Fin n) (Fin D ⊕ (Fin m ⊕ Fin D)) ℂ := fromCols C (fromCols G H) with hEdef
  have hE : Eᴴ * E = 1 := by
    rw [hEdef, conjTranspose_fromCols_eq_fromRows_conjTranspose,
      conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols, fromRows_mul,
      fromRows_mul, mul_fromCols, mul_fromCols, mul_fromCols, fromRows_fromCols_eq_fromBlocks,
      hCC, hCG, hCH, hGC, hGG, hGH, hHC, hHG, hHH, fromCols_zero, fromRows_zero, fromBlocks_one,
      fromBlocks_one]
  have hT : Fintype.card (FrameIdx D m) = n := by
    rw [← hcard]
    simp [Fintype.card_congr (frameEquiv D m)]
  let g : Fin n ≃ Fin D ⊕ (Fin m ⊕ Fin D) :=
    (Fintype.orderIsoFinOfCardEq (FrameIdx D m) hT).toEquiv.trans (frameEquiv D m)
  refine ⟨E.submatrix id g, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    show (E.submatrix id g)ᴴ * E.submatrix id g = 1
    rw [conjTranspose_submatrix, ← submatrix_mul _ _ g id g Function.bijective_id, hE,
      submatrix_one_equiv]
  · intro s b b' t h1 h2 h3 hb ht hb'
    have hs : s * E = E * fromBlocks b 0 0 (fromBlocks t 0 0 b') := by
      rw [hEdef, mul_fromCols, mul_fromCols, h1, h2, h3, fromCols_mul_fromBlocks,
        fromCols_mul_fromBlocks]
      simp
    have hΔ : Eᴴ * s * E = fromBlocks b 0 0 (fromBlocks t 0 0 b') := by
      rw [Matrix.mul_assoc, hs, ← Matrix.mul_assoc, hE, Matrix.one_mul]
    have hM : (E.submatrix id g)ᴴ * s * E.submatrix id g =
        (fromBlocks b 0 0 (fromBlocks t 0 0 b')).submatrix g g := by
      rw [← hΔ, submatrix_mul _ _ g id g Function.bijective_id,
        submatrix_mul _ _ g id id Function.bijective_id, submatrix_id_id,
        conjTranspose_submatrix]
    rw [hM]
    intro x y hxy
    exact block_zero b b' t hb ht hb' _ _ ((Fintype.orderIsoFinOfCardEq (FrameIdx D m) hT).lt_iff_lt.2 hxy)

theorem unitary_adapted_triangularises : ∀ {n D m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ)
    (J' : Matrix (Fin m) (Fin m) ℂ) (C : Matrix (Fin n) (Fin D) ℂ) (R : Matrix (Fin n) (Fin m) ℂ),
    J * J = 1 → Jᴴ = J → Cᴴ * C = 1 → Cᴴ * J * C = 0 → Rᴴ * R = 1 → J * R = R * J' →
    Cᴴ * R = 0 → C * Cᴴ + J * C * Cᴴ * J + R * Rᴴ = 1 →
    ∀ U₀ ∈ Matrix.unitaryGroup (Fin m) ℂ, ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ,
      ∀ (s : Matrix (Fin n) (Fin n) ℂ) (b b' : Matrix (Fin D) (Fin D) ℂ)
        (t : Matrix (Fin m) (Fin m) ℂ),
        s * C = C * b → s * (R * U₀) = (R * U₀) * t → s * (J * C) = (J * C) * b' →
        b.BlockTriangular id → t.BlockTriangular id → (∀ x y, x < y → b' x y = 0) →
        (Uᴴ * s * U).BlockTriangular id := by
  intro n D m J J' C R hJJ hJh hCC hCJC hRR hJR hCR hsum U₀ hU₀
  have hU : U₀ᴴ * U₀ = 1 := (Matrix.mem_unitaryGroup_iff').1 hU₀
  have hRC : Rᴴ * C = 0 := by
    have := congrArg conjTranspose hCR
    simpa [conjTranspose_mul] using this
  have hRJ : Rᴴ * J = J'ᴴ * Rᴴ := by
    have := congrArg conjTranspose hJR
    simpa [conjTranspose_mul, hJh] using this
  have t1 : trace (C * Cᴴ) = (D : ℂ) := by
    rw [trace_mul_comm, hCC, trace_one]; simp
  have t2 : trace (J * C * Cᴴ * J) = (D : ℂ) := by
    rw [trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJJ, Matrix.one_mul, t1]
  have t3 : trace (R * Rᴴ) = (m : ℂ) := by
    rw [trace_mul_comm, hRR, trace_one]; simp
  have hcard : D + (m + D) = n := by
    have h := congrArg trace hsum
    rw [trace_add, trace_add, t1, t2, t3, trace_one] at h
    simp only [Fintype.card_fin] at h
    have h' : ((D + D + m : ℕ) : ℂ) = (n : ℂ) := by push_cast; exact h
    have h'' : D + D + m = n := by exact_mod_cast h'
    omega
  refine unitary_of_blocks C (J * C) (R * U₀) hCC ?_ ?_ ?_ ?_ ?_ hcard
  · rw [← Matrix.mul_assoc, hCR, Matrix.zero_mul]
  · rw [← Matrix.mul_assoc, hCJC]
  · rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Rᴴ, hRR, Matrix.one_mul, hU]
  · rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Rᴴ, hRJ, Matrix.mul_assoc, hRC]
    simp
  · rw [conjTranspose_mul, hJh, Matrix.mul_assoc, ← Matrix.mul_assoc J, hJJ, Matrix.one_mul, hCC]

end GlobalTheory.CompanionTheory.WittFrame
end

section

open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.MatrixComm

theorem commute_diagonal_of_dominated {n : ℕ} (d e : Fin n → ℂ)
    (Z : Matrix (Fin n) (Fin n) ℂ) (hZ : Matrix.diagonal d * Z = Z * Matrix.diagonal d)
    (hde : ∀ i j, d i = d j → e i = e j) :
    Z * Matrix.diagonal e = Matrix.diagonal e * Z := by
  ext i j
  have hij := congrFun (congrFun hZ i) j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at hij
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hz : Z i j = 0
  · simp [hz]
  · have hd : d i = d j := by
      have : Z i j * d i = Z i j * d j := by rw [mul_comm (Z i j) (d i)]; exact hij
      exact mul_left_cancel₀ hz this
    rw [hde i j hd, mul_comm]

theorem commute_of_dominated_diag {n : ℕ} (U H A Y : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hH : (Uᴴ * H * U).IsDiag) (hA : (Uᴴ * A * U).IsDiag)
    (hdom : ∀ i j, (Uᴴ * H * U) i i = (Uᴴ * H * U) j j → (Uᴴ * A * U) i i = (Uᴴ * A * U) j j)
    (hHY : H * Y = Y * H) : Y * A = A * Y := by
  have h2 : U * Uᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hU
    simpa [Matrix.star_eq_conjTranspose] using this
  have conj_mul : ∀ P Q : Matrix (Fin n) (Fin n) ℂ,
      (Uᴴ * P * U) * (Uᴴ * Q * U) = Uᴴ * (P * Q) * U := by
    intro P Q
    calc (Uᴴ * P * U) * (Uᴴ * Q * U) = Uᴴ * P * (U * Uᴴ) * Q * U := by
          simp only [Matrix.mul_assoc]
      _ = Uᴴ * (P * Q) * U := by
          rw [h2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  have back : ∀ P : Matrix (Fin n) (Fin n) ℂ, U * (Uᴴ * P * U) * Uᴴ = P := by
    intro P
    calc U * (Uᴴ * P * U) * Uᴴ = (U * Uᴴ) * P * (U * Uᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = P := by rw [h2]; simp
  have hcomm : (Uᴴ * H * U) * (Uᴴ * Y * U) = (Uᴴ * Y * U) * (Uᴴ * H * U) := by
    rw [conj_mul, conj_mul, hHY]
  have hdH : Matrix.diagonal (fun i => (Uᴴ * H * U) i i) = Uᴴ * H * U := hH.diagonal_diag
  have hdA : Matrix.diagonal (fun i => (Uᴴ * A * U) i i) = Uᴴ * A * U := hA.diagonal_diag
  have key := commute_diagonal_of_dominated (fun i => (Uᴴ * H * U) i i)
    (fun i => (Uᴴ * A * U) i i) (Uᴴ * Y * U) (by rw [hdH]; exact hcomm) hdom
  rw [hdA, conj_mul, conj_mul] at key
  have := congrArg (fun M => U * M * Uᴴ) key
  simpa only [back] using this

end GlobalTheory.CompanionTheory.MatrixComm
end

section

open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.FrameSort

theorem exists_antitone_reorder : ∀ {n : ℕ} (U₀ : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ), U₀ ∈ Matrix.unitaryGroup (Fin n) ℂ → ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∃ h : Fin n → ℝ, Antitone h ∧ U * Matrix.diagonal (fun i => (h i : ℂ)) * Uᴴ = U₀ * Matrix.diagonal (fun i => (d i : ℂ)) * U₀ᴴ ∧ ∀ Z : Matrix (Fin n) (Fin n) ℂ, (U₀ᴴ * Z * U₀).IsDiag → (Uᴴ * Z * U).IsDiag := by
  intro n U₀ d hU
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin n), Antitone (d ∘ σ) := by
    refine ⟨Tuple.sort (fun i => - d i), ?_⟩
    intro a b hab
    have := Tuple.monotone_sort (fun i => - d i) hab
    simpa using this
  have hH : (U₀.submatrix id σ)ᴴ = U₀ᴴ.submatrix σ id := by
    ext i j; simp
  have hconj : ∀ Z : Matrix (Fin n) (Fin n) ℂ,
      (U₀.submatrix id σ)ᴴ * Z * U₀.submatrix id σ = (U₀ᴴ * Z * U₀).submatrix σ σ := by
    intro Z
    rw [hH]
    ext i j
    simp [Matrix.mul_apply]
  refine ⟨U₀.submatrix id σ, ?_, d ∘ σ, hσ, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    have h1 := hconj 1
    rw [Matrix.mul_one] at h1
    rw [h1, Matrix.mul_one]
    have h2 : U₀ᴴ * U₀ = 1 := by
      have := Matrix.mem_unitaryGroup_iff'.mp hU
      simpa [Matrix.star_eq_conjTranspose] using this
    rw [h2]
    simp
  · rw [hH]
    ext a b
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.submatrix_apply, id, Function.comp]
    exact Equiv.sum_comp σ (fun i => U₀ a i * (d i : ℂ) * U₀ᴴ i b)
  · intro Z hZ
    rw [hconj Z]
    intro i j hij
    simpa using hZ (fun e => hij (σ.injective e))

end GlobalTheory.CompanionTheory.FrameSort
end

section

namespace GlobalTheory.CompanionTheory.Hecke

theorem heckeSum_fixed :
    ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
      (K : Subgroup G) (f : G → ℂ), (Function.support fun q : G ⧸ K => f q.out).Finite →
      (∀ k ∈ K, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) → ∀ v : V, (∀ k ∈ K, ρ k v = v) →
      ∀ k ∈ K, ρ k (∑ᶠ q : G ⧸ K, f q.out • ρ q.out v) = ∑ᶠ q : G ⧸ K, f q.out • ρ q.out v := by
  intro G V _ _ _ ρ K f hfin hbi v hv k hk
  have hsupp : (Function.support fun q : G ⧸ K => f q.out • ρ q.out v).Finite := by
    refine hfin.subset ?_
    intro q hq h0
    apply hq
    have h0' : f q.out = 0 := h0
    simp [h0']
  have hstep : ∀ q : G ⧸ K, ρ k (f q.out • ρ q.out v)
      = f (MulAction.toPerm k q).out • ρ (MulAction.toPerm k q).out v := by
    intro q
    have hmk : ((MulAction.toPerm k q : G ⧸ K).out : G ⧸ K) = ((k * q.out : G) : G ⧸ K) := by
      rw [QuotientGroup.out_eq', MulAction.toPerm_apply]
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have hκ : (k * q.out)⁻¹ * (MulAction.toPerm k q : G ⧸ K).out ∈ K :=
      QuotientGroup.eq.mp hmk.symm
    obtain ⟨κ, hκK, hκ⟩ : ∃ κ ∈ K, (MulAction.toPerm k q : G ⧸ K).out = k * q.out * κ :=
      ⟨_, hκ, by group⟩
    rw [hκ, (hbi κ hκK _).2, (hbi k hk _).1, map_mul, map_mul, map_smul]
    simp [hv κ hκK]
  have h1 := (ρ k).toAddMonoidHom.map_finsum hsupp
  have h2 : ρ k (∑ᶠ q : G ⧸ K, f q.out • ρ q.out v)
      = ∑ᶠ q : G ⧸ K, ρ k (f q.out • ρ q.out v) := h1
  rw [h2, finsum_congr hstep]
  exact finsum_comp_equiv (MulAction.toPerm k) (f := fun q : G ⧸ K => f q.out • ρ q.out v)

end GlobalTheory.CompanionTheory.Hecke
end

section

namespace GlobalTheory.CompanionTheory.DualFin

theorem finite_dual_all : ∀ (R M : Type) [CommRing R] [Finite R] [AddCommGroup M] [Module R M] [Finite M], Finite (Module.Dual R M) :=
  fun R M _ _ _ _ _ =>
    Finite.of_injective (fun f : Module.Dual R M => (f : M → R)) DFunLike.coe_injective

end GlobalTheory.CompanionTheory.DualFin
end
