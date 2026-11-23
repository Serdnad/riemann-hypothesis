module

import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.CosetCover
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace SemilocalBasis

open scoped Pointwise

theorem exists_forall_notMem {A V J : Type*} [CommRing A] [IsLocalRing A]
    [Infinite (IsLocalRing.ResidueField A)] [AddCommGroup V] [Module A V] [Finite J]
    (p : J → Submodule A V) (hp : ∀ i, p i ≠ ⊤)
    (hm : ∀ i, ∀ a ∈ IsLocalRing.maximalIdeal A, ∀ x, a • x ∈ p i) : ∃ x : V, ∀ i, x ∉ p i := by
  let I := IsLocalRing.maximalIdeal A
  let : Field (A ⧸ I) := Ideal.Quotient.field I
  let : Infinite (A ⧸ I) := inferInstanceAs (Infinite (IsLocalRing.ResidueField A))
  let N : Submodule A V := I • ⊤
  let q : V →ₛₗ[Ideal.Quotient.mk I] V ⧸ N :=
    { toFun := Submodule.Quotient.mk
      map_add' := map_add N.mkQ
      map_smul' := Module.Quotient.mk_smul_mk V I }
  have hq : LinearMap.ker q = N := Submodule.ker_mkQ N
  have hle (i : J) : N ≤ p i := Submodule.smul_le.mpr fun a ha x _ => hm i a ha x
  have hne (i : J) : (p i).map q ≠ ⊤ := by
    intro h
    have hc := Submodule.comap_map_eq_self (f := q) (hq ▸ hle i)
    rw [h, Submodule.comap_top] at hc
    exact hp i hc.symm
  obtain ⟨y, hy⟩ := Submodule.exists_forall_notMem_of_forall_ne_top (K := A ⧸ I) (fun i => (p i).map q) hne
  obtain ⟨x, rfl⟩ := N.mkQ_surjective y
  exact ⟨x, fun i hx => hy i (Submodule.mem_map_of_mem hx)⟩

noncomputable def red {B M : Type*} [CommRing B] [AddCommGroup M] [Module B M] {n : ℕ}
    (e : Module.Basis (Fin n) B M) (I : Ideal B) : M →ₗ[B] (Fin n → B ⧸ I) :=
  LinearMap.pi fun j => (Submodule.mkQ I).comp (e.coord j)

theorem red_apply {B M : Type*} [CommRing B] [AddCommGroup M] [Module B M] {n : ℕ}
    (e : Module.Basis (Fin n) B M) (I : Ideal B) (x : M) (j : Fin n) :
    red e I x j = Ideal.Quotient.mk I (e.repr x j) := rfl

theorem red_surjective {B M : Type*} [CommRing B] [AddCommGroup M] [Module B M] {n : ℕ}
    (e : Module.Basis (Fin n) B M) (I : Ideal B) : Function.Surjective (red e I) := by
  intro y
  choose s hs using Ideal.Quotient.mk_surjective (I := I)
  refine ⟨e.equivFun.symm fun j => s (y j), ?_⟩
  ext j
  rw [red_apply, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, hs]

theorem exists_linearIndependent {A B M : Type*} [CommRing A] [IsLocalRing A]
    [Infinite (IsLocalRing.ResidueField A)] [CommRing B] [Algebra A B]
    [Finite (MaximalSpectrum B)] [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    {n : ℕ} (e : Module.Basis (Fin n) B M) (N : Submodule A M)
    (hm : ∀ m : MaximalSpectrum B,
      (IsLocalRing.maximalIdeal A).map (algebraMap A B) ≤ m.asIdeal)
    (hN : Submodule.span B (N : Set M) = ⊤) (k : ℕ) (hk : k ≤ n) :
    ∃ v : Fin k → M, (∀ i, v i ∈ N) ∧ ∀ m : MaximalSpectrum B,
      LinearIndependent (B ⧸ m.asIdeal) (fun i => red e m.asIdeal (v i)) := by
  induction k with
  | zero => exact ⟨Fin.elim0, fun i => i.elim0, fun _ => linearIndependent_empty_type⟩
  | succ k ih =>
    obtain ⟨v, hvN, hv⟩ := ih (by omega)
    let W : ∀ m : MaximalSpectrum B, Submodule (B ⧸ m.asIdeal) (Fin n → B ⧸ m.asIdeal) :=
      fun m => Submodule.span _ (Set.range fun i => red e m.asIdeal (v i))
    let q : MaximalSpectrum B → Submodule B M :=
      fun m => ((W m).restrictScalars B).comap (red e m.asIdeal)
    let p : MaximalSpectrum B → Submodule A N :=
      fun m => ((q m).restrictScalars A).comap N.subtype
    obtain ⟨x, hx⟩ := exists_forall_notMem p (fun m h => by
      have := m.isMaximal
      letI := Ideal.Quotient.field m.asIdeal
      have h1 : q m = ⊤ := by
        rw [eq_top_iff, ← hN, Submodule.span_le]
        intro y hy
        have : (⟨y, hy⟩ : N) ∈ p m := h ▸ Submodule.mem_top
        exact this
      have h2 : W m = ⊤ := by
        rw [eq_top_iff]
        intro y _
        obtain ⟨z, rfl⟩ := red_surjective e m.asIdeal y
        have : z ∈ q m := h1 ▸ Submodule.mem_top
        exact this
      have h3 : Module.finrank (B ⧸ m.asIdeal) (W m) = k := by
        have := finrank_span_eq_card (hv m)
        simpa using this
      rw [h2] at h3
      simp at h3
      omega) (fun m a ha y => by
      have h0 : red e m.asIdeal (a • (y : M)) = 0 := by
        ext j
        rw [red_apply, ← algebraMap_smul B, map_smul, Finsupp.smul_apply, smul_eq_mul,
          Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mul_mem_right _ _ (hm m (Ideal.mem_map_of_mem _ ha))
      change red e m.asIdeal (a • (y : M)) ∈ W m
      rw [h0]
      exact zero_mem _)
    refine ⟨Fin.cons (x : M) v, fun i => ?_, fun m => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · exact x.2
      · exact hvN j
    · have := m.isMaximal
      letI := Ideal.Quotient.field m.asIdeal
      have h1 : (fun i => red e m.asIdeal (Fin.cons (α := fun _ => M) (x : M) v i)) =
          Fin.cons (red e m.asIdeal x) (fun i => red e m.asIdeal (v i)) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      rw [h1, linearIndependent_finCons]
      exact ⟨hv m, hx m⟩

end SemilocalBasis

theorem exists_basis_mem_of_span_eq_top_of_semilocal :
    ∀ (A B M : Type) [CommRing A] [IsLocalRing A] [Infinite (IsLocalRing.ResidueField A)] [CommRing B] [Algebra A B] [Finite (MaximalSpectrum B)] [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M] (n : ℕ) (_ : Module.Basis (Fin n) B M) (N : Submodule A M), (∀ m : MaximalSpectrum B, (IsLocalRing.maximalIdeal A).map (algebraMap A B) ≤ m.asIdeal) → Submodule.span B (N : Set M) = ⊤ → ∃ b : Module.Basis (Fin n) B M, ∀ i, b i ∈ N := by
  intro A B M _ _ _ _ _ _ _ _ _ _ n e N hm hN
  obtain ⟨v, hvN, hv⟩ := SemilocalBasis.exists_linearIndependent e N hm hN n le_rfl
  have hu : IsUnit (e.det v) := by
    by_contra hne
    obtain ⟨I, hI, hmem⟩ := exists_max_ideal_of_mem_nonunits hne
    letI := Ideal.Quotient.field I
    have h1 := hv ⟨I, hI⟩
    have h2 : IsUnit ((e.toMatrix v).map (Ideal.Quotient.mk I)) :=
      Matrix.linearIndependent_cols_iff_isUnit.mp h1
    rw [Matrix.isUnit_iff_isUnit_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      ← Module.Basis.det_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hmem] at h2
    exact not_isUnit_zero h2
  obtain ⟨hli, hsp⟩ := e.is_basis_iff_det.mpr hu
  exact ⟨Module.Basis.mk hli hsp.ge, fun i => by simpa using hvN i⟩

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_mul_eq_smul_one_of_mulVec_injective {R K : Type} [CommRing R] [Field K]
    (g : R →+* K) {m l : Type} [Fintype m] [Fintype l] [DecidableEq l] (M : Matrix m l R)
    (hM : ∀ x : l → K, (M.map g).mulVec x = 0 → x = 0) :
    ∃ (r : R) (T : Matrix l m R), g r ≠ 0 ∧ T * M = r • (1 : Matrix l l R) := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K (fun i : m => (M.map g) i)
  have : Fintype κ := Fintype.ofInjective a ha
  have h1 : Fintype.card κ ≤ Fintype.card l := by
    have := hli.fintype_card_le_finrank
    simpa using this
  have h2 : Fintype.card l ≤ Fintype.card κ := by
    have hinj : Function.Injective (Matrix.mulVecLin ((M.map g).submatrix a id)) := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro x hx
      apply hM
      funext i
      have hi : (M.map g) i ∈ Submodule.span K (Set.range ((fun i : m => (M.map g) i) ∘ a)) := by
        rw [hspan]; exact Submodule.subset_span ⟨i, rfl⟩
      have key : ∀ y ∈ Submodule.span K (Set.range ((fun i : m => (M.map g) i) ∘ a)),
          y ⬝ᵥ x = 0 := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨k, rfl⟩ := hy
          exact congrFun hx k
        | zero => simp
        | add y z _ _ hy hz => rw [add_dotProduct, hy, hz, add_zero]
        | smul c y _ hy => rw [smul_dotProduct, hy, smul_zero]
      exact key _ hi
    have := LinearMap.finrank_le_finrank_of_injective hinj
    simpa using this
  let e : l ≃ κ := Fintype.equivOfCardEq (le_antisymm h2 h1)
  let N : Matrix l l R := M.submatrix (a ∘ e) id
  have hN : IsUnit (N.map g) := by
    rw [← Matrix.linearIndependent_rows_iff_isUnit]
    exact hli.comp e e.injective
  refine ⟨N.det, N.adjugate * (1 : Matrix m m R).submatrix (a ∘ e) id, ?_, ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det] at hN
    have : g N.det = (N.map g).det := by rw [RingHom.map_det]; rfl
    rw [this]; exact hN.ne_zero
  · rw [Matrix.mul_assoc]
    have : (1 : Matrix m m R).submatrix (a ∘ e) id * M = N := by
      ext i j
      simp [N, Matrix.mul_apply, Matrix.one_apply]
    rw [this, Matrix.adjugate_mul]

theorem exists_kernel_certificate {R K : Type} [CommRing R] [Field K] (g : R →+* K)
    {a b c : Type} [Fintype a] [Fintype b] [Fintype c] [DecidableEq a]
    (D₀ : Matrix b a R) (D₁ : Matrix c b R) (h0 : D₁ * D₀ = 0)
    (hex : ∀ w : b → K, (D₁.map g).mulVec w = 0 → ∃ v, (D₀.map g).mulVec v = w) :
    ∃ (r : R) (n : ℕ) (B : Matrix a (Fin n) R) (C : Matrix (Fin n) a R) (H : Matrix a b R),
      g r ≠ 0 ∧ D₀ * B = 0 ∧ C * B = r • (1 : Matrix (Fin n) (Fin n) R) ∧
        B * C + H * D₀ = r • (1 : Matrix a a R) := by
  classical
  obtain ⟨κ, s, hs, hspan, hli⟩ := exists_linearIndependent' K (fun j : a => (D₀.map g).col j)
  have : Fintype κ := Fintype.ofInjective s hs
  let S : Matrix a κ R := (1 : Matrix a a R).submatrix id s
  have hDS : D₀ * S = D₀.submatrix id s := by
    ext i j
    simp [S, Matrix.mul_apply, Matrix.one_apply]
  have hsum : ∀ x : κ → K, ((D₀ * S).map g).mulVec x =
      ∑ k, x k • ((fun j : a => (D₀.map g).col j) ∘ s) k := by
    intro x
    funext i
    simp [hDS, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  obtain ⟨r₀, T₀, hr₀, hT₀⟩ := exists_mul_eq_smul_one_of_mulVec_injective g (D₀ * S) (by
    intro x hx
    rw [hsum] at hx
    funext k
    exact Fintype.linearIndependent_iff.1 hli x hx k)
  obtain ⟨r₁, T₁, hr₁, hT₁⟩ := exists_mul_eq_smul_one_of_mulVec_injective g
    (Matrix.fromRows T₀ D₁) (by
    intro w hw
    have hw1 : (T₀.map g).mulVec w = 0 := by
      funext k; exact congrFun hw (Sum.inl k)
    have hw2 : (D₁.map g).mulVec w = 0 := by
      funext k; exact congrFun hw (Sum.inr k)
    obtain ⟨v, hv⟩ := hex w hw2
    have hmem : w ∈ Submodule.span K (Set.range ((fun j : a => (D₀.map g).col j) ∘ s)) := by
      rw [hspan, ← hv]
      have : (D₀.map g).mulVec v = ∑ j, v j • (D₀.map g).col j := by
        funext i
        simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
      rw [this]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    obtain ⟨u, hu⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hmem
    rw [← hsum] at hu
    rw [← hu, Matrix.mulVec_mulVec, ← Matrix.map_mul, hT₀] at hw1
    have hu0 : u = 0 := by
      funext k
      have := congrFun hw1 k
      simp [Matrix.mulVec, dotProduct, Matrix.one_apply, apply_ite g] at this
      rcases this with h | h
      · exact absurd h hr₀
      · exact h
    rw [← hu, hu0, Matrix.mulVec_zero])
  let Q : Matrix a a R := r₀ • (1 : Matrix a a R) - S * T₀ * D₀
  have hQS : Q * S = 0 := by
    simp only [Q, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc, hT₀,
      Matrix.mul_smul, Matrix.mul_one, sub_self]
  have hDQ : r₁ • (D₀ * Q) = 0 := by
    have h1 : T₀ * (D₀ * Q) = 0 := by
      have : T₀ * (D₀ * (S * T₀ * D₀)) = (T₀ * (D₀ * S)) * (T₀ * D₀) := by
        simp only [Matrix.mul_assoc]
      simp only [Q, Matrix.mul_sub, this, hT₀, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
        Matrix.one_mul, sub_self]
    have h2 : D₁ * (D₀ * Q) = 0 := by rw [← Matrix.mul_assoc, h0, Matrix.zero_mul]
    have h3 : Matrix.fromRows T₀ D₁ * (D₀ * Q) = 0 := by
      rw [Matrix.fromRows_mul, h1, h2, Matrix.fromRows_zero]
    calc r₁ • (D₀ * Q) = (T₁ * Matrix.fromRows T₀ D₁) * (D₀ * Q) := by
          rw [hT₁, Matrix.smul_mul, Matrix.one_mul]
      _ = 0 := by rw [Matrix.mul_assoc, h3, Matrix.mul_zero]
  let t := {j : a // j ∉ Set.range s}
  let e : Fin (Fintype.card t) ≃ t := (Fintype.equivFin t).symm
  let f : Fin (Fintype.card t) → a := fun i => (e i).1
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hfs : ∀ i k, f i ≠ s k := fun i k h => (e i).2 ⟨k, h.symm⟩
  let E : Matrix a (Fin (Fintype.card t)) R := (1 : Matrix a a R).submatrix id f
  have hEE : E.transpose * E = 1 := by
    ext i j
    simp [E, Matrix.mul_apply, Matrix.one_apply, hf.eq_iff]
  have hES : E.transpose * S = 0 := by
    ext i j
    simp [E, S, Matrix.mul_apply, Matrix.one_apply, hfs]
  have hQE : Q * E * E.transpose = Q := by
    ext i j
    have hQE' : Q * E = Q.submatrix id f := by
      ext i j
      simp [E, Matrix.mul_apply, Matrix.one_apply]
    rw [hQE']
    by_cases hj : j ∈ Set.range s
    · obtain ⟨k, rfl⟩ := hj
      have : Q i (s k) = (Q * S) i k := by
        simp [S, Matrix.mul_apply, Matrix.one_apply]
      rw [this, hQS]
      simp [E, Matrix.mul_apply, Matrix.one_apply, hfs]
    · obtain ⟨k, hk⟩ : ∃ k, f k = j := ⟨e.symm ⟨j, hj⟩, by simp [f]⟩
      subst hk
      simp [E, Matrix.mul_apply, Matrix.one_apply, hf.eq_iff]
  refine ⟨r₁ * r₀, _, r₁ • (Q * E), E.transpose, r₁ • (S * T₀), ?_, ?_, ?_, ?_⟩
  · rw [map_mul]; exact mul_ne_zero hr₁ hr₀
  · rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.smul_mul, hDQ, Matrix.zero_mul]
  · have : E.transpose * (S * T₀ * D₀ * E) = (E.transpose * S) * (T₀ * D₀ * E) := by
      simp only [Matrix.mul_assoc]
    simp only [Q, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, this, hES, Matrix.zero_mul,
      sub_zero, Matrix.smul_mul, Matrix.one_mul, hEE, smul_smul]
  · rw [Matrix.smul_mul, Matrix.smul_mul, hQE, ← smul_add, mul_smul]
    simp only [Q, sub_add_cancel]

theorem exists_matrix_basis_ker_of_exact_at_point :
    ∀ (R K : Type) [CommRing R] [Field K] (g₀ : R →+* K) (a b c : ℕ) (D₀ : Matrix (Fin b) (Fin a) R) (D₁ : Matrix (Fin c) (Fin b) R), D₁ * D₀ = 0 → (∀ w : Fin b → K, (D₁.map g₀).mulVec w = 0 → ∃ v, (D₀.map g₀).mulVec v = w) → ∃ (r : R) (n : ℕ) (B : Matrix (Fin a) (Fin n) R), g₀ r ≠ 0 ∧ D₀ * B = 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g r) → ∀ v : Fin a → R', (D₀.map g).mulVec v = 0 → ∃! z : Fin n → R', (B.map g).mulVec z = v := by
  intro R K _ _ g₀ a b c D₀ D₁ h0 hex
  obtain ⟨r, n, B, C, H, hr, hB, hCB, hBC⟩ := exists_kernel_certificate g₀ D₀ D₁ h0 hex
  refine ⟨r, n, B, hr, hB, ?_⟩
  intro R' _ g hu v hv
  obtain ⟨u, hu⟩ := hu
  have hone : ∀ (m : ℕ) (x : Fin m → R'),
      ((r • (1 : Matrix (Fin m) (Fin m) R)).map g).mulVec x = g r • x := by
    intro m x
    funext k
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply, apply_ite g]
  have h1 : ∀ z : Fin n → R', (C.map g).mulVec ((B.map g).mulVec z) = (u : R') • z := by
    intro z
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hCB, hone, hu]
  have h2 : (B.map g).mulVec ((C.map g).mulVec v) = (u : R') • v := by
    rw [hu, ← hone, ← hBC, Matrix.map_add _ (map_add g), Matrix.add_mulVec, Matrix.map_mul,
      Matrix.map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero,
      add_zero]
  refine ⟨((u⁻¹ : R'ˣ) : R') • (C.map g).mulVec v, ?_, ?_⟩
  · show (B.map g).mulVec _ = v
    rw [Matrix.mulVec_smul, h2, smul_smul, Units.inv_mul, one_smul]
  · intro z hz
    rw [← hz, h1, smul_smul, Units.inv_mul, one_smul]

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem sec_eq_zero_of_chart {X : Scheme.{0}} [IsIntegral X] (N : LB X) (s : LB.Sec N)
    (j : N.ι) (x : X) (hx : x ∈ N.U j) (hj : s.f j = 0) (i : N.ι) : s.f i = 0 := by
  by_cases hi : (N.U i : Set X).Nonempty
  · have hij : ((N.U i ⊓ N.U j : X.Opens) : Set X).Nonempty :=
      nonempty_preirreducible_inter (N.U i).isOpen (N.U j).isOpen hi ⟨x, hx⟩
    have : Nonempty (N.U i ⊓ N.U j : X.Opens) := hij.to_subtype
    have h := s.compat i j
    rw [hj, map_zero, mul_zero] at h
    apply map_injective_of_isIntegral X (homOfLE (inf_le_left : N.U i ⊓ N.U j ≤ N.U i))
    rw [map_zero]
    exact h
  · have : N.U i = ⊥ := by
      ext1
      simpa using Set.not_nonempty_iff_eq_empty.1 hi
    have : Subsingleton Γ(X, N.U i) := by rw [this]; infer_instance
    exact Subsingleton.elim _ _

theorem eq_zero_of_mem_pow_span {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (U : X.Opens) (x : X) (hx : x ∈ U) (a b : Γ(X, U)) (ha : x ∉ X.basicOpen a)
    (hb : ∀ e : ℕ, b ∈ Ideal.span {a} ^ e) : b = 0 := by
  apply germ_injective_of_isIntegral X x hx
  rw [map_zero]
  rw [X.mem_basicOpen a x hx] at ha
  have hI : Ideal.span {(X.presheaf.germ U x hx).hom a} ≠ ⊤ := by
    rwa [Ne, Ideal.span_singleton_eq_top]
  have h := Ideal.iInf_pow_eq_bot_of_isLocalRing _ hI
  rw [← Ideal.mem_bot, ← h, Ideal.mem_iInf]
  intro e
  have := Ideal.mem_map_of_mem (X.presheaf.germ U x hx).hom (hb e)
  rwa [Ideal.map_pow, Ideal.map_span, Set.image_singleton] at this

theorem sec_eq_zero_of_dvd_pow_uniformiser :
    (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f →
      GeometricallyIntegral f) → Semi.lemmaBSt.{0} := by
  intro H V _ _ _ G _ _ _ _ _ _ N hN s π hπ hs
  have : GeometricallyIntegral G.hom := H _ _ _ inferInstance inferInstance
  have : IsIntegral G.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian G.hom
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  obtain ⟨x, hx⟩ := G.hom.surjective (IsLocalRing.closedPoint V)
  obtain ⟨j, hj⟩ : ∃ j, x ∈ N.U j := by
    have : x ∈ ⨆ i, N.U i := by rw [hN.cover]; trivial
    exact Opens.mem_iSup.1 this
  refine sec_eq_zero_of_chart N s j x hj ?_
  refine eq_zero_of_mem_pow_span (N.U j) x hj _ _ ?_ (hs j)
  intro h
  have h2 := ((Scheme.basicOpen_res G.left _ (homOfLE (le_top :
    N.U j ≤ G.hom ⁻¹ᵁ ⊤)).op).le h).2
  have h3 : x ∈ G.hom ⁻¹ᵁ (Spec (CommRingCat.of V)).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of V)).inv π) := by
    rw [Scheme.preimage_basicOpen]
    exact h2
  rw [basicOpen_eq_of_affine] at h3
  have h4 : G.hom x ∈ PrimeSpectrum.basicOpen π := h3
  rw [hx] at h4
  exact h4 ((IsLocalRing.mem_maximalIdeal π).2 hπ.not_isUnit)

end GlobalTheory
end
