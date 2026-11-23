module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Algebra.Module.Projective
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
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
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

@[expose] public section

section

open scoped NNReal

namespace GlobalTheory

open Matrix

theorem echelon_projector_frobenius (l : ℕ) [Fact l.Prime] (C : Type) [Field C] [CharP C l]
    (d : ℕ) (Y A : Matrix (Fin d) (Fin d) C) (hA : A.det ≠ 0)
    (hY : Y.map (frobenius C l) = Y * A) :
    ∃ (I : Finset (Fin d)) (Q Λ : Matrix (Fin d) (Fin d) C), Y * Q = 0 ∧
      (∀ v, Y.mulVec v = 0 → Q.mulVec v = v) ∧
      (∀ i ∈ I, ∀ j, Q i j = if i = j then 1 else 0) ∧ (∀ i, ∀ j ∉ I, Q i j = 0) ∧
      Q = A * Q.map (frobenius C l) * Λ := by
  classical
  set N : Submodule C (Fin d → C) := LinearMap.ker (Matrix.toLin' Y) with hN
  let e : Fin d → (Fin d → C) := fun k => Pi.single k 1

  have hsupp : ∀ (S : Set (Fin d)) (v : Fin d → C), (∀ i, i ∉ S → v i = 0) →
      v ∈ Submodule.span C (e '' S) := by
    intro S v hv
    rw [show v = ∑ k, Pi.single k (v k) from (Finset.univ_sum_single v).symm]
    refine Submodule.sum_mem _ fun k _ => ?_
    by_cases hk : k ∈ S
    · have : Pi.single k (v k) = v k • e k := by
        ext i; simp [e, Pi.single_apply]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)
    · rw [hv k hk, Pi.single_zero]; exact Submodule.zero_mem _
  have hspan : Submodule.span C (Set.range (N.mkQ ∘ e)) = ⊤ := by
    rw [Set.range_comp, ← Submodule.map_span]
    have : Submodule.span C (Set.range e) = ⊤ := by
      rw [eq_top_iff]; intro v _
      have := hsupp Set.univ v (fun i hi => absurd (Set.mem_univ i) hi)
      rwa [Set.image_univ] at this
    rw [this, Submodule.map_top, Submodule.range_mkQ]
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' C (N.mkQ ∘ e)
  have : Finite κ := Finite.of_injective a ha
  have := Fintype.ofFinite κ
  set W : Submodule C (Fin d → C) := Submodule.span C (e '' Set.range a) with hW
  have hWeq : W = Submodule.span C (Set.range (e ∘ a)) := by rw [hW, Set.range_comp]
  have hWcoord : ∀ w ∈ W, ∀ i, i ∉ Set.range a → w i = 0 := by
    intro w hw i hi
    refine Submodule.span_induction (p := fun w _ => w i = 0) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨k, ⟨m, rfl⟩, rfl⟩
      have : i ≠ a m := fun h => hi ⟨m, h.symm⟩
      simp [e, Pi.single_apply, this]
    · simp
    · intro x y _ _ hx hy; simp [hx, hy]
    · intro c x _ hx; simp [hx]
  have hc : IsCompl N W := by
    constructor
    · rw [disjoint_iff, eq_bot_iff]
      intro y ⟨hyN, hyW⟩
      rw [hWeq] at hyW
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun C).mp hyW
      have h0 : ∑ j, c j • (N.mkQ ∘ e ∘ a) j = 0 := by

        simp only [Function.comp_apply, ← map_smul, ← map_sum]
        exact (Submodule.Quotient.mk_eq_zero N).mpr hyN
      have hc0 := Fintype.linearIndependent_iff.mp hli c h0
      simp [hc0]
    · rw [codisjoint_iff, ← Submodule.map_mkQ_eq_top, hWeq, Submodule.map_span, ← Set.range_comp]
      exact hsp.trans hspan
  set P := N.projection W hc with hP
  set Q : Matrix (Fin d) (Fin d) C := LinearMap.toMatrix' P with hQ
  have hQv : ∀ v, Q *ᵥ v = P v := fun v => by
    rw [← Matrix.toLin'_apply, hQ, Matrix.toLin'_toMatrix']
  have hPN : ∀ v, P v ∈ N := fun v => Submodule.projection_apply_mem hc v
  have hmemN : ∀ v, v ∈ N ↔ Y *ᵥ v = 0 := fun v => by
    rw [hN, LinearMap.mem_ker, Matrix.toLin'_apply]
  have key : ∀ X Z : Matrix (Fin d) (Fin d) C, (∀ v, X *ᵥ v = Z *ᵥ v) → X = Z :=
    fun X Z h => Matrix.toLin'.injective (LinearMap.ext fun v => by simpa [Matrix.toLin'_apply] using h v)
  have hYQ : Y * Q = 0 := key _ _ fun v => by
    rw [← Matrix.mulVec_mulVec, hQv, Matrix.zero_mulVec]; exact (hmemN _).mp (hPN v)
  set I : Finset (Fin d) := Finset.univ.filter (fun i => i ∉ Set.range a) with hI
  have hmemI : ∀ i, i ∈ I ↔ i ∉ Set.range a := fun i => by simp [hI]
  have hrow : ∀ i ∈ I, ∀ j, Q i j = if i = j then 1 else 0 := by
    intro i hi j
    rw [hQ, LinearMap.toMatrix'_apply]
    have h1 := hWcoord _ (Submodule.sub_projection_mem hc (Pi.single j (1 : C))) i ((hmemI i).mp hi)
    rw [Pi.sub_apply, sub_eq_zero, Pi.single_apply] at h1
    rw [← hP] at h1
    exact h1.symm
  have hcol : ∀ i, ∀ j ∉ I, Q i j = 0 := by
    intro i j hj
    rw [hmemI, not_not] at hj
    rw [hQ, LinearMap.toMatrix'_apply]
    have : Pi.single j (1 : C) ∈ W := Submodule.subset_span ⟨j, hj, rfl⟩
    rw [Submodule.projection_apply_of_mem_right hc this]; rfl

  set M : Matrix (Fin d) (Fin d) C := A * Q.map (frobenius C l) with hM
  have hYM : Y * M = 0 := by
    rw [hM, ← mul_assoc, ← hY, ← Matrix.map_mul, hYQ, Matrix.map_zero _ (map_zero _)]
  have hrangeN : LinearMap.range (Matrix.toLin' M) ≤ N := by
    rintro _ ⟨v, rfl⟩
    rw [hmemN, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hYM, Matrix.zero_mulVec]
  have hkerW : LinearMap.ker (Matrix.toLin' M) ≤ W := by
    intro v hv
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, hM, ← Matrix.mulVec_mulVec] at hv
    have hAu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
    have h0 : Q.map (frobenius C l) *ᵥ v = 0 := by
      have := congrArg (fun x => A⁻¹ *ᵥ x) hv
      simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at this
      rwa [← mul_assoc, Matrix.nonsing_inv_mul A hAu, one_mul] at this
    have := hsupp (Set.range a) v (fun i hi => by
      have hi' : i ∈ I := (hmemI i).mpr hi
      have h2 := congrFun h0 i
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hrow i hi', Pi.zero_apply] at h2
      simpa [apply_ite] using h2)
    rwa [← hW] at this
  have hrange : LinearMap.range (Matrix.toLin' M) = N := by
    refine Submodule.eq_of_le_of_finrank_le hrangeN ?_
    have h1 := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' M)
    have h2 := Submodule.finrank_add_eq_of_isCompl hc
    have h3 := Submodule.finrank_mono hkerW
    omega
  have hex : ∀ j, ∃ w, Matrix.toLin' M w = P (Pi.single j 1) := fun j => by
    have : P (Pi.single j 1) ∈ LinearMap.range (Matrix.toLin' M) := hrange ▸ hPN _
    exact this
  choose lam hlam using hex
  refine ⟨I, Q, Matrix.of fun k j => lam j k, hYQ, fun v hv => ?_, hrow, hcol, ?_⟩
  · rw [hQv]; exact Submodule.projection_apply_of_mem_left hc ((hmemN v).mpr hv)
  · ext i j
    rw [← hM, Matrix.mul_apply]
    have := congrFun (hlam j) i
    rw [Matrix.toLin'_apply] at this
    rw [hQ, LinearMap.toMatrix'_apply, ← this]
    simp [Matrix.mulVec, dotProduct]

end GlobalTheory
end

section

open Polynomial

namespace GlobalTheory.SqZeroPow

theorem dual_decomp {R : Type} [CommRing R] (b : DualNumber R) (r s : R) (h : r * s = b.fst) :
    TrivSqZeroExt.inl b.snd * (DualNumber.eps : DualNumber R)
      + TrivSqZeroExt.inl s * TrivSqZeroExt.inl r = b := by
  ext <;> simp [← h, mul_comm]

theorem dual_fst_of_eps_mul {R : Type} [CommRing R] (f : DualNumber R) (r : R) (n : ℕ)
    (h : (DualNumber.eps : DualNumber R) * (TrivSqZeroExt.inl r) ^ n * f = 0) :
    r ^ n * f.fst = 0 := by
  have hs := congrArg TrivSqZeroExt.snd h
  simpa [mul_comm] using hs

theorem dual_inl_pow {R : Type} [CommRing R] (r : R) (n : ℕ) (h : r ^ n = 0) :
    (TrivSqZeroExt.inl r : DualNumber R) ^ n = 0 := by
  rw [TrivSqZeroExt.inl_pow, h, TrivSqZeroExt.inl_zero]

theorem exists_ring (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (m : ℕ) (hm : 0 < m) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra O B) (j : A →ₐ[O] B) (π : B →ₐ[O] A) (x y : B),
      (∀ a, π (j a) = a) ∧ (∀ b, π b = 0 → b ∈ Ideal.span {x, y}) ∧ π x = 0 ∧ π y = 0 ∧
      x * x = 0 ∧ y ^ m = 0 ∧ ∀ f, x * y ^ (m - 1) * f = 0 → π f = 0 := by
  classical
  have h0 : (X ^ m : A[X]).eval₂ (AlgHom.id O A : A →+* A) 0 = 0 := by
    simp [zero_pow (Nat.pos_iff_ne_zero.mp hm)]
  obtain ⟨g, hg⟩ : ∃ g : AdjoinRoot (X ^ m : A[X]) →ₐ[O] A,
      ∀ p : A[X], g (AdjoinRoot.mk _ p) = p.coeff 0 :=
    ⟨AdjoinRoot.liftAlgHom _ (AlgHom.id O A) 0 h0, fun p => by
      rw [AdjoinRoot.liftAlgHom_mk, Polynomial.eval₂_at_zero]
      rfl⟩
  have hroot : (AdjoinRoot.root (X ^ m : A[X])) ^ m = 0 := by
    have hself : AdjoinRoot.mk (X ^ m : A[X]) (X ^ m) = 0 := AdjoinRoot.mk_self
    rwa [map_pow, AdjoinRoot.mk_X] at hself
  refine ⟨DualNumber (AdjoinRoot (X ^ m : A[X])), inferInstance, inferInstance,
    (TrivSqZeroExt.inlAlgHom O _ _).comp (IsScalarTower.toAlgHom O A _),
    g.comp (TrivSqZeroExt.fstHom O _ _),
    DualNumber.eps, TrivSqZeroExt.inl (AdjoinRoot.root _), ?_, ?_, ?_, ?_,
    DualNumber.eps_mul_eps, dual_inl_pow _ _ hroot, ?_⟩
  · intro a
    simp only [AlgHom.comp_apply, TrivSqZeroExt.inlAlgHom_apply, TrivSqZeroExt.fstHom_apply,
      TrivSqZeroExt.fst_inl, IsScalarTower.toAlgHom_apply]
    rw [AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C, hg, Polynomial.coeff_C_zero]
  · intro b hb
    simp only [AlgHom.comp_apply, TrivSqZeroExt.fstHom_apply] at hb
    obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective b.fst
    rw [← hp, hg] at hb
    obtain ⟨q, rfl⟩ := Polynomial.X_dvd_iff.mpr hb
    have hq : AdjoinRoot.root (X ^ m : A[X]) * AdjoinRoot.mk _ q = b.fst := by
      rw [← hp, map_mul, AdjoinRoot.mk_X]
    have e := dual_decomp b _ _ hq
    rw [← e]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span ?_))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ?_)) <;> simp
  · simp only [AlgHom.comp_apply, TrivSqZeroExt.fstHom_apply, DualNumber.fst_eps, map_zero]
  · simp only [AlgHom.comp_apply, TrivSqZeroExt.fstHom_apply, TrivSqZeroExt.fst_inl]
    rw [← AdjoinRoot.mk_X, hg, Polynomial.coeff_X_zero]
  · intro f hf
    have h1 := dual_fst_of_eps_mul f _ (m - 1) hf
    simp only [AlgHom.comp_apply, TrivSqZeroExt.fstHom_apply]
    obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective f.fst
    have e : AdjoinRoot.root (X ^ m : A[X]) ^ (m - 1) * AdjoinRoot.mk _ p
        = AdjoinRoot.mk _ (X ^ (m - 1) * p) := by
      rw [map_mul, map_pow, AdjoinRoot.mk_X]
    rw [← hp, e, AdjoinRoot.mk_eq_zero, Polynomial.X_pow_dvd_iff] at h1
    have h2 := h1 (m - 1) (Nat.sub_lt hm Nat.one_pos)
    rw [Polynomial.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self] at h2
    rw [← hp, hg]
    exact h2

end GlobalTheory.SqZeroPow
end

section

namespace GlobalTheory.InvariantRightInverse

theorem exists_rightInverse_subfield {L : Type} [Field L] (K : Subfield L) {N b : Type}
    [Fintype N] [DecidableEq b] (κ : Matrix b N L) (Y : Matrix N b L)
    (h : κ * Y = 1) (hκ : ∀ i k, κ i k ∈ K) :
    ∃ Λ : Matrix N b L, κ * Λ = 1 ∧ ∀ k j, Λ k j ∈ K := by
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K L)
    (LinearMap.ker_eq_bot.mpr (fun x y hxy => Subtype.ext hxy))
  have hπ' : ∀ x : K, π (x : L) = x := fun x => LinearMap.congr_fun hπ x
  refine ⟨Matrix.of fun k j => (π (Y k j) : L), ?_, fun k j => (π (Y k j)).2⟩
  ext i j
  have h1 : ∑ k, κ i k * Y k j = (1 : Matrix b b L) i j := by
    rw [← h, Matrix.mul_apply]
  have h2 : ∀ k, κ i k * (π (Y k j) : L) = (π (κ i k * Y k j) : L) := by
    intro k
    have := π.map_smul (⟨κ i k, hκ i k⟩ : K) (Y k j)
    have e : (⟨κ i k, hκ i k⟩ : K) • Y k j = κ i k * Y k j := rfl
    rw [e] at this
    rw [this]
    rfl
  have h3 : (1 : Matrix b b L) i j ∈ K := by
    rw [Matrix.one_apply]
    split_ifs
    · exact K.one_mem
    · exact K.zero_mem
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply]
  calc ∑ k, κ i k * (π (Y k j) : L) = ∑ k, (π (κ i k * Y k j) : L) :=
        Finset.sum_congr rfl (fun k _ => h2 k)
    _ = ((∑ k, π (κ i k * Y k j) : K) : L) := by push_cast; rfl
    _ = (π (∑ k, κ i k * Y k j) : L) := by rw [map_sum]
    _ = (1 : Matrix b b L) i j := by
        rw [h1]
        exact congrArg Subtype.val (hπ' ⟨_, h3⟩)

theorem exists_invariant_rightInverse_field {L : Type} [Field L] (G : Type)
    (act : G → L →+* L) (N b : Type) [Fintype N] [DecidableEq b]
    (κ : Matrix b N L) (Y : Matrix N b L) (h : κ * Y = 1)
    (hκ : ∀ g : G, Matrix.map κ (⇑(act g) : L → L) = κ) :
    ∃ Λ : Matrix N b L, κ * Λ = 1 ∧ ∀ g : G, Matrix.map Λ (⇑(act g) : L → L) = Λ := by
  have hK : ∀ x : L, x ∈ (⨅ g : G, RingHom.eqLocusField (act g) (RingHom.id L)) ↔
      ∀ g, act g x = x := by
    intro x
    rw [Subfield.mem_iInf]
    exact Iff.rfl
  obtain ⟨Λ, h1, h2⟩ := exists_rightInverse_subfield
    (⨅ g : G, RingHom.eqLocusField (act g) (RingHom.id L)) κ Y h
    (fun i k => (hK _).2 (fun g => congrFun (congrFun (hκ g) i) k))
  refine ⟨Λ, h1, fun g => ?_⟩
  ext k j
  exact (hK _).1 (h2 k j) g

theorem exists_invariant_rightInverse :
    ∀ (L : Type) [inst : CommRing L], IsField L → ∀ (G : Type) (act : G → L →+* L) (N b : Type) [inst_1 : Fintype N] [DecidableEq N] [Fintype b] [inst_4 : DecidableEq b] (κ : Matrix b N L) (Y : Matrix N b L), κ * Y = (1 : Matrix b b L) → (∀ (g : G), Matrix.map κ (⇑(act g) : L → L) = κ) → ∃ (Λ : Matrix N b L), κ * Λ = (1 : Matrix b b L) ∧ ∀ (g : G), Matrix.map Λ (⇑(act g) : L → L) = Λ := by
  intro L _ hL G act N b _ _ _ _ κ Y h hκ
  letI : Field L := hL.toField
  exact exists_invariant_rightInverse_field G act N b κ Y h hκ

end GlobalTheory.InvariantRightInverse
end

section

namespace GlobalTheory.ProofStatement

theorem main : ∀ (l : ℕ) [hl : Fact (Nat.Prime l)] (a : AlgebraicClosure (ZMod l)), a ≠ (0 : AlgebraicClosure (ZMod l)) → ∃ (m : ℕ), (0 : ℕ) < m ∧ ¬l ∣ m ∧ a ^ m = (1 : AlgebraicClosure (ZMod l)) := by
  intro l hl a ha
  set K := IntermediateField.adjoin (ZMod l) ({a} : Set (AlgebraicClosure (ZMod l))) with hK
  haveI : FiniteDimensional (ZMod l) K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a)
  haveI : Finite K := Module.finite_of_finite (ZMod l)
  letI : Fintype K := Fintype.ofFinite K
  haveI : CharP K l := charP_of_injective_algebraMap (algebraMap (ZMod l) K).injective l
  obtain ⟨n, _, hcard⟩ := FiniteField.card K l
  have ha' : (⟨a, IntermediateField.mem_adjoin_simple_self (ZMod l) a⟩ : K) ≠ 0 := by
    intro h; apply ha; exact congrArg Subtype.val h
  have hpow := FiniteField.pow_card_sub_one_eq_one _ ha'
  have hl1 : 2 ≤ l := hl.out.two_le
  have hn : 1 ≤ (n : ℕ) := n.pos
  have hq : l ≤ l ^ (n : ℕ) := Nat.le_self_pow (by omega) l
  refine ⟨Fintype.card K - 1, by omega, ?_, ?_⟩
  · rw [hcard]
    intro hd
    have h2 : l ∣ l ^ (n : ℕ) := dvd_pow_self l (by omega)
    have h3 : l ∣ l ^ (n : ℕ) - (l ^ (n : ℕ) - 1) := Nat.dvd_sub h2 hd
    rw [Nat.sub_sub_self (by omega)] at h3
    exact hl.out.one_lt.ne' (Nat.dvd_one.mp h3)
  · have := congrArg Subtype.val hpow
    simpa using this

end GlobalTheory.ProofStatement
end

section

open Polynomial

namespace GlobalTheory

theorem exists_linearIndependent_of_pow_le_card_zmod (l : ℕ) [Fact l.Prime] {Q ι : Type} [AddCommGroup Q] [Module (ZMod l) Q]
    (Z : Finset ι) (w : ι → Q) (hinj : Set.InjOn w Z) (h : ℕ) (hcard : l ^ h ≤ Z.card) :
    ∃ x : Fin h → ι, (∀ a, x a ∈ Z) ∧ LinearIndependent (ZMod l) (fun a => w (x a)) := by
  classical
  have hl1 : 1 < l := (Fact.out : l.Prime).one_lt
  have hs : (Z.image w).card = Z.card := Finset.card_image_of_injOn hinj
  obtain ⟨b, hbs, hspan, hli⟩ := exists_linearIndependent (ZMod l) ((Z.image w : Finset Q) : Set Q)
  have hbfin : b.Finite := (Finset.finite_toSet _).subset hbs
  haveI : Fintype b := hbfin.fintype
  have hrange : ∀ y ∈ Z.image w, ∃ f : b → ZMod l, ∑ c, f c • (c : Q) = y := by
    intro y hy
    have hy' : y ∈ Submodule.span (ZMod l) b := by
      rw [hspan]; exact Submodule.subset_span (by exact_mod_cast hy)
    rw [← Subtype.range_coe (s := b)] at hy'
    exact (Submodule.mem_span_range_iff_exists_fun (ZMod l)).1 hy'
  have hle : (Z.image w).card ≤ l ^ Fintype.card b := by
    have h3 : (Z.image w).card ≤ (Finset.univ.image (fun f : b → ZMod l => ∑ c, f c • (c : Q))).card := by
      apply Finset.card_le_card
      intro y hy
      obtain ⟨f, hf⟩ := hrange y hy
      exact Finset.mem_image.2 ⟨f, Finset.mem_univ _, hf⟩
    calc _ ≤ _ := h3
      _ ≤ (Finset.univ : Finset (b → ZMod l)).card := Finset.card_image_le
      _ = l ^ Fintype.card b := by rw [Finset.card_univ, Fintype.card_fun, ZMod.card]
  have hhb : h ≤ Fintype.card b := by
    have : l ^ h ≤ l ^ Fintype.card b := hcard.trans (hs ▸ hle)
    exact (Nat.pow_le_pow_iff_right hl1).1 this
  let e : Fin h ↪ b := (Fin.castLEEmb hhb).trans (Fintype.equivFin b).symm.toEmbedding
  have hpre : ∀ c : b, ∃ i ∈ Z, w i = c := fun c => Finset.mem_image.1 (hbs c.2)
  choose g hgZ hgw using hpre
  refine ⟨fun a => g (e a), fun a => hgZ _, ?_⟩
  have hli' : LinearIndependent (ZMod l) (fun a => ((e a : b) : Q)) := hli.comp e e.injective
  convert hli' using 1
  funext a
  exact hgw (e a)

theorem ph_a_basis : ∀ (l : ℕ) [Fact l.Prime] (V ι : Type) [AddCommGroup V] (K' : AddSubgroup V) (h : ℕ)
    (Z : Finset ι) (v : ι → V), (∀ x : V, l • x = 0) → l ^ h ≤ Z.card →
    (∀ i ∈ Z, ∀ i' ∈ Z, i ≠ i' → v i - v i' ∉ K') →
    ∃ x : Fin h → ι, (∀ a, x a ∈ Z) ∧ ∀ n : Fin h → ℕ, ∑ a, n a • v (x a) ∈ K' → ∀ a, l ∣ n a := by
  intro l _ V ι _ K' h Z v hl hcard hdist
  have hQ : ∀ y : V ⧸ K', l • y = 0 := by
    intro y
    induction y using QuotientAddGroup.induction_on with
    | H z => rw [← QuotientAddGroup.mk_nsmul, hl z]; rfl
  letI : Module (ZMod l) (V ⧸ K') := AddCommGroup.zmodModule hQ
  have hinj : Set.InjOn (fun i => (v i : V ⧸ K')) Z := by
    intro i hi i' hi' he
    by_contra hne
    exact hdist i hi i' hi' hne ((QuotientAddGroup.eq_iff_sub_mem).1 he)
  obtain ⟨x, hxZ, hli⟩ := exists_linearIndependent_of_pow_le_card_zmod l Z (fun i => (v i : V ⧸ K')) hinj h hcard
  refine ⟨x, hxZ, ?_⟩
  intro n hn a
  have hm : QuotientAddGroup.mk' K' (∑ a, n a • v (x a)) = 0 := (QuotientAddGroup.eq_zero_iff _).2 hn

  rw [map_sum] at hm
  simp only [map_nsmul, QuotientAddGroup.mk'_apply] at hm
  have hsum : ∑ a, (n a : ZMod l) • ((v (x a) : V ⧸ K')) = 0 := by
    rw [← hm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Nat.cast_smul_eq_nsmul]
  have hz := Fintype.linearIndependent_iff.1 hli (fun a => (n a : ZMod l)) hsum a
  exact (ZMod.natCast_eq_zero_iff _ _).1 hz

end GlobalTheory
end

section

namespace GlobalTheory

theorem projective_compHom_of_free_of_finite_free :
    ∀ (Z S A D : Type) [CommRing Z] [CommRing S] [CommRing A] [AddCommGroup D] [Module A D] (z : Z →+* S) (a : S →+* A) (N : Submodule A D) (q : ℕ) (x : Fin q → D), (∀ y, y ∈ N ↔ ∃ s : Fin q → S, y = ∑ i, a (s i) • x i) → (∀ s : Fin q → S, ∑ i, a (s i) • x i = 0 → s = 0) → (∃ (d : ℕ) (w : Fin d → S), ∀ y : S, ∃! c : Fin d → Z, y = ∑ i, z (c i) * w i) → @Module.Projective Z _ ↥N _ (Module.compHom _ (a.comp z)) := by
  intro Z S A D _ _ _ _ _ z a N q x hN hli ⟨d, w, hw⟩
  letI : Module Z N := Module.compHom _ (a.comp z)
  have hsm : ∀ (r : Z) (n : N), ((r • n : N) : D) = a (z r) • (n : D) := fun _ _ => rfl
  let f : (Fin q → Fin d → Z) →ₗ[Z] N :=
    { toFun := fun c => ⟨∑ i, a (∑ m, z (c i m) * w m) • x i, (hN _).2 ⟨_, rfl⟩⟩
      map_add' := fun c c' => by
        apply Subtype.ext
        simp [add_mul, Finset.sum_add_distrib, add_smul]
      map_smul' := fun r c => by
        apply Subtype.ext
        rw [hsm]
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, Finset.smul_sum,
          smul_smul, mul_assoc, ← Finset.mul_sum] }
  have hinj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro c hc
    have h1 := hli (fun i => ∑ m, z (c i m) * w m) (congrArg Subtype.val hc)
    funext i
    have h2 : (0 : S) = ∑ m, z (c i m) * w m := (congrFun h1 i).symm
    exact (hw 0).unique h2 (by simp)
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨s, rfl⟩ := (hN y).1 hy
    choose c hc _ using fun i => hw (s i)
    refine ⟨c, Subtype.ext ?_⟩
    change ∑ i, a (∑ m, z (c i m) * w m) • x i = ∑ i, a (s i) • x i
    exact Finset.sum_congr rfl fun i _ => by rw [← hc i]
  exact Module.Projective.of_equiv (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩)

end GlobalTheory
end
