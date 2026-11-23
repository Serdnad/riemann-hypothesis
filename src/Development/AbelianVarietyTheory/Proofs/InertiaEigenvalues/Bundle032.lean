module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

@[expose] public section

section

namespace GlobalTheory

open Submodule

theorem antitone_filtration_exists_adapted_linearIndep_set {L M : Type} [Field L] [AddCommGroup M] [Module L M]
    (A : ℤ → Submodule L M) (hA : Antitone A) (hi : ℤ) (hhi : A hi = ⊥) (n : ℕ) :
    ∃ (s : Set M) (k : M → ℤ), LinearIndepOn L id s ∧ (∀ x ∈ s, hi - n ≤ k x) ∧
      ∀ a, hi - n ≤ a → A a = span L {x | x ∈ s ∧ a ≤ k x} := by
  classical
  induction n with
  | zero =>
    refine ⟨∅, fun _ => hi, linearIndepOn_empty L id, fun x hx => hx.elim, fun a ha => ?_⟩
    simp only [Set.mem_empty_iff_false, false_and, Set.ofPred_false, Submodule.span_empty]
    rw [eq_bot_iff, ← hhi]
    exact hA (by simpa using ha)
  | succ n ih =>
    obtain ⟨s, k, hs, hk, hspan⟩ := ih
    have hsA : s ⊆ A (hi - (n + 1 : ℕ)) := by
      intro x hx
      have hx' : x ∈ A (hi - n) := by
        rw [hspan _ le_rfl]
        exact Submodule.subset_span ⟨hx, hk x hx⟩
      exact hA (by push_cast; omega) hx'
    obtain ⟨t, htA, hst, hAt, ht⟩ := exists_linearIndepOn_id_extension hs hsA
    have hkt : ∀ x ∈ t, hi - ((n + 1 : ℕ) : ℤ) ≤ (if x ∈ s then k x else hi - (n + 1 : ℕ)) := by
      intro x _
      split_ifs with h
      · have := hk x h
        push_cast at this ⊢
        omega
      · exact le_rfl
    refine ⟨t, fun x => if x ∈ s then k x else hi - (n + 1 : ℕ), ht, hkt, fun a ha => ?_⟩
    rcases eq_or_lt_of_le ha with h | h
    · subst h
      have hset : {x | x ∈ t ∧ hi - ((n + 1 : ℕ) : ℤ) ≤
          (if x ∈ s then k x else hi - (n + 1 : ℕ))} = t := by
        ext x
        exact ⟨fun hx => hx.1, fun hx => ⟨hx, hkt x hx⟩⟩
      rw [hset]
      exact le_antisymm (fun x hx => hAt hx) (Submodule.span_le.2 htA)
    · have ha' : hi - (n : ℤ) ≤ a := by
        push_cast at h
        omega
      rw [hspan a ha']
      congr 1
      ext x
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hx, hkx⟩
        exact ⟨hst hx, by rw [if_pos hx]; exact hkx⟩
      · rintro ⟨hx, hkx⟩
        split_ifs at hkx with hxs
        · exact ⟨hxs, hkx⟩
        · push_cast at h hkx
          omega

theorem filtration_adapted_basis {L M : Type} [Field L] [AddCommGroup M] [Module L M]
    (A : ℤ → Submodule L M) (hA : Antitone A) (hfd : FiniteDimensional L ↥(⨆ a, A a))
    (hsep : ∀ x, (∀ a, x ∈ A a) → x = 0) :
    ∃ (m : ℕ) (d : Fin m → M) (k : Fin m → ℤ), LinearIndependent L d ∧
      ∀ a, A a = Submodule.span L (d '' {i | a ≤ k i}) := by
  classical
  have hle : ∀ a, A a ≤ ⨆ b, A b := fun a => le_iSup A a
  have hfa : ∀ a, FiniteDimensional L (A a) := fun a => Submodule.finiteDimensional_of_le (hle a)
  obtain ⟨a0, ha0⟩ : ∃ a0, ∀ a, Module.finrank L (A a0) ≤ Module.finrank L (A a) := by
    have hex : ∃ m, ∃ a, Module.finrank L (A a) = m := ⟨_, 0, rfl⟩
    obtain ⟨a0, h0⟩ := Nat.find_spec hex
    refine ⟨a0, fun a => ?_⟩
    have h := Nat.find_min' hex ⟨a, rfl⟩
    rw [← h0] at h
    exact h
  have hbot : A a0 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    apply hsep
    intro a
    rcases le_total a a0 with h | h
    · exact hA h hx
    · rw [Submodule.eq_of_le_of_finrank_le (hA h) (ha0 a)]
      exact hx
  obtain ⟨a1, ha1⟩ : ∃ a1, ∀ a, Module.finrank L (A a) ≤ Module.finrank L (A a1) := by
    have hex : ∃ m, ∃ a, Module.finrank L ↥(⨆ b, A b) - Module.finrank L (A a) = m := ⟨_, 0, rfl⟩
    obtain ⟨a1, h1⟩ := Nat.find_spec hex
    refine ⟨a1, fun a => ?_⟩
    have h2 := Nat.find_min' hex ⟨a, rfl⟩
    rw [← h1] at h2
    have h3 := Submodule.finrank_mono (hle a)
    have h4 := Submodule.finrank_mono (hle a1)
    omega
  have htop : ⨆ b, A b = A a1 := by
    refine le_antisymm (iSup_le fun a => ?_) (hle a1)
    rcases le_total a1 a with h | h
    · exact hA h
    · exact (Submodule.eq_of_le_of_finrank_le (hA h) (ha1 a)).symm.le
  obtain ⟨n, hn⟩ : ∃ n : ℕ, a0 - n ≤ a1 := ⟨(a0 - a1).toNat, by omega⟩
  obtain ⟨s, k, hs, hk, hspan⟩ := antitone_filtration_exists_adapted_linearIndep_set A hA a0 hbot n
  have hlow : ∀ a, a ≤ a0 - n → A a = A (a0 - n) := by
    intro a ha
    refine le_antisymm ?_ (hA ha)
    calc A a ≤ ⨆ c, A c := hle a
      _ = A a1 := htop
      _ ≤ A (a0 - n) := hA hn
  have hsU : ∀ x ∈ s, x ∈ (⨆ b, A b : Submodule L M) := by
    intro x hx
    have hx' : x ∈ A (a0 - n) := by
      rw [hspan _ le_rfl]
      exact Submodule.subset_span ⟨hx, hk x hx⟩
    exact hle _ hx'
  have hli : LinearIndependent L (fun x : s => (⟨x, hsU x x.2⟩ : (⨆ b, A b : Submodule L M))) :=
    LinearIndependent.of_comp (⨆ b, A b).subtype hs
  have hfin : s.Finite := Set.finite_coe_iff.1 hli.finite
  have _ := hfin.fintype
  let e : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  refine ⟨Fintype.card s, fun i => (e.symm i : M), fun i => k (e.symm i),
    LinearIndependent.comp hs e.symm e.symm.injective, fun a => ?_⟩
  show A a = Submodule.span L ((fun i => (e.symm i : M)) '' {i | a ≤ k (e.symm i)})
  have himg : (fun i => (e.symm i : M)) '' {i | a ≤ k (e.symm i)} = {x | x ∈ s ∧ a ≤ k x} := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨(e.symm i).2, hi⟩
    · rintro ⟨hx, hkx⟩
      exact ⟨e ⟨x, hx⟩, by simpa using hkx, by simp⟩
  rw [himg]
  rcases le_or_gt (a0 - n) a with h | h
  · exact hspan a h
  · rw [hlow a h.le, hspan _ le_rfl]
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hx, -⟩
      exact ⟨hx, by have := hk x hx; omega⟩
    · rintro ⟨hx, -⟩
      exact ⟨hx, hk x hx⟩

end GlobalTheory
end

section

open NumberField IsDedekindDomain TensorProduct Polynomial

namespace GlobalTheory

theorem exists_tensor_idem_of_algHom (E K E' : Type) [Field E] [CharZero E] [Field K] [Field E']
    [Algebra E K] [Algebra E E'] [FiniteDimensional E E'] (ψ : K ⊗[E] E' →ₐ[K] K) :
    ∃ e : K ⊗[E] E', ψ e = 1 ∧ ∀ a, e * a = algebraMap K (K ⊗[E] E') (ψ a) * e := by
  classical
  set A := K ⊗[E] E'
  let pb := Field.powerBasisOfFiniteOfSeparable E E'
  set θ := pb.gen
  let T : A := Algebra.TensorProduct.includeRight θ
  set α : K := ψ T
  let f : E[X] := minpoly E θ
  let fK : K[X] := f.map (algebraMap E K)
  have hfT : aeval T fK = 0 := by
    rw [aeval_map_algebraMap]
    have : aeval T f = Algebra.TensorProduct.includeRight (aeval θ f) := by
      rw [aeval_algHom_apply]
    rw [this, minpoly.aeval, map_zero]
  have hroot : IsRoot fK α := by
    have h1 : aeval α fK = ψ (aeval T fK) := by
      rw [aeval_algHom_apply]
    rw [hfT, map_zero] at h1
    simpa [IsRoot, aeval_def, eval₂_eq_eval_map] using h1
  have hsep : fK.Separable := Polynomial.Separable.map (p := f) (Algebra.IsSeparable.isSeparable E θ)
  set g : K[X] := fK /ₘ (X - C α)
  have hfac : (X - C α) * g = fK := (mul_divByMonic_eq_iff_isRoot).2 hroot
  have hgα : g.eval α ≠ 0 := by
    have hd := hsep.eval₂_derivative_ne_zero (RingHom.id K) (x := α) (by simpa [eval₂_id] using hroot)
    rw [eval₂_id, ← hfac] at hd
    simpa [derivative_mul] using hd
  let e : A := algebraMap K A (g.eval α)⁻¹ * aeval T g
  have hψg : ψ (aeval T g) = g.eval α := by
    rw [← aeval_algHom_apply]; rfl
  have hψe : ψ e = 1 := by
    have hc : ψ (algebraMap K A (g.eval α)⁻¹) = (g.eval α)⁻¹ := ψ.commutes _
    simp only [e, map_mul, hc, hψg]
    exact inv_mul_cancel₀ hgα
  have hTe : e * T = algebraMap K A (ψ T) * e := by
    have h0 : (T - algebraMap K A α) * aeval T g = 0 := by
      have : aeval T ((X - C α) * g) = (T - algebraMap K A α) * aeval T g := by
        simp [map_mul, map_sub]
      rw [← this, hfac, hfT]
    have h1 : T * aeval T g = algebraMap K A α * aeval T g := by
      rw [sub_mul] at h0; exact sub_eq_zero.1 h0
    simp only [e]
    calc algebraMap K A (g.eval α)⁻¹ * aeval T g * T
        = algebraMap K A (g.eval α)⁻¹ * (T * aeval T g) := by ring
      _ = algebraMap K A α * (algebraMap K A (g.eval α)⁻¹ * aeval T g) := by rw [h1]; ring

  let Q : A → Prop := fun a => e * a = algebraMap K A (ψ a) * e
  have Qmul : ∀ a b, Q a → Q b → Q (a * b) := by
    intro a b ha hb
    show e * (a * b) = algebraMap K A (ψ (a * b)) * e
    rw [map_mul, map_mul, ← mul_assoc, ha, mul_assoc, hb]; ring
  have Qadd : ∀ a b, Q a → Q b → Q (a + b) := by
    intro a b ha hb
    show e * (a + b) = algebraMap K A (ψ (a + b)) * e
    rw [map_add (f := _), map_add (f := _), mul_add, ha, hb, add_mul]
  have Qalg : ∀ k : K, Q (algebraMap K A k) := by
    intro k
    show e * algebraMap K A k = algebraMap K A (ψ (algebraMap K A k)) * e
    rw [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, mul_comm]
  have Qright : ∀ x : E', Q (Algebra.TensorProduct.includeRight x) := by
    intro x
    have hx : x ∈ Algebra.adjoin E ({θ} : Set E') := by rw [pb.adjoin_gen_eq_top]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
      rw [Set.mem_singleton_iff.1 hy]; exact hTe
    | algebraMap r =>
      have : (Algebra.TensorProduct.includeRight (algebraMap E E' r) : A)
          = algebraMap K A (algebraMap E K r) := by
        rw [AlgHom.commutes, IsScalarTower.algebraMap_apply E K A]
      rw [this]; exact Qalg _
    | add y z _ _ hy hz => rw [map_add (f := _)]; exact Qadd _ _ hy hz
    | mul y z _ _ hy hz => rw [map_mul]; exact Qmul _ _ hy hz
  refine ⟨e, hψe, fun a => ?_⟩
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul k x =>
    have : (k ⊗ₜ[E] x : A) = algebraMap K A k * Algebra.TensorProduct.includeRight x := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, Algebra.algebraMap_self, RingHom.id_apply, one_mul]
    rw [this]; exact Qmul _ _ (Qalg k) (Qright x)
  | add a b ha hb => exact Qadd _ _ ha hb

end GlobalTheory
end

section

open Polynomial

namespace GlobalTheory

theorem charpoly_nilpotent_add_scalar : ∀ (k : Type) [Field k] (n : ℕ) (N : Matrix (Fin n) (Fin n) k) (c : k), IsNilpotent N → (N + Matrix.scalar (Fin n) c).charpoly = (X - C c) ^ n := by
  intro k _ n N c hN
  have hc : N.charpoly = X ^ n := by
    have := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hN
    rw [Fintype.card_fin] at this
    exact sub_eq_zero.mp this.eq_zero
  have h1 := Matrix.charpoly_sub_scalar (N + Matrix.scalar (Fin n) c) c
  rw [add_sub_cancel_right, hc] at h1
  have hXC : ((X : k[X]) + C c).comp (X - C c) = X := by simp
  calc (N + Matrix.scalar (Fin n) c).charpoly
      = ((N + Matrix.scalar (Fin n) c).charpoly.comp (X + C c)).comp (X - C c) := by
        rw [comp_assoc, hXC, comp_X]
    _ = (X - C c) ^ n := by rw [← h1]; simp

end GlobalTheory
end

section

universe u_1 u_2 u_3

namespace GlobalTheory.DvdSubMapMk

theorem dvd_sub_iff_map_mk_eq {R : Type u_1} [inst : CommRing R] {p : Type u_2} {q : Type u_3}
    (a : R) (A B : Matrix p q R) :
    (∀ (i : p) (j : q), a ∣ (A - B) i j) ↔
      Matrix.map A (⇑(Ideal.Quotient.mk (Ideal.span {a})) : R → R ⧸ Ideal.span {a}) =
        Matrix.map B (⇑(Ideal.Quotient.mk (Ideal.span {a})) : R → R ⧸ Ideal.span {a}) := by
  rw [← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [Matrix.map_apply, Matrix.map_apply, Ideal.Quotient.eq, Ideal.mem_span_singleton,
    Matrix.sub_apply]

end GlobalTheory.DvdSubMapMk
end

section

open TensorProduct Module

open Matrix

theorem GlobalTheory.InertiaEigenvalues.finrank_invariants_eq_of_period_matrix : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] (B : Type) [CommRing B] [Nontrivial B] [Algebra F B] [Algebra E B] [IsScalarTower F E B] (G : Type) (act : G → B →+* B) (n : Type) [Fintype n] [DecidableEq n] (A : G → Matrix n n B), (∀ b : B, (∀ g, act g b = b) ↔ ∃ c : E, algebraMap E B c = b) → ∀ Q : GL n B, (∀ g, A g * (Q : Matrix n n B).map (act g) = Q) → ∀ W : Submodule F (n → B), (∀ x, x ∈ W ↔ ∀ g, (A g).mulVec (fun i => act g (x i)) = x) → finrank F ↥W = finrank F E * Fintype.card n := by
  intro F E _ _ _ _ B _ _ _ _ _ G act n _ _ A hfix Q hQ W hW
  set Q' : Matrix n n B := (Q : Matrix n n B) with hQ'
  have hQQ' : (↑Q⁻¹ : Matrix n n B) * Q' = 1 := by rw [hQ']; exact_mod_cast Q.inv_mul
  have hQQ : Q' * (↑Q⁻¹ : Matrix n n B) = 1 := by rw [hQ']; exact_mod_cast Q.mul_inv
  have key : ∀ g (y : n → B), (A g).mulVec (fun i => act g ((Q' *ᵥ y) i)) = Q' *ᵥ (fun i => act g (y i)) := by
    intro g y
    have h1 : (fun i => act g ((Q' *ᵥ y) i)) = Q'.map (act g) *ᵥ (fun i => act g (y i)) := by
      funext i; exact RingHom.map_mulVec _ _ _ _
    rw [h1, Matrix.mulVec_mulVec, hQ g]
  have inj : ∀ u v : n → B, Q' *ᵥ u = Q' *ᵥ v → u = v := by
    intro u v h
    have h2 := congrArg (fun w => (↑Q⁻¹ : Matrix n n B) *ᵥ w) h
    simp only [Matrix.mulVec_mulVec] at h2
    rwa [hQQ', Matrix.one_mulVec, Matrix.one_mulVec] at h2
  let φ : (n → E) →ₗ[F] (n → B) :=
    { toFun := fun c => Q' *ᵥ (fun i => algebraMap E B (c i))
      map_add' := by
        intro a b
        have : (fun i => algebraMap E B ((a + b) i)) = (fun i => algebraMap E B (a i)) + (fun i => algebraMap E B (b i)) := by
          funext i; simp
        rw [this, Matrix.mulVec_add]
      map_smul' := by
        intro r a
        have : (fun i => algebraMap E B ((r • a) i)) = r • (fun i => algebraMap E B (a i)) := by
          funext i
          simp only [Pi.smul_apply]
          rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
        rw [this, Matrix.mulVec_smul]
        rfl }
  have hφ : ∀ c, φ c = Q' *ᵥ (fun i => algebraMap E B (c i)) := fun c => rfl
  have φinj : Function.Injective φ := by
    intro a b h
    rw [hφ, hφ] at h
    have h3 := inj _ _ h
    funext i
    exact (algebraMap E B).injective (congrFun h3 i)
  have hWr : W = LinearMap.range φ := by
    ext x
    rw [hW, LinearMap.mem_range]
    constructor
    · intro hx
      set y : n → B := (↑Q⁻¹ : Matrix n n B) *ᵥ x with hy
      have hxy : Q' *ᵥ y = x := by rw [hy, Matrix.mulVec_mulVec, hQQ, Matrix.one_mulVec]
      have hfixy : ∀ i g, act g (y i) = y i := by
        intro i g
        have h4 := hx g
        rw [← hxy, key] at h4
        exact congrFun (inj _ _ h4) i
      choose c hc using fun i => (hfix (y i)).1 (hfixy i)
      refine ⟨c, ?_⟩
      rw [hφ, ← hxy]
      congr 1
      funext i; exact hc i
    · rintro ⟨c, rfl⟩ g
      rw [hφ, key]
      congr 1
      funext i
      exact ((hfix _).2 ⟨c i, rfl⟩) g
  subst hWr
  rw [LinearMap.finrank_range_of_inj φinj, Module.finrank_pi_fintype]
  simp [Finset.sum_const, Finset.card_univ, mul_comm]
end

section

noncomputable section

open Matrix

namespace GlobalTheory.PMon

variable {R : Type*} [CommRing R] {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

def vecM {S : Type*} (X : Matrix a b S) : a × b → S := fun p => X p.1 p.2

def homUnit (A : GL a R) (B : GL b R) : GL (a × b) R where
  val := Matrix.kroneckerMap (· * ·) (A : Matrix a a R) ((B⁻¹ : GL b R) : Matrix b b R)ᵀ
  inv := Matrix.kroneckerMap (· * ·) ((A⁻¹ : GL a R) : Matrix a a R) (B : Matrix b b R)ᵀ
  val_inv := by
    rw [← Matrix.mul_kronecker_mul, ← Matrix.transpose_mul]
    simp [Matrix.one_kronecker_one]
  inv_val := by
    rw [← Matrix.mul_kronecker_mul, ← Matrix.transpose_mul]
    simp [Matrix.one_kronecker_one]

theorem homUnit_val (A : GL a R) (B : GL b R) :
    ((homUnit A B : GL (a × b) R) : Matrix (a × b) (a × b) R) =
      Matrix.kroneckerMap (· * ·) (A : Matrix a a R) ((B⁻¹ : GL b R) : Matrix b b R)ᵀ := rfl

theorem kronecker_transpose_mulVec {S : Type*} [CommRing S] (A : Matrix a a S) (C : Matrix b b S) (X : Matrix a b S) :
    (Matrix.kroneckerMap (· * ·) A Cᵀ).mulVec (vecM X) = vecM (A * X * C) := by
  funext p
  obtain ⟨i, j⟩ := p
  simp only [vecM, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Matrix.transpose_apply, Matrix.mul_apply,
    Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
  ring

theorem homUnit_mulVec {S : Type*} [CommRing S] (f : R →+* S) (A : GL a R) (B : GL b R) (X : Matrix a b S) :
    (((homUnit A B : GL (a × b) R) : Matrix (a × b) (a × b) R).map f).mulVec (vecM X) =
      vecM ((A : Matrix a a R).map f * X * ((B⁻¹ : GL b R) : Matrix b b R).map f) := by
  rw [homUnit_val, ← kronecker_transpose_mulVec]
  congr 1
  ext p q
  simp [Matrix.kroneckerMap_apply]

def homRep {G : Type*} [Group G] (ρ₁ : G →* GL a R) (ρ₂ : G →* GL b R) : G →* GL (a × b) R where
  toFun g := homUnit (ρ₁ g) (ρ₂ g)
  map_one' := by
    ext1
    simp [homUnit_val, Matrix.one_kronecker_one]
  map_mul' g h := by
    ext1
    show ((homUnit (ρ₁ (g * h)) (ρ₂ (g * h)) : GL (a × b) R) : Matrix _ _ R) = ((homUnit (ρ₁ g) (ρ₂ g) : GL (a × b) R) : Matrix (a × b) (a × b) R) * ((homUnit (ρ₁ h) (ρ₂ h) : GL (a × b) R) : Matrix (a × b) (a × b) R)
    rw [homUnit_val, homUnit_val, homUnit_val, map_mul, map_mul, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, Matrix.transpose_mul, Matrix.mul_kronecker_mul]

theorem homRep_apply {G : Type*} [Group G] (ρ₁ : G →* GL a R) (ρ₂ : G →* GL b R) (g : G) :
    homRep ρ₁ ρ₂ g = homUnit (ρ₁ g) (ρ₂ g) := rfl

def extCoc {G : Type*} [Group G] (ρ₂ : G →* GL b R) (c : G → Matrix a b R) (g : G) : a × b → R :=
  vecM (c g * (((ρ₂ g)⁻¹ : GL b R) : Matrix b b R))

theorem vecM_injective {S : Type*} : Function.Injective (vecM : Matrix a b S → a × b → S) := by
  intro X Y h
  ext i j
  exact congrFun h (i, j)

end GlobalTheory.PMon
end
end
