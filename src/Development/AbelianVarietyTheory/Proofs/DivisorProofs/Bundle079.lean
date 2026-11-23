module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.Nullstellensatz
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
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.PID

@[expose] public section

section

open Polynomial IsLocalRing

namespace GlobalTheory

theorem kummer_residue_mem_adjoin (T V : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Algebra T V] [IsLocalHom (algebraMap T V)]
    (hinj : Function.Injective (algebraMap T V))
    (α γ : V) (ϖ : T) (m : ℕ) (hϖ : Irreducible ϖ) (hm : 0 < m) (hγ : IsUnit γ)
    (hα : α ^ m = γ * algebraMap T V ϖ)
    (hpol : ∀ h : Polynomial T, Polynomial.aeval γ h = 0 ∨
      ∃ (a : ℕ) (h' c : Polynomial T), IsUnit (Polynomial.aeval γ c) ∧ IsUnit (Polynomial.aeval γ h') ∧
        Polynomial.aeval γ c * Polynomial.aeval γ h = algebraMap T V ϖ ^ a * Polynomial.aeval γ h')
    (hgen : ∀ v : V, ∃ f g : Polynomial T, Polynomial.aeval α g ≠ 0 ∧
      Polynomial.aeval α g * v = Polynomial.aeval α f)
    (v : V) : IsLocalRing.residue V v ∈
      IntermediateField.adjoin (IsLocalRing.ResidueField T) {IsLocalRing.residue V γ} := by
  set K := IntermediateField.adjoin (IsLocalRing.ResidueField T) {IsLocalRing.residue V γ} with hK
  have hγK : residue V γ ∈ K := IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)
  have hres : ∀ p : T[X], residue V (aeval γ p) ∈ K := by
    intro p
    induction p using Polynomial.induction_on with
    | C a =>
      rw [aeval_C]
      have : residue V (algebraMap T V a) =
          algebraMap (ResidueField T) (ResidueField V) (residue T a) :=
        (ResidueField.map_residue _ a).symm
      rw [this]; exact K.algebraMap_mem _
    | add p q hp hq => rw [map_add (f := _), map_add (f := _)]; exact K.add_mem hp hq
    | monomial n a ih =>
      rw [pow_succ, ← mul_assoc, map_mul, aeval_X, map_mul]
      exact K.mul_mem ih hγK
  have hϖ0 : algebraMap T V ϖ ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap T V)]; exact fun h => hϖ.ne_zero (hinj h)
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at hα
    exact mul_ne_zero hγ.ne_zero hϖ0 hα.symm
  have hαnu : ¬ IsUnit α := by
    intro h
    have h1 : IsUnit (γ * algebraMap T V ϖ) := hα ▸ h.pow m
    exact hϖ.not_isUnit ((isUnit_map_iff (algebraMap T V) ϖ).1 (isUnit_of_mul_isUnit_right h1))
  have hsmall : ∀ k : ℕ, 0 < k → ∀ x : V, residue V (α ^ k * x) = 0 := by
    intro k hk x
    rw [residue_eq_zero_iff]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ ((mem_maximalIdeal _).2 hαnu) k hk)
  have hcomb : ∀ (u u' : V) (k : ℕ), 0 < k → IsUnit u → residue V u ∈ K →
      IsUnit (u + α ^ k * u') ∧ residue V (u + α ^ k * u') ∈ K := by
    intro u u' k hk hu huK
    have e : residue V (u + α ^ k * u') = residue V u := by rw [map_add (f := _), hsmall k hk, add_zero]
    refine ⟨?_, e ▸ huK⟩
    rw [← residue_ne_zero_iff_isUnit, e, residue_ne_zero_iff_isUnit]; exact hu
  let Good : Finset ℕ → V → Prop := fun s x =>
    x = 0 ∨ ∃ n u, IsUnit u ∧ residue V u ∈ K ∧ n % m ∈ s ∧ x = α ^ n * u
  have hdec : ∀ p : T[X], ∃ a : ℕ → T[X],
      aeval α p = ∑ j ∈ Finset.range m, aeval γ (a j) * α ^ j := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      obtain ⟨a, ha⟩ := hp; obtain ⟨b, hb⟩ := hq
      exact ⟨a + b, by simp only [map_add (f := _), ha, hb, Pi.add_apply, add_mul, Finset.sum_add_distrib]⟩
    | monomial n t =>
      refine ⟨fun j => if j = n % m then C t * (C ϖ * X) ^ (n / m) else 0, ?_⟩
      simp only [apply_ite (aeval γ), ite_mul, map_zero, zero_mul, Finset.sum_ite_eq',
        Finset.mem_range, Nat.mod_lt _ hm, if_true]
      rw [aeval_monomial, map_mul, aeval_C, map_pow, map_mul, aeval_C, aeval_X]
      conv_lhs => rw [← Nat.div_add_mod n m, pow_add, pow_mul, hα]
      ring
  have hterm : ∀ (a : T[X]) (j : ℕ), j < m → Good {j} (aeval γ a * α ^ j) := by
    intro a j hj
    rcases hpol a with h0 | ⟨b, h', c, hc, hh', hrel⟩
    · left; rw [h0, zero_mul]
    · right
      refine ⟨m * b + j, ((hγ.unit⁻¹ ^ b * hc.unit⁻¹ : Vˣ) : V) * aeval γ h',
        (Units.isUnit _).mul hh', ?_, ?_, ?_⟩
      · rw [map_mul, Units.val_mul, map_mul, Units.val_pow_eq_pow_val, map_pow, map_units_inv,
          map_units_inv, IsUnit.unit_spec, IsUnit.unit_spec]
        exact K.mul_mem (K.mul_mem (pow_mem (K.inv_mem hγK) b) (K.inv_mem (hres c))) (hres h')
      · rw [Finset.mem_singleton, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
      · have e1 : (γ * ((hγ.unit⁻¹ : Vˣ) : V)) ^ b = 1 := by
          rw [IsUnit.mul_val_inv hγ, one_pow]
        have e2 : aeval γ c * ((hc.unit⁻¹ : Vˣ) : V) = 1 := by
          exact IsUnit.mul_val_inv hc
        rw [pow_add, pow_mul, hα, Units.val_mul, Units.val_pow_eq_pow_val]
        linear_combination (-(aeval γ a * α ^ j)) * e2 + (((hc.unit⁻¹ : Vˣ) : V) * α ^ j) * hrel
          + (-(algebraMap T V ϖ ^ b * aeval γ h' * ((hc.unit⁻¹ : Vˣ) : V) * α ^ j)) * e1
  have hsum : ∀ (a : ℕ → T[X]) (s : Finset ℕ), s ⊆ Finset.range m →
      Good s (∑ j ∈ s, aeval γ (a j) * α ^ j) := by
    intro a s
    induction s using Finset.induction_on with
    | empty => intro _; left; simp
    | insert j s hjs ih =>
      intro hsub
      rw [Finset.sum_insert hjs]
      have hj : j < m := Finset.mem_range.1 (hsub (Finset.mem_insert_self _ _))
      have ih' := ih ((Finset.subset_insert _ _).trans hsub)
      rcases hterm (a j) j hj with h0 | ⟨n, u, hu, huK, hn, he⟩
      · rw [h0, zero_add]
        rcases ih' with h | ⟨n', u', hu', hu'K, hn', he'⟩
        · left; exact h
        · right; exact ⟨n', u', hu', hu'K, Finset.mem_insert_of_mem hn', he'⟩
      · rw [Finset.mem_singleton] at hn
        rcases ih' with h | ⟨n', u', hu', hu'K, hn', he'⟩
        · right; rw [h, add_zero]
          exact ⟨n, u, hu, huK, hn ▸ Finset.mem_insert_self _ _, he⟩
        · right
          have hne : n ≠ n' := by rintro rfl; exact hjs (hn ▸ hn')
          rcases lt_or_gt_of_ne hne with hlt | hlt
          · obtain ⟨h1, h2⟩ := hcomb u u' (n' - n) (Nat.sub_pos_of_lt hlt) hu huK
            refine ⟨n, _, h1, h2, hn ▸ Finset.mem_insert_self _ _, ?_⟩
            rw [he, he', mul_add, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hlt.le]
          · obtain ⟨h1, h2⟩ := hcomb u' u (n - n') (Nat.sub_pos_of_lt hlt) hu' hu'K
            refine ⟨n', _, h1, h2, Finset.mem_insert_of_mem hn', ?_⟩
            rw [he, he', mul_add, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hlt.le, add_comm]
  by_cases hv : IsUnit v
  · obtain ⟨f, g, hg0, hfg⟩ := hgen v
    obtain ⟨a, ha⟩ := hdec g
    obtain ⟨b, hb⟩ := hdec f
    have Gg := hsum a _ subset_rfl
    have Gf := hsum b _ subset_rfl
    rw [← ha] at Gg
    rw [← hb] at Gf
    rcases Gg with h | ⟨n, u, hu, huK, -, he⟩
    · exact absurd h hg0
    rcases Gf with h | ⟨n', u', hu', hu'K, -, he'⟩
    · exact absurd (hfg.trans h) (mul_ne_zero hg0 hv.ne_zero)
    rw [he, he'] at hfg
    have key : n = n' := by
      rcases lt_trichotomy n n' with h | h | h
      · exfalso
        have h2 : α ^ n * (u * v) = α ^ n * (α ^ (n' - n) * u') := by
          rw [← mul_assoc, hfg, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' h.le]
        have h3 := mul_left_cancel₀ (pow_ne_zero n hα0) h2
        have h4 := hsmall (n' - n) (Nat.sub_pos_of_lt h) u'
        rw [← h3] at h4
        exact (residue_ne_zero_iff_isUnit _).2 (hu.mul hv) h4
      · exact h
      · exfalso
        have h2 : α ^ n' * (α ^ (n - n') * (u * v)) = α ^ n' * u' := by
          rw [← hfg, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' h.le, mul_assoc]
        have h3 := mul_left_cancel₀ (pow_ne_zero n' hα0) h2
        have h4 := hsmall (n - n') (Nat.sub_pos_of_lt h) (u * v)
        rw [h3] at h4
        exact (residue_ne_zero_iff_isUnit _).2 hu' h4
    subst key
    have huv : u * v = u' := mul_left_cancel₀ (pow_ne_zero n hα0) (by rw [← mul_assoc, hfg])
    have hr : residue V u * residue V v = residue V u' := by rw [← map_mul, huv]
    have hru : residue V u ≠ 0 := (residue_ne_zero_iff_isUnit _).2 hu
    have : residue V v = residue V u' / residue V u := by
      rw [← hr]; field_simp
    rw [this]; exact K.div_mem hu'K huK
  · rw [(residue_eq_zero_iff v).2 ((mem_maximalIdeal _).2 hv)]; exact K.zero_mem

end GlobalTheory
end

section

open MvPolynomial

namespace GlobalTheory.PointTransfer

theorem exists_algHom_algebraicClosure (F A : Type) [Field F] [CommRing A] [Nontrivial A] [Algebra F A]
    [Algebra.FiniteType F A] : Nonempty (A →ₐ[F] AlgebraicClosure F) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite F (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing F (A ⧸ m)
  exact ⟨(IsAlgClosed.lift : (A ⧸ m) →ₐ[F] AlgebraicClosure F).comp (Ideal.Quotient.mkₐ F m)⟩

theorem exists_common_zero {Ω τ : Type} [Field Ω] [IsAlgClosed Ω] [Finite τ]
    (I : Ideal (MvPolynomial τ Ω)) (hI : I ≠ ⊤) : ∃ y : τ → Ω, ∀ f ∈ I, aeval y f = 0 := by
  by_contra h
  have he : zeroLocus Ω I = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro y hy
    exact h ⟨y, fun f hf => hy f hf⟩
  have h2 := MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := Ω) I
  rw [he, MvPolynomial.vanishingIdeal_empty] at h2
  exact hI (Ideal.radical_eq_top.1 h2.symm)

noncomputable def partialEval {F A σ τ : Type} [CommRing F] [CommRing A] [Algebra F A] (u : σ → A) :
    MvPolynomial (σ ⊕ τ) F →ₐ[F] MvPolynomial τ A :=
  aeval (Sum.elim (fun s => C (u s)) X)

theorem eval₂Hom_partialEval {F A B σ τ : Type} [CommRing F] [CommRing A] [CommRing B] [Algebra F A]
    [Algebra F B] (ψ : A →ₐ[F] B) (u : σ → A) (y : τ → B) (g : MvPolynomial (σ ⊕ τ) F) :
    eval₂Hom (ψ : A →+* B) y (partialEval u g) = aeval (Sum.elim (fun s => ψ (u s)) y) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [partialEval, MvPolynomial.algebraMap_apply]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    cases i <;> simp [partialEval]

theorem map_partialEval {F A B σ τ : Type} [CommRing F] [CommRing A] [CommRing B] [Algebra F A]
    [Algebra F B] (ψ : A →ₐ[F] B) (u : σ → A) (g : MvPolynomial (σ ⊕ τ) F) :
    MvPolynomial.map (ψ : A →+* B) (partialEval u g) = partialEval (fun s => ψ (u s)) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [partialEval, MvPolynomial.algebraMap_apply]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    cases i <;> simp [partialEval]

theorem solvable_transfer (F σ τ : Type) [Field F] [Finite σ] [Finite τ]
    (P : Ideal (MvPolynomial σ F)) (J : Ideal (MvPolynomial (σ ⊕ τ) F))
    (H : ∀ u : σ → AlgebraicClosure F, (∀ g ∈ P, aeval u g = 0) →
      ∃ y : τ → AlgebraicClosure F, ∀ g ∈ J, aeval (Sum.elim u y) g = 0)
    (Ω : Type) [Field Ω] [Algebra F Ω] [IsAlgClosed Ω] (u : σ → Ω)
    (hu : ∀ g ∈ P, aeval u g = 0) :
    ∃ y : τ → Ω, ∀ g ∈ J, aeval (Sum.elim u y) g = 0 := by
  have hI : J.map (partialEval (F := F) (τ := τ) u) ≠ ⊤ := by
    intro htop
    have h1 : (1 : MvPolynomial τ Ω) ∈ Submodule.span (MvPolynomial τ Ω)
        ((partialEval (F := F) (τ := τ) u) '' (J : Set _)) := by
      have : (1 : MvPolynomial τ Ω) ∈ J.map (partialEval (F := F) (τ := τ) u) := by
        rw [htop]; trivial
      exact this
    obtain ⟨n, c, g, hsum⟩ := Submodule.mem_span_set'.1 h1
    choose g' hg'J hg' using fun i => (g i).2
    let S : Set Ω := Set.range u ∪ ⋃ i, ((c i).coeffs : Set Ω)
    have hS : S.Finite :=
      (Set.finite_range u).union (Set.finite_iUnion fun i => (c i).coeffs.finite_toSet)
    let A : Subalgebra F Ω := Algebra.adjoin F S
    haveI : Algebra.FiniteType F A :=
      (Subalgebra.fg_iff_finiteType A).1 (Subalgebra.fg_def.2 ⟨S, hS, rfl⟩)
    obtain ⟨ψ⟩ := exists_algHom_algebraicClosure F A
    let uA : σ → A := fun s => ⟨u s, Algebra.subset_adjoin (Or.inl ⟨s, rfl⟩)⟩
    have hc : ∀ i, c i ∈ Set.range (MvPolynomial.map (σ := τ) (A.val : A →+* Ω)) := by
      intro i
      rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
      intro a ha
      exact ⟨⟨a, Algebra.subset_adjoin (Or.inr (Set.mem_iUnion.2 ⟨i, ha⟩))⟩, rfl⟩
    choose c' hc' using hc
    have hid : ∑ i, c' i * partialEval uA (g' i) = 1 := by
      apply MvPolynomial.map_injective (A.val : A →+* Ω) Subtype.val_injective

      rw [map_one, ← hsum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, hc', map_partialEval, smul_eq_mul, ← hg' i]
      rfl
    obtain ⟨y, hy⟩ := H (fun s => ψ (uA s)) (by
      intro p hp
      have h0 : aeval uA p = 0 := by
        apply Subtype.val_injective
        have := DFunLike.congr_fun (MvPolynomial.comp_aeval uA A.val) p
        exact this.trans (hu p hp)
      have := DFunLike.congr_fun (MvPolynomial.comp_aeval uA ψ) p
      rw [← this, AlgHom.comp_apply, h0, map_zero])
    have := congrArg (eval₂Hom (ψ : A →+* AlgebraicClosure F) y) hid

    rw [map_one, map_sum, Finset.sum_eq_zero] at this
    · exact zero_ne_one this
    · intro i _
      rw [map_mul, eval₂Hom_partialEval, hy _ (hg'J i), mul_zero]
  obtain ⟨y, hy⟩ := exists_common_zero _ hI
  refine ⟨y, fun g hg => ?_⟩
  have h := hy _ (Ideal.mem_map_of_mem _ hg)
  have h2 := eval₂Hom_partialEval (AlgHom.id F Ω) u y g
  exact h2.symm.trans h

end GlobalTheory.PointTransfer
end

section

open Polynomial

namespace GlobalTheory.FiniteFieldOfPoints

theorem factor_of_range {C K₂ Ω : Type} [CommRing C] [Field K₂] [Field Ω]
    (j : K₂ →+* Ω) (ψ : C →+* Ω) (h : ∀ c, ∃ x, j x = ψ c) :
    ∃ ψ₀ : C →+* K₂, j.comp ψ₀ = ψ := by
  choose f hf using h
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, ?_⟩
  · apply j.injective; simp [hf]
  · intro a b; apply j.injective; simp [hf]
  · apply j.injective; simp [hf]
  · intro a b; apply j.injective; simp [hf]
  · ext c; simp [hf]

theorem exists_finite_field_of_points (K : Type) [Field K] (C : Type) [CommRing C] (φ : K →+* C)
    (hφ : RingHom.Finite φ) :
    ∃ (E : IntermediateField K (AlgebraicClosure K)), FiniteDimensional K ↥E ∧
      ∀ (K₂ Ω : Type) [Field K₂] [Field Ω] (e : ↥E →+* K₂) (j : K₂ →+* Ω) (ψ : C →+* Ω),
        RingHom.comp ψ φ = RingHom.comp j (RingHom.comp e (algebraMap K ↥E)) →
        ∃ (ψ₀ : C →+* K₂), RingHom.comp j ψ₀ = ψ := by
  classical
  letI : Algebra K C := φ.toAlgebra
  haveI : Module.Finite K C := hφ
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := K) (M := C)
  have hint : ∀ c : C, IsIntegral K c := fun c => Algebra.IsIntegral.isIntegral c
  choose p hpm hpe using hint
  set P : K[X] := ∏ c ∈ s, p c with hP
  have hPm : P.Monic := monic_prod_of_monic _ _ (fun c _ => hpm c)
  have hsf : IsSplittingField K
      (IntermediateField.adjoin K (P.rootSet (AlgebraicClosure K))) P :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  refine ⟨IntermediateField.adjoin K (P.rootSet (AlgebraicClosure K)),
    IsSplittingField.finiteDimensional _ P, ?_⟩
  generalize IntermediateField.adjoin K (P.rootSet (AlgebraicClosure K)) = E at hsf ⊢
  intro K₂ Ω _ _ e j ψ hc
  have hspl : (P.map (algebraMap K E)).Splits := hsf.splits'
  have hspl2 : (P.map (e.comp (algebraMap K E))).Splits := by
    rw [← Polynomial.map_map]; exact hspl.map e
  have hgen : ∀ c ∈ s, ψ c ∈ j.range := by
    intro c hcs
    have h0 : eval₂ φ c P = 0 := by
      rw [hP, eval₂_finsetProd]
      exact Finset.prod_eq_zero hcs (hpe c)
    have h1 : ((P.map (e.comp (algebraMap K E))).map j).IsRoot (ψ c) := by
      rw [Polynomial.map_map, ← hc, IsRoot, eval_map, ← hom_eval₂, h0, map_zero]
    exact hspl2.mem_range_of_isRoot (hPm.map _).ne_zero h1
  apply factor_of_range
  intro c
  have hmem : c ∈ Submodule.span K (s : Set C) := by rw [hs]; trivial
  change ψ c ∈ j.range
  induction hmem using Submodule.span_induction with
  | mem x hx => exact hgen x hx
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx =>
    rw [Algebra.smul_def, map_mul]
    refine mul_mem ?_ hx
    refine ⟨e (algebraMap K E a), ?_⟩
    exact (RingHom.congr_fun hc a).symm

end GlobalTheory.FiniteFieldOfPoints
end

section

namespace GlobalTheory

theorem mem_subfield_of_zpow_mem {K : Type} [Field K] (k₀ : Subfield K) [IsAlgClosed k₀]
    (u : Kˣ) (m : ℤ) (hm : m ≠ 0) (h : ((u ^ m : Kˣ) : K) ∈ k₀) : (u : K) ∈ k₀ := by
  have h1 : (u : K) ^ m.natAbs ∈ k₀ := by
    rw [Units.val_zpow_eq_zpow_val] at h
    rcases Int.natAbs_eq m with h2 | h2
    · rw [h2, zpow_natCast] at h; exact h
    · rw [h2, zpow_neg, zpow_natCast] at h
      simpa using k₀.inv_mem h
  have hint : IsIntegral k₀ (u : K) := by
    apply IsIntegral.of_pow (Int.natAbs_pos.mpr hm)
    exact isIntegral_algebraMap (R := k₀) (x := ⟨_, h1⟩)
  obtain ⟨y, hy⟩ := minpoly.mem_range_of_degree_eq_one k₀ (u : K)
    (IsAlgClosed.degree_eq_one_of_irreducible k₀ (minpoly.irreducible hint))
  rw [← hy]
  exact y.2

def monomialExponents {I : Type} [Fintype I] {K : Type} [Field K] (k₀ : Subfield K)
    (t : I → Kˣ) : Submodule ℤ (I → ℤ) :=
  AddSubgroup.toIntSubmodule
  { carrier := {v | ((∏ k, t k ^ v k : Kˣ) : K) ∈ k₀}
    zero_mem' := by simp [k₀.one_mem]
    add_mem' := by
      intro a b ha hb
      simp only [Set.mem_setOf_eq, Pi.add_apply, zpow_add, Finset.prod_mul_distrib,
        Units.val_mul] at *
      exact k₀.mul_mem ha hb
    neg_mem' := by
      intro a ha
      simp only [Set.mem_setOf_eq, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib,
        Units.val_inv_eq_inv_val] at *
      exact k₀.inv_mem ha }

theorem mem_monomialExponents {I : Type} [Fintype I] {K : Type} [Field K] (k₀ : Subfield K)
    (t : I → Kˣ) (v : I → ℤ) :
    v ∈ monomialExponents k₀ t ↔ ((∏ k, t k ^ v k : Kˣ) : K) ∈ k₀ := Iff.rfl

theorem mem_monomialExponents_of_smul {I : Type} [Fintype I] {K : Type} [Field K]
    (k₀ : Subfield K) [IsAlgClosed k₀] (t : I → Kˣ) (v : I → ℤ) (m : ℤ) (hm : m ≠ 0)
    (h : m • v ∈ monomialExponents k₀ t) : v ∈ monomialExponents k₀ t := by
  rw [mem_monomialExponents] at h ⊢
  apply mem_subfield_of_zpow_mem k₀ _ m hm
  convert h using 2
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_mul, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem mem_subfield_of_bilinForm_monomials :
    ∀ (X : Type) [AddCommGroup X] (S : Submodule ℤ (LinearMap.BilinForm ℤ X)) (I : Type) [Fintype I]
    (ε : Module.Basis I ℤ S) (K : Type) [Field K] (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (n : ℤ), n ≠ 0 →
    ∀ (t : I → Kˣ), (∀ a b : X, ((∏ k, t k ^ (n * (ε k : LinearMap.BilinForm ℤ X) a b) : Kˣ) : K) ∈ k₀) →
    ∀ k, (t k : K) ∈ k₀ := by
  intro X _ S I _ ε K _ k₀ hk n hn t h k
  classical
  set P := monomialExponents k₀ t with hP
  have hv : ∀ a b : X, (fun k => (ε k : LinearMap.BilinForm ℤ X) a b) ∈ P := fun a b =>
    mem_monomialExponents_of_smul k₀ t _ n hn (h a b)
  haveI : NoZeroSMulDivisors ℤ ((I → ℤ) ⧸ P) := by
    refine ⟨fun {c x} hx => ?_⟩
    obtain ⟨v, rfl⟩ := P.mkQ_surjective x
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      rw [← map_smul] at hx
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx ⊢
      exact mem_monomialExponents_of_smul k₀ t v c hc hx
  haveI : Module.Free ℤ ((I → ℤ) ⧸ P) := Module.free_of_finite_type_torsion_free'
  have key : P.mkQ (Pi.single k 1) = 0 := by
    rw [← Module.forall_dual_apply_eq_zero_iff ℤ]
    intro φ
    have hz : ∑ j, φ (P.mkQ (Pi.single j 1)) • ε j = 0 := by
      apply Subtype.ext
      ext a b
      have h0 : φ (P.mkQ (fun k => (ε k : LinearMap.BilinForm ℤ X) a b)) = 0 := by
        rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero P).mpr (hv a b), map_zero]
      have h1 : (fun k => (ε k : LinearMap.BilinForm ℤ X) a b)
          = ∑ j, (ε j : LinearMap.BilinForm ℤ X) a b • (Pi.single j 1 : I → ℤ) := by
        funext i
        simp [Finset.sum_apply, Pi.single_apply]

      rw [h1, map_sum, map_sum] at h0
      simp only [map_smul, smul_eq_mul] at h0
      simp only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul, LinearMap.sum_apply,
        LinearMap.smul_apply, smul_eq_mul, ZeroMemClass.coe_zero, LinearMap.zero_apply]
      rw [← h0]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    exact Fintype.linearIndependent_iff.mp ε.linearIndependent _ hz k
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hP, mem_monomialExponents] at key
  convert key using 2
  rw [Finset.prod_eq_single k]
  · simp
  · intro j _ hj; simp [Pi.single_apply, hj]
  · simp

end GlobalTheory
end
