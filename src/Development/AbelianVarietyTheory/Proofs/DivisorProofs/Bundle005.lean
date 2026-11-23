module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.Algebra.Azumaya.Defs
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Action.Prod
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.SetTheory.Cardinal.Finite
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.MatrixAlgebra
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.GroupAction.Basic

@[expose] public section

section

open scoped TensorProduct

namespace GlobalTheory

theorem exists_generators_dual_point_derivations :
    ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] [Module.Finite k A] (ε : A →ₐ[k] k),
      IsNilpotent (RingHom.ker ε) → ∃ (d : ℕ) (x : Fin d → A) (l : Fin d → A →ₗ[k] k),
        (∀ i a b, l i (a * b) = ε a * l i b + ε b * l i a) ∧
        (∀ i j, l i (x j) = if i = j then 1 else 0) ∧ Algebra.adjoin k (Set.range x) = ⊤ := by
  intro k A _ _ _ _ ε hnil
  set I : Ideal A := RingHom.ker ε with hI
  let W : Submodule k A := (I ^ 2).restrictScalars k
  let U : Submodule k (A ⧸ W) := (I.restrictScalars k).map W.mkQ
  let b : Module.Basis (Fin (Module.finrank k U)) k U := Module.finBasis k U
  have hx : ∀ j, ∃ y, y ∈ I ∧ W.mkQ y = (b j : A ⧸ W) := fun j => by
    obtain ⟨y, hy, hy'⟩ := Submodule.mem_map.mp (b j).2
    exact ⟨y, hy, hy'⟩
  choose x hxI hxq using hx
  let P : A →ₗ[k] A := LinearMap.id - (Algebra.linearMap k A) ∘ₗ ε.toLinearMap
  have hPa : ∀ a, P a = a - algebraMap k A (ε a) := fun a => rfl
  have hP : ∀ a, P a ∈ I := fun a => by
    rw [hI, RingHom.mem_ker, hPa, map_sub, AlgHom.commutes]
    simp
  let T : A →ₗ[k] U := LinearMap.codRestrict U (W.mkQ ∘ₗ P)
    (fun a => Submodule.mem_map_of_mem (show P a ∈ I.restrictScalars k from hP a))
  have hT : ∀ a, ((T a : U) : A ⧸ W) = W.mkQ (P a) := fun a => rfl
  let l : Fin (Module.finrank k U) → A →ₗ[k] k := fun i => b.coord i ∘ₗ T
  have hspan : ∀ y ∈ I, ∃ s ∈ Submodule.span k (Set.range x), y - s ∈ I ^ 2 := by
    intro y hy
    let u : U := ⟨W.mkQ y, Submodule.mem_map_of_mem (show y ∈ I.restrictScalars k from hy)⟩
    refine ⟨∑ j, b.repr u j • x j,
      Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)), ?_⟩
    have h1 : W.mkQ (∑ j, b.repr u j • x j) = ∑ j, b.repr u j • (b j : A ⧸ W) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, hxq]
    have h2 := congrArg Subtype.val (b.sum_repr u)
    push_cast at h2
    have hq : W.mkQ (∑ j, b.repr u j • x j) = W.mkQ y := by rw [h1, h2]
    have h0 : W.mkQ (y - ∑ j, b.repr u j • x j) = 0 := by rw [map_sub, hq, sub_self]
    have h3 := LinearMap.mem_ker.mpr h0
    rw [Submodule.ker_mkQ] at h3
    exact h3
  let S := Algebra.adjoin k (Set.range x)
  have spanS : Submodule.span k (Set.range x) ≤ Subalgebra.toSubmodule S :=
    Submodule.span_le.mpr (fun z hz => Algebra.subset_adjoin hz)
  have spanI : Submodule.span k (Set.range x) ≤ I.restrictScalars k :=
    Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hxI j)
  have hstep : ∀ n : ℕ, ∀ z ∈ I ^ n,
      z ∈ Subalgebra.toSubmodule S ⊔ (I ^ (n + 1)).restrictScalars k := by
    intro n
    induction n with
    | zero =>
      intro z _
      refine Submodule.mem_sup.mpr ⟨_, S.algebraMap_mem (ε z), P z, ?_, ?_⟩
      · show P z ∈ I ^ (0 + 1)
        rw [zero_add, pow_one]; exact hP z
      · rw [hPa]; abel
    | succ n ih =>
      intro z hz
      rw [pow_succ'] at hz
      refine Submodule.mul_induction_on hz ?_ (fun a c ha hc => add_mem ha hc)
      intro y hy w hw
      obtain ⟨s, hs, hys⟩ := hspan y hy
      obtain ⟨t, ht, v, hv, htv⟩ := Submodule.mem_sup.mp (ih w hw)
      have h1 : s * v ∈ I ^ (n + 1 + 1) := by
        rw [pow_succ']; exact Ideal.mul_mem_mul (spanI hs) hv
      have h2 : (y - s) * w ∈ I ^ (n + 1 + 1) := by
        rw [show n + 1 + 1 = 2 + n by omega, pow_add]; exact Ideal.mul_mem_mul hys hw
      refine Submodule.mem_sup.mpr ⟨s * t, S.mul_mem (spanS hs) ht, s * v + (y - s) * w,
        add_mem h1 h2, ?_⟩
      rw [← htv]; ring
  have hall : ∀ n : ℕ, ∀ a : A, a ∈ Subalgebra.toSubmodule S ⊔ (I ^ n).restrictScalars k := by
    intro n
    induction n with
    | zero =>
      intro a
      refine Submodule.mem_sup.mpr ⟨0, zero_mem _, a, ?_, zero_add a⟩
      show a ∈ I ^ 0
      rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
    | succ n ih =>
      intro a
      obtain ⟨s, hs, w, hw, hsw⟩ := Submodule.mem_sup.mp (ih a)
      obtain ⟨t, ht, v, hv, htv⟩ := Submodule.mem_sup.mp (hstep n w hw)
      refine Submodule.mem_sup.mpr ⟨s + t, add_mem hs ht, v, hv, ?_⟩
      rw [← hsw, ← htv]; abel
  refine ⟨Module.finrank k U, x, l, ?_, ?_, ?_⟩
  · intro i a c
    have key : P (a * c) - (ε a • P c + ε c • P a) = P a * P c := by
      simp only [hPa, Algebra.smul_def, map_mul]; ring
    have hmem : P (a * c) - (ε a • P c + ε c • P a) ∈ W := by
      rw [key]
      show P a * P c ∈ I ^ 2
      rw [pow_two]; exact Ideal.mul_mem_mul (hP a) (hP c)
    have hTac : T (a * c) = ε a • T c + ε c • T a := by
      apply Subtype.ext
      rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, hT, hT, hT]
      have h0 : W.mkQ (P (a * c) - (ε a • P c + ε c • P a)) = 0 := by
        rw [← LinearMap.mem_ker, Submodule.ker_mkQ]; exact hmem
      rw [map_sub, map_add (f := _), map_smul, map_smul, sub_eq_zero] at h0
      exact h0
    show b.coord i (T (a * c)) = ε a * b.coord i (T c) + ε c * b.coord i (T a)
    rw [hTac, map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  · intro i j
    have hTx : T (x j) = b j := by
      apply Subtype.ext
      rw [hT, hPa]
      have : ε (x j) = 0 := (RingHom.mem_ker).mp (hxI j)
      rw [this, map_zero, sub_zero, hxq]
    show b.coord i (T (x j)) = _
    rw [hTx, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  · obtain ⟨N, hN⟩ := hnil
    have hv : (I ^ N).restrictScalars k = ⊥ := by
      rw [hI, hN, Submodule.zero_eq_bot, Submodule.restrictScalars_bot]
    refine eq_top_iff.mpr (fun a _ => ?_)
    have := hall N a
    rw [hv, sup_bot_eq] at this
    exact this

end GlobalTheory
end

section

open Algebra

theorem GlobalTheory.adjoin_mem_of_away_localization {R A R' A' : Type} [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] [Algebra R A] [Algebra R R'] [Algebra R' A'] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A'] [IsScalarTower R R' A'] (g : R) [IsLocalization.Away g R'] [IsLocalization.Away (algebraMap R A g) A'] (T : Set A) (b : A)
    (hb : algebraMap A A' b ∈ Algebra.adjoin R' (algebraMap A A' '' T)) :
    ∃ m : ℕ, algebraMap R A g ^ m * b ∈ Algebra.adjoin R T := by
  have hg : algebraMap A A' (algebraMap R A g) = algebraMap R A' g :=
    (IsScalarTower.algebraMap_apply R A A' g).symm
  have key : ∀ y ∈ Algebra.adjoin R' (algebraMap A A' '' T), ∃ k : ℕ, ∃ z ∈ Algebra.adjoin R T,
      algebraMap A A' z = algebraMap R A' g ^ k * y := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact ⟨0, a, Algebra.subset_adjoin ha, by simp⟩
    | algebraMap r =>
      obtain ⟨⟨r0, ⟨_, n, rfl⟩⟩, hr⟩ := IsLocalization.surj (Submonoid.powers g) r
      refine ⟨n, algebraMap R A r0, Subalgebra.algebraMap_mem _ r0, ?_⟩
      simp only at hr
      rw [← IsScalarTower.algebraMap_apply R A A', IsScalarTower.algebraMap_apply R R' A', ← hr,
        map_mul, ← IsScalarTower.algebraMap_apply R R' A', map_pow, mul_comm]
    | add x y _ _ hx hy =>
      obtain ⟨k1, z1, hz1, e1⟩ := hx
      obtain ⟨k2, z2, hz2, e2⟩ := hy
      refine ⟨k1 + k2, algebraMap R A g ^ k2 * z1 + algebraMap R A g ^ k1 * z2, ?_, ?_⟩
      · refine add_mem (mul_mem ?_ hz1) (mul_mem ?_ hz2) <;>
          (rw [← map_pow]; exact Subalgebra.algebraMap_mem _ _)
      · rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, hg, e1, e2]; ring
    | mul x y _ _ hx hy =>
      obtain ⟨k1, z1, hz1, e1⟩ := hx
      obtain ⟨k2, z2, hz2, e2⟩ := hy
      refine ⟨k1 + k2, z1 * z2, mul_mem hz1 hz2, ?_⟩
      rw [map_mul, e1, e2]; ring
  obtain ⟨k, z, hz, e⟩ := key _ hb
  have h0 : algebraMap A A' (z - algebraMap R A g ^ k * b) = 0 := by
    rw [map_sub, map_mul, map_pow, hg, e, sub_self]
  obtain ⟨⟨_, c, rfl⟩, hc⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers (algebraMap R A g)) A' _).1 h0
  refine ⟨c + k, ?_⟩
  have : algebraMap R A g ^ (c + k) * b = algebraMap R A g ^ c * z := by
    simp only at hc
    rw [mul_sub, sub_eq_zero] at hc
    rw [hc, pow_add]; ring
  rw [this]
  refine mul_mem ?_ hz
  rw [← map_pow]; exact Subalgebra.algebraMap_mem _ _

theorem GlobalTheory.adjoin_mem_of_away_localization' : ∀ {R A R' A' : Type} [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] [Algebra R A] [Algebra R R'] [Algebra R' A'] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A'] [IsScalarTower R R' A'] (g : R) [IsLocalization.Away g R'] [IsLocalization.Away (algebraMap R A g) A'], ∀ (T : Set A) (b : A), algebraMap A A' b ∈ Algebra.adjoin R' (algebraMap A A' '' T) → ∃ m : ℕ, algebraMap R A g ^ m * b ∈ Algebra.adjoin R T := by
  intros R A R' A' _ _ _ _ _ _ _ _ _ _ _ g _ _ T b h
  exact GlobalTheory.adjoin_mem_of_away_localization g T b h
end

section

namespace GlobalTheory.TargetInequalityLemmas

open Polynomial

theorem main {R F K : Type} [CommRing R] [IsDomain R] [Field F] [Algebra R F] [IsFractionRing R F]
    [Field K] [Algebra R K] [Algebra F K] [IsScalarTower R F K] (θ z : K)
    (hz : z ∈ Algebra.adjoin F ({θ} : Set K)) :
    ∃ d : R, d ≠ 0 ∧ (algebraMap R K d * z) ∈ Algebra.adjoin R ({θ} : Set K) := by
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hz
  simp only [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range]
  obtain ⟨p, rfl⟩ := hz
  obtain ⟨b, hbM, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) p
  refine ⟨b, nonZeroDivisors.ne_zero hbM, IsLocalization.integerNormalization (nonZeroDivisors R) p, ?_⟩
  have hmap : (IsLocalization.integerNormalization (nonZeroDivisors R) p).map (algebraMap R F)
      = C (algebraMap R F b) * p := by
    rw [hb]
    ext i
    rw [AddMonoidAlgebra.coeff_smul_apply, coeff_C_mul, Algebra.smul_def]
  rw [← aeval_map_algebraMap F, hmap, map_mul, aeval_C, ← IsScalarTower.algebraMap_apply]

theorem target : ∀ {R F K : Type} [inst : CommRing R] [IsDomain R] [inst_2 : Field F] [inst_3 : Algebra R F] [IsFractionRing R F] [inst_5 : Field K] [inst_6 : Algebra R K] [inst_7 : Algebra F K] [IsScalarTower R F K] (θ z : K), Membership.mem (Algebra.adjoin F (Singleton.singleton θ)) z → Exists fun (d : R) ↦ And (Ne d (0 : R)) (Membership.mem (Algebra.adjoin R (Singleton.singleton θ)) (HMul.hMul ((Algebra.algebraMap R K) d) z)) :=
  fun θ z hz => main θ z hz

end GlobalTheory.TargetInequalityLemmas
end

section

namespace GlobalTheory.EtC

def firstAndFinite (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ) (F : Finset A) :
    Subalgebra R (PiTensorProduct R (fun _ : Fin (k + 1) => A)) :=
  Algebra.adjoin R (Set.range (PiTensorProduct.singleAlgHom (R := R) (A := fun _ : Fin (k + 1) => A) 0) ∪
    ⋃ i : Fin (k + 1), (PiTensorProduct.singleAlgHom (R := R) (A := fun _ : Fin (k + 1) => A) i) '' (F : Set A))

def firstIncl (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ) (F : Finset A) :
    A →ₐ[R] firstAndFinite R A k F :=
  (PiTensorProduct.singleAlgHom (R := R) (A := fun _ : Fin (k + 1) => A) 0).codRestrict _
    (fun a => Algebra.subset_adjoin (Or.inl ⟨a, rfl⟩))

end GlobalTheory.EtC
end

section

open scoped TensorProduct
open Function

namespace GlobalTheory
open TensorProduct MulOpposite

variable (A S Λ : Type) [CommRing A] [CommRing S] [Algebra A S] [Ring Λ] [Algebra A Λ]

noncomputable def endBaseChangeMap :
    S ⊗[A] Module.End A Λ →ₗ[S] Module.End S (S ⊗[A] Λ) :=
  (LinearMap.baseChangeHom A S Λ Λ).liftBaseChange S

lemma endBaseChangeMap_tmul (s : S) (f : Module.End A Λ) :
    endBaseChangeMap A S Λ (s ⊗ₜ f) = s • f.baseChange S := by
  simp [endBaseChangeMap]

lemma endBaseChangeMap_bijective [Module.Free A Λ] [Module.Finite A Λ] :
    Bijective (endBaseChangeMap A S Λ) := by
  classical
  let ι := Module.Free.ChooseBasisIndex A Λ
  let b := Module.Free.chooseBasis A Λ
  let bS := Algebra.TensorProduct.basis S b
  let e₁ : S ⊗[A] Module.End A Λ ≃ₗ[S] S ⊗[A] Matrix ι ι A :=
    (LinearMap.toMatrix b b).baseChange A S _ _
  let e₂ := (matrixEquivTensor ι A S).symm
  let e₃ := LinearMap.toMatrix bS bS
  have h : ∀ x, e₃ (endBaseChangeMap A S Λ x) = e₂ (e₁ x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s f =>
      simp [e₁, e₂, e₃, bS, endBaseChangeMap_tmul, matrixEquivTensor_apply_symm]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have : (endBaseChangeMap A S Λ : _ → _) = e₃.symm ∘ e₂ ∘ e₁ := by
    funext x; simp [← h x]
  rw [this]
  exact e₃.symm.bijective.comp (e₂.bijective.comp e₁.bijective)

noncomputable def opBaseChange : S ⊗[A] Λᵐᵒᵖ ≃ₗ[S] (S ⊗[A] Λ)ᵐᵒᵖ :=
  ((opLinearEquiv A (M := Λ)).symm.baseChange A S _ _).trans (opLinearEquiv S)

noncomputable def envBaseChange :
    S ⊗[A] (Λ ⊗[A] Λᵐᵒᵖ) ≃ₗ[S] (S ⊗[A] Λ) ⊗[S] (S ⊗[A] Λ)ᵐᵒᵖ :=
  (AlgebraTensorModule.distribBaseChange A S Λ Λᵐᵒᵖ).trans
    (TensorProduct.congr (LinearEquiv.refl S _) (opBaseChange A S Λ))

lemma mulLeftRight_envBaseChange (x : S ⊗[A] (Λ ⊗[A] Λᵐᵒᵖ)) :
    AlgHom.mulLeftRight S (S ⊗[A] Λ) (envBaseChange A S Λ x) =
      endBaseChangeMap A S Λ ((AlgHom.mulLeftRight A Λ).toLinearMap.lTensor S x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul s y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz => simp only [tmul_add, map_add (f := _), hy, hz]
    | tmul a b =>
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z w hz hw => simp only [map_add (f := _), hz, hw]
      | tmul t y =>
        simp [envBaseChange, opBaseChange, endBaseChangeMap_tmul,
          AlgebraTensorModule.distribBaseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul,
          smul_tmul', mul_comm, mul_left_comm]

theorem isAzumaya_baseChange [IsAzumaya A Λ] [Module.Free A Λ] :
    IsAzumaya S (S ⊗[A] Λ) := by
  classical
  haveI : Module.Finite A Λ := inferInstance
  refine { toProjective := inferInstance, toFinite := inferInstance,
           toFaithfulSMul := ?_, bij := ?_ }
  · rcases subsingleton_or_nontrivial S with hS | hS
    · exact ⟨fun _ => Subsingleton.elim _ _⟩
    · haveI : Nontrivial A := (algebraMap A S).domain_nontrivial
      haveI : Nontrivial Λ := by
        by_contra hΛ
        rw [not_nontrivial_iff_subsingleton] at hΛ
        have : (0 : A) = 1 :=
          FaithfulSMul.eq_of_smul_eq_smul (α := Λ) fun _ => Subsingleton.elim _ _
        exact zero_ne_one this
      let b := Module.Free.chooseBasis A Λ
      let bS := Algebra.TensorProduct.basis S b
      obtain ⟨i⟩ := b.index_nonempty
      refine ⟨fun {s₁ s₂} h => ?_⟩
      have := congrArg (fun x => bS.repr x i) (h (bS i))
      simpa using this
  · have hφ : Bijective ((AlgHom.mulLeftRight A Λ).toLinearMap.lTensor S) := by
      let e := LinearEquiv.ofBijective (AlgHom.mulLeftRight A Λ).toLinearMap IsAzumaya.bij
      have : (AlgHom.mulLeftRight A Λ).toLinearMap.lTensor S = (e.lTensor S : _ →ₗ[A] _) := rfl
      rw [this]; exact (e.lTensor S).bijective
    have hc : (AlgHom.mulLeftRight S (S ⊗[A] Λ) : _ → _) =
        (endBaseChangeMap A S Λ ∘ (AlgHom.mulLeftRight A Λ).toLinearMap.lTensor S) ∘
          (envBaseChange A S Λ).symm := by
      funext y
      simp [← mulLeftRight_envBaseChange]
    rw [hc]
    exact ((endBaseChangeMap_bijective A S Λ).comp hφ).comp (envBaseChange A S Λ).symm.bijective

end GlobalTheory
end

section

noncomputable section

namespace GlobalTheory.OrbitUnfold

def ConjSelf (Γ : Type) : Type := Γ

namespace ConjSelf

variable {Γ : Type} [Group Γ]

def of (γ : Γ) : ConjSelf Γ := γ

def val (γ : ConjSelf Γ) : Γ := γ

instance : MulAction Γ (ConjSelf Γ) where
  smul η γ := of (η * val γ * η⁻¹)
  one_smul γ := by
    change (1 : Γ) * val γ * 1⁻¹ = val γ
    simp
  mul_smul a b γ := by
    change a * b * val γ * (a * b)⁻¹ = a * (b * val γ * b⁻¹) * a⁻¹
    group

theorem val_smul (η : Γ) (γ : ConjSelf Γ) : val (η • γ) = η * val γ * η⁻¹ := rfl

theorem stabilizer_eq_centralizer (γ : ConjSelf Γ) :
    MulAction.stabilizer Γ γ = Subgroup.centralizer {val γ} := by
  ext η
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' := congrArg val h
    rw [val_smul] at h'
    calc η * val γ = η * val γ * η⁻¹ * η := by group
      _ = val γ * η := by rw [h']
  · intro h
    change η * val γ * η⁻¹ = val γ
    rw [h.eq]
    group

end ConjSelf

open ConjSelf

variable {Γ Y : Type} [Group Γ] [MulAction Γ Y]

theorem stabilizer_pair (p : Y × ConjSelf Γ) :
    MulAction.stabilizer Γ p = MulAction.stabilizer Γ p.1 ⊓ Subgroup.centralizer {val p.2} := by
  rw [← stabilizer_eq_centralizer]
  ext η
  simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_inf, Prod.smul_def, Prod.ext_iff]

def pairTerm (F : Y → Γ → ℂ) (p : Y × ConjSelf Γ) : ℂ :=
  ((Nat.card (MulAction.stabilizer Γ p) : ℕ) : ℂ)⁻¹ * F p.1 (val p.2)

theorem pairTerm_smul (F : Y → Γ → ℂ) (hF : ∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ)
    (η : Γ) (p : Y × ConjSelf Γ) : pairTerm F (η • p) = pairTerm F p := by
  unfold pairTerm
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    Subgroup.card_map_of_injective (MulAut.conj η).injective]
  congr 1
  exact hF η p.1 (val p.2)

theorem pairTerm_out (F : Y → Γ → ℂ) (hF : ∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ)
    (p : Y × ConjSelf Γ) :
    pairTerm F (Quotient.out (Quotient.mk (MulAction.orbitRel Γ (Y × ConjSelf Γ)) p)) = pairTerm F p := by
  obtain ⟨η, hη⟩ := Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel Γ (Y × ConjSelf Γ)) p))
  rw [← hη]
  exact pairTerm_smul F hF η p

def pairSum (F : Y → Γ → ℂ) : ℂ :=
  ∑ᶠ o : MulAction.orbitRel.Quotient Γ (Y × ConjSelf Γ), pairTerm F (Quotient.out o)

end GlobalTheory.OrbitUnfold
end
end
