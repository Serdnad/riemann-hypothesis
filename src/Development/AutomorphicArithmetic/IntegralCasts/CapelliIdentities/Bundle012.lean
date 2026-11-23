module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
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
import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.RingTheory.Finiteness.Nakayama
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action

@[expose] public section

section

namespace UpperTheory.Reformulated.B.ExistsAverage

private theorem exists_op {K : Type*} {M : Type*} [Group K] [AddCommGroup M] [Module ℂ M]
    (ρ : K →* Module.End ℂ M) (H : Subgroup K) [H.Normal] [H.FiniteIndex] :
    ∃ A : M →ₗ[ℂ] M,
      (∀ m, (∀ h ∈ H, ρ h m = m) → ∀ k, ρ k (A m) = A m) ∧
      (∀ m, (∀ h ∈ H, ρ h m = m) → ∀ k, A (ρ k m) = A m) ∧
      (∀ m, (∀ k, ρ k m = m) → A m = m) ∧
      (∀ m, m - A m ∈ Submodule.span ℂ {x : M | ∃ k y, x = y - ρ k y}) := by
  classical
  haveI : Fintype (K ⧸ H) := Fintype.ofFinite _
  have hc : ((Fintype.card (K ⧸ H) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have key : ∀ m, (∀ h ∈ H, ρ h m = m) → ∀ g : K, ρ g m = ρ ((g : K ⧸ H).out) m := by
    intro m hm g
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
    rw [hh, map_mul, Module.End.mul_apply, hm h h.2]
  have hA : ∀ m, (((Fintype.card (K ⧸ H) : ℕ) : ℂ)⁻¹ • ∑ q : K ⧸ H, (ρ q.out : M →ₗ[ℂ] M)) m
      = ((Fintype.card (K ⧸ H) : ℕ) : ℂ)⁻¹ • ∑ q : K ⧸ H, ρ q.out m := by
    intro m
    rw [LinearMap.smul_apply, LinearMap.sum_apply]
  have hconst : ∀ m : M, ((Fintype.card (K ⧸ H) : ℕ) : ℂ)⁻¹ • ∑ _q : K ⧸ H, m = m := by
    intro m
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      inv_mul_cancel₀ hc, one_smul]
  refine ⟨((Fintype.card (K ⧸ H) : ℕ) : ℂ)⁻¹ • ∑ q : K ⧸ H, (ρ q.out : M →ₗ[ℂ] M),
    ?_, ?_, ?_, ?_⟩
  · intro m hm k

    rw [hA, map_smul, map_sum]
    congr 1
    refine Fintype.sum_equiv (Equiv.mulLeft (k : K ⧸ H)) _ _ fun q => ?_
    rw [← Module.End.mul_apply, ← map_mul, key m hm]
    simp
  · intro m hm k
    rw [hA, hA]
    congr 1
    refine Fintype.sum_equiv (Equiv.mulRight (k : K ⧸ H)) _ _ fun q => ?_
    rw [← Module.End.mul_apply, ← map_mul, key m hm]
    simp
  · intro m hm
    rw [hA]
    simp only [hm]
    exact hconst m
  · intro m
    rw [hA]
    nth_rewrite 1 [← hconst m]
    rw [← smul_sub, ← Finset.sum_sub_distrib]
    exact Submodule.smul_mem _ _
      (Submodule.sum_mem _ fun q _ => Submodule.subset_span ⟨_, _, rfl⟩)

private theorem exists_sub {K : Type*} {M : Type*} [Group K] [AddCommGroup M] [Module ℂ M]
    [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    (ρ : K →* Module.End ℂ M) (hs : ∀ m : M, IsOpen {k : K | ρ k m = m}) (m : M) :
    ∃ H : Subgroup K, H.Normal ∧ H.FiniteIndex ∧ ∀ h ∈ H, ρ h m = m := by
  let S : Subgroup K :=
    { carrier := {k : K | ρ k m = m}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at *
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at *
        nth_rewrite 1 [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  haveI : Finite (K ⧸ S) := Subgroup.quotient_finite_of_isOpen S (hs m)
  haveI : S.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact ⟨S.normalCore, inferInstance, inferInstance, fun h hh => S.normalCore_le hh⟩

theorem exists_avg {K : Type*} {M : Type*} [Group K] [AddCommGroup M] [Module ℂ M]
    [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    (ρ : K →* Module.End ℂ M) (hs : ∀ m : M, IsOpen {k : K | ρ k m = m}) :
    ∃ P : M →ₗ[ℂ] M, (∀ (m : M) (k : K), ρ k (P m) = P m) ∧
      (∀ m : M, (∀ k : K, ρ k m = m) → P m = m) ∧
      ∀ T : M →ₗ[ℂ] M, (∀ (k : K) (m : M), T (ρ k m) = ρ k (T m)) →
        ∀ m : M, T (P m) = P (T m) := by
  set N : Submodule ℂ M := Submodule.span ℂ {x : M | ∃ k y, x = y - ρ k y} with hN
  have hdis : ∀ x ∈ N, (∀ k, ρ k x = x) → x = 0 := by
    intro x hx hfix
    have : ∃ H : Subgroup K, H.Normal ∧ H.FiniteIndex ∧ ∀ A : M →ₗ[ℂ] M,
        (∀ m, (∀ h ∈ H, ρ h m = m) → ∀ k, A (ρ k m) = A m) → A x = 0 := by
      clear hfix
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k, y, rfl⟩ := hx
        obtain ⟨H, h1, h2, h3⟩ := exists_sub ρ hs y
        exact ⟨H, h1, h2, fun A hA => by rw [map_sub, hA y h3, sub_self]⟩
      | zero => exact ⟨⊤, inferInstance, inferInstance, fun A _ => map_zero A⟩
      | add x y _ _ hx hy =>
        obtain ⟨H, h1, h2, h3⟩ := hx
        obtain ⟨H', h1', h2', h3'⟩ := hy
        refine ⟨H ⊓ H', inferInstance, inferInstance, fun A hA => ?_⟩
        rw [map_add (f := _), h3 A fun m hm => hA m fun h hh => hm h hh.1,
          h3' A fun m hm => hA m fun h hh => hm h hh.2, add_zero]
      | smul c x _ hx =>
        obtain ⟨H, h1, h2, h3⟩ := hx
        exact ⟨H, h1, h2, fun A hA => by rw [map_smul, h3 A hA, smul_zero]⟩
    obtain ⟨H, h1, h2, h3⟩ := this
    obtain ⟨A, -, a2, a3, -⟩ := exists_op ρ H
    rw [← a3 x hfix]
    exact h3 A a2
  have hex : ∀ m : M, ∃ p : M, (∀ k, ρ k p = p) ∧ m - p ∈ N := by
    intro m
    obtain ⟨H, h1, h2, h3⟩ := exists_sub ρ hs m
    obtain ⟨A, a1, -, -, a4⟩ := exists_op ρ H
    exact ⟨A m, a1 m h3, a4 m⟩
  choose f hf1 hf2 using hex
  have huniq : ∀ m p : M, (∀ k, ρ k p = p) → m - p ∈ N → f m = p := by
    intro m p hp hm
    rw [← sub_eq_zero]
    refine hdis _ ?_ fun k => by rw [map_sub, hf1, hp]
    have := N.sub_mem hm (hf2 m)
    rwa [sub_sub_sub_cancel_left] at this
  refine ⟨{ toFun := f, map_add' := ?_, map_smul' := ?_ }, hf1, ?_, ?_⟩
  · intro x y
    refine huniq _ _ (fun k => by rw [map_add (f := _), hf1, hf1]) ?_
    rw [add_sub_add_comm]
    exact N.add_mem (hf2 x) (hf2 y)
  · intro c x
    refine huniq _ _ (fun k => by rw [map_smul, hf1]) ?_
    rw [RingHom.id_apply, ← smul_sub]
    exact N.smul_mem c (hf2 x)
  · intro m hm
    exact huniq m m hm (by rw [sub_self]; exact N.zero_mem)
  · intro T hT m
    refine (huniq (T m) (T (f m)) (fun k => by rw [← hT, hf1]) ?_).symm
    rw [← map_sub]
    have hle : N ≤ N.comap T := by
      rw [hN, Submodule.span_le]
      rintro _ ⟨k, y, rfl⟩
      exact Submodule.subset_span ⟨k, T y, by rw [map_sub, hT]⟩
    exact hle (hf2 m)

end UpperTheory.Reformulated.B.ExistsAverage
end

section

namespace FiniteTypeOfFiniteProjectiveExtension

private lemma exists_retr {C D : Type*} [CommRing C] [CommRing D] [Algebra C D] [Module.Finite C D]
    [Module.Projective C D] (h : Function.Injective (algebraMap C D)) :
    ∃ π : D →ₗ[C] C, π 1 = 1 := by
  let J : Ideal C := LinearMap.range (LinearMap.applyₗ (R := C) (M := D) (M₂ := C) (1 : D))
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective C D
  have key : ∀ d : D, d ∈ J • (⊤ : Submodule C D) := by
    intro d
    have hd : d = ∑ i, g d i • f (Pi.single i 1) := by
      have e1 : d = f (g d) := by
        have := LinearMap.congr_fun hfg d
        simpa using this.symm
      conv_lhs => rw [e1, ← Finset.univ_sum_single (g d)]

      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← map_smul]
      congr 1
      ext j
      simp [Pi.single_apply]
    rw [hd]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul ?_ trivial
    refine LinearMap.mem_range.2 ⟨(LinearMap.proj i).comp (g.comp (LinearMap.mulLeft C d)), ?_⟩
    simp
  obtain ⟨r, hr1, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul J ⊤
    (Module.Finite.fg_top) (fun d _ => key d)
  have hr : r = 0 := h (by simpa [Algebra.smul_def] using hr0 1 trivial)
  have h1 : (1 : C) ∈ J := by
    have := J.neg_mem hr1
    simpa [hr] using this
  obtain ⟨π, hπ⟩ := LinearMap.mem_range.1 h1
  exact ⟨π, by simpa using hπ⟩

end FiniteTypeOfFiniteProjectiveExtension

theorem UpperTheory.Reformulated.B.FiniteTypeDescent.main.{u_1, u_2, u_3} :
    ∀ (R : Type u_1) (C : Type u_2) (D : Type u_3) [inst : CommRing R] [inst_1 : CommRing C] [inst_2 : CommRing D]
      [inst_3 : Algebra R C] [inst_4 : Algebra C D] [inst_5 : Algebra R D] [IsScalarTower R C D] [Module.Finite C D]
      [Module.Projective C D],
      Function.Injective (⇑(Algebra.algebraMap C D) : C → D) → ∀ [Algebra.FiniteType R D], Algebra.FiniteType R C := by
  intro R C D _ _ _ _ _ _ _ _ _ hinj hft
  obtain ⟨π, hπ⟩ := FiniteTypeOfFiniteProjectiveExtension.exists_retr (C := C) (D := D) hinj
  obtain ⟨B₀, hB₀, hB₀D⟩ := exists_subalgebra_of_fg R C D hft.out (Module.Finite.fg_top)
  haveI : Module.Finite B₀ D := ⟨hB₀D⟩
  let π' : D →ₗ[B₀] C := π.restrictScalars B₀
  have hsurj : Function.Surjective π' := fun c =>
    ⟨algebraMap C D c, by
      show π (algebraMap C D c) = c
      rw [Algebra.algebraMap_eq_smul_one, map_smul, hπ, smul_eq_mul, mul_one]⟩
  haveI : Module.Finite B₀ C := Module.Finite.of_surjective π' hsurj
  haveI : Algebra.FiniteType R B₀ := ⟨B₀.fg_top.2 hB₀⟩
  exact Algebra.FiniteType.trans (S := B₀) inferInstance inferInstance
end

section

theorem UpperTheory.Reformulated.B.DYhb1.main :
    ∀ (A M : Type) [inst : CommRing A] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module A M] [Module.Finite A M]
      [Module.Projective A M],
      ∃ (n : ℕ) (e : Fin n → M) (f : Fin n → Module.Dual A M), ∀ (m : M), ∑ i : Fin n, (f i : M → A) m • e i = m := by
  intro A M _ _ _ _ _
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' A M
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p LinearMap.id hp
  refine ⟨n, fun i => p (fun j => if i = j then 1 else 0),
    fun i => (LinearMap.proj i).comp s, fun m => ?_⟩
  have h1 : p (s m) = m := by
    have := LinearMap.congr_fun hs m
    simpa using this
  have h2 := LinearMap.pi_apply_eq_sum_univ p (s m)
  rw [h1] at h2
  exact h2.symm
end

section

theorem UpperTheory.Reformulated.B.LocallyTrivialClassesAddEquiv.main :
    ∀ {R ι H C : Type} [inst : CommRing R] [inst_1 : AddCommGroup H] [inst_2 : _root_.Module R H] [inst_3 : AddCommGroup C]
      {Hv Cv : ι → Type} [inst_4 : (v : ι) → AddCommGroup (Hv v)] [inst_5 : (v : ι) → AddCommGroup (Cv v)]
      (res : (v : ι) → H →+ Hv v) (pres : (v : ι) → C →+ Cv v) (E : H ≃+ C) (Ev : (v : ι) → Hv v ≃+ Cv v),
      (∀ (v : ι) (x : H), (Ev v : Hv v → Cv v) ((res v : H → Hv v) x) = (pres v : C → Cv v) ((E : H → C) x)) →
        ∀ (U : Submodule R H) (T : AddSubgroup C),
          (∀ (x : H), x ∈ U ↔ ∀ (v : ι), (res v : H → Hv v) x = (0 : Hv v)) →
            (∀ (y : C), y ∈ T ↔ ∀ (v : ι), (pres v : C → Cv v) y = (0 : Cv v)) → Nonempty (↥U ≃+ ↥T) := by
  intro R ι H C _ _ _ _ Hv Cv _ _ res pres E Ev hcomm U T hU hT
  have key : ∀ x : H, x ∈ U ↔ E x ∈ T := by
    intro x
    rw [hU, hT]
    refine forall_congr' fun v => ?_
    rw [← hcomm v x]
    constructor
    · intro h; rw [h, map_zero]
    · intro h
      have := congrArg (Ev v).symm h
      simpa using this
  exact ⟨{ toFun := fun x => ⟨E x.1, (key x.1).1 x.2⟩
           invFun := fun y => ⟨E.symm y.1, (key _).2 (by simpa using y.2)⟩
           left_inv := fun x => by ext; simp
           right_inv := fun y => by ext; simp
           map_add' := fun x y => by ext; simp }⟩
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qf7.GLOps.{u_2, u_3} :
    ℕ → (K : Type u_2) → (V : Type u_3) → [inst : Field K] → [inst_1 : AddCommGroup V] → [_root_.Module K V] → Type u_3 :=
    fun (n : ℕ) (K : Type u_2) (V : Type u_3) [Field K] [AddCommGroup V] [_root_.Module K V] ↦
      Fin n → Fin n → Module.End K V

noncomputable def UpperTheory.Reformulated.B.Qf7.weightSp.{u_2, u_3} :
    {n : ℕ} →
      {K : Type u_2} →
        {V : Type u_3} →
          [inst : Field K] →
            [inst_1 : AddCommGroup V] →
              [inst_2 : _root_.Module K V] → UpperTheory.Reformulated.B.Qf7.GLOps n K V → (Fin n → ℤ) → Submodule K V :=
    fun {n : ℕ} {K : Type u_2} {V : Type u_3} [Field K] [AddCommGroup V] [_root_.Module K V]
        (E : UpperTheory.Reformulated.B.Qf7.GLOps n K V) (mu : Fin n → ℤ) ↦
      ⨅ (a : Fin n), LinearMap.ker (E a a - (↑(mu a) : K) • (1 : Module.End K V))

private theorem UpperTheory.Reformulated.B.Qf7.apply_of_mem_weightSp {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V]
    [_root_.Module K V] {E : UpperTheory.Reformulated.B.Qf7.GLOps n K V} {mu : Fin n → ℤ} {x : V}
    (hx : x ∈ UpperTheory.Reformulated.B.Qf7.weightSp E mu) (a : Fin n) : E a a x = (mu a : K) • x := by
  unfold UpperTheory.Reformulated.B.Qf7.weightSp at hx
  have h := (Submodule.mem_iInf _).1 hx a
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    sub_eq_zero] at h
  exact h

theorem UpperTheory.Reformulated.B.Qf7.weight_components_mem_invariant.{u_1, u_2} :
    ∀ {n : ℕ} {K : Type u_1} {V : Type u_2} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]
      [CharZero K] (E : UpperTheory.Reformulated.B.Qf7.GLOps n K V) (W : Submodule K V),
      (∀ (a : Fin n), ∀ x ∈ W, (E a a : V → V) x ∈ W) →
        ∀ (s : Finset (Fin n → ℤ)) (f : (Fin n → ℤ) → V),
          (∀ mu ∈ s, f mu ∈ UpperTheory.Reformulated.B.Qf7.weightSp E mu) → ∑ mu ∈ s, f mu ∈ W → ∀ mu ∈ s, f mu ∈ W := by
  intro n K V _ _ _ _ E W hW s
  classical
  induction s using Finset.induction_on with
  | empty => intro f _ _ mu hmu; simp at hmu
  | insert nu t hnu ih =>
    intro f hf hsum
    have ht : ∀ mu ∈ t, f mu ∈ W := by
      intro mu hmu
      have hne : mu ≠ nu := fun h => hnu (h ▸ hmu)
      obtain ⟨a, ha⟩ := Function.ne_iff.1 hne
      have h1 : E a a (∑ l ∈ insert nu t, f l) - (nu a : K) • (∑ l ∈ insert nu t, f l) ∈ W :=
        W.sub_mem (hW a _ hsum) (W.smul_mem _ hsum)
      have h2 : E a a (∑ l ∈ insert nu t, f l) - (nu a : K) • (∑ l ∈ insert nu t, f l)
          = ∑ l ∈ insert nu t, ((l a : K) - (nu a : K)) • f l := by

        rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun l hl => ?_
        rw [UpperTheory.Reformulated.B.Qf7.apply_of_mem_weightSp (hf l hl) a, sub_smul]
      rw [h2, Finset.sum_insert hnu, sub_self, zero_smul, zero_add] at h1
      have h3 := ih (fun l => ((l a : K) - (nu a : K)) • f l)
        (fun l hl => Submodule.smul_mem _ _ (hf l (Finset.mem_insert_of_mem hl))) h1 mu hmu
      have hc : ((mu a : K) - (nu a : K)) ≠ 0 :=
        sub_ne_zero.2 (fun h => ha (Int.cast_injective h))
      exact (W.smul_mem_iff hc).1 h3
    intro mu hmu
    rcases Finset.mem_insert.1 hmu with rfl | hmu
    · rw [Finset.sum_insert hnu] at hsum
      exact (W.add_mem_iff_left (W.sum_mem ht)).1 hsum
    · exact ht mu hmu
end

section

theorem UpperTheory.Reformulated.B.Qh12.ell :
    ∀ (O Λ Γ X : Type) [inst : CommRing O] [inst_1 : CommRing Λ] [inst_2 : Algebra O Λ]
    [inst_3 : CommGroup Γ] [inst_4 : AddCommGroup X] [inst_5 : _root_.Module O X] (th₀ : Λ →ₐ[O] O) (d : Λ →ₗ[O] X)
    (χ : Γ →* Multiplicative X),
    (∀ (a b : Λ), (d : Λ → X) (a * b) = (th₀ : Λ → O) a • (d : Λ → X) b + (th₀ : Λ → O) b • (d : Λ → X) a) →
      ∃ (th : MonoidAlgebra Λ Γ →ₐ[O] O) (ell : MonoidAlgebra Λ Γ →ₗ[O] X),
        (∀ (g : Γ) (a : Λ), (th : MonoidAlgebra Λ Γ → O) (MonoidAlgebra.single g a) = (th₀ : Λ → O) a) ∧
          (∀ (a b : MonoidAlgebra Λ Γ),
              (ell : MonoidAlgebra Λ Γ → X) (a * b) =
                (th : MonoidAlgebra Λ Γ → O) a • (ell : MonoidAlgebra Λ Γ → X) b +
                  (th : MonoidAlgebra Λ Γ → O) b • (ell : MonoidAlgebra Λ Γ → X) a) ∧
            ∀ (g : Γ) (a : Λ),
              (ell : MonoidAlgebra Λ Γ → X) (MonoidAlgebra.single g a) =
                (d : Λ → X) a +
                  (th₀ : Λ → O) a • (Multiplicative.toAdd : Multiplicative X → X) ((χ : Γ → Multiplicative X) g) := by
  intro O Λ Γ X _ _ _ _ _ _ th₀ d χ hd
  classical
  let th : MonoidAlgebra Λ Γ →ₐ[O] O :=
    MonoidAlgebra.liftNCAlgHom th₀ (1 : Γ →* O) (fun _ _ => Commute.all _ _)
  have hth : ∀ (g : Γ) (a : Λ), th (MonoidAlgebra.single g a) = th₀ a := by
    intro g a
    simp [th]
  let ell : MonoidAlgebra Λ Γ →ₗ[O] X :=
    (Finsupp.lsum O (fun g : Γ => d + th₀.toLinearMap.smulRight (Multiplicative.toAdd (χ g)))) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv O).toLinearMap
  have hell : ∀ (g : Γ) (a : Λ), ell (MonoidAlgebra.single g a)
      = d a + th₀ a • Multiplicative.toAdd (χ g) := by
    intro g a
    simp [ell]
  refine ⟨th, ell, hth, ?_, hell⟩
  intro a b
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a a' ha ha' =>
    simp only [add_mul, map_add (f := _), ha, ha', add_smul, smul_add]
    abel
  | single g a =>
    induction b using MonoidAlgebra.induction_linear with
    | zero => simp
    | add b b' hb hb' =>
      simp only [mul_add, map_add (f := _), hb, hb', add_smul, smul_add]
      abel
    | single h b =>
      rw [MonoidAlgebra.single_mul_single, hell, hell, hell, hth, hth, hd, map_mul, map_mul,
        toAdd_mul]
      module
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qj21.XZ :
    Type → ℕ → ℕ → Type :=
    fun (Lt : Type) (N0 N1 : ℕ) ↦ Lt × ℕ × Fin N0 ⊕ Lt × Fin N0 × Fin N1

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qj21.PolyXZ :
    Type → ℕ → ℕ → Type :=
    fun (H : Type) (N0 N1 : ℕ) ↦ MvPolynomial (UpperTheory.Reformulated.B.Qj21.XZ (Bool × H) N0 N1) ℤ

noncomputable def UpperTheory.Reformulated.B.Qj21.lfo :
    {H : Type} → {N0 N1 : ℕ} → H → ℕ × Fin N1 → UpperTheory.Reformulated.B.Qj21.PolyXZ H N0 N1 :=
    fun {H : Type} {N0 N1 : ℕ} (t : H) (c : ℕ × Fin N1) ↦
      ∑ a : Fin N0, MvPolynomial.X (Sum.inl ((Bool.false, t), c.1, a)) * MvPolynomial.X (Sum.inr ((Bool.false, t), a, c.2))

noncomputable def UpperTheory.Reformulated.B.Qj21.tmL :
    {H : Type} → {N0 N1 : ℕ} → H → List (ℕ × Fin N1) → UpperTheory.Reformulated.B.Qj21.PolyXZ H N0 N1 → UpperTheory.Reformulated.B.Qj21.PolyXZ H N0 N1 :=
    fun {H : Type} {N0 N1 : ℕ} (t : H) (L : List (ℕ × Fin N1)) (h : UpperTheory.Reformulated.B.Qj21.PolyXZ H N0 N1) ↦
      (List.map (UpperTheory.Reformulated.B.Qj21.lfo t) L).prod * h

noncomputable def UpperTheory.Reformulated.B.Qj21.nzc :
    {N1 : ℕ} → List (ℕ × Fin N1) → ℕ :=
    fun {N1 : ℕ} (L : List (ℕ × Fin N1)) ↦
      (List.map (fun (c : ℕ × Fin N1) ↦ if c.1 = (0 : ℕ) then (0 : ℕ) else (1 : ℕ)) L).sum

noncomputable def UpperTheory.Reformulated.B.Qj21.z0c :
    {N1 : ℕ} → List (ℕ × Fin N1) → ℕ :=
    fun {N1 : ℕ} (L : List (ℕ × Fin N1)) ↦
      (List.map (fun (c : ℕ × Fin N1) ↦ if c.1 = (0 : ℕ) then (1 : ℕ) else (0 : ℕ)) L).sum

noncomputable def UpperTheory.Reformulated.B.Qj21.MS :
    {H : Type} → {N0 N1 : ℕ} → H → ℕ → ℕ → Submodule ℤ (UpperTheory.Reformulated.B.Qj21.PolyXZ H N0 N1) :=
    fun {H : Type} {N0 N1 : ℕ} (t : H) (a b : ℕ) ↦
      Submodule.span ℤ
        {Q : UpperTheory.Reformulated.B.Qj21.PolyXZ H N0 N1 |
          ∃ (L : List (ℕ × Fin N1)),
            Q = UpperTheory.Reformulated.B.Qj21.tmL t L (1 : UpperTheory.Reformulated.B.Qj21.PolyXZ H N0 N1) ∧
              UpperTheory.Reformulated.B.Qj21.nzc L = a ∧ UpperTheory.Reformulated.B.Qj21.z0c L = b}

theorem UpperTheory.Reformulated.B.Qj21.ms_mul :
    ∀ {H : Type} {N0 N1 : ℕ} (t : H) {a b a' b' : ℕ} {P Q : UpperTheory.Reformulated.B.Qj21.PolyXZ H N0 N1},
      P ∈ UpperTheory.Reformulated.B.Qj21.MS t a b → Q ∈ UpperTheory.Reformulated.B.Qj21.MS t a' b' → P * Q ∈ UpperTheory.Reformulated.B.Qj21.MS t (a + a') (b + b') := by
  intro H N0 N1 t a b a' b' P Q hP hQ
  have key : UpperTheory.Reformulated.B.Qj21.MS (N0 := N0) (N1 := N1) t a b * UpperTheory.Reformulated.B.Qj21.MS t a' b'
      ≤ UpperTheory.Reformulated.B.Qj21.MS t (a + a') (b + b') := by
    unfold UpperTheory.Reformulated.B.Qj21.MS
    rw [Submodule.span_mul_span]
    apply Submodule.span_mono
    rintro _ ⟨x, ⟨L, rfl, h1, h2⟩, y, ⟨L', rfl, h3, h4⟩, rfl⟩
    refine ⟨L ++ L', ?_, ?_, ?_⟩
    · simp only [UpperTheory.Reformulated.B.Qj21.tmL, List.map_append, List.prod_append, mul_one]
    · rw [← h1, ← h3]
      simp only [UpperTheory.Reformulated.B.Qj21.nzc, List.map_append, List.sum_append]
    · rw [← h2, ← h4]
      simp only [UpperTheory.Reformulated.B.Qj21.z0c, List.map_append, List.sum_append]
  exact key (Submodule.mul_mem_mul hP hQ)
end
