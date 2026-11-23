module

public import Mathlib.NumberTheory.NumberField.Basic
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.PicardGroup
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
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.FractionalIdeal.Operations

@[expose] public section

section

open NumberField Module

namespace GlobalTheory

theorem exists_basis_closure_eq_of_fg_of_nsmul_mem {Γ : Type} [AddCommGroup Γ] [Module ℚ Γ]
    (A : AddSubgroup Γ) (hA : A.FG) (hN : ∀ x : Γ, ∃ N : ℕ, 0 < N ∧ N • x ∈ A) :
    ∃ (n : ℕ) (b : Basis (Fin n) ℚ Γ), A = AddSubgroup.closure (Set.range b) := by
  classical
  have : HasUniqueDiv Γ := .of_module_rat Γ
  have : Module.Finite ℤ A :=
    Module.Finite.iff_addGroup_fg.mpr ((AddGroup.fg_iff_addSubgroup_fg A).mpr hA)
  let bA := Module.finBasis ℤ A
  let v : Fin (Module.finrank ℤ A) → Γ := fun i => (bA i : Γ)
  have hliZ : LinearIndependent ℤ v :=
    bA.linearIndependent.map' A.subtype.toIntLinearMap
      (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hli : LinearIndependent ℚ v := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hliZ
  have hcl : A = AddSubgroup.closure (Set.range v) := by
    apply le_antisymm
    · intro a ha
      have h' : a = ∑ i, bA.repr ⟨a, ha⟩ i • v i := by
        conv_lhs => rw [show a = ((⟨a, ha⟩ : A) : Γ) from rfl, ← bA.sum_repr ⟨a, ha⟩]
        rw [AddSubgroup.val_finsetSum]
        simp [v]
      rw [h']
      exact AddSubgroup.sum_mem _ fun i _ =>
        AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self i)) _
    · rw [AddSubgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact (bA i).2
  have hsp : ⊤ ≤ Submodule.span ℚ (Set.range v) := by
    intro x _
    obtain ⟨N, hN0, hNx⟩ := hN x
    have hmem : N • x ∈ Submodule.span ℚ (Set.range v) := by
      rw [hcl] at hNx
      exact (AddSubgroup.closure_le (Submodule.span ℚ (Set.range v)).toAddSubgroup).mpr
        Submodule.subset_span hNx
    rw [← Nat.cast_smul_eq_nsmul ℚ] at hmem
    have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN0.ne'
    have := Submodule.smul_mem _ (N : ℚ)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hN', one_smul] at this
  refine ⟨Module.finrank ℤ A, Basis.mk hli hsp, ?_⟩
  rw [Basis.coe_mk]
  exact hcl

theorem relIndex_map_nsmul_comap_eq_abs_norm_det :
    ∀ (E Γ : Type) [Field E] [NumberField E] [AddCommGroup Γ] [Module E Γ] [FiniteDimensional E Γ] (A : AddSubgroup Γ), A.FG → (∀ x : Γ, ∃ N : ℕ, 0 < N ∧ N • x ∈ A) → ∀ (m : Module.End E Γ) (N : ℕ), N ≠ 0 → LinearMap.det m ≠ 0 → (∀ x ∈ A, N • m x ∈ A) → (((A.map (N • AddMonoidHom.id Γ)).relIndex (A.comap m.toAddMonoidHom) : ℕ) : ℚ) = |Algebra.norm ℚ ((N : E) ^ Module.finrank E Γ * LinearMap.det m)| := by
  intro E Γ _ _ _ _ _ A hA hAN m N hN0 hdet hmA
  classical
  letI : Module ℚ Γ := Module.compHom Γ (algebraMap ℚ E)
  have : IsScalarTower ℚ E Γ := ⟨fun q c x => by
    show (q • c) • x = algebraMap ℚ E q • (c • x)
    rw [Algebra.smul_def, mul_smul]⟩
  obtain ⟨n, b, hb⟩ := exists_basis_closure_eq_of_fg_of_nsmul_mem A hA hAN
  have : FiniteDimensional ℚ Γ := Module.Finite.of_basis b
  let mQ : Γ →ₗ[ℚ] Γ := m.restrictScalars ℚ
  have hdetQ : LinearMap.det mQ = Algebra.norm ℚ (LinearMap.det m) :=
    LinearMap.det_restrictScalars
  have hdetQ0 : LinearMap.det mQ ≠ 0 := by
    rw [hdetQ]
    exact Algebra.norm_ne_zero_iff.mpr hdet
  have hu : IsUnit mQ := (LinearMap.isUnit_iff_isUnit_det mQ).mpr (isUnit_iff_ne_zero.mpr hdetQ0)
  let e : Γ ≃ₗ[ℚ] Γ := LinearEquiv.ofBijective mQ ((Module.End.isUnit_iff mQ).mp hu)
  have he : ∀ x, e x = m x := fun x => rfl
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN0
  let b₁ : Basis (Fin n) ℚ Γ := b.map (LinearEquiv.smulOfNeZero ℚ Γ (N : ℚ) hN')
  let b₂ : Basis (Fin n) ℚ Γ := b.map e.symm
  have hb₁ : ∀ i, b₁ i = N • b i := fun i => by
    simp [b₁, Nat.cast_smul_eq_nsmul]
  have h₁ : A.map (N • AddMonoidHom.id Γ) = AddSubgroup.closure (Set.range b₁) := by
    rw [hb, AddMonoidHom.map_closure, ← Set.range_comp]
    congr 1
    ext x
    simp [hb₁]
  have h₂ : A.comap m.toAddMonoidHom = AddSubgroup.closure (Set.range b₂) := by
    have hr : Set.range b₂ = e.symm.toLinearMap.toAddMonoidHom '' Set.range b := by
      rw [← Set.range_comp]
      rfl
    rw [hr, ← AddMonoidHom.map_closure, ← hb]
    ext x
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_map]
    constructor
    · intro hx
      exact ⟨m x, hx, by rw [← he]; exact e.symm_apply_apply x⟩
    · rintro ⟨a, ha, rfl⟩
      change m (e.symm a) ∈ A
      rw [← he, e.apply_symm_apply]
      exact ha
  have hle : A.map (N • AddMonoidHom.id Γ) ≤ A.comap m.toAddMonoidHom := by
    rintro _ ⟨a, ha, rfl⟩
    change m (N • a) ∈ A
    rw [map_nsmul]
    exact hmA a ha
  rw [AddSubgroup.relIndex_eq_abs_det _ _ hle b₁ b₂ h₁ h₂]
  congr 1
  have hcomp : e.symm.symm ∘ b₁ = ((N : ℚ) • mQ) ∘ b := by
    funext i
    simp only [Function.comp_apply, LinearEquiv.symm_symm, hb₁, LinearMap.smul_apply,
      Nat.cast_smul_eq_nsmul]
    rw [he, map_nsmul]
    rfl
  rw [Basis.det_map, hcomp, Basis.det_comp, Basis.det_self, mul_one, LinearMap.det_smul, hdetQ,
    map_mul, map_pow, ← map_natCast (algebraMap ℚ E), Algebra.norm_algebraMap, ← pow_mul,
    Module.finrank_mul_finrank]

end GlobalTheory
end

section

open NumberField

namespace GlobalTheory

theorem linearIndependent_images_of_rankOne_lattice :
    ∀ {K : Type} [Field K] [NumberField K] {p m n : ℕ} (ell : Submodule (𝓞 K) (Fin m → K))
    (M : Fin p → ((Fin m → K) →ₗ[K] (Fin n → K))) (v : Fin m → K), v ≠ 0 → ∀ (𝔟 : Submodule (𝓞 K) K),
    𝔟 ≠ ⊥ → (∀ e, e ∈ ell ↔ ∃ β ∈ 𝔟, e = β • v) → (∀ a, Function.Injective (M a)) →
    iSupIndep (fun a => Submodule.span K
      ((ell.map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K))) →
    LinearIndependent K (fun a => M a v) := by
  intro K _ _ p m n ell M v hv 𝔟 h𝔟 hell hinj hind
  obtain ⟨β, hβ, hβ0⟩ := (Submodule.ne_bot_iff 𝔟).1 h𝔟
  refine hind.linearIndependent _ (fun a => ?_) (fun a => ?_)
  · have hmem : M a (β • v) ∈ Submodule.span K
        ((ell.map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K)) :=
      Submodule.subset_span ⟨β • v, (hell _).2 ⟨β, hβ, rfl⟩, rfl⟩
    have : M a v = β⁻¹ • M a (β • v) := by
      rw [map_smul, smul_smul, inv_mul_cancel₀ hβ0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ hmem
  · intro h
    exact hv ((hinj a) (by rw [h, map_zero]))

end GlobalTheory
end

section

open scoped TensorProduct Polynomial

namespace GlobalTheory

theorem exists_numberField_of_finiteType_rat (R : Type) [CommRing R] [Nontrivial R] [Algebra ℚ R]
    [Algebra.FiniteType ℚ R] : ∃ (K : Type) (_ : Field K) (_ : NumberField K) (φ : R →+* K), True := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType ℚ (R ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℚ m) Ideal.Quotient.mk_surjective
  haveI : Module.Finite ℚ (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℚ (R ⧸ m)
  haveI : CharZero (R ⧸ m) := algebraRat.charZero _
  have hfin := (inferInstance : Module.Finite ℚ (R ⧸ m))
  haveI : @FiniteDimensional ℚ (R ⧸ m) _ _ (@Algebra.toModule ℚ (R ⧸ m) _ _ DivisionRing.toRatAlgebra) := by
    have e : (Ideal.Quotient.algebra ℚ : Algebra ℚ (R ⧸ m)) = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
    convert hfin
    first
      | exact (congrArg (@Algebra.toModule ℚ (R ⧸ m) _ _) e).symm
      | (rw [← e]; rfl)
  haveI : NumberField (R ⧸ m) := ⟨⟩
  exact ⟨R ⧸ m, inferInstance, inferInstance, Ideal.Quotient.mk m, trivial⟩

theorem exists_numberField_point_ne_zero :
    ∀ (A : Type) [CommRing A] [IsDomain A] [CharZero A], Algebra.FiniteType ℤ A →
      ∀ a : A, a ≠ 0 → ∃ (K : Type) (_ : Field K) (_ : NumberField K) (χ : A →+* K), χ a ≠ 0 := by
  intro A _ _ _ hA a ha
  classical
  obtain ⟨s, hs⟩ := hA.out
  let F := FractionRing A
  let f : A →+* F := algebraMap A F
  let B : Subalgebra ℚ F := Algebra.adjoin ℚ (insert (f a)⁻¹ ((s.image f : Finset F) : Set F))
  have hmem : ∀ x : A, f x ∈ B := by
    intro x
    have hx : x ∈ Algebra.adjoin ℤ (s : Set A) := by rw [hs]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ (by simpa using ⟨x, hx, rfl⟩))
    | algebraMap n =>
      have : f (algebraMap ℤ A n) = algebraMap ℚ F (n : ℚ) := by simp [f]
      rw [this]; exact B.algebraMap_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact B.add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact B.mul_mem hx hy
  have hinv : (f a)⁻¹ ∈ B := Algebra.subset_adjoin (Set.mem_insert _ _)
  haveI hBft : Algebra.FiniteType ℚ B := by
    rw [← Subalgebra.fg_iff_finiteType]
    exact ⟨insert (f a)⁻¹ (s.image f), by simp [B]⟩
  have hfa : f a ≠ 0 := by
    simpa [f] using (IsFractionRing.injective A F).ne ha
  let ψ : A →+* B := f.codRestrict B hmem
  have hu : IsUnit (ψ a) := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨(f a)⁻¹, hinv⟩, Subtype.ext ?_⟩
    show f a * (f a)⁻¹ = 1
    exact mul_inv_cancel₀ hfa
  obtain ⟨K, _, _, φ, -⟩ := exists_numberField_of_finiteType_rat B
  exact ⟨K, inferInstance, inferInstance, φ.comp ψ, (hu.map φ).ne_zero⟩

end GlobalTheory
end

section

open NumberField

namespace GlobalTheory.GensModNsmul

theorem exists_gen_mod_nsmul_of_linearMap (E : Type) [Field E] [NumberField E] (M : ℕ) (hM : 1 ≤ M)
    (N : Type) [AddCommGroup N] [Module (𝓞 E) N] [Module.Finite (𝓞 E) N] (π : N →ₗ[𝓞 E] E) :
    ∃ l : N, ∀ x : N, ∃ o : 𝓞 E, ∃ y : N, π x = o • π l + M • π y := by
  have hfg : (LinearMap.range π).FG := by
    rw [LinearMap.range_eq_map]; exact Module.Finite.fg_top.map _
  obtain ⟨d, hd, hint⟩ := FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors (𝓞 E)) hfg
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hd0' : (algebraMap (𝓞 E) E d) ≠ 0 := by simpa using hd0
  set I : Ideal (𝓞 E) := Submodule.comap (Algebra.linearMap (𝓞 E) E) (LinearMap.range (d • π)) with hI
  have hmem : ∀ a : 𝓞 E, a ∈ I ↔ ∃ x : N, d • π x = algebraMap (𝓞 E) E a := by
    intro a; simp [hI]
  have hM0 : (M : 𝓞 E) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have key : ∃ a ∈ I, Ideal.span {(M : 𝓞 E)} * I ⊔ Ideal.span {a} = I := by
    by_cases h : I = ⊥
    · exact ⟨0, I.zero_mem, by simp [h]⟩
    · obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq
        (I := Ideal.span {(M : 𝓞 E)} * I) (J := I) Ideal.mul_le_right
        (mul_ne_zero (by simpa using hM0) h)
      refine ⟨a, ?_, ha⟩
      rw [← ha]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
  obtain ⟨a, haI, ha⟩ := key
  obtain ⟨l, hl⟩ := (hmem a).1 haI
  refine ⟨l, fun x => ?_⟩
  obtain ⟨b, hb⟩ := hint (π x) ⟨x, rfl⟩
  have hbI : b ∈ I := (hmem b).2 ⟨x, hb.symm⟩
  rw [← ha, Submodule.mem_sup] at hbI
  obtain ⟨u, hu, v, hv, huv⟩ := hbI
  obtain ⟨c, hc, rfl⟩ := Ideal.mem_span_singleton_mul.1 hu
  obtain ⟨o, rfl⟩ := Ideal.mem_span_singleton'.1 hv
  obtain ⟨y, hy⟩ := (hmem c).1 hc
  refine ⟨o, y, ?_⟩
  apply mul_left_cancel₀ hd0'
  rw [Algebra.smul_def] at hb hl hy
  rw [← hb, ← huv, Algebra.smul_def, nsmul_eq_mul, map_add (f := _), map_mul, map_mul, map_natCast, ← hl, ← hy]
  ring

theorem exists_gens_mod_nsmul_of_injective (E : Type) [Field E] [NumberField E] (M : ℕ) (hM : 1 ≤ M)
    (r : ℕ) : ∀ (N : Type) [AddCommGroup N] [Module (𝓞 E) N] [Module.Finite (𝓞 E) N]
    (f : N →ₗ[𝓞 E] (Fin r → E)), Function.Injective f →
    ∃ e : Fin r → N, ∀ x : N, ∃ o : Fin r → 𝓞 E, ∃ y : N, x = ∑ i, o i • e i + M • y := by
  induction r with
  | zero =>
    intro N _ _ _ f hf
    refine ⟨Fin.elim0, fun x => ⟨Fin.elim0, 0, ?_⟩⟩
    simpa using hf (Subsingleton.elim (f x) (f 0))
  | succ r ih =>
    intro N _ _ _ f hf
    let π : N →ₗ[𝓞 E] E := (LinearMap.proj 0) ∘ₗ f
    obtain ⟨l, hl⟩ := exists_gen_mod_nsmul_of_linearMap E M hM N π
    let f' : LinearMap.ker π →ₗ[𝓞 E] (Fin r → E) :=
      LinearMap.pi fun i => (LinearMap.proj i.succ) ∘ₗ f ∘ₗ (LinearMap.ker π).subtype
    have hf' : Function.Injective f' := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro x hx
      apply Subtype.ext
      apply hf
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [Submodule.coe_zero, map_zero]; exact x.2
      · simpa [f'] using congrFun hx j
    obtain ⟨e, he⟩ := ih (LinearMap.ker π) f' hf'
    refine ⟨Fin.cons l (fun i => (e i : N)), fun x => ?_⟩
    obtain ⟨o, y, hoy⟩ := hl x
    have hk : x - o • l - M • y ∈ LinearMap.ker π := by
      rw [LinearMap.mem_ker, map_sub, map_sub, map_smul, map_nsmul, hoy]; abel
    obtain ⟨o', y', h'⟩ := he ⟨_, hk⟩
    refine ⟨Fin.cons o o', y + y', ?_⟩
    have h2 := congrArg Subtype.val h'
    simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul,
      Submodule.coe_smul_of_tower] at h2
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, smul_add]
    have : x = o • l + M • y + (x - o • l - M • y) := by abel
    rw [this, h2]; abel

theorem exists_gens_mod_nsmul (E : Type) [Field E] [NumberField E] (r M : ℕ)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (hM : 1 ≤ M) (hΛ : Λ.FG) :
    ∃ e : Fin r → Fin r → E, (∀ i, e i ∈ Λ) ∧
      ∀ x ∈ Λ, ∃ o : Fin r → 𝓞 E, ∃ y ∈ Λ, x = ∑ i, o i • e i + M • y := by
  haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hΛ
  obtain ⟨e, he⟩ := exists_gens_mod_nsmul_of_injective E M hM r Λ Λ.subtype Subtype.val_injective
  refine ⟨fun i => e i, fun i => (e i).2, fun x hx => ?_⟩
  obtain ⟨o, y, h⟩ := he ⟨x, hx⟩
  refine ⟨o, y, y.2, ?_⟩
  have h2 := congrArg Subtype.val h
  simpa only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul,
      Submodule.coe_smul_of_tower] using h2

end GlobalTheory.GensModNsmul
end

section

open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory

open NumberField in
open scoped nonZeroDivisors in
private theorem one_mem_colon_one_smul_of_fg {E : Type} [Field E] [NumberField E]
    (A : Submodule (𝓞 E) E) (hA : A.FG) (h1 : (1 : E) ∈ A) :
    (1 : E) ∈ ((1 : Submodule (𝓞 E) E).colon (A : Set E)) • A := by
  set Af : FractionalIdeal (𝓞 E)⁰ E := ⟨A, FractionalIdeal.isFractional_of_fg hA⟩ with hAf
  have hne : Af ≠ 0 := by
    intro h
    have : (1 : E) ∈ Af := h1
    rw [h, FractionalIdeal.mem_zero_iff] at this
    exact one_ne_zero this
  have hmem : (1 : E) ∈ ((Af * Af⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) := by
    rw [mul_inv_cancel₀ hne]; exact FractionalIdeal.one_mem_one _
  rw [FractionalIdeal.coe_mul] at hmem
  refine Submodule.mul_induction_on hmem (fun a ha x hx => ?_) (fun _ _ => add_mem)
  have hinv : ∀ y ∈ A, x * y ∈ (1 : Submodule (𝓞 E) E) := by
    intro y hy
    have := FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coe.mp hx) (show y ∈ Af from hy)
    rw [inv_mul_cancel₀ hne] at this
    rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_one] at this
    exact this
  obtain ⟨i, rfl⟩ := Submodule.mem_one.mp (by simpa using hinv 1 h1)
  have hi : i ∈ (1 : Submodule (𝓞 E) E).colon (A : Set E) := by
    rw [Submodule.mem_colon]
    intro s hs
    rw [Algebra.smul_def]
    exact hinv s hs
  rw [mul_comm, ← Algebra.smul_def]
  exact Submodule.smul_mem_smul hi ha


open NumberField in
open scoped nonZeroDivisors in
theorem _root_.GlobalTheory.colon_one_span_image_eq_map {E K : Type} [Field E] [NumberField E] [Field K]
    [NumberField K]
    (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K) (hτ : ∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K))
    (A : Submodule (𝓞 E) E) (hA : A.FG) (h1 : (1 : E) ∈ A) :
    (1 : Submodule (𝓞 K) K).colon (Submodule.span (𝓞 K) (τE '' A) : Set K) =
      ((1 : Submodule (𝓞 E) E).colon (A : Set E)).map τ := by
  have key := one_mem_colon_one_smul_of_fg A hA h1
  apply le_antisymm
  · intro r hr
    rw [Submodule.mem_colon] at hr
    have hb : ∀ a ∈ A, ∃ u : 𝓞 K, (u : K) = (r : K) * τE a := by
      intro a ha
      obtain ⟨u, hu⟩ := Submodule.mem_one.mp (hr _ (Submodule.subset_span ⟨a, ha, rfl⟩))
      rw [Algebra.smul_def] at hu
      exact ⟨u, hu⟩
    have hP : ∀ x ∈ ((1 : Submodule (𝓞 E) E).colon (A : Set E)) • A,
        ∃ t ∈ ((1 : Submodule (𝓞 E) E).colon (A : Set E)).map τ, (t : K) = (r : K) * τE x := by
      intro x hx
      refine Submodule.smul_induction_on
        (p := fun x => ∃ t ∈ ((1 : Submodule (𝓞 E) E).colon (A : Set E)).map τ,
          (t : K) = (r : K) * τE x) hx (fun i hi a ha => ?_) ?_
      · obtain ⟨u, hu⟩ := hb a ha
        refine ⟨τ i * u, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem τ hi), ?_⟩
        rw [Algebra.smul_def, map_mul]
        change ((τ i : 𝓞 K) : K) * (u : K) = (r : K) * (τE (i : E) * τE a)
        rw [hu, hτ]
        ring
      · rintro x y ⟨t, ht, hte⟩ ⟨t', ht', hte'⟩
        refine ⟨t + t', add_mem ht ht', ?_⟩
        rw [map_add (f := _), mul_add, ← hte, ← hte']
        rfl
    obtain ⟨t, ht, hte⟩ := hP 1 key
    rw [map_one, mul_one] at hte
    have htr : t = r := by exact_mod_cast hte
    rwa [← htr]
  · rw [Ideal.map_le_iff_le_comap]
    intro i hi
    rw [Ideal.mem_comap, Submodule.mem_colon]
    intro s hs
    rw [SetLike.mem_coe] at hs
    induction hs using Submodule.span_induction with
    | mem s hs =>
      obtain ⟨a, ha, rfl⟩ := hs
      obtain ⟨y, hy⟩ := Submodule.mem_one.mp ((Submodule.mem_colon.mp hi) a ha)
      refine Submodule.mem_one.mpr ⟨τ y, ?_⟩
      rw [Algebra.smul_def] at hy ⊢
      change (y : E) = (i : E) * a at hy
      change ((τ y : 𝓞 K) : K) = ((τ i : 𝓞 K) : K) * τE a
      rw [← hτ, ← hτ, hy, map_mul]
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ c hx

end GlobalTheory
end

section

open NumberField

namespace GlobalTheory

open TensorProduct nonZeroDivisors in
theorem finrank_int_eq_finrank_ringOfIntegers_mul : ∀ (E : Type) [Field E] [NumberField E] (N : Type) [AddCommGroup N] [Module (𝓞 E) N] [Module.Free ℤ N] [Module.Finite ℤ N], Module.finrank ℤ N = Module.finrank (𝓞 E) N * Module.finrank ℚ E := by
  intro E _ _ N _ _ _ _
  let g : N →ₗ[𝓞 E] E ⊗[𝓞 E] N := TensorProduct.mk (𝓞 E) E N 1
  have hb : IsBaseChange E g := TensorProduct.isBaseChange (𝓞 E) N E
  have h1 : Module.finrank E (E ⊗[𝓞 E] N) = Module.finrank (𝓞 E) N := hb.finrank_eq
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) E := inferInstance
  haveI h2 : IsLocalizedModule (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) g :=
    (isLocalizedModule_iff_isBaseChange _ E g).2 hb
  haveI h3 : IsLocalizedModule ℤ⁰ (g.restrictScalars ℤ) :=
    IsLocalizedModule.restrictScalars ℤ⁰ g
  have h4 : Module.finrank ℤ (E ⊗[𝓞 E] N) = Module.finrank ℤ N :=
    IsLocalizedModule.finrank_eq ℤ⁰ (g.restrictScalars ℤ) le_rfl
  have h5 : Module.finrank ℚ (E ⊗[𝓞 E] N) = Module.finrank ℤ (E ⊗[𝓞 E] N) :=
    IsFractionRing.finrank_right_eq ℤ ℚ _
  rw [← h4, ← h5, ← h1, mul_comm, Module.finrank_mul_finrank]
end GlobalTheory
end

end

section

@[expose] public section

open scoped TensorProduct Polynomial
theorem _root_.GlobalTheory.T.finite_type_to_number_field : ∀ (A : Type) [CommRing A] [IsDomain A] [CharZero A], Algebra.FiniteType ℤ A → ∀ a : A, a ≠ 0 → ∃ (K : Type) (_ : Field K) (_ : NumberField K) (χ : A →+* K), χ a ≠ 0 := by
  first | exact @_root_.GlobalTheory.exists_numberField_point_ne_zero | exact _root_.GlobalTheory.exists_numberField_point_ne_zero | (intros; apply _root_.GlobalTheory.exists_numberField_point_ne_zero <;> assumption)

end
end
