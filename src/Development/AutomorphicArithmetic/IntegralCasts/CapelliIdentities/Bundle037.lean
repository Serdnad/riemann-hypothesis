module

public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.CategoryTheory.Functor.OfSequence
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
public import Mathlib.Order.KonigLemma
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Data.Nat.Init
public import Mathlib.Order.Basic
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Preorder
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Data.Finset.Insert
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Order.AddGroupWithTop
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Finset.Fin

@[expose] public section

section

private def UpperTheory.Reformulated.B.Qi50.proj {P : ℕ → Type 1} (t : (j : ℕ) → P (j + 1) → P j)
    {i j : ℕ} (h : i ≤ j) : P j → P i :=
  Nat.leRec (motive := fun j _ => P j → P i) id (fun k _ f => f ∘ t k) h

private theorem UpperTheory.Reformulated.B.Qi50.proj_self {P : ℕ → Type 1} (t : (j : ℕ) → P (j + 1) → P j)
    {i : ℕ} (h : i ≤ i) (a : P i) : UpperTheory.Reformulated.B.Qi50.proj t h a = a := by
  unfold UpperTheory.Reformulated.B.Qi50.proj
  rw [Nat.leRec_self]
  rfl

private theorem UpperTheory.Reformulated.B.Qi50.proj_succ {P : ℕ → Type 1} (t : (j : ℕ) → P (j + 1) → P j)
    {i j : ℕ} (h : i ≤ j) (h' : i ≤ j + 1) (a : P (j + 1)) :
    UpperTheory.Reformulated.B.Qi50.proj t h' a = UpperTheory.Reformulated.B.Qi50.proj t h (t j a) := by
  unfold UpperTheory.Reformulated.B.Qi50.proj
  rw [Nat.leRec_succ _ _ h]
  rfl

private theorem UpperTheory.Reformulated.B.Qi50.proj_trans {P : ℕ → Type 1} (t : (j : ℕ) → P (j + 1) → P j)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (a : P k) :
    UpperTheory.Reformulated.B.Qi50.proj t hij (UpperTheory.Reformulated.B.Qi50.proj t hjk a)
      = UpperTheory.Reformulated.B.Qi50.proj t (hij.trans hjk) a := by
  induction k, hjk using Nat.le_induction with
  | base => rw [UpperTheory.Reformulated.B.Qi50.proj_self]
  | succ k hk ih =>
    rw [UpperTheory.Reformulated.B.Qi50.proj_succ t hk, UpperTheory.Reformulated.B.Qi50.proj_succ t (hij.trans hk), ih]

theorem UpperTheory.Reformulated.B.Qi50.seq_sec :
    ∀ (P : ℕ → Type 1),
    (∀ (j : ℕ), Finite (P j)) →
      (∀ (j : ℕ), Nonempty (P j)) →
        ∀ (t : (j : ℕ) → P (j + (1 : ℕ)) → P j), ∃ (s : (j : ℕ) → P j), ∀ (j : ℕ), t j (s (j + (1 : ℕ))) = s j := by
  intro P hfin hne t
  obtain ⟨s, hs⟩ := exists_seq_forall_proj_of_forall_finite (α := P)
    (fun h => UpperTheory.Reformulated.B.Qi50.proj t h)
    (fun _ a => UpperTheory.Reformulated.B.Qi50.proj_self t _ a)
    (fun _ _ _ hij hjk a => UpperTheory.Reformulated.B.Qi50.proj_trans t hij hjk a)
    (fun _ _ => Set.toFinite _)
  refine ⟨s, fun j => ?_⟩
  have h := hs (Nat.le_succ j)
  rwa [UpperTheory.Reformulated.B.Qi50.proj_succ t le_rfl, UpperTheory.Reformulated.B.Qi50.proj_self] at h
end

section

theorem UpperTheory.Reformulated.B.DYdc6.main :
    ∀ {X : ℕ → Type} [∀ (n : ℕ), Finite (X n)] [∀ (n : ℕ), Nonempty (X n)] (f : (n : ℕ) → X (n + (1 : ℕ)) → X n),
      ∃ (x : (n : ℕ) → X n), ∀ (n : ℕ), f n (x (n + (1 : ℕ))) = x n := by
  intro X _ _ f
  let F : CategoryTheory.Functor ℕᵒᵖ Type :=
    CategoryTheory.Functor.ofOpSequence (X := X) (fun n => TypeCat.ofHom (f n))
  haveI : ∀ j : ℕᵒᵖ, Finite (F.obj j) := fun j => inferInstanceAs (Finite (X j.unop))
  haveI : ∀ j : ℕᵒᵖ, Nonempty (F.obj j) := fun j => inferInstanceAs (Nonempty (X j.unop))
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_inverse_system F
  refine ⟨fun n => s (Opposite.op n), fun n => ?_⟩
  have h := hs (CategoryTheory.homOfLE (Nat.le_add_right n 1)).op
  rw [CategoryTheory.Functor.ofOpSequence_map_homOfLE_succ] at h
  exact h
end

section

theorem UpperTheory.Reformulated.B.OneAddPowLeTwoPowMul.main :
    ∀ (t : ℝ), (0 : ℝ) ≤ t → ∀ (N : ℕ), ((1 : ℝ) + t) ^ N ≤ (2 : ℝ) ^ N * ((1 : ℝ) + t ^ N) := by
  intro t ht N
  have h1 : (1 : ℝ) + t ≤ 2 * max 1 t := by
    linarith [le_max_left (1 : ℝ) t, le_max_right (1 : ℝ) t]
  have h2 : ((1 : ℝ) + t) ^ N ≤ (2 * max 1 t) ^ N := pow_le_pow_left₀ (by linarith) h1 N
  rw [mul_pow] at h2
  have h3 : (max (1 : ℝ) t) ^ N ≤ 1 + t ^ N := by
    rcases le_total t 1 with h | h
    · rw [max_eq_left h, one_pow]
      have : (0 : ℝ) ≤ t ^ N := pow_nonneg ht N
      linarith
    · rw [max_eq_right h]
      linarith
  calc ((1 : ℝ) + t) ^ N ≤ 2 ^ N * (max 1 t) ^ N := h2
    _ ≤ 2 ^ N * (1 + t ^ N) := mul_le_mul_of_nonneg_left h3 (by positivity)
end

section

theorem UpperTheory.Reformulated.B.Ydd5.main :
    ∀ {I : Type} (s : Finset I) (c : ℝ),
      (0 : ℝ) < c → ∀ (f : I → ℝ), (∀ (i : I), (0 : ℝ) < f i) → ∃ (ρ : ℝ), (0 : ℝ) < ρ ∧ ρ ≤ c ∧ ∀ i ∈ s, ρ ≤ f i := by
  intro I s c hc f hf
  classical
  refine Finset.induction_on s ?_ ?_
  · exact ⟨c, hc, le_rfl, by simp⟩
  · intro a t _ ih
    obtain ⟨ρ, h0, h1, h2⟩ := ih
    refine ⟨min ρ (f a), lt_min h0 (hf a), (min_le_left _ _).trans h1, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (h2 i hi)
end

section

theorem UpperTheory.Reformulated.B.Qm9.det_sq_eq_one_of_preserves_bilin.{u_1} :
    ∀ {V : Type u_1} [inst : AddCommGroup V]
    [inst_1 : _root_.Module ℝ V] [FiniteDimensional ℝ V] (B : LinearMap.BilinForm ℝ V),
    B.Nondegenerate →
      ∀ (f : V →ₗ[ℝ] V),
        (∀ (x y : V), ((B : V → V →ₗ[ℝ] ℝ) ((f : V → V) x) : V → ℝ) ((f : V → V) y) = ((B : V → V →ₗ[ℝ] ℝ) x : V → ℝ) y) →
          (LinearMap.det : (V →ₗ[ℝ] V) → ℝ) f ^ (2 : ℕ) = (1 : ℝ) := by
  intro V _ _ _ B hB f hf
  classical
  let b := Module.finBasis ℝ V
  have hcomp : B.comp f f = B := by
    ext x y
    simpa using hf x y
  have hmat := LinearMap.BilinForm.toMatrix_comp b b B f f
  rw [hcomp] at hmat
  have hne : (LinearMap.BilinForm.toMatrix b B).det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hB
  have hdet := congrArg Matrix.det hmat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix] at hdet
  apply mul_left_cancel₀ hne
  linear_combination -hdet
end

section

noncomputable def UpperTheory.Reformulated.B.Qh31.vR :
    {K : Type} → [inst : Field K] → AddValuation K (WithTop ℚ) → K → WithTop ℝ :=
    fun {K : Type} [Field K] (v : AddValuation K (WithTop ℚ)) (x : K) ↦
      WithTop.map (fun (n : ℚ) ↦ (↑n : ℝ)) ((v : K → WithTop ℚ) x)

noncomputable def UpperTheory.Reformulated.B.Qh31.vge :
    {K : Type} → [inst : Field K] → AddValuation K (WithTop ℚ) → ℝ → K → Prop :=
    fun {K : Type} [Field K] (v : AddValuation K (WithTop ℚ)) (a : ℝ) (x : K) ↦ (↑a : WithTop ℝ) ≤ UpperTheory.Reformulated.B.Qh31.vR v x

private theorem UpperTheory.Reformulated.B.Qh31.map_cast_mono :
    Monotone (WithTop.map (fun (n : ℚ) ↦ (↑n : ℝ))) :=
  Monotone.withTop_map (fun _ _ h ↦ Rat.cast_le.mpr h)

theorem UpperTheory.Reformulated.B.Qh31.vge_sum :
    ∀ {K : Type} [inst : Field K] (v : AddValuation K (WithTop ℚ)) {ι : Type} {a : ℝ} (s : Finset ι) (f : ι → K),
      (∀ i ∈ s, UpperTheory.Reformulated.B.Qh31.vge v a (f i)) → UpperTheory.Reformulated.B.Qh31.vge v a (∑ i ∈ s, f i) := by
  intro K _ v ι a s f h
  refine Finset.sum_induction f (UpperTheory.Reformulated.B.Qh31.vge v a) ?_ ?_ h
  · intro x y hx hy
    unfold UpperTheory.Reformulated.B.Qh31.vge UpperTheory.Reformulated.B.Qh31.vR at *
    rcases min_le_iff.mp (v.map_add x y) with hxy | hxy
    · exact hx.trans (UpperTheory.Reformulated.B.Qh31.map_cast_mono hxy)
    · exact hy.trans (UpperTheory.Reformulated.B.Qh31.map_cast_mono hxy)
  · unfold UpperTheory.Reformulated.B.Qh31.vge UpperTheory.Reformulated.B.Qh31.vR
    rw [v.map_zero, WithTop.map_top]
    exact le_top
end

section

private theorem UpperTheory.cyclic_trivial_induction_ring {R : Type} [Ring R] (hR : ∀ c : R, ∃ m : ℤ, c = m) :
    ∀ {H : Type} [Monoid H] (n : ℕ) (P : Rep.{0, 0, 0} R H → Prop),
        (∀ C : Rep.{0, 0, 0} R H, Finite C.V → IsAddCyclic C.V →
          (∀ (g : H) (c : C.V), C.ρ g c = c) → (∀ c : C.V, n • c = 0) → P C) →
        (∀ (A B C : Rep.{0, 0, 0} R H) (f : A ⟶ B) (g : B ⟶ C),
          (∀ (h : H) (a : A.V), A.ρ h a = a) → (∀ (h : H) (c : C.V), C.ρ h c = c) →
          Function.Injective f.hom → Function.Exact f.hom g.hom → Function.Surjective g.hom →
          P A → P C → P B) →
        ∀ A : Rep.{0, 0, 0} R H, Finite A.V →
          (∀ (g : H) (a : A.V), A.ρ g a = a) → (∀ a : A.V, n • a = 0) → P A := by
  intro H _ n P hcyc hext A
  induction hk : Nat.card A.V using Nat.strong_induction_on generalizing A with
  | _ k ih =>
    intro hfin htriv htors
    by_cases hne : ∃ a : A.V, a ≠ 0
    · obtain ⟨a, ha⟩ := hne
      let B : Submodule R A.V := Submodule.span _ {a}
      let S : Rep.{0, 0, 0} R H := Rep.of (Representation.trivial R H B)
      let Q : Rep.{0, 0, 0} R H :=
        Rep.of (Representation.trivial R H (A.V ⧸ B))
      let f : S ⟶ A := Rep.ofHom (ρ := Representation.trivial R H B) (σ := A.ρ)
        (B.subtype.intertwiningMap_of_isIntertwiningMap _ _ (fun g v => by
          simpa using (htriv g v.1).symm))
      let g : A ⟶ Q := Rep.ofHom (ρ := A.ρ) (σ := Representation.trivial R H (A.V ⧸ B))
        (B.mkQ.intertwiningMap_of_isIntertwiningMap _ _ (fun g v => by
          simp [htriv g v]))
      have hlt : Nat.card (A.V ⧸ B) < Nat.card A.V := by
        by_contra hcon
        have hbij := (Submodule.mkQ_surjective B).bijective_of_nat_card_le (not_lt.mp hcon)
        have hmem : a ∈ B := Submodule.mem_span_singleton_self a
        have h0 : B.mkQ a = B.mkQ 0 := by
          simpa using (Submodule.Quotient.mk_eq_zero B).2 hmem
        exact ha (hbij.1 h0)
      have hS : P S := by
        refine hcyc S (inferInstanceAs (Finite B)) ?_ (fun _ _ => rfl) ?_
        · refine (⟨⟨⟨a, Submodule.mem_span_singleton_self a⟩, fun x => ?_⟩⟩ : IsAddCyclic B)
          obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 x.2
          obtain ⟨m, rfl⟩ := hR c
          refine AddSubgroup.mem_zmultiples_iff.2 ⟨m, Subtype.ext ?_⟩
          rw [← hc, Int.cast_smul_eq_zsmul]
          rfl
        · intro c
          exact Subtype.ext (htors c.1)
      have hQ : P Q := by
        refine ih (Nat.card (A.V ⧸ B)) (hk ▸ hlt) Q rfl
          (Finite.of_surjective B.mkQ (Submodule.mkQ_surjective B))
          (fun _ _ => rfl) ?_
        intro c
        obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective B c
        have : n • B.mkQ x = B.mkQ (n • x) := (map_nsmul B.mkQ n x).symm
        exact this.trans (by rw [htors x, map_zero])
      exact hext S A Q f g (fun _ _ => rfl) (fun _ _ => rfl) (Subtype.val_injective)
        (LinearMap.exact_subtype_mkQ B) (Submodule.mkQ_surjective B) hS hQ
    · have : Subsingleton A.V := ⟨fun x y => by
        push_neg at hne
        rw [hne x, hne y]⟩
      exact hcyc A hfin inferInstance htriv htors

theorem UpperTheory.cyclic_trivial_induction :
    ∀ {H : Type} [Monoid H] (n : ℕ) (P : Rep.{0, 0, 0} (ULift.{0, 0} ℤ) H → Prop),
        (∀ C : Rep.{0, 0, 0} (ULift.{0, 0} ℤ) H, Finite C.V → IsAddCyclic C.V →
          (∀ (g : H) (c : C.V), C.ρ g c = c) → (∀ c : C.V, n • c = 0) → P C) →
        (∀ (A B C : Rep.{0, 0, 0} (ULift.{0, 0} ℤ) H) (f : A ⟶ B) (g : B ⟶ C),
          (∀ (h : H) (a : A.V), A.ρ h a = a) → (∀ (h : H) (c : C.V), C.ρ h c = c) →
          Function.Injective f.hom → Function.Exact f.hom g.hom → Function.Surjective g.hom →
          P A → P C → P B) →
        ∀ A : Rep.{0, 0, 0} (ULift.{0, 0} ℤ) H, Finite A.V →
          (∀ (g : H) (a : A.V), A.ρ g a = a) → (∀ a : A.V, n • a = 0) → P A := by
  intro H _
  exact UpperTheory.cyclic_trivial_induction_ring (R := ULift.{0, 0} ℤ) (fun c => ⟨c.down, ULift.ext (by simp)⟩)
end

section

open CategoryTheory in
private lemma exists_lift {k : Type} [CommRing k] {K L M : CochainComplex (ModuleCat.{0} k) ℕ}
    (u : K ⟶ M) (ι : L ⟶ M) (hι : ∀ m : ℕ, Function.Injective (ι.f m).hom)
    (h : ∀ (m : ℕ) (x : K.X m), ∃ y, (ι.f m).hom y = (u.f m).hom x) :
    ∃ φ : K ⟶ L, ∀ (m : ℕ) (x : K.X m), (ι.f m).hom ((φ.f m).hom x) = (u.f m).hom x := by
  let p : ∀ m : ℕ, K.X m ⟶ L.X m := fun m =>
    ModuleCat.ofHom ((u.f m).hom.codRestrictOfInjective (ι.f m).hom (hι m) (h m))
  have hp : ∀ m : ℕ, p m ≫ ι.f m = u.f m := fun m =>
    ModuleCat.hom_ext (LinearMap.codRestrictOfInjective_comp _ _ _ _)
  refine ⟨{ f := p, comm' := fun i j _ => ?_ }, fun m x => congr($(hp m).hom x)⟩
  haveI : Mono (ι.f j) := (ModuleCat.mono_iff_injective _).2 (hι j)
  rw [← cancel_mono (ι.f j), Category.assoc, Category.assoc, hp, ← ι.comm, ← Category.assoc, hp,
    u.comm]

open CategoryTheory in
private lemma exists_map {k G : Type} [CommRing k] [Group G] [TopologicalSpace G]
    {A B : Rep.{0, 0, 0} k G} (f : A ⟶ B) {KA KB : CochainComplex (ModuleCat.{0} k) ℕ}
    (ιA : KA ⟶ groupCohomology.inhomogeneousCochains A)
    (ιB : KB ⟶ groupCohomology.inhomogeneousCochains B)
    (iB : ∀ m : ℕ, Function.Injective (ιB.f m).hom)
    (hA : ∀ (m : ℕ) (x : (Fin m → G) → A.V), (∃ y, (ιA.f m).hom y = x) ↔ IsLocallyConstant x)
    (hB : ∀ (m : ℕ) (x : (Fin m → G) → B.V), (∃ y, (ιB.f m).hom y = x) ↔ IsLocallyConstant x) :
    ∃ φ : KA ⟶ KB, ∀ (m : ℕ) (x : KA.X m) (t : Fin m → G),
      ((ιB.f m).hom ((φ.f m).hom x) : (Fin m → G) → B.V) t =
        f.hom (((ιA.f m).hom x : (Fin m → G) → A.V) t) := by
  obtain ⟨φ, hφ⟩ := exists_lift (ιA ≫ groupCohomology.cochainsMap (MonoidHom.id G) f) ιB iB
    fun m x => (hB m _).2 (((hA m _).1 ⟨x, rfl⟩).comp f.hom)
  exact ⟨φ, fun m x t => congr_fun (hφ m x) t⟩

theorem UpperTheory.cochain_injective_exact :
    ∀ {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] (A B C : Rep.{0, 0, 0} k G)
        (f : A ⟶ B) (g : B ⟶ C) (KA KB KC : CochainComplex (ModuleCat.{0} k) ℕ)
        (ιA : KA ⟶ groupCohomology.inhomogeneousCochains A)
        (ιB : KB ⟶ groupCohomology.inhomogeneousCochains B)
        (ιC : KC ⟶ groupCohomology.inhomogeneousCochains C),
        Function.Injective f.hom → Function.Exact f.hom g.hom → Function.Surjective g.hom →
        (∀ m : ℕ, Function.Injective (ιA.f m).hom) → (∀ m : ℕ, Function.Injective (ιB.f m).hom) →
        (∀ m : ℕ, Function.Injective (ιC.f m).hom) →
        (∀ (m : ℕ) (x : (Fin m → G) → A.V), (∃ y, (ιA.f m).hom y = x) ↔ IsLocallyConstant x) →
        (∀ (m : ℕ) (x : (Fin m → G) → B.V), (∃ y, (ιB.f m).hom y = x) ↔ IsLocallyConstant x) →
        (∀ (m : ℕ) (x : (Fin m → G) → C.V), (∃ y, (ιC.f m).hom y = x) ↔ IsLocallyConstant x) →
        ∃ (φ : KA ⟶ KB) (ψ : KB ⟶ KC) (w : CategoryTheory.CategoryStruct.comp φ ψ = 0),
          (CategoryTheory.ShortComplex.mk φ ψ w).ShortExact := by
  intro k G _ _ _ A B C f g KA KB KC ιA ιB ιC hf hfg hg iA iB iC hA hB hC
  obtain ⟨φ, hφ⟩ := exists_map f ιA ιB iB hA hB
  obtain ⟨ψ, hψ⟩ := exists_map g ιB ιC iC hB hC
  have w : CategoryTheory.CategoryStruct.comp φ ψ = 0 := by
    ext m : 1
    refine ModuleCat.hom_ext (LinearMap.ext fun x => iC m ?_)
    change (ιC.f m).hom ((ψ.f m).hom ((φ.f m).hom x)) = (ιC.f m).hom 0
    rw [map_zero]
    funext t
    rw [hψ, hφ]
    exact hfg.apply_apply_eq_zero _
  refine ⟨φ, ψ, w, HomologicalComplex.shortExact_of_degreewise_shortExact _ fun m => ?_⟩
  have hm : CategoryTheory.Mono (φ.f m) := by
    refine (ModuleCat.mono_iff_injective _).2 fun a b hab => iA m (funext fun t => hf ?_)
    have hab' : (φ.f m).hom a = (φ.f m).hom b := hab
    rw [← hφ, ← hφ, hab']
  have he : CategoryTheory.Epi (ψ.f m) := by
    refine (ModuleCat.epi_iff_surjective _).2 fun c => ?_
    obtain ⟨b, hb⟩ := (hB m _).2 (((hC m _).1 ⟨c, rfl⟩).comp (Function.surjInv hg))
    refine ⟨b, iC m (funext fun t => ?_)⟩
    refine (hψ m b t).trans ?_
    rw [hb]
    exact Function.surjInv_eq hg _
  refine { exact := ?_, mono_f := hm, epi_g := he }
  refine (CategoryTheory.ShortComplex.moduleCat_exact_iff _).2 fun (b : KB.X m) hb => ?_
  have hb0 : (ψ.f m).hom b = 0 := hb
  have hb' : ∀ t : Fin m → G, ∃ a, f.hom a = ((ιB.f m).hom b : (Fin m → G) → B.V) t := fun t => by
    refine (hfg _).1 ?_
    rw [← hψ, hb0, map_zero]
    rfl
  choose a ha using hb'
  have hla : IsLocallyConstant a := by
    refine IsLocallyConstant.desc a f.hom ?_ hf
    have e : f.hom ∘ a = (ιB.f m).hom b := funext ha
    rw [e]
    exact (hB m _).1 ⟨b, rfl⟩
  obtain ⟨y, hy⟩ := (hA m a).2 hla
  refine ⟨y, iB m (funext fun t => ?_)⟩
  refine (hφ m y t).trans ?_
  rw [hy]
  exact ha t
end

section

theorem UpperTheory.Reformulated.B.Yhb2.main :
    ∀ {a : WithBot ℕ∞} {d : ℕ}, a < (↑(d + (1 : ℕ)) : WithBot ℕ∞) → a ≤ (↑d : WithBot ℕ∞) := by
  intro a d h
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe b =>
    have h1 : b < ((d+1 : ℕ) : ℕ∞) := by exact_mod_cast h
    have h2 : b ≤ (d : ℕ∞) := by
      induction b using ENat.recTopCoe with
      | top => exact absurd h1 (not_lt.mpr le_top)
      | coe n =>
        have h3 : n < d + 1 := by exact_mod_cast h1
        exact_mod_cast Nat.lt_succ_iff.mp h3
    exact_mod_cast h2
end

section

theorem UpperTheory.Reformulated.B.Qn14.le_of_add_one_le_succ :
    ∀ {a : WithBot ℕ∞} {k : ℕ},
    a + (1 : WithBot ℕ∞) ≤ (↑(k + (1 : ℕ)) : WithBot ℕ∞) → a ≤ (↑k : WithBot ℕ∞) := by
  intro a k h
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have h1 : ((⊤ : ℕ∞) + 1 : ℕ∞) ≤ ((k + 1 : ℕ) : ℕ∞) := by
        rw [← WithBot.coe_le_coe]
        exact h
      rw [top_add, top_le_iff] at h1
      exact ENat.coe_ne_top _ h1
    | coe n =>
      have h1 : ((n : ℕ∞) + 1 : ℕ∞) ≤ ((k + 1 : ℕ) : ℕ∞) := by
        rw [← WithBot.coe_le_coe]
        exact h
      have h2 : n + 1 ≤ k + 1 := by exact_mod_cast h1
      have h3 : (n : ℕ∞) ≤ (k : ℕ∞) := by exact_mod_cast (Nat.le_of_succ_le_succ h2)
      exact WithBot.coe_le_coe.mpr h3
end

section

theorem UpperTheory.Reformulated.B.Ydd3.withBot_eq_of_le_of_add_one_le :
    ∀ {x : WithBot ℕ∞} {c : ℕ},
      (↑c : WithBot ℕ∞) ≤ x → x + (1 : WithBot ℕ∞) ≤ (↑(c + (1 : ℕ)) : WithBot ℕ∞) → x = (↑c : WithBot ℕ∞) := by
  intro x c h1 h2
  induction x using WithBot.recBotCoe with
  | bot => exact le_antisymm bot_le h1
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      exfalso
      have h3 : ((⊤ : ℕ∞) + 1 : ℕ∞) ≤ ((c + 1 : ℕ) : ℕ∞) := by exact_mod_cast h2
      rw [top_add, top_le_iff] at h3
      exact ENat.coe_ne_top _ h3
    | coe n =>
      have h3 : c ≤ n := by exact_mod_cast h1
      have h4 : n + 1 ≤ c + 1 := by exact_mod_cast h2
      have h5 : n = c := by omega
      subst h5
      rfl
end

section

theorem UpperTheory.Reformulated.B.DYlb8.main :
    ∀ {n : ℕ} {S : Finset (Fin n)}, (∀ (a b : Fin n), b ≤ a → a ∈ S → b ∈ S) → ∀ (a : Fin n), a ∈ S ↔ (↑a : ℕ) < S.card := by
  intro n S h a
  constructor
  · intro ha
    have hsub : Finset.Iic a ⊆ S := fun b hb => h a b (Finset.mem_Iic.mp hb) ha
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hcard
    omega
  · intro hlt
    by_contra ha
    have hsub : S ⊆ Finset.Iio a :=
      fun b hb => Finset.mem_Iio.mpr (lt_of_not_ge fun hab => ha (h b a hab hb))
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hcard
    omega
end
