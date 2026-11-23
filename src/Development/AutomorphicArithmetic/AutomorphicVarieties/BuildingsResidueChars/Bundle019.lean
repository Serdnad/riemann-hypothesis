module

public import Formalism.RealPlaceAnalysis.Bundle003
public import GroundTheory.AutomorphicForms.AdelicGLn
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Uniform
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.FormsFiniteAlt
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Archimedean
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.AltSum
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

@[expose] public section

section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem UpperTheory.quantum_determinant_map {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    (X : Fin n → Fin n → A) (u : ℂ) : f (Formalism.REAL.qdet X u) = Formalism.REAL.qdet (fun i j => f (X i j)) u := by

  simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, Formalism.REAL.Tm, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn,
  Function.comp_def, map_add, apply_ite f, AlgHom.commutes, map_zero]

theorem UpperTheory.algMod_of_injective_intertwining :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (N : Type) [AddCommGroup N] [Module ℂ N] (n : ℕ) (f : M →ₗ[ℂ] N) (E : Fin n → Fin n → Module.End ℂ M) (E' : Fin n → Fin n → Module.End ℂ N), (∀ i j x, f (E i j x) = E' i j (f x)) → ∀ u x, f (Formalism.REAL.qdet E u x) = Formalism.REAL.qdet E' u (f x) := by
  intro M _ _ N _ _ n f E E' h u x
  let S : Subalgebra ℂ (Module.End ℂ M × Module.End ℂ N) :=
    { carrier := {p | ∀ y, f (p.1 y) = p.2 (f y)}
      mul_mem' := fun {a b} ha hb y => (ha _).trans (congrArg a.2 (hb y))
      add_mem' := fun {a b} ha hb y => by
        simp only [Prod.fst_add, Prod.snd_add, LinearMap.add_apply, map_add (f := _), ha y, hb y]
      algebraMap_mem' := fun c y => map_smul f c y }
  let Z : Fin n → Fin n → S := fun i j => ⟨(E i j, E' i j), h i j⟩
  have h1 : (Formalism.REAL.qdet Z u).1.1 = Formalism.REAL.qdet E u :=
    UpperTheory.quantum_determinant_map ((AlgHom.fst ℂ _ _).comp S.val) Z u
  have h2 : (Formalism.REAL.qdet Z u).1.2 = Formalism.REAL.qdet E' u :=
    UpperTheory.quantum_determinant_map ((AlgHom.snd ℂ _ _).comp S.val) Z u
  rw [← h1, ← h2]
  exact (Formalism.REAL.qdet Z u).2 x
end

section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem exists_normal_open_level_subgroup {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H L : Subgroup G) (hHc : IsCompact (H : Set G)) (hHo : IsOpen (H : Set G))
    (hL : IsOpen (L : Set G)) :
    ∃ L' : Subgroup G, IsOpen (L' : Set G) ∧ L' ≤ L ∧ (∀ k ∈ H, ∀ u ∈ L', k⁻¹ * u * k ∈ L') ∧
      ∃ t : Finset G, ∀ k ∈ H, ∃ c ∈ t, c⁻¹ * k ∈ L' := by
  classical
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hHc
  have hNo : IsOpen ((L.subgroupOf H : Subgroup H) : Set H) := hL.preimage continuous_subtype_val
  haveI : Finite (H ⧸ L.subgroupOf H) := (L.subgroupOf H).quotient_finite_of_isOpen hNo
  haveI : (L.subgroupOf H).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hCo : IsOpen ((L.subgroupOf H).normalCore : Set H) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _
      ((L.subgroupOf H).normalCore_isClosed (Subgroup.isClosed_of_isOpen _ hNo))
  refine ⟨(L.subgroupOf H).normalCore.map H.subtype, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.coe_map]
    exact hHo.isOpenMap_subtype_val _ hCo
  · rintro _ ⟨u, hu, rfl⟩
    have := (L.subgroupOf H).normalCore_le hu
    exact this
  · rintro k hk _ ⟨u, hu, rfl⟩
    refine ⟨(⟨k, hk⟩ : H)⁻¹ * u * ⟨k, hk⟩, ?_, by simp⟩
    have := (Subgroup.normalCore_normal (L.subgroupOf H)).conj_mem u hu ((⟨k, hk⟩ : H)⁻¹)
    simpa using this
  · haveI : Finite (H ⧸ (L.subgroupOf H).normalCore) := Subgroup.finite_quotient_of_finiteIndex
    letI := Fintype.ofFinite (H ⧸ (L.subgroupOf H).normalCore)
    refine ⟨Finset.univ.image (fun q : H ⧸ (L.subgroupOf H).normalCore => ((q.out : H) : G)), ?_⟩
    intro k hk
    refine ⟨(((QuotientGroup.mk ⟨k, hk⟩ : H ⧸ (L.subgroupOf H).normalCore).out : H) : G),
      Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    have := QuotientGroup.eq.1
      (QuotientGroup.out_eq' (QuotientGroup.mk ⟨k, hk⟩ : H ⧸ (L.subgroupOf H).normalCore))
    exact ⟨_, this, by simp⟩

theorem UpperTheory.exists_open_level_normalized_by_integralFiniteGL :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (L : Subgroup (AdelicGLn.FiniteAdelicGL K n)), IsOpen (L : Set (AdelicGLn.FiniteAdelicGL K n)) → ∃ L' : Subgroup (AdelicGLn.FiniteAdelicGL K n), IsOpen (L' : Set (AdelicGLn.FiniteAdelicGL K n)) ∧ L' ≤ L ∧ (∀ k ∈ AdelicGLn.integralFiniteGL K n, ∀ u ∈ L', k⁻¹ * u * k ∈ L') ∧ ∃ t : Finset (AdelicGLn.FiniteAdelicGL K n), ∀ k ∈ AdelicGLn.integralFiniteGL K n, ∃ c ∈ t, c⁻¹ * k ∈ L' := by
  intro K _ _ n L hL
  exact exists_normal_open_level_subgroup _ L (AdelicGLn.isCompact_integralFiniteGL K n)
    (AdelicGLn.isOpen_integralFiniteGL K n) hL
end

section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.locallyFinite_of_algMod_criterion :
    ∀ (X Y : Type) [MeasurableSpace X] (μ : Measure X) (V : Submodule ℂ (Y → ℂ)), FiniteDimensional ℂ V → ∀ F : X → Y → ℂ, (∀ x, F x ∈ V) → (∀ y, Integrable (fun x => F x y) μ) → (fun y => ∫ x, F x y ∂μ) ∈ V := by
  intro X Y _ μ V hV F hF hI
  classical
  let ev : Y → (V →ₗ[ℂ] ℂ) := fun y => (LinearMap.proj y).comp V.subtype
  have hspan : Submodule.span ℂ (Set.range ev) = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro z hz
    by_contra h
    apply hz
    ext y
    by_contra hy
    exact h ⟨ev y, ⟨y, rfl⟩, hy⟩
  have hint : ∀ φ : V →ₗ[ℂ] ℂ, Integrable (fun x => φ ⟨F x, hF x⟩) μ := by
    intro φ
    have hφ : φ ∈ Submodule.span ℂ (Set.range ev) := hspan ▸ Submodule.mem_top
    induction hφ using Submodule.span_induction with
    | mem f hf => obtain ⟨y, rfl⟩ := hf; exact hI y
    | zero => simp
    | add f g _ _ hf hg => exact hf.add hg
    | smul c f _ hf => exact hf.const_mul c
  let b := Module.finBasis ℂ V
  have key : (fun y => ∫ x, F x y ∂μ)
      = ∑ i, (∫ x, b.coord i ⟨F x, hF x⟩ ∂μ) • ((b i : V) : Y → ℂ) := by
    funext y
    have h1 : ∀ x, F x y = ∑ i, b.coord i ⟨F x, hF x⟩ * ((b i : V) : Y → ℂ) y := by
      intro x
      have h := congrArg (ev y) (b.sum_repr ⟨F x, hF x⟩)

      rw [map_sum] at h
      simp only [map_smul] at h
      exact h.symm
    simp only [h1, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_finsetSum _ (fun i _ => (hint (b.coord i)).mul_const _)]
    exact Finset.sum_congr rfl fun i _ => integral_mul_const _ _
  rw [key]
  exact V.sum_mem fun i _ => V.smul_mem _ (b i).2
end

section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem aeval_preserves_invariant_submodule {M : Type} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M)
    (N : Submodule ℂ M) (hN : ∀ x ∈ N, T x ∈ N) (p : Polynomial ℂ) :
    ∀ x ∈ N, Polynomial.aeval T p x ∈ N := by
  intro x hx
  have hpow : ∀ n : ℕ, ∀ y ∈ N, (T ^ n) y ∈ N := by
    intro n
    induction n with
    | zero =>
      intro y hy
      simpa using hy
    | succ n ih =>
      intro y hy
      rw [pow_succ', Module.End.mul_apply]
      exact hN _ (ih y hy)
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add (f := _), LinearMap.add_apply]
    exact N.add_mem hp hq
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact N.smul_mem a (hpow n x hx)

theorem UpperTheory.finiteDimensional_inf_ker_aeval_monic :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) (N : Submodule ℂ M), (∀ x ∈ N, T x ∈ N) → (∀ c : ℂ, FiniteDimensional ℂ ↥(N ⊓ T.eigenspace c)) → ∀ p : Polynomial ℂ, p.Monic → FiniteDimensional ℂ ↥(N ⊓ LinearMap.ker (Polynomial.aeval T p)) := by
  intro M _ _ T N hN hE p hp
  have key : ∀ s : Multiset ℂ, FiniteDimensional ℂ ↥(N ⊓ LinearMap.ker
      (Polynomial.aeval T (s.map (fun a => Polynomial.X - Polynomial.C a)).prod)) := by
    intro s
    induction s using Multiset.induction_on with
    | empty =>
      rw [Multiset.map_zero, Multiset.prod_zero, map_one]
      have h1 : LinearMap.ker (1 : Module.End ℂ M) = ⊥ := LinearMap.ker_id
      rw [h1, inf_bot_eq]
      infer_instance
    | cons a s ih =>
      set q := (s.map (fun a => Polynomial.X - Polynomial.C a)).prod with hq
      rw [Multiset.map_cons, Multiset.prod_cons]
      rw [← Submodule.fg_iff_finiteDimensional] at ih ⊢
      apply Submodule.fg_of_fg_map_of_fg_inf_ker (f := Polynomial.aeval T q)
      · have hle : (N ⊓ LinearMap.ker (Polynomial.aeval T ((Polynomial.X - Polynomial.C a) * q))).map
            (Polynomial.aeval T q) ≤ N ⊓ T.eigenspace a := by
          rintro _ ⟨x, ⟨hxN, hxk⟩, rfl⟩
          refine ⟨aeval_preserves_invariant_submodule T N hN q x hxN, ?_⟩
          show _ ∈ T.eigenspace a
          rw [Module.End.mem_eigenspace_iff]
          change x ∈ LinearMap.ker _ at hxk
          rw [LinearMap.mem_ker, map_mul, Module.End.mul_apply, map_sub, Polynomial.aeval_X,
            Polynomial.aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply, sub_eq_zero] at hxk
          exact hxk
        haveI := hE a
        rw [Submodule.fg_iff_finiteDimensional]
        exact Submodule.finiteDimensional_of_le hle
      · apply Submodule.FG.of_le ih
        rintro x ⟨⟨hxN, -⟩, hxq⟩
        exact ⟨hxN, hxq⟩
  have hsplit := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hp IsAlgClosed.card_roots_eq_natDegree
  rw [← hsplit]
  exact key p.roots
end

section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.finiteDimensional_map_of_separately_finite :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (X Y : Type) (S : Submodule ℂ M) (Φ : M →ₗ[ℂ] (X × Y → ℂ)) (V₁ : Submodule ℂ (X → ℂ)) (V₂ : Submodule ℂ (Y → ℂ)), FiniteDimensional ℂ V₁ → FiniteDimensional ℂ V₂ → (∀ m ∈ S, ∀ y, (fun x => Φ m (x, y)) ∈ V₁) → (∀ m ∈ S, ∀ x, (fun y => Φ m (x, y)) ∈ V₂) → FiniteDimensional ℂ (S.map Φ) := by
  intro M _ _ X Y S Φ V₁ V₂ h₁ h₂ hrow hcol
  obtain ⟨T, hT⟩ := exists_finset_eval_eq_zero V₁
  have mem : ∀ g ∈ S.map Φ, ∀ x, (fun y => g (x, y)) ∈ V₂ := by
    rintro g ⟨m, hm, rfl⟩ x
    exact hcol m hm x
  have memr : ∀ g ∈ S.map Φ, ∀ y, (fun x => g (x, y)) ∈ V₁ := by
    rintro g ⟨m, hm, rfl⟩ y
    exact hrow m hm y
  let F : S.map Φ →ₗ[ℂ] (T → V₂) :=
    LinearMap.pi fun t => LinearMap.codRestrict V₂
      ((LinearMap.funLeft ℂ ℂ (fun y : Y => ((t : X), y))).comp (S.map Φ).subtype)
      (fun g => mem g.1 g.2 t)
  have hF : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro g hg
    apply Subtype.ext
    funext p
    obtain ⟨x, y⟩ := p
    have h0 := hT (fun x => g.1 (x, y)) (memr g.1 g.2 y) (by
      intro t ht
      have := congrArg (fun v : T → V₂ => ((v ⟨t, ht⟩ : V₂) : Y → ℂ) y) hg
      simpa [F, LinearMap.funLeft] using this)
    simpa using congrFun h0 x
  exact Module.Finite.of_injective F hF
end
