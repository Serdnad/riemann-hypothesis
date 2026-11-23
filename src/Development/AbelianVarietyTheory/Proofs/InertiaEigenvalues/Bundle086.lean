module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SpanSingletonEqTopIffIsUnitOfIsBaseChange
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsMulRightInvariantOfCovolumeOne
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle036
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
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle001
public import Mathlib.MeasureTheory.Measure.Haar.Basic

@[expose] public section

section

open TensorProduct

namespace GlobalTheory.CocycleDescent

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {d : ℕ}

noncomputable def defect (ε : Matrix (Fin d) (Fin d) (B ⊗[A] B)) :
    (Fin d → B) →ₗ[A] (Fin d → B ⊗[A] B) :=
  (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).toLinearMap.compLeft (Fin d) -
    (ε.mulVecLin.restrictScalars A) ∘ₗ
      (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toLinearMap.compLeft (Fin d)

theorem defect_apply (ε : Matrix (Fin d) (Fin d) (B ⊗[A] B)) (z : Fin d → B) :
    defect ε z = (fun i => z i ⊗ₜ[A] (1 : B)) - ε.mulVec fun i => (1 : B) ⊗ₜ[A] z i := rfl

theorem lTensor_defect (ε : Matrix (Fin d) (Fin d) (B ⊗[A] B)) (x : B ⊗[A] (Fin d → B)) :
    piRight A A B (fun _ : Fin d => B ⊗[A] B) ((defect ε).lTensor B x) =
      (fun i => Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)
          (piRight A A B (fun _ : Fin d => B) x i)) -
      (ε.map (Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B))).mulVec
        (fun i => Algebra.TensorProduct.map (AlgHom.id A B)
          (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)
            (piRight A A B (fun _ : Fin d => B) x i)) := by
  induction x with
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]
    ext i
    simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Pi.sub_apply, map_add (f := _), mul_add,
      Finset.sum_add_distrib]
    abel
  | tmul b z =>
    ext i
    simp [defect_apply, Matrix.mulVec, dotProduct, tmul_sub, tmul_sum]

theorem isBaseChange [Module.Flat A B] (ε : Matrix (Fin d) (Fin d) (B ⊗[A] B)) (hε : IsUnit ε)
    (hc : ε.map (Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)) *
      ε.map (Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)) =
      ε.map (Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B))) :
    IsBaseChange B (LinearMap.ker (defect ε)).subtype := by
  set N := LinearMap.ker (defect ε) with hN
  set e := piRight A A B (fun _ : Fin d => B) with he
  have hεinj : Function.Injective ε.mulVec := Matrix.mulVec_injective_of_isUnit hε
  have key : ∀ x : B ⊗[A] N, (fun i => (N.subtype.liftBaseChange B x) i ⊗ₜ[A] (1 : B)) =
      ε.mulVec (e (N.subtype.lTensor B x)) := by
    intro x
    induction x with
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), map_add (f := _), Matrix.mulVec_add, ← hx, ← hy]
      ext i
      simp [add_tmul]
    | tmul b n =>
      have hn : defect ε n.1 = 0 := n.2
      rw [defect_apply, sub_eq_zero] at hn
      have h1 : e (N.subtype.lTensor B (b ⊗ₜ n)) =
          (b ⊗ₜ[A] (1 : B)) • fun i => (1 : B) ⊗ₜ[A] n.1 i := by
        ext i
        simp [he]
      rw [h1, Matrix.mulVec_smul, ← hn]
      ext i
      simp
  have hleft : ∀ z w : Fin d → B,
      (fun i => z i ⊗ₜ[A] (1 : B)) = (fun i => w i ⊗ₜ[A] (1 : B)) → z = w := by
    intro z w h
    ext i
    simpa using congrArg (Algebra.TensorProduct.lmul' A (S := B)) (congrFun h i)
  change Function.Bijective (N.subtype.liftBaseChange B)
  constructor
  · intro x y hxy
    have h := key x
    rw [hxy, key y] at h
    exact (Module.Flat.lTensor_preserves_injective_linearMap N.subtype N.injective_subtype
      (e.injective (hεinj h))).symm
  · intro z
    obtain ⟨y, hy⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hε (fun i => z i ⊗ₜ[A] (1 : B))
    have hex := Module.Flat.lTensor_exact B (LinearMap.exact_subtype_ker_map (defect ε))
    have h0 : (defect ε).lTensor B (e.symm y) = 0 := by
      apply (piRight A A B (fun _ : Fin d => B ⊗[A] B)).injective
      rw [lTensor_defect, map_zero, sub_eq_zero, ← he, e.apply_symm_apply]
      set i₁₂ := Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) with h12
      set i₁₃ := Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) with h13
      have hu : IsUnit (ε.map i₁₂) := hε.map (i₁₂.toRingHom.mapMatrix)
      apply Matrix.mulVec_injective_of_isUnit hu
      rw [Matrix.mulVec_mulVec, hc]
      ext i
      have a := RingHom.map_mulVec i₁₂.toRingHom ε y i
      have b := RingHom.map_mulVec i₁₃.toRingHom ε y i
      refine a.symm.trans (Eq.trans ?_ b)
      rw [hy]
      simp [h12, h13, ← Algebra.TensorProduct.one_def]
    obtain ⟨x, hx⟩ := (hex _).mp h0
    refine ⟨x, hleft _ _ ?_⟩
    rw [key, ← hy]
    congr 1
    rw [← e.apply_symm_apply y, ← hx]

theorem descent (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    (d : ℕ) (ε : Matrix (Fin d) (Fin d) (B ⊗[A] B)) (hε : IsUnit ε)
    (hc : ε.map (Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)) *
      ε.map (Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)) =
      ε.map (Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)))
    (N : Submodule A (Fin d → B))
    (hN : ∀ z, z ∈ N ↔ (fun i => z i ⊗ₜ[A] (1 : B)) = ε.mulVec fun i => (1 : B) ⊗ₜ[A] z i) :
    Module.Finite A ↥N ∧ Module.Projective A ↥N ∧ IsBaseChange B N.subtype := by
  have hk : N = LinearMap.ker (defect ε) := by
    ext z
    rw [hN, LinearMap.mem_ker, defect_apply, sub_eq_zero]
  have hb : IsBaseChange B N.subtype := hk ▸ isBaseChange ε hε hc
  have : Module.Finite B (B ⊗[A] N) := Module.Finite.equiv hb.equiv.symm
  have : Module.Projective B (B ⊗[A] N) := Module.Projective.of_equiv hb.equiv.symm
  exact ⟨GlobalTheory.Descent.finite B, GlobalTheory.Descent.projective B, hb⟩

end GlobalTheory.CocycleDescent
end

section

open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial

namespace GlobalTheory.StableGraph

variable {O : Type} [CommRing O] {A₁ A₂ : Type} [CommRing A₁] [CommRing A₂] [Algebra O A₁]
  [Algebra O A₂] {M₁ : Submodule O A₁} {M₂ : Submodule O A₂}

theorem mem_of_inl {M : Submodule O (A₁ × A₂)} (h : M.comap (LinearMap.inl O A₁ A₂) = M₁)
    {a : A₁} (ha : (a, (0 : A₂)) ∈ M) : a ∈ M₁ := by
  rw [← h]; exact ha

theorem mem_of_snd {M : Submodule O (A₁ × A₂)} (h : M.map (LinearMap.snd O A₁ A₂) = M₂)
    {a : A₁} {x : A₂} (hx : (a, x) ∈ M) : x ∈ M₂ := by
  rw [← h]; exact Submodule.mem_map_of_mem (f := LinearMap.snd O A₁ A₂) hx

theorem exists_of_map {M : Submodule O (A₁ × A₂)} (h : M.map (LinearMap.snd O A₁ A₂) = M₂)
    (x : M₂) : ∃ a : A₁, (a, (x : A₂)) ∈ M := by
  have hx : (x : A₂) ∈ M.map (LinearMap.snd O A₁ A₂) := h ▸ x.2
  obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.1 hx
  have hp' : p = (p.1, (x : A₂)) := Prod.ext rfl hpx
  exact ⟨p.1, hp' ▸ hp⟩

noncomputable def classOf {M : Submodule O (A₁ × A₂)} (h₂ : M.map (LinearMap.snd O A₁ A₂) = M₂)
    (x : M₂) : A₁ ⧸ M₁ :=
  Submodule.Quotient.mk (exists_of_map h₂ x).choose

theorem classOf_eq {M : Submodule O (A₁ × A₂)} (h₁ : M.comap (LinearMap.inl O A₁ A₂) = M₁)
    (h₂ : M.map (LinearMap.snd O A₁ A₂) = M₂) {x : M₂} {a : A₁} (hp : (a, (x : A₂)) ∈ M) :
    classOf (M₁ := M₁) h₂ x = Submodule.Quotient.mk a := by
  unfold classOf
  rw [Submodule.Quotient.eq]
  apply mem_of_inl h₁
  have := M.sub_mem (exists_of_map h₂ x).choose_spec hp
  simpa using this

noncomputable def toHom (M : Submodule O (A₁ × A₂)) (h₁ : M.comap (LinearMap.inl O A₁ A₂) = M₁)
    (h₂ : M.map (LinearMap.snd O A₁ A₂) = M₂) : M₂ →ₗ[O] A₁ ⧸ M₁ where
  toFun := classOf h₂
  map_add' x y := by
    obtain ⟨a, ha⟩ := exists_of_map h₂ x
    obtain ⟨b, hb⟩ := exists_of_map h₂ y
    rw [classOf_eq h₁ h₂ ha, classOf_eq h₁ h₂ hb, ← Submodule.Quotient.mk_add]
    exact classOf_eq h₁ h₂ (by simpa using M.add_mem ha hb)
  map_smul' c x := by
    obtain ⟨a, ha⟩ := exists_of_map h₂ x
    rw [classOf_eq h₁ h₂ ha, RingHom.id_apply, ← Submodule.Quotient.mk_smul]
    exact classOf_eq h₁ h₂ (by simpa using M.smul_mem c ha)

def graph (φ : M₂ →ₗ[O] A₁ ⧸ M₁) : Submodule O (A₁ × A₂) where
  carrier := {p | ∃ h : p.2 ∈ M₂, Submodule.Quotient.mk p.1 = φ ⟨p.2, h⟩}
  add_mem' := by
    rintro ⟨a, x⟩ ⟨b, y⟩ ⟨hx, ha⟩ ⟨hy, hb⟩
    refine ⟨M₂.add_mem hx hy, ?_⟩
    have e : (⟨x + y, M₂.add_mem hx hy⟩ : M₂) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    simp only [Prod.fst_add, Prod.snd_add] at *
    rw [e, map_add (f := _), Submodule.Quotient.mk_add, ha, hb]
  zero_mem' := ⟨M₂.zero_mem, by
    have e : (⟨0, M₂.zero_mem⟩ : M₂) = 0 := rfl
    simp only [Prod.fst_zero, Prod.snd_zero]
    rw [e, map_zero, Submodule.Quotient.mk_zero]⟩
  smul_mem' := by
    rintro c ⟨a, x⟩ ⟨hx, ha⟩
    refine ⟨M₂.smul_mem c hx, ?_⟩
    have e : (⟨c • x, M₂.smul_mem c hx⟩ : M₂) = c • ⟨x, hx⟩ := rfl
    simp only [Prod.smul_fst, Prod.smul_snd] at *
    rw [e, map_smul, Submodule.Quotient.mk_smul, ha]

theorem mem_graph {φ : M₂ →ₗ[O] A₁ ⧸ M₁} {a : A₁} {x : A₂} :
    (a, x) ∈ graph φ ↔ ∃ h : x ∈ M₂, Submodule.Quotient.mk a = φ ⟨x, h⟩ := Iff.rfl

theorem graph_comap (φ : M₂ →ₗ[O] A₁ ⧸ M₁) : (graph φ).comap (LinearMap.inl O A₁ A₂) = M₁ := by
    ext a
    simp only [Submodule.mem_comap, LinearMap.inl_apply]
    rw [mem_graph]
    constructor
    · rintro ⟨h, e⟩
      have e0 : (⟨0, h⟩ : M₂) = 0 := rfl
      rw [e0, map_zero, Submodule.Quotient.mk_eq_zero] at e
      exact e
    · intro ha
      refine ⟨M₂.zero_mem, ?_⟩
      have e0 : (⟨0, M₂.zero_mem⟩ : M₂) = 0 := rfl
      rw [e0, map_zero, Submodule.Quotient.mk_eq_zero]
      exact ha

theorem graph_map (φ : M₂ →ₗ[O] A₁ ⧸ M₁) : (graph φ).map (LinearMap.snd O A₁ A₂) = M₂ := by
    ext x
    constructor
    · rintro ⟨p, ⟨h, _⟩, rfl⟩
      exact h
    · intro hx
      obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective M₁ (φ ⟨x, hx⟩)
      exact ⟨(a, x), ⟨hx, ha⟩, rfl⟩

noncomputable def stableEquiv (g₁ : A₁) (g₂ : A₂) (hM₂ : ∀ y ∈ M₂, g₂ * y ∈ M₂) :
    {M : Submodule O (A₁ × A₂) // (∀ y ∈ M, (g₁, g₂) * y ∈ M) ∧
        M.comap (LinearMap.inl O A₁ A₂) = M₁ ∧ M.map (LinearMap.snd O A₁ A₂) = M₂} ≃
      {φ : M₂ →ₗ[O] A₁ ⧸ M₁ // ∀ x y : M₂, (y : A₂) = g₂ * x → ∀ a : A₁,
        φ x = Submodule.Quotient.mk a → φ y = Submodule.Quotient.mk (g₁ * a)} where
  toFun M := ⟨toHom M.1 M.2.2.1 M.2.2.2, by
    obtain ⟨M, hst, h₁, h₂⟩ := M
    intro x y hy a ha
    obtain ⟨c, hc⟩ := exists_of_map h₂ x
    have hφx : toHom M h₁ h₂ x = Submodule.Quotient.mk c := classOf_eq h₁ h₂ hc
    rw [hφx, Submodule.Quotient.eq] at ha
    have h1 : (c - a, (0 : A₂)) ∈ M := by rw [← h₁] at ha; exact ha
    have h2 := hst _ hc
    have h3 := hst _ h1
    have h4 : (g₁ * a, (y : A₂)) ∈ M := by
      have := M.sub_mem h2 h3
      rw [hy]
      convert this using 1
      ext
      · simp only [Prod.fst_sub, Prod.fst_mul]; ring
      · simp
    exact classOf_eq h₁ h₂ h4⟩
  invFun φ := ⟨graph φ.1, by
    rintro ⟨a, x⟩ ⟨hx, ha⟩
    exact ⟨hM₂ x hx, (φ.2 ⟨x, hx⟩ ⟨g₂ * x, hM₂ x hx⟩ rfl a ha.symm).symm⟩,
    graph_comap φ.1, graph_map φ.1⟩
  left_inv M := by
    obtain ⟨M, hst, h₁, h₂⟩ := M
    apply Subtype.ext
    ext ⟨a, x⟩
    show (a, x) ∈ graph (toHom M h₁ h₂) ↔ (a, x) ∈ M
    rw [mem_graph]
    constructor
    · rintro ⟨hx, e⟩
      obtain ⟨c, hc⟩ := exists_of_map h₂ ⟨x, hx⟩
      have hφx : toHom M h₁ h₂ ⟨x, hx⟩ = Submodule.Quotient.mk c := classOf_eq h₁ h₂ hc
      rw [hφx, Submodule.Quotient.eq] at e
      have h1 : (a - c, (0 : A₂)) ∈ M := by rw [← h₁] at e; exact e
      have := M.add_mem h1 hc
      simpa using this
    · intro hm
      exact ⟨mem_of_snd h₂ hm, (classOf_eq h₁ h₂ hm).symm⟩
  right_inv φ := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective M₁ (φ.1 x)
    have hm : (a, (x : A₂)) ∈ graph φ.1 := ⟨x.2, ha⟩
    exact (classOf_eq (graph_comap φ.1) (graph_map φ.1) hm).trans ha

end GlobalTheory.StableGraph


open GlobalTheory.StableGraph in
theorem GlobalTheory.StableGraph.card_stable_eq_card_hom : ∀ (O : Type) [CommRing O] (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] (g₁ : A₁) (g₂ : A₂) (M₁ : Submodule O A₁) (M₂ : Submodule O A₂), (∀ y ∈ M₂, g₂ * y ∈ M₂) → Nat.card {M : Submodule O (A₁ × A₂) // (∀ y ∈ M, (g₁, g₂) * y ∈ M) ∧ M.comap (LinearMap.inl O A₁ A₂) = M₁ ∧ M.map (LinearMap.snd O A₁ A₂) = M₂} = Nat.card {φ : M₂ →ₗ[O] A₁ ⧸ M₁ // ∀ x y : M₂, (y : A₂) = g₂ * x → ∀ a : A₁, φ x = Submodule.Quotient.mk a → φ y = Submodule.Quotient.mk (g₁ * a)} := by
  intro O _ A₁ A₂ _ _ _ _ g₁ g₂ M₁ M₂ hM₂
  exact Nat.card_congr (stableEquiv g₁ g₂ hM₂)
end

section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Pointwise

namespace GlobalTheory.UnipAvg

section Covolume

variable {U : Type*} [Group U] [MeasurableSpace U] [MeasurableMul₂ U] [MeasurableInv U]

theorem measurePreserving_mulEquiv_of_covolume_one (ν : Measure U) [SigmaFinite ν] [ν.IsMulLeftInvariant]
    (U₀ : Subgroup U) [Countable U₀] {D : Set U} (hD : IsFundamentalDomain U₀ D ν) (hνD : ν D = 1)
    (c : U ≃* U) (hc : Measurable c) (hc' : Measurable c.symm)
    (h₁ : ∀ b ∈ U₀, c b ∈ U₀) (h₂ : ∀ b ∈ U₀, c.symm b ∈ U₀) : MeasurePreserving c ν ν := by
  haveI : SMulInvariantMeasure U₀ U ν := ⟨fun γ s _ => measure_preimage_mul ν (γ : U) s⟩
  let e : U ≃ᵐ U := ⟨c.toEquiv, hc, hc'⟩
  haveI : SigmaFinite (ν.map c) := e.sigmaFinite_map
  haveI : (ν.map c).IsMulLeftInvariant := ⟨fun g => by
    rw [map_map (measurable_const_mul g) hc]
    conv_rhs => rw [← map_mul_left_eq_self ν (c.symm g), map_map hc (measurable_const_mul _)]
    congr 1
    ext x
    simp⟩
  have h := measure_eq_div_smul (ν.map c) ν (s := D) (by rw [hνD]; exact one_ne_zero)
    (by rw [hνD]; exact ENNReal.one_ne_top)
  have hq : QuasiMeasurePreserving c ν ν := ⟨hc.aemeasurable, by rw [h]; exact smul_absolutelyContinuous⟩
  have hD' : IsFundamentalDomain U₀ (c ⁻¹' D) ν :=
    hD.preimage_of_equiv hq (e := fun b : U₀ => (⟨c.symm b, h₂ b b.2⟩ : U₀))
      ⟨fun b b' hb => Subtype.ext (c.symm.injective (congrArg Subtype.val hb)),
        fun b => ⟨⟨c b, h₁ b b.2⟩, Subtype.ext (c.symm_apply_apply b)⟩⟩
      (fun b x => by
        change c (c.symm b * x) = b * c x
        simp)
  have h1 : (ν.map c) D = 1 := by
    have : (ν.map c) D = ν (c ⁻¹' D) := e.map_apply (μ := ν) D
    rw [this, hD'.measure_eq hD, hνD]
  refine ⟨hc, ?_⟩
  rw [h, h1, hνD]; simp

theorem setLIntegral_mul_right_of_covolume_one (ν : Measure U) [SigmaFinite ν] [ν.IsMulLeftInvariant]
    (U₀ : Subgroup U) [Countable U₀] {D : Set U} (hD : IsFundamentalDomain U₀ D ν) (hνD : ν D = 1)
    (f : U → ℝ≥0∞) (hf : ∀ b ∈ U₀, ∀ u, f (b * u) = f u) (v : U) :
    ∫⁻ u in D, f (u * v) ∂ν = ∫⁻ u in D, f u ∂ν := by
  haveI : SMulInvariantMeasure U₀ U ν := ⟨fun γ s _ => measure_preimage_mul ν (γ : U) s⟩
  haveI := isMulRightInvariant_of_covolume_one ν U₀ hD hνD
  have hD' : IsFundamentalDomain U₀ ((· * v) ⁻¹' D) ν :=
    hD.preimage_of_equiv (quasiMeasurePreserving_mul_right ν v) (e := id) Function.bijective_id
      (fun g x => mul_assoc (g : U) x v)
  rw [hD.setLIntegral_eq hD' (fun u => f (u * v)) (fun b x => by
    change f ((b : U) * x * v) = _
    rw [mul_assoc, hf _ b.2])]
  exact (measurePreserving_mul_right ν v).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.mulRight v).measurableEmbedding f D

end Covolume

theorem setLIntegral_add_left_of_periodic {A : Type*} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd₂ A]
    (ν : Measure A) [ν.IsAddLeftInvariant] (A₀ : AddSubgroup A) [Countable A₀] {D : Set A}
    (hD : IsAddFundamentalDomain A₀ D ν) (f : A → ℝ≥0∞) (hf : ∀ b ∈ A₀, ∀ y, f (b + y) = f y) (t : A) :
    ∫⁻ y in D, f (t + y) ∂ν = ∫⁻ y in D, f y ∂ν := by
  haveI : VAddInvariantMeasure A₀ A ν := ⟨fun γ s _ => measure_preimage_add ν (γ : A) s⟩
  have hD' : IsAddFundamentalDomain A₀ ((t + ·) ⁻¹' D) ν :=
    hD.preimage_of_equiv (measurePreserving_add_left ν t).quasiMeasurePreserving (e := id) Function.bijective_id
      (fun g x => add_left_comm t (g : A) x)
  rw [hD.setLIntegral_eq hD' (fun u => f (t + u)) (fun b x => by
    change f (t + ((b : A) + x)) = _
    rw [add_left_comm, hf _ b.2])]
  exact (measurePreserving_add_left ν t).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.addLeft t).measurableEmbedding f D

theorem exists_covolume_one_of_cocompact {U : Type*} [Group U] [TopologicalSpace U] [IsTopologicalGroup U]
    [LocallyCompactSpace U] [SecondCountableTopology U] [MeasurableSpace U] [BorelSpace U]
    (U₀ : Subgroup U) [DiscreteTopology U₀] {K : Set U} (hK : IsCompact K) (hcov : ∀ u, ∃ b ∈ U₀, b * u ∈ K) :
    ∃ (ν : Measure U) (D : Set U), SigmaFinite ν ∧ ν.IsMulLeftInvariant ∧ IsFundamentalDomain U₀ D ν ∧ ν D = 1 := by
  haveI := countable_of_discrete_subgroup U₀
  obtain ⟨D, -, -, hD⟩ := exists_isFundamentalDomain_subgroup U₀
  let m : Measure U := haar
  haveI : SMulInvariantMeasure U₀ U m := ⟨fun γ s _ => measure_preimage_mul m (γ : U) s⟩
  have h0 : m D ≠ 0 := (hD m).measure_ne_zero (NeZero.ne m)
  have h1 : m D ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt ?_ (hK.measure_lt_top (μ := m)))
    rw [(hD m).measure_eq_tsum K]
    refine le_trans (measure_mono fun u hu => ?_) (measure_iUnion_le _)
    obtain ⟨b, hb, hbu⟩ := hcov u
    exact mem_iUnion.2 ⟨(⟨b, hb⟩ : U₀)⁻¹, mem_inv_smul_set_iff.2 hbu, hu⟩
  haveI : ((m D)⁻¹ • m).IsHaarMeasure := IsHaarMeasure.smul m (ENNReal.inv_ne_zero.2 h1) (ENNReal.inv_ne_top.2 h0)
  exact ⟨(m D)⁻¹ • m, D, inferInstance, inferInstance, hD _, by
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 h1]⟩

theorem setLIntegral_average_abelian_quotient : ∀ (G A : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd₂ A] [MeasurableNeg A] (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] (Γ U : Subgroup G) [DiscreteTopology Γ], IsClosed (U : Set G) → (∀ γ ∈ Γ, ∀ u ∈ U, γ⁻¹ * u * γ ∈ U) → (∃ K : Set G, IsCompact K ∧ ∀ u ∈ U, ∃ γ ∈ Γ, γ ∈ U ∧ γ * u ∈ K) → ∀ (ι : A → G), (∀ x y, ι (x + y) = ι x * ι y) → Measurable ι → (∀ x, ι x ∈ U) → ∀ (ν : Measure A) [SigmaFinite ν] [ν.IsAddLeftInvariant] (A₀ : AddSubgroup A) [Countable A₀], (∀ b ∈ A₀, ι b ∈ Γ) → ∀ (D : Set A), IsAddFundamentalDomain A₀ D ν → ν D = 1 → ∀ (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ (Φ : G → ENNReal), Measurable Φ → (∀ γ ∈ Γ, ∀ g, Φ (γ * g) = Φ g) → (∀ u ∈ U, ∃ y : A, ∀ g, Φ (u * g) = Φ (ι y * g)) → ∫⁻ g in 𝓕, Φ g ∂μ = ∫⁻ g in 𝓕, ∫⁻ y in D, Φ (ι y * g) ∂ν ∂μ := by
  intro G A _ _ _ _ _ _ _ _ _ _ _ _ μ _ _ Γ U _ hU hnorm ⟨K, hK, hcov⟩ ι hadd hιm hιU ν _ _ A₀ _ hA₀ D hD hνD 𝓕 h𝓕
    Φ hΦ hinv hact
  haveI := countable_of_discrete_subgroup Γ
  haveI : LocallyCompactSpace U := hU.locallyCompactSpace
  haveI : SecondCountableTopology U := TopologicalSpace.Subtype.secondCountableTopology (U : Set G)
  haveI : DiscreteTopology (Γ.subgroupOf U) :=
    DiscreteTopology.of_continuous_injective (f := fun b : Γ.subgroupOf U => (⟨(b : U), b.2⟩ : Γ))
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
      (fun b b' h => Subtype.ext (Subtype.ext (congrArg (fun z : Γ => (z : G)) h)))
  haveI := countable_of_discrete_subgroup (Γ.subgroupOf U)
  obtain ⟨m, E, _, _, hE, hmE⟩ := exists_covolume_one_of_cocompact (Γ.subgroupOf U)
    (hU.isClosedEmbedding_subtypeVal.isCompact_preimage hK) (fun u => by
      obtain ⟨γ, h1, h2, h3⟩ := hcov u u.2
      exact ⟨⟨γ, h2⟩, h1, h3⟩)
  have hconj : ∀ a ∈ (Γ : Set G), ∃ c : U → U, MeasurePreserving c m m ∧
      ∀ u, U.subtype (c u) = a⁻¹ * U.subtype u * a := by
    intro a ha
    have ha' : ∀ u ∈ U, a * u * a⁻¹ ∈ U := fun u hu => by simpa using hnorm a⁻¹ (Γ.inv_mem ha) u hu
    let c : U ≃* U :=
      { toFun := fun u => ⟨a⁻¹ * u * a, hnorm a ha u u.2⟩
        invFun := fun u => ⟨a * u * a⁻¹, ha' u u.2⟩
        left_inv := fun u => Subtype.ext (by simp only; group)
        right_inv := fun u => Subtype.ext (by simp only; group)
        map_mul' := fun u v => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
    exact ⟨c, measurePreserving_mulEquiv_of_covolume_one m _ hE hmE c
      (((measurable_subtype_coe.const_mul _).mul_const _).subtype_mk)
      (((measurable_subtype_coe.const_mul _).mul_const _).subtype_mk)
      (fun b hb => Γ.mul_mem (Γ.mul_mem (Γ.inv_mem ha) hb) ha)
      (fun b hb => Γ.mul_mem (Γ.mul_mem ha hb) (Γ.inv_mem ha)), fun _ => rfl⟩
  rw [setLIntegral_average U.subtype Subtype.val_injective measurable_subtype_coe μ m Γ (Γ.subgroupOf U)
    (fun b hb => hb) Γ (fun γ hγ => ⟨γ, hγ, 1, one_mem _, by simp⟩) hconj hE hmE h𝓕 Φ hΦ hinv]
  refine lintegral_congr fun g => ?_
  calc ∫⁻ u in E, Φ (U.subtype u * g) ∂m = ∫⁻ _y in D, ∫⁻ u in E, Φ ((u : G) * g) ∂m ∂ν := by simp [hνD]
    _ = ∫⁻ y in D, ∫⁻ u in E, Φ ((u : G) * (ι y * g)) ∂m ∂ν := by
        refine lintegral_congr fun y => ?_
        rw [← setLIntegral_mul_right_of_covolume_one m _ hE hmE (fun u => Φ ((u : G) * g))
          (fun b hb u => by rw [Subgroup.coe_mul, mul_assoc, hinv (b : G) hb]) ⟨ι y, hιU y⟩]
        simp only [Subgroup.coe_mul, mul_assoc]
    _ = ∫⁻ u in E, ∫⁻ y in D, Φ ((u : G) * (ι y * g)) ∂ν ∂m :=
        lintegral_lintegral_swap (hΦ.comp ((measurable_subtype_coe.comp measurable_snd).mul
          ((hιm.comp measurable_fst).mul_const g))).aemeasurable
    _ = ∫⁻ _u in E, ∫⁻ y in D, Φ (ι y * g) ∂ν ∂m := by
        refine lintegral_congr fun u => ?_
        obtain ⟨t, ht⟩ := hact u u.2
        rw [← setLIntegral_add_left_of_periodic ν A₀ hD (fun y => Φ (ι y * g))
          (fun b hb y => by rw [hadd, mul_assoc, hinv _ (hA₀ b hb)]) t]
        simp only [ht, hadd, mul_assoc]
    _ = ∫⁻ y in D, Φ (ι y * g) ∂ν := by simp [hmE]

end GlobalTheory.UnipAvg
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_span_prime_eq_pow_mul_coprime : ∀ (L : Type) [Field L] [NumberField L] (l e : ℕ), l.Prime → ∀ (la : Ideal (𝓞 L)) [la.IsMaximal], ((l : ℕ) : 𝓞 L) ∈ la → ((l : ℕ) : 𝓞 L) ∉ la ^ (e + 1) → ∃ (e' : ℕ) (J : Ideal (𝓞 L)), 0 < e' ∧ e' ≤ e ∧ la ⊔ J = ⊤ ∧ Ideal.span {((l : ℕ) : 𝓞 L)} = la ^ e' * J := by
  first | exact @GlobalTheory.maxIdeal_exact_pow_dvd_span_prime | exact GlobalTheory.maxIdeal_exact_pow_dvd_span_prime | (intros; apply GlobalTheory.maxIdeal_exact_pow_dvd_span_prime <;> assumption)
end
