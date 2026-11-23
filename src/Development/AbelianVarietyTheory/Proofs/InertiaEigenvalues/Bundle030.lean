module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs

@[expose] public section

section

open Polynomial

namespace GlobalTheory.SepGeneric

theorem separable_iff_resultant {K : Type} [Field K] {f : K[X]} (hf : f.Monic) {t : ℕ}
    (ht : f.natDegree = t) : f.Separable ↔ resultant f (derivative f) t t ≠ 0 := by
  have hle : (derivative f).natDegree ≤ t :=
    (natDegree_derivative_le f).trans (by omega)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  have h1 : resultant f (derivative f) t t
      = resultant f (derivative f) f.natDegree (derivative f).natDegree := by
    have := resultant_add_right_deg f (derivative f) t (derivative f).natDegree k le_rfl
    rw [← hk] at this
    rw [this, ← ht, hf.coeff_natDegree]
    simp
  rw [h1, ← isUnit_iff_ne_zero, isUnit_resultant_iff_isCoprime hf]
  rfl

theorem finite_bad_base {K : Type} [Field K] {t : ℕ} (B A : Matrix (Fin t) (Fin t) K)
    (hB : B.charpoly.Separable) : {l : K | ¬ (B + l • A).charpoly.Separable}.Finite := by
  classical
  let N : Matrix (Fin t) (Fin t) K[X] := B.map C + (X : K[X]) • A.map C
  let D : K[X] := resultant N.charpoly (derivative N.charpoly) t t
  have hN : ∀ l : K, N.map (evalRingHom l) = B + l • A := by
    intro l
    ext i j
    simp [N]
    ring
  have hD : ∀ l : K, (B + l • A).charpoly.Separable ↔ D.eval l ≠ 0 := by
    intro l
    rw [separable_iff_resultant (Matrix.charpoly_monic _)
      (t := t) (by simp), ← hN, Matrix.charpoly_map, derivative_map, resultant_map_map]
    rfl
  have hD0 : D ≠ 0 := by
    intro h
    have := (hD 0).1 (by simpa using hB)
    simp [h] at this
  refine (D.roots.toFinset.finite_toSet).subset ?_
  intro l hl
  simp only [Set.mem_setOf_eq, hD, not_not] at hl
  simp [hD0, hl]

theorem separable_smul {K : Type} [Field K] {t : ℕ} (A : Matrix (Fin t) (Fin t) K) {c : K}
    (hc : c ≠ 0) (hA : A.charpoly.Separable) : (c • A).charpoly.Separable := by
  classical
  have h1 : (c • A).charpoly = C c ^ t * A.charpoly.comp (C c⁻¹ * X) := by
    have : (c • A).charmatrix = (C c : K[X]) • (A.charmatrix.map (compRingHom (C c⁻¹ * X))) := by
      ext1 i j
      by_cases h : i = j
      · subst h
        have h3 : (C c : K[X]) * (C c⁻¹ * X) = X := by
          rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hc, C_1, one_mul]
        simp [mul_sub, h3]
      · simp [Matrix.charmatrix_apply_ne _ _ _ h]
    rw [Matrix.charpoly, this, Matrix.det_smul, Matrix.charpoly, Fintype.card_fin]
    congr 1
    exact ((compRingHom (C c⁻¹ * X)).map_det A.charmatrix).symm
  have h2 : (A.charpoly.comp (C c⁻¹ * X)).Separable := by
    rw [separable_def, derivative_comp]
    have hu : IsUnit (derivative (C c⁻¹ * X : K[X])) := by
      simpa using isUnit_C.2 (IsUnit.mk0 _ (inv_ne_zero hc))
    rw [isCoprime_mul_unit_left_right hu]
    exact ((separable_def _).1 hA).map (compRingHom (C c⁻¹ * X))
  rw [h1, mul_comm]
  exact h2.mul_unit ((isUnit_C.2 (IsUnit.mk0 _ hc)).pow t)

theorem finite_bad_dir {K : Type} [Field K] {t : ℕ} (B A : Matrix (Fin t) (Fin t) K) {c : K}
    (hc : c ≠ 0) (hA : (c • A).charpoly.Separable) :
    {l : K | ¬ (B + l • A).charpoly.Separable}.Finite := by
  have hA' : A.charpoly.Separable := by
    have := separable_smul _ (inv_ne_zero hc) hA
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  have hf := (finite_bad_base A B hA').preimage (f := fun l : K => l⁻¹) inv_injective.injOn
  refine (hf.insert 0).subset ?_
  intro l hl
  by_cases h0 : l = 0
  · exact Or.inl h0
  · refine Or.inr ?_
    intro h
    apply hl
    have := separable_smul _ h0 h
    rwa [smul_add, smul_smul, mul_inv_cancel₀ h0, one_smul, add_comm] at this

theorem exists_separable {O K X : Type} [CommRing O] [IsDomain O] [Infinite O] [Field K]
    [Algebra O K] [IsFractionRing O K] [Finite X] (t : ℕ)
    (M : Submodule O (X → Matrix (Fin t) (Fin t) K)) (a : X → Matrix (Fin t) (Fin t) K)
    (h : ∀ x, (a x).charpoly.Separable ∨
      ∃ s ∈ M, ∃ c : K, c ≠ 0 ∧ (c • s x).charpoly.Separable) :
    ∃ s ∈ M, ∀ x, (a x + s x).charpoly.Separable := by
  classical
  have key : ∀ Y : Finset X, ∃ s ∈ M, ∀ x ∈ Y, (a x + s x).charpoly.Separable := by
    intro Y
    induction Y using Finset.induction_on with
    | empty => exact ⟨0, M.zero_mem, by simp⟩
    | insert x Y hx ih =>
      obtain ⟨s, hs, hY⟩ := ih
      have h1 : ∃ s' ∈ M, {l : K | ¬ (a x + s x + l • s' x).charpoly.Separable}.Finite := by
        rcases h x with h | ⟨s', hs', c, hc, h⟩
        · refine ⟨s, hs, ?_⟩
          have hf := (finite_bad_base (a x) (s x) h).preimage (f := fun l : K => 1 + l)
            (add_right_injective 1).injOn
          refine hf.subset ?_
          intro l hl
          simpa [add_smul, add_assoc] using hl
        · exact ⟨s', hs', finite_bad_dir _ _ hc h⟩
      obtain ⟨s', hs', h1⟩ := h1
      have h2 : (⋃ y ∈ insert x Y,
          {l : K | ¬ (a y + s y + l • s' y).charpoly.Separable}).Finite := by
        refine (insert x Y).finite_toSet.biUnion ?_
        intro y hy
        rcases Finset.mem_insert.1 hy with rfl | hy
        · exact h1
        · exact finite_bad_base _ _ (hY y hy)
      have h3 := h2.preimage (f := algebraMap O K) (IsFractionRing.injective O K).injOn
      obtain ⟨l, hl⟩ := h3.exists_notMem
      refine ⟨s + l • s', M.add_mem hs (M.smul_mem l hs'), ?_⟩
      intro y hy
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_not] at hl
      have := hl y hy
      rwa [algebraMap_smul, add_assoc] at this
  have := Fintype.ofFinite X
  obtain ⟨s, hs, h⟩ := key Finset.univ
  exact ⟨s, hs, fun x => h x (Finset.mem_univ x)⟩

end GlobalTheory.SepGeneric
end

section

namespace GlobalTheory.AltCorank

open Module

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

def Good (S₁ S₂ : Submodule K V) : Prop :=
  ∃ ω : V →ₗ[K] V →ₗ[K] K, (∀ v, ω v v = 0) ∧ ∀ x : Fin 2 → V, (∀ a, x a ∈ S₁) →
    (∀ a, ∀ y ∈ S₂, ω (x a) y = 0) → ¬ LinearIndependent K x

theorem good_step (S₁ S₂ T₁ T₂ : Submodule K V) (u v : V) (φ ψ : V →ₗ[K] K)
    (hφu : φ u = 1) (hφv : φ v = 0) (hψu : ψ u = 0) (hψv : ψ v = 1) (hv : v ∈ S₂)
    (hu : u ∈ S₂ ∨ ∀ x ∈ S₁, ψ x = 0)
    (h₁ : ∀ x ∈ S₁, φ x = 0 → ψ x = 0 → x ∈ T₁)
    (h₂ : ∀ y ∈ T₂, y ∈ S₂ ∧ φ y = 0 ∧ ψ y = 0) (h : Good T₁ T₂) : Good S₁ S₂ := by
  obtain ⟨ω, hω, hk⟩ := h
  let π : V →ₗ[K] V := LinearMap.id - φ.smulRight u - ψ.smulRight v
  have hπ : ∀ x, π x = x - φ x • u - ψ x • v := fun x => rfl
  let Ω : V →ₗ[K] V →ₗ[K] K :=
    ω.compl₁₂ π π + (LinearMap.mul K K).compl₁₂ φ ψ - (LinearMap.mul K K).compl₁₂ ψ φ
  have hΩ : ∀ x y, Ω x y = ω (π x) (π y) + φ x * ψ y - ψ x * φ y := fun x y => rfl
  have hπu : π u = 0 := by simp [hπ, hφu, hψu]
  have hπv : π v = 0 := by simp [hπ, hφv, hψv]
  refine ⟨Ω, fun x => by rw [hΩ, hω]; ring, fun x hx hz => ?_⟩
  have e1 : ∀ a, φ (x a) = 0 := fun a => by
    have := hz a v hv
    rw [hΩ, hπv, hφv, hψv] at this
    simpa using this
  have e2 : ∀ a, ψ (x a) = 0 := fun a => by
    rcases hu with hu | hu
    · have := hz a u hu
      rw [hΩ, hπu, hφu, hψu] at this
      simpa using this
    · exact hu _ (hx a)
  refine hk x (fun a => h₁ _ (hx a) (e1 a) (e2 a)) fun a y hy => ?_
  obtain ⟨hy, f1, f2⟩ := h₂ y hy
  have := hz a y hy
  rw [hΩ, hπ, hπ, e1, e2, f1, f2] at this
  simpa using this

theorem finrank_inf_ker [Module.Finite K V] (S : Submodule K V) (φ : V →ₗ[K] K) (u : V)
    (hu : u ∈ S) (hφ : φ u = 1) :
    finrank K (S ⊓ LinearMap.ker φ : Submodule K V) + 1 = finrank K S := by
  have hne : (φ.domRestrict S : Module.Dual K S) ≠ 0 := by
    intro h
    have := LinearMap.congr_fun h ⟨u, hu⟩
    simp [hφ] at this
  rw [← Module.Dual.finrank_ker_add_one_of_ne_zero hne, LinearMap.ker_domRestrict,
    ← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq]

theorem exists_dual (S : Submodule K V) (u : V) (hu : u ∉ S) :
    ∃ φ : V →ₗ[K] K, φ u = 1 ∧ ∀ x ∈ S, φ x = 0 := by
  obtain ⟨f, hf, hS⟩ := S.exists_dual_map_eq_bot_of_notMem hu inferInstance
  refine ⟨(f u)⁻¹ • f, by simp [hf], fun x hx => ?_⟩
  have : f x ∈ S.map f := ⟨x, hx, rfl⟩
  rw [hS] at this
  simp [(Submodule.mem_bot K).1 this]

theorem good_of_finrank_eq [Module.Finite K V] (n : ℕ) :
    ∀ S₁ S₂ : Submodule K V, finrank K S₁ = n → finrank K S₂ = n → Good S₁ S₂ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S₁ S₂ h₁ h₂
  by_cases hE : S₁ = S₂
  · subst hE
    by_cases hx : ∃ x : Fin 2 → V, (∀ a, x a ∈ S₁) ∧ LinearIndependent K x
    · obtain ⟨x, hx, hli⟩ := hx
      have n0 : x 0 ∉ Submodule.span K {x 1} := by
        have := hli.notMem_span_image (s := {1}) (x := 0) (by simp)
        simpa using this
      have n1 : x 1 ∉ Submodule.span K {x 0} := by
        have := hli.notMem_span_image (s := {0}) (x := 1) (by simp)
        simpa using this
      obtain ⟨φ, a1, a2⟩ := exists_dual _ _ n0
      obtain ⟨ψ, b1, b2⟩ := exists_dual _ _ n1
      have a3 := a2 _ (Submodule.mem_span_singleton_self _)
      have b3 := b2 _ (Submodule.mem_span_singleton_self _)
      have hlt : finrank K (S₁ ⊓ LinearMap.ker φ ⊓ LinearMap.ker ψ : Submodule K V) < n := by
        have := finrank_inf_ker S₁ φ _ (hx 0) a1
        have := Submodule.finrank_mono
          (inf_le_left : S₁ ⊓ LinearMap.ker φ ⊓ LinearMap.ker ψ ≤ S₁ ⊓ LinearMap.ker φ)
        omega
      refine good_step S₁ S₁ _ _ (x 0) (x 1) φ ψ a1 a3 b3 b1 (hx 1) (Or.inl (hx 0)) ?_ ?_
        (ih _ hlt _ _ rfl rfl)
      · intro y h1 h2 h3
        exact ⟨⟨h1, h2⟩, h3⟩
      · rintro y ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, h2, h3⟩
    · exact ⟨0, fun _ => rfl, fun x h1 _ h2 => hx ⟨x, h1, h2⟩⟩
  · have l1 : ¬ S₁ ≤ S₂ := fun h => hE (Submodule.eq_of_le_of_finrank_eq h (h₁.trans h₂.symm))
    have l2 : ¬ S₂ ≤ S₁ := fun h =>
      hE (Submodule.eq_of_le_of_finrank_eq h (h₂.trans h₁.symm)).symm
    obtain ⟨u, hu1, hu2⟩ := SetLike.not_le_iff_exists.1 l1
    obtain ⟨v, hv2, hv1⟩ := SetLike.not_le_iff_exists.1 l2
    obtain ⟨φ, a1, a2⟩ := exists_dual _ _ hu2
    obtain ⟨ψ, b1, b2⟩ := exists_dual _ _ hv1
    have c1 := finrank_inf_ker S₁ φ u hu1 a1
    have c2 := finrank_inf_ker S₂ ψ v hv2 b1
    refine good_step S₁ S₂ (S₁ ⊓ LinearMap.ker φ) (S₂ ⊓ LinearMap.ker ψ) u v φ ψ a1 (a2 _ hv2)
      (b2 _ hu1) b1 hv2 (Or.inr b2) ?_ ?_ (ih (n - 1) (by omega) _ _ (by omega) (by omega))
    · intro y h1 h2 _
      exact ⟨h1, h2⟩
    · rintro y ⟨h1, h2⟩
      exact ⟨h1, a2 _ h1, h2⟩

theorem exists_alt_corank_le_one :
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
      (S₁ S₂ : Submodule K V), Module.finrank K S₁ = Module.finrank K S₂ →
      ∃ ω : V →ₗ[K] V →ₗ[K] K, (∀ v, ω v v = 0) ∧ ∀ x : Fin 2 → V, (∀ a, x a ∈ S₁) →
        (∀ a, ∀ y ∈ S₂, ω (x a) y = 0) → ¬ LinearIndependent K x :=
  fun _ _ _ _ _ _ S₁ S₂ h => good_of_finrank_eq _ S₁ S₂ h rfl

end GlobalTheory.AltCorank
end

section

open Module

namespace GlobalTheory.HyodoDef.PairLin

variable {k M M' : Type*} [Field k] [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M']
  [FiniteDimensional k M] [FiniteDimensional k M']

theorem finrank_annihilator_add (β : M →ₗ[k] M' →ₗ[k] k) (S : Submodule k M')
    (hS : LinearMap.ker β.flip ≤ S) :
    finrank k (LinearMap.ker (S.subtype.dualMap ∘ₗ β)) + finrank k S
      = finrank k M + finrank k (LinearMap.ker β.flip) := by
  set φ : M →ₗ[k] Dual k S := S.subtype.dualMap ∘ₗ β with hφ
  set ψ : S →ₗ[k] Dual k M := β.flip ∘ₗ S.subtype with hψ
  have hφψ : φ = ψ.dualMap ∘ₗ (Module.evalEquiv k M).toLinearMap := by
    ext a s; rfl
  have hrange : LinearMap.range φ = LinearMap.range ψ.dualMap := by
    rw [hφψ, LinearEquiv.range_comp]
  have h1 := LinearMap.finrank_range_add_finrank_ker φ
  have h2 := LinearMap.finrank_range_add_finrank_ker ψ
  have h3 : finrank k (LinearMap.range φ) = finrank k (LinearMap.range ψ) := by
    rw [hrange, LinearMap.finrank_range_dualMap_eq_finrank_range]
  have h4 : finrank k (LinearMap.ker ψ) = finrank k (LinearMap.ker β.flip) := by
    have : LinearMap.ker ψ = (LinearMap.ker β.flip).comap S.subtype := by
      rw [hψ, LinearMap.ker_comp]
    rw [this]
    exact (Submodule.comapSubtypeEquivOfLe hS).finrank_eq
  omega

theorem finrank_add_le (β : M →ₗ[k] M' →ₗ[k] k) (Ag Af : Submodule k M) (Ae Af' : Submodule k M')
    (hN : ∀ b : M', (∀ a : M, β a b = 0) → b ∈ Ae ⊓ Af')
    (hg : ∀ a ∈ Ag, ∀ b ∈ Ae, β a b = 0)
    (hf : ∀ a : M, a ∈ Af ↔ ∀ b ∈ Af', β a b = 0) :
    finrank k Ag + finrank k Ae ≤ finrank k Af + finrank k Af' := by
  have hker : ∀ b : M', b ∈ LinearMap.ker β.flip → b ∈ Ae ⊓ Af' := by
    intro b hb
    apply hN b
    intro a
    have := LinearMap.congr_fun (LinearMap.mem_ker.mp hb) a
    simpa using this
  have hNe : LinearMap.ker β.flip ≤ Ae := fun b hb => (hker b hb).1
  have hNf : LinearMap.ker β.flip ≤ Af' := fun b hb => (hker b hb).2
  have he := finrank_annihilator_add β Ae hNe
  have hf' := finrank_annihilator_add β Af' hNf
  have hgle : Ag ≤ LinearMap.ker (Ae.subtype.dualMap ∘ₗ β) := by
    intro a ha
    rw [LinearMap.mem_ker]
    ext ⟨b, hb⟩
    simpa using hg a ha b hb
  have hfeq : Af = LinearMap.ker (Af'.subtype.dualMap ∘ₗ β) := by
    ext a
    rw [hf a, LinearMap.mem_ker]
    constructor
    · intro h
      ext ⟨b, hb⟩
      simpa using h b hb
    · intro h b hb
      have := LinearMap.congr_fun h ⟨b, hb⟩
      simpa using this
  have hAg := Submodule.finrank_mono hgle
  rw [hfeq]
  omega

end GlobalTheory.HyodoDef.PairLin
end

section

open scoped Classical BigOperators
open IsLocalRing Module Matrix

noncomputable section

namespace GlobalTheory.AdaptedLocalData

section Field

variable {k : Type} [Field k]

theorem card_isCompl [Finite k] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (R : Submodule k V) :
    Nat.card {U : Submodule k V // IsCompl R U} =
      Nat.card k ^ (finrank k (V ⧸ R) * finrank k R) := by
  obtain ⟨f₀, hf₀⟩ := R.subtype.exists_leftInverse_of_injective R.ker_subtype
  have h₀ : ∀ x : R, f₀ x = x := fun x => LinearMap.congr_fun hf₀ x
  rw [Nat.card_congr R.isComplEquivProj, ← Module.finrank_linearMap k k,
    ← Module.natCard_eq_pow_finrank (K := k)]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun g => ⟨f₀ + g.comp R.mkQ, fun x => by
      have : R.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero R).2 x.2
      rw [LinearMap.add_apply, LinearMap.comp_apply, this, map_zero, add_zero, h₀]⟩) ⟨?_, ?_⟩)
  · intro g g' h
    have h1 : g.comp R.mkQ = g'.comp R.mkQ := add_left_cancel (congrArg Subtype.val h)
    exact R.linearMap_qext h1
  · rintro ⟨f, hf⟩
    refine ⟨R.liftQ (f - f₀) fun x hx => ?_, Subtype.ext ?_⟩
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, hf ⟨x, hx⟩, h₀ ⟨x, hx⟩, sub_self]
    · simp

theorem card_sup_eq_top [Finite k] (r t : ℕ) (R : Submodule k (Fin (r + t) → k))
    (hR : finrank k R ≤ r) :
    Nat.card {U : Submodule k (Fin (r + t) → k) // finrank k U = t ∧ R ⊔ U = ⊤} =
      if finrank k R = r then Nat.card k ^ (r * t) else 0 := by
  have key : ∀ U : Submodule k (Fin (r + t) → k), R ⊔ U = ⊤ →
      r + t + finrank k ↥(R ⊓ U) = finrank k R + finrank k U := fun U h => by
    have := Submodule.finrank_sup_add_finrank_inf_eq R U
    rwa [h, finrank_top, finrank_fin_fun] at this
  split_ifs with h
  · have hq : finrank k ((Fin (r + t) → k) ⧸ R) = t := by
      have := R.finrank_quotient_add_finrank
      rw [finrank_fin_fun] at this
      omega
    have := card_isCompl R
    rw [hq, h, mul_comm] at this
    rw [← this]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun U => ⟨fun ⟨h1, h2⟩ => ?_, fun hc => ?_⟩)
    · refine ⟨disjoint_iff.2 (Submodule.finrank_eq_zero.1 ?_), codisjoint_iff.2 h2⟩
      have := key U h2
      omega
    · have := key U hc.sup_eq_top
      rw [hc.inf_eq_bot, finrank_bot] at this
      exact ⟨by omega, hc.sup_eq_top⟩
  · haveI : IsEmpty {U : Submodule k (Fin (r + t) → k) // finrank k U = t ∧ R ⊔ U = ⊤} :=
      ⟨fun U => by have := key U.1 U.2.2; have := U.2.1; omega⟩
    exact Nat.card_of_isEmpty

end Field

section Local

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {F : Type} [Field F] [Algebra O F] [IsFractionRing O F]

variable [Finite (ResidueField O)]

end Local

end GlobalTheory.AdaptedLocalData
end
end

section

namespace GlobalTheory.NondegenerateFinrank

theorem finrank_eq_of_nondegenerate {LL : Type} [Field LL] {V V' : Type} [AddCommGroup V] [Module LL V]
    [FiniteDimensional LL V] [AddCommGroup V'] [Module LL V'] [FiniteDimensional LL V']
    (P : V →ₗ[LL] V' →ₗ[LL] LL)
    (h1 : ∀ (x : V), (∀ (y : V'), P x y = 0) → x = 0)
    (h2 : ∀ (y : V'), (∀ (x : V), P x y = 0) → y = 0) :
    Module.finrank LL V = Module.finrank LL V' := by
  have i1 : Function.Injective P := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    exact h1 x (fun y => by simp [hx])
  have i2 : Function.Injective P.flip := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    exact h2 y (fun x => by
      have := LinearMap.congr_fun hy x
      simpa using this)
  have a := LinearMap.finrank_le_finrank_of_injective i1
  have b := LinearMap.finrank_le_finrank_of_injective i2
  have ea : Module.finrank LL (V' →ₗ[LL] LL) = Module.finrank LL V' := Subspace.dual_finrank_eq
  have eb : Module.finrank LL (V →ₗ[LL] LL) = Module.finrank LL V := Subspace.dual_finrank_eq
  omega

theorem main : ∀ {LL : Type} [inst : Field LL] {V V' : Type} [inst_1 : AddCommGroup V] [inst_2 : Module LL V] [FiniteDimensional LL V] [inst_4 : AddCommGroup V'] [inst_5 : Module LL V'] [FiniteDimensional LL V'] (P : V →ₗ[LL] V' →ₗ[LL] LL), (∀ (x : V), (∀ (y : V'), ((P : V → V' →ₗ[LL] LL) x : V' → LL) y = (0 : LL)) → x = (0 : V)) → (∀ (y : V'), (∀ (x : V), ((P : V → V' →ₗ[LL] LL) x : V' → LL) y = (0 : LL)) → y = (0 : V')) → Module.finrank LL V = Module.finrank LL V' :=
  fun P h1 h2 => finrank_eq_of_nondegenerate P h1 h2

end GlobalTheory.NondegenerateFinrank
end
