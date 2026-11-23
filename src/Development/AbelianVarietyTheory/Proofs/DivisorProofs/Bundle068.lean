module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Valuation.LocalSubring
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
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Geometry.Manifold.StructureGroupoid
import Mathlib.NumberTheory.ModularForms.SlashActions
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Max

@[expose] public section

section

namespace GlobalTheory.BasisLeftInverse

theorem exists_left_inv {E : Type} [Field E] {n d : ℕ} (B : Matrix (Fin n) (Fin d) E)
    (h : LinearIndependent E B.col) : ∃ C : Matrix (Fin d) (Fin n) E, C * B = 1 := by
  have hinj : Function.Injective B.mulVec := Matrix.mulVec_injective_iff.2 h
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' B) (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [← LinearMap.toMatrix'_toLin' B, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]

theorem injective_mulVec_map_basis {E : Type} [Field E] {n : ℕ} (V : Submodule E (Fin n → E))
    (τ : E →+* ℂ) :
    Function.Injective (Matrix.mulVec (Matrix.of fun (k : Fin n) (i : Fin (Module.finrank E V)) =>
      τ (((Module.finBasis E V i : V) : Fin n → E) k))) := by
  let B : Matrix (Fin n) (Fin (Module.finrank E V)) E :=
    Matrix.of fun k i => ((Module.finBasis E V i : V) : Fin n → E) k
  have hB : LinearIndependent E B.col :=
    (Module.finBasis E V).linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  obtain ⟨C, hC⟩ := exists_left_inv B hB
  have hC' : C.map τ * B.map τ = 1 := by
    rw [← Matrix.map_mul, hC, Matrix.map_one τ (map_zero τ) (map_one τ)]
  change Function.Injective (B.map τ).mulVec
  intro v w hvw
  have h1 : Matrix.mulVec (C.map τ * B.map τ) v = Matrix.mulVec (C.map τ * B.map τ) w := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hvw]
  rwa [hC', Matrix.one_mulVec, Matrix.one_mulVec] at h1

end GlobalTheory.BasisLeftInverse
end

section

namespace GlobalTheory

theorem complex_matrix_descends_of_rational_on_tuple : ∀ {K : Type} [Field K] (σ : K →+* ℂ) {T : Type} (n D : ℕ) (dQ nV : T → ℕ) (ι : ∀ t, Matrix (Fin D) (Fin (dQ t)) K) (Pq : ∀ t, Matrix (Fin (dQ t)) (Fin (nV t)) K) (V : ∀ t, Matrix (Fin n) (Fin (nV t)) K) (r : T → K) (U : Set T) (t0 : T) (Ψc : Matrix (Fin n) (Fin D) ℂ), t0 ∈ U → Function.Bijective (ι t0).mulVec → Function.Surjective (Pq t0).mulVec → (∀ t ∈ U, Ψc * (ι t * Pq t).map σ = ((r t)⁻¹ • V t).map σ) → (∃ Ψ : Matrix (Fin n) (Fin D) K, Ψ.map σ = Ψc ∧ ∀ t ∈ U, Ψ * ι t * Pq t = (r t)⁻¹ • V t) ∧ (Function.Injective Ψc.mulVec → r t0 = 1 → LinearMap.ker (V t0).mulVecLin = LinearMap.ker (Pq t0).mulVecLin) := by
  intro K _ σ T n D dQ nV ι Pq V r U t0 Ψc ht0 hι hP h
  have hσ : Function.Injective σ := σ.injective
  have hsurj : Function.Surjective (ι t0 * Pq t0).mulVec := by
    intro y
    obtain ⟨x, rfl⟩ := hι.2 y
    obtain ⟨z, rfl⟩ := hP x
    exact ⟨z, (Matrix.mulVec_mulVec _ _ _).symm⟩
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.1 hsurj
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Matrix (Fin n) (Fin D) K, Ψ = ((r t0)⁻¹ • V t0) * R := ⟨_, rfl⟩
  have hΨc : Ψ.map σ = Ψc := by
    calc Ψ.map σ = ((r t0)⁻¹ • V t0).map σ * R.map σ := by rw [hΨ, Matrix.map_mul]
      _ = Ψc * (ι t0 * Pq t0).map σ * R.map σ := by rw [h t0 ht0]
      _ = Ψc * ((ι t0 * Pq t0) * R).map σ := by rw [Matrix.map_mul (M := R), Matrix.mul_assoc]
      _ = Ψc := by rw [hR, Matrix.map_one σ σ.map_zero σ.map_one, Matrix.mul_one]
  have hall : ∀ t ∈ U, Ψ * ι t * Pq t = (r t)⁻¹ • V t := by
    intro t ht
    apply Matrix.map_injective hσ
    show (Ψ * ι t * Pq t).map σ = ((r t)⁻¹ • V t).map σ
    rw [Matrix.mul_assoc, Matrix.map_mul, hΨc, h t ht]
  refine ⟨⟨Ψ, hΨc, hall⟩, fun hinj hr => ?_⟩
  have key : Ψ * ι t0 * Pq t0 = V t0 := by
    rw [hall t0 ht0, hr, inv_one, one_smul]
  have hΨinj : Function.Injective Ψ.mulVec := by
    intro x y hxy
    have hc : Ψc.mulVec (fun j => σ (x j)) = Ψc.mulVec (fun j => σ (y j)) := by
      funext i
      change (Ψc).mulVec (σ ∘ x) i = (Ψc).mulVec (σ ∘ y) i
      rw [← hΨc, ← RingHom.map_mulVec, ← RingHom.map_mulVec, hxy]
    funext j
    exact hσ (congrFun (hinj hc) j)
  ext v
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro hv
    rw [← key, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hv
    have h1 : (ι t0).mulVec ((Pq t0).mulVec v) = 0 := hΨinj (hv.trans (Matrix.mulVec_zero Ψ).symm)
    exact hι.1 (h1.trans (Matrix.mulVec_zero (ι t0)).symm)
  · intro hv
    rw [← key, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

end GlobalTheory
end

section

namespace GlobalTheory.AdTh

theorem scalar_of_intertwines_up_to_scalar (Γ M : Type) [Group Γ] [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] [Nontrivial M] (ρ : Γ →* Module.End ℂ M) (S : Set Γ)
    (hS : Subgroup.closure S = ⊤) (htr : ∀ γ ∈ S, LinearMap.trace ℂ M (ρ γ) ≠ 0)
    (hirr : ∀ U : Submodule ℂ M, (∀ γ, U.map (ρ γ) ≤ U) → U = ⊥ ∨ U = ⊤)
    (T : M →ₗ[ℂ] M) (χ : Γ → ℂ) (hT : Function.Injective T)
    (h : ∀ γ x, T (ρ γ x) = χ γ • ρ γ (T x)) : ∃ a : ℂ, ∀ x, T x = a • x := by
  have hu : IsUnit (T : Module.End ℂ M) :=
    (Module.End.isUnit_iff _).2 ⟨hT, LinearMap.injective_iff_surjective.1 hT⟩
  obtain ⟨u, hu⟩ := hu
  have h1 : ∀ γ, (u : Module.End ℂ M) * ρ γ = χ γ • (ρ γ * u) := by
    intro γ
    ext x
    simp [hu, h]
  have hχ : ∀ γ ∈ S, χ γ = 1 := by
    intro γ hγ
    have h2 : (u : Module.End ℂ M) * ρ γ * (↑u⁻¹ : Module.End ℂ M) = χ γ • ρ γ := by
      rw [h1, smul_mul_assoc, mul_assoc, Units.mul_inv, mul_one]
    have h3 := congrArg (LinearMap.trace ℂ M) h2
    rw [LinearMap.trace_mul_comm, ← mul_assoc, Units.inv_mul, one_mul, map_smul, smul_eq_mul] at h3
    have h4 := htr γ hγ
    have : (χ γ - 1) * LinearMap.trace ℂ M (ρ γ) = 0 := by linear_combination -h3
    rcases mul_eq_zero.1 this with h5 | h5
    · exact sub_eq_zero.1 h5
    · exact absurd h5 h4
  have hc : ∀ γ, Commute (u : Module.End ℂ M) (ρ γ) := by
    intro γ
    have hγ : γ ∈ Subgroup.closure S := hS ▸ Subgroup.mem_top γ
    induction hγ using Subgroup.closure_induction with
    | mem x hx =>
      have := h1 x
      rw [hχ x hx, one_smul] at this
      exact this
    | one => rw [map_one]; exact Commute.one_right _
    | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul_right hy
    | inv x _ hx =>
      have e1 : ρ x * ρ x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      have e2 : ρ x⁻¹ * ρ x = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
      exact Commute.units_inv_right (u := ⟨ρ x, ρ x⁻¹, e1, e2⟩) hx
  obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue (T : Module.End ℂ M)
  refine ⟨a, fun x => ?_⟩
  rcases hirr (Module.End.eigenspace T a) (by
      rintro γ _ ⟨y, hy, rfl⟩
      have hy' : T y = a • y := Module.End.mem_eigenspace_iff.1 hy
      rw [Module.End.mem_eigenspace_iff]
      have := congrArg (fun f : Module.End ℂ M => f y) (hc γ).eq
      simp only [hu, Module.End.mul_apply] at this
      rw [this, hy', map_smul]) with h0 | h0
  · exact absurd h0 (Module.End.hasEigenvalue_iff.1 ha)
  · exact Module.End.mem_eigenspace_iff.1 (h0 ▸ Submodule.mem_top)

end GlobalTheory.AdTh
end

section

open Matrix
open scoped Classical

namespace GlobalTheory

theorem pi_prod_rows_orthonormal {K : Type} [Fintype K] [DecidableEq K] {κ : K → Type}
    [∀ k, Fintype (κ k)] [∀ k, DecidableEq (κ k)] [DecidableEq (∀ k, κ k)]
    (A : ∀ k, Matrix (κ k) (κ k) ℂ)
    (hA : ∀ k a b, ∑ y, A k a y * star (A k b y) = if a = b then 1 else 0)
    (T T'' : ∀ k, κ k) :
    ∑ x : ∀ k, κ k, (∏ k, A k (T k) (x k)) * star (∏ k, A k (T'' k) (x k)) =
      if T = T'' then 1 else 0 := by
  simp only [star_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun k y => A k (T k) y * star (A k (T'' k) y))]
  rw [Finset.prod_congr rfl (fun k _ => hA k (T k) (T'' k)), Finset.prod_boole]
  by_cases hT : T = T''
  · subst hT; simp
  · rw [if_neg hT, if_neg]
    intro hall
    exact hT (funext fun k => hall k (Finset.mem_univ k))

theorem unitary_tensor_places_positions : ∀ (J ι : Type) [Fintype J] [DecidableEq J] [Fintype ι]
    [DecidableEq ι] (n : J → ℕ) (C : J → Matrix ι ι ℂ), (∀ j, C j ∈ Matrix.unitaryGroup ι ℂ) →
    (Matrix.of fun T T' : (∀ j, Fin (n j) → ι) => ∏ j, ∏ r, C j (T j r) (T' j r)) ∈
      Matrix.unitaryGroup (∀ j, Fin (n j) → ι) ℂ := by
  intro J ι _ _ _ _ n C hC
  have hC' : ∀ j (a b : ι), ∑ y, C j a y * star (C j b y) = if a = b then 1 else 0 := by
    intro j a b
    have := congrFun (congrFun ((mem_unitaryGroup_iff).1 (hC j)) a) b
    simpa only [Matrix.mul_apply, star_apply, Matrix.one_apply] using this
  have hD : ∀ j (S S'' : Fin (n j) → ι),
      ∑ y : Fin (n j) → ι, (∏ r, C j (S r) (y r)) * star (∏ r, C j (S'' r) (y r)) =
        if S = S'' then 1 else 0 := fun j =>
    pi_prod_rows_orthonormal (κ := fun _ => ι) (fun _ => C j) (fun _ => hC' j)
  have key := pi_prod_rows_orthonormal (κ := fun j => Fin (n j) → ι)
    (fun j => of fun S S' : Fin (n j) → ι => ∏ r, C j (S r) (S' r))
    (fun j a b => by simpa only [of_apply] using hD j a b)
  rw [mem_unitaryGroup_iff]
  ext T T''
  simpa only [Matrix.mul_apply, star_apply, of_apply, Matrix.one_apply] using key T T''

end GlobalTheory
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.CMModel

theorem exists_valuationSubring_complex_over_prime :
    ∀ (F : IntermediateField ℚ ℂ) [NumberField F] (w : HeightOneSpectrum (𝓞 F)),
      ∃ V : ValuationSubring ℂ, ∀ x : F, (x : ℂ) ∈ V ↔ x ∈ w.valuationSubringAtPrime F := by
  intro F _ w
  set R := w.valuationSubringAtPrime F with hR
  obtain ⟨V, hV, hloc⟩ := IsLocalRing.exists_factor_valuationRing
    ((algebraMap F ℂ).comp R.subtype)
  refine ⟨V, fun x => ⟨fun hx => ?_, fun hx => hV ⟨x, hx⟩⟩⟩
  by_contra hxR
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hxR R.zero_mem
  have hinv : x⁻¹ ∈ R := (R.mem_or_inv_mem x).resolve_left hxR
  have hx0' : (x : ℂ) ≠ 0 := by exact_mod_cast hx0
  have hu : IsUnit ((((algebraMap F ℂ).comp R.subtype).codRestrict V.toSubring hV) ⟨x⁻¹, hinv⟩) := by
    refine IsUnit.of_mul_eq_one ⟨(x : ℂ), hx⟩ ?_
    apply Subtype.ext
    change ((x⁻¹ : F) : ℂ) * (x : ℂ) = 1
    rw [IntermediateField.coe_inv, inv_mul_cancel₀ hx0']
  have hu' : IsUnit (⟨x⁻¹, hinv⟩ : R) := hloc.map_nonunit _ hu
  obtain ⟨y, hy⟩ := hu'.exists_right_inv
  have hy' : x⁻¹ * (y : F) = 1 := congrArg Subtype.val hy
  have : x = (y : F) := by
    have h := congrArg (x * ·) hy'
    simp only [← mul_assoc, mul_inv_cancel₀ hx0, one_mul, mul_one] at h
    exact h.symm
  exact hxR (this ▸ y.2)

end GlobalTheory.CMModel
end

section

namespace GlobalTheory


open Classical in
theorem iSup_stable_inf_typeSpace {G E C : Type} [Group G] [Fintype G] [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ G E) (P : Subgroup G) (ψ : P →* ℂˣ) (U : C → Submodule ℂ E) (S : C → Prop)
    (hU : ∀ c g, (U c).map (ρ g) ≤ U c) :
    (⨆ (c : C) (_ : S c), U c) ⊓
        (⨅ h : P, LinearMap.ker (ρ (h : G) - ((ψ h : ℂˣ) : ℂ) • LinearMap.id)) =
      ⨆ (c : C) (_ : S c), U c ⊓
        (⨅ h : P, LinearMap.ker (ρ (h : G) - ((ψ h : ℂˣ) : ℂ) • LinearMap.id)) := by
  set K : Submodule ℂ E :=
    ⨅ h : P, LinearMap.ker (ρ (h : G) - ((ψ h : ℂˣ) : ℂ) • LinearMap.id) with hK
  have memK : ∀ x, x ∈ K ↔ ∀ h : P, ρ (h : G) x = ((ψ h : ℂˣ) : ℂ) • x := by
    intro x
    simp [hK, Submodule.mem_iInf, sub_eq_zero]
  have hc : (Fintype.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  let T : E →ₗ[ℂ] E :=
    (Fintype.card P : ℂ)⁻¹ • ∑ h : P, (((ψ h)⁻¹ : ℂˣ) : ℂ) • ρ (h : G)
  have hT : ∀ x, T x = (Fintype.card P : ℂ)⁻¹ • ∑ h : P, (((ψ h)⁻¹ : ℂˣ) : ℂ) • ρ (h : G) x := by
    intro x
    simp only [T, LinearMap.smul_apply, LinearMap.sum_apply]
  have h1 : ∀ x ∈ K, T x = x := by
    intro x hx
    rw [hT]
    have : ∀ h : P, (((ψ h)⁻¹ : ℂˣ) : ℂ) • ρ (h : G) x = x := by
      intro h
      rw [(memK x).1 hx h, smul_smul, Units.inv_mul, one_smul]
    simp only [this, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have h2 : ∀ x, T x ∈ K := by
    intro x
    rw [memK]
    intro k
    rw [hT, map_smul, smul_comm]
    congr 1

    rw [map_sum, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft k) _ _ ?_
    intro h
    simp only [Equiv.coe_mulLeft, map_smul, map_mul, Subgroup.coe_mul, Module.End.mul_apply,
      smul_smul]
    congr 1
    rw [← Units.val_mul, mul_inv_rev, mul_comm (ψ h)⁻¹, mul_inv_cancel_left]
  have h3 : ∀ c, ∀ x ∈ U c, T x ∈ U c := by
    intro c x hx
    rw [hT]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun h _ =>
      Submodule.smul_mem _ _ (hU c h (Submodule.mem_map_of_mem hx)))
  apply le_antisymm
  · rintro x ⟨hx, hxK⟩
    have hle : (⨆ (c : C) (_ : S c), U c) ≤ (⨆ (c : C) (_ : S c), U c ⊓ K).comap T := by
      refine iSup₂_le fun c hc y hy => ?_
      exact (le_iSup₂_of_le (f := fun (c : C) (_ : S c) => U c ⊓ K) c hc le_rfl)
        (show T y ∈ U c ⊓ K from ⟨h3 c y hy, h2 y⟩)
    have := hle hx
    rwa [Submodule.mem_comap, h1 x hxK] at this
  · exact iSup₂_le fun c hc => inf_le_inf_right _
      (le_iSup₂_of_le (f := fun (c : C) (_ : S c) => U c) c hc le_rfl)

end GlobalTheory
end

section

noncomputable section

namespace GlobalTheory.InvTransposeEnds

section General

variable {G H V W Y : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W] [AddCommGroup Y] [Module ℂ Y]

theorem isIrreducible_comp {ρ : Representation ℂ G V} (h : ρ.IsIrreducible) (φ : H →* G)
    (hφ : Function.Surjective φ) : Representation.IsIrreducible (ρ.comp φ) := by
  haveI hV : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    exact (bot_ne_top (α := Subrepresentation ρ))
      (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
  refine { toNontrivial := ⟨⟨⊥, ⊤, fun e => ?_⟩⟩, eq_bot_or_eq_top := fun S => ?_ }
  · exact bot_ne_top (α := Submodule ℂ V) (congrArg Subrepresentation.toSubmodule e)
  · let S' : Subrepresentation ρ := ⟨S.toSubmodule, fun g v hv => by
      obtain ⟨x, rfl⟩ := hφ g
      exact S.apply_mem_toSubmodule x hv⟩
    rcases h.eq_bot_or_eq_top S' with e | e
    · exact Or.inl (Subrepresentation.toSubmodule_injective
        (congrArg (Subrepresentation.toSubmodule (ρ := ρ)) e :))
    · exact Or.inr (Subrepresentation.toSubmodule_injective
        (congrArg (Subrepresentation.toSubmodule (ρ := ρ)) e :))

end General

end GlobalTheory.InvTransposeEnds
end
end

section

noncomputable section

namespace GlobalTheory.ReducedFactor

section General

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem nontrivial_of_irr {ρ : Representation ℂ G V} (h : ρ.IsIrreducible) : Nontrivial V := by
  have : IsSimpleOrder (Subrepresentation ρ) := h
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
  apply Subrepresentation.toSubmodule_injective
  ext x
  rw [Subsingleton.elim x 0]
  exact iff_of_true (zero_mem _) (zero_mem _)

end General

section Tensor

variable {G H V V' U : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  [AddCommGroup U] [Module ℂ U]

end Tensor

end GlobalTheory.ReducedFactor

namespace GlobalTheory.ReducedFactor

end GlobalTheory.ReducedFactor
end
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open Polynomial

namespace GlobalTheory.QFam

theorem isIntegral_of_esymm_mem (ι : Type) [Fintype ι] (R : Subring ℂ) (x : ι → ℂ)
    (h : ∀ k : ℕ, (∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, x i) ∈ R) (i : ι) :
    IsIntegral R (x i) := by
  classical
  set Q : ℂ[X] := ∏ j, (X + C (x j)) with hQ
  have hmon : Q.Monic := monic_prod_of_monic _ _ (fun j _ => monic_X_add_C (x j))
  have hdeg : Q.natDegree = (Finset.univ : Finset ι).card := by
    rw [hQ, natDegree_prod_of_monic _ _ (fun j _ => monic_X_add_C (x j))]
    simp
  have hl : Q ∈ Polynomial.lifts (algebraMap R ℂ) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    by_cases hn : n ≤ (Finset.univ : Finset ι).card
    · rw [hQ, Finset.prod_X_add_C_coeff _ _ hn]
      exact ⟨⟨_, h _⟩, rfl⟩
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
      exact ⟨0, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hmon
  have hneg : IsIntegral R (-x i) := by
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.eval_map, hq, hQ, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  simpa using hneg.neg

end GlobalTheory.QFam
end

section

namespace GlobalTheory.PositiveLowerBoundFinset

theorem pos_lower_bound_on_finset : ∀ {Y : Type} (T : Finset Y) (f : Y → ℝ),
    (∀ (P : Y), (0 : ℝ) < f P) → ∃ (r : ℝ), (0 : ℝ) < r ∧ ∀ P ∈ T, r ≤ f P := by
  intro Y T f hf
  rcases T.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, by simp [h]⟩
  · obtain ⟨x, -, hmin⟩ := T.exists_min_image f h
    exact ⟨f x, hf x, hmin⟩

end GlobalTheory.PositiveLowerBoundFinset
end
