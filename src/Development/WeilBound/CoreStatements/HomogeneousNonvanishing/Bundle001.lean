module

public import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
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
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.QuasiFinite.Basic

@[expose] public section

section

open AlgebraicGeometry CategoryTheory

namespace PositivityTheory.UnitarySelfGeneration

theorem subfield_closure_eq_top_of_epi : ∀ (O F : Type) [CommRing O] [Field F] (β : O →+* F), (∀ (T : Type) [CommRing T] (g₁ g₂ : F →+* T), g₁.comp β = g₂.comp β → g₁ = g₂) → Subfield.closure (Set.range β) = ⊤ := by
  intro O F _ _ β h
  set K := Subfield.closure (Set.range β) with hK
  by_contra hne
  have key := h (TensorProduct K F F) Algebra.TensorProduct.includeLeftRingHom
    (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := F)).toRingHom (by
      ext o
      have ho : β o ∈ K := Subfield.subset_closure ⟨o, rfl⟩
      have e : β o = (⟨β o, ho⟩ : K) • (1 : F) := by
        rw [Subfield.smul_def, smul_eq_mul, mul_one]
      show β o ⊗ₜ[K] (1 : F) = (1 : F) ⊗ₜ[K] β o
      rw [e, TensorProduct.smul_tmul])
  have hlt : Submodule.span K {(1 : F)} < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro ht
    apply hne
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Submodule.span K {(1 : F)} := ht ▸ Submodule.mem_top
    obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [Subfield.smul_def, smul_eq_mul, mul_one]
    exact k.2
  obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ hlt
  have h1 : φ 1 = 0 := hφ (Submodule.mem_span_singleton_self 1)
  apply hφ0
  ext b
  have e : b ⊗ₜ[K] (1 : F) = (1 : F) ⊗ₜ[K] b := RingHom.congr_fun key b
  have e2 := congrArg (fun z => TensorProduct.lid K F (TensorProduct.map φ LinearMap.id z)) e
  simp only [TensorProduct.map_tmul, TensorProduct.lid_tmul, LinearMap.id_apply, h1, zero_smul] at e2
  rcases smul_eq_zero.1 e2 with h | h
  · simpa using h
  · exact absurd h one_ne_zero

end PositivityTheory.UnitarySelfGeneration
end

section

open AlgebraicGeometry CategoryTheory

namespace PositivityTheory.UnitarySelfGeneration

theorem extends_to_fraction_field : ∀ (O F L : Type) [CommRing O] [Field F] [CommRing L] (β : O →+* F) (θ : O →+* L), Subfield.closure (Set.range β) = ⊤ → (∀ b, β b ≠ 0 → IsUnit (θ b)) → (∀ a, β a = 0 → θ a = 0) → ∃ χ : F →+* L, χ.comp β = θ := by
  intro O F L _ _ _ β θ hcl hu hz
  classical
  set R : Subring F := β.range with hR
  have hk : ∀ a ∈ RingHom.ker β, θ a = 0 := fun a ha => hz a ((RingHom.mem_ker).mp ha)
  let θR : R →+* L :=
    (Ideal.Quotient.lift (RingHom.ker β) θ hk).comp (RingHom.quotientKerEquivRange β).symm.toRingHom
  have hθR : ∀ o : O, θR ⟨β o, o, rfl⟩ = θ o := by
    intro o
    have h : (RingHom.quotientKerEquivRange β).symm ⟨β o, o, rfl⟩ = Ideal.Quotient.mk _ o := by
      rw [RingEquiv.symm_apply_eq]
      rfl
    simp only [θR, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, h,
      Ideal.Quotient.lift_mk]
  have hunit : ∀ r : nonZeroDivisors R, IsUnit (θR r) := by
    intro r
    obtain ⟨b, hb⟩ := (r : R).2
    have hne : (r : R) ≠ 0 := nonZeroDivisors.ne_zero r.2
    have hr : (r : R) = ⟨β b, b, rfl⟩ := Subtype.ext hb.symm
    rw [hr, hθR]
    apply hu
    intro h0
    apply hne
    rw [hr]
    exact Subtype.ext h0
  have hinj : Function.Injective R.subtype := Subtype.val_injective
  let ι : FractionRing R →+* F := IsFractionRing.lift hinj
  have hsurj : Function.Surjective ι := by
    have h := IsFractionRing.lift_fieldRange (K := FractionRing R) hinj
    have hcl' : Subfield.closure (R : Set F) = ⊤ := by rw [hR, RingHom.coe_range]; exact hcl
    rw [Subring.range_subtype, hcl'] at h
    intro x
    have hx : x ∈ ι.fieldRange := by
      change x ∈ (IsFractionRing.lift hinj : FractionRing R →+* F).fieldRange
      rw [h]
      trivial
    obtain ⟨y, hy⟩ := RingHom.mem_fieldRange.mp hx
    exact ⟨y, hy⟩
  let e : FractionRing R ≃+* F := RingEquiv.ofBijective ι ⟨ι.injective, hsurj⟩
  refine ⟨(IsLocalization.lift (M := nonZeroDivisors R) (S := FractionRing R) hunit).comp
    e.symm.toRingHom, ?_⟩
  ext o
  have he : e.symm (β o) = algebraMap R (FractionRing R) ⟨β o, o, rfl⟩ := by
    rw [RingEquiv.symm_apply_eq]
    show β o = ι (algebraMap R (FractionRing R) ⟨β o, o, rfl⟩)
    rw [IsFractionRing.lift_algebraMap]
    rfl
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, he,
    IsLocalization.lift_eq, hθR]

end PositivityTheory.UnitarySelfGeneration
end

section

open NumberField TensorProduct

namespace PositivityTheory.UnitarySelfGeneration

theorem tw_g_herm : ∀ (Z R : Type) [CommRing Z] [CommRing R] [Algebra Z R] (σ : R →ₐ[Z] R), (∀ r, σ (σ r) = r) → ∀ lam : R →ₗ[Z] Z, (∀ r, lam (σ r) = -lam r) → Function.Bijective (fun r : R => lam.comp (LinearMap.mulLeft Z r)) → ∀ (N : ℕ) (ψ : LinearMap.BilinForm Z (Fin N → R)), (∀ x, ψ x x = 0) → Function.Bijective ψ → (∀ (a : R) x y, ψ (a • x) y = ψ x (σ a • y)) → ∃ A : Matrix (Fin N) (Fin N) R, (A.map σ).transpose = A ∧ IsUnit A.det ∧ ∀ x y, ψ x y = lam (∑ i, ∑ j, x i * A i j * σ (y j)) := by
  intro Z R _ _ _ σ hσ lam hlam hbij N ψ halt hψ hadj
  have hskew : ∀ x y, ψ x y = -ψ y x := fun x y => by
    have := halt (x + y)
    simp only [map_add (f := _), LinearMap.add_apply, halt] at this
    linear_combination this
  have hinj : ∀ a b : R, (∀ r, lam (a * r) = lam (b * r)) → a = b := fun a b h =>
    hbij.1 (LinearMap.ext fun r => h r)
  have hex : ∀ i j : Fin N, ∃ a : R, ∀ r : R, lam (a * r) = ψ (r • Pi.single i 1) (Pi.single j 1) := by
    intro i j
    obtain ⟨a, ha⟩ := hbij.2 ((ψ.flip (Pi.single j 1)).comp
      ((LinearMap.toSpanSingleton R (Fin N → R) (Pi.single i 1)).restrictScalars Z))
    exact ⟨a, fun r => LinearMap.congr_fun ha r⟩
  choose A hA using hex
  have hform : ∀ x y, ψ x y = lam (∑ i, ∑ j, x i * A i j * σ (y j)) := by
    intro x y
    conv_lhs => rw [pi_eq_sum_univ' x, pi_eq_sum_univ' y]

    simp only [map_sum, LinearMap.sum_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h1 := hadj (σ (y j)) (x i • Pi.single i 1) (Pi.single j 1)
    rw [hσ, smul_smul, ← hA] at h1
    rw [← h1]
    congr 1; ring
  refine ⟨Matrix.of A, ?_, ?_, hform⟩
  · ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply]
    refine hinj _ _ fun r => ?_
    have h1 := hlam (A j i * σ r)
    rw [map_mul, hσ] at h1
    rw [h1, hA, hA, hadj r, hskew (Pi.single i 1)]
  · rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.vecMul_surjective_iff_isUnit]
    intro w
    let F : (Fin N → R) →ₗ[Z] Z := ∑ j, lam.comp ((LinearMap.mulLeft Z (w j)).comp
      (σ.toLinearMap.comp ((LinearMap.proj j : (Fin N → R) →ₗ[R] R).restrictScalars Z)))
    obtain ⟨x, hx⟩ := hψ.2 F
    refine ⟨x, funext fun j => hinj _ _ fun r => ?_⟩
    have h1 := LinearMap.congr_fun hx (Pi.single j (σ r))
    rw [hform] at h1
    simp only [F, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LinearMap.proj_apply, AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply] at h1
    have h2 : ∑ d, lam (w d * σ (Pi.single (M := fun _ => R) j (σ r) d)) = lam (w j * r) := by
      rw [Finset.sum_eq_single j (fun k _ hk => by simp [Pi.single_eq_of_ne hk]) (by simp),
        Pi.single_eq_same, hσ]
    rw [← h2, ← h1]
    congr 1
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single j (fun k _ hk => by simp [Pi.single_eq_of_ne hk]) (by simp),
      Pi.single_eq_same, hσ]

end PositivityTheory.UnitarySelfGeneration
end

section

open NumberField TensorProduct

namespace PositivityTheory.UnitarySelfGeneration

attribute [local instance] Algebra.TensorProduct.rightAlgebra

theorem free_semilocal (A R : Type) [CommRing A] [IsLocalRing A] [CommRing R] [Algebra A R] [Module.Finite A R] :
    Finite (MaximalSpectrum R) := by
  haveI := (Algebra.QuasiFinite.finite_primesOver (R := A) (S := R)
    (IsLocalRing.maximalIdeal A)).to_subtype
  have hover : ∀ P : MaximalSpectrum R, IsLocalRing.maximalIdeal A = Ideal.under A P.asIdeal :=
    fun P =>
      haveI := P.isMaximal
      (IsLocalRing.eq_maximalIdeal
        (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) P.asIdeal)).symm
  exact Finite.of_injective (β := ↥((IsLocalRing.maximalIdeal A).primesOver R))
    (fun P => ⟨P.asIdeal, P.isMaximal.isPrime, Ideal.LiesOver.mk (hover P)⟩)
    (fun P Q h => MaximalSpectrum.ext (congrArg Subtype.val h))

theorem free_rank (B K L : Type) [CommRing B] [IsDomain B] [Field K] [Algebra B K] [AddCommGroup L] [Module B L]
    [Module.Finite B L] [Module.Projective B L] : Module.finrank K (K ⊗[B] L) = Module.finrank B L := by
  haveI : Module.Flat B L := Module.Flat.of_projective
  haveI : Module.Free K (K ⊗[B] L) := Module.Free.of_divisionRing K _
  have hstalk : ∀ q : PrimeSpectrum B, Module.rankAtStalk L q = Module.finrank B L := by
    intro q
    have hle := Ideal.primeCompl_le_nonZeroDivisors q.asIdeal
    show Module.finrank (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl L) = _
    rw [IsLocalization.finrank_eq (Localization.AtPrime q.asIdeal) q.asIdeal.primeCompl hle,
      IsLocalizedModule.finrank_eq q.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap q.asIdeal.primeCompl L) hle]
  have hK := congrFun (Module.rankAtStalk_eq_finrank_of_free (R := K) (M := K ⊗[B] L))
    (IsLocalRing.closedPoint K)
  rw [Module.rankAtStalk_baseChange, hstalk] at hK
  simp only [Pi.natCast_apply, Nat.cast_id] at hK
  exact hK.symm

theorem tw_g_free : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] (L : Type) [AddCommGroup L] [Module (𝓞 E) L] [Module.Finite (𝓞 E) L] [Module.Projective (𝓞 E) L], ∃ φ : (ℤ_[p] ⊗[ℤ] L) ≃ₗ[ℤ_[p]] (Fin (Module.finrank (𝓞 E) L) → ℤ_[p] ⊗[ℤ] 𝓞 E), ∀ (z : ℤ_[p]) (a : 𝓞 E) (x : L), φ (z ⊗ₜ (a • x)) = ((1 : ℤ_[p]) ⊗ₜ[ℤ] a : ℤ_[p] ⊗[ℤ] 𝓞 E) • φ (z ⊗ₜ x) := by
  intro E _ _ p _ L _ _ _ _
  haveI : Module.Flat (𝓞 E) L := Module.Flat.of_projective
  haveI : Module.Finite ℤ_[p] (ℤ_[p] ⊗[ℤ] 𝓞 E) := Module.Finite.base_change ℤ ℤ_[p] (𝓞 E)
  haveI : Finite (MaximalSpectrum (ℤ_[p] ⊗[ℤ] 𝓞 E)) :=
    PositivityTheory.UnitarySelfGeneration.free_semilocal ℤ_[p] (ℤ_[p] ⊗[ℤ] 𝓞 E)
  haveI : Module.Flat (ℤ_[p] ⊗[ℤ] 𝓞 E) ((ℤ_[p] ⊗[ℤ] 𝓞 E) ⊗[𝓞 E] L) :=
    Module.Flat.baseChange (𝓞 E) (ℤ_[p] ⊗[ℤ] 𝓞 E) L
  haveI : Module.Finite (ℤ_[p] ⊗[ℤ] 𝓞 E) ((ℤ_[p] ⊗[ℤ] 𝓞 E) ⊗[𝓞 E] L) :=
    Module.Finite.base_change (𝓞 E) (ℤ_[p] ⊗[ℤ] 𝓞 E) L
  haveI : Algebra.IsPushout ℤ ℤ_[p] (𝓞 E) (ℤ_[p] ⊗[ℤ] 𝓞 E) := TensorProduct.isPushout
  have hrank : ∀ P : MaximalSpectrum (ℤ_[p] ⊗[ℤ] 𝓞 E),
      Module.finrank ((ℤ_[p] ⊗[ℤ] 𝓞 E) ⧸ P.asIdeal)
        (((ℤ_[p] ⊗[ℤ] 𝓞 E) ⧸ P.asIdeal) ⊗[ℤ_[p] ⊗[ℤ] 𝓞 E] ((ℤ_[p] ⊗[ℤ] 𝓞 E) ⊗[𝓞 E] L)) =
        Module.finrank (𝓞 E) L := by
    intro P
    haveI := P.isMaximal
    letI : Field ((ℤ_[p] ⊗[ℤ] 𝓞 E) ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
    exact (TensorProduct.AlgebraTensorModule.cancelBaseChange (𝓞 E) (ℤ_[p] ⊗[ℤ] 𝓞 E)
      ((ℤ_[p] ⊗[ℤ] 𝓞 E) ⧸ P.asIdeal) ((ℤ_[p] ⊗[ℤ] 𝓞 E) ⧸ P.asIdeal) L).finrank_eq.trans
      (PositivityTheory.UnitarySelfGeneration.free_rank (𝓞 E) ((ℤ_[p] ⊗[ℤ] 𝓞 E) ⧸ P.asIdeal) L)
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (ℤ_[p] ⊗[ℤ] 𝓞 E)
    ((ℤ_[p] ⊗[ℤ] 𝓞 E) ⊗[𝓞 E] L) _ hrank
  refine ⟨(Algebra.IsPushout.cancelBaseChange ℤ ℤ_[p] (𝓞 E) (ℤ_[p] ⊗[ℤ] 𝓞 E) L).symm.trans
    (b.equivFun.restrictScalars ℤ_[p]), ?_⟩
  intro z a x
  have key : (algebraMap ℤ_[p] (ℤ_[p] ⊗[ℤ] 𝓞 E) z) ⊗ₜ[𝓞 E] (a • x) =
      ((1 : ℤ_[p]) ⊗ₜ[ℤ] a : ℤ_[p] ⊗[ℤ] 𝓞 E) • ((algebraMap ℤ_[p] (ℤ_[p] ⊗[ℤ] 𝓞 E) z) ⊗ₜ[𝓞 E] x) := by
    rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def, smul_eq_mul,
      Algebra.TensorProduct.right_algebraMap_apply]
  simp only [LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    Algebra.IsPushout.cancelBaseChange_symm_tmul, key, map_smul]

end PositivityTheory.UnitarySelfGeneration
end
