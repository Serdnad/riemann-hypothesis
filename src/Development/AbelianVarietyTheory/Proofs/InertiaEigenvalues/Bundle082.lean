module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle023
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle014
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle025
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle026
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

namespace GlobalTheory.SmGL.EvalInj

open ValuativeRel Topology in
private theorem eq_zero_of_sum_intertwining_apply_eq_zero {H X Y : Type} [Group H] [AddCommGroup X]
    [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ H X)
    (ρ : Representation ℂ H Y) (hρ : ρ.IsIrreducible)
    (hschur : ∀ T : ρ.IntertwiningMap ρ, ∃ c : ℂ, ∀ v, T v = c • v) :
    ∀ (m : ℕ) (φ : Fin m → (Y →ₗ[ℂ] X)), LinearIndependent ℂ φ →
      (∀ i g v, φ i (ρ g v) = τ g (φ i v)) → ∀ y : Fin m → Y, ∑ i, φ i (y i) = 0 → y = 0 := by
  intro m
  induction m with
  | zero => intro φ _ _ y _; exact Subsingleton.elim _ _
  | succ m ih =>
    intro φ hli hφ y hy
    let Φ : (Fin (m + 1) → Y) →ₗ[ℂ] X := ∑ i, (φ i).comp (LinearMap.proj i)
    have hΦ : ∀ w, Φ w = ∑ i, φ i (w i) := fun w => by simp [Φ]
    let S := LinearMap.ker Φ
    have hSinv : ∀ g, ∀ w ∈ S, (fun i => ρ g (w i)) ∈ S := by
      intro g w hw
      rw [LinearMap.mem_ker, hΦ] at hw ⊢
      simp_rw [hφ]

      rw [← map_sum, hw, map_zero]
    let p : S →ₗ[ℂ] Y := (LinearMap.proj (Fin.last m)).comp S.subtype
    have hp : Function.Injective p := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro w hw
      have hw0 : (w : Fin (m + 1) → Y) (Fin.last m) = 0 := hw
      have hsum : ∑ i : Fin m, φ (Fin.castSucc i) ((w : Fin (m + 1) → Y) (Fin.castSucc i)) = 0 := by
        have hw' := w.2
        rw [LinearMap.mem_ker, hΦ, Fin.sum_univ_castSucc, hw0, map_zero, add_zero] at hw'
        exact hw'
      have hzero := ih (fun i => φ (Fin.castSucc i)) (hli.comp _ (Fin.castSucc_injective m))
        (fun i => hφ _) _ hsum
      apply Subtype.ext
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact hw0
      · exact congrFun hzero j
    let R : Subrepresentation ρ := ⟨LinearMap.range p, by
      rintro g _ ⟨w, rfl⟩
      exact ⟨⟨fun i => ρ g ((w : Fin (m + 1) → Y) i), hSinv g w w.2⟩, rfl⟩⟩
    have hyS : y ∈ S := by rw [LinearMap.mem_ker, hΦ]; exact hy
    haveI := hρ
    rcases IsSimpleOrder.eq_bot_or_eq_top R with hR | hR
    · have hrange : LinearMap.range p = ⊥ := congrArg Subrepresentation.toSubmodule hR
      have hpy : p ⟨y, hyS⟩ = 0 := by
        rw [LinearMap.range_eq_bot] at hrange
        rw [hrange]
        rfl
      exact congrArg Subtype.val (hp (hpy.trans (map_zero p).symm))
    · exfalso
      have hrange : LinearMap.range p = ⊤ := congrArg Subrepresentation.toSubmodule hR
      let e := LinearEquiv.ofBijective p ⟨hp, LinearMap.range_eq_top.mp hrange⟩
      have hlast : ∀ v, (e.symm v : Fin (m + 1) → Y) (Fin.last m) = v := fun v =>
        e.apply_symm_apply v
      have he : ∀ g v, e.symm (ρ g v) =
          ⟨fun i => ρ g ((e.symm v : Fin (m + 1) → Y) i), hSinv g _ (e.symm v).2⟩ := by
        intro g v
        apply e.injective
        rw [LinearEquiv.apply_symm_apply]
        show ρ g v = ρ g ((e.symm v : Fin (m + 1) → Y) (Fin.last m))
        rw [hlast]
      let T : Fin m → ρ.IntertwiningMap ρ := fun j =>
        ⟨(LinearMap.proj (Fin.castSucc j)).comp (S.subtype.comp e.symm.toLinearMap), by
          intro g
          ext v
          simp [he]⟩
      choose c hc using fun j => hschur (T j)
      have hT : ∀ j v, (e.symm v : Fin (m + 1) → Y) (Fin.castSucc j) = c j • v := fun j v => hc j v
      have hzero : ∑ i, (Fin.snoc (α := fun _ => ℂ) c 1 i) • φ i = 0 := by
        ext v
        have hv := (e.symm v).2
        rw [LinearMap.mem_ker, hΦ, Fin.sum_univ_castSucc] at hv
        simp only [hT, hlast, map_smul] at hv
        simpa [Fin.sum_univ_castSucc] using hv
      have h1 := (Fintype.linearIndependent_iff.mp hli) _ hzero (Fin.last m)
      simp at h1


open ValuativeRel Topology in
theorem _root_.GlobalTheory.SmGL.EvalInj.lift_subtype_injective :
    ∀ (H X Y : Type) [Group H] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
      (τ : Representation ℂ H X) (ρ : Representation ℂ H Y), ρ.IsIrreducible →
      (∀ T : ρ.IntertwiningMap ρ, ∃ c : ℂ, ∀ v, T v = c • v) →
      ∀ (M : Submodule ℂ (Y →ₗ[ℂ] X)), (∀ φ ∈ M, ∀ g v, φ (ρ g v) = τ g (φ v)) →
      Function.Injective (TensorProduct.lift M.subtype) := by
  intro H X Y _ _ _ _ _ τ ρ hρ hschur M hM
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨M', hfin, hsub⟩ :=
    TensorProduct.exists_finite_submodule_left_of_setFinite {t} (Set.finite_singleton t)
  obtain ⟨t₀, rfl⟩ := hsub (Set.mem_singleton t)
  haveI := hfin
  let b := Module.finBasis ℂ M'
  set y : Fin (Module.finrank ℂ M') → Y := fun i => TensorProduct.equivFinsuppOfBasisLeft b t₀ i
    with hy
  have ht₀ : t₀ = ∑ i, b i ⊗ₜ[ℂ] y i := by
    conv_lhs => rw [← (TensorProduct.equivFinsuppOfBasisLeft b).symm_apply_apply t₀]
    rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum_fintype]
    intro i
    exact TensorProduct.tmul_zero _ _
  let φ : Fin (Module.finrank ℂ M') → (Y →ₗ[ℂ] X) := fun i => ((b i : M) : Y →ₗ[ℂ] X)
  have hli : LinearIndependent ℂ φ :=
    (b.linearIndependent.map' M'.subtype (Submodule.ker_subtype _)).map' M.subtype
      (Submodule.ker_subtype _)
  have hsum : ∑ i, φ i (y i) = 0 := by
    rw [ht₀] at ht

    simpa [map_sum, φ] using ht
  have hy0 := eq_zero_of_sum_intertwining_apply_eq_zero τ ρ hρ hschur _ φ hli
    (fun i g v => hM _ (b i : M).2 g v) y hsum
  rw [ht₀, hy0]
  simp

end GlobalTheory.SmGL.EvalInj
end

section

open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_limit_family_of_finite_coefficients' : ∀ (σ I R : Type) [Finite σ] [Finite I] [Finite R] (F : ℕ → I → (σ →₀ ℕ) → R), ∃ G : I → (σ →₀ ℕ) → R, ∀ N M₀ : ℕ, ∃ M, M₀ ≤ M ∧ ∀ x m, m.degree ≤ N → F M x m = G x m := by
  first | exact @GlobalTheory.exists_limit_family_of_finite_coefficients | exact GlobalTheory.exists_limit_family_of_finite_coefficients | (intros; apply GlobalTheory.exists_limit_family_of_finite_coefficients <;> assumption)
end

section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

theorem _root_.GlobalTheory.T.exists_residue_annihilator_of_not_standard_column_form_alt : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ x : Matrix (Fin r ⊕ Fin t) (Fin r) O, (¬ ∃ (g : GL (Fin r) K) (z : Matrix (Fin r ⊕ Fin t) (Fin r) O), x.map (algebraMap O K) * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z).map (algebraMap O K)) → ∃ a : Fin r → IsLocalRing.ResidueField O, a ≠ 0 ∧ ∀ u : Fin r ⊕ Fin t → O, (fun i => algebraMap O K (u i)) ∈ Submodule.span K (Set.range fun j => fun i => algebraMap O K (x i j)) → (∀ i, IsLocalRing.residue O (u (Sum.inr i)) = 0) → a ⬝ᵥ (fun i => IsLocalRing.residue O (u (Sum.inl i))) = 0 := by
  first | exact @GlobalTheory.exists_residue_annihilator_of_not_standard_column_form | exact GlobalTheory.exists_residue_annihilator_of_not_standard_column_form | (intros; apply GlobalTheory.exists_residue_annihilator_of_not_standard_column_form <;> assumption)
end

section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

theorem _root_.GlobalTheory.T.frame_translate_lattice_coset_subset : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ (x : Matrix (Fin r ⊕ Fin t) (Fin r) K) (g g' : GL (Fin r) K) (z z' : Matrix (Fin r ⊕ Fin t) (Fin r) O), x * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z).map (algebraMap O K) → x * (g' : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z').map (algebraMap O K) → ∀ (y : Matrix (Fin r ⊕ Fin t) (Fin r) K) (w : Matrix (Fin r ⊕ Fin t) (Fin r) O), y * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • w).map (algebraMap O K) → ∃ w' : Matrix (Fin r ⊕ Fin t) (Fin r) O, y * (g' : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • w').map (algebraMap O K) := by
  first | exact @GlobalTheory.ParahoricTranslate.translate_lattice_coset_subset | exact GlobalTheory.ParahoricTranslate.translate_lattice_coset_subset | (intros; apply GlobalTheory.ParahoricTranslate.translate_lattice_coset_subset <;> assumption)
end

section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

theorem _root_.GlobalTheory.T.lattice_coset_translate_mem_of_cover : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ (N : ℕ) (x : Matrix (Fin r ⊕ Fin t) (Fin r) K) (g : GL (Fin r) K) (z₀ : Matrix (Fin r ⊕ Fin t) (Fin r) O), x * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z₀).map (algebraMap O K) → (∀ z : Matrix (Fin r ⊕ Fin t) (Fin r) O, ∃ (g' : GL (Fin r) K) (z' : Matrix (Fin r ⊕ Fin t) (Fin r) O), (x + (ϖ ^ N • z).map (algebraMap O K)) * (g' : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z').map (algebraMap O K)) → ∀ z : Matrix (Fin r ⊕ Fin t) (Fin r) O, ∃ z' : Matrix (Fin r ⊕ Fin t) (Fin r) O, (x + (ϖ ^ N • z).map (algebraMap O K)) * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z').map (algebraMap O K) := by
  first | exact @GlobalTheory.coset_translate_mem_of_cover | exact GlobalTheory.coset_translate_mem_of_cover | (intros; apply GlobalTheory.coset_translate_mem_of_cover <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_isUnit_matrix_of_pow_smul_span_invert : ∀ (S EE W RW Y : Type) [CommRing S] [CommRing EE] [CommRing W] [CommRing RW] [AddCommGroup Y] [Module RW Y] (a : S →+* EE) (ι : EE →+* RW) (c : W →+* RW) (ψ : S →+* W) (Q : S), Function.Injective ι → (∀ s, ι (a s) = c (ψ s)) → IsUnit (a Q) → ∀ (q : ℕ) (x z : Fin q → Y), (∀ w : Fin q → W, ∑ i, c (w i) • x i = 0 → w = 0) → (∀ j, ∃ (k : ℕ) (s : Fin q → S), c (ψ Q) ^ k • z j = ∑ i, c (ψ (s i)) • x i) → (∀ i, ∃ (k : ℕ) (s : Fin q → S), c (ψ Q) ^ k • x i = ∑ j, c (ψ (s j)) • z j) → ∃ A : Matrix (Fin q) (Fin q) EE, IsUnit A ∧ ∀ j, z j = ∑ i, ι (A i j) • x i := by
  first | exact @GlobalTheory.exists_isUnit_matrix_of_pow_smul_span | exact GlobalTheory.exists_isUnit_matrix_of_pow_smul_span | (intros; apply GlobalTheory.exists_isUnit_matrix_of_pow_smul_span <;> assumption)
end

section


theorem _root_.GlobalTheory.T.frobenius_equation_of_twisted_cocycle_defect : ∀ (R : Type) [CommRing R] (φ σ : R →+* R) (d N k : ℕ) (lr e e₀ : R) (Q Q' B B' A₀ A₀' ε : Matrix (Fin d) (Fin d) R), (∀ x : R, lr * x = 0 → x = 0) → (∃ v : Rˣ, e = lr * v) → (∃ v : Rˣ, e₀ = lr * v) → (∀ x, φ (σ x) = σ (φ x)) → φ lr = lr → σ lr = lr → σ e₀ = e₀ → A₀.map σ = A₀ → Q * Q' = lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R) → B * B' = e ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) R) → A₀ * A₀' = e₀ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) R) → e ^ N • (Q * A₀) = e₀ ^ N • (B * Q.map φ) → e ^ N • (ε * B.map σ) = σ e ^ N • (B * ε.map φ) → e₀ ^ (2 * N) • (Q' * ε * Q.map σ - lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R)) = A₀ * (Q' * ε * Q.map σ - lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R)).map φ * A₀' := by
  first | (exact @GlobalTheory.FrobeniusDefect.frobenius_defect_eq) | (exact GlobalTheory.FrobeniusDefect.frobenius_defect_eq) | (intros; apply GlobalTheory.FrobeniusDefect.frobenius_defect_eq  <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.transport_matrix_identity_injective_ringHom : ∀ {R L : Type} [CommRing R] [CommRing L] (ι : R →+* L), Function.Injective ι → ∀ (d N q : ℕ) (p : Fin d → ℕ) (ξ s : R) (Qm Q₁ : Matrix (Fin d) (Fin d) L) (X B c V : Matrix (Fin d) (Fin d) R), ι s ^ N • Qm = (X * B).map ι → (∀ i j, ι ξ ^ q * Q₁ i j = ι (ξ ^ p j * V i j)) → Q₁ = Qm * c.map ι → ξ ^ q • (X * B * c) = s ^ N • (V * Matrix.diagonal (fun j => ξ ^ p j)) := by
  first | (exact @GlobalTheory.transport_matrix_identity_star_alg) | (exact GlobalTheory.transport_matrix_identity_star_alg) | (intros; apply GlobalTheory.transport_matrix_identity_star_alg  <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.pow_dvd_entries_of_mul_eq_diagonal_pow : ∀ {R : Type} [CommRing R] [IsDomain R] (d N N₀ q : ℕ) (p : Fin d → ℕ) (ξ : R) (A A' B B' c c' V₀ V₀' : Matrix (Fin d) (Fin d) R), ξ ≠ 0 → B * B' = 1 → c * c' = 1 → V₀ * V₀' = 1 → A * A' = ξ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) R) → ξ ^ q • (A * B * c) = ξ ^ N • (V₀ * Matrix.diagonal (fun j => ξ ^ p j)) → N₀ ≤ N → (∀ i, |(p i : ℤ) - q| ≤ N₀) → (∀ i j, ξ ^ (N - N₀) ∣ A i j) ∧ ∀ i j, ξ ^ (N - N₀) ∣ A' i j := by
  first | (exact @GlobalTheory.frobenius_matrix_comatrix_divisible) | (exact GlobalTheory.frobenius_matrix_comatrix_divisible) | (intros; apply GlobalTheory.frobenius_matrix_comatrix_divisible  <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_adapted_frame_of_isotropic_columns' : ∀ (E : Type) [Field E] (r : ℕ) (Y : Submodule E ((Fin r → E) × (Fin r → E))), Module.finrank E Y = r → ∀ (C : Matrix (Fin r) (Fin r) E × Matrix (Fin r) (Fin r) E), Submodule.span E (Set.range fun j => ((fun a => C.1 a j), (fun a => C.2 a j))) = Y → ∀ (s : ℕ) (I : Matrix (Fin r) (Fin s) E), LinearIndependent E I.transpose → (∀ j, ((fun a => I a j), (0 : Fin r → E)) ∈ Y) → ∃ (t : ℕ) (J : Matrix (Fin r) (Fin s) E) (K : Matrix (Fin r) (Fin t) E) (L : Matrix (Fin s) (Fin r) E) (M : Matrix (Fin t) (Fin r) E), C.1 * J = I ∧ C.2 * J = 0 ∧ L * J = 1 ∧ L * K = 0 ∧ M * J = 0 ∧ M * K = 1 ∧ J * L + K * M = 1 := by
  first | exact @GlobalTheory.exists_adapted_frame_of_isotropic_columns | exact GlobalTheory.exists_adapted_frame_of_isotropic_columns | (intros; apply GlobalTheory.exists_adapted_frame_of_isotropic_columns <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_invariant_matrix_lift_of_adic_complete : ∀ (G : Type) [Group G] (A : Type) [CommRing A] (π : A), IsAdicComplete (Ideal.span {π}) A → ∀ (σ : G → A →+* A), (∀ g h a, σ (g * h) a = σ g (σ h a)) → (∀ g, σ g π = π) → ∀ (r : ℕ) (M : G →* Matrix (Fin r) (Fin r) A), (∀ g h i j, σ g (M h i j) = M h i j) → ∀ (S : Set (Subgroup G)), (∀ N ∈ S, N.Normal ∧ Finite (G ⧸ N) ∧ ∃ τ : A, (∀ g ∈ N, σ g τ = τ) ∧ ∑ᶠ x : G ⧸ N, σ x.out τ = 1) → (∀ N ∈ S, ∀ k : ℕ, ∃ N' ∈ S, N' ≤ N ∧ ∀ g ∈ N', ∀ i j, π ^ k ∣ (M g - 1) i j) → ∀ (W₀ : Matrix (Fin r) (Fin r) A), (∃ N ∈ S, ∀ g ∈ N, W₀.map (σ g) = W₀) → (∀ g i j, π ∣ (M g * W₀.map (σ g) - W₀) i j) → ∃ W : Matrix (Fin r) (Fin r) A, (∀ i j, π ∣ (W - W₀) i j) ∧ ∀ g, M g * W.map (σ g) = W := by
  first | exact @GlobalTheory.InvariantLift.exists_invariant_lift | exact GlobalTheory.InvariantLift.exists_invariant_lift | (intros; apply GlobalTheory.InvariantLift.exists_invariant_lift <;> assumption)
end

section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

theorem _root_.GlobalTheory.T.exists_residue_first_block_factor_of_second : ∀ (O : Type) [CommRing O] [IsLocalRing O] (r t : ℕ) (U : Submodule O (Fin r ⊕ Fin t → O)) (a : Fin r → IsLocalRing.ResidueField O), (∀ u ∈ U, (∀ i, IsLocalRing.residue O (u (Sum.inr i)) = 0) → a ⬝ᵥ (fun i => IsLocalRing.residue O (u (Sum.inl i))) = 0) → ∀ g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O), (∀ v, a ⬝ᵥ v = 0 → g.mulVec v = v) → ∃ b : Matrix (Fin r) (Fin t) (IsLocalRing.ResidueField O), ∀ u ∈ U, g.mulVec (fun i => IsLocalRing.residue O (u (Sum.inl i))) + b.mulVec (fun i => IsLocalRing.residue O (u (Sum.inr i))) = (fun i => IsLocalRing.residue O (u (Sum.inl i))) := by
  first | exact @GlobalTheory.residue_top_factor_through_bottom | exact GlobalTheory.residue_top_factor_through_bottom | (intros; apply GlobalTheory.residue_top_factor_through_bottom <;> assumption)
end
