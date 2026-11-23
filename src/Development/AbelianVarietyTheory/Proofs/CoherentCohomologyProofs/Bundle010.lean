module

public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.Smooth.Basic
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
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeRightExact
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.WeightAddLeOfMemSupportDividedContraction
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem exists_isBaseChange_coker {R₀ R A₀ A M₁ M₂ N₁ N₂ : Type*} [CommRing R₀] [CommRing R]
    [Algebra R₀ R] [Ring A₀] [Ring A] [Algebra R₀ A₀] [Algebra R A] [SMul R₀ A]
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup N₁] [AddCommGroup N₂]
    [Module R₀ M₁] [Module R₀ M₂] [Module A₀ M₁] [Module A₀ M₂]
    [IsScalarTower R₀ A₀ M₁] [IsScalarTower R₀ A₀ M₂]
    [Module R₀ N₁] [Module R₀ N₂] [Module R N₁] [Module R N₂] [Module A N₁] [Module A N₂]
    [IsScalarTower R₀ R N₁] [IsScalarTower R₀ R N₂] [IsScalarTower R A N₁] [IsScalarTower R A N₂]
    [IsScalarTower R₀ A N₂]
    (f₀ : M₁ →ₗ[A₀] M₂) (f : N₁ →ₗ[A] N₂) (h₁ : M₁ →ₗ[R₀] N₁) (h₂ : M₂ →ₗ[R₀] N₂)
    (b₁ : IsBaseChange R h₁) (b₂ : IsBaseChange R h₂) (hcomm : ∀ x, h₂ (f₀ x) = f (h₁ x)) :
    ∃ ψ : (M₂ ⧸ LinearMap.range f₀) →ₗ[R₀] (N₂ ⧸ LinearMap.range f),
      IsBaseChange R ψ ∧ ∀ y, ψ (Submodule.Quotient.mk y) = Submodule.Quotient.mk (h₂ y) := by
  let q₀ : M₂ →ₗ[R₀] (M₂ ⧸ LinearMap.range f₀) := (LinearMap.range f₀).mkQ.restrictScalars R₀
  let q : N₂ →ₗ[R] (N₂ ⧸ LinearMap.range f) := (LinearMap.range f).mkQ.restrictScalars R
  have hq₀ : Function.Surjective q₀ := (LinearMap.range f₀).mkQ_surjective
  have hq : Function.Surjective q := (LinearMap.range f).mkQ_surjective
  have hex₀ : Function.Exact (f₀.restrictScalars R₀) q₀ := LinearMap.exact_map_mkQ_range f₀
  have hex : Function.Exact (f.restrictScalars R) q := LinearMap.exact_map_mkQ_range f
  have hker : LinearMap.ker q₀ ≤ LinearMap.ker ((q.restrictScalars R₀).comp h₂) := by
    intro y hy
    obtain ⟨x, rfl⟩ := (hex₀ y).1 hy
    exact (hex _).2 ⟨h₁ x, (hcomm x).symm⟩
  let ψ : (M₂ ⧸ LinearMap.range f₀) →ₗ[R₀] (N₂ ⧸ LinearMap.range f) :=
    ((LinearMap.ker q₀).liftQ _ hker).comp (q₀.quotKerEquivOfSurjective hq₀).symm.toLinearMap
  have hψ : ∀ y, ψ (q₀ y) = q (h₂ y) := by
    intro y
    have : (q₀.quotKerEquivOfSurjective hq₀).symm (q₀ y) = Submodule.Quotient.mk y := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [ψ, LinearMap.comp_apply, LinearEquiv.coe_coe, this]
    rfl
  exact ⟨ψ, IsBaseChange.of_right_exact R (f := f₀.restrictScalars R₀) (g := q₀)
    (f' := f.restrictScalars R) (g' := q) h₁ h₂ ψ (LinearMap.ext hcomm) (LinearMap.ext hψ)
    b₁ b₂ hex₀ hq₀ hex hq, hψ⟩

theorem isBaseChange_coker_matrix_mvPolynomial :
    ∀ (ι : Type) (R₀ R : Type) [CommRing R₀] [CommRing R] [Algebra R₀ R] (a b : ℕ)
      (Φ₀ : Matrix (Fin a) (Fin b) (MvPolynomial ι R₀))
      (Φ : Matrix (Fin a) (Fin b) (MvPolynomial ι R)),
      Φ₀.map (MvPolynomial.map (algebraMap R₀ R)) = Φ →
      ∃ ψ : ((Fin a → MvPolynomial ι R₀) ⧸ LinearMap.range Φ₀.mulVecLin) →ₗ[R₀]
          ((Fin a → MvPolynomial ι R) ⧸ LinearMap.range Φ.mulVecLin),
        IsBaseChange R ψ ∧ ∀ y : Fin a → MvPolynomial ι R₀,
          ψ (Submodule.Quotient.mk y) =
            Submodule.Quotient.mk fun l => MvPolynomial.map (algebraMap R₀ R) (y l) := by
  intro ι R₀ R _ _ _ a b Φ₀ Φ hΦ
  have hm : IsBaseChange R (mapAlgHom (σ := ι) (Algebra.ofId R₀ R)).toLinearMap :=
    IsBaseChange.of_equiv (algebraTensorAlgEquiv R₀ R).toLinearEquiv fun p => by
      simp [mapAlgHom_apply]
  refine exists_isBaseChange_coker Φ₀.mulVecLin Φ.mulVecLin _ _
    (IsBaseChange.finitePow (Fin b) hm) (IsBaseChange.finitePow (Fin a) hm) fun x => ?_
  funext l
  rw [← hΦ]
  exact RingHom.map_mulVec (MvPolynomial.map (algebraMap R₀ R)) Φ₀ x l

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem exists_sum_mul_of_mem_span_range_sq {S : Type} [CommRing S] {r : ℕ} (g : Fin r → S)
    (x : S) (hx : x ∈ Ideal.span (Set.range g) * Ideal.span (Set.range g)) :
    ∃ b : Fin r → Fin r → S, x = ∑ k, ∑ l, b k l * (g k * g l) := by

  have hx' : x ∈ Ideal.span (Set.range fun p : Fin r × Fin r => g p.1 * g p.2) := by
    open Pointwise in
    have hset : Set.range g * Set.range g =
        Set.range fun p : Fin r × Fin r => g p.1 * g p.2 := by
      ext y
      simp [Set.mem_mul]
    open Pointwise in
    rwa [Ideal.span_mul_span', hset] at hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun S).1 hx'
  refine ⟨fun k l => c (k, l), ?_⟩
  rw [← hc, Fintype.sum_prod_type]
  simp only [smul_eq_mul]

theorem exists_witnesses_of_formallySmooth_quotient :
    ∀ (ι : Type) [Fintype ι] (R : Type) [CommRing R] (r : ℕ) (g : Fin r → MvPolynomial ι R), Algebra.FormallySmooth R (MvPolynomial ι R ⧸ Ideal.span (Set.range g)) → ∃ (a : ι → Fin r → MvPolynomial ι R) (b : Fin r → Fin r → Fin r → MvPolynomial ι R), ∀ j, aeval (fun i => X i + ∑ k, a i k * g k) (g j) = ∑ k, ∑ l, b j k l * (g k * g l) := by
  intro ι _ R _ r g hs
  set I : Ideal (MvPolynomial ι R) := Ideal.span (Set.range g) with hI
  have hsurj : Function.Surjective (Ideal.Quotient.mkₐ R I) := Ideal.Quotient.mkₐ_surjective R I

  obtain ⟨σ, hσ⟩ := (Algebra.FormallySmooth.iff_split_surjection _ hsurj).1 hs
  have hK : RingHom.ker (Ideal.Quotient.mkₐ R I).toRingHom = I := by
    ext x
    rw [RingHom.mem_ker]
    exact Ideal.Quotient.eq_zero_iff_mem

  have hlift : ∀ i : ι, ∃ y : MvPolynomial ι R,
      Ideal.Quotient.mk _ y = σ (Ideal.Quotient.mkₐ R I (X i)) :=
    fun i => Ideal.Quotient.mk_surjective _
  choose y hy using hlift

  have hdiff : ∀ i, y i - X i ∈ I := by
    intro i
    have h1 := congrArg (Ideal.Quotient.mkₐ R I).kerSquareLift (hy i)
    rw [AlgHom.kerSquareLift_mk, ← AlgHom.comp_apply, hσ, AlgHom.id_apply] at h1
    exact Ideal.Quotient.eq.1 h1
  choose a ha using fun i => (Submodule.mem_span_range_iff_exists_fun (MvPolynomial ι R)).1 (hdiff i)
  have hy' : ∀ i, X i + ∑ k, a i k * g k = y i := by
    intro i
    have := ha i
    simp only [smul_eq_mul] at this
    rw [this]
    ring

  have hcomp : (Ideal.Quotient.mkₐ R _).comp
      (aeval fun i => X i + ∑ k, a i k * g k : MvPolynomial ι R →ₐ[R] MvPolynomial ι R) =
      σ.comp (Ideal.Quotient.mkₐ R I) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, aeval_X, hy', AlgHom.comp_apply, ← hy i]
    rfl

  have hmem : ∀ j, aeval (fun i => X i + ∑ k, a i k * g k) (g j) ∈ I * I := by
    intro j
    have hgj : Ideal.Quotient.mkₐ R I (g j) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨j, rfl⟩)
    have h2 := AlgHom.congr_fun hcomp (g j)
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hgj, map_zero, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem, hK, pow_two] at h2
    exact h2
  choose b hb using fun j => exists_sum_mul_of_mem_span_range_sq g _ (hmem j)
  exact ⟨a, b, hb⟩

end GlobalTheory
end
