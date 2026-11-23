module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Factorization
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
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis

@[expose] public section

section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.Mem

theorem exists_orthonormalBasis_adapted (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (I : Type) [Fintype I] [DecidableEq I] (p : I → Submodule ℂ E)
    (htop : (⨆ i, p i) = ⊤) (horth : ∀ i j, i ≠ j → p i ⟂ p j) :
    ∃ (b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E) (ty : Fin (Module.finrank ℂ E) → I),
      ∀ i, Submodule.span ℂ (b '' {σ | ty σ = i}) = p i := by
  classical
  have hV : OrthogonalFamily ℂ (fun i => p i) (fun i => (p i).subtypeₗᵢ) :=
    OrthogonalFamily.of_pairwise (fun i j h => horth i j h)
  have hint : DirectSum.IsInternal p :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top p).2 ⟨hV.independent, htop⟩
  let v : ∀ i, OrthonormalBasis (Fin (Module.finrank ℂ (p i))) ℂ (p i) :=
    fun i => stdOrthonormalBasis ℂ (p i)
  let c := hint.collectedOrthonormalBasis hV v
  have hc : ∀ a : (Σ i, Fin (Module.finrank ℂ (p i))), c a = (v a.1 a.2 : E) := by
    intro a
    simp [c, DirectSum.IsInternal.collectedOrthonormalBasis, DirectSum.IsInternal.collectedBasis_coe]
  have hcard : Fintype.card (Σ i, Fin (Module.finrank ℂ (p i))) = Module.finrank ℂ E :=
    (Module.finrank_eq_card_basis c.toBasis).symm
  let e : (Σ i, Fin (Module.finrank ℂ (p i))) ≃ Fin (Module.finrank ℂ E) :=
    Fintype.equivFinOfCardEq hcard
  refine ⟨c.reindex e, fun σ => (e.symm σ).1, fun i => ?_⟩
  have himg : (c.reindex e) '' {σ | (e.symm σ).1 = i}
      = (p i).subtype '' Set.range (v i).toBasis := by
    ext x
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      rw [OrthonormalBasis.reindex_apply, hc]
      simp only [Set.mem_ofPred_eq] at hσ
      generalize e.symm σ = a at hσ
      obtain ⟨j, k⟩ := a
      subst hσ
      exact ⟨v j k, ⟨k, by simp⟩, rfl⟩
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      refine ⟨e ⟨i, k⟩, by simp, ?_⟩
      rw [OrthonormalBasis.reindex_apply, Equiv.symm_apply_apply, hc]
      simp
  rw [himg, ← Submodule.map_span, Module.Basis.span_eq, Submodule.map_top, Submodule.range_subtype]

end GlobalTheory.Mem
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory

theorem semilinear_basis_image_indep_of_basis :
    ∀ (K : Type) [Field K] (e : K →+* ℂ) (V : Type) [AddCommGroup V] [Module K V]
      (W : Type) [AddCommGroup W] [Module ℂ W] (j : V →ₛₗ[e] W) (ι κ : Type)
      (b : Module.Basis ι K V) (b' : Module.Basis κ K V),
      (LinearIndependent ℂ (fun i => j (b i)) ∧
        Submodule.span ℂ (Set.range fun i => j (b i)) = ⊤) →
      LinearIndependent ℂ (fun i => j (b' i)) ∧
        Submodule.span ℂ (Set.range fun i => j (b' i)) = ⊤ := by
  intro K _ e V _ _ W _ _ j ι κ b b' ⟨hli, hsp⟩
  letI : Algebra K ℂ := e.toAlgebra
  letI : Module K W := Module.compHom W e
  haveI : IsScalarTower K ℂ W := ⟨fun k c w => by
    change (e k * c) • w = e k • c • w
    exact mul_smul _ _ _⟩
  let j' : V →ₗ[K] W :=
    { toFun := j
      map_add' := j.map_add
      map_smul' := fun k v => j.map_smulₛₗ k v }
  let L : ℂ ⊗[K] V →ₗ[ℂ] W := j'.liftBaseChange ℂ
  have hL : ∀ v : V, L (1 ⊗ₜ[K] v) = j v := fun v => by
    simp [L, j']
  let c : Module.Basis ι ℂ W := Module.Basis.mk hli hsp.ge
  let E : ℂ ⊗[K] V ≃ₗ[ℂ] W := (b.baseChange ℂ).equiv c (Equiv.refl ι)
  have hE : (E : ℂ ⊗[K] V →ₗ[ℂ] W) = L := by
    refine (b.baseChange ℂ).ext fun i => ?_
    rw [LinearEquiv.coe_coe]
    simp only [E, Module.Basis.equiv_apply, Equiv.refl_apply, c, Module.Basis.mk_apply]
    rw [Module.Basis.baseChange_apply, hL]
  have hb : (fun i => j (b' i)) = ⇑((b'.baseChange ℂ).map E) := by
    funext i
    rw [Module.Basis.map_apply, Module.Basis.baseChange_apply, ← hL, ← hE, LinearEquiv.coe_coe]
  rw [hb]
  exact ⟨Module.Basis.linearIndependent _, Module.Basis.span_eq _⟩

end GlobalTheory
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped nonZeroDivisors

namespace GlobalTheory

theorem fractionalIdeal_eq_of_count_eq {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, FractionalIdeal.count K v I = FractionalIdeal.count K v J) :
    I = J := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ]
  exact finprod_congr fun v => by rw [h v]

theorem submodule_eq_span_of_pow_eq_span_pow :
    ∀ (K : Type) [Field K] [NumberField K] (I : Submodule (𝓞 K) K) (β : K) (h : ℕ),
      0 < h → β ≠ 0 → I.FG → I ^ h = Submodule.span (𝓞 K) {β ^ h} →
      I = Submodule.span (𝓞 K) {β} := by
  intro K _ _ I β h hh hβ hfg hpow
  let J : FractionalIdeal (𝓞 K)⁰ K := ⟨I, FractionalIdeal.isFractional_of_fg hfg⟩
  have hJI : (J : Submodule (𝓞 K) K) = I := rfl
  have hB : FractionalIdeal.spanSingleton (𝓞 K)⁰ β ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr hβ
  have hp : J ^ h = FractionalIdeal.spanSingleton (𝓞 K)⁰ β ^ h := by
    rw [FractionalIdeal.spanSingleton_pow]
    apply FractionalIdeal.coeToSubmodule_injective
    simp only [FractionalIdeal.coe_pow, FractionalIdeal.coe_spanSingleton, hJI, hpow]
  have hJ : J ≠ 0 := by
    intro h0
    rw [h0, zero_pow hh.ne'] at hp
    exact pow_ne_zero h hB hp.symm
  have hJB : J = FractionalIdeal.spanSingleton (𝓞 K)⁰ β := by
    refine fractionalIdeal_eq_of_count_eq hJ hB fun v => ?_
    have := congrArg (FractionalIdeal.count K v) hp
    rw [FractionalIdeal.count_pow, FractionalIdeal.count_pow] at this
    exact mul_left_cancel₀ (by exact_mod_cast hh.ne') this
  rw [← hJI, hJB, FractionalIdeal.coe_spanSingleton]

end GlobalTheory
end
