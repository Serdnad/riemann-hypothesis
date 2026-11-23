module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle061
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle099
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle059
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle060
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle057
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentHeckeSupport
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.TwistedIndependenceLemma.TwistedIndependence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCharacterExistsUnique
public import Formalism.FormalDegreeBessel.StatementDS
public import Formalism.RealPlaceAnalysis.Bundle003
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle100
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle101
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.RingTheory.Ideal.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConnectionOnDividedPowerBasis
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle082
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle084
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle001
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
import Mathlib.RingTheory.DividedPowers.Basic
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

noncomputable section

open NumberField

namespace GlobalTheory.CompanionTheory.MassCount

variable {F : Type} [Field F] [NumberField F]

theorem count_box [IsTotallyReal F] (N : ℕ) (hN : 0 < N) (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (B : ℝ) (hB : 0 ≤ B) :
    {x : F | x ≠ 0 ∧ (∃ y ∈ I, (y : F) = N * x) ∧ ∀ w : InfinitePlace F, w x ≤ B}.Finite ∧
    (({x : F | x ≠ 0 ∧ (∃ y ∈ I, (y : F) = N * x) ∧ ∀ w : InfinitePlace F, w x ≤ B}.ncard : ℕ) : ℝ) *
      (Ideal.absNorm I : ℝ) ≤ (4 * B * N) ^ Module.finrank ℚ F :=
  _root_.UpperTheory.Reformulated.B.GaloisBoundSecond.main N hN I hI B hB

theorem norm_theta_mul [IsTotallyReal F] (θ : ℝ →+* InfiniteAdeleRing F) (ε : ℝ) (x : F) (w : InfinitePlace F) :
    ‖(θ ε * algebraMap F (InfiniteAdeleRing F) x) w‖ = |ε| * w x := by
  have hw := IsTotallyReal.isReal w
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  let ev : InfiniteAdeleRing F →+* w.Completion := Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) w
  have h0 : ((e : w.Completion →+* ℝ).comp (ev.comp θ)) = RingHom.id ℝ := Subsingleton.elim _ _
  have h1 : e (ev (θ ε)) = ε := DFunLike.congr_fun h0 ε
  have hn : ∀ a : w.Completion, ‖a‖ = |e a| := by
    intro a
    rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply, ← Real.norm_eq_abs]
    exact ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) a).symm
  have h2 : (θ ε * algebraMap F (InfiniteAdeleRing F) x) w = ev (θ ε) * (algebraMap F (InfiniteAdeleRing F) x) w := rfl
  rw [h2, norm_mul, hn (ev (θ ε)), h1, InfiniteAdeleRing.algebraMap_apply, InfinitePlace.Completion.norm_coe]
  rfl

theorem countBd : PositivityTheory.Rg.Mass.CountBd := by
  intro F _ _ hF θ _ K hK N hN
  haveI := hF
  have hb : ∀ w : InfinitePlace F, ∃ c : ℝ, ∀ a ∈ K, ‖(a : InfiniteAdeleRing F) w‖ ≤ c := fun w =>
    hK.exists_bound_of_continuousOn (f := fun a : InfiniteAdeleRing F => a w)
      (continuous_apply w).continuousOn
  choose c hc using hb
  set R : ℝ := ∑ w, |c w| with hRdef
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hcR : ∀ w, c w ≤ R := fun w =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun w => |c w|) (fun _ _ => abs_nonneg _) (Finset.mem_univ w))
  refine ⟨(4 * R * N) ^ Module.finrank ℚ F, fun ε hε I hI => ?_⟩
  have hsub : {x : F | x ≠ 0 ∧ (∃ y ∈ I, (y : F) = N * x) ∧ θ ε * algebraMap F (InfiniteAdeleRing F) x ∈ K} ⊆
      {x : F | x ≠ 0 ∧ (∃ y ∈ I, (y : F) = N * x) ∧ ∀ w : InfinitePlace F, w x ≤ R / ε} := by
    rintro x ⟨hx, hy, hxK⟩
    refine ⟨hx, hy, fun w => ?_⟩
    have h := hc w _ hxK
    rw [norm_theta_mul, abs_of_pos hε] at h
    rw [le_div_iff₀ hε, mul_comm]
    exact h.trans (hcR w)
  obtain ⟨hfin, hcount⟩ := count_box N hN I hI (R / ε) (div_nonneg hR0 hε.le)
  refine ⟨hfin.subset hsub, ?_⟩
  have hI0 : (0 : ℝ) < Ideal.absNorm I := by
    have : Ideal.absNorm I ≠ 0 := fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)
    exact_mod_cast Nat.pos_of_ne_zero this
  have hle := Set.ncard_le_ncard hsub hfin
  rw [le_div_iff₀ hI0]
  have hle' := (mul_le_mul_of_nonneg_right (Nat.cast_le (α := ℝ).2 hle) hI0.le).trans hcount
  calc _ ≤ ε ^ Module.finrank ℚ F * (4 * (R / ε) * N) ^ Module.finrank ℚ F := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hle' (by positivity)
    _ = (4 * R * N) ^ Module.finrank ℚ F := by
        rw [← mul_pow]
        congr 1
        field_simp

end GlobalTheory.CompanionTheory.MassCount
end
end

section

open scoped TensorProduct
open IsLocalRing

namespace GlobalTheory.CompanionTheory.UnitNorm

noncomputable section

section Basics

variable {O O' R : Type} [CommRing O] [CommRing O'] [Algebra O O'] [CommRing R] [Algebra O R]

def tw (τ : O' ≃ₐ[O] O') (j : ℕ) : O' ⊗[O] R →ₐ[O] O' ⊗[O] R :=
  Algebra.TensorProduct.map ((τ ^ j : O' ≃ₐ[O] O').toAlgHom) (AlgHom.id O R)

def nrm (ℓ : ℕ) (τ : O' ≃ₐ[O] O') (s : O' ⊗[O] R) : O' ⊗[O] R :=
  ∏ j ∈ Finset.range ℓ, tw τ j s

abbrev inc : R →ₐ[O] O' ⊗[O] R := Algebra.TensorProduct.includeRight

theorem nrm_mul (ℓ : ℕ) (τ : O' ≃ₐ[O] O') (x y : O' ⊗[O] R) :
    nrm ℓ τ (x * y) = nrm ℓ τ x * nrm ℓ τ y := by
  simp only [GlobalTheory.CompanionTheory.UnitNorm.nrm, map_mul, Finset.prod_mul_distrib]

theorem nrm_one (ℓ : ℕ) (τ : O' ≃ₐ[O] O') : nrm ℓ τ (1 : O' ⊗[O] R) = 1 := by
  simp only [GlobalTheory.CompanionTheory.UnitNorm.nrm, map_one, Finset.prod_const_one]

theorem map_tw (τ : O' ≃ₐ[O] O') (j : ℕ) (s : O' ⊗[O] R) :
    Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id O R) (tw τ j s) = tw τ (j + 1) s := by
  induction s using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y =>
    simp only [GlobalTheory.CompanionTheory.UnitNorm.tw, Algebra.TensorProduct.map_tmul, AlgEquiv.coe_toAlgHom, AlgHom.coe_coe,
      AlgHom.id_apply, pow_succ', AlgEquiv.mul_apply]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem tw_period {ℓ : ℕ} {τ : O' ≃ₐ[O] O'} (hτ : τ ^ ℓ = 1) (s : O' ⊗[O] R) :
    tw τ ℓ s = tw τ 0 s := by
  simp only [GlobalTheory.CompanionTheory.UnitNorm.tw, hτ, pow_zero]

theorem nrm_fixed {ℓ : ℕ} {τ : O' ≃ₐ[O] O'} (hℓ : 0 < ℓ) (hτ : τ ^ ℓ = 1) (s : O' ⊗[O] R) :
    Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id O R) (nrm ℓ τ s) = nrm ℓ τ s := by
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  simp only [GlobalTheory.CompanionTheory.UnitNorm.nrm, map_prod, GlobalTheory.CompanionTheory.UnitNorm.map_tw]
  rw [Finset.prod_range_succ, Finset.prod_range_succ', GlobalTheory.CompanionTheory.UnitNorm.tw_period hτ]

theorem map_inc_map (A : Ideal O) :
    Ideal.map (inc : R →ₐ[O] O' ⊗[O] R) (Ideal.map (algebraMap O R) A) =
      Ideal.map (algebraMap O (O' ⊗[O] R)) A := by
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes]
    exact Ideal.mem_map_of_mem _ hx
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, ← AlgHom.commutes (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) x]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hx)

theorem tw_mem (τ : O' ≃ₐ[O] O') (j : ℕ) (A : Ideal O) {x : O' ⊗[O] R}
    (hx : x ∈ Ideal.map (algebraMap O (O' ⊗[O] R)) A) :
    tw τ j x ∈ Ideal.map (algebraMap O (O' ⊗[O] R)) A := by
  have h : Ideal.map (algebraMap O (O' ⊗[O] R)) A ≤
      Ideal.comap (GlobalTheory.CompanionTheory.UnitNorm.tw τ j) (Ideal.map (algebraMap O (O' ⊗[O] R)) A) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes]
    exact Ideal.mem_map_of_mem _ ha
  exact h hx

theorem nrm_sub_mem (ℓ : ℕ) (τ : O' ≃ₐ[O] O') (A : Ideal O) {x y : O' ⊗[O] R}
    (h : x - y ∈ Ideal.map (algebraMap O (O' ⊗[O] R)) A) :
    nrm ℓ τ x - nrm ℓ τ y ∈ Ideal.map (algebraMap O (O' ⊗[O] R)) A := by
  rw [← Ideal.Quotient.eq]
  simp only [GlobalTheory.CompanionTheory.UnitNorm.nrm, map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Ideal.Quotient.eq, ← map_sub]
  exact GlobalTheory.CompanionTheory.UnitNorm.tw_mem τ j A h

theorem step [Module.Finite O O'] [Module.Free O O'] [Nontrivial O'] {ℓ : ℕ} {τ : O' ≃ₐ[O] O'}
    (hℓ : 0 < ℓ) (hτ : τ ^ ℓ = 1)
    (hfixS : ∀ s : O' ⊗[O] R, Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id O R) s = s →
      s ∈ Set.range (inc : R →ₐ[O] O' ⊗[O] R))
    (a : O')
    (hcong : ∀ m : ℕ, 1 ≤ m → ∀ r ∈ (⊥ : Ideal R).jacobson ^ m,
      nrm ℓ τ (1 + a ⊗ₜ[O] r) - (inc : R →ₐ[O] O' ⊗[O] R) (1 + r) ∈
        Ideal.map (inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ (m + 1)))
    (u : R) (m : ℕ) (hm : 1 ≤ m) (P : (O' ⊗[O] R)ˣ)
    (h : (inc : R →ₐ[O] O' ⊗[O] R) u - nrm ℓ τ (P : O' ⊗[O] R) ∈
      Ideal.map (inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ m)) :
    ∃ P' : (O' ⊗[O] R)ˣ, (P' : O' ⊗[O] R) - (P : O' ⊗[O] R) ∈
        Ideal.map (inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ m) ∧
      (inc : R →ₐ[O] O' ⊗[O] R) u - nrm ℓ τ (P' : O' ⊗[O] R) ∈
        Ideal.map (inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ (m + 1)) := by
  have hfix_incR : ∀ x : R, Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id O R)
      ((GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) x) = (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) x := by
    intro x
    simp only [GlobalTheory.CompanionTheory.UnitNorm.inc, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul,
      map_one, AlgHom.id_apply]
  obtain ⟨r, hr⟩ := hfixS ((GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) u - GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ (P : O' ⊗[O] R)) (by
    rw [map_sub, hfix_incR, GlobalTheory.CompanionTheory.UnitNorm.nrm_fixed hℓ hτ])
  obtain ⟨v, hv⟩ := hfixS (GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ ((P⁻¹ : (O' ⊗[O] R)ˣ) : O' ⊗[O] R))
    (GlobalTheory.CompanionTheory.UnitNorm.nrm_fixed hℓ hτ _)
  have hrm : r ∈ (⊥ : Ideal R).jacobson ^ m := by
    have h' := h
    rw [← hr] at h'
    exact GlobalTheory.T.tensor_ideal_map_injective O O' R _ r h'
  have hvr : v * r ∈ (⊥ : Ideal R).jacobson ^ m := Ideal.mul_mem_left _ v hrm
  have hsplit : a ⊗ₜ[O] (v * r) = (a ⊗ₜ[O] (1 : R)) * (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) (v * r) := by
    simp only [GlobalTheory.CompanionTheory.UnitNorm.inc, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, one_mul]
  have hmem : a ⊗ₜ[O] (v * r) ∈
      Ideal.map (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ m) := by
    rw [hsplit]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hvr)
  have hJ : a ⊗ₜ[O] (v * r) ∈ Ideal.map (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) (⊥ : Ideal R).jacobson :=
    Ideal.map_mono (Ideal.pow_le_self (by omega)) hmem
  have hU : IsUnit (1 + a ⊗ₜ[O] (v * r)) :=
    GlobalTheory.T.isUnit_one_add_jacobson_tensor O O' R _ hJ
  have hPP : GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ (P : O' ⊗[O] R) *
      GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ ((P⁻¹ : (O' ⊗[O] R)ˣ) : O' ⊗[O] R) = 1 := by
    rw [← GlobalTheory.CompanionTheory.UnitNorm.nrm_mul, Units.mul_inv, GlobalTheory.CompanionTheory.UnitNorm.nrm_one]
  have hc' : (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) (1 + v * r) - GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ (1 + a ⊗ₜ[O] (v * r)) ∈
      Ideal.map (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ (m + 1)) := by
    have h'' := neg_mem (hcong m hm (v * r) hvr)
    rwa [neg_sub] at h''
  have key : (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) u -
        GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ (P : O' ⊗[O] R) * GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ (1 + a ⊗ₜ[O] (v * r)) =
      GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ (P : O' ⊗[O] R) *
        ((GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) (1 + v * r) - GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ (1 + a ⊗ₜ[O] (v * r))) := by
    rw [map_add (f := _), map_one, map_mul]
    linear_combination (-1 : O' ⊗[O] R) * hr +
      (-((GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) r * GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ (P : O' ⊗[O] R))) * hv +
      (-((GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) r)) * hPP
  refine ⟨P * hU.unit, ?_, ?_⟩
  · rw [Units.val_mul, IsUnit.unit_spec,
      show (P : O' ⊗[O] R) * (1 + a ⊗ₜ[O] (v * r)) - P = P * (a ⊗ₜ[O] (v * r)) by ring]
    exact Ideal.mul_mem_left _ _ hmem
  · rw [Units.val_mul, IsUnit.unit_spec, GlobalTheory.CompanionTheory.UnitNorm.nrm_mul, key]
    exact Ideal.mul_mem_left _ _ hc'

end Basics

theorem norm_units_surjective : PositivityTheory.Rg.Tf.Loc.N1 → PositivityTheory.Rg.Tf.Loc.N2 → PositivityTheory.Rg.Tf.Loc.N3 := by
  intro hInt hConj
  unfold PositivityTheory.Rg.Tf.Loc.N3
  intro O O' R _ _ _ _ _ _ _ _ _ _ _ _ ℓ τ hℓ hτ hfix hbasis r
  by_cases hO' : Nontrivial O'
  swap
  · haveI : Subsingleton O' := not_nontrivial_iff_subsingleton.mp hO'
    have h1 : (1 : O' ⊗[O] R) = 0 := by
      calc (1 : O' ⊗[O] R) = (1 : O') ⊗ₜ[O] (1 : R) := Algebra.TensorProduct.one_def
        _ = (0 : O') ⊗ₜ[O] (1 : R) := by rw [Subsingleton.elim (1 : O') 0]
        _ = 0 := by rw [TensorProduct.zero_tmul]
    haveI : Subsingleton (O' ⊗[O] R) := subsingleton_of_zero_eq_one h1.symm
    exact ⟨1, Subsingleton.elim _ _⟩
  haveI := hO'
  obtain ⟨hfixS, a, ha1, hcong⟩ := hConj O O' R ℓ τ hℓ hτ hfix hbasis
  obtain ⟨hle, N, hN⟩ := GlobalTheory.T.local_finite_algebra_jacobson_radical O R
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal O) (O' ⊗[O] R) :=
    GlobalTheory.T.finite_module_adic_complete O (O' ⊗[O] R)
  obtain ⟨P₁, hP₁⟩ :=
    GlobalTheory.T.cyclic_algebra_hilbert_ninety hInt O O' R ℓ τ hℓ hτ hfix hbasis ⟨a, ha1⟩ r
  have h2 : ∀ k : ℕ, Ideal.map (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ (N * k + 1)) ≤
      Ideal.map (algebraMap O (O' ⊗[O] R)) (IsLocalRing.maximalIdeal O ^ k) := by
    intro k
    rw [← GlobalTheory.CompanionTheory.UnitNorm.map_inc_map]
    refine Ideal.map_mono ?_
    rw [Ideal.map_pow]
    exact le_trans (Ideal.pow_le_pow_right (Nat.le_succ _))
      (by rw [pow_mul]; exact Ideal.pow_right_mono hN k)
  have h3 : Ideal.map (algebraMap O (O' ⊗[O] R)) (IsLocalRing.maximalIdeal O) ≤
      Ideal.map (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ 1) := by
    rw [← GlobalTheory.CompanionTheory.UnitNorm.map_inc_map, pow_one]
    exact Ideal.map_mono hle
  have h4 : ∀ x ∈ Ideal.map (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ 1),
      IsUnit (1 + x) := fun x hx =>
    GlobalTheory.T.isUnit_one_add_jacobson_tensor O O' R x (by rwa [pow_one] at hx)
  have h6 : (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) (r : R) - GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ (P₁ : O' ⊗[O] R) ∈
      Ideal.map (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ 1) := by
    rw [pow_one, ← neg_sub]
    exact neg_mem hP₁
  obtain ⟨L, hL⟩ := GlobalTheory.T.norm_map_congruence O (O' ⊗[O] R)
    (IsLocalRing.maximalIdeal O)
    (fun m => Ideal.map (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ m)) N
    (GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ) ((GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) (r : R)) P₁
    (fun m => Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ m))) h2 h3 h4
    (fun k x y hxy => GlobalTheory.CompanionTheory.UnitNorm.nrm_sub_mem ℓ τ _ hxy) h6
    (fun m hm P hP => GlobalTheory.CompanionTheory.UnitNorm.step hℓ hτ hfixS a hcong (r : R) m hm P hP)
  exact ⟨L, hL⟩

end

end GlobalTheory.CompanionTheory.UnitNorm
end

section


theorem _root_.GlobalTheory.T.unipotent_hecke_support : PositivityTheory.Rg.Tf.Loc.QuotientIntegralCompactOpen := by
  first | exact @GlobalTheory.CompanionTheory.QuotU.h2U | exact GlobalTheory.CompanionTheory.QuotU.h2U | (intros; apply GlobalTheory.CompanionTheory.QuotU.h2U <;> assumption)
end

section


theorem _root_.GlobalTheory.T.hecke_character_exists_unique : PositivityTheory.Lbc.HeckeExistsUnique := by
  first | exact @GlobalTheory.CompanionTheory.HeckeFixed.heckeExistsUnique | exact GlobalTheory.CompanionTheory.HeckeFixed.heckeExistsUnique | (intros; apply GlobalTheory.CompanionTheory.HeckeFixed.heckeExistsUnique <;> assumption)
end

section

namespace GlobalTheory.CompanionTheory.PairMult

theorem capelliPoly_neg {n : ℕ} (χ : Fin n → ℂ) (Y : ℂ) :
    Formalism.QuantumDeterminants.capP (fun a => -χ a) (-Y) = (-1 : ℂ) ^ n * Formalism.QuantumDeterminants.capP χ Y := by
  have h : ∀ s : Fin n, -Y + -χ s = (-1 : ℂ) * (Y + χ s) := fun s => by ring
  simp only [Formalism.QuantumDeterminants.capP, h, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end GlobalTheory.CompanionTheory.PairMult
end

section

open Formalism.REAL

noncomputable section

namespace GlobalTheory.CompanionTheory.CapelliAntipode

theorem unop_ofFn_prod {A : Type*} [Ring A] : ∀ {t : ℕ} (f : Fin t → Aᵐᵒᵖ),
    MulOpposite.unop (List.ofFn f).prod = (List.ofFn fun i => MulOpposite.unop (f i.rev)).prod
  | 0, f => by simp
  | t + 1, f => by
    rw [List.ofFn_succ, List.prod_cons, MulOpposite.unop_mul, unop_ofFn_prod (fun i => f i.succ),
      List.ofFn_succ' (fun i : Fin (t + 1) => MulOpposite.unop (f i.rev)), List.prod_concat]
    simp only [Fin.rev_last, Fin.rev_castSucc]

theorem ofFn_prod_neg {A : Type*} [Ring A] [Algebra ℂ A] : ∀ {t : ℕ} (g : Fin t → A),
    (List.ofFn fun k => -g k).prod = ((-1 : ℂ) ^ t) • (List.ofFn g).prod
  | 0, g => by simp
  | t + 1, g => by
    rw [List.ofFn_succ, List.prod_cons, ofFn_prod_neg (fun k => g k.succ), List.ofFn_succ (f := g),
      List.prod_cons, pow_succ, mul_comm, mul_smul, neg_mul, mul_smul_comm, neg_one_smul]

theorem Tm_op_neg {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (X : Fin n → Fin n → A) (w : ℂ)
    (i j : Fin n) :
    Tm (fun i j => MulOpposite.op (-X i j)) w i j = MulOpposite.op (-(Tm X (-w) i j)) := by
  unfold Tm
  by_cases h : i = j
  · simp [h, MulOpposite.algebraMap_apply, add_comm]
  · simp [h]

theorem arg_rev {t : ℕ} (v : ℂ) (j : Fin t) :
    -(v - (((Fin.rev j : Fin t) : ℕ) : ℂ)) = ((t : ℂ) - 1 - v) - ((j : ℕ) : ℂ) := by
  have hj := j.isLt
  rw [Fin.val_rev, Nat.cast_sub (by omega : (j : ℕ) + 1 ≤ t)]
  push_cast
  ring

theorem unop_term {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (X : Fin n → Fin n → A) (v : ℂ)
    (σ : Equiv.Perm (Fin n)) :
    MulOpposite.unop ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : Aᵐᵒᵖ) *
        (List.ofFn fun k : Fin n =>
          Tm (fun i j => MulOpposite.op (-X i j)) (v - ((k : ℕ) : ℂ)) (id (σ k)) (id k)).prod) =
      ((-1 : ℂ) ^ n) • ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A) *
        (List.ofFn fun j : Fin n =>
          Tm X (((n : ℂ) - 1 - v) - ((j : ℕ) : ℂ)) (σ j.rev) j.rev).prod) := by
  rw [MulOpposite.unop_mul, MulOpposite.unop_intCast, unop_ofFn_prod]
  simp only [Tm_op_neg, MulOpposite.unop_op, id, arg_rev]
  rw [ofFn_prod_neg, smul_mul_assoc, ← Int.cast_comm]

theorem qminor_id_rev {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (X : Fin n → Fin n → A) (w : ℂ) :
    qminor X id (id ∘ (Fin.revPerm : Equiv.Perm (Fin n))) w =
      (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤˣ) : ℤ) : A) *
        ∑ σ : Equiv.Perm (Fin n), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A) *
          (List.ofFn fun j : Fin n => Tm X (w - ((j : ℕ) : ℂ)) (σ j.rev) j.rev).prod := by
  unfold qminor
  rw [Finset.mul_sum]
  refine (Fintype.sum_equiv (Equiv.mulRight (Fin.revPerm : Equiv.Perm (Fin n))) _ _ (fun σ => ?_)).symm
  simp only [Equiv.coe_mulRight, Equiv.Perm.sign_mul, Equiv.Perm.mul_apply, Fin.revPerm_apply,
    Function.comp_apply, id, Units.val_mul, Int.cast_mul]
  rw [← mul_assoc, Int.cast_comm]

theorem unop_qdet_op_neg (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A)
    (hX : GlRel X) (v : ℂ) :
    MulOpposite.unop (qdet (fun i j => MulOpposite.op (-X i j)) v) =
      ((-1 : ℂ) ^ n) • qdet X ((n : ℂ) - 1 - v) := by
  have hs := quantumMinorColSkew_holds A n n X hX id id (Fin.revPerm : Equiv.Perm (Fin n)) ((n : ℂ) - 1 - v)
  rw [qminor_id_rev] at hs
  have hu : (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤˣ) : ℤ) : A) *
      (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤˣ) : ℤ) : A) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have h2 := congrArg (fun x => (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤˣ) : ℤ) : A) * x) hs
  simp only [← mul_assoc, hu, one_mul] at h2
  have h3 : qdet X ((n : ℂ) - 1 - v) = _ := h2.symm
  rw [h3]
  unfold qdet qminor
  rw [Finset.unop_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun σ _ => unop_term X v σ

end GlobalTheory.CompanionTheory.CapelliAntipode
end
end

section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix


theorem _root_.GlobalTheory.T.relative_norm_cm_absNorm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ t : 𝓞 E, algebraMap F E ((RingOfIntegers.norm F t : 𝓞 F) : F) = (t : E) * σ (t : E) ∧ Ideal.absNorm (Ideal.span {RingOfIntegers.norm F t}) = Ideal.absNorm (Ideal.span {t}) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.NormSig.norm_eq_mul_conj_and_absNorm | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.NormSig.norm_eq_mul_conj_and_absNorm | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.NormSig.norm_eq_mul_conj_and_absNorm <;> assumption)
end

section

open MeasureTheory Topology
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.disintegration_haar_base : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure] [ν.IsAddHaarMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (U W : Set V), IsOpen W → W ⊆ U → W.Nonempty → ∀ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν Set.univ fib → ∀ T : X → V → V, (∀ s, Measurable (T s)) → (∀ s, μ.map (T s) = μ) → (∀ s, ContinuousOn (T s) W) → (∀ s v, T s v ∈ W ↔ v ∈ W) → (∀ s, ∀ v ∈ W, T (-s) (T s v) = v) → (∀ s, ∀ v ∈ W, g (T s v) = g v + s) → ∀ b : X, fib b ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.SW.FibreShift.fib_ne_zero | exact GlobalTheory.CompanionTheory.SW.FibreShift.fib_ne_zero | (intros; apply GlobalTheory.CompanionTheory.SW.FibreShift.fib_ne_zero <;> assumption)
end

section

open MeasureTheory Topology

theorem _root_.GlobalTheory.T.measurable_embedding_of_injective_proper : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (W : Set V), IsOpen W → ∀ (B B' : Set X), IsOpen B → IsOpen B' → B' ⊆ B → ∀ fib fib' : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B ∩ W) ν B fib → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B' ∩ W) ν B' fib' → ∀ b ∈ B', fib' b = fib b := by
  first | exact @GlobalTheory.CompanionTheory.SW.FibreUniq.fibreFamily_eq_inter | exact GlobalTheory.CompanionTheory.SW.FibreUniq.fibreFamily_eq_inter | (intros; apply GlobalTheory.CompanionTheory.SW.FibreUniq.fibreFamily_eq_inter <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

theorem _root_.GlobalTheory.T.connection_on_divided_power_basis : ∀ {B M : Type} [CommRing B] [AddCommGroup M] [Module B M] (e : Module.Basis ℕ B M) (I : ℕ → Ideal B) (p : ℕ) (q : B) (ν : ℕ → B) (D : M →ₗ[B] M), p ≠ 0 → IsNilpotent (p : B) → IsNilpotent (q - 1) → (∀ a c, I a * I c ≤ I (a + c)) → (∀ a c, a ≤ c → I c ≤ I a) → ν 1 = 1 → (∀ m, ν (m + 1) ∈ I m) → (∀ m, 2 ≤ m → IsNilpotent (ν m)) → (∃ N, ∀ m, N ≤ m → ν m = 0) → (∀ k, D (e k) = (∑ i ∈ Finset.range k, q ^ i) • e k + ∑ m ∈ Finset.range k, (ν (m + 1) * q ^ (k - (m + 1))) • e (k - (m + 1))) → (∀ z, D z = 0 → ∃ c : B, z = c • e 0) ∧ ∀ (r : ℕ) (z : M), (∀ k, e.repr z k ∈ I (r - k)) → ∃ y, (∀ k, e.repr y k ∈ I (r + 1 - k)) ∧ D y = z := by
  first | exact @GlobalTheory.CompanionTheory.QDerivative.ker_and_surjective | exact GlobalTheory.CompanionTheory.QDerivative.ker_and_surjective | (intros; apply GlobalTheory.CompanionTheory.QDerivative.ker_and_surjective <;> assumption)
end
