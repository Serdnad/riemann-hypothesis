module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle089
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle014
public import Mathlib.Analysis.Normed.Field.Instances
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LatExistsSat
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle004
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle002
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle149
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle150
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle151
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
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Filtration
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle111
import Mathlib.Analysis.Fourier.Notation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle147

@[expose] public section

section

open IsLocalRing

namespace GlobalTheory

theorem eq_pow_mul_unit_of_maximalIdeal_eq_span {V : Type} [CommRing V] [IsLocalRing V]
    [IsNoetherianRing V] (T : V) (hm : maximalIdeal V = Ideal.span {T}) (v : V) (hv : v ≠ 0) :
    ∃ (a : ℕ) (c : V), IsUnit c ∧ v = T ^ a * c := by
  apply GlobalTheory.Pat.unit_mul_pow_of_maximalIdeal_eq_span <;> assumption

theorem maximalIdeal_eq_span_map_of_fractions (V W : Type) [CommRing V] [IsLocalRing V]
    [IsNoetherianRing V] [CommRing W] [IsLocalRing W] (φ : V →+* W) (T : V)
    (hm : IsLocalRing.maximalIdeal V = Ideal.span {T})
    (hTm : φ T ∈ IsLocalRing.maximalIdeal W) (hTn : φ T ∈ nonZeroDivisors W)
    (hfrac : ∀ w : W, ∃ x z : V, φ z ∈ nonZeroDivisors W ∧ φ z * w = φ x) :
    IsLocalRing.maximalIdeal W = Ideal.span {φ T} := by
  have cancel : ∀ (n : ℕ) (y : W), φ T ^ n * y = 0 → y = 0 := fun n y h =>
    (mul_left_mem_nonZeroDivisors_eq_zero_iff (pow_mem hTn n)).mp h
  have surj : ∀ w : W, ∃ v : V, φ v = w := by
    intro w
    obtain ⟨x, z, hz, hzw⟩ := hfrac w
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [map_zero] at hz
      have h1 : (1 : W) = 0 :=
        (mul_left_mem_nonZeroDivisors_eq_zero_iff hz).mp (zero_mul 1)
      exact one_ne_zero h1
    by_cases hx : x = 0
    · refine ⟨0, ?_⟩
      rw [hx, map_zero] at hzw
      rw [map_zero, eq_comm]
      exact (mul_left_mem_nonZeroDivisors_eq_zero_iff hz).mp hzw
    obtain ⟨a, α, hα, rfl⟩ := eq_pow_mul_unit_of_maximalIdeal_eq_span T hm x hx
    obtain ⟨c, β, hβ, rfl⟩ := eq_pow_mul_unit_of_maximalIdeal_eq_span T hm z hz0
    obtain ⟨βi, hβi⟩ := hβ.exists_right_inv
    simp only [map_mul, map_pow] at hzw
    rcases le_or_gt c a with h | h
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
      refine ⟨βi * T ^ d * α, ?_⟩
      have h1 : φ β * w = φ T ^ d * φ α := by
        apply sub_eq_zero.mp
        apply cancel c
        linear_combination hzw
      have h2 : φ βi * φ β = 1 := by rw [← map_mul, mul_comm, hβi, map_one]
      calc φ (βi * T ^ d * α) = φ βi * (φ T ^ d * φ α) := by simp only [map_mul, map_pow]; ring
        _ = φ βi * (φ β * w) := by rw [h1]
        _ = w := by rw [← mul_assoc, h2, one_mul]
    · exfalso
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h
      have h1 : φ T ^ (d + 1) * φ β * w = φ α := by
        apply sub_eq_zero.mp
        apply cancel a
        linear_combination hzw
      have hmem : φ T ^ (d + 1) * φ β * w ∈ maximalIdeal W := by
        rw [mul_assoc]
        exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hTm _ (Nat.succ_pos d))
      rw [h1, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hmem
      exact hmem (hα.map φ)
  ext w
  constructor
  · intro hw
    obtain ⟨v, rfl⟩ := surj w
    have hv : v ∈ maximalIdeal V := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hw
      exact hw (hu.map φ)
    rw [hm] at hv
    obtain ⟨v', rfl⟩ := Ideal.mem_span_singleton'.mp hv
    rw [map_mul, Ideal.mem_span_singleton']
    exact ⟨φ v', rfl⟩
  · intro hw
    obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.mp hw
    exact Ideal.mul_mem_left _ _ hTm

end GlobalTheory
end

section

namespace GlobalTheory.RingOfIntegersNormBound

theorem norm_le_one_of_isIntegral {F : Type*} [NormedField F] [IsUltrametricDist F]
    {x : F} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  apply GlobalTheory.norm_le_one_of_isIntegral_int <;> assumption

theorem norm_map_ringOfIntegers_le_one {K : Type} [Field K] [NumberField K] {p : ℕ}
    [Fact (Nat.Prime p)] (f : K →+* ℂ_[p]) (c : NumberField.RingOfIntegers K) :
    ‖(f : K → ℂ_[p]) (↑c : K)‖ ≤ (1 : ℝ) :=
  norm_le_one_of_isIntegral (map_isIntegral_int f (NumberField.RingOfIntegers.isIntegral_coe c))

end GlobalTheory.RingOfIntegersNormBound
end

section

namespace GlobalTheory.NonzeroScalarMultipleMembership

theorem exists_ne_zero_smul_mem {K V : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    {L : Submodule (NumberField.RingOfIntegers K) V} {x : V}
    (hx : x ∈ Submodule.span K (L : Set V)) :
    ∃ a : NumberField.RingOfIntegers K, a ≠ 0 ∧ a • x ∈ L := by
  apply Formalism.L2.SG.Pf.LatEx.exists_smul_mem_of_mem_span <;> assumption

end GlobalTheory.NonzeroScalarMultipleMembership
end

section

open Polynomial
open scoped TensorProduct

namespace GlobalTheory.SepCentralizer

theorem exists_ne_zero_aeval_eq_zero {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (g : Module.End K V) (p : K[X]) (hp : Irreducible p)
    (hdvd : p ∣ g.charpoly) : ∃ w : V, w ≠ 0 ∧ aeval g p w = 0 := by
  apply Formalism.IrreducibleCountingLemmas.Z.exists_ne_zero_aeval_eq_zero <;> assumption

theorem exists_annihilator_eq {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (g : Module.End K V) (hs : g.charpoly.Separable) (d : K[X]) :
    d ∣ g.charpoly → ∃ e : V, aeval g d e = 0 ∧ ∀ q : K[X], aeval g q e = 0 → d ∣ q := by
  apply Formalism.IrreducibleCountingLemmas.Z.exists_annihilator_eq <;> assumption

theorem exists_cyclic {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (g : Module.End K V) (hs : g.charpoly.Separable) :
    ∃ e : V, ∀ v : V, ∃ q : K[X], aeval g q e = v := by
  obtain ⟨e, -, he⟩ := exists_annihilator_eq g hs g.charpoly dvd_rfl
  refine ⟨e, ?_⟩
  let φ : K[X] →ₗ[K] V := (LinearMap.applyₗ e) ∘ₗ (aeval g).toLinearMap
  have hφ : ∀ p, φ p = aeval g p e := fun p => rfl
  let ψ : degreeLT K (Module.finrank K V) →ₗ[K] V := φ ∘ₗ (degreeLT K (Module.finrank K V)).subtype
  have hinj : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro q hq
    have h1 : g.charpoly ∣ (q : K[X]) := he _ hq
    have h2 : (q : K[X]).degree < g.charpoly.degree := by
      rw [degree_eq_natDegree g.charpoly_monic.ne_zero, LinearMap.charpoly_natDegree]
      exact mem_degreeLT.1 q.2
    exact Subtype.ext (eq_zero_of_dvd_of_degree_lt h1 h2)
  have hfin : Module.finrank K (degreeLT K (Module.finrank K V)) = Module.finrank K V := by
    rw [(degreeLTEquiv K (Module.finrank K V)).finrank_eq, Module.finrank_fin_fun]
  have : FiniteDimensional K (degreeLT K (Module.finrank K V)) :=
    (degreeLTEquiv K (Module.finrank K V)).symm.finiteDimensional
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).1 hinj
  intro v
  obtain ⟨q, hq⟩ := hsurj v
  exact ⟨q, hq⟩

theorem exists_eq_aeval_of_commute {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (g c : Module.End K V) (hs : g.charpoly.Separable)
    (hc : c * g = g * c) : ∃ p : K[X], c = aeval g p := by
  obtain ⟨e, he⟩ := exists_cyclic g hs
  obtain ⟨p, hp⟩ := he (c e)
  refine ⟨p, LinearMap.ext fun v => ?_⟩
  obtain ⟨q, rfl⟩ := he v
  have hcq : Commute (aeval g q) c :=
    (Algebra.commute_of_mem_adjoin_singleton_of_commute (aeval_mem_adjoin_singleton K g) hc).symm
  rw [← Module.End.mul_apply, ← hcq.eq, Module.End.mul_apply, ← hp, ← Module.End.mul_apply,
    ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]

theorem eq_aeval_of_commute_of_separable : ∀ (k : Type) [Field k] (n : ℕ)
    (Γ C : Matrix (Fin n) (Fin n) k) (u r : k[X]),
    u * Γ.charpoly + r * derivative Γ.charpoly = 1 → C * Γ = Γ * C →
    ∃ g : k[X], C = aeval Γ g := by
  intro k _ n Γ C u r h hC
  let e := (Matrix.toLinAlgEquiv' (R := k) (n := Fin n))
  have hs : (e Γ).charpoly.Separable := by
    rw [show e Γ = Matrix.toLin' Γ from rfl, Matrix.charpoly_toLin']
    exact ⟨u, r, h⟩
  have hc : e C * e Γ = e Γ * e C := by
    rw [← map_mul, ← map_mul, hC]
  obtain ⟨p, hp⟩ := exists_eq_aeval_of_commute _ _ hs hc
  refine ⟨p, e.injective ?_⟩
  rw [hp]
  exact aeval_algHom_apply e.toAlgHom Γ p

end GlobalTheory.SepCentralizer
end

section

open scoped NNReal

theorem _root_.GlobalTheory.T.latticeDetRelation_of_lsmul_shift : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (ℓ : C), 0 < w ℓ → w ℓ < 1 → ∀ (p q : ℕ) (F : Submodule C (Fin (p + q) → C)) (X0 : Submodule w.valuationSubring (Fin (p + q) → C)) (L : Submodule w.valuationSubring ((Fin (p + q) → C) ⧸ F)) (M : Submodule w.valuationSubring (Fin (p + q) → C)) (y : ℝ) (d : w.valuationSubring), d ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.DetRel w ℓ F (X0.map (LinearMap.lsmul w.valuationSubring (Fin (p + q) → C) d)) L M y → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.DetRel w ℓ F X0 L M (y - ((p + q : ℕ) : ℝ) * GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.addVal w ℓ (d : C)) := by
  first | exact @GlobalTheory.detRel_of_detRel_lsmul | exact GlobalTheory.detRel_of_detRel_lsmul | (intros; apply GlobalTheory.detRel_of_detRel_lsmul <;> assumption)
end

section

open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace

theorem _root_.GlobalTheory.T.summable_lipschitzLatticeNormPowSummand : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : FractionalIdeal (𝓞 F)⁰ F), M ≠ 0 → ∀ (k : ℕ), 2 ≤ k → ∀ (z : (F →+* ℝ) → ℂ), (∀ τ, (z τ).im ≠ 0) → Summable (fun a : (M : Set F) => lhsTerm k z a) := by
  first | exact @GlobalTheory.LipschitzTR.summable_lhsTerm_ideal | exact GlobalTheory.LipschitzTR.summable_lhsTerm_ideal | (intros; apply GlobalTheory.LipschitzTR.summable_lhsTerm_ideal <;> assumption)
end

section

open scoped NNReal

theorem _root_.GlobalTheory.T.piEigenSublattice_free_eq_differentScaled : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (r : ℕ) (τ : S), Function.Injective a → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (W := fun _ => Fin r → C) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a r) τ = GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.flatLattice (r := r) a τ (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.diffGen a τ) := by
  first | exact @GlobalTheory.EigenSubFree.main | exact GlobalTheory.EigenSubFree.main | (intros; apply GlobalTheory.EigenSubFree.main <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

noncomputable section
namespace GlobalTheory.RingFacts

variable {O : Type} [CommRing O] {S : Type} [Fintype S] [DecidableEq S]

theorem monic_Q (a : S → O) : (∏ s, (X - Polynomial.C (a s)) : O[X]).Monic :=
  monic_prod_of_monic _ _ fun s _ => monic_X_sub_C (a s)

theorem lin_eq (a : S → O) (s : S) :
    lin a s = AdjoinRoot.mk (∏ s, (X - Polynomial.C (a s)) : O[X]) (X - Polynomial.C (a s)) := by
  simp [lin, AdjoinRoot.mk_X, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]

theorem cofac_eq (a : S → O) (τ : S) :
    cofac a τ = AdjoinRoot.mk (∏ s, (X - Polynomial.C (a s)) : O[X])
      (∏ s ∈ Finset.univ.erase τ, (X - Polynomial.C (a s))) := by
  rw [cofac, map_prod]
  exact Finset.prod_congr rfl fun s _ => lin_eq a s

theorem ev_mk (a : S → O) (τ : S) (f : O[X]) :
    ev a τ (AdjoinRoot.mk _ f) = f.eval (a τ) := by
  simp [ev]

theorem exists_lin_mul_of_ev_eq_zero (a : S → O) (τ : S) (r : RS a) (hr : ev a τ r = 0) :
    ∃ r', r = lin a τ * r' := by
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective r
  rw [ev_mk] at hr
  obtain ⟨h, hh⟩ := (Polynomial.dvd_iff_isRoot).2 hr
  exact ⟨AdjoinRoot.mk _ h, by rw [hh, map_mul, lin_eq]⟩

theorem eq_algebraMap_add_lin_mul (a : S → O) (τ : S) (r : RS a) :
    ∃ g, r = algebraMap O (RS a) (ev a τ r) + lin a τ * g := by
  obtain ⟨g, hg⟩ := exists_lin_mul_of_ev_eq_zero a τ (r - algebraMap O (RS a) (ev a τ r))
    (by rw [map_sub, AlgHom.commutes]; simp)
  exact ⟨g, by rw [← hg]; ring⟩

theorem lin_mul_cofac (a : S → O) (τ : S) : lin a τ * cofac a τ = 0 := by
  rw [cofac, Finset.mul_prod_erase _ _ (Finset.mem_univ τ), Finset.prod_congr rfl
    (fun s _ => lin_eq a s), ← map_prod]
  exact AdjoinRoot.mk_self

theorem ev_cofac (a : S → O) (τ : S) :
    ev a τ (cofac a τ) = ∏ s ∈ Finset.univ.erase τ, (a τ - a s) := by
  rw [cofac, map_prod]
  exact Finset.prod_congr rfl fun s _ => ev_lin a τ s

theorem eq_smul_cofac_of_lin_mul_eq_zero [IsDomain O] (a : S → O) (τ : S) (r : RS a)
    (hr : lin a τ * r = 0) : ∃ c : O, r = algebraMap O (RS a) c * cofac a τ := by
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective r
  rw [lin_eq, ← map_mul, AdjoinRoot.mk_eq_zero] at hr
  obtain ⟨g, hg⟩ := hr
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), mul_assoc] at hg
  have hf : f = (∏ s ∈ Finset.univ.erase τ, (X - Polynomial.C (a s))) * g :=
    mul_left_cancel₀ (X_sub_C_ne_zero (a τ)) hg
  obtain ⟨h, hh⟩ := eq_algebraMap_add_lin_mul a τ (AdjoinRoot.mk _ g)
  refine ⟨ev a τ (AdjoinRoot.mk _ g), ?_⟩
  have hc := lin_mul_cofac a τ
  calc AdjoinRoot.mk _ f = cofac a τ * AdjoinRoot.mk _ g := by rw [hf, map_mul, cofac_eq]
    _ = cofac a τ * (algebraMap O (RS a) (ev a τ (AdjoinRoot.mk _ g)) + lin a τ * h) := by
        rw [← hh]
    _ = algebraMap O (RS a) (ev a τ (AdjoinRoot.mk _ g)) * cofac a τ
        + (lin a τ * cofac a τ) * h := by ring
    _ = _ := by rw [hc]; simp

theorem ring_facts : ∀ (O : Type) [CommRing O] [IsDomain O] (S : Type) [Fintype S] [DecidableEq S]
    (a : S → O) (τ : S), Module.Free O (RS a) ∧ Module.Finite O (RS a) ∧
    lin a τ * cofac a τ = 0 ∧ ev a τ (cofac a τ) = ∏ s ∈ Finset.univ.erase τ, (a τ - a s) ∧
    (∀ r : RS a, ev a τ r = 0 → ∃ r', r = lin a τ * r') ∧
    (∃ g : RS a, cofac a τ = algebraMap O (RS a) (ev a τ (cofac a τ)) + lin a τ * g) ∧
    (∀ r : RS a, lin a τ * r = 0 → ∃ c : O, r = algebraMap O (RS a) c * cofac a τ) := by
  intro O _ _ S _ _ a τ
  let pb := AdjoinRoot.powerBasis' (monic_Q a)
  exact ⟨Module.Free.of_basis pb.basis, pb.finite, lin_mul_cofac a τ, ev_cofac a τ,
    exists_lin_mul_of_ev_eq_zero a τ, eq_algebraMap_add_lin_mul a τ (cofac a τ),
    eq_smul_cofac_of_lin_mul_eq_zero a τ⟩

end GlobalTheory.RingFacts
end
end

section

open NumberField
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.lipschitzConstant_inverseDifferent_eisenstein : ∀ (F : Type) [Field F] [NumberField F] (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (k : ℕ), 1 ≤ k →
    ((2 * (Real.pi : ℂ) * Complex.I) ^ (k * Module.finrank ℚ F))⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.lipConst k (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞) *
      (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm 𝔞 : ℂ) ^ (k - 1) = (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ^ k / (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F k : ℂ) := by
  first | exact @GlobalTheory.LipEisConst.lip_const_eis | exact GlobalTheory.LipEisConst.lip_const_eis | (intros; apply GlobalTheory.LipEisConst.lip_const_eis <;> assumption)
end

section

open NumberField
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.mem_traceDualSignedPositiveCone_iff_totallyPositive : ∀ (F : Type) [Field F] [NumberField F] (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (b : F), b ≠ 0 →
    ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, ∀ ν : F,
      ν ∈ GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.dualCone (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞) (fun τ => ((τ b : ℝ) : ℂ) * z τ) ↔
        (ν ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ∧ ∀ τ : F →+* ℝ, 0 < τ (ν * b)) := by
  first | exact @GlobalTheory.Div.LipschitzCone.cone_iff | exact GlobalTheory.Div.LipschitzCone.cone_iff | (intros; apply GlobalTheory.Div.LipschitzCone.cone_iff <;> assumption)
end

section

open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

theorem _root_.GlobalTheory.T.abs_norm_le_abs_norm_mul_div_absNorm_of_eisensteinIndexPair : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔞 𝔟 : Frac F) (p : QPair 𝔞 𝔟), |(Algebra.norm ℚ p.1.1 : ℝ)| ≤ |(Algebra.norm ℚ (p.1.1 * p.1.2) : ℝ)| / nrm 𝔟 := by
  first | exact @GlobalTheory.NormLe.main | exact GlobalTheory.NormLe.main | (intros; apply GlobalTheory.NormLe.main <;> assumption)
end

section

open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

theorem _root_.GlobalTheory.T.summable_exp_neg_trace_totallyPositive_fractionalIdeal : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (L : FractionalIdeal (𝓞 F)⁰ F) (δ : ℝ), 0 < δ → Summable (fun x : {x : F // x ∈ L ∧ ∀ τ : Emb F, 0 < τ x} => Real.exp (-δ * ∑ τ : Emb F, τ x.1)) := by
  first | exact @GlobalTheory.LatExpSum.summable_exp_neg_trace | exact GlobalTheory.LatExpSum.summable_exp_neg_trace | (intros; apply GlobalTheory.LatExpSum.summable_exp_neg_trace <;> assumption)
end
