module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.DiscreteValuationRing
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle012
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.WittVector.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Regular.RegularSequence
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle817
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle815
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle816
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
public import Mathlib.RingTheory.WittVector.Teichmuller
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import Mathlib.CategoryTheory.Preadditive.EndoFunctor
import Mathlib.RingTheory.Bialgebra.Basic
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfK
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle387
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle788

@[expose] public section

section

open IsLocalRing

theorem _root_.GlobalTheory.T.exists_finite_extension_complete_dvr_padicAlgCl : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (κ : FractionRing V →+* PadicAlgCl p), (∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) → (∀ q : ℚ_[p], algebraMap ℚ_[p] (PadicAlgCl p) q ∈ κ.range) → ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] (y₀ : R →+* PadicAlgCl p), ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : IsAdicComplete (maximalIdeal W) W) (_ : CharZero W) (fV : V →+* W) (fK : FractionRing V →+* FractionRing W) (κ' : FractionRing W →+* PadicAlgCl p), Function.Injective fV ∧ IsLocalHom fV ∧ fV.Finite ∧ (∀ a, fK (algebraMap V _ a) = algebraMap W _ (fV a)) ∧ κ'.comp fK = κ ∧ (∀ x, ‖κ' x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W))) ∧ ∀ a, y₀ a ∈ κ'.range := by
  first | exact @GlobalTheory.DvrFinExt.exists_finite_extension | exact GlobalTheory.DvrFinExt.exists_finite_extension | (intros; apply GlobalTheory.DvrFinExt.exists_finite_extension <;> assumption)
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu.ColenDet

theorem map_eq_unit_mul_pow {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p]
    (ψ : ℤ_[p] →+* WittVector p k) {x : ℤ_[p]} (hx : x ≠ 0) :
    ψ x = ψ (PadicInt.unitCoeff hx : ℤ_[p]) * (p : WittVector p k) ^ x.valuation := by
  conv_lhs => rw [PadicInt.unitCoeff_spec hx]
  rw [map_mul, map_pow, map_natCast]

theorem addVal_map {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]
    (ψ : ℤ_[p] →+* WittVector p k) {x : ℤ_[p]} (hx : x ≠ 0) :
    IsDiscreteValuationRing.addVal (WittVector p k) (ψ x) = (x.valuation : ℕ∞) := by
  rw [map_eq_unit_mul_pow ψ hx, AddValuation.map_mul, AddValuation.map_pow,
    IsDiscreteValuationRing.addVal_uniformizer (WittVector.irreducible p),
    (IsDiscreteValuationRing.addVal_eq_zero_iff).mpr ((PadicInt.unitCoeff hx).isUnit.map ψ)]
  simp

theorem colength_det : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (N : Type) [AddCommGroup N] [Module (WittVector p k) N] [Module.Free (WittVector p k) N] [Module.Finite (WittVector p k) N] (ψ : ℤ_[p] →+* (WittVector p k)) (u : N →ₗ[(WittVector p k)] N) (d : ℤ_[p]), LinearMap.det u = ψ d → (∀ e : ℕ, Module.length (WittVector p k) (N ⧸ LinearMap.range u) = e → ‖d‖ = (p : ℝ) ^ (-(e : ℤ))) ∧ (¬ Function.Injective u → d = 0) ∧ Function.Injective ψ := by
  intro p _ k _ _ _ N _ _ _ _ ψ u d hdet
  have hψ : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    have h1 := addVal_map ψ h0
    rw [hx, AddValuation.map_zero] at h1
    exact ENat.top_ne_coe _ h1
  have hlen := GlobalTheory.length_quot_range_eq_addVal_det u
  refine ⟨fun e he => ?_, fun hu => ?_, hψ⟩
  · rw [hlen, hdet] at he
    have hd : d ≠ 0 := by
      rintro rfl
      rw [map_zero, AddValuation.map_zero] at he
      exact ENat.top_ne_coe _ he
    rw [addVal_map ψ hd] at he
    have he' : d.valuation = e := by exact_mod_cast he
    rw [PadicInt.norm_eq_zpow_neg_valuation hd, he']
  · have h0 : LinearMap.det u = 0 := by
      by_contra h
      apply hu
      rwa [LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, LinearMap.ker_eq_bot] at h
    exact hψ (by rw [← hdet, h0, map_zero])

end GlobalTheory.Dieu.ColenDet
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem length_ge_finrank_of_semilinear_surj (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (N U : Type) [AddCommGroup N] [Module (WittVector p k) N] [AddCommGroup U]
    [Module k U] [Module.Finite k U] (e : (WittVector p k) ≃+* (WittVector p k)) (θ : N →+ U) :
    Function.Surjective θ → (∀ (a : (WittVector p k)) n, θ (e a • n) = WittVector.constantCoeff a • θ n) →
    ∀ L : Submodule (WittVector p k) N, ((∀ n ∈ L, θ n = 0) →
      (Module.finrank k U : ℕ∞) ≤ Module.length (WittVector p k) (N ⧸ L)) ∧
      ((∀ n, n ∈ L ↔ θ n = 0) → Module.length (WittVector p k) (N ⧸ L) = Module.finrank k U) := by
  intro hθ hsemi L
  let σ : WittVector p k →+* k := (WittVector.constantCoeff).comp e.symm.toRingHom
  have hσ : Function.Surjective σ := by
    intro x
    obtain ⟨a, ha⟩ : ∃ a : WittVector p k, WittVector.constantCoeff a = x :=
      ⟨WittVector.teichmuller p x, by simp⟩
    exact ⟨e a, by simp [σ, ha]⟩
  letI : Algebra (WittVector p k) k := σ.toAlgebra
  letI : Module (WittVector p k) U := Module.compHom U σ
  haveI : IsScalarTower (WittVector p k) k U :=
    ⟨fun a b u => by
      show (σ a * b) • u = σ a • (b • u)
      exact mul_smul _ _ _⟩
  have hlenU : Module.length (WittVector p k) U = Module.finrank k U := by
    rw [Module.length_eq_of_surjective (R := k) (S := WittVector p k) (M := U) hσ,
      Module.length_eq_finrank]
  let θl : N →ₗ[WittVector p k] U :=
    { toFun := θ
      map_add' := θ.map_add
      map_smul' := fun a n => by
        have h := hsemi (e.symm a) n
        rw [RingEquiv.apply_symm_apply] at h
        exact h }
  have hθl : Function.Surjective θl := hθ
  refine ⟨fun hL => ?_, fun hL => ?_⟩
  · have hle : L ≤ LinearMap.ker θl := fun n hn => hL n hn
    rw [← hlenU]
    exact Module.length_le_of_surjective (L.liftQ θl hle) (by
      intro u
      obtain ⟨n, rfl⟩ := hθl u
      exact ⟨Submodule.Quotient.mk n, rfl⟩)
  · have hK : L = LinearMap.ker θl := by
      ext n
      exact hL n
    rw [← hlenU, hK]
    exact (θl.quotKerEquivOfSurjective hθl).length_eq

end GlobalTheory.Dieu
end

section

open MvPolynomial

namespace GlobalTheory.UnifCorr

variable {R : Type} [CommRing R] {σ : Type}

theorem coeff_X_pow_mul_mem (I : Ideal R) (i : σ) (k : ℕ) (G : MvPolynomial σ R)
    (h : ∀ m, AddMonoidAlgebra.coeff G m ∈ I) : ∀ m, AddMonoidAlgebra.coeff ((X i : MvPolynomial σ R) ^ k * G) m ∈ I := by
  intro m
  rw [X_pow_eq_monomial, coeff_monomial_mul']
  split_ifs
  · exact I.mul_mem_left _ (h _)
  · exact I.zero_mem

theorem mem_of_coeff_mem (I : Ideal R) (K : Ideal (MvPolynomial σ R))
    (hC : ∀ a ∈ I, C a ∈ K) (G : MvPolynomial σ R) (h : ∀ m, AddMonoidAlgebra.coeff G m ∈ I) : G ∈ K := by
  rw [G.as_sum]
  refine K.sum_mem fun v _ => ?_
  rw [← mul_one (AddMonoidAlgebra.coeff G v), ← C_mul_monomial]
  exact K.mul_mem_right _ (hC _ (h v))

end GlobalTheory.UnifCorr

open GlobalTheory.UnifCorr in
theorem GlobalTheory.homogeneous_correction_next_level : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (n : ℕ) (K : ℕ → Ideal (MvPolynomial (Fin (n + 1)) R)), (∀ (e t : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → (∀ i, ∃ N : ℕ, (X i : MvPolynomial (Fin (n + 1)) R) ^ N * F ∈ K e) → F ∈ K e) → (∀ e, ∀ a ∈ I ^ (e + 1), C a ∈ K e) → (∀ (e t : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → F ∈ K e → ∀ i, ∃ (N : ℕ) (G : MvPolynomial (Fin (n + 1)) R), G.IsHomogeneous (t + N) ∧ (∀ m, AddMonoidAlgebra.coeff G m ∈ I ^ (e + 1)) ∧ (X i : MvPolynomial (Fin (n + 1)) R) ^ N * F - G ∈ K (e + 1)) → ∃ t₀ : ℕ, ∀ t, t₀ ≤ t → ∀ (e : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → F ∈ K e → ∃ G : MvPolynomial (Fin (n + 1)) R, G.IsHomogeneous t ∧ (∀ m, AddMonoidAlgebra.coeff G m ∈ I ^ (e + 1)) ∧ F - G ∈ K (e + 1) := by
  intro R _ _ I n K hsat hC hstep
  have hcoef : ∀ e (G : MvPolynomial (Fin (n + 1)) R), (∀ m, AddMonoidAlgebra.coeff G m ∈ I ^ (e + 1)) → G ∈ K e :=
    fun e G h => mem_of_coeff_mem (I ^ (e + 1)) (K e) (hC e) G h
  have hJ : ∀ (e t : ℕ) (a : R) (F : MvPolynomial (Fin (n + 1)) R), a ∈ I → F.IsHomogeneous t →
      (∀ m, AddMonoidAlgebra.coeff F m ∈ I ^ e) → F ∈ K e → C a * F ∈ K (e + 1) := by
    intro e t a F ha hF _ hFK
    have hCF : (C a * F).IsHomogeneous t := by
      have := (isHomogeneous_C (Fin (n + 1)) a).mul hF
      rwa [zero_add] at this
    apply hsat (e + 1) t (C a * F) hCF
    intro i
    obtain ⟨N, G, _, hGc, hk⟩ := hstep e t F hF hFK i
    refine ⟨N, ?_⟩
    have h1 : C a * G ∈ K (e + 1) := by
      apply hcoef (e + 1)
      intro m
      rw [coeff_C_mul]
      have := Ideal.mul_mem_mul ha (hGc m)
      rwa [← pow_succ'] at this
    have : (X i : MvPolynomial (Fin (n + 1)) R) ^ N * (C a * F) = C a * (X i ^ N * F - G) + C a * G := by ring
    rw [this]
    exact add_mem ((K (e + 1)).mul_mem_left _ hk) h1
  obtain ⟨d₀, hd₀⟩ := GlobalTheory.T.uniform_serre_sections_alt R I n K hJ
  refine ⟨d₀, fun t ht e F hF hFK => ?_⟩
  choose N G hG hGc hk using hstep e t F hF hFK
  obtain ⟨M, hNM⟩ : ∃ M, ∀ i, N i ≤ M :=
    ⟨∑ i, N i, fun i => Finset.single_le_sum (fun j _ => Nat.zero_le (N j)) (Finset.mem_univ i)⟩
  let G' : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R := fun i => X i ^ (M - N i) * G i
  have hXM : ∀ i, (X i : MvPolynomial (Fin (n + 1)) R) ^ M = X i ^ (M - N i) * X i ^ N i := fun i => by
    rw [← pow_add, Nat.sub_add_cancel (hNM i)]
  have hG'h : ∀ i, (G' i).IsHomogeneous (t + M) := fun i => by
    show (X i ^ (M - N i) * G i).IsHomogeneous (t + M)
    rw [show t + M = (M - N i) + (t + N i) by have := hNM i; omega]
    exact (isHomogeneous_X_pow i (M - N i)).mul (hG i)
  have hG'c : ∀ i m, AddMonoidAlgebra.coeff (G' i) m ∈ I ^ (e + 1) := fun i => coeff_X_pow_mul_mem _ i _ _ (hGc i)
  have hk' : ∀ i, (X i : MvPolynomial (Fin (n + 1)) R) ^ M * F - G' i ∈ K (e + 1) := fun i => by
    have : (X i : MvPolynomial (Fin (n + 1)) R) ^ M * F - G' i = X i ^ (M - N i) * (X i ^ N i * F - G i) := by
      simp only [G', hXM i]; ring
    rw [this]; exact (K (e + 1)).mul_mem_left _ (hk i)
  obtain ⟨G0, hG0, hG0c, hL⟩ := hd₀ t ht (e + 1) M G' hG'h hG'c (fun i j => ⟨0, by
    have : ((X i : MvPolynomial (Fin (n + 1)) R) * X j) ^ 0 * (X j ^ M * G' i - X i ^ M * G' j)
        = X i ^ M * (X j ^ M * F - G' j) - X j ^ M * (X i ^ M * F - G' i) := by ring
    rw [this]
    exact sub_mem ((K (e + 1)).mul_mem_left _ (hk' j)) ((K (e + 1)).mul_mem_left _ (hk' i))⟩)
  refine ⟨G0, hG0, hG0c, ?_⟩
  apply hsat (e + 1) t (F - G0) (hF.sub hG0)
  intro i
  obtain ⟨L, hLi⟩ := hL i
  refine ⟨L + M, ?_⟩
  have : (X i : MvPolynomial (Fin (n + 1)) R) ^ (L + M) * (F - G0)
      = X i ^ L * (X i ^ M * F - G' i) + X i ^ L * (G' i - X i ^ M * G0) := by ring
  rw [this]
  exact add_mem ((K (e + 1)).mul_mem_left _ (hk' i)) hLi
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.koszul_resolution_three_terms_exact : ∀ (O : Type) [CommRing O] (g : ℕ) (f : Fin g → O), RingTheory.Sequence.IsWeaklyRegular O (List.ofFn f) → ∃ (e₁ : (Fin g → O) →ₗ[O] O) (e₂ : (Fin (g.choose 2) → O) →ₗ[O] (Fin g → O)), Function.Exact e₁ (Ideal.span (Set.range f)).mkQ ∧ Function.Exact e₂ e₁ ∧ (∀ x, e₁ x ∈ Ideal.span (Set.range f)) ∧ ∀ x i, e₂ x i ∈ Ideal.span (Set.range f) := by
  first | exact @GlobalTheory.koszul_resolution_three_terms | exact GlobalTheory.koszul_resolution_three_terms | (intros; apply GlobalTheory.koszul_resolution_three_terms <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.smoothSection_cutoff_mul_holomorphic : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (la : La) (W : Set Y) (χ : Y → ℝ) (h : ι → Y → ℂ), IsOpen W → A.SmoothFn χ → tsupport χ ⊆ W → A.IsSecOn la W h → A.IsSSec la (fun i y => (χ y : ℂ) * h i y) := by
  first | exact @GlobalTheory.smooth_cutoff_mul_sec | exact GlobalTheory.smooth_cutoff_mul_sec | (intros; apply GlobalTheory.smooth_cutoff_mul_sec <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.leviAt_log_nsq_ratio_eq_leviAt_ph : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E : La) (U : Set Y) (β J : ι → Y → ℂ), IsOpen U → A.IsFrameOn (A.kap + E) U β → A.IsFrameOn A.kap U J → ∀ x ∈ U, ∀ i, x ∈ (A.chart i).source → ContDiffAt ℝ ∞ ((fun y => -Real.log (A.nsq (A.kap + E) β y) + Real.log (A.nsq A.kap J y)) ∘ (A.chart i).symm) (A.chart i x) ∧ ∀ f : Y → ℝ, ContDiffAt ℝ ∞ (f ∘ (A.chart i).symm) (A.chart i x) → ∀ ξ : Fin n → ℂ, A.leviAt i (fun y => (-Real.log (A.nsq (A.kap + E) β y) + Real.log (A.nsq A.kap J y)) + f y) x ξ = A.leviAt i (fun y => A.ph E i y + f y) x ξ := by
  first | exact @GlobalTheory.frameWeight_levi | exact GlobalTheory.frameWeight_levi | (intros; apply GlobalTheory.frameWeight_levi <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.ChartBallExt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def InOrbit (X : Data E r) (x : Frame X.Ψ r) (R : ℝ) (y : Frame X.Ψ r) : Prop :=
  ∃ z : V (nd X), ‖z‖ ≤ R ∧ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, y = lact γ (rmul (cpt X x z) b)


open Classical in
noncomputable def ext (X : Data E r) (x : Frame X.Ψ r) (R : ℝ) (η : V (nd X) → ℝ) (y : Frame X.Ψ r) : ℝ :=
  if h : InOrbit X x R y then η h.choose else 0

theorem uniq (X : Data E r) {x : Frame X.Ψ r} {R : ℝ} (ho : IsOrth X x)
    (hinj : ∀ γ ∈ X.Γ, ∀ z z' : V (nd X), ‖z‖ ≤ R → ‖z'‖ ≤ R → ∀ b ∈ Bor X.Ψ r,
      lact γ (cpt X x z) = rmul (cpt X x z') b → γ = 1)
    {γ γ' : GL (Fin r) E} (hγ : γ ∈ X.Γ) (hγ' : γ' ∈ X.Γ) {b b' : Frame X.Ψ r}
    (hb : b ∈ Bor X.Ψ r) (hb' : b' ∈ Bor X.Ψ r) {z z' : V (nd X)} (hz : ‖z‖ ≤ R) (hz' : ‖z'‖ ≤ R)
    (h : lact γ (rmul (cpt X x z) b) = lact γ' (rmul (cpt X x z') b')) : z = z' := by
  have h1 : lact (γ'⁻¹ * γ) (rmul (cpt X x z) b) = rmul (cpt X x z') b' := by
    rw [← IW.lact_lact, h, IW.lact_lact, inv_mul_cancel, IW.lact_one]
  have h2 : lact (γ'⁻¹ * γ) (cpt X x z) = rmul (cpt X x z') (IW.bmul X b' (IW.binv X b)) := by
    rw [← IW.rmul_rmul, ← h1, IW.lact_rmul, IW.rmul_binv X _ hb]
  have h3 := hinj _ (X.Γ.mul_mem (X.Γ.inv_mem hγ') hγ) z z' hz hz' _
    (IW.bmul_mem X hb' (IW.binv_mem X hb)) h2
  rw [h3, IW.lact_one] at h1
  exact (KU.cpt_inj X ho hb hb' h1).1

theorem ext_val (X : Data E r) {x : Frame X.Ψ r} {R : ℝ} (ho : IsOrth X x)
    (hinj : ∀ γ ∈ X.Γ, ∀ z z' : V (nd X), ‖z‖ ≤ R → ‖z'‖ ≤ R → ∀ b ∈ Bor X.Ψ r,
      lact γ (cpt X x z) = rmul (cpt X x z') b → γ = 1)
    (η : V (nd X) → ℝ) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    {z : V (nd X)} (hz : ‖z‖ ≤ R) : ext X x R η (lact γ (rmul (cpt X x z) b)) = η z := by
  have hP : InOrbit X x R (lact γ (rmul (cpt X x z) b)) := ⟨z, hz, γ, hγ, b, hb, rfl⟩
  unfold ext
  rw [dite_eq_left hP]
  obtain ⟨hz', γ', hγ', b', hb', he⟩ := hP.choose_spec
  rw [uniq X ho hinj hγ' hγ hb' hb hz' hz he.symm]

theorem ext_zero (X : Data E r) {x : Frame X.Ψ r} {R : ℝ} (η : V (nd X) → ℝ) {y : Frame X.Ψ r}
    (hy : ¬ InOrbit X x R y) : ext X x R η y = 0 := by
  unfold ext
  rw [dite_eq_right hy]

end GlobalTheory.ChartBallExt


open GlobalTheory.ChartBallExt in
theorem GlobalTheory.chartBall_extend_by_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (R : ℝ), IsOrth X x → (∀ z : V (nd X), ‖z‖ ≤ R → z ∈ OmF X x) → (∀ γ ∈ X.Γ, ∀ z z' : V (nd X), ‖z‖ ≤ R → ‖z'‖ ≤ R → ∀ b ∈ Bor X.Ψ r, lact γ (cpt X x z) = rmul (cpt X x z') b → γ = 1) → ∀ η : V (nd X) → ℝ, ∃ ψ : Frame X.Ψ r → ℝ, (∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, ∀ z : V (nd X), ‖z‖ ≤ R → ψ (lact γ (rmul (cpt X x z) b)) = η z) ∧ (∀ y, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ R ∧ y = lact γ (rmul (cpt X x z) b)) → ψ y = 0) ∧ (∀ γ ∈ X.Γ, ∀ y, ψ (lact γ y) = ψ y) ∧ (∀ y, ∀ b ∈ Bor X.Ψ r, ψ (rmul y b) = ψ y) := by
  intro E _ _ _ r X x R ho _ hinj η
  refine ⟨ext X x R η, ?_, ?_, ?_, ?_⟩
  · intro γ hγ b hb z hz
    exact ext_val X ho hinj η hγ hb hz
  · intro y hy
    refine ext_zero X η ?_
    rintro ⟨z, hz, γ, hγ, b, hb, e⟩
    exact hy ⟨γ, hγ, b, hb, z, hz, e⟩
  · intro γ hγ y
    by_cases hy : InOrbit X x R y
    · obtain ⟨z, hz, γ0, hγ0, b, hb, rfl⟩ := hy
      rw [IW.lact_lact, ext_val X ho hinj η (X.Γ.mul_mem hγ hγ0) hb hz, ext_val X ho hinj η hγ0 hb hz]
    · have hy' : ¬ InOrbit X x R (lact γ y) := by
        rintro ⟨z, hz, γ0, hγ0, b, hb, e⟩
        refine hy ⟨z, hz, γ⁻¹ * γ0, X.Γ.mul_mem (X.Γ.inv_mem hγ) hγ0, b, hb, ?_⟩
        rw [← IW.lact_lact, ← e, IW.lact_lact, inv_mul_cancel, IW.lact_one]
      rw [ext_zero X η hy, ext_zero X η hy']
  · intro y b hb
    by_cases hy : InOrbit X x R y
    · obtain ⟨z, hz, γ0, hγ0, b0, hb0, rfl⟩ := hy
      rw [← IW.lact_rmul, IW.rmul_rmul, ext_val X ho hinj η hγ0 (IW.bmul_mem X hb0 hb) hz,
        ext_val X ho hinj η hγ0 hb0 hz]
    · have hy' : ¬ InOrbit X x R (rmul y b) := by
        rintro ⟨z, hz, γ0, hγ0, b0, hb0, e⟩
        refine hy ⟨z, hz, γ0, hγ0, IW.bmul X b0 (IW.binv X b), IW.bmul_mem X hb0 (IW.binv_mem X hb), ?_⟩
        rw [← IW.rmul_rmul, IW.lact_rmul, ← e, IW.rmul_binv X y hb]
      rw [ext_zero X η hy, ext_zero X η hy']
end

section

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

theorem _root_.GlobalTheory.T.chartDensity_continuousAt_zero_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), IsOrth X x → ContinuousAt (densF X x) 0 ∧ densF X x 0 = 1 ∧ ∀ τ, (mat x τ).det ≠ 0 := by
  first | exact @GlobalTheory.DensOne.dens_one | exact GlobalTheory.DensOne.dens_one | (intros; apply GlobalTheory.DensOne.dens_one <;> assumption)
end

section

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

theorem _root_.GlobalTheory.T.leftMul_near_one_lu_split_small_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), IsOrth X x → ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∀ m : X.Ψ → Matrix (Fin r) (Fin r) ℂ, (∀ τ a b, ‖m τ a b - (1 : Matrix (Fin r) (Fin r) ℂ) a b‖ < ε) → ∃ z : V (nd X), ‖z‖ < δ ∧ ∃ b ∈ Bor X.Ψ r, X.lmulC m x = rmul (cpt X x z) b := by
  first | exact @GlobalTheory.LUNear.lmulC_split_near_one | exact GlobalTheory.LUNear.lmulC_split_near_one | (intros; apply GlobalTheory.LUNear.lmulC_split_near_one <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.lineBundleIso_pullback_pair_transfer : ∀ (X Y : Scheme.{0}) (Q₁ Q₂ : LB X) (m m' : Y ⟶ X), Q₁.IsLB → Q₂.IsLB → LBIso Q₁ Q₂ → LBIso (Q₁.pull m) (Q₁.pull m') → LBIso (Q₂.pull m) (Q₂.pull m') := by
  first | (exact @GlobalTheory.PullIsoCongr.isocongr) | (exact GlobalTheory.PullIsoCongr.isocongr) | (intros; apply GlobalTheory.PullIsoCongr.isocongr  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_groupScheme_baseChange_hom_of_grpPullback : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G A : Over S) [GrpObj G] [GrpObj A] (G' A' : Over S') [GrpObj G'] [GrpObj A'] (φG : G'.left ⟶ G.left) (φA : A'.left ⟶ A.left) (p : G ⟶ A), IsGrpPullback G' G f φG → IsGrpPullback A' A f φA → IsMonHom p → ∃ p' : G' ⟶ A', IsMonHom p' ∧ p'.left ≫ φA = φG ≫ p.left := by
  first | (exact @GlobalTheory.GrpBC.exists_baseChange_hom) | (exact GlobalTheory.GrpBC.exists_baseChange_hom) | (intros; apply GlobalTheory.GrpBC.exists_baseChange_hom  <;> assumption)
end
