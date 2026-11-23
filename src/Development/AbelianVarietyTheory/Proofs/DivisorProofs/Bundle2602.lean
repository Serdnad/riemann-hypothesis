module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle013
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
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
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle625

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PowerSeriesUniformiser

theorem span_C_eq_ker {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {ϖ : A}
    (hϖ : Irreducible ϖ) :
    Ideal.span {(PowerSeries.C ϖ : PowerSeries A)} =
      RingHom.ker (PowerSeries.map (IsLocalRing.residue A)) := by
  have hm : IsLocalRing.maximalIdeal A = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  ext f
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨g, rfl⟩
    ext n
    simp [PowerSeries.coeff_C_mul, hm, Ideal.mem_span_singleton']
  · intro hf
    have h : ∀ n, ∃ b : A, PowerSeries.coeff n f = ϖ * b := fun n => by
      have : IsLocalRing.residue A (PowerSeries.coeff n f) = 0 := by
        have := congrArg (PowerSeries.coeff n) hf
        simpa using this
      rw [IsLocalRing.residue_eq_zero_iff, hm, Ideal.mem_span_singleton] at this
      exact this
    choose b hb using h
    refine ⟨PowerSeries.mk b, ?_⟩
    ext n
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hb]

theorem span_C_isPrime {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {ϖ : A}
    (hϖ : Irreducible ϖ) : (Ideal.span {(PowerSeries.C ϖ : PowerSeries A)}).IsPrime := by
  rw [span_C_eq_ker hϖ]
  exact RingHom.ker_isPrime _

theorem isDiscreteValuationRing_atPrime_span {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] {π : R}
    (h0 : π ≠ 0) [(Ideal.span {π}).IsPrime] :
    IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {π})) := by
  have hm : IsLocalRing.maximalIdeal (Localization.AtPrime (Ideal.span {π})) =
      Ideal.span {algebraMap R _ π} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_singleton]
  have hinj : Function.Injective (algebraMap R (Localization.AtPrime (Ideal.span {π}))) :=
    IsLocalization.injective _ (Ideal.span {π}).primeCompl_le_nonZeroDivisors
  have hnf : ¬ IsField (Localization.AtPrime (Ideal.span {π})) := fun hf => by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hm, Ideal.span_singleton_eq_bot] at hf
    exact h0 (hinj (hf.trans (map_zero _).symm))
  have hp : (IsLocalRing.maximalIdeal (Localization.AtPrime (Ideal.span {π}))).IsPrincipal := ⟨_, hm⟩
  exact ((IsDiscreteValuationRing.TFAE _ hnf).out 1 5).2 hp

theorem main : ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (ϖ : A), Irreducible ϖ →
    ∃ _ : (Ideal.span {(PowerSeries.C ϖ : PowerSeries A)}).IsPrime,
      IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {(PowerSeries.C ϖ : PowerSeries A)})) := by
  intro A _ _ _ ϖ hϖ
  haveI := span_C_isPrime hϖ
  refine ⟨this, isDiscreteValuationRing_atPrime_span ?_⟩
  intro h
  exact hϖ.ne_zero (PowerSeries.C_injective (h.trans (map_zero _).symm))

end GlobalTheory.PowerSeriesUniformiser
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LineNorm
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv actR)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlatModel.Proj

theorem exists_dual {O κ : Type} [CommRing O] [Fintype κ] [DecidableEq κ] (b : Module.Basis κ ℤ O)
    (hd : Algebra.discr ℤ b ≠ 0) :
    ∃ c : κ → O, (∀ a k, a * c k = ∑ i, b.repr (a * b i) k • c i) ∧
      ∑ i, c i * b i = ((Algebra.discr ℤ b : ℤ) : O) := by
  set T := Algebra.traceMatrix ℤ b with hT
  have hd' : T.det ≠ 0 := hd
  have nd : ∀ x y : O, (∀ l, Algebra.trace ℤ O (x * b l) = Algebra.trace ℤ O (y * b l)) → x = y := by
    intro x y h
    rw [← sub_eq_zero]
    have h1 : Matrix.vecMul (b.repr (x - y)) T = 0 := by
      funext l
      have h2 : Algebra.trace ℤ O ((x - y) * b l) = 0 := by rw [sub_mul, map_sub, h, sub_self]

      rw [← b.sum_repr (x - y), Finset.sum_mul, map_sum] at h2
      simp only [smul_mul_assoc, map_smul, smul_eq_mul] at h2
      exact h2
    have h3 := Matrix.eq_zero_of_vecMul_eq_zero hd' h1
    apply b.repr.injective
    rw [map_zero]
    exact DFunLike.coe_injective h3
  let c : κ → O := fun i => ∑ j, T.adjugate i j • b j
  have hc : ∀ i k, Algebra.trace ℤ O (c i * b k) = if i = k then T.det else 0 := by
    intro i k
    have h1 := congrFun (congrFun (Matrix.adjugate_mul T) i) k
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, _root_.mul_one, mul_zero] at h1
    rw [← h1]

    simp only [c, Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, smul_eq_mul]
    rfl
  have hc2 : ∀ i x, Algebra.trace ℤ O (c i * x) = T.det * b.repr x i := by
    intro i x
    conv_lhs => rw [← b.sum_repr x]

    simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_smul, hc, smul_eq_mul, mul_ite, mul_zero]
    simp [mul_comm]
  refine ⟨c, fun a k => nd _ _ fun l => ?_, nd _ _ fun l => ?_⟩
  · rw [mul_comm a, _root_.mul_assoc, hc2]

    simp only [Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, hc, smul_eq_mul, mul_ite, mul_zero]
    simp [mul_comm]
  · set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_mul, map_sum, _root_.mul_assoc, hc2]
    rw [← zsmul_eq_mul, map_smul, Algebra.trace_eq_matrix_trace b, smul_eq_mul, Matrix.trace, ← Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, mul_comm]

section Lin

variable {O S M κ : Type} [CommRing O] [CommRing S] [AddCommGroup M] [Module S M] [Fintype κ]
  (ρ : O →+* Module.End S M) (σ : O →+* S) (b : Module.Basis κ ℤ O) (c : κ → O)

theorem eig_proj (hc : ∀ a k, a * c k = ∑ i, b.repr (a * b i) k • c i) (a : O) (v : M) :
    ρ a (∑ i, σ (c i) • ρ (b i) v) = σ a • ∑ i, σ (c i) • ρ (b i) v := by
  have h1 : ∀ i, ρ a (ρ (b i) v) = ∑ k, b.repr (a * b i) k • ρ (b k) v := fun i => by
    rw [← Module.End.mul_apply, ← map_mul]
    conv_lhs => rw [← b.sum_repr (a * b i)]

    simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply]

  simp only [map_sum, map_smul, h1, Finset.smul_sum, smul_smul, ← map_mul, hc, map_zsmul, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  rw [smul_comm, smul_assoc]

theorem proj_eig {d : ℤ} (hc : ∑ i, c i * b i = (d : O)) (v : M) (hv : ∀ a, ρ a v = σ a • v) :
    ∑ i, σ (c i) • ρ (b i) v = (d : S) • v := by

  simp only [hv, smul_smul, ← map_mul, ← Finset.sum_smul, ← map_sum, hc, map_intCast]

end Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X}

theorem eq_of_comb {S : Type} [CommRing S] {x : Sp S ⟶ X} {m : ℕ} (T : Fin m → TanM x t.G) {w : Fin m → S}
    {u : Sp (DualNumber S) ⟶ t.G.left} (h : IsCombAtG t x (fun i => (tv (T i)).left) w u) :
    u = (tv (∑ i, w i • T i)).left := by
  obtain ⟨y, hy, rfl⟩ := h
  obtain ⟨z, hz, e⟩ := (GlobalTheory.LieMet.isComb_iff T w _).2 rfl
  rw [← e]
  have : y = z := funext fun i => Over.OverMorphism.ext ((hy i).trans (hz i).symm)
  rw [this]

end GlobalTheory.FlatModel.Proj

end
end
