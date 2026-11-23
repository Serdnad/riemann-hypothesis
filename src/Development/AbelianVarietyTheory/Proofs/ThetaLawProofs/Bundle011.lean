module

public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.DualLiftInjective
public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Smooth.Basic
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle017
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLaw
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.UnivChartLoc
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory

namespace DiffLin

open ReciprocityTheory.ChartRestriction.G.Chart (zR jetAug dualLift dualLift_zR fstD_comp_dualLift ker_jetAug_pow)

variable {R : Type} [CommRing R] {n : ℕ}

theorem fst_dualLift (t : Fin n → R) (y : Chart.JetR R (Fin n) 1) :
    (dualLift t y).fst = jetAug R (Fin n) 1 y :=
  AlgHom.congr_fun (fstD_comp_dualLift t) y

theorem snd_dualLift_sum {k : ℕ} (c : Fin k → R) (t : Fin k → Fin n → R) (y : Chart.JetR R (Fin n) 1) :
    (dualLift (∑ i, c i • t i) y).snd = ∑ i, c i * (dualLift (t i) y).snd := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h : ∀ s : Fin n → R,
        (dualLift s (Ideal.Quotient.mk _ (MvPolynomial.C a))).snd = 0 := fun s => by
      have := (dualLift s).commutes a
      exact (congrArg TrivSqZeroExt.snd this).trans rfl
    simp only [h, mul_zero, Finset.sum_const_zero]
  | add p q hp hq =>
    simp only [map_add (f := _), TrivSqZeroExt.snd_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p j hp =>
    have h : ∀ s : Fin n → R,
        (dualLift s (Ideal.Quotient.mk _ (p * MvPolynomial.X j))).snd =
          jetAug R (Fin n) 1 (Ideal.Quotient.mk _ p) * s j := fun s => by
      rw [map_mul, map_mul, dualLift_zR, DualNumber.snd_mul, fst_dualLift]
      simp
    simp only [h, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

theorem spMap_dualLift_surjective (t : Fin n → R) :
    Function.Surjective (spMap (dualLift t : Chart.JetR R (Fin n) 1 →+* DualNumber R)) := by
  intro p
  have hs : Function.Surjective (jetAug R (Fin n) 1 : Chart.JetR R (Fin n) 1 →+* R) := fun a =>
    ⟨algebraMap R _ a, (jetAug R (Fin n) 1).commutes a⟩
  have hp : (p : PrimeSpectrum (Chart.JetR R (Fin n) 1)) ∈
      Set.range (PrimeSpectrum.comap (jetAug R (Fin n) 1 : Chart.JetR R (Fin n) 1 →+* R)) := by
    rw [range_comap_of_surjective _ _ hs]
    intro a ha
    apply (PrimeSpectrum.isPrime p).mem_of_pow_mem (1 + 1)
    have : a ^ (1 + 1) ∈ (RingHom.ker (jetAug R (Fin n) 1)) ^ (1 + 1) := Ideal.pow_mem_pow ha _
    rw [ker_jetAug_pow, Ideal.mem_bot] at this
    rw [this]
    exact Ideal.zero_mem _
  obtain ⟨q, rfl⟩ := hp
  refine ⟨PrimeSpectrum.comap (TrivSqZeroExt.fstHom R R R).toRingHom q, ?_⟩
  refine PrimeSpectrum.ext (Ideal.ext fun y => ?_)
  change (dualLift t y).fst ∈ q.asIdeal ↔ jetAug R (Fin n) 1 y ∈ q.asIdeal
  rw [fst_dualLift]

theorem top_le_preimage_of_dualLift {X : Scheme.{0}} (x : Sp (Chart.JetR R (Fin n) 1) ⟶ X) (U : X.Opens)
    (t : Fin n → R)
    (h : ⊤ ≤ (spMap (dualLift t : Chart.JetR R (Fin n) 1 →+* DualNumber R) ≫ x) ⁻¹ᵁ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  intro p _
  obtain ⟨q, rfl⟩ := spMap_dualLift_surjective t p
  exact h (Set.mem_univ q)

open GlobalTheory.TangentOrigin in
theorem evalPt_of_eq {X : Scheme.{0}} (x : Sp (Chart.JetR R (Fin n) 1) ⟶ X) (U : X.Opens)
    (hx : ⊤ ≤ x ⁻¹ᵁ U) (t : Fin n → R) (v : Sp (DualNumber R) ⟶ X)
    (e : v = spMap (dualLift t : Chart.JetR R (Fin n) 1 →+* DualNumber R) ≫ x) (f : Γ(X, U)) :
    ∃ h : ⊤ ≤ v ⁻¹ᵁ U, evalPt v U h f = dualLift t (evalPt x U hx f) := by
  subst e
  exact ⟨fun p _ => hx (Set.mem_univ _), evalPt_spMap_comp _ x U hx _ f⟩

end DiffLin


open GlobalTheory.TangentOrigin DiffLin in
theorem isDiff_sum_smul_of_isLieComb :
    ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (g n : ℕ) (u : HolUnif A L g)
    (v : Fin n → (epsR ℂ ⟶ A)) (W : Fin n → Fin g → ℂ) (c : Fin n → ℂ) (w : epsR ℂ ⟶ A),
    (∀ i, IsTangent (v i)) → (∀ i, u.IsDiff (W i) (v i)) → IsLieComb c v w → u.IsDiff (∑ i, c i • W i) w := by
  intro A _ hA L g n u v W c w hv hd hc U h f
  have : Smooth A.hom := hA.smooth
  obtain ⟨m, x, hx⟩ := Chart.univChartLoc A
  have htan : ∀ i, Chart.IsTan (v i) := fun i => (Chart.isTan_iff _).mpr (hv i)
  obtain ⟨hw, e⟩ := Chart.prodPts_tan hx c v htan
  have ew : w.left = spMap (Chart.dualLift (∑ i, c i • Chart.tcoord hx (v i) (htan i)) :
      Chart.JetR ℂ (Fin m) 1 →+* DualNumber ℂ) ≫ (x 1).left := by
    rw [← e, (Chart.isLieComb_iff c v w).1 hc]
    exact congrArg CommaMorphism.left (Chart.tcoord_spec hx _ hw)
  have ev : ∀ i, (v i).left = spMap (Chart.dualLift (Chart.tcoord hx (v i) (htan i)) :
      Chart.JetR ℂ (Fin m) 1 →+* DualNumber ℂ) ≫ (x 1).left := fun i =>
    congrArg CommaMorphism.left (Chart.tcoord_spec hx _ (htan i))
  have hU : ⊤ ≤ (x 1).left ⁻¹ᵁ U := top_le_preimage_of_dualLift _ U _ (ew ▸ h)
  obtain ⟨h', e'⟩ := evalPt_of_eq (x 1).left U hU _ w.left ew f
  change (evalPt (R := DualNumber ℂ) w.left U h' f).snd = _

  rw [e', snd_dualLift_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨hi, ei⟩ := evalPt_of_eq (x 1).left U hU _ (v i).left (ev i) f
  rw [← ei, map_smul, smul_eq_mul]
  exact congrArg (c i * ·) (hd i U hi f)

end GlobalTheory
end
end

section

namespace GlobalTheory.CurveNorm

theorem exists_lift_of_isIntegral {k E E' : Type} [Field k] [IsAlgClosed k] [CommRing E]
    [CommRing E'] [Algebra k E] [Algebra k E'] [Algebra E E'] [IsScalarTower k E E']
    [Algebra.IsIntegral E E'] (hinj : Function.Injective (algebraMap E E')) (e : E →ₐ[k] k) :
    ∃ e' : E' →ₐ[k] k, e'.comp (IsScalarTower.toAlgHom k E E') = e := by
  have hsurj : Function.Surjective e := fun c => ⟨algebraMap k E c, by simp⟩
  haveI hp : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := E')
    (RingHom.ker e) ⊥ (by
      intro x hx
      have : x = 0 := hinj (by simpa using hx)
      simp [this])
  have key : ∀ x : E, algebraMap k (E' ⧸ Q) (e x) = Ideal.Quotient.mk Q (algebraMap E E' x) := by
    intro x
    have h1 : algebraMap k E (e x) - x ∈ RingHom.ker e := by simp [RingHom.mem_ker]
    rw [← hQc, Ideal.mem_comap, map_sub, ← Ideal.Quotient.eq, ← IsScalarTower.algebraMap_apply] at h1
    exact h1
  haveI : Algebra.IsIntegral k (E' ⧸ Q) := by
    constructor
    intro y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨p, hpm, hp0⟩ := Algebra.IsIntegral.isIntegral (R := E) y
    refine ⟨p.map (e : E →+* k), hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have : (algebraMap k (E' ⧸ Q)).comp (e : E →+* k)
        = (Ideal.Quotient.mk Q).comp (algebraMap E E') := RingHom.ext key
    rw [this, ← Polynomial.hom_eval₂, hp0, map_zero]
  have hbij : Function.Bijective (algebraMap k (E' ⧸ Q)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let φ : k ≃ₐ[k] (E' ⧸ Q) := AlgEquiv.ofBijective (Algebra.ofId k _) hbij
  refine ⟨(φ.symm : (E' ⧸ Q) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k Q), ?_⟩
  ext x
  apply φ.injective
  exact (φ.apply_symm_apply _).trans (key x).symm

theorem exists_smooth_normalisation (E : Type) [CommRing E] [IsDomain E] [Algebra ℂ E]
    [Algebra.FiniteType ℂ E] [Ring.DimensionLEOne E] (e : E →ₐ[ℂ] ℂ) :
    ∃ (E' : Type) (_ : CommRing E') (_ : IsDomain E') (_ : Algebra ℂ E') (ρ : E →ₐ[ℂ] E')
      (e' : E' →ₐ[ℂ] ℂ), Algebra.Smooth ℂ E' ∧ Function.Injective ρ ∧ e'.comp ρ = e := by
  let F := FractionRing E
  let E' : Type := integralClosure E F
  haveI : Module.Finite E E' := GlobalTheory.NormFin.finite_integralClosure_of_isAlgClosed ℂ E F
  letI : Algebra ℂ E' := ((algebraMap E E').comp (algebraMap ℂ E)).toAlgebra
  haveI : IsScalarTower ℂ E E' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.FiniteType ℂ E' := Algebra.FiniteType.trans (S := E) inferInstance inferInstance
  haveI : IsNoetherianRing E' := Algebra.FiniteType.isNoetherianRing ℂ E'
  haveI : Ring.DimensionLEOne E' := Ring.DimensionLEOne.integralClosure E F
  haveI : IsIntegrallyClosed E' := integralClosure.isIntegrallyClosedOfFiniteExtension F
  haveI : IsDedekindRing E' := ⟨⟩
  haveI : IsDedekindDomain E' := inferInstance
  have hinj : Function.Injective (algebraMap E E') := by
    intro x y h
    apply IsFractionRing.injective E F
    exact congrArg Subtype.val h
  obtain ⟨e', he'⟩ := exists_lift_of_isIntegral hinj e
  exact ⟨E', inferInstance, inferInstance, inferInstance, IsScalarTower.toAlgHom ℂ E E', e',
    GlobalTheory.DedekindSmooth.smooth_of_isDedekindDomain ℂ E', hinj, he'⟩

end GlobalTheory.CurveNorm
end
