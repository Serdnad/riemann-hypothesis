module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1686
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1689
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1690
public import Formalism.LocalRingCardinality.DataCD
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle035
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1691
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceHyperspecialStableLatticeEqMultiple
import Formalism.LocalToGlobal.IndefiniteReal.Bundle018
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1692
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1693
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle032
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernTopDens

variable {n : ℕ}

theorem coeff_aeval_C_mul_X (c : ℂ) (Q : MvPolynomial (Fin n × Fin n) ℂ) (d : Fin n × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (aeval (fun y => C c * X y) Q) d = c ^ (d.sum fun _ e => e) * AddMonoidAlgebra.coeff Q d := by
  induction Q using MvPolynomial.induction_on' with
  | monomial u a =>
    have : aeval (fun y => C c * X y) (monomial u a) = monomial u (c ^ (u.sum fun _ e => e) * a) := by
      rw [aeval_monomial, monomial_eq]
      simp only [mul_pow, Finsupp.prod_mul, algebraMap_eq]
      rw [Finsupp.prod, Finsupp.prod, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum, C_mul, map_prod]
      simp only [map_pow]
      ring
    rw [this, coeff_monomial, coeff_monomial]
    split_ifs with h
    · rw [h]
    · simp
  | add p q hp hq => rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

section Rev

variable {r : Type} [Fintype r] [DecidableEq r]

theorem charpolyRev_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (M : Matrix r r A) :
    (M.map f).charpolyRev = M.charpolyRev.map f := by
  unfold Matrix.charpolyRev
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j : 1
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem charpolyRev_smul {A : Type} [CommRing A] (c : A) (M : Matrix r r A) :
    (c • M).charpolyRev = M.charpolyRev.comp (Polynomial.C c * Polynomial.X) := by
  unfold Matrix.charpolyRev
  rw [← Polynomial.coe_compRingHom_apply, RingHom.map_det]
  congr 1
  ext i j : 1
  by_cases h : i = j <;> simp [Matrix.one_apply, h] <;> ring

theorem aeval_chernPoly (c : ℂ) (G : V n → Matrix r r ℂ) (v : V n) (k : ℕ) :
    aeval (fun y => C c * X y) (chernPoly G v k) = c ^ k • chernPoly G v k := by
  let ψ : MvPolynomial (Fin n × Fin n) ℂ →+* MvPolynomial (Fin n × Fin n) ℂ :=
    (aeval fun y => C c * X y : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n × Fin n) ℂ).toRingHom
  have e : ∀ p, aeval (fun y => C c * X y) p = ψ p := fun _ => rfl
  have hM : (-curvPoly G v).map ψ = (C c : MvPolynomial (Fin n × Fin n) ℂ) • (-curvPoly G v) := by
    refine Matrix.ext fun i j => ?_

    simp only [Matrix.map_apply, Matrix.neg_apply, Matrix.smul_apply, curvPoly, Matrix.of_apply, map_neg, map_sum,
    map_mul, smul_eq_mul, Finset.mul_sum, mul_neg, ← e, aeval_X, aeval_C, algebraMap_eq]
    refine congrArg _ (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_)
    ring
  unfold chernPoly
  rw [e, ← Polynomial.coeff_map, ← charpolyRev_map, hM, charpolyRev_smul, Polynomial.comp_C_mul_X_coeff, smul_eq_C_mul,
    map_pow, mul_comm]

end Rev

theorem topCoeff_aeval_C_mul_X (c : ℂ) (Q : MvPolynomial (Fin n × Fin n) ℂ) :
    topCoeff (aeval (fun y => C c * X y) Q) = c ^ n * topCoeff Q := by
  unfold topCoeff
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hdeg : (∑ a, Finsupp.single (a, w a) 1 : Fin n × Fin n →₀ ℕ).sum (fun _ e => e) = n := by
    change Finsupp.degree (∑ a, Finsupp.single (a, w a) 1 : Fin n × Fin n →₀ ℕ) = n

    simp [map_sum]
  rw [coeff_aeval_C_mul_X, hdeg]
  ring

theorem kappa_div : kappa ^ n / (Complex.I / 2) ^ n = (((Real.pi ^ n)⁻¹ : ℝ) : ℂ) := by
  rw [← div_pow, Complex.ofReal_inv, Complex.ofReal_pow, ← inv_pow]
  congr 1
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  rw [kappa]
  field_simp

end GlobalTheory.ChernTopDens


open GlobalTheory.ChernTopDens in
theorem GlobalTheory.ChernCalc.dens_chernAt_re (n : ℕ) (ι : Type) (m : ι → ℕ) (R : MvPolynomial (ι × ℕ) ℝ) (G : V n → Mat m ℂ)
    (v : V n) :
    (dens ((aeval (fun x : ι × ℕ => chernAt (fun u => G u x.1) v x.2) (R.map (algebraMap ℝ ℂ)) : Ev n) : Alt n)).re =
      chernTop R G v := by
  let Φ : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] Ev n := (aeval sym).comp (aeval fun y => C kappa * X y)
  have h1 : (fun x : ι × ℕ => chernAt (fun u => G u x.1) v x.2) =
      fun x => Φ (chernPoly (fun u => G u x.1) v x.2) := by
    funext x
    simp only [Φ, AlgHom.comp_apply, aeval_chernPoly, map_smul, chernAt]
  have h2 : aeval (fun x : ι × ℕ => chernAt (fun u => G u x.1) v x.2) (R.map (algebraMap ℝ ℂ)) =
      aeval sym (aeval (fun y => C kappa * X y)
        (aeval (fun x : ι × ℕ => chernPoly (fun u => G u x.1) v x.2) R)) := by
    rw [h1, ← comp_aeval, AlgHom.comp_apply, aeval_map_algebraMap]
    rfl
  rw [h2, GlobalTheory.T.topDegreeDensityComplexForm_aeval_dzWedgeDzbar, topCoeff_aeval_C_mul_X, mul_div_right_comm, kappa_div, Complex.re_ofReal_mul]
  rfl
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
namespace GlobalTheory.ChernCalc

noncomputable def linPoly {n : ℕ} (α : V n → V n → ℂ) : MvPolynomial (Fin n × Fin n) ℂ :=
  ∑ a, ∑ b, C (α (coordVec a) (coordVec b)) * X (a, b)

theorem linPoly_isHomogeneous {n : ℕ} (α : V n → V n → ℂ) : (linPoly α).IsHomogeneous 1 := by
  unfold linPoly
  refine IsHomogeneous.sum _ _ _ fun a _ => IsHomogeneous.sum _ _ _ fun b _ => ?_
  simpa using (isHomogeneous_C (Fin n × Fin n) (α (coordVec a) (coordVec b))).mul (isHomogeneous_X ℂ (a, b))

theorem aeval_sym_linPoly {n : ℕ} (α : V n → V n → ℂ) : aeval sym (linPoly α) = ofValues α := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [linPoly, ofValues, map_sum, Algebra.smul_def]

theorem degree_permMono {n : ℕ} (w : Equiv.Perm (Fin n)) :
    Finsupp.degree (∑ a, Finsupp.single (a, w a) 1 : Fin n × Fin n →₀ ℕ) = n := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]; simp [Finsupp.degree_single]

theorem topCoeff_eq_zero_of_isHomogeneous {n d : ℕ} {Q : MvPolynomial (Fin n × Fin n) ℂ} (hQ : Q.IsHomogeneous d)
    (hd : d ≠ n) : topCoeff Q = 0 := by
  unfold topCoeff
  refine Finset.sum_eq_zero fun w _ => ?_
  rw [hQ.coeff_eq_zero (by rw [degree_permMono]; exact fun h => hd h.symm), mul_zero]

theorem dens_aeval_ofValues_offDeg : ∀ (n : ℕ) (κ : Type) (α : κ → V n → V n → ℂ) (d : ℕ) (P : MvPolynomial κ ℝ),
    P.IsHomogeneous d → d ≠ n →
      dens ((aeval (fun i => ofValues (α i)) (P.map (algebraMap ℝ ℂ)) : Ev n) : Alt n) = 0 := by
  intro n κ α d P hP hd
  have h1 : (aeval (fun i => ofValues (α i)) (P.map (algebraMap ℝ ℂ)) : Ev n) =
      aeval sym (bind₁ (fun i => linPoly (α i)) (P.map (algebraMap ℝ ℂ))) := by
    rw [aeval_bind₁]; simp only [aeval_sym_linPoly]
  have hQ : (bind₁ (fun i => linPoly (α i)) (P.map (algebraMap ℝ ℂ))).IsHomogeneous d := by
    simpa only [one_mul, mul_one, MvPolynomial.bind₁] using
      (hP.map (algebraMap ℝ ℂ)).aeval (fun i => linPoly (α i)) fun i => linPoly_isHomogeneous (α i)
  rw [h1, GlobalTheory.T.topDegreeDensityComplexForm_aeval_dzWedgeDzbar, topCoeff_eq_zero_of_isHomogeneous hQ hd, zero_div]

end GlobalTheory.ChernCalc
end

section

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

theorem _root_.GlobalTheory.T.holAtlas_pullback_eq_chart_expression : ∀ (M M' : Type) [TopologicalSpace M] [TopologicalSpace M'] (n n' : ℕ) (A : HolAtlas M n) (A' : HolAtlas M' n')
    (f : M' → M) (α : A.Fld), A.IsHolo A' f → A.IsForm α →
    ∀ (x : A'.Pt) (i : A.ι) (h : f x.pt ∈ (A.e i).source),
      A.pullback A' f α x = pull (fderiv ℂ (A.e i ∘ f ∘ x.ch.symm) x.crd) (α ⟨(i, f x.pt), h⟩) := by
  first | exact @GlobalTheory.CxForm.pullback_eq_chart | exact GlobalTheory.CxForm.pullback_eq_chart | (intros; apply GlobalTheory.CxForm.pullback_eq_chart <;> assumption)
end

section

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

theorem _root_.GlobalTheory.T.isForm_one_add_mul_smul : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n), A.IsForm 1 ∧
    ∀ (c : ℂ) (α β : A.Fld), A.IsForm α → A.IsForm β → A.IsForm (α + β) ∧ A.IsForm (α * β) ∧ A.IsForm (c • α) := by
  first | exact @GlobalTheory.CxForm.HolAtlas.isForm_algebra | exact GlobalTheory.CxForm.HolAtlas.isForm_algebra | (intros; apply GlobalTheory.CxForm.HolAtlas.isForm_algebra <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.dbar_operator_local_calculus_complex_forms : ∀ (n : ℕ) (v : V n), (∀ α β : V n → Alt n, α =ᶠ[𝓝 v] β → dbarAt α v = dbarAt β v) ∧ (∀ (J : Type) (s : Finset J) (α : J → V n → Alt n), (∀ j ∈ s, ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (α j x) S) v) → dbarAt (fun x => ∑ j ∈ s, α j x) v = ∑ j ∈ s, dbarAt (α j) v) ∧ (∀ (c : ℂ) (α : V n → Alt n), (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (α x) S) v) → dbarAt (fun x => c • α x) v = c • dbarAt α v) ∧ (∀ γ : Alt n, dbarAt (fun _ => γ) v = 0) ∧ (∀ (w : V n → Ev n) (β : V n → Alt n), (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr ((w x : Alt n)) S) v) → (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (β x) S) v) → dbarAt (fun x => (w x : Alt n) * β x) v = dbarAt (fun x => (w x : Alt n)) v * β v + (w v : Alt n) * dbarAt β v) := by
  first | exact @GlobalTheory.CxForm.dbarAt_local_calculus | exact GlobalTheory.CxForm.dbarAt_local_calculus | (intros; apply GlobalTheory.CxForm.dbarAt_local_calculus <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder

namespace GlobalTheory.CxForm.IntegralSum

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

set_option autoImplicit false in
open Set Matrix MeasureTheory in
open scoped ComplexOrder in
variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : _root_.GlobalTheory.CxForm.HolAtlas M n) in
private theorem isForm_zero' : A.IsForm 0 := by
  constructor
  · intro i S
    unfold _root_.GlobalTheory.CxForm.HolAtlas.loc
    refine (contDiffOn_const (c := (0 : ℂ))).congr ?_
    intro v _
    split_ifs
    erw [Pi.zero_apply, map_zero, Finsupp.zero_apply]
  · intro x x' _
    exact (map_zero _).symm

set_option autoImplicit false in
open Set Matrix MeasureTheory in
open scoped ComplexOrder in
variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : _root_.GlobalTheory.CxForm.HolAtlas M n) in
variable [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] in
private theorem integral_zero_fld : A.integral 0 = 0 := by
  have h := A.integral_sub_of_isForm 0 0 (isForm_zero' A) (isForm_zero' A)
  simpa using h

set_option autoImplicit false in
open Set Matrix MeasureTheory in
open scoped ComplexOrder in
variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : _root_.GlobalTheory.CxForm.HolAtlas M n) in
private theorem isForm_add' {α β : A.Fld}
    (ha : A.IsForm α) (hb : A.IsForm β) :
    A.IsForm (α + β) := by
  constructor
  · intro i S
    have h1 := ha.smooth i S
    have h2 := hb.smooth i S
    unfold _root_.GlobalTheory.CxForm.HolAtlas.loc
    unfold _root_.GlobalTheory.CxForm.HolAtlas.loc at h1 h2
    refine (h1.add h2).congr ?_
    intro v hv
    simp only [dif_pos hv]
    erw [Pi.add_apply, map_add, Finsupp.add_apply]
  · intro x x' hx
    simp [ha.compat x x' hx, hb.compat x x' hx]

set_option autoImplicit false in
open Set Matrix MeasureTheory in
open scoped ComplexOrder in
variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : _root_.GlobalTheory.CxForm.HolAtlas M n) in
private theorem isForm_sub' {α β : A.Fld}
    (ha : A.IsForm α) (hb : A.IsForm β) :
    A.IsForm (α - β) := by
  constructor
  · intro i S
    have h1 := ha.smooth i S
    have h2 := hb.smooth i S
    unfold _root_.GlobalTheory.CxForm.HolAtlas.loc
    unfold _root_.GlobalTheory.CxForm.HolAtlas.loc at h1 h2
    refine (h1.sub h2).congr ?_
    intro v hv
    simp only [dif_pos hv]
    erw [Pi.sub_apply, map_sub, Finsupp.sub_apply]
  · intro x x' hx
    simp [ha.compat x x' hx, hb.compat x x' hx]

set_option autoImplicit false in
open Set Matrix MeasureTheory in
open scoped ComplexOrder in
variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : _root_.GlobalTheory.CxForm.HolAtlas M n) in
variable [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] in
private theorem integral_add_of_isForm {α β : A.Fld}
    (ha : A.IsForm α) (hb : A.IsForm β) :
    A.integral (α + β) =
      A.integral α + A.integral β := by
  have hnb : A.IsForm (0 - β) :=
    isForm_sub' A (isForm_zero' A) hb
  have h := A.integral_sub_of_isForm α (0 - β) ha hnb
  have h0 := A.integral_sub_of_isForm 0 β (isForm_zero' A) hb
  rw [integral_zero_fld A] at h0
  rw [show α - (0 - β) = α + β by abel] at h
  rw [h, h0]
  ring

set_option autoImplicit false in
open Set Matrix MeasureTheory in
open scoped ComplexOrder in
variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : _root_.GlobalTheory.CxForm.HolAtlas M n) in
variable [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] in
private theorem isForm_and_integral_finset_sum {ι : Type} (s : Finset ι)
    (α : ι → A.Fld) (hα : ∀ j ∈ s, A.IsForm (α j)) :
    A.IsForm (∑ j ∈ s, α j) ∧
      A.integral (∑ j ∈ s, α j) = ∑ j ∈ s, A.integral (α j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ⟨isForm_zero' A, integral_zero_fld A⟩
  | insert a s ha ih =>
    have hs := ih (fun j hj => hα j (Finset.mem_insert_of_mem hj))
    have hA := hα a (Finset.mem_insert_self a s)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨isForm_add' A hA hs.1, ?_⟩
    rw [integral_add_of_isForm A hA hs.1, hs.2]


set_option autoImplicit false in
theorem _root_.GlobalTheory.CxForm.IntegralSum.integral_sum : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M]
    [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ}
    (A : _root_.GlobalTheory.CxForm.HolAtlas M n) {N : ℕ} (α : Fin N → A.Fld),
    (∀ j, A.IsForm (α j)) →
      A.integral (∑ j, α j) = ∑ j, A.integral (α j) := by
  intro M _ _ _ _ _ _ n A N α hα
  exact (isForm_and_integral_finset_sum A Finset.univ α (fun j _ => hα j)).2

end GlobalTheory.CxForm.IntegralSum
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.VolUp.DetImMeas

theorem measurableSet_det_im_pos : ∀ (κ : Type) [Fintype κ] (p q : κ → ℕ) (ρ₀ : κ), MeasurableSet {b : ∀ ρ, UpqT (p ρ) (q ρ) | 0 < (UpqT.mat (b ρ₀)).det.im} := by
  intro κ _ p q ρ₀
  haveI : BorelSpace (UpqT (p ρ₀) (q ρ₀)) := (GlobalTheory.UpqTopology.upq_lcsc (p ρ₀) (q ρ₀)).2.2.2.2.1
  have hc : Continuous fun g : UpqT (p ρ₀) (q ρ₀) => (UpqT.mat g).det.im :=
    Complex.continuous_im.comp ((continuous_id.matrix_det).comp GlobalTheory.UpqTopology.continuous_mat)
  have hm : Measurable fun b : (∀ ρ, UpqT (p ρ) (q ρ)) => (UpqT.mat (b ρ₀)).det.im :=
    hc.measurable.comp (measurable_pi_apply ρ₀)
  exact measurableSet_lt measurable_const hm

end GlobalTheory.CovTop.VolUp.DetImMeas
end

section

open Formalism.REAL (inG)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin)

theorem _root_.GlobalTheory.T.kFinite_smoothVec_of_irreducible_unitaryRep :
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [Nontrivial H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
      IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → ∀ v, IsKFin ε σ v →
        Formalism.L2.Theta.SmoothVec {X | inG ε X} σ v :=
  GlobalTheory.HdSmooth.kFinite_smoothVec
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

theorem _root_.GlobalTheory.T.inertPlace_hyperspecialStable_lattice_eq_multiple : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E) (e : Formalism.L2.Theta.AE D), (∃ v ε, IsPlaceIdem D v ε ∧ e = algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) ε) → (∀ x : 𝓞 D.host.E, x ≠ 0 → (x ∈ P.asIdeal ↔ finPart D (e * incA D ((x : D.host.E)⁻¹)) ∉ intAE D)) → ∀ (M : AddSubgroup (Fin V.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))), (∀ a ∈ intAE D, ∀ z ∈ M, a • z ∈ M) → (∀ z ∈ M, finPart D (e) • z = z) → (∃ N : ℕ, 0 < N ∧ (∀ y ∈ Formalism.L2.NTheta.LamHat V, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • (finPart D (e) • y) ∈ M) ∧ ∀ z ∈ M, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • z ∈ Formalism.L2.NTheta.LamHat V) → (∀ g : GA D V, g ∈ KsphC V ∅ → SuppF V (e) g → ∀ z ∈ M, (finMat D.sp.cm.sig V.gram g).mulVec z ∈ M) → ∃ c : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), IsUnit c ∧ ∀ z, z ∈ M ↔ (finPart D (e) • z = z ∧ c • z ∈ Formalism.L2.NTheta.LamHat V) := by
  first | exact @GlobalTheory.InertLatMult.lattice_eq_mult | exact GlobalTheory.InertLatMult.lattice_eq_mult | (intros; apply GlobalTheory.InertLatMult.lattice_eq_mult <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_split_supported_unitary_lift_detOne : ∀ {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}, IsBaseFrame V β Λ N → ∀ {P : Pl D.host.E} {e : AE D}, Formalism.L2.NTheta.IsIdemAt e P → ∀ (k : GL (Fin V.rank) (kP P)), Matrix.GeneralLinearGroup.det k = 1 → ∃ κ : GA D V, SuppAt e V κ ∧ κ ∈ GfC V ∧ finE V κ ∈ St β ∧ redFn β P (finE V κ) = k ∧ (∀ P', P' ≠ P → ¬ Lev.IsConjPl P P' → redFn β P' (finE V κ) = 1) ∧ IsDetAt e V κ 1 := by
  first | exact @GlobalTheory.ParahoricLiftDet.exists_local_lift_det | exact GlobalTheory.ParahoricLiftDet.exists_local_lift_det | (intros; apply GlobalTheory.ParahoricLiftDet.exists_local_lift_det <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.dictionaryChar_eq_one_on_principalLevel : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i, ∀ k ∈ (levG (Wc D i) (R.βW i) (R.datWp i R.triv)), castDict hV (T.mu ((i : ℕ) + 1) (res T σ)) k = 1 := by
  first | exact @GlobalTheory.HolDict.PrincLevChar.char_eq_one | exact GlobalTheory.HolDict.PrincLevChar.char_eq_one | (intros; apply GlobalTheory.HolDict.PrincLevChar.char_eq_one <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rational_substitution_theta_heisenberg_unitary : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D), ∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (fun w => f (actO S T γ⁻¹ γ'⁻¹ w)) ∧ (∀ w₀, (fun w => heisO ψ S T w₀ f (actO S T γ⁻¹ γ'⁻¹ w)) = heisO ψ S T (actO S T γ γ' w₀) (fun w => f (actO S T γ⁻¹ γ'⁻¹ w))) ∧ ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∫⁻ w in 𝓕, ‖f (actO S T γ⁻¹ γ'⁻¹ w)‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.RatSubst.rational_substitution | exact GlobalTheory.RatSubst.rational_substitution | (intros; apply GlobalTheory.RatSubst.rational_substitution <;> assumption)
end
