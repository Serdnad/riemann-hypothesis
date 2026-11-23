module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsWeightedHomogeneousOfMemOrbitSpan
public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle007
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle003
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle008
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.TraceHermNondegenerate
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.SumFinsuppAntidiagProdPowDivMultiFactorial
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle004

@[expose] public section

section

namespace GlobalTheory.TensorLat

open NumberField ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {dim : (E →+* ℂ) → ℕ} {n : ℕ}

theorem norm_sq_contr_apply_le (γ : Fin n → Vsp dim) (w : Fin n → E) (i : Idx dim) :
    ‖contr γ w i‖ ^ 2 ≤ (∑ k, ‖i.1 (w k)‖ ^ 2) * ∑ k, ‖γ k i‖ ^ 2 := by
  refine le_trans ?_ (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖i.1 (w k)‖)
    fun k => ‖γ k i‖)
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  rw [contr_apply]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  simp

theorem norm_sq_contr_le (γ : Fin n → Vsp dim) (w : Fin n → E) {R : ℝ}
    (hw : ∀ τ : E →+* ℂ, ∑ k, ‖τ (w k)‖ ^ 2 ≤ R) :
    ‖contr γ w‖ ^ 2 ≤ R * ‖flat γ‖ ^ 2 := by
  rw [norm_sq_flat, EuclideanSpace.norm_sq_eq]
  simp only [EuclideanSpace.norm_sq_eq (γ _)]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => (norm_sq_contr_apply_le γ w i).trans ?_
  exact mul_le_mul_of_nonneg_right (hw i.1) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem norm_contr_le (γ : Fin n → Vsp dim) (w : Fin n → E) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hw : ∀ τ : E →+* ℂ, ∑ k, ‖τ (w k)‖ ^ 2 ≤ ρ ^ 2) :
    ‖contr γ w‖ ≤ ρ * ‖flat γ‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow]
  exact norm_sq_contr_le γ w hw

theorem exists_contr_ne_zero {ι : Type*} (v : ι → Fin n → E)
    (hspan : Submodule.span E (Set.range v) = ⊤) {γ : Fin n → Vsp dim} (hγ : γ ≠ 0) :
    ∃ i, contr γ (v i) ≠ 0 := by
  by_contra h
  push Not at h
  exact hγ (eq_zero_of_contr_span hspan (by rintro _ ⟨i, rfl⟩; exact h i))

theorem le_mul_norm_flat (X : PT E) (Λ' : Submodule (𝓞 E) (Fin n → E)) {ι : Type*}
    (v : ι → Fin n → E) (hv : ∀ i, v i ∈ Λ') (hspan : Submodule.span E (Set.range v) = ⊤)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hlen : ∀ i (τ : E →+* ℂ), ∑ k, ‖τ (v i k)‖ ^ 2 ≤ ρ ^ 2)
    {lam : ℝ} (hlam : ∀ x ∈ X.L, x ≠ 0 → lam ≤ ‖x‖)
    {γ : Fin n → Vsp X.dim} (hγ : γ ∈ tensorLat X Λ') (h0 : γ ≠ 0) :
    lam ≤ ρ * ‖flat γ‖ := by
  obtain ⟨i, hi⟩ := exists_contr_ne_zero v hspan h0
  exact (hlam _ (hγ _ (hv i)) hi).trans (norm_contr_le γ (v i) hρ (hlen i))


omit [IsCMField E] in
theorem span_eq_top_of_rat {S : Set (Fin n → E)} (h : Submodule.span ℚ S = ⊤) :
    Submodule.span E S = ⊤ :=
  eq_top_iff.2 fun x _ => Submodule.span_le_restrictScalars ℚ E S (h ▸ Submodule.mem_top (x := x))

theorem le_mul_norm_flat_of_selfDual (X : PT E) (Λ' : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ'.FG)
    (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ')
    {lam : ℝ} (hlam : ∀ x ∈ X.L, x ≠ 0 → lam ≤ ‖x‖)
    {γ : Fin n → Vsp X.dim} (hγ : γ ∈ tensorLat X Λ') (h0 : γ ≠ 0) :
    lam ≤ 2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E * ‖flat γ‖ := by
  obtain ⟨v, hv, -, hspan, hlen⟩ := exists_short_vectors Λ' hfg hint hdual
  have hr : 0 ≤ rdE E := Real.rpow_nonneg (abs_nonneg _) _
  exact le_mul_norm_flat X Λ' v hv (span_eq_top_of_rat hspan) (by positivity) hlen hlam hγ h0

end GlobalTheory.TensorLat
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.TB (perpVec)

namespace GlobalTheory.Harm

open GlobalTheory.MvPoly GlobalTheory.GridSize

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}


variable (E n) in
noncomputable def conjVec : (Fin n → E) →ₛₗ[((IsCMField.ringOfIntegersComplexConj E).toRingEquiv :
    𝓞 E →+* 𝓞 E)] (Fin n → E) where
  toFun v k := cc (v k)
  map_add' v w := funext fun k => map_add (IsCMField.complexConj E) (v k) (w k)
  map_smul' a v := funext fun k => map_mul (IsCMField.complexConj E) (a : E) (v k)

@[simp] theorem conjVec_apply (v : Fin n → E) (k : Fin n) : conjVec E n v k = cc (v k) := rfl


open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
@[simp] theorem _root_.GlobalTheory.Harm.conjVec_conjVec (v : Fin n → E) :
    _root_.GlobalTheory.Harm.conjVec E n (_root_.GlobalTheory.Harm.conjVec E n v) = v := by
  funext k
  exact _root_.GlobalTheory.TraceDualMin.cc_cc (v k)


open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
theorem _root_.GlobalTheory.Harm.herm_conjVec (v w : Fin n → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 (_root_.GlobalTheory.Harm.conjVec E n v) (_root_.GlobalTheory.Harm.conjVec E n w)
      = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 w v := by
  simp only [_root_.GlobalTheory.DualFamily.herm_one_eq, _root_.GlobalTheory.Harm.conjVec_apply,
    _root_.GlobalTheory.TraceDualMin.cc_cc]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

noncomputable def conjLattice (Λ : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) (Fin n → E) :=
  Λ.map (conjVec E n)

variable {Λ : Submodule (𝓞 E) (Fin n → E)}


open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
variable {Λ : Submodule (𝓞 E) (Fin n → E)} in
theorem _root_.GlobalTheory.Harm.mem_conjLattice {v : Fin n → E} :
    v ∈ _root_.GlobalTheory.Harm.conjLattice Λ ↔ _root_.GlobalTheory.Harm.conjVec E n v ∈ Λ := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [_root_.GlobalTheory.Harm.conjVec_conjVec]
    exact hw
  · intro hv
    exact ⟨_, hv, _root_.GlobalTheory.Harm.conjVec_conjVec v⟩


open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
variable {Λ : Submodule (𝓞 E) (Fin n → E)} in
theorem _root_.GlobalTheory.Harm.conjLattice_selfDual (hfg : Λ.FG)
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y)) → x ∈ Λ) :
    (_root_.GlobalTheory.Harm.conjLattice Λ).FG ∧
      (∀ x ∈ _root_.GlobalTheory.Harm.conjLattice Λ, ∀ y ∈ _root_.GlobalTheory.Harm.conjLattice Λ, IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y)) ∧
      ∀ x, (∀ y ∈ _root_.GlobalTheory.Harm.conjLattice Λ, IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y)) →
        x ∈ _root_.GlobalTheory.Harm.conjLattice Λ := by
  refine ⟨hfg.map _, ?_, ?_⟩
  · intro x hx y hy
    rw [_root_.GlobalTheory.Harm.mem_conjLattice] at hx hy
    have h := hint _ hy _ hx
    rwa [_root_.GlobalTheory.Harm.herm_conjVec] at h
  · intro x hx
    rw [_root_.GlobalTheory.Harm.mem_conjLattice]
    refine hdual _ fun y hy => ?_
    have hy' : _root_.GlobalTheory.Harm.conjVec E n y ∈ _root_.GlobalTheory.Harm.conjLattice Λ := by
      rw [_root_.GlobalTheory.Harm.mem_conjLattice, _root_.GlobalTheory.Harm.conjVec_conjVec]
      exact hy
    have h := _root_.GlobalTheory.TraceDualMin.isIntegral_cc (hx _ hy')
    rw [← _root_.GlobalTheory.DualFamily.herm_one_symm] at h
    have h2 := _root_.GlobalTheory.Harm.herm_conjVec (E := E) x (_root_.GlobalTheory.Harm.conjVec E n y)
    rw [_root_.GlobalTheory.Harm.conjVec_conjVec] at h2
    rw [h2]
    exact h


open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
variable {Λ : Submodule (𝓞 E) (Fin n → E)} in
omit [IsCMField E] in
theorem _root_.GlobalTheory.Harm.one_le_rdE : 1 ≤ _root_.ReciprocityTheory.ChartRestriction.G.FD.rdE E := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.rdE _root_.ReciprocityTheory.ChartRestriction.G.FD.dE
  apply Real.one_le_rpow _ (by positivity)
  have h : (discr E : ℝ) ≠ 0 := by exact_mod_cast discr_ne_zero E
  have h' : (1 : ℝ) ≤ |((discr E : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (discr_ne_zero E)
  exact_mod_cast h'


open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
variable {Λ : Submodule (𝓞 E) (Fin n → E)} in
theorem _root_.GlobalTheory.Harm.one_le_fdeg : 1 ≤ _root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E := by
  have h := _root_.GlobalTheory.ShortVectors.finrank_eq (E := E)
  have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
  omega


open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
variable {Λ : Submodule (𝓞 E) (Fin n → E)} in
theorem _root_.GlobalTheory.Harm.one_le_add_of_one_le_typeDegree {T : Type*} [Fintype T] {p q : ℕ}
    {c : T → Fin p → ℕ} {c' : T → Fin q → ℕ} (ha : 1 ≤ _root_.GlobalTheory.Harm.typeDegree c c') :
    1 ≤ p + q := by
  by_contra hpq
  obtain ⟨rfl, rfl⟩ : p = 0 ∧ q = 0 := by omega
  simp [_root_.GlobalTheory.Harm.typeDegree, _root_.GlobalTheory.Harm.partSize] at ha


variable (E n) in
noncomputable def hermPairing : (Fin n → E) →ₗ[E] ((Fin n → E) → E) where
  toFun x y := herm 1 x y
  map_add' x x' := funext fun y => by simp [herm_one_eq_sum, add_mul, Finset.sum_add_distrib]
  map_smul' r x := funext fun y => TraceDualMin.herm_smul_left r x y


open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
variable {Λ : Submodule (𝓞 E) (Fin n → E)} in
theorem _root_.GlobalTheory.Harm.perpVec_hermPairing_mem
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y)) {p : ℕ}
    {e e' : Fin p → Fin n → E} {g : Fin n → E} (he : ∀ a, e a ∈ Λ) (he' : ∀ a, e' a ∈ Λ)
    (hg : g ∈ Λ) : _root_.ReciprocityTheory.ChartRestriction.G.TB.perpVec (_root_.GlobalTheory.Harm.hermPairing E n) e e' g ∈ Λ := by
  classical
  unfold _root_.ReciprocityTheory.ChartRestriction.G.TB.perpVec
  set M := _root_.ReciprocityTheory.ChartRestriction.G.TB.hMat (_root_.GlobalTheory.Harm.hermPairing E n) e e' with hM
  have hMint : ∀ i j, IsIntegral ℤ (M i j) := fun i j => hint _ (he' i) _ (he j)
  let Mo : Matrix (Fin p) (Fin p) (𝓞 E) := fun i j => ⟨M i j, hMint i j⟩
  have hMo : M = (algebraMap (𝓞 E) E).mapMatrix Mo := by ext i j; rfl
  have key : ∀ (c : 𝓞 E) (x : Fin n → E), x ∈ Λ → ((c : E) • x) ∈ Λ :=
    fun c x hx => Λ.smul_mem c hx
  apply Λ.sub_mem
  · rw [hMo, ← RingHom.map_det]
    exact key _ _ hg
  · refine Λ.sum_mem fun a _ => Λ.sum_mem fun a' _ => ?_
    have hga : IsIntegral ℤ (_root_.GlobalTheory.Harm.hermPairing E n g (e a)) := hint _ hg _ (he a)
    rw [hMo, ← RingHom.map_adjugate]
    have hc : (algebraMap (𝓞 E) E).mapMatrix Mo.adjugate a a'
        * _root_.GlobalTheory.Harm.hermPairing E n g (e a)
        = ((Mo.adjugate a a' * ⟨_, hga⟩ : 𝓞 E) : E) := by
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
      rfl
    rw [hc]
    exact key _ _ (he' a')

end GlobalTheory.Harm
end
