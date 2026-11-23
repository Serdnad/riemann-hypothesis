module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle027
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle093
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Pi
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle006
public import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open MeasureTheory NumberField Formalism.MainNotions.S
open scoped ENNReal InnerProductSpace

namespace GlobalTheory.ProdFactor

theorem integrable_of_integrable_prod {ι : Type} [Fintype ι] {E : ι → Type} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : ∀ i, Measure (E i)} [∀ i, SigmaFinite (μ i)] {f : ∀ i, E i → ℂ}
    (hm : ∀ i, AEStronglyMeasurable (f i) (μ i)) (h0 : ∀ i, ¬ f i =ᵐ[μ i] 0)
    (h : Integrable (fun x : ∀ i, E i => ∏ i, f i (x i)) (Measure.pi μ)) (i : ι) :
    Integrable (f i) (μ i) := by

  by_contra hi
  have hn : ¬ Integrable (fun x => ‖f i x‖) (μ i) := fun h' => hi ((integrable_norm_iff (hm i)).1 h')
  have hprod : ∫ x : (∀ j, E j), ∏ j, ‖f j (x j)‖ ∂(Measure.pi μ) = 0 :=
    (integral_fintype_prod_eq_prod (μ := μ) (fun j (y : E j) => ‖f j y‖)).trans
      (Finset.prod_eq_zero (Finset.mem_univ i) (integral_undef hn))
  have hnorm : Integrable (fun x : ∀ j, E j => ∏ j, ‖f j (x j)‖) (Measure.pi μ) := by
    have h' := h.norm
    simp only [norm_prod] at h'
    exact h'
  have hae := (integral_eq_zero_iff_of_nonneg
    (fun x => Finset.prod_nonneg fun j _ => norm_nonneg (f j (x j))) hnorm).1 hprod
  have hbox : Measure.pi μ (Set.univ.pi fun j => {y | f j y ≠ 0}) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 hae)
    intro x hx
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq] at hx
    simp only [Set.mem_ofPred_eq, Pi.zero_apply]
    exact Finset.prod_ne_zero_iff.2 fun j _ => norm_ne_zero_iff.2 (hx j)
  rw [Measure.pi_pi] at hbox
  refine (Finset.prod_ne_zero_iff.2 fun j _ => ?_) hbox
  intro hz
  exact h0 j (ae_iff.2 (by simpa using hz))

theorem integrable_of_integrable_prod_of_continuous {ι : Type} [Fintype ι] {E : ι → Type}
    [∀ i, TopologicalSpace (E i)] {mE : ∀ i, MeasurableSpace (E i)} [∀ i, OpensMeasurableSpace (E i)]
    {μ : ∀ i, Measure (E i)} [∀ i, SigmaFinite (μ i)] [∀ i, (μ i).IsOpenPosMeasure] {f : ∀ i, E i → ℂ}
    (hc : ∀ i, Continuous (f i)) (h0 : ∀ i, ∃ x, f i x ≠ 0)
    (h : Integrable (fun x : ∀ i, E i => ∏ i, f i (x i)) (Measure.pi μ)) (i : ι) :
    Integrable (f i) (μ i) := by

  refine integrable_of_integrable_prod (fun j => (hc j).aestronglyMeasurable) (fun j hj => ?_) h i
  obtain ⟨x, hx⟩ := h0 j
  exact hx (congrFun (((hc j).ae_eq_iff_eq (μ j) continuous_zero).1 hj) x)

section Local

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem continuous_coefOn (hU : IsURepOn (UJset ε) σ) (v w : H) : Continuous (coefOn (ε := ε) σ v w) := by
  obtain ⟨-, -, hcont⟩ := hU
  have hσ : Continuous fun g : Formalism.REAL.UJ ε => σ (umat g) v :=
    (hcont v).comp_continuous (Units.continuous_val.comp continuous_subtype_val) fun g => g.2
  exact continuous_const.inner hσ

theorem coefOn_one (hU : IsURepOn (UJset ε) σ) {w : H} (hw : ‖w‖ = 1) : coefOn (ε := ε) σ w w 1 = 1 := by
  obtain ⟨⟨h1, -⟩, -, -⟩ := hU
  have hu : umat (1 : Formalism.REAL.UJ ε) = 1 := rfl
  show ⟪w, σ (umat (1 : Formalism.REAL.UJ ε)) w⟫_ℂ = 1
  rw [hu, h1, one_apply_eq_self, inner_self_eq_norm_sq_to_K, hw]
  norm_num

theorem fdegOf_pos (hU : IsURepOn (UJset ε) σ) (hsq : IsSqIntOn ε σ) {w : H} (hw : ‖w‖ = 1) :
    0 < fdegOf (Formalism.REAL.muG ε) σ w := by

  show 0 < ‖w‖ ^ 4 / ∫ g, ‖coefOn (ε := ε) σ w w g‖ ^ 2 ∂(Formalism.REAL.muG ε)
  rw [hw, one_pow]
  refine div_pos one_pos ?_
  have hcont : Continuous fun g : Formalism.REAL.UJ ε => ‖coefOn (ε := ε) σ w w g‖ ^ 2 :=
    (continuous_coefOn hU w w).norm.pow 2
  have hint : Integrable (fun g => ‖coefOn (ε := ε) σ w w g‖ ^ 2) (Formalism.REAL.muG ε) :=
    (hsq w w).norm.integrable_sq
  rw [integral_pos_iff_support_of_nonneg (fun g => by positivity) hint]
  refine hcont.isOpen_support.measure_pos _ ⟨1, ?_⟩
  simp [Function.mem_support, coefOn_one hU hw]

end Local

theorem integrable_factor {ι : Type} [Fintype ι] {n : ℕ} (ε : ι → Fin n → Bool) {H : ι → Type}
    [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    (σ : ∀ v, Matrix (Fin n) (Fin n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v) (d : ι → ℝ)
    (hU : ∀ v, IsURepOn (UJset (ε v)) (σ v)) (hw : ∀ v, ‖w v‖ = 1) (hd : ∀ v, d v ≠ 0)
    (h : Integrable (fun g : ∀ v, Formalism.REAL.UJ (ε v) =>
      ∏ v, (d v : ℂ) * star (coefOn (ε := ε v) (σ v) (w v) (w v) (g v))) (Measure.pi fun v => Formalism.REAL.muG (ε v)))
    (v : ι) :
    Integrable (fun g => (d v : ℂ) * star (coefOn (ε := ε v) (σ v) (w v) (w v) g)) (Formalism.REAL.muG (ε v)) := by

  exact integrable_of_integrable_prod_of_continuous (E := fun v => Formalism.REAL.UJ (ε v))
    (μ := fun v => Formalism.REAL.muG (ε v))
    (f := fun v g => (d v : ℂ) * star (coefOn (ε := ε v) (σ v) (w v) (w v) g))
    (fun v => continuous_const.mul (continuous_coefOn (hU v) (w v) (w v)).star)
    (fun v => ⟨1, by simp [coefOn_one (hU v) (hw v), hd v]⟩) h v

theorem integrable_factor' {ι : Type} [Fintype ι] {n : ℕ} (ε : ι → Fin n → Bool) {H : ι → Type}
    [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    (σ : ∀ v, Matrix (Fin n) (Fin n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v) (d : ι → ℝ)
    (hU : ∀ v, IsURepOn (UJset (ε v)) (σ v)) (hw : ∀ v, ‖w v‖ = 1) (hd : ∀ v, d v ≠ 0)
    (h : Integrable (fun g : ∀ v, Formalism.REAL.UJ (ε v) =>
      ((∏ v, d v : ℝ) : ℂ) * star (∏ v, coefOn (ε := ε v) (σ v) (w v) (w v) (g v)))
      (Measure.pi fun v => Formalism.REAL.muG (ε v))) (v : ι) :
    Integrable (fun g => (d v : ℂ) * star (coefOn (ε := ε v) (σ v) (w v) (w v) g)) (Formalism.REAL.muG (ε v)) := by
  have hfun : (fun g : ∀ v, Formalism.REAL.UJ (ε v) =>
      ((∏ v, d v : ℝ) : ℂ) * star (∏ v, coefOn (ε := ε v) (σ v) (w v) (w v) (g v))) =
      fun g => ∏ v, (d v : ℂ) * star (coefOn (ε := ε v) (σ v) (w v) (w v) (g v)) := by
    funext g
    rw [Complex.ofReal_prod, star_prod, Finset.prod_mul_distrib]
  rw [hfun] at h
  exact integrable_factor ε σ w d hU hw hd h v

end GlobalTheory.ProdFactor
end
end

section

universe u_1

namespace GlobalTheory.UpperUnipotentProductFlagMeasures

theorem upUni_mul {R : Type u_1} [CommRing R] {n : ℕ} {l l' : Matrix (Fin n) (Fin n) R}
    (h : Formalism.MainNotions.S.IsUpUni l) (h' : Formalism.MainNotions.S.IsUpUni l') : Formalism.MainNotions.S.IsUpUni (l * l') := by
  intro i j
  refine ⟨fun hji => ?_, fun hij => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k i with hk | hk
    · rw [(h i k).1 hk, zero_mul]
    · rw [(h' k j).1 (lt_of_lt_of_le hji hk), mul_zero]
  · subst hij
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [(h i i).2 rfl, (h' i i).2 rfl, mul_one]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with hk | hk
      · rw [(h i k).1 hk, zero_mul]
      · rw [(h' k i).1 hk, mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi

end GlobalTheory.UpperUnipotentProductFlagMeasures
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace ContDiff

namespace GlobalTheory

theorem smoothOnG_exists_contDiff_compactSupport_extension :
    ∀ (n : ℕ) (ε : Fin n → Bool) (β : Matrix (Fin n) (Fin n) ℂ → ℂ), SmoothOnG ε β →
      HasCompactSupport (fun g : UJ ε => β (umat g)) →
      ∃ F : (Fin n → Fin n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
        ∀ g : UJ ε, β (umat g) = F (fun i j => umat g i j) := by
  intro n ε β hβ hc
  obtain ⟨F₀, hF₀, hF₀eq⟩ := smoothOnG_exists_contDiff_extension n ε β hβ

  have hp : Continuous (fun g : UJ ε => (fun i j => umat g i j : Fin n → Fin n → ℂ)) := by
    have hu : Continuous (fun g : UJ ε => umat g) :=
      Units.continuous_val.comp continuous_subtype_val
    exact continuous_pi fun i => continuous_pi fun j => hu.matrix_elem i j

  have hK : IsCompact ((fun g : UJ ε => (fun i j => umat g i j : Fin n → Fin n → ℂ)) ''
      tsupport (fun g : UJ ε => β (umat g))) := hc.isCompact.image hp
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0

  let χ : ContDiffBump (0 : Fin n → Fin n → ℂ) :=
    ⟨max R 0 + 1, max R 0 + 2, by positivity, by linarith⟩
  refine ⟨fun x => (χ x : ℂ) * F₀ x, ?_, ?_, ?_⟩
  · exact (Complex.ofRealCLM.contDiff.comp χ.contDiff).mul hF₀
  · exact (χ.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right
  · intro g
    have h₀ : F₀ (fun i j => umat g i j) = β (umat g) := hF₀eq (umat g) g.2
    by_cases hz : β (umat g) = 0
    · show β (umat g) = (χ (fun i j => umat g i j) : ℂ) * F₀ (fun i j => umat g i j)
      rw [h₀, hz, mul_zero]
    · have hmem : (fun i j => umat g i j : Fin n → Fin n → ℂ) ∈ Metric.closedBall 0 χ.rIn := by
        refine Metric.closedBall_subset_closedBall ?_ (hR ⟨g, subset_tsupport _ hz, rfl⟩)
        show R ≤ max R 0 + 1
        linarith [le_max_left R 0]
      show β (umat g) = (χ (fun i j => umat g i j) : ℂ) * F₀ (fun i j => umat g i j)
      rw [χ.one_of_mem_closedBall hmem, h₀, Complex.ofReal_one, one_mul]

end GlobalTheory
end

section

open MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Classical

namespace GlobalTheory.RowLev

theorem isDS_lowUnit_unitary_fdegOf : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ → (∃ w, IsLowUnit ε lam σ w) ∧ (∀ (x : Formalism.REAL.UJ ε) a b, ⟪σ (uMat x) a, σ (uMat x) b⟫_ℂ = ⟪a, b⟫_ℂ) ∧ ∀ (c : NNReal) (d : ℝ) (w : H), 0 < c → ‖w‖ = 1 → IsFdeg ((c : ENNReal) • Formalism.REAL.muG ε) σ d → fdegOf (Formalism.REAL.muG ε) σ w = c * d := by
  intro n ε lam H _ _ σ h
  obtain ⟨-, -, hU, -, -, ⟨S, hS⟩, -⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨v, hvS, hv, -⟩ := hS.2.2.2.1
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    refine ⟨((‖v‖⁻¹ : ℝ) : ℂ) • v, ?_, ?_⟩
    · rw [norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    · have hle : S ≤ lowKSub ε lam σ := le_sSup hS
      exact hle (S.smul_mem _ hvS)
  · intro x a b
    have hx : uMat x ∈ UJset ε := x.2
    let f : H →ₗᵢ[ℂ] H := ⟨(σ (uMat x) : H →ₗ[ℂ] H), hU.2.1 _ hx⟩
    exact f.inner_map_map a b
  · intro c d w hc hw hF
    obtain ⟨hd, hI⟩ := hF
    have h1 := (hI w w w w).2
    have hc' : (0 : ℝ) < (c : ℝ) := hc
    have hww : ⟪w, w⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hw]; simp
    have hpt : (fun g : Formalism.REAL.UJ ε => coefOn σ w w g * star (coefOn σ w w g))
        = fun g => ((‖coefOn σ w w g‖ ^ 2 : ℝ) : ℂ) := by
      funext g
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hpt, integral_smul_measure, integral_complex_ofReal, hww, ENNReal.coe_toReal,
      Complex.real_smul] at h1
    have h2 : (c : ℝ) * ∫ g, ‖coefOn σ w w g‖ ^ 2 ∂(Formalism.REAL.muG ε) = 1 * 1 / d := by
      exact_mod_cast h1
    have h3 : ∫ g, ‖coefOn σ w w g‖ ^ 2 ∂(Formalism.REAL.muG ε) = 1 / ((c : ℝ) * d) := by
      field_simp at h2 ⊢
      linarith
    unfold fdegOf
    rw [h3, hw]
    simp

end GlobalTheory.RowLev
end

section

open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory.MinorJet

section Linfty
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem hasDerivAt_exp_entry {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (i j : Fin n) :
    HasDerivAt (fun u : ℝ => NormedSpace.exp ((u : ℂ) • Y) i j)
      ((NormedSpace.exp ((s : ℂ) • Y) * Y) i j) s := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y s
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have h2 := (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt s h
  simp only [Complex.coe_smul]
  exact h2

end Linfty

theorem hasDerivAt_mul_entry {r : ℕ} (G H : ℝ → Matrix (Fin r) (Fin r) ℂ)
    (G' H' : Matrix (Fin r) (Fin r) ℂ) (t : ℝ)
    (hG : ∀ i j, HasDerivAt (fun s => G s i j) (G' i j) t)
    (hH : ∀ i j, HasDerivAt (fun s => H s i j) (H' i j) t) (i j : Fin r) :
    HasDerivAt (fun s => (G s * H s) i j) ((G' * H t + G t * H') i j) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => (hG i k).fun_mul (hH k j))
  simpa [Matrix.mul_apply, Matrix.add_apply, Finset.sum_add_distrib] using h

theorem hasDerivAt_adjugate_entry {r : ℕ} (G : ℝ → Matrix (Fin r) (Fin r) ℂ)
    (A : Matrix (Fin r) (Fin r) ℂ) (t : ℝ) (h0 : G t = 1)
    (hG : ∀ i j, HasDerivAt (fun s => G s i j) (A i j) t) (i j : Fin r) :
    HasDerivAt (fun s => (G s).adjugate i j) ((A.trace • (1 : Matrix (Fin r) (Fin r) ℂ) - A) i j) t := by
  have hP : ∀ a b, HasDerivAt (fun s => (G s).adjugate a b)
      ((((G t).updateRow b (Pi.single a 1)).adjugate * A.updateRow b 0).trace) t := by
    intro a b
    have hrow : ∀ p q, HasDerivAt (fun s => (G s).updateRow b (Pi.single a 1) p q)
        ((A.updateRow b 0) p q) t := by
      intro p q
      by_cases hp : p = b
      · subst hp
        simp only [updateRow_self]
        exact hasDerivAt_const _ _
      · simp only [updateRow_ne hp]
        exact hG p q
    have h := ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det (fun s => (G s).updateRow b (Pi.single a 1)) _ t hrow
    simpa only [adjugate_apply] using h
  let D : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a b =>
    (((G t).updateRow b (Pi.single a 1)).adjugate * A.updateRow b 0).trace
  have hD : ∀ a b, HasDerivAt (fun s => (G s).adjugate a b) (D a b) t := fun a b => hP a b
  have h1 := hasDerivAt_mul_entry (fun s => (G s).adjugate) G D A t hD hG i j
  have h2 := (ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det G A t hG).mul_const ((1 : Matrix (Fin r) (Fin r) ℂ) i j)
  have h3 : HasDerivAt (fun s => (G s).det * (1 : Matrix (Fin r) (Fin r) ℂ) i j)
      ((D * G t + (G t).adjugate * A) i j) t := by
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    simp only [adjugate_mul, Matrix.smul_apply, smul_eq_mul]
  have hu := h3.unique h2
  rw [h0, adjugate_one, Matrix.mul_one, Matrix.one_mul, Matrix.add_apply] at hu
  have hDij : D i j = A.trace * (1 : Matrix (Fin r) (Fin r) ℂ) i j - A i j := by
    linear_combination hu
  convert hD i j using 1
  rw [hDij, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]

private theorem sum_castLE_lemma {n l : ℕ} (hl : l ≤ n) (f : Fin n → ℂ) :
    ∑ x : Fin l, f (Fin.castLE hl x) = ∑ a : Fin n, if a.val < l then f a else 0 := by
  have e : (Finset.univ : Finset (Fin l)).map (Fin.castLEEmb hl) =
      Finset.univ.filter (fun a : Fin n => a.val < l) := by
    ext a
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_filter, Fin.castLEEmb_apply]
    constructor
    · rintro ⟨x, rfl⟩
      simp
    · intro h
      exact ⟨⟨a.val, h⟩, Fin.ext rfl⟩
  rw [← Finset.sum_filter, ← e, Finset.sum_map]
  rfl

theorem trace_block {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (hY : Y.IsHermitian) (l : ℕ) (hl : l ≤ n) :
    ((Y * Y).submatrix (Fin.castLE hl) (Fin.castLE hl)).trace -
      (Y.submatrix (Fin.castLE hl) (Fin.castLE hl) * Y.submatrix (Fin.castLE hl) (Fin.castLE hl)).trace =
    ((∑ a : Fin n, ∑ b : Fin n, if l ≤ a.val ∧ b.val < l then ‖Y a b‖ ^ 2 else 0 : ℝ) : ℂ) := by
  have hH : ∀ a b, Y a b * Y b a = ((‖Y b a‖ ^ 2 : ℝ) : ℂ) := by
    intro a b
    have e : Y a b = star (Y b a) := by
      have := congrFun (congrFun hY a) b
      rw [conjTranspose_apply] at this
      exact this.symm
    rw [e, Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have e1 : ((Y * Y).submatrix (Fin.castLE hl) (Fin.castLE hl)).trace =
      ∑ a : Fin n, if a.val < l then ∑ b : Fin n, Y a b * Y b a else 0 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply, Matrix.mul_apply]
    exact sum_castLE_lemma hl (fun a => ∑ b : Fin n, Y a b * Y b a)
  have e2 : (Y.submatrix (Fin.castLE hl) (Fin.castLE hl) *
      Y.submatrix (Fin.castLE hl) (Fin.castLE hl)).trace =
      ∑ a : Fin n, if a.val < l then ∑ b : Fin n, (if b.val < l then Y a b * Y b a else 0) else 0 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.submatrix_apply]
    rw [← sum_castLE_lemma hl (fun a => ∑ b : Fin n, if b.val < l then Y a b * Y b a else 0)]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    exact sum_castLE_lemma hl (fun b => Y (Fin.castLE hl x) b * Y b (Fin.castLE hl x))
  have key : ∀ a : Fin n, ((if a.val < l then ∑ b : Fin n, Y a b * Y b a else 0) -
      (if a.val < l then ∑ b : Fin n, (if b.val < l then Y a b * Y b a else 0) else 0)) =
      ∑ b : Fin n, ((if l ≤ b.val ∧ a.val < l then ‖Y b a‖ ^ 2 else 0 : ℝ) : ℂ) := by
    intro a
    by_cases ha : a.val < l
    · rw [if_pos ha, if_pos ha, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      by_cases hb : b.val < l
      · rw [if_pos hb, if_neg (fun h => absurd h.1 (Nat.not_le.mpr hb)), sub_self,
          Complex.ofReal_zero]
      · rw [if_neg hb, sub_zero, if_pos ⟨Nat.le_of_not_lt hb, ha⟩, hH]
    · rw [if_neg ha, if_neg ha, sub_self]
      symm
      refine Finset.sum_eq_zero (fun b _ => ?_)
      rw [if_neg (fun h => ha h.2), Complex.ofReal_zero]
  rw [e1, e2, ← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun a _ => key a), Finset.sum_comm,
    Complex.ofReal_sum]
  simp only [Complex.ofReal_sum]

theorem deriv_leadMinor_exp : ∀ (n : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ), Y.IsHermitian → (∀ a, Y a a = 0) → ∀ (l : ℕ) (hl : l ≤ n), deriv (fun t : ℝ => (leadMinor (NormedSpace.exp ((t : ℂ) • Y)) l hl).re) 0 = 0 ∧ deriv (deriv (fun t : ℝ => (leadMinor (NormedSpace.exp ((t : ℂ) • Y)) l hl).re)) 0 = ∑ a : Fin n, ∑ b : Fin n, if l ≤ a.val ∧ b.val < l then ‖Y a b‖ ^ 2 else 0 := by
  intro n Y hY hdiag l hl
  have hE0 : NormedSpace.exp (((0 : ℝ) : ℂ) • Y) = 1 := by simp
  have hM0 : (NormedSpace.exp (((0 : ℝ) : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl) = 1 := by
    rw [hE0]
    exact submatrix_one _ (Fin.castLE_injective hl)
  have hM'0 : (NormedSpace.exp (((0 : ℝ) : ℂ) • Y) * Y).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      Y.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
    rw [hE0, Matrix.one_mul]
  have htr : (Y.submatrix (Fin.castLE hl) (Fin.castLE hl)).trace = 0 := by
    simp [Matrix.trace, hdiag]
  have hM : ∀ (t : ℝ) x y, HasDerivAt
      (fun s : ℝ => (NormedSpace.exp ((s : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl) x y)
      ((NormedSpace.exp ((t : ℂ) • Y) * Y).submatrix (Fin.castLE hl) (Fin.castLE hl) x y) t :=
    fun t x y => hasDerivAt_exp_entry Y t (Fin.castLE hl x) (Fin.castLE hl y)
  have hf : ∀ t : ℝ, HasDerivAt
      (fun s : ℝ => (leadMinor (NormedSpace.exp ((s : ℂ) • Y)) l hl).re)
      (((NormedSpace.exp ((t : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl)).adjugate *
        (NormedSpace.exp ((t : ℂ) • Y) * Y).submatrix (Fin.castLE hl) (Fin.castLE hl)).trace.re t := by
    intro t
    have hg := ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det
      (fun s : ℝ => (NormedSpace.exp ((s : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl)) _ t (hM t)
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hg
    simpa [leadMinor, Function.comp_def] using h
  have hderiv : deriv (fun s : ℝ => (leadMinor (NormedSpace.exp ((s : ℂ) • Y)) l hl).re) =
      fun t : ℝ => (((NormedSpace.exp ((t : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl)).adjugate *
        (NormedSpace.exp ((t : ℂ) • Y) * Y).submatrix (Fin.castLE hl) (Fin.castLE hl)).trace.re :=
    funext fun t => (hf t).deriv
  rw [hderiv]
  refine ⟨?_, ?_⟩
  · beta_reduce
    rw [hM0, hM'0, adjugate_one, Matrix.one_mul, htr, Complex.zero_re]
  · have hadj : ∀ x y, HasDerivAt
        (fun s : ℝ => ((NormedSpace.exp ((s : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl)).adjugate x y)
        (((Y.submatrix (Fin.castLE hl) (Fin.castLE hl)).trace • (1 : Matrix (Fin l) (Fin l) ℂ) -
          Y.submatrix (Fin.castLE hl) (Fin.castLE hl)) x y) 0 := by
      intro x y
      have h := hasDerivAt_adjugate_entry
        (fun s : ℝ => (NormedSpace.exp ((s : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl)) _ 0 hM0
        (hM 0) x y
      rwa [hM'0] at h
    have hMd : ∀ x y, HasDerivAt
        (fun s : ℝ => (NormedSpace.exp ((s : ℂ) • Y) * Y).submatrix (Fin.castLE hl) (Fin.castLE hl) x y)
        ((Y * Y).submatrix (Fin.castLE hl) (Fin.castLE hl) x y) 0 := by
      intro x y
      have h := hasDerivAt_mul_entry (fun s : ℝ => NormedSpace.exp ((s : ℂ) • Y)) (fun _ => Y)
        (NormedSpace.exp (((0 : ℝ) : ℂ) • Y) * Y) 0 0 (hasDerivAt_exp_entry Y 0)
        (fun _ _ => hasDerivAt_const _ _) (Fin.castLE hl x) (Fin.castLE hl y)
      rw [hE0, Matrix.one_mul, Matrix.mul_zero, add_zero] at h
      exact h
    have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun x _ =>
      hasDerivAt_mul_entry
        (fun s : ℝ => ((NormedSpace.exp ((s : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl)).adjugate)
        (fun s : ℝ => (NormedSpace.exp ((s : ℂ) • Y) * Y).submatrix (Fin.castLE hl) (Fin.castLE hl))
        _ _ 0 hadj hMd x x)
    have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hsum
    have h3 : HasDerivAt
        (fun t : ℝ => (((NormedSpace.exp ((t : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl)).adjugate *
          (NormedSpace.exp ((t : ℂ) • Y) * Y).submatrix (Fin.castLE hl) (Fin.castLE hl)).trace.re)
        ((((Y.submatrix (Fin.castLE hl) (Fin.castLE hl)).trace • (1 : Matrix (Fin l) (Fin l) ℂ) - Y.submatrix (Fin.castLE hl) (Fin.castLE hl)) *
          (NormedSpace.exp (((0 : ℝ) : ℂ) • Y) * Y).submatrix (Fin.castLE hl) (Fin.castLE hl) +
          ((NormedSpace.exp (((0 : ℝ) : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl)).adjugate *
          (Y * Y).submatrix (Fin.castLE hl) (Fin.castLE hl)).trace).re 0 := h2
    have hv : (((Y.submatrix (Fin.castLE hl) (Fin.castLE hl)).trace • (1 : Matrix (Fin l) (Fin l) ℂ) - Y.submatrix (Fin.castLE hl) (Fin.castLE hl)) *
          (NormedSpace.exp (((0 : ℝ) : ℂ) • Y) * Y).submatrix (Fin.castLE hl) (Fin.castLE hl) +
          ((NormedSpace.exp (((0 : ℝ) : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl)).adjugate *
          (Y * Y).submatrix (Fin.castLE hl) (Fin.castLE hl)).trace =
        ((Y * Y).submatrix (Fin.castLE hl) (Fin.castLE hl)).trace - (Y.submatrix (Fin.castLE hl) (Fin.castLE hl) * Y.submatrix (Fin.castLE hl) (Fin.castLE hl)).trace := by
      rw [hM0, hM'0, adjugate_one, htr, zero_smul, zero_sub, Matrix.neg_mul, Matrix.one_mul,
        Matrix.trace_add, Matrix.trace_neg]
      ring
    rw [h3.deriv, hv, trace_block Y hY l hl, Complex.ofReal_re]

end GlobalTheory.MinorJet
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.continuous_hasCompactSupport_infFin_product_testFunction : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (M n : ℕ) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (Φi : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ), Continuous Φi → HasCompactSupport Φi → Continuous Φf → HasCompactSupport Φf → IsProdInfFin Φ Φi Φf → Continuous Φ ∧ HasCompactSupport Φ := by
  first | exact @GlobalTheory.prod_continuous_hasCompactSupport | exact GlobalTheory.prod_continuous_hasCompactSupport | (intros; apply GlobalTheory.prod_continuous_hasCompactSupport <;> assumption)
end
