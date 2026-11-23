module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish
import GroundTheory.AutomorphicForms.ReductionDirichlet
public import GroundTheory.AutomorphicForms.ReductionHeight
public import GroundTheory.AutomorphicForms.ReductionIwasawa
import GroundTheory.AutomorphicForms.Bundle012
public import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.GJGlobalModulus
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import GroundTheory.AutomorphicForms.GL2Classical.Bundle001
import GroundTheory.AutomorphicForms.Bundle016
import GroundTheory.AutomorphicForms.ReductionCore
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.ideleCover :
    ∀ (F : Type) [Field F] [NumberField F] (c : ℝ), 0 < c → ∃ (C : Set (IdeleGroup F)) (ρ : IdeleGroup F), IsCompact C ∧ 1 < ab ρ ∧ ∀ a : IdeleGroup F, c ≤ ab a → ∃ (t : Fˣ) (n : ℕ), ∃ x ∈ C, IdeleGroup.diagonal F t * a = ρ ^ n * x := by
  intro F _ _ c hc
  set ρ : IdeleGroup F := Reduction.posIdele (K := F) 2 two_pos with hρ
  have hr : ab ρ = 2 ^ Module.finrank ℚ F := Reduction.ideleModule_posIdele (K := F) 2 two_pos
  have h1 : 1 < ab ρ := by
    rw [hr]
    exact one_lt_pow₀ one_lt_two Module.finrank_pos.ne'
  have hr0 : 0 < ab ρ := one_pos.trans h1
  obtain ⟨S, hS, hSm⟩ := Reduction.exists_isCompact_mul_mem_of_ideleModule_mem_Icc (K := F) hc (c * ab ρ)
  refine ⟨S, ρ, hS, h1, fun a ha => ?_⟩
  have hx : 1 ≤ ab a / c := (one_le_div hc).2 ha
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hx h1
  have hp : 0 < ab ρ ^ n := pow_pos hr0 n
  have hm : (IdeleGroup.ideleModule F ((ρ ^ n)⁻¹ * a) : ℝ) = ab a / ab ρ ^ n := by
    have : (IdeleGroup.ideleModule F ((ρ ^ n)⁻¹ * a) : ℝ)
        = ((IdeleGroup.ideleModule F ρ : ℝ) ^ n)⁻¹ * (IdeleGroup.ideleModule F a : ℝ) := by
      simp [map_mul, map_inv, map_pow]
    rw [this, div_eq_inv_mul]
    rfl
  obtain ⟨t, ht⟩ := hSm ((ρ ^ n)⁻¹ * a)
    (by
      rw [hm, le_div_iff₀ hp]
      have := (le_div_iff₀ hc).1 hn1
      linarith)
    (by
      rw [hm, div_le_iff₀ hp]
      have h2 := (div_lt_iff₀ hc).1 hn2
      rw [pow_succ] at h2
      nlinarith)
  refine ⟨t, n, _, ht, ?_⟩
  rw [mul_left_comm, mul_inv_cancel_left]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.kkFin :
    ∀ (F : Type) [Field F] [NumberField F], ∀ (k : G1 F) (v : HeightOneSpectrum (𝓞 F)), IntAt v k ↔ Reduction.finAt v (gl k) ∈ GLnLocal.integralGL (v.adicCompletion F) 2 := by
  intro F _ _ k v
  have hinv : (Reduction.finAt v (gl k))⁻¹ = Reduction.finAt v (gl k⁻¹) := by
    have e : ∀ g : GL (Fin 2) (A F), Reduction.finAt v g = Matrix.GeneralLinearGroup.map (Reduction.finEval v) g := by
      intro g; ext i j; rfl
    rw [e, e, ← map_inv, ← map_inv]
  have hent : ∀ (g : G1 F) i j, (Reduction.finAt v (gl g)) i j = (g i j).2 v := fun _ _ _ => rfl
  rw [GLnLocal.mem_integralGL_iff, hinv]
  simp only [hent, GroundTheory.Global.mem_valuationInteger_iff]
  refine ⟨fun h => ⟨h, ?_⟩, fun h => h.1⟩
  intro i j
  have e : (k⁻¹ : G1 F).1 = !![k.1 1 1, -k.1 0 1; -k.1 1 0, k.1 0 0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two]
  have hn : ∀ a b, (-(k.1 a b)).2 v ∈ v.adicCompletionIntegers F := fun a b =>
    neg_mem (h a b)
  show ((k⁻¹ : G1 F).1 i j).2 v ∈ _
  rw [e]
  fin_cases i <;> fin_cases j
  · exact h 1 1
  · exact hn 0 1
  · exact hn 1 0
  · exact h 0 0
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise

namespace UpperTheory.ConvolutionTheory.R2

variable {F : Type} [Field F] [NumberField F]

instance : SecondCountableTopology (G1 F) :=
  TopologicalSpace.Subtype.secondCountableTopology {M : Matrix (Fin 2) (Fin 2) (A F) | M.det = 1}

instance : LocallyCompactSpace (G1 F) := by
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (A F)) := inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → A F))
  have h : IsClosed {M : Matrix (Fin 2) (Fin 2) (A F) | M.det = 1} :=
    isClosed_eq (continuous_id.matrix_det) continuous_const
  exact h.locallyCompactSpace

namespace M

theorem ab_pos (a : (A F)ˣ) : 0 < ab a := (IdeleGroup.ideleModule F a).2
theorem ab_mul (a b : (A F)ˣ) : ab (a * b) = ab a * ab b := by simp [ab]
theorem ab_one : ab (1 : (A F)ˣ) = 1 := by simp [ab]
theorem ab_inv (a : (A F)ˣ) : ab a⁻¹ = (ab a)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← ab_mul, inv_mul_cancel, ab_one])
theorem continuous_ab : Continuous (ab : (A F)ˣ → ℝ) :=
  continuous_subtype_val.comp (IdeleGroup.continuous_ideleModule (K := F))

theorem val_mul (g h : G1 F) : (g * h).1 = g.1 * h.1 := rfl
theorem val_gl (g : G1 F) : (gl g).val = g.1 := rfl
theorem val_ratS (γ : Matrix.SpecialLinearGroup (Fin 2) F) : (ratS F γ).1 = γ.1.map (algebraMap F (A F)) := rfl

theorem nU_add (a b : A F) : nU (a + b) = nU a * nU b := by
  refine Subtype.ext ?_; rw [val_mul]; ext i j; fin_cases i <;> fin_cases j <;> simp [nU, Matrix.mul_apply, Fin.sum_univ_two, add_comm]
theorem nU_zero : nU (0 : A F) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [nU]
theorem nU_neg (a : A F) : nU (-a) = (nU a)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← nU_add, neg_add_cancel, nU_zero])
theorem mD_mul (a b : (A F)ˣ) : mD (a * b) = mD a * mD b := by
  refine Subtype.ext ?_; rw [val_mul]; ext i j; fin_cases i <;> fin_cases j <;> simp [mD, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
theorem mD_one : mD (1 : (A F)ˣ) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [mD]
theorem mD_inv (a : (A F)ˣ) : mD a⁻¹ = (mD a)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← mD_mul, inv_mul_cancel, mD_one])
theorem mD_mul_nU (a : (A F)ˣ) (b : A F) : mD a * nU b = nU ((a : A F) ^ 2 * b) * mD a := by
  refine Subtype.ext ?_; rw [val_mul, val_mul]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [mD, nU, Matrix.mul_apply, Fin.sum_univ_two, pow_two, mul_assoc, mul_comm b]
theorem gl_cD (t : (A F)ˣ) (g : G1 F) : gl (cD t g) * dM t = dM t * gl g := by
  refine Units.ext ?_; rw [Units.val_mul, Units.val_mul, val_gl, val_gl]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [cD, dM, Matrix.mul_apply, Fin.sum_univ_two, mul_assoc, mul_comm]
theorem gl_inj : Function.Injective (gl : G1 F → GL (Fin 2) (A F)) := Matrix.SpecialLinearGroup.toGL_injective
theorem gl_cD' (t : (A F)ˣ) (g : G1 F) : gl (cD t g) = dM t * gl g * (dM t)⁻¹ := by
  rw [← gl_cD, mul_inv_cancel_right]
theorem dM_mul (s t : (A F)ˣ) : dM (s * t) = dM s * dM t := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [dM, Matrix.mul_apply, Fin.sum_univ_two]
theorem dM_one : dM (1 : (A F)ˣ) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [dM]
theorem cD_mul (t : (A F)ˣ) (g h : G1 F) : cD t (g * h) = cD t g * cD t h :=
  gl_inj (by
    have h : ∀ x y : G1 F, gl (x * y) = gl x * gl y := fun x y => map_mul _ x y
    rw [h, gl_cD', gl_cD', gl_cD', h]; group)
theorem cD_cD (s t : (A F)ˣ) (g : G1 F) : cD s (cD t g) = cD (s * t) g :=
  gl_inj (by rw [gl_cD', gl_cD', gl_cD', dM_mul]; group)
theorem cD_one (g : G1 F) : cD 1 g = g := gl_inj (by rw [gl_cD', dM_one]; group)
theorem cD_nU (t : (A F)ˣ) (b : A F) : cD t (nU b) = nU (b * ((t⁻¹ : (A F)ˣ) : A F)) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cD, nU]
theorem cD_sq (t : (A F)ˣ) (g : G1 F) : cD (t * t) g = (mD t)⁻¹ * g * mD t := by
  rw [← mD_inv]
  refine Subtype.ext ?_; rw [val_mul, val_mul]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [cD, mD, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, mul_assoc, mul_comm, mul_left_comm]

theorem continuous_nU : Continuous (nU : A F → G1 F) :=
  Continuous.subtype_mk (continuous_matrix fun i j => by fin_cases i <;> fin_cases j <;> simp <;> fun_prop) _
theorem continuous_mD : Continuous (mD : (A F)ˣ → G1 F) :=
  Continuous.subtype_mk (continuous_matrix fun i j => by
    fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] <;>
      first | exact continuous_const | exact Units.continuous_val | exact Units.continuous_coe_inv) _
theorem continuous_entry (i j : Fin 2) : Continuous fun g : G1 F => g i j :=
  (continuous_subtype_val (p := fun M : Matrix (Fin 2) (Fin 2) (A F) => M.det = 1)).matrix_elem i j
theorem continuous_cD (t : (A F)ˣ) : Continuous (cD t : G1 F → G1 F) :=
  Continuous.subtype_mk (continuous_matrix fun i j => by
    fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] <;>
      first | exact continuous_entry _ _ | exact (continuous_entry _ _).mul continuous_const | exact continuous_const.mul (continuous_entry _ _)) _
theorem continuous_gl : Continuous (gl : G1 F → GL (Fin 2) (A F)) := Matrix.SpecialLinearGroup.continuous_toGL

theorem ratS_up (ξ : F) : ratS F ⟨!![1, ξ; 0, 1], by simp [Matrix.det_fin_two]⟩ = nU (rt ξ) := by
  refine Subtype.ext ((val_ratS _).trans ?_); ext i j; fin_cases i <;> fin_cases j <;> simp [nU]
theorem nU_rt_mem (ξ : F) : nU (rt ξ) ∈ Gam F := ⟨_, ratS_up ξ⟩
theorem mD_diag_mem (t : Fˣ) : mD (IdeleGroup.diagonal F t) ∈ Gam F := by
  refine ⟨⟨!![(t : F), 0; 0, ((t⁻¹ : Fˣ) : F)], by simp [Matrix.det_fin_two]⟩, ?_⟩
  refine Subtype.ext ((val_ratS _).trans ?_); ext i j; fin_cases i <;> fin_cases j <;> simp [mD, IdeleGroup.diagonal, ← map_inv]
theorem ab_diag (t : Fˣ) : ab (IdeleGroup.diagonal F t) = 1 := by
  simp [ab, IdeleGroup.ideleModule_diagonal]

instance : Countable (Matrix.SpecialLinearGroup (Fin 2) F) := by
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  haveI : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  exact inferInstanceAs (Countable {M : Matrix (Fin 2) (Fin 2) F // M.det = 1})
instance : Countable (Gam F) := (Set.countable_range _).to_subtype

instance : DiscreteTopology (Gam F) := by
  haveI := AdelicGLn.discreteTopology_rationalGL F 2
  have hm : ∀ g : Gam F, gl g.1 ∈ AdelicGLn.rationalGL F 2 := by
    rintro ⟨_, γ, rfl⟩
    exact ⟨Matrix.SpecialLinearGroup.toGL γ, Units.ext rfl⟩
  refine DiscreteTopology.of_continuous_injective
    (f := fun g : Gam F => (⟨gl g.1, hm g⟩ : AdelicGLn.rationalGL F 2)) ?_
    fun a b h => Subtype.ext (gl_inj (congrArg (·.1) h))
  exact (continuous_gl.comp continuous_subtype_val).subtype_mk _


variable (F) in
def Ks : Subgroup (G1 F) := (Reduction.maxCompact (K := F) (n := 2)).comap Matrix.SpecialLinearGroup.toGL

variable (F) in
def Bor : Subgroup (G1 F) := (Reduction.adelicBorel (K := F) (n := 2)).comap Matrix.SpecialLinearGroup.toGL

def wt (a : (A F)ˣ) : ℝ≥0∞ := ENNReal.ofReal ((ab a)⁻¹ ^ 2)

def J0 (M : Meas F) (u : G1 F → ℝ≥0∞) : ℝ≥0∞ := ∫⁻ p, wt p.1 * u (mD p.1 * p.2) ∂M.ν

def NWt (β : G1 F → ℝ≥0∞) : Prop := Measurable β ∧ ∀ g, ∑' ξ : F, β (nU (rt ξ) * g) = 1

def RowSec (σ : {r : Fin 2 → F // r ≠ 0} → Matrix.SpecialLinearGroup (Fin 2) F) : Prop := ∀ r, (σ r).1 1 = r.1

theorem measurable_wt : Measurable (wt : IdeleGroup F → ℝ≥0∞) :=
  ((continuous_ab.measurable.inv).pow_const 2).ennreal_ofReal

theorem transfer {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {m : Measure X} {n : Measure Y} {u : X → ℂ} {v : Y → ℂ}
    (hu : Measurable u) (hv : Measurable v)
    (h : ∀ φ : ℂ → ℝ≥0∞, Measurable φ → ∫⁻ x, φ (u x) ∂m = ∫⁻ y, φ (v y) ∂n) :
    (Integrable u m ↔ Integrable v n) ∧ ∫ x, u x ∂m = ∫ y, v y ∂n := by
  have e : m.map u = n.map v := by
    ext s hs
    rw [← lintegral_indicator_one hs, ← lintegral_indicator_one hs, lintegral_map (measurable_one.indicator hs) hu,
      lintegral_map (measurable_one.indicator hs) hv]
    exact h _ (measurable_one.indicator hs)
  constructor
  · have h1 := integrable_map_measure (μ := m) (f := u) (g := id) aestronglyMeasurable_id hu.aemeasurable
    have h2 := integrable_map_measure (μ := n) (f := v) (g := id) aestronglyMeasurable_id hv.aemeasurable
    rw [e] at h1
    exact h1.symm.trans h2
  · have h1 := integral_map (μ := m) (φ := u) (f := id) hu.aemeasurable aestronglyMeasurable_id
    have h2 := integral_map (μ := n) (φ := v) (f := id) hv.aemeasurable aestronglyMeasurable_id
    rw [e] at h1
    exact h1.symm.trans h2

end M

end UpperTheory.ConvolutionTheory.R2

end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

private theorem real_iff {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    (∀ z : Fin n → ℝ, Reduction.euclidNorm (z ᵥ* M) = Reduction.euclidNorm z) ↔ M * Mᵀ = 1 := by
  constructor
  · intro h
    have hq : ∀ z : Fin n → ℝ, (z ᵥ* M) ⬝ᵥ (z ᵥ* M) = z ⬝ᵥ z := by
      intro z
      have h2 := congrArg (· ^ 2) (h z)
      simp only [Reduction.euclidNorm_sq, Real.norm_eq_abs, sq_abs] at h2
      simpa only [dotProduct, sq] using h2
    have hb : ∀ x z : Fin n → ℝ, (x ᵥ* M) ⬝ᵥ (z ᵥ* M) = x ⬝ᵥ z := by
      intro x z
      have h1 := hq (x + z)
      rw [add_vecMul] at h1
      simp only [add_dotProduct, dotProduct_add, hq] at h1
      rw [dotProduct_comm (z ᵥ* M), dotProduct_comm z x] at h1
      linarith
    ext i j
    have h3 := hb (Pi.single i 1) (Pi.single j 1)
    rw [single_one_vecMul, single_one_vecMul, single_one_dotProduct] at h3
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [transpose_apply]
    refine Eq.trans h3 ?_
    simp [Pi.single_apply]
  · intro h z
    refine Reduction.euclidNorm_vecMul_unitary ?_ z
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
    exact h

private theorem entry_mul {F : Type} [Field F] [NumberField F] (k : G1 F) (w : InfinitePlace F) (i j : Fin 2) :
    ((k.1 * k.1ᵀ) i j).1 w = ∑ l, (k i l).1 w * (k j l).1 w := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  rfl

private theorem entry_one {F : Type} [Field F] [NumberField F] (w : InfinitePlace F) (i j : Fin 2) :
    ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j).1 w = (1 : Matrix (Fin 2) (Fin 2) w.Completion) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

private theorem place_iff {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (k : G1 F) (w : InfinitePlace F) :
    Reduction.infAt w (gl k) ∈ Reduction.archCompact w ↔
      ∀ i j, ((k.1 * k.1ᵀ) i j).1 w = ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j).1 w := by
  set ψ := InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) with hψdef
  have hψ : ∀ z, ‖ψ.toRingHom z‖ = ‖z‖ := fun z =>
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (IsTotallyReal.isReal w)).norm_map_of_map_zero
      (map_zero _) z
  let M : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i j => ψ ((k i j).1 w)
  have e : ∀ z : Fin 2 → w.Completion,
      (fun j => ψ.toRingHom ((z ᵥ* (Reduction.infAt w (gl k) : Matrix (Fin 2) (Fin 2) w.Completion)) j)) =
        (fun i => ψ.toRingHom (z i)) ᵥ* M := by
    intro z
    ext j

    simp only [vecMul, dotProduct, map_sum, map_mul]
    rfl
  have key : ∀ i j, (M * Mᵀ) i j = ψ (((k.1 * k.1ᵀ) i j).1 w) := by
    intro i j

    rw [entry_mul, map_sum, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul]
    rfl
  have key1 : ∀ i j, (1 : Matrix (Fin 2) (Fin 2) ℝ) i j = ψ (((1 : Matrix (Fin 2) (Fin 2) (A F)) i j).1 w) := by
    intro i j
    rw [entry_one, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h1 : Reduction.infAt w (gl k) ∈ Reduction.archCompact w ↔
      ∀ z : Fin 2 → ℝ, Reduction.euclidNorm (z ᵥ* M) = Reduction.euclidNorm z := by
    rw [Reduction.mem_archCompact]
    constructor
    · intro h z
      have hz : z = fun i => ψ.toRingHom (ψ.symm (z i)) := funext fun i => (ψ.apply_symm_apply _).symm
      rw [hz, ← e, Reduction.euclidNorm_map _ hψ, Reduction.euclidNorm_map _ hψ, h]
    · intro h z
      rw [← Reduction.euclidNorm_map _ hψ, e, h, Reduction.euclidNorm_map _ hψ]
  rw [h1, real_iff]
  constructor
  · intro h i j
    apply ψ.injective
    rw [← key, ← key1, h]
  · intro h
    ext i j
    rw [key, key1, h i j]

theorem UpperTheory.ConvolutionTheory.R2.M.kkInf :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∀ k : G1 F, InfOrth k ↔ ∀ w, Reduction.infAt w (gl k) ∈ Reduction.archCompact w := by
  intro F _ _ _ k
  simp only [place_iff, InfOrth]
  exact ⟨fun h w i j => congrFun (h i j) w, fun h i j => funext fun w => h w i j⟩
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

namespace UpperTheory.ConvolutionTheory.R2.M

variable {F : Type} [Field F] [NumberField F]

private theorem int_det {R : Type*} [CommRing R] (S : Subring R) {m : Matrix (Fin 2) (Fin 2) R}
    (h : ∀ i j, m i j ∈ S) : m.det ∈ S := by
  rw [Matrix.det_fin_two]
  exact S.sub_mem (S.mul_mem (h 0 0) (h 1 1)) (S.mul_mem (h 0 1) (h 1 0))

private theorem fin_int {k : GL (Fin 2) (A F)} (hk : k ∈ Reduction.maxCompact (K := F) (n := 2))
    (v : HeightOneSpectrum (𝓞 F)) :
    (((Matrix.GeneralLinearGroup.det k : (A F)ˣ) : A F)).2 v ∈
      (ValuativeRel.valuation (v.adicCompletion F)).integer := by
  have h := ((GLnLocal.mem_integralGL_iff _ _).1 (hk.2 v)).1
  have e := GL2Classical.det_finAt_eq v k
  have e' : (((Matrix.GeneralLinearGroup.det k : (A F)ˣ) : A F)).2 v =
      ((Reduction.finAt v k : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det := e
  rw [e']
  exact int_det _ h

private theorem inf_norm {k : GL (Fin 2) (A F)} (hk : k ∈ Reduction.maxCompact (K := F) (n := 2))
    (w : InfinitePlace F) : ‖(((Matrix.GeneralLinearGroup.det k : (A F)ˣ) : A F)).1 w‖ = 1 := by
  have e := GL2Classical.det_infAt_eq w k
  have e' : (((Matrix.GeneralLinearGroup.det k : (A F)ˣ) : A F)).1 w =
      ((Reduction.infAt w k : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion).det := e
  rw [e']
  exact Reduction.norm_det_infAt_of_mem_maxCompact hk w

private theorem dM_mem (t : (A F)ˣ) (h1 : ∀ w : InfinitePlace F, ‖((t : A F)).1 w‖ = 1)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 F), ((t : A F)).2 v ∈
      (ValuativeRel.valuation (v.adicCompletion F)).integer)
    (h3 : ∀ v : HeightOneSpectrum (𝓞 F), (((t⁻¹ : (A F)ˣ) : A F)).2 v ∈
      (ValuativeRel.valuation (v.adicCompletion F)).integer) :
    dM t ∈ Reduction.maxCompact (K := F) (n := 2) := by
  refine ⟨fun w => ?_, fun v => ?_⟩
  · intro y
    have key : Reduction.euclidNorm (y ᵥ* ((Reduction.infAt w (dM t) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion)) ^ 2 = Reduction.euclidNorm y ^ 2 := by
      rw [Reduction.euclidNorm_sq, Reduction.euclidNorm_sq, Fin.sum_univ_two, Fin.sum_univ_two]
      have a0 : (y ᵥ* ((Reduction.infAt w (dM t) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion)) 0 = y 0 := by
        simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, dM]
        exact Or.inr rfl
      have a1 : (y ᵥ* ((Reduction.infAt w (dM t) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion)) 1 = y 1 * ((t : A F)).1 w := by
        simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, dM]
        exact Or.inr rfl
      rw [a0, a1, norm_mul, h1 w, mul_one]
    exact (sq_eq_sq₀ (Reduction.euclidNorm_nonneg _) (Reduction.euclidNorm_nonneg _)).1 key
  · rw [GLnLocal.mem_integralGL_iff, ← Reduction.finAt_inv]
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [dM, h2 v] <;> change (0 : v.adicCompletion F) ∈ _ <;> exact Subring.zero_mem _
    · fin_cases i <;> fin_cases j <;> simp [dM, h3 v] <;> change (0 : v.adicCompletion F) ∈ _ <;> exact Subring.zero_mem _

end UpperTheory.ConvolutionTheory.R2.M

theorem UpperTheory.ConvolutionTheory.R2.M.detK :
    ∀ (F : Type) [Field F] [NumberField F], ∀ k ∈ Reduction.maxCompact (K := F) (n := 2), dM (Matrix.GeneralLinearGroup.det k) ∈ Reduction.maxCompact (K := F) (n := 2) ∧ ab (Matrix.GeneralLinearGroup.det k) = 1 := by
  intro F _ _ k hk
  refine ⟨dM_mem _ (inf_norm hk) (fin_int hk) fun v => ?_, ?_⟩
  · have := fin_int (inv_mem hk) v
    rwa [map_inv] at this
  · have := GJGlobal.Modulus.ideleModule_det_of_mem_maxCompact' hk
    simp [ab, this]
end
