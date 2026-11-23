module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ScalarOfMultOne
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Formalism.LocalRingCardinality.Bundle001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle009
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
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameOfHasSignature
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.OpNorm

theorem norm_le_sum_inner {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {ι : Type} [Fintype ι]
    (b : OrthonormalBasis ι ℂ W) (u : W) : ‖u‖ ≤ ∑ i, ‖⟪b i, u⟫_ℂ‖ := by
  calc ‖u‖ = ‖∑ i, ⟪b i, u⟫_ℂ • b i‖ := by rw [b.sum_repr']
    _ ≤ ∑ i, ‖⟪b i, u⟫_ℂ • b i‖ := norm_sum_le _ _
    _ = ∑ i, ‖⟪b i, u⟫_ℂ‖ := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [norm_smul, b.orthonormal.1 i, mul_one]

theorem rankOne_integral {X : Type} [MeasurableSpace X] (ν : Measure X)
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (f : X → Wp) (g : X → Wq) (hf : AEStronglyMeasurable f ν) (hg : AEStronglyMeasurable g ν) (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ (v : Wp) (w : Wq), ‖v‖ = 1 → ‖w‖ = 1 →
      ∫⁻ x, ENNReal.ofReal (‖⟪v, f x⟫_ℂ‖ * ‖⟪w, g x⟫_ℂ‖) ∂ν ≤ ENNReal.ofReal K) :
    Integrable (fun x => (innerSL ℂ (g x)).smulRight (f x)) ν ∧
      ‖∫ x, (innerSL ℂ (g x)).smulRight (f x) ∂ν‖ ≤ K := by
  haveI := FiniteDimensional.complete ℂ Wp
  set T : X → (Wq →L[ℂ] Wp) := fun x => (innerSL ℂ (g x)).smulRight (f x) with hT
  set e := stdOrthonormalBasis ℂ Wp
  set b := stdOrthonormalBasis ℂ Wq
  have hcont : Continuous (Function.uncurry fun (a : Wq) (c : Wp) => (innerSL ℂ a).smulRight c) := by
    fun_prop
  have hmeas : AEStronglyMeasurable T ν := hcont.comp_aestronglyMeasurable₂ hg hf
  have hbd : ∀ x, ‖f x‖ * ‖g x‖ ≤ ∑ j, ∑ i, ‖⟪e j, f x⟫_ℂ‖ * ‖⟪b i, g x⟫_ℂ‖ := fun x => by
    rw [← Finset.sum_mul_sum]
    exact mul_le_mul (norm_le_sum_inner e _) (norm_le_sum_inner b _) (norm_nonneg _)
      (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hnormT : ∀ x, ‖T x‖ = ‖g x‖ * ‖f x‖ := fun x => by
    simp only [hT, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
  have hterm : ∀ j i, AEMeasurable
      (fun x => ENNReal.ofReal (‖⟪e j, f x⟫_ℂ‖ * ‖⟪b i, g x⟫_ℂ‖)) ν := fun j i =>
    ((aestronglyMeasurable_const.inner hf).norm.mul
      (aestronglyMeasurable_const.inner hg).norm).aemeasurable.ennreal_ofReal
  have hfin : (∫⁻ x, ENNReal.ofReal ‖T x‖ ∂ν) < ⊤ := by
    calc (∫⁻ x, ENNReal.ofReal ‖T x‖ ∂ν)
        ≤ ∫⁻ x, ∑ j, ∑ i, ENNReal.ofReal (‖⟪e j, f x⟫_ℂ‖ * ‖⟪b i, g x⟫_ℂ‖) ∂ν := by
          refine lintegral_mono fun x => ?_
          rw [hnormT, mul_comm]
          refine (ENNReal.ofReal_le_ofReal (hbd x)).trans (le_of_eq ?_)
          rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity]
          exact Finset.sum_congr rfl fun j _ => ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity
      _ = ∑ j, ∑ i, ∫⁻ x, ENNReal.ofReal (‖⟪e j, f x⟫_ℂ‖ * ‖⟪b i, g x⟫_ℂ‖) ∂ν := by
          have hsum : ∀ j, AEMeasurable
              (fun x => ∑ i, ENNReal.ofReal (‖⟪e j, f x⟫_ℂ‖ * ‖⟪b i, g x⟫_ℂ‖)) ν := by
            intro j
            first
              | exact Finset.aemeasurable_fun_sum _ fun i _ => hterm j i
              | exact Finset.aemeasurable_sum' _ fun i _ => hterm j i
              | exact (Finset.aemeasurable_sum _ fun i _ => hterm j i).congr
                  (Filter.Eventually.of_forall fun x => by simp [Finset.sum_apply])
          rw [MeasureTheory.lintegral_finsetSum' _ fun j _ => hsum j]
          exact Finset.sum_congr rfl fun j _ => MeasureTheory.lintegral_finsetSum' _ fun i _ => hterm j i
      _ ≤ ∑ j, ∑ i, ENNReal.ofReal K :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ =>
            h (e j) (b i) (e.orthonormal.1 j) (b.orthonormal.1 i)
      _ < ⊤ := by simp [ENNReal.mul_lt_top]
  have hi : Integrable T ν := ⟨hmeas, hasFiniteIntegral_iff_norm _ |>.2 hfin⟩
  refine ⟨hi, ?_⟩
  have key : ∀ (v : Wp) (w : Wq), ‖v‖ = 1 → ‖w‖ = 1 → ‖⟪v, (∫ x, T x ∂ν) w⟫_ℂ‖ ≤ K := by
    intro v w hv hw
    rw [ContinuousLinearMap.integral_apply hi w, ← integral_inner (hi.apply_continuousLinearMap w) v]
    refine (norm_integral_le_lintegral_norm _).trans (ENNReal.toReal_le_of_le_ofReal hK ?_)
    refine le_trans (le_of_eq (lintegral_congr fun x => ?_)) (h v w hv hw)
    show ENNReal.ofReal ‖⟪v, ⟪g x, w⟫_ℂ • f x⟫_ℂ‖ = ENNReal.ofReal (‖⟪v, f x⟫_ℂ‖ * ‖⟪w, g x⟫_ℂ‖)
    rw [inner_smul_right, norm_mul, norm_inner_symm, mul_comm]
  refine ContinuousLinearMap.opNorm_le_of_unit_norm hK fun w hw => ?_
  set y := (∫ x, T x ∂ν) w
  by_cases hy : y = 0
  · rw [hy, norm_zero]; exact hK
  have hy' : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hv : ‖((‖y‖⁻¹ : ℝ) : ℂ) • y‖ = 1 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hy'), inv_mul_cancel₀ hy'.ne']
  have hk := key _ w hv hw
  rw [inner_smul_left, norm_mul, Complex.conj_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 hy'), inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm] at hk
  calc ‖y‖ = ‖y‖⁻¹ * ‖y‖ ^ 2 := by rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hy'.ne', one_mul]
    _ ≤ K := hk

private theorem mul_mem_dualWeyl_complex {k r : ℕ} {a b : Mat k r} (ha : a ∈ GG k r) (hb : b ∈ GG k r) :
    a * b ∈ GG k r := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  calc (a * b)ᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

private theorem measurableSet_of_isOpen' (k r : ℕ) : MeasurableSet {x : Mt k r | Matrix.of x ∈ GG k r} := by
  have hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  have hc : IsClosed {x : Mt k r | (Matrix.of x)ᴴ * Hpk k r * Matrix.of x = Hpk k r} :=
    isClosed_eq ((hof.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hof) continuous_const
  exact hc.measurableSet

theorem integrable_and_norm_ampJ_le : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (ν : Measure (Mt k r)) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq) (γ : Mat k r) (c K : ℝ), γ ∈ GG k r → ν {x | Matrix.of x ∉ GG k r} = 0 → ContinuousOn Φ (GG k r) → ContinuousOn Φ' (GG k r) → 0 < c → 0 ≤ K → (∀ (v : Wp) (w : Wq), ‖v‖ = 1 → ‖w‖ = 1 → ∫⁻ x, ENNReal.ofReal (‖⟪v, Φ (γ * Matrix.of x)⟫_ℂ‖ * ‖⟪w, Φ' (Matrix.of x)⟫_ℂ‖) ∂ν ≤ ENNReal.ofReal K) → Integrable (fun x => (innerSL ℂ (Φ' (Matrix.of x))).smulRight (Φ (γ * Matrix.of x))) ν ∧ ‖(haveI := FiniteDimensional.complete ℂ Wp; ampJ ν c Φ Φ' γ)‖ ≤ K / c := by
  intro k r Wp _ _ _ Wq _ _ _ ν Φ Φ' γ c K hγ hν hΦ hΦ' hc hK h
  haveI := FiniteDimensional.complete ℂ Wp
  have hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  have hS := measurableSet_of_isOpen' k r
  have hae : ν.restrict {x : Mt k r | Matrix.of x ∈ GG k r} = ν :=
    Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hν)
  have hf : AEStronglyMeasurable (fun x : Mt k r => Φ (γ * Matrix.of x)) ν := by
    rw [← hae]
    exact (hΦ.comp (continuous_const.mul hof).continuousOn fun x hx => mul_mem_dualWeyl_complex hγ hx).aestronglyMeasurable hS
  have hg : AEStronglyMeasurable (fun x : Mt k r => Φ' (Matrix.of x)) ν := by
    rw [← hae]
    exact (hΦ'.comp hof.continuousOn fun x hx => hx).aestronglyMeasurable hS
  obtain ⟨hi, hn⟩ := rankOne_integral ν _ _ hf hg K hK h
  refine ⟨hi, ?_⟩
  simp only [ampJ, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hn (inv_nonneg.2 hc.le)

end GlobalTheory.Amp.OpNorm
end

section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder

noncomputable section
namespace GlobalTheory.Dec.PermGroup
variable {n : ℕ}

lemma memLp_equiv {ε ε' : Fin n → Bool} (e : UJ ε' ≃ₜ* UJ ε) (F : UJ ε → ℂ) (p : ENNReal) :
    MemLp F p (muG ε) ↔ MemLp (fun g => F (e g)) p (muG ε') := by
  have hE : (Measure.map e (muG ε')).IsHaarMeasure := e.isHaarMeasure_map (muG ε')
  have hc : Measure.map e (muG ε') =
      Measure.haarScalarFactor (Measure.map e (muG ε')) (muG ε) • muG ε := Measure.isMulLeftInvariant_eq_smul _ _
  set c : ENNReal := ((Measure.haarScalarFactor (Measure.map e (muG ε')) (muG ε) : NNReal) : ENNReal)
    with hcdef
  have hc' : Measure.map e (muG ε') = c • muG ε := by rw [hcdef, ← ENNReal.smul_def]; exact hc
  have hT : c ≠ ⊤ := ENNReal.coe_ne_top
  have h0 : c ≠ 0 := by
    intro hz
    have hz' : Measure.map e (muG ε') = 0 := by rw [hc', hz, zero_smul]
    rw [Measure.map_eq_zero_iff
      (show AEMeasurable (⇑e) (muG ε') from (map_continuous e).measurable.aemeasurable)] at hz'
    exact NeZero.ne _ hz'
  have hm := (e.toHomeomorph.toMeasurableEquiv).memLp_map_measure_iff (g := F) (p := p) (μ := muG ε')
  change MemLp F p (Measure.map e (muG ε')) ↔ MemLp (F ∘ e) p (muG ε') at hm
  change MemLp F p (muG ε) ↔ MemLp (F ∘ e) p (muG ε')
  rw [← hm, hc']
  constructor
  · intro h
    exact h.smul_measure hT
  · intro h
    have h' := h.smul_measure (ENNReal.inv_ne_top.2 h0)
    rwa [smul_smul, ENNReal.inv_mul_cancel h0 hT, one_smul] at h'

def homUJ {ε ε' : Fin n → Bool} (φ : Matrix (Fin n) (Fin n) ℂ →* Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ g ∈ UJset ε', φ g ∈ UJset ε) : UJ ε' →* UJ ε :=
  ((Units.map φ).comp (UJ ε').subtype).codRestrict (UJ ε) fun g => h _ g.2

lemma homUJ_cont {ε ε' : Fin n → Bool} (φ : Matrix (Fin n) (Fin n) ℂ →* Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ g ∈ UJset ε', φ g ∈ UJset ε) (hc : Continuous φ) : Continuous (homUJ φ h) := by
  refine continuous_induced_rng.2 ?_
  rw [Units.continuous_iff]
  exact ⟨hc.comp (Units.continuous_val.comp continuous_subtype_val),
    hc.comp (Units.continuous_coe_inv.comp continuous_subtype_val)⟩

lemma memLp_hom {ε ε' : Fin n → Bool} (φ ψ : Matrix (Fin n) (Fin n) ℂ →* Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ g ∈ UJset ε', φ g ∈ UJset ε) (h' : ∀ g ∈ UJset ε, ψ g ∈ UJset ε')
    (hc : Continuous φ) (hc' : Continuous ψ) (h1 : ∀ g, ψ (φ g) = g) (h2 : ∀ g, φ (ψ g) = g)
    (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (p : ENNReal) :
    MemLp (fun g : UJ ε => f (umat g)) p (muG ε) ↔
      MemLp (fun g : UJ ε' => f (φ (umat g))) p (muG ε') := by
  let e : UJ ε' ≃ₜ* UJ ε :=
    { toFun := homUJ φ h
      invFun := homUJ ψ h'
      left_inv := fun g => Subtype.ext (Units.ext (h1 ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)))
      right_inv := fun g => Subtype.ext (Units.ext (h2 ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)))
      map_mul' := fun a b => map_mul (homUJ φ h) a b
      continuous_toFun := homUJ_cont φ h hc
      continuous_invFun := homUJ_cont ψ h' hc' }
  exact memLp_equiv e (fun g => f (umat g)) p

def perm (s : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℂ ≃+* Matrix (Fin n) (Fin n) ℂ :=
  (Matrix.reindexAlgEquiv ℂ ℂ s).toRingEquiv

lemma perm_apply (s : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) :
    perm s g = g.submatrix s.symm s.symm := rfl

lemma perm_cont (s : Equiv.Perm (Fin n)) : Continuous (perm s) := by
  have h : ⇑(perm s) = fun g => g.submatrix s.symm s.symm := funext (perm_apply s)
  rw [h]
  exact continuous_id.matrix_submatrix _ _

lemma perm_ct (s : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) : (perm s g)ᴴ = perm s gᴴ := rfl

lemma perm_Jm (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)) : Jm ε = perm s (Jm (ε ∘ s)) := by
  rw [perm_apply]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Jm]
  · have hij' : s.symm i ≠ s.symm j := fun h => hij (s.symm.injective h)
    simp [Jm, hij, hij']

lemma perm_UJ (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) :
    g ∈ UJset (ε ∘ s) ↔ perm s g ∈ UJset ε := by
  simp only [UJset, Set.mem_ofPred_eq, inUJ]
  rw [perm_ct, perm_Jm ε s]
  simp only [← map_mul]
  exact (perm s).injective.eq_iff.symm

lemma perm_K (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) :
    g ∈ Kset (ε ∘ s) ↔ perm s g ∈ Kset ε := by
  simp only [Kset, Set.mem_ofPred_eq, Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  rw [perm_ct, perm_Jm ε s]
  simp only [← map_mul, EmbeddingLike.map_eq_one_iff, (perm s).injective.eq_iff]

lemma perm_P (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) :
    inP (ε ∘ s) g ↔ inP ε (perm s g) := by
  simp only [inP, inG]
  rw [perm_ct, perm_Jm ε s]
  simp only [← map_mul, ← map_add (f := _), ← map_neg, EmbeddingLike.map_eq_zero_iff,
    (perm s).injective.eq_iff]

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
lemma perm_exp (s : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp (perm s g) = perm s (NormedSpace.exp g) := (NormedSpace.map_exp (perm s) (perm_cont s) g).symm

def permM (s : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℂ →* Matrix (Fin n) (Fin n) ℂ where
  toFun g := g.submatrix s.symm s.symm
  map_one' := map_one (perm s)
  map_mul' := map_mul (perm s)

lemma permM_symm (s : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) :
    permM s.symm (permM s g) = g := by
  show (g.submatrix s.symm s.symm).submatrix s.symm.symm s.symm.symm = g
  ext i j
  simp

lemma permM_symm' (s : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) :
    permM s (permM s.symm g) = g := by
  show (g.submatrix s.symm.symm s.symm.symm).submatrix s.symm s.symm = g
  ext i j
  simp

def conj : Matrix (Fin n) (Fin n) ℂ →* Matrix (Fin n) (Fin n) ℂ where
  toFun g := g.map star
  map_one' := FormF.map_star_one
  map_mul' := FormF.map_star_mul

lemma conj_cont : Continuous (conj (n := n)) := by
  show Continuous fun g : Matrix (Fin n) (Fin n) ℂ => g.map star
  exact continuous_id.matrix_map continuous_star

theorem permGroup : ∀ (n : ℕ) (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)), (∀ g : Matrix (Fin n) (Fin n) ℂ, (g ∈ UJset (ε ∘ s) ↔ g.submatrix s.symm s.symm ∈ UJset ε) ∧ (g ∈ Kset (ε ∘ s) ↔ g.submatrix s.symm s.symm ∈ Kset ε) ∧ (inP (ε ∘ s) g ↔ inP ε (g.submatrix s.symm s.symm)) ∧ NormedSpace.exp (g.submatrix s.symm s.symm) = (NormedSpace.exp g).submatrix s.symm s.symm) ∧ ∀ (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (p : ENNReal), (MemLp (fun g : UJ ε => f (umat g)) p (muG ε) ↔ MemLp (fun g : UJ (ε ∘ s) => f ((umat g).submatrix s.symm s.symm)) p (muG (ε ∘ s))) ∧ (MemLp (fun g : UJ ε => f (umat g)) p (muG ε) ↔ MemLp (fun g : UJ ε => f ((umat g).map star)) p (muG ε)) := by
  intro n ε s
  have hpm : ∀ (t : Equiv.Perm (Fin n)) (x : Matrix (Fin n) (Fin n) ℂ), permM t x = perm t x :=
    fun t x => (perm_apply t x).symm
  have hcont : ∀ t : Equiv.Perm (Fin n), Continuous (permM t) := fun t => by
    have h : ⇑(permM t) = ⇑(perm t) := funext (hpm t)
    rw [h]
    exact perm_cont t
  refine ⟨fun g => ⟨?_, ?_, ?_, ?_⟩, fun f p => ⟨?_, ?_⟩⟩
  · rw [← perm_apply]; exact perm_UJ ε s g
  · rw [← perm_apply]; exact perm_K ε s g
  · rw [← perm_apply]; exact perm_P ε s g
  · rw [← perm_apply, ← perm_apply]; exact perm_exp s g
  · refine memLp_hom (permM s) (permM s.symm) (fun g hg => ?_) (fun g hg => ?_) (hcont s)
      (hcont s.symm) (permM_symm s) (permM_symm' s) f p
    · rw [hpm]; exact (perm_UJ ε s g).1 hg
    · apply (perm_UJ ε s _).2
      rw [← hpm, permM_symm']
      exact hg
  · exact memLp_hom GlobalTheory.Dec.PermGroup.conj GlobalTheory.Dec.PermGroup.conj (fun g hg => FormF.UJ_star hg)
      (fun g hg => FormF.UJ_star hg) conj_cont conj_cont (fun g => FormF.map_star_star g)
      (fun g => FormF.map_star_star g) f p

end GlobalTheory.Dec.PermGroup
end
end

section

open Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Count.Cartan

noncomputable section

namespace GlobalTheory.Dec

theorem dOp_fin_zero (g : Matrix (Fin 0) (Fin 0) ℂ) : dOp g = 0 := by

  rw [Subsingleton.elim g 0]
  simp [GlobalTheory.Count.dOp]

private theorem isHermitian_of_inP {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : Formalism.REAL.inP ε X) : X.IsHermitian := by
  have hX' : Formalism.REAL.inG ε X ∧ X * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X) := hX
  have hG : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := hX'.1
  have h1 : Xᴴ * Formalism.REAL.Jm ε = X * Formalism.REAL.Jm ε := by
    rw [hX'.2]
    exact eq_neg_of_add_eq_zero_left hG
  have h2 := congrArg (· * Formalism.REAL.Jm ε) h1
  simp only [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one] at h2
  exact h2

private theorem isUnit_of_inUJ_flag_measures' {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : Formalism.REAL.inUJ ε g) : IsUnit g := by
  have hg' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  have h : (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', Formalism.REAL.Jm_mul_self]
  exact (Matrix.isUnit_iff_isUnit_det g).mpr (Matrix.isUnit_det_of_left_inverse h)

private theorem dOp_one' {n : ℕ} (hn : 1 ≤ n) (ε : Fin n → Bool) :
    dOp (1 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  have hP : Formalism.REAL.inP ε 0 := by simp [Formalism.REAL.inP, Formalism.REAL.inG]
  obtain ⟨h0, h1, -⟩ := GlobalTheory.Count.Cartan.dOp_bounds hn (Matrix.unitaryGroup (Fin n) ℂ).one_mem hP
  have hs0 : Formalism.REAL.hs (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by simp [Formalism.REAL.hs]
  simp only [NormedSpace.exp_zero, Matrix.mul_one] at h0 h1
  rw [hs0, Real.sqrt_zero] at h1
  have hs2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hle : dOp (1 : Matrix (Fin n) (Fin n) ℂ) ≤ 0 := by
    by_contra h
    have := mul_pos hs2 (lt_of_not_ge h)
    linarith
  exact le_antisymm hle h0

theorem dFacts_holds : DFacts := by
  intro n ε
  rcases Nat.eq_zero_or_pos n with rfl | hn
  ·
    refine ⟨fun g _ => ⟨by rw [dOp_fin_zero], by rw [dOp_fin_zero, dOp_fin_zero],
      fun g' _ => by rw [dOp_fin_zero, dOp_fin_zero, dOp_fin_zero, add_zero],
      fun k₁ _ k₂ _ => by rw [dOp_fin_zero, dOp_fin_zero]⟩,
      GlobalTheory.Count.Cartan.continuousOn_dOp ε, fun k hk X hX => ⟨?_, ?_, ?_⟩⟩
    · exact GlobalTheory.Count.Cartan.dHS_polar hk.1 (isHermitian_of_inP hX)
    · rw [dOp_fin_zero, mul_zero]
      exact Real.sqrt_nonneg _
    · rw [dOp_fin_zero, mul_zero]
      simp [Formalism.REAL.hs]
  · refine ⟨fun g hg => ?_, GlobalTheory.Count.Cartan.continuousOn_dOp ε, fun k hk X hX => ?_⟩
    · have hgU : Formalism.REAL.inUJ ε g := hg
      have hu := isUnit_of_inUJ_flag_measures' hgU
      refine ⟨?_, GlobalTheory.Count.Cartan.dOp_inv hgU,
        fun g' hg' => GlobalTheory.Count.Cartan.dOp_mul_le hn hu (isUnit_of_inUJ_flag_measures' hg'),
        fun k₁ hk₁ k₂ hk₂ => GlobalTheory.Count.Cartan.dOp_unitary hk₁.1 hk₂.1 g⟩

      have hdet : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).mp hu
      have hinv : IsUnit g⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hu
      have h := GlobalTheory.Count.Cartan.dOp_mul_le hn hu hinv
      rw [Matrix.mul_nonsing_inv g hdet, dOp_one' hn ε, GlobalTheory.Count.Cartan.dOp_inv hgU] at h
      linarith
    · obtain ⟨-, h1, h2⟩ := GlobalTheory.Count.Cartan.dOp_bounds hn hk.1 hX
      exact ⟨GlobalTheory.Count.Cartan.dHS_polar hk.1 (isHermitian_of_inP hX), h1, h2⟩

end GlobalTheory.Dec
end
end

section

noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CellDens

def lev (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℕ :=
  if i.val < r then i.val else if i.val ≤ r + k then r else i.val - k

def wC (k r : ℕ) : Mat k r := bigCell k r (fun _ => 1) 1

def torD (k r : ℕ) (x : Fin r → ℂ) : Mat k r := Matrix.diagonal fun i =>
  if h : i.val < r then x ⟨i.val, h⟩
  else if h' : r + k < i.val then -star (x ⟨2 * r + k - i.val, by omega⟩) else 0

def um {m : ℕ} {S : Set (Matrix (Fin m) (Fin m) ℂ)} (X : lieE S) : Matrix (Fin m) (Fin m) ℂ :=
  unrealify (X : EuclideanSpace ℝ (Fin m × Fin m × Bool))

abbrev EE (k r : ℕ) : Type :=
  (lieE (Nset k r) × lieE (Nset k r)) × ((Fin r → ℂ) × lieE (Formalism.FourierDecayAlt.B2.UWb k r))

def chart (k r : ℕ) (v : EE k r) : Mat k r :=
  wC k r * (NormedSpace.exp (-um v.1.1) * bigCell k r (fun a => 1 + v.2.1 a) 1 * NormedSpace.exp (um v.2.2) *
    NormedSpace.exp (um v.1.2))

def dchart (k r : ℕ) (v : EE k r) : Mat k r :=
  -(wC k r * um v.1.1 * wC k r) + torD k r v.2.1 + um v.2.2 + um v.1.2

end GlobalTheory.CellDens
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.StdDefinite

open GlobalTheory.AutInhab

theorem cmData_maximalRealSubfield {K : Type} [Field K] [NumberField K] [StarRing K]
    (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) : Formalism.BasicNotions.CMData (maximalRealSubfield K) K := by
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hne : ∃ z : K, star z ≠ z := by
    by_contra hcon
    push Not at hcon
    haveI := hK.1
    refine IsTotallyComplex.complexEmbedding_not_isReal σ ?_
    rw [ComplexEmbedding.isReal_iff]
    ext z
    rw [ComplexEmbedding.conjugate_coe_eq, ← hK.2.1, hcon]
  haveI : IsCMField K := GlobalTheory.LeastExponentCompare.isCMField_of_conj K star hK.2.1 hne
  refine ⟨hK, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ _, fun a => ⟨fun h => ?_, ?_⟩⟩
  · refine ⟨⟨a, fun φ => ?_⟩, rfl⟩
    have := hK.2.1 φ a
    rw [h] at this
    exact this.symm
  · rintro ⟨b, rfl⟩
    apply σ.injective
    rw [hK.2.1]
    exact b.2 σ

end GlobalTheory.StdDefinite
end
end
