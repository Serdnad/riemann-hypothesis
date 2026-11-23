module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomain
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SecondLabelsNonempty
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle096
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finset.Functor
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec

private lemma exp_mul_exp_neg_eq_shell (a : ℝ) (r : ℕ) :
    Real.exp (2 * a * (r + 1)) * Real.exp (-(4 * a * r)) =
      Real.exp (2 * a) * Real.exp (-(2 * a)) ^ r := by
  rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem shell_sum_majorant : ∀ (n q : ℕ) (h : ℝ), 1 ≤ n → 1 ≤ q → 32 * (n : ℝ) ^ 2 * Real.sqrt q ≤ h → AntitoneOn (decE q h) (Set.Ici 0) ∧ (∀ r : ℕ, decE q h r ≤ Real.exp (-(4 * (n : ℝ) ^ 2 * r))) ∧ Summable (fun r : ℕ => Real.exp (2 * (n : ℝ) ^ 2 * (r + 1)) * Real.exp (-(4 * (n : ℝ) ^ 2 * r))) ∧ ∑' r : ℕ, Real.exp (2 * (n : ℝ) ^ 2 * (r + 1)) * Real.exp (-(4 * (n : ℝ) ^ 2 * r)) ≤ 2 * Real.exp (2 * (n : ℝ) ^ 2) := by
  intro n q h hn hq hh
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hsq : 1 ≤ Real.sqrt (q : ℝ) := Real.one_le_sqrt.mpr hq1
  have hsqpos : 0 < Real.sqrt (q : ℝ) := by linarith
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hh0 : 0 ≤ h := by
    have : 0 ≤ 32 * (n : ℝ) ^ 2 * Real.sqrt q := by positivity
    linarith
  have hgeo := fun r : ℕ => exp_mul_exp_neg_eq_shell ((n : ℝ) ^ 2) r
  have h3 : 3 ≤ Real.exp (2 * (n : ℝ) ^ 2) := by
    linarith [Real.add_one_le_exp (2 * (n : ℝ) ^ 2)]
  have he0 : 0 ≤ Real.exp (-(2 * (n : ℝ) ^ 2)) := (Real.exp_pos _).le
  have he : Real.exp (-(2 * (n : ℝ) ^ 2)) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro x hx y hy hxy
    simp only [Set.mem_Ici] at hx hy
    unfold GlobalTheory.Count.decE
    apply Real.exp_le_exp.mpr
    have hm : min (2 * x ^ 2) (x / Real.sqrt q) ≤ min (2 * y ^ 2) (y / Real.sqrt q) := by
      apply min_le_min
      · nlinarith
      · exact div_le_div_of_nonneg_right hxy hsqpos.le
    rw [neg_mul, neg_mul, neg_le_neg_iff]
    exact mul_le_mul_of_nonneg_left hm (by positivity)
  ·
    intro r
    unfold GlobalTheory.Count.decE
    apply Real.exp_le_exp.mpr
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      simp
    · have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
      have hmin : min (2 * (r : ℝ) ^ 2) (r / Real.sqrt q) = r / Real.sqrt q := by
        apply min_eq_right
        have : (r : ℝ) / Real.sqrt q ≤ r := div_le_self (by linarith) hsq
        nlinarith
      rw [hmin, neg_mul]
      apply neg_le_neg
      have hd : 32 * (n : ℝ) ^ 2 ≤ h / Real.sqrt q := by
        rw [le_div_iff₀ hsqpos]
        exact hh
      have := mul_le_mul_of_nonneg_right hd (by linarith : (0 : ℝ) ≤ r)
      have hdiv : h / 8 * (r / Real.sqrt q) = h / Real.sqrt q * r / 8 := by ring
      rw [hdiv]
      linarith
  · rw [funext hgeo]
    exact (summable_geometric_of_lt_one he0 (by linarith)).mul_left _
  ·
    rw [funext hgeo, tsum_mul_left, tsum_geometric_of_lt_one he0 (by linarith)]
    have hinv : (1 - Real.exp (-(2 * (n : ℝ) ^ 2)))⁻¹ ≤ 2 := by
      rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
      linarith
    have := mul_le_mul_of_nonneg_left hinv (Real.exp_pos (2 * (n : ℝ) ^ 2)).le
    linarith

end GlobalTheory.Dec
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.AdelicUnfold

theorem unfold_smul {Γ X : Type} [Group Γ] [Countable Γ] [MulAction Γ X] [MeasurableSpace X]
    [MeasurableConstSMul Γ X] (μ : Measure X) [SMulInvariantMeasure Γ X μ] {s : Set X}
    (hs : IsFundamentalDomain Γ s μ) (f : X → ℂ) (hf : Integrable f μ) :
    IntegrableOn (fun z => ∑' γ : Γ, f (γ • z)) s μ ∧
      ∫ z, f z ∂μ = ∫ z in s, ∑' γ : Γ, f (γ • z) ∂μ := by
  classical
  have hmeas : ∀ γ : Γ, AEStronglyMeasurable (fun z => f (γ • z)) μ := fun γ =>
    hf.aestronglyMeasurable.comp_measurePreserving (measurePreserving_smul γ μ)
  have hfin : ∑' γ : Γ, ∫⁻ z in s, ‖f (γ • z)‖ₑ ∂μ ≠ ⊤ := by
    rw [← hs.lintegral_eq_tsum'' (fun z => ‖f z‖ₑ)]
    exact hf.hasFiniteIntegral.ne
  have hae : ∀ᵐ z ∂μ.restrict s, ∑' γ : Γ, ‖f (γ • z)‖ₑ < ⊤ := by
    apply ae_lt_top' (AEMeasurable.tsum fun γ => (hmeas γ).restrict.enorm)
    rw [lintegral_tsum fun γ => (hmeas γ).restrict.enorm]
    exact hfin
  have hsm : ∀ᵐ z ∂μ.restrict s, Summable fun γ : Γ => f (γ • z) := by
    filter_upwards [hae] with z hz
    exact Summable.of_norm (tsum_enorm_ne_top_iff_summable_norm.1 hz.ne)
  have hasm : AEStronglyMeasurable (fun z => ∑' γ : Γ, f (γ • z)) (μ.restrict s) := by
    refine aestronglyMeasurable_of_tendsto_ae (u := (Filter.atTop : Filter (Finset Γ)))
      (f := fun t z => ∑ γ ∈ t, f (γ • z)) (fun t => ?_) ?_
    · convert Finset.aestronglyMeasurable_sum t (fun γ _ => (hmeas γ).restrict) using 1
      ext z
      simp [Finset.sum_apply]
    · filter_upwards [hsm] with z hz using hz.hasSum
  refine ⟨⟨hasm, ?_⟩, ?_⟩
  · calc ∫⁻ z in s, ‖∑' γ : Γ, f (γ • z)‖ₑ ∂μ ≤ ∫⁻ z in s, ∑' γ : Γ, ‖f (γ • z)‖ₑ ∂μ :=
          lintegral_mono fun z => enorm_tsum_le_tsum_enorm
      _ = ∑' γ : Γ, ∫⁻ z in s, ‖f (γ • z)‖ₑ ∂μ :=
          lintegral_tsum fun γ => (hmeas γ).restrict.enorm
      _ < ⊤ := hfin.lt_top
  · rw [integral_tsum (fun γ => (hmeas γ).restrict) hfin]
    exact hs.integral_eq_tsum'' f hf

theorem measurePreserving_left (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf]
    (g : I.GA) : MeasurePreserving (fun z => g * z) (I.muA μf) (I.muA μf) := by
  unfold AutInst.muA
  have h0 : ∀ v, (muG (I.ε v)).IsMulLeftInvariant := fun v => inferInstance
  have h1 : (Measure.pi fun v => muG (I.ε v)).IsMulLeftInvariant := inferInstance
  have h2 : ((Measure.pi fun v => muG (I.ε v)).prod μf).IsMulLeftInvariant := inferInstance
  exact measurePreserving_mul_left _ g

theorem integral_unfold_kernel : ∀ (B : RowsAut) (φ F : B.I.GA → ℂ) (x : B.I.GA), (∀ᵐ z ∂(B.I.muA B.μf), ∀ γ ∈ B.I.GFset, F (γ * z) = F z) → Integrable (fun g => φ g * F (x * g)) (B.I.muA B.μf) → IntegrableOn (fun z => kern B.I φ x z * F z) B.fund (B.I.muA B.μf) ∧ ∫ g, φ g * F (x * g) ∂(B.I.muA B.μf) = ∫ z in B.fund, kern B.I φ x z * F z ∂(B.I.muA B.μf) := by
  intro B φ F x hF hint
  have := B.haar
  have := B.sf
  have hcount : Countable (GlobalTheory.RatDiscrete.ratSub B.I) := by
    have := (GlobalTheory.RatDiscrete.countable_GFset B.I).to_subtype
    exact this
  have : MeasurableConstSMul (GlobalTheory.RatDiscrete.ratSub B.I) B.I.GA :=
    ⟨fun γ => (measurePreserving_left B.I B.μf γ.1).measurable⟩
  have : SMulInvariantMeasure (GlobalTheory.RatDiscrete.ratSub B.I) B.I.GA (B.I.muA B.μf) :=
    ⟨fun γ A hA => (measurePreserving_left B.I B.μf γ.1).measure_preimage hA.nullMeasurableSet⟩
  have hfd : IsFundamentalDomain (GlobalTheory.RatDiscrete.ratSub B.I) B.fund (B.I.muA B.μf) :=
    GlobalTheory.RatDiscrete.isFundamentalDomain B.I B.μf B.fund B.fund_spec

  have hh : Integrable (fun z => φ (x⁻¹ * z) * F z) (B.I.muA B.μf) := by
    have := ((measurePreserving_left B.I B.μf x⁻¹).integrable_comp hint.aestronglyMeasurable).2 hint
    convert this using 1
    ext z
    simp [Function.comp, mul_inv_cancel_left]
  have hB : ∫ g, φ g * F (x * g) ∂(B.I.muA B.μf) = ∫ z, φ (x⁻¹ * z) * F z ∂(B.I.muA B.μf) := by
    have hmp := measurePreserving_left B.I B.μf x
    have e := integral_map hmp.measurable.aemeasurable
      (f := fun z => φ (x⁻¹ * z) * F z) (by rw [hmp.map_eq]; exact hh.aestronglyMeasurable)
    rw [hmp.map_eq] at e
    rw [e]
    congr 1
    ext g
    simp [inv_mul_cancel_left]

  have hD : (fun z => ∑' γ : GlobalTheory.RatDiscrete.ratSub B.I, φ (x⁻¹ * (γ.1 * z)) * F (γ.1 * z))
      =ᵐ[(B.I.muA B.μf).restrict B.fund] fun z => kern B.I φ x z * F z := by
    filter_upwards [ae_restrict_of_ae (s := B.fund) hF] with z hz
    unfold kern
    have hγ : ∀ γ : GlobalTheory.RatDiscrete.ratSub B.I,
        φ (x⁻¹ * (γ.1 * z)) * F (γ.1 * z) = φ (x⁻¹ * γ.1 * z) * F z := fun γ => by
      rw [hz γ.1 γ.2, mul_assoc]
    rw [tsum_congr hγ, tsum_mul_right]
    rfl
  obtain ⟨hI, hE⟩ := unfold_smul (B.I.muA B.μf) hfd (fun z => φ (x⁻¹ * z) * F z) hh
  refine ⟨hI.congr hD, ?_⟩
  rw [hB, hE]
  exact integral_congr_ae hD

end GlobalTheory.AdelicUnfold
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.WUnfold

variable {k r : ℕ}

theorem mul_mem_GG_iff {s x : Mat k r} (hs : s ∈ GG k r) : s * x ∈ GG k r ↔ x ∈ GG k r := by
  have hs' : sᴴ * Hpk k r * s = Hpk k r := hs
  have : (s * x)ᴴ * Hpk k r * (s * x) = xᴴ * Hpk k r * x := by
    rw [Matrix.conjTranspose_mul]
    calc xᴴ * sᴴ * Hpk k r * (s * x) = xᴴ * (sᴴ * Hpk k r * s) * x := by
          simp only [Matrix.mul_assoc]
      _ = xᴴ * Hpk k r * x := by rw [hs']
  show (s * x)ᴴ * Hpk k r * (s * x) = Hpk k r ↔ xᴴ * Hpk k r * x = Hpk k r
  rw [this]

theorem Sset_subset (z : Fin (2 * r + k + 1) → ℂ) : Sset k r z ⊆ GG k r := by
  rintro s ⟨h, hh, m, hm, rfl⟩
  exact (mul_mem_GG_iff hh.1).2 hm.1

theorem measurableSet_not_GG : MeasurableSet {x : Mt k r | Matrix.of x ∉ GG k r} := by
  have hc : IsClosed {x : Mat k r | xᴴ * Hpk k r * x = Hpk k r} :=
    isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
      continuous_id) continuous_const
  have hc' : IsClosed {x : Mt k r | Matrix.of x ∈ GG k r} := hc
  exact hc'.measurableSet.compl

theorem ae_mem_GG {z : Fin (2 * r + k + 1) → ℂ} {μG μS ν : Measure (Mt k r)}
    (hG : IsHaarOn (GG k r) μG) (hS : IsHaarOn (Sset k r z) μS) (hq : IsQuotMeas μG μS ν) :
    ∀ᵐ x ∂ν, Matrix.of x ∈ GG k r := by
  set U : Set (Mt k r) := {x | Matrix.of x ∉ GG k r} with hU
  have hUm : MeasurableSet U := measurableSet_not_GG
  have haeS : ∀ᵐ s ∂μS, Matrix.of s ∈ Sset k r z := hS.2.2.1
  have h1 := hq (U.indicator 1) (measurable_const.indicator hUm)
  rw [lintegral_indicator_one hUm, hG.2.2.1] at h1
  have h2 : ∫⁻ x, U.indicator (fun _ => μS Set.univ) x ∂ν ≤ 0 := by
    rw [h1]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ U
    · rw [Set.indicator_of_mem hx, ← lintegral_one]
      refine lintegral_mono_ae (haeS.mono fun s hs => ?_)
      have : (fun i j => (Matrix.of s * Matrix.of x) i j : Mt k r) ∈ U := fun h =>
        hx ((mul_mem_GG_iff (Sset_subset z hs)).1 h)
      rw [Set.indicator_of_mem this]; rfl
    · rw [Set.indicator_of_notMem hx]; exact zero_le
  rw [lintegral_indicator_const hUm, nonpos_iff_eq_zero, mul_eq_zero] at h2
  rcases h2 with h | h
  · exact absurd (Measure.measure_univ_eq_zero.1 h) hS.2.1
  · exact h

end GlobalTheory.SgInf.WUnfold
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem fdegH_eq_of_schurH (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)) (μG : Measure (Mt k r)) (d : ℝ) (w : H)
    (hS : SchurH μG σ d) (hw : w ≠ 0) : fdegH μG σ w = d := by
  obtain ⟨hd, hrel⟩ := hS
  obtain ⟨-, hint⟩ := hrel w w w w
  have hpt : ∀ g : Mt k r, coef σ w w (Matrix.of g) * star (coef σ w w (Matrix.of g))
      = ((‖⟪w, σ (Matrix.of g) w⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    simp only [coef]
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [hpt] at hint
  rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K] at hint
  have hreal : ∫ x, ‖⟪w, σ (Matrix.of x) w⟫_ℂ‖ ^ 2 ∂μG = ‖w‖ ^ 4 / d := by
    apply Complex.ofReal_injective
    rw [hint]
    push_cast
    rw [← pow_add]
    rfl
  have hn : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  unfold fdegH
  rw [hreal]
  have h4 : (‖w‖ ^ 4 : ℝ) ≠ 0 := by positivity
  field_simp

end GlobalTheory.SgInf
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf.OpNormU

theorem eucl_eq {N : ℕ} (v : Fin N → ℂ) : eucl v = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp only [eucl, Complex.normSq_eq_norm_sq]

theorem eucl_nonneg {N : ℕ} (v : Fin N → ℂ) : 0 ≤ eucl v := Real.sqrt_nonneg _

theorem eucl_mulVec_le {N : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ) :
    eucl (x *ᵥ v) ≤ opn x * eucl v := by
  rw [eucl_eq, eucl_eq, ← Matrix.toEuclideanCLM_toLp]
  exact ContinuousLinearMap.le_opNorm _ _

theorem continuous_opn {N : ℕ} : Continuous fun x : Matrix (Fin N) (Fin N) ℂ => opn x :=
  (LinearMap.continuous_of_finiteDimensional
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin N)).toAlgEquiv.toLinearMap).norm

theorem opn_conjTranspose {N : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) : opn xᴴ = opn x := by
  unfold opn
  rw [← Matrix.star_eq_conjTranspose, map_star, norm_star]

theorem norm_entry_le {N : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) : ‖x i j‖ ≤ opn x := by
  have h := eucl_mulVec_le x (Pi.single j 1)
  have h1 : eucl (Pi.single j (1 : ℂ) : Fin N → ℂ) = 1 := by
    rw [eucl_eq]; simpa using (EuclideanSpace.norm_single (𝕜 := ℂ) j (1 : ℂ))
  have h2 : ‖x i j‖ ≤ eucl (x *ᵥ Pi.single j 1) := by
    rw [eucl_eq]
    have := PiLp.norm_apply_le (p := 2) (WithLp.toLp 2 (x *ᵥ Pi.single j (1 : ℂ)) : EuclideanSpace ℂ (Fin N)) i
    simpa [Matrix.mulVec_single] using this
  rw [h1, mul_one] at h
  exact h2.trans h

theorem herm_le {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (u v : Fin N → ℂ) :
    ‖herm H u v‖ ≤ opn H * eucl u * eucl v := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N)) (WithLp.toLp 2 (H *ᵥ u))
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm, ← eucl_eq, ← eucl_eq, mul_comm] at h
  exact h.trans (mul_le_mul_of_nonneg_right (eucl_mulVec_le H u) (eucl_nonneg _))

theorem eucl_mulVec_le_hs {N : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) (w : Fin N → ℂ) :
    eucl (x *ᵥ w) ≤ Real.sqrt (Formalism.REAL.hs x) * eucl w := by
  unfold eucl
  have hnn : 0 ≤ Formalism.REAL.hs x := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [← Real.sqrt_mul hnn]
  apply Real.sqrt_le_sqrt
  simp only [Complex.normSq_eq_norm_sq, Formalism.REAL.hs, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : ‖(x *ᵥ w) i‖ ≤ ∑ j, ‖x i j‖ * ‖w j‖ := by
    rw [Matrix.mulVec, dotProduct]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp only [norm_mul]
  calc ‖(x *ᵥ w) i‖ ^ 2 ≤ (∑ j, ‖x i j‖ * ‖w j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ j, ‖x i j‖ ^ 2) * ∑ j, ‖w j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = _ := Finset.sum_mul _ _ _

theorem opn_le_sqrt_hs {N : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) : opn x ≤ Real.sqrt (Formalism.REAL.hs x) := by
  unfold opn
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun v => ?_
  obtain ⟨w, rfl⟩ : ∃ w : Fin N → ℂ, v = WithLp.toLp 2 w := ⟨v.ofLp, rfl⟩
  rw [Matrix.toEuclideanCLM_toLp, ← eucl_eq, ← eucl_eq]
  exact eucl_mulVec_le_hs x w

theorem sqrt_hs_le {N : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) :
    Real.sqrt (Formalism.REAL.hs x) ≤ (N : ℝ) * opn x := by
  rw [Real.sqrt_le_iff]
  refine ⟨mul_nonneg (Nat.cast_nonneg _) (opn_nonneg _), ?_⟩
  calc Formalism.REAL.hs x ≤ ∑ _i : Fin N, ∑ _j : Fin N, opn x ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          pow_le_pow_left₀ (norm_nonneg _) (norm_entry_le x i j) 2
    _ = ((N : ℝ) * opn x) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

variable {k r : ℕ}

theorem opn_Hpk (k r : ℕ) : opn (Hpk k r) = 1 := by
  have h : opn ((Hpk k r)ᴴ * Hpk k r) = opn (Hpk k r) * opn (Hpk k r) := by
    unfold opn
    rw [← Matrix.star_eq_conjTranspose, map_mul, map_star, CStarRing.norm_star_mul_self]
  rw [GBasic.Hpk_herm, GBasic.Hpk_sq, opn_one] at h
  rcases mul_self_eq_one_iff.mp h.symm with h1 | h1
  · exact h1
  · have := opn_nonneg (Hpk k r); linarith

theorem left_inv {g : Mat k r} (hg : g ∈ GG k r) : Hpk k r * gᴴ * Hpk k r * g = 1 := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', GBasic.Hpk_sq]

theorem inv_eq {g : Mat k r} (hg : g ∈ GG k r) : g⁻¹ = Hpk k r * gᴴ * Hpk k r :=
  Matrix.inv_eq_left_inv (left_inv hg)

theorem inv_mul {g : Mat k r} (hg : g ∈ GG k r) : g⁻¹ * g = 1 := by
  rw [inv_eq hg]; exact left_inv hg

theorem mul_inv {g : Mat k r} (hg : g ∈ GG k r) : g * g⁻¹ = 1 := by
  exact Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse (left_inv hg))

theorem opn_inv_le {g : Mat k r} (hg : g ∈ GG k r) : opn g⁻¹ ≤ opn g := by
  rw [inv_eq hg]
  calc opn (Hpk k r * gᴴ * Hpk k r) ≤ opn (Hpk k r) * opn gᴴ * opn (Hpk k r) :=
        (opn_mul_le _ _).trans (mul_le_mul_of_nonneg_right (opn_mul_le _ _) (opn_nonneg _))
    _ = opn g := by rw [opn_Hpk, opn_conjTranspose]; ring

theorem le_opn_inv {g : Mat k r} (hg : g ∈ GG k r) : opn g ≤ opn g⁻¹ := by
  have e : g = Hpk k r * (g⁻¹)ᴴ * Hpk k r := by
    rw [inv_eq hg]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, GBasic.Hpk_herm, ← Matrix.mul_assoc,
      GBasic.Hpk_sq, Matrix.one_mul]
    rw [Matrix.mul_assoc, GBasic.Hpk_sq, Matrix.mul_one]
  calc opn g = opn (Hpk k r * (g⁻¹)ᴴ * Hpk k r) := congrArg opn e
    _ ≤ opn (Hpk k r) * opn (g⁻¹)ᴴ * opn (Hpk k r) :=
        (opn_mul_le _ _).trans (mul_le_mul_of_nonneg_right (opn_mul_le _ _) (opn_nonneg _))
    _ = opn g⁻¹ := by rw [opn_Hpk, opn_conjTranspose]; ring

theorem opn_inv {g : Mat k r} (hg : g ∈ GG k r) : opn g⁻¹ = opn g :=
  le_antisymm (opn_inv_le hg) (le_opn_inv hg)

theorem one_le_opn {g : Mat k r} (hg : g ∈ GG k r) : 1 ≤ opn g := by
  have h : (1 : ℝ) ≤ opn g * opn g := by
    have := opn_mul_le g g⁻¹
    rwa [mul_inv hg, opn_one, opn_inv hg] at this
  by_contra h'
  have h0 := opn_nonneg g
  nlinarith

theorem opn_pos {g : Mat k r} (hg : g ∈ GG k r) : 0 < opn g := lt_of_lt_of_le one_pos (one_le_opn hg)

theorem div_le_opn_mul {x y : Mat k r} (hx : x ∈ GG k r) (hy : y ∈ GG k r) :
    opn x / opn y ≤ opn (x * y) ∧ opn y / opn x ≤ opn (x * y) := by
  constructor
  · rw [div_le_iff₀ (opn_pos hy)]
    calc opn x = opn (x * y * y⁻¹) := by rw [Matrix.mul_assoc, mul_inv hy, Matrix.mul_one]
      _ ≤ opn (x * y) * opn y⁻¹ := opn_mul_le _ _
      _ = opn (x * y) * opn y := by rw [opn_inv hy]
  · rw [div_le_iff₀ (opn_pos hx)]
    calc opn y = opn (x⁻¹ * (x * y)) := by rw [← Matrix.mul_assoc, inv_mul hx, Matrix.one_mul]
      _ ≤ opn x⁻¹ * opn (x * y) := opn_mul_le _ _
      _ = opn (x * y) * opn x := by rw [opn_inv hx, mul_comm]

end GlobalTheory.SgInf.OpNormU

namespace GlobalTheory.SgInf

theorem opn_facts : ∀ (k r : ℕ) , (∀ g ∈ GG k r, opn g⁻¹ = opn g ∧ 1 ≤ opn g) ∧
    (∀ x y : Mat k r, opn (x * y) ≤ opn x * opn y) ∧ Continuous (fun x : Mat k r => opn x) ∧
    (∀ (x : Mat k r) i j, ‖x i j‖ ≤ opn x) ∧
    (∀ (x : Mat k r) (v : Fin (2 * r + k + 1) → ℂ), eucl (x *ᵥ v) ≤ opn x * eucl v) ∧
    (∀ u v : Fin (2 * r + k + 1) → ℂ, ‖herm (Hpk k r) u v‖ ≤ eucl u * eucl v) ∧
    (∀ x ∈ GG k r, ∀ y ∈ GG k r, opn x / opn y ≤ opn (x * y) ∧ opn y / opn x ≤ opn (x * y)) ∧
    (∀ x : Mat k r, opn x ≤ Real.sqrt (Formalism.REAL.hs x) ∧
      Real.sqrt (Formalism.REAL.hs x) ≤ ((2 * r + k + 1 : ℕ) : ℝ) * opn x) := by
  intro k r
  refine ⟨fun g hg => ⟨OpNormU.opn_inv hg, OpNormU.one_le_opn hg⟩, fun x y => opn_mul_le x y,
    OpNormU.continuous_opn, OpNormU.norm_entry_le, OpNormU.eucl_mulVec_le, fun u v => ?_,
    fun x hx y hy => OpNormU.div_le_opn_mul hx hy,
    fun x => ⟨OpNormU.opn_le_sqrt_hs x, OpNormU.sqrt_hs_le x⟩⟩
  simpa [OpNormU.opn_Hpk] using OpNormU.herm_le (Hpk k r) u v

end GlobalTheory.SgInf
end
end

section

open GlobalTheory.Diag.PG

theorem _root_.GlobalTheory.T.globalRankNumberBounds_gaps_exceed : ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C : ℝ, 0 < C → ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ m f k lrd Del : ℝ, RankNums x eps CD m f k lrd Del → ∀ r : ℝ, k ≤ r → r ≤ 2 * k → C * k * m ^ 4 + r * m ^ 10 < 4 * Del ∧ C * k * m ^ 4 + r * m ^ 10 < Real.sqrt (bx x eps) ∧ C * k * m ^ 4 + r * m ^ 10 < x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps ∧ C * r ^ 19 * f ^ 5 * x ^ eps ≤ x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps := by
  first | exact @GlobalTheory.Diag.PG.gaps_exceed | exact GlobalTheory.Diag.PG.gaps_exceed | (intros; apply GlobalTheory.Diag.PG.gaps_exceed <;> assumption)
end
