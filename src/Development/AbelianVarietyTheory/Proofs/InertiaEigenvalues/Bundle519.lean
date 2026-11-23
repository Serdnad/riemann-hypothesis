module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle334
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle510
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle362
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle025
public import Formalism.DoubleCosetMeasures.StatementZ
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle508
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle509
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HaarMeasureInverseInvariant
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CrystallineSubrepresentation
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsOpenKerFinIdele

@[expose] public section

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.FunExt GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RSGam.Transport

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w}
  {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
  {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A' w'}
  {φ : Ω ≃+* Ω'}

theorem wdRel_mk (c : Weil h ≃* Weil h') (hcr : ∀ σ σ', WeilRel φ σ σ' ↔ c σ = σ')
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : WDRep h V) (b' : WDRep h' V)
    (hN : b.N = b'.N) (hρ : ∀ σ, b'.ρ (c σ) = b.ρ σ) : WDRel φ (WD.mk b) (WD.mk b') := by
  let e : V ≃ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ) := (Module.finBasis ℂ V).equivFun
  refine ⟨_, b.transport e, b'.transport e, WD.sound (b.iso_transport e).symm,
    WD.sound (b'.iso_transport e).symm, ?_, fun σ σ' hσ => ?_⟩
  · show e.conjAlgEquiv ℂ b.N = e.conjAlgEquiv ℂ b'.N
    rw [hN]
  · show e.conjAlgEquiv ℂ (b.ρ σ) = e.conjAlgEquiv ℂ (b'.ρ σ')
    rw [← (hcr σ σ').1 hσ, hρ]

theorem wdRel_lpUnr (c : Weil h ≃* Weil h') (hcr : ∀ σ σ', WeilRel φ σ σ' ↔ c σ = σ')
    (hdeg : ∀ σ, deg (c σ) = deg σ) (m : Multiset ℂ) :
    WDRel φ (WD.lpUnr (h := h) m) (WD.lpUnr (h := h') m) := by
  classical
  unfold WD.lpUnr
  refine wdRel_mk c hcr _ _ rfl fun σ => ?_
  rw [WDRep.diag_ρ, WDRep.diag_ρ, hdeg]

end GlobalTheory.RSGam.Transport

end
end

section

noncomputable section

namespace GlobalTheory.WachTensor

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts GlobalTheory.EtaleExact
open GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation (LocQuotCrys LocTensorCrys LocDualCrys)

set_option synthInstance.maxHeartbeats 400000

variable {l : ℕ} [Fact l.Prime]

private theorem frobW_surjective_lemma : Function.Surjective (frobW l) := by
  have hC : IsAlgClosed (Cb l) := (GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing l).1
  have hf : Function.Surjective (frobenius (Cb l) l) := by
    first
      | exact surjective_frobenius (Cb l) l
      | exact (bijective_frobenius (Cb l) l).2
      | exact fun y => ⟨(frobeniusEquiv (Cb l) l).symm y, by simp⟩
  intro y
  obtain ⟨x, hx⟩ := WittVector.map_surjective (p := l) _ hf y
  unfold frobW
  exact ⟨x, hx⟩

theorem φRW_surjective (LL : FinExt l) : Function.Surjective (φRW LL) := by
  have hg : Function.Surjective (frobW l).toLinearMap := frobW_surjective_lemma
  intro y
  obtain ⟨x, rfl⟩ := LinearMap.lTensor_surjective (↥(OL LL)) hg y
  refine ⟨x, ?_⟩
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [φRW]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

theorem map_ne_top {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l}
    {h : Good K s LL}
    {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))}
    (E : EtSit P AI K s LL h W) (m : Ideal W.EE) (hm : m.IsMaximal) :
    m.map E.tie.ioE.toRingHom ≠ ⊤ := by
  have : Module.Finite ℤ_[l] ↥(OL LL) := GlobalTheory.EtaleExact.finite_OL LL
  have : IsNoetherianRing ↥(OL LL) := by
    first
      | infer_instance
      | exact isNoetherian_of_tower ℤ_[l] inferInstance
  refine GlobalTheory.EtaleExact.map_ne_top_of_tie E.tie (fun c => ?_) (fun x hx => ?_) m hm
  · rw [P.PD_p K]
    exact GlobalTheory.EtaleExact.isUnit_or_dvd_pow P LL c
  · exact GlobalTheory.EtaleExact.sep_RW LL x (by simpa [P.PD_p K] using hx)

theorem descends {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l}
    {h : Good K s LL}
    {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))}
    (E : EtSit P AI K s LL h W) : Descends E.tie := by
  intro ι _ M w hg hw i
  exact GlobalTheory.T.mem_range_of_frobeniusEquation_cyclotomicFixed l P AI K s LL h W E ι M 0 w hg (fun i => by simpa using hw i) i

end GlobalTheory.WachTensor
end
end

section

noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

namespace GlobalTheory.JSW

theorem norm_toL_mul_le {E : Type} [Field E] [NumberField E] {a : ℕ} (A : Matrix (Fin a) (Fin a) (Cinf E)) (B : Lie E a) :
    ‖toL (A * Matrix.of B)‖ ≤ a * (‖toL A‖ * ‖B‖) := by
  have h0 : 0 ≤ (a : ℝ) * (‖toL A‖ * ‖B‖) := by positivity
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
  show ‖(A * Matrix.of B) i j‖ ≤ _
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  have hk : ∀ k, ‖A i k * Matrix.of B k j‖ ≤ ‖toL A‖ * ‖B‖ := fun k => by
    refine (norm_mul_le _ _).trans (mul_le_mul ?_ ?_ (norm_nonneg _) (norm_nonneg _))
    · exact (norm_le_pi_norm (toL A i) k).trans (norm_le_pi_norm (toL A) i)
    · exact (norm_le_pi_norm (B k) j).trans (norm_le_pi_norm B k)
  calc ∑ k, ‖A i k * Matrix.of B k j‖ ≤ ∑ _k : Fin a, ‖toL A‖ * ‖B‖ := Finset.sum_le_sum fun k _ => hk k
    _ = _ := by simp

theorem norm_fderiv_chart_le : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    (∀ i, ∃ C : ℝ, ∀ g, ‖(lie E a (lieBasis E a i) φ).1 g‖ ≤ C) →
      ∃ C : ℝ, ∀ (g : GA E a) (y : GL (Fin a) (Cinf E)), ‖fderiv ℝ (chart φ.1 g) (toL y.val)‖ ≤ C * ‖toL (y⁻¹).val‖ := by
  intro E _ _ _ a φ hC
  choose C hC using hC
  set D : ℝ := ∑ i, max (C i) 0 * ‖lieCoord E a i‖ with hDdef
  have hD : 0 ≤ D := Finset.sum_nonneg fun i _ => mul_nonneg (le_max_right _ _) (norm_nonneg _)
  have hlie : ∀ (X : Lie E a) (h : GA E a), ‖lieD X φ.1 h‖ ≤ D * ‖X‖ := by
    intro X h
    have e : lieD X φ.1 h = ∑ i, ((lieBasis E a).coord i X) • lieD (lieBasis E a i) φ.1 h := by
      conv_lhs => rw [← sum_lieCoord X]

      simp only [lieD, map_sum, map_smul]
    rw [e, hDdef, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul]
    have h1 : ‖(lieBasis E a).coord i X‖ ≤ ‖lieCoord E a i‖ * ‖X‖ := by
      have : ‖lieCoord E a i X‖ = ‖(lieBasis E a).coord i X‖ := by simp [lieCoord]
      rw [← this]; exact (lieCoord E a i).le_opNorm X
    have h2 : ‖lieD (lieBasis E a i) φ.1 h‖ ≤ max (C i) 0 := by
      have := hC i h
      rw [GlobalTheory.CuspRep.lie_apply] at this
      exact this.trans (le_max_left _ _)
    calc ‖(lieBasis E a).coord i X‖ * ‖lieD (lieBasis E a i) φ.1 h‖
        ≤ (‖lieCoord E a i‖ * ‖X‖) * max (C i) 0 := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  refine ⟨a * D, fun g y => ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun W => ?_
  set X : Lie E a := toL ((y⁻¹).val * Matrix.of W) with hX
  have e := chart_lieD φ.2 X g (val_mem_invSet y)
  have eW : rmul X (toL y.val) = W := by
    change y.val * ((y⁻¹).val * Matrix.of W) = Matrix.of W
    rw [← mul_assoc, Units.mul_inv, one_mul]
  rw [eW, chart_val] at e
  rw [← e]
  calc ‖lieD X φ.1 (g * infGL E a y)‖ ≤ D * ‖X‖ := hlie _ _
    _ ≤ D * (a * (‖toL (y⁻¹).val‖ * ‖W‖)) := mul_le_mul_of_nonneg_left (norm_toL_mul_le _ _) hD
    _ = a * D * ‖toL (y⁻¹).val‖ * ‖W‖ := by ring

end GlobalTheory.JSW
end
end

section

noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

namespace GlobalTheory.JSW

namespace RapidCoef

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem norm_toL_mul_le (A B : Matrix (Fin a) (Fin a) (Cinf E)) :
    ‖toL (A * B)‖ ≤ a * ‖toL A‖ * ‖toL B‖ := by
  have h : ∀ (C : Matrix (Fin a) (Fin a) (Cinf E)) i j, ‖C i j‖ ≤ ‖toL C‖ := fun C i j =>
    (norm_le_pi_norm (toL C i) j).trans (norm_le_pi_norm (toL C) i)
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  change ‖(A * B) i j‖ ≤ _
  rw [Matrix.mul_apply]
  calc ‖∑ l, A i l * B l j‖ ≤ ∑ l, ‖A i l * B l j‖ := norm_sum_le _ _
    _ ≤ ∑ _l : Fin a, ‖toL A‖ * ‖toL B‖ := Finset.sum_le_sum fun l _ =>
        (norm_mul_le _ _).trans (mul_le_mul (h A i l) (h B l j) (norm_nonneg _) (norm_nonneg _))
    _ = _ := by simp [mul_assoc]

theorem continuous_smul_adj : Continuous fun q : Cinf E × Lie E a => toL (q.1 • (Matrix.of q.2).adjugate) := by
  change Continuous fun q : Cinf E × Matrix (Fin a) (Fin a) (Cinf E) => q.1 • q.2.adjugate
  fun_prop

theorem continuous_conj (M : Matrix (Fin a) (Fin a) (Cinf E)) :
    Continuous fun q : Lie E a × Lie E a => toL (Matrix.of q.1 * M * Matrix.of q.2) := by
  change Continuous fun q : Matrix (Fin a) (Fin a) (Cinf E) × Matrix (Fin a) (Fin a) (Cinf E) => q.1 * M * q.2
  fun_prop

theorem inv_val_eq (y : GL (Fin a) (Cinf E)) :
    (y⁻¹).val = (fun v => (y.val.det v)⁻¹) • y.val.adjugate := by
  symm
  apply Units.eq_inv_of_mul_eq_one_left
  rw [mul_smul_comm, Matrix.mul_adjugate, smul_smul]
  have hu : IsUnit y.val.det := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
  have : (fun v => (y.val.det v)⁻¹) * y.val.det = 1 := by
    funext v
    exact inv_mul_cancel₀ ((Pi.isUnit_iff.1 hu) v).ne_zero
  rw [this, one_smul]

end RapidCoef


open RapidCoef in
theorem isRapidInf_mul_adCoef : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : Type)
    [MeasurableSpace X] (ν : Measure X) (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ →
      ∀ p, IsRapidInf ν (fun x => k x * adCoef (γ x) p) γ := by
  intro E _ _ _ a X _ ν k γ hr p
  obtain ⟨hk, hγ, hint⟩ := hr
  haveI : SecondCountableTopology (Lie E a) := inferInstance
  haveI : BorelSpace (Lie E a) := inferInstance
  haveI : OpensMeasurableSpace (Lie E a × Lie E a) := inferInstance
  haveI : OpensMeasurableSpace (Cinf E × Lie E a) := inferInstance
  have hA : Measurable fun x => toL (γ x).val := hγ
  have hdet : Measurable fun x => ((γ x).val).det := contDiff_det.continuous.measurable.comp hA
  have hc : Measurable fun x => (fun v => (((γ x).val).det v)⁻¹ : Cinf E) :=
    Measurable.of_eval fun v => ((measurable_pi_apply v).comp hdet).inv
  have hinv : Measurable fun x => toL (γ x)⁻¹.val := by
    have : (fun x => toL (γ x)⁻¹.val) =
        (fun q : Cinf E × Lie E a => toL (q.1 • (Matrix.of q.2).adjugate)) ∘
          fun x => ((fun v => (((γ x).val).det v)⁻¹ : Cinf E), toL (γ x).val) := by
      funext x; simp only [Function.comp_apply, inv_val_eq]; rfl
    rw [this]
    exact continuous_smul_adj.measurable.comp (hc.prodMk hA)
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin a) (Fin a) (Cinf E), M = Matrix.of (lieBasis E a p.2) := ⟨_, rfl⟩
  have e : ∀ y : GL (Fin a) (Cinf E), adCoef y p = lieCoord E a p.1 (toL ((y⁻¹).val * M * y.val)) :=
    fun y => by subst hM; rfl
  have hconj : Measurable fun x => toL ((γ x)⁻¹.val * M * (γ x).val) := by
    have h := (continuous_conj M).measurable.comp (hinv.prodMk hA)
    exact h
  have had : Measurable fun x => adCoef (γ x) p := by
    have h := (lieCoord E a p.1).continuous.measurable.comp hconj
    have h' : (fun x => adCoef (γ x) p) = fun x => lieCoord E a p.1 (toL ((γ x)⁻¹.val * M * (γ x).val)) :=
      funext fun x => e (γ x)
    rw [h']
    exact h
  have hh : Measurable fun x => height (γ x) := by
    unfold height
    exact (measurable_const.add hA.norm).add hinv.norm
  have hh1 : ∀ y : GL (Fin a) (Cinf E), 1 ≤ height y := fun y => by
    unfold height; linarith [norm_nonneg (toL y.val), norm_nonneg (toL (y⁻¹).val)]
  have hA_le : ∀ y : GL (Fin a) (Cinf E), ‖toL y.val‖ ≤ height y := fun y => by
    unfold height; linarith [norm_nonneg (toL (y⁻¹).val)]
  have hI_le : ∀ y : GL (Fin a) (Cinf E), ‖toL (y⁻¹).val‖ ≤ height y := fun y => by
    unfold height; linarith [norm_nonneg (toL y.val)]
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = ‖lieCoord E a p.1‖ * ((a : ℝ) * (a * ‖toL M‖)) := ⟨_, rfl⟩
  have hbd : ∀ y : GL (Fin a) (Cinf E), ‖adCoef y p‖ ≤ C * height y ^ 2 := fun y => by
    have h0 : 0 ≤ height y := zero_le_one.trans (hh1 y)
    have h1 : ‖toL ((y⁻¹).val * M * y.val)‖ ≤ a * (a * ‖toL (y⁻¹).val‖ * ‖toL M‖) * ‖toL y.val‖ :=
      (_root_.GlobalTheory.JSW.RapidCoef.norm_toL_mul_le ((y⁻¹).val * M) y.val).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (_root_.GlobalTheory.JSW.RapidCoef.norm_toL_mul_le (y⁻¹).val M) (Nat.cast_nonneg _))
          (norm_nonneg _))
    have h2 : a * (a * ‖toL (y⁻¹).val‖ * ‖toL M‖) * ‖toL y.val‖ ≤ a * (a * height y * ‖toL M‖) * height y :=
      mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hI_le y) (Nat.cast_nonneg _)) (norm_nonneg _)) (Nat.cast_nonneg _))
        (hA_le y) (norm_nonneg _) (by positivity)
    rw [e]
    calc ‖lieCoord E a p.1 (toL ((y⁻¹).val * M * y.val))‖ ≤ ‖lieCoord E a p.1‖ * ‖toL ((y⁻¹).val * M * y.val)‖ :=
          (lieCoord E a p.1).le_opNorm _
      _ ≤ ‖lieCoord E a p.1‖ * (a * (a * height y * ‖toL M‖) * height y) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (norm_nonneg _)
      _ = C * height y ^ 2 := by rw [hC]; ring
  refine ⟨hk.mul had, hγ, fun N => ?_⟩
  refine ((hint (N + 2)).const_mul C).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact ((hk.mul had).norm.mul (hh.pow_const N)).aestronglyMeasurable
  · have hpos : 0 ≤ height (γ x) ^ N := pow_nonneg (zero_le_one.trans (hh1 _)) N
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) hpos), norm_mul]
    calc ‖k x‖ * ‖adCoef (γ x) p‖ * height (γ x) ^ N
        ≤ ‖k x‖ * (C * height (γ x) ^ 2) * height (γ x) ^ N :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hbd _) (norm_nonneg _)) hpos
      _ = C * (‖k x‖ * height (γ x) ^ (N + 2)) := by ring

end GlobalTheory.JSW
end
end

section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

noncomputable section

namespace GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem fderiv_chart_rmul (φ : Sm E a) (g : GA E a) (y : GL (Fin a) (Cinf E)) (W : Lie E a) :
    fderiv ℝ (chart φ.1 g) (toL y.val) (rmul (toL y.val) W) =
      lieD (toL ((y⁻¹).val * Matrix.of W * y.val)) φ.1 (g * infGL E a y) := by
  rw [← chart_val (lieD _ φ.1), chart_lieD φ.2 _ g (val_mem_invSet y)]
  congr 1
  change Matrix.of W * y.val = y.val * ((y⁻¹).val * Matrix.of W * y.val)
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]

theorem lieD_eq_sum (V : Lie E a) (F : GA E a → ℂ) (h : GA E a) :
    lieD V F h = ∑ i, (lieCoord E a i V) * lieD (lieBasis E a i) F h := by
  conv_lhs => rw [← sum_lieCoord V]

  rw [lieD, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Complex.real_smul]
  rfl

theorem smul_fderiv_chart_comp (φ : Sm E a) (g : GA E a) (y : GL (Fin a) (Cinf E)) (c : ℂ) :
    c • (fderiv ℝ (chart φ.1 g) (toL y.val)).comp (rmul (toL y.val)) =
      ∑ p, (c * adCoef y p * (lie E a (lieBasis E a p.1) φ).1 (g * infGL E a y)) • lieCoord E a p.2 := by
  refine ContinuousLinearMap.coe_injective ((lieBasis E a).ext fun r => ?_)
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, fderiv_chart_rmul, CuspRep.lie_apply]
  rw [lieD_eq_sum, Fintype.sum_prod_type, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single r]
  · simp only [lieCoord, adCoef, ContinuousLinearMap.coe_comp', Function.comp_apply, LinearMap.coe_toContinuousLinearMap',
      Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same, Complex.ofRealCLM_apply, Complex.ofReal_one,
      smul_eq_mul, mul_one]
    ring
  · intro j _ hj
    simp [lieCoord, Module.Basis.repr_self, Finsupp.single_apply, hj]
  · simp

theorem integral_fderiv_chart_eq_of {X : Type} [MeasurableSpace X] (ν : Measure X) (k : X → ℂ)
    (γ : X → GL (Fin a) (Cinf E)) (hrc : ∀ p, IsRapidInf ν (fun x => k x * adCoef (γ x) p) γ) (φ : Sm E a)
    (hb : ∀ i, ∃ C : ℝ, ∀ g, ‖(lie E a (lieBasis E a i) φ).1 g‖ ≤ C) (g : GA E a) :
    ∫ x, k x • (fderiv ℝ (chart φ.1 g) (toL (γ x).val)).comp (rmul (toL (γ x).val)) ∂ν =
      ∑ p, kerOp ν (fun x => k x * adCoef (γ x) p) γ (lie E a (lieBasis E a p.1) φ).1 g • lieCoord E a p.2 := by
  have hint : ∀ p, Integrable (fun x => (k x * adCoef (γ x) p) *
      (lie E a (lieBasis E a p.1) φ).1 (g * infGL E a (γ x))) ν := by
    intro p
    obtain ⟨C, hC⟩ := hb p.1
    exact (hrc p).integrable (lie E a (lieBasis E a p.1) φ).2 ⟨C, 0, fun y => by simpa using hC _⟩
  simp_rw [smul_fderiv_chart_comp]
  rw [integral_finsetSum _ fun p _ => (hint p).smul_const _]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_smul_const]
  rfl

end GlobalTheory.JSW
end
end

section

noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

namespace GlobalTheory.JSW

theorem measurable_smooth_comp_infGL {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    {X : Type} [MeasurableSpace X] (γ : X → GL (Fin a) (Cinf E))
    (hγ : Measurable (fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E)))) (φ : Sm E a) (g : GA E a) :
    Measurable (fun x => φ.1 (g * infGL E a (γ x))) := by
  classical
  have hc : Measurable (chart φ.1 g) := by
    have e : chart φ.1 g = (invSet E a).piecewise (chart φ.1 g) (fun _ => 0) := by
      funext x
      by_cases h : x ∈ invSet E a
      · simp [Set.piecewise, h]
      · have h' : ¬ IsUnit (Matrix.of x) := h
        simp only [Set.piecewise, h, if_false]
        simp [chart, h']
    rw [e]
    exact ContinuousOn.measurable_piecewise (φ.2 g).continuousOn continuousOn_const isOpen_invSet.measurableSet
  have hγ' : Measurable (fun x => toL (γ x).val) := hγ
  have h2 := hc.comp hγ'
  simpa [Function.comp_def, chart_val] using h2

theorem kerOp_integrable_continuous : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X)
    (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → ∀ φ : Sm E a, Continuous φ.1 →
    (∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C) →
      (∀ g, Integrable (fun x => k x * φ.1 (g * infGL E a (γ x))) ν) ∧ Continuous (kerOp ν k γ φ.1) := by
  intro E _ _ _ a X _ ν k γ hk φ hφc hb
  obtain ⟨C, hC⟩ := hb
  have hint : Integrable (fun x => ‖k x‖ * C) ν := by
    have h0 := hk.2.2 0
    simp only [pow_zero, mul_one] at h0
    exact h0.mul_const C
  have hm : ∀ g, AEStronglyMeasurable (fun x => k x * φ.1 (g * infGL E a (γ x))) ν := fun g =>
    (hk.1.mul (measurable_smooth_comp_infGL γ hk.2.1 φ g)).aestronglyMeasurable
  have hbd : ∀ g, ∀ᵐ x ∂ν, ‖k x * φ.1 (g * infGL E a (γ x))‖ ≤ ‖k x‖ * C := fun g =>
    Filter.Eventually.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  refine ⟨fun g => Integrable.mono' hint (hm g) (hbd g), ?_⟩

  exact continuous_of_dominated hm hbd hint (Filter.Eventually.of_forall fun x =>
    continuous_const.mul (hφc.comp (continuous_id.mul continuous_const)))

end GlobalTheory.JSW
end
end

section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory

theorem _root_.GlobalTheory.T.isCompact_adelicUnitriangular_entries_mem_compact : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (C : Set (Ad E)), IsCompact C →
    IsCompact {g : GA E n | g ∈ GlobalTheory.CellDec.NA E n ∧ ∀ i j : Fin n, i < j → (g : Matrix (Fin n) (Fin n) (Ad E)) i j ∈ C} := by
  first | exact @GlobalTheory.CellDec.isCompact_unip_entries_mem | exact GlobalTheory.CellDec.isCompact_unip_entries_mem | (intros; apply GlobalTheory.CellDec.isCompact_unip_entries_mem <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

theorem _root_.GlobalTheory.T.isOpen_C0 : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
    IsOpen (GlobalTheory.CellDec.C0 E n S) := by
  first | exact @GlobalTheory.CellDec.isOpen_adelicUnipotentTimesIntegralOutsideSet | exact GlobalTheory.CellDec.isOpen_adelicUnipotentTimesIntegralOutsideSet | (intros; apply GlobalTheory.CellDec.isOpen_adelicUnipotentTimesIntegralOutsideSet <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

theorem _root_.GlobalTheory.T.haar_measure_inverse_invariant : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) [MeasurableSpace (GA E n)] [BorelSpace (GA E n)]
    (ν : Measure (GlobalTheory.CellDec.NA E n)) [ν.IsHaarMeasure], ν.IsInvInvariant := by
  first | exact @GlobalTheory.CellDec.NA_isInvInvariant | exact GlobalTheory.CellDec.NA_isInvInvariant | (intros; apply GlobalTheory.CellDec.NA_isInvInvariant <;> assumption)
end
