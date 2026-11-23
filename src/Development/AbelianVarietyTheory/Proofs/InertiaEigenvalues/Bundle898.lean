module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle872
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.BaseIntSet
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjHalfInvariantFormIdemSumVacuumNeZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacuumTranslateSumFixedByFlippedLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle883
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle885
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsIntegralEntireTheta
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntersectionFamilyMultilinear
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle854
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU

@[expose] public section

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.exists_conjHalfInvariant_form_idemSum_vacuum_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (eT : AE D), IsIdemSum eT T → ∃ ℓ : (WO V W → ℂ) →ₗ[ℂ] ℂ, ℓ f₀ ≠ 0 ∧ ∀ y : WO V W, IsHalf (cA D eT) y → ∀ φ : WO V W → ℂ, IsThetaFunO ψ V W φ → ℓ (heisO ψ V W y φ) = ℓ φ := by
  first | exact @GlobalTheory.LevelSeries.exists_invariant_form_idemSum | exact GlobalTheory.LevelSeries.exists_invariant_form_idemSum | (intros; apply GlobalTheory.LevelSeries.exists_invariant_form_idemSum <;> assumption)
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.vacuum_translate_sum_fixed_by_flipped_lattice : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) (eT : AE D), IsIdemSum eT T → Odd m → Nat.Coprime m (GlobalTheory.Tow.badN D) → (∀ PP ∈ T, ((m : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → ∀ Y : Finset (WO V W), (∀ y ∈ Y, IsHalf (cA D eT) y ∧ m • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True)) → (∀ y ∈ Y, ∀ y' ∈ Y, y - y' ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → y = y') → (∀ y : WO V W, IsHalf (cA D eT) y → m • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → ∃ y' ∈ Y, y - y' ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True)) → (∀ u ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True), heisO ψ V W (flipElt eT m • (2 • u)) (∑ y ∈ Y, heisO ψ V W y f₀) = ∑ y ∈ Y, heisO ψ V W y f₀) ∧ ∀ e : AE D, IsSplitIdem D e → ∀ u ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True), IsHalf e u → heisO ψ V W (flipElt eT m • u) (∑ y ∈ Y, heisO ψ V W y f₀) = ∑ y ∈ Y, heisO ψ V W y f₀ := by
  first | exact @GlobalTheory.FlipFixSum.flip_fix | exact GlobalTheory.FlipFixSum.flip_fix | (intros; apply GlobalTheory.FlipFixSum.flip_fix <;> assumption)
end

section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

noncomputable section

namespace GlobalTheory.MSpanDecay.RapidLie

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
theorem norm_entry_le (A : Matrix (Fin a) (Fin a) (Cinf E)) (i j : Fin a) : ‖A i j‖ ≤ ‖toL A‖ :=
  (norm_le_pi_norm (toL A i) j).trans (norm_le_pi_norm (toL A) i)


omit [_root_.NumberField.IsTotallyComplex E] in
theorem norm_toL_mul_le (A B : Matrix (Fin a) (Fin a) (Cinf E)) : ‖toL (A * B)‖ ≤ a * (‖toL A‖ * ‖toL B‖) := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  change ‖(A * B) i j‖ ≤ _
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (‖toL A‖ * ‖toL B‖) fun k _ => ?_).trans ?_)
  · exact (norm_mul_le _ _).trans (mul_le_mul (norm_entry_le A i k) (norm_entry_le B k j) (norm_nonneg _) (norm_nonneg _))
  · simp


omit [_root_.NumberField.IsTotallyComplex E] in
theorem measurable_comp_of_continuousOn {X : Type} [MeasurableSpace X] {f : Lie E a → ℂ}
    (hf : ContinuousOn f (invSet E a)) {φ : X → Lie E a} (hφ : Measurable φ) (hφ' : ∀ x, φ x ∈ invSet E a) :
    Measurable fun x => f (φ x) := by
  have e : (fun x => f (φ x)) = (invSet E a).restrict f ∘ fun x => (⟨φ x, hφ' x⟩ : invSet E a) := rfl
  rw [e]
  exact hf.restrict.measurable.comp (hφ.subtype_mk)


omit [_root_.NumberField.IsTotallyComplex E] in
theorem measurable_inv {X : Type} [MeasurableSpace X] {γ : X → GL (Fin a) (Cinf E)}
    (hγ : Measurable fun x => toL (γ x).val) : Measurable fun x => toL ((γ x)⁻¹).val := by
  have key : ∀ y : GL (Fin a) (Cinf E), ((y⁻¹ : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) =
      (fun w => ((y : Matrix (Fin a) (Fin a) (Cinf E)).det w)⁻¹) • (y : Matrix (Fin a) (Fin a) (Cinf E)).adjugate := by
    intro y
    refine Units.inv_eq_of_mul_eq_one_left ?_
    have hu : IsUnit (y : Matrix (Fin a) (Fin a) (Cinf E)).det := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
    have h1 : (fun w => ((y : Matrix (Fin a) (Fin a) (Cinf E)).det w)⁻¹) * (y : Matrix (Fin a) (Fin a) (Cinf E)).det = 1 := by
      funext w
      have hw : (y : Matrix (Fin a) (Fin a) (Cinf E)).det w ≠ 0 :=
        ((Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w).isUnit_map hu).ne_zero
      exact inv_mul_cancel₀ hw
    rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, h1, one_smul]
  have e : (fun x => toL ((γ x)⁻¹).val) = fun x => toL ((fun w => ((γ x : Matrix (Fin a) (Fin a) (Cinf E)).det w)⁻¹) •
      (γ x : Matrix (Fin a) (Fin a) (Cinf E)).adjugate) := funext fun x => congrArg toL (key (γ x))
  rw [e]
  have hdet : Measurable fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E)).det :=
    (contDiff_det (E := E) (a := a)).continuous.measurable.comp hγ
  have hadjc : Continuous fun m : Lie E a => (toL (Matrix.of m).adjugate : Lie E a) :=
    Continuous.matrix_adjugate continuous_id
  have hadj : Measurable fun x => toL (γ x : Matrix (Fin a) (Fin a) (Cinf E)).adjugate :=
    hadjc.measurable.comp hγ
  have hc : Measurable fun x => (fun w => ((γ x : Matrix (Fin a) (Fin a) (Cinf E)).det w)⁻¹ : Cinf E) :=
    Measurable.of_eval fun w => ((measurable_pi_apply w).comp hdet).inv
  exact (continuous_smul (M := Cinf E) (X := Lie E a)).measurable.comp (hc.prodMk hadj)

end GlobalTheory.MSpanDecay.RapidLie

namespace GlobalTheory.MSpanDecay.RapidLie

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem measurable_mul {X : Type} [MeasurableSpace X] {A B : X → Lie E a} (hA : Measurable A) (hB : Measurable B) :
    Measurable fun x => toL (Matrix.of (A x) * Matrix.of (B x)) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => Measurable.of_eval fun w => ?_
  have e : (fun x => toL (Matrix.of (A x) * Matrix.of (B x)) i j w) = fun x => ∑ k, A x i k w * B x k j w := by
    funext x; simp [Matrix.mul_apply, Finset.sum_apply]
  rw [e]
  exact Finset.measurable_sum _ fun k _ =>
    ((measurable_pi_apply w).comp ((measurable_pi_apply k).comp ((measurable_pi_apply i).comp hA))).mul
      ((measurable_pi_apply w).comp ((measurable_pi_apply j).comp ((measurable_pi_apply k).comp hB)))

theorem measurable_conj {X : Type} [MeasurableSpace X] {γ : X → GL (Fin a) (Cinf E)}
    (hγ : Measurable fun x => toL (γ x).val) (Y : Lie E a) :
    Measurable fun x => toL (((γ x)⁻¹).val * Matrix.of Y * (γ x).val) :=
  measurable_mul (measurable_mul (measurable_inv hγ) measurable_const) hγ

end GlobalTheory.MSpanDecay.RapidLie

namespace GlobalTheory.MSpanDecay.RapidLie

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
theorem norm_conj_le (y : GL (Fin a) (Cinf E)) (Y : Lie E a) :
    ‖toL ((y⁻¹).val * Matrix.of Y * y.val)‖ ≤ a * a * ‖Y‖ * height y ^ 2 := by
  have h1 : ‖toL y.val‖ ≤ height y := by unfold height; linarith [norm_nonneg (toL (y⁻¹).val)]
  have h2 : ‖toL (y⁻¹).val‖ ≤ height y := by unfold height; linarith [norm_nonneg (toL y.val)]
  have h3 : ‖toL ((y⁻¹).val * Matrix.of Y)‖ ≤ a * (‖toL (y⁻¹).val‖ * ‖Y‖) := norm_toL_mul_le _ _
  calc ‖toL ((y⁻¹).val * Matrix.of Y * y.val)‖ ≤ a * (‖toL ((y⁻¹).val * Matrix.of Y)‖ * ‖toL y.val‖) :=
        norm_toL_mul_le _ _
    _ ≤ a * ((a * (height y * ‖Y‖)) * height y) := by
        have h4 : ‖toL ((y⁻¹).val * Matrix.of Y)‖ ≤ a * (height y * ‖Y‖) :=
          h3.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)) (Nat.cast_nonneg a))
        exact mul_le_mul_of_nonneg_left (mul_le_mul h4 h1 (norm_nonneg _) ((norm_nonneg _).trans h4)) (Nat.cast_nonneg a)
    _ = a * a * ‖Y‖ * height y ^ 2 := by ring

theorem lieD_eq_sum {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ (Lie E a)) (W : Lie E a) (G : GA E a → ℂ)
    (g : GA E a) : lieD W G g = ∑ j, ((b.repr W j : ℝ) : ℂ) * lieD (b j) G g := by
  unfold lieD
  conv_lhs => rw [← b.sum_repr W]

  rw [map_sum]
  simp only [map_smul, Complex.real_smul]

theorem measurable_height {X : Type} [MeasurableSpace X] {γ : X → GL (Fin a) (Cinf E)}
    (hγ : Measurable fun x => toL (γ x).val) : Measurable fun x => height (γ x) := by
  have e : (fun x => height (γ x)) = fun x => 1 + ‖toL (γ x).val‖ + ‖toL ((γ x)⁻¹).val‖ := rfl
  rw [e]
  exact (measurable_const.add hγ.norm).add (measurable_inv hγ).norm

end GlobalTheory.MSpanDecay.RapidLie

namespace GlobalTheory.MSpanDecay


open RapidLie in
theorem integral_lieD_conj_mem_kSpan : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (G : GA E a → ℂ) (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)) (Y : Lie E a), GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.MSpanDecay.Good G → (fun g : GA E a => ∫ x, k x * lieD (toL (((γ x)⁻¹).val * Matrix.of Y * (γ x).val)) G (g * infGL E a (γ x)) ∂ν) ∈ GlobalTheory.MSpanDecay.kSpan E a := by
  intro E _ _ _ a G X _ ν _ k γ Y hk hG
  obtain ⟨hkm, hγm, hint⟩ := hk
  have hγ : Measurable fun x => toL (γ x).val := hγm
  let b := Module.finBasis ℝ (Lie E a)
  let L : Fin (Module.finrank ℝ (Lie E a)) → Lie E a →L[ℝ] ℝ := fun j => LinearMap.toContinuousLinearMap (b.coord j)
  let W : X → Lie E a := fun x => toL (((γ x)⁻¹).val * Matrix.of Y * (γ x).val)
  let c : Fin (Module.finrank ℝ (Lie E a)) → X → ℂ := fun j x => ((L j (W x) : ℝ) : ℂ)
  have hW : Measurable W := measurable_conj hγ Y
  have hc : ∀ j, Measurable (c j) := fun j => Complex.measurable_ofReal.comp ((L j).continuous.measurable.comp hW)
  set D : Fin (Module.finrank ℝ (Lie E a)) → ℝ := fun j => ‖L j‖ * (a * a * ‖Y‖) with hD
  have hD0 : ∀ j, 0 ≤ D j := fun j => by positivity
  have hcb : ∀ j x, ‖c j x‖ ≤ D j * height (γ x) ^ 2 := by
    intro j x
    have h := (L j).le_opNorm (W x)
    rw [Complex.norm_real]
    refine h.trans ?_
    rw [hD, mul_assoc]
    exact mul_le_mul_of_nonneg_left (norm_conj_le (γ x) Y) (norm_nonneg _)
  have hG' : ∀ j, Good (lieD (b j) G) := fun j => hG.derivative _
  have hrap : ∀ j, GlobalTheory.JSW.IsRapidInf ν (fun x => k x * c j x) γ := by
    intro j
    refine ⟨hkm.mul (hc j), hγm, fun N => ?_⟩
    refine Integrable.mono' ((hint (N + 2)).const_mul (D j))
      (((hkm.mul (hc j)).norm.mul ((measurable_height hγ).pow_const N)).aestronglyMeasurable)
      (ae_of_all _ fun x => ?_)
    have h1 := one_le_height (γ x)
    have hp : 0 ≤ height (γ x) ^ N := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul]
    calc ‖k x‖ * ‖c j x‖ * height (γ x) ^ N ≤ ‖k x‖ * (D j * height (γ x) ^ 2) * height (γ x) ^ N := by
          gcongr; exact hcb j x
      _ = D j * (‖k x‖ * height (γ x) ^ (N + 2)) := by ring
  have hmeasG : ∀ j g, Measurable fun x => lieD (b j) G (g * infGL E a (γ x)) := by
    intro j g
    have e : (fun x => lieD (b j) G (g * infGL E a (γ x))) = fun x => chart (lieD (b j) G) g (toL (γ x).val) :=
      funext fun x => (chart_val _ g (γ x)).symm
    rw [e]
    exact measurable_comp_of_continuousOn (((hG' j).mem_Sm g).continuousOn) hγ fun x => val_mem_invSet (γ x)
  have hintj : ∀ j g, Integrable (fun x => k x * c j x * lieD (b j) G (g * infGL E a (γ x))) ν := by
    intro j g
    obtain ⟨C, N, hCN⟩ := (hG' j).growth g
    refine Integrable.mono' ((hint (N + 2)).const_mul (D j * |C|))
      (((hkm.mul (hc j)).mul (hmeasG j g)).aestronglyMeasurable) (ae_of_all _ fun x => ?_)
    have h1 := one_le_height (γ x)
    have hp : 0 ≤ height (γ x) ^ N := by positivity
    have hg : ‖lieD (b j) G (g * infGL E a (γ x))‖ ≤ |C| * height (γ x) ^ N :=
      (hCN (γ x)).trans (mul_le_mul_of_nonneg_right (le_abs_self C) hp)
    rw [norm_mul, norm_mul]
    calc ‖k x‖ * ‖c j x‖ * ‖lieD (b j) G (g * infGL E a (γ x))‖
        ≤ ‖k x‖ * (D j * height (γ x) ^ 2) * (|C| * height (γ x) ^ N) := by
          gcongr
          · exact hcb j x
      _ = D j * |C| * (‖k x‖ * height (γ x) ^ (N + 2)) := by ring
  have e : (fun g : GA E a => ∫ x, k x * lieD (toL (((γ x)⁻¹).val * Matrix.of Y * (γ x).val)) G
      (g * infGL E a (γ x)) ∂ν) =
      ∑ j, fun g : GA E a => ∫ x, k x * c j x * lieD (b j) G (g * infGL E a (γ x)) ∂ν := by
    funext g
    rw [Finset.sum_apply, ← integral_finsetSum _ fun j _ => hintj j g]
    congr 1
    funext x
    rw [lieD_eq_sum b, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (mul_assoc (k x) (c j x) _).symm
  rw [e]
  exact Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨X, inferInstance, ν, inferInstance, _, γ, _, hrap j, hG' j, rfl⟩

end GlobalTheory.MSpanDecay
end
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped ENNReal nonZeroDivisors ComplexConjugate

noncomputable section

namespace GlobalTheory.RSPoleToc

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem eq_ofReal_norm {z : ℂ} (h1 : 0 ≤ z.re) (h2 : z.im = 0) : z = ((‖z‖ : ℝ) : ℂ) := by
  have hz : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [h2])
  rw [hz, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h1]

theorem rsPsi_self_eq (ℓ : Fin a) (F : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ)
    (hΦ : ∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (g : GA E a)
    (y : Fin a → Ad E) :
    GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g y = ((‖GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g y‖ : ℝ) : ℂ) := by
  set u : Fin a → Cinf E := fun i => pInf E (y i)
  set w := g * (infGL E a (GlobalTheory.RSTheta.rowGL ℓ u))⁻¹
  set s : ℝ := (GlobalTheory.ThetaPoisson.latt a J).indicator 1 ((fun i => pFin E (y i)) - η)
  have hs : (GlobalTheory.ThetaPoisson.latt a J).indicator (1 : (Fin a → Af E) → ℂ) ((fun i => pFin E (y i)) - η) = (s : ℂ) := by
    classical
    simp only [s]; rw [Set.indicator_apply, Set.indicator_apply]; split_ifs <;> simp
  have hs0 : 0 ≤ s := Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hΦu : Φ u = (((Φ u).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [(hΦ u).2])
  have e : GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g y = ((Complex.normSq (F w) * (Φ u).re * s : ℝ) : ℂ) := by
    simp only [GlobalTheory.RSTheta.rsPsi, GlobalTheory.ThetaPoisson.thetaFn, GlobalTheory.RSTheta.rsInf]
    rw [hs, Complex.mul_conj, hΦu]
    push_cast
    rfl
  refine eq_ofReal_norm ?_ ?_
  · rw [e, Complex.ofReal_re]
    exact mul_nonneg (mul_nonneg (Complex.normSq_nonneg _) (hΦ u).1) hs0
  · rw [e, Complex.ofReal_im]

theorem tsum_eq_toReal {ι : Type} (f : ι → ℂ) (hf : ∀ i, f i = ((‖f i‖ : ℝ) : ℂ)) :
    ∑' i, f i = (((∑' i, ‖f i‖ₑ).toReal : ℝ) : ℂ) := by
  rw [ENNReal.tsum_toReal_eq fun _ => enorm_ne_top, Complex.ofReal_tsum]
  exact tsum_congr fun i => by rw [toReal_enorm, ← hf i]

theorem thetaZ_eq_toReal (ℓ : Fin a) (F : GA E a → ℂ) (hF : Continuous F) (Φ : (Fin a → Cinf E) → ℂ)
    (hΦc : Continuous Φ) (hΦs : tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ) (hΦ : ∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0)
    (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (μ : Measure (GA E a)) (𝓕 : Set (GA E a)) (x : ℝ)
    (hfin : ∫⁻ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g
        ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ₑ) *
        ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ ≠ ⊤) :
    GlobalTheory.RSPole.thetaZ μ 𝓕 ℓ F F Φ J η x = (((∫⁻ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
                 ‖GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ₑ) *
                 ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ).toReal : ℝ) : ℂ) := by
  set G : GA E a → ℝ≥0∞ := fun g => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g
        ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ₑ) *
        ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) with hG

  have hcont : ∀ ξ : {ξ : Fin a → E // ξ ≠ 0}, Continuous fun g : GA E a => GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g
      ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val) := by
    intro ξ
    have h1 : Continuous fun g : GA E a =>
        (g, (fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g.val : Matrix (Fin a) (Fin a) (Ad E))) :=
      continuous_id.prodMk (continuous_const.matrix_vecMul Units.continuous_val)
    have h2 := GlobalTheory.RSTheta.continuous_rsPsi hF hF hΦc hΦs J η
    have h3 := h2.comp h1
    exact h3
  have hdet : Continuous fun g : GA E a => ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) := by
    have h : Continuous fun g : GA E a => (ideleModule E (GeneralLinearGroup.det g) : ℝ) :=
      continuous_subtype_val.comp (continuous_ideleModule.comp (GroundTheory.Automorphic.AdelicGLn.continuous_det E a))
    exact h.rpow_const fun g => Or.inl (ideleModule E (GeneralLinearGroup.det g)).2.ne'
  have hGm : Measurable G := by
    refine Measurable.mul ?_ (ENNReal.measurable_ofReal.comp hdet.measurable)
    exact (lowerSemicontinuous_tsum fun ξ => (hcont ξ).enorm.lowerSemicontinuous).measurable

  have hpt : ∀ g : GA E a, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g
      ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) *
      ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ) = (((G g).toReal : ℝ) : ℂ) := by
    intro g
    rw [tsum_eq_toReal _ fun ξ => rsPsi_self_eq ℓ F Φ hΦ J η g _, hG]
    simp only
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (Real.rpow_nonneg (ideleModule E (GeneralLinearGroup.det g)).2.le x), Complex.ofReal_mul]
  have hae : ∀ᵐ g ∂μ.restrict 𝓕, G g < ⊤ := ae_lt_top hGm hfin
  calc GlobalTheory.RSPole.thetaZ μ 𝓕 ℓ F F Φ J η x = ∫ g in 𝓕, (((G g).toReal : ℝ) : ℂ) ∂μ := by
        rw [GlobalTheory.RSPole.thetaZ]; exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ((∫ g in 𝓕, (G g).toReal ∂μ : ℝ) : ℂ) := integral_ofReal
    _ = _ := by rw [integral_toReal hGm.aemeasurable hae]

theorem thetaZ_eq_toReal_lintegral : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ℓ : Fin a) (π : CuspSub E a)
    (F : GA E a → ℂ), F ∈ GlobalTheory.JSW.mspanR π → Continuous F →
    ∀ (Φ : (Fin a → Cinf E) → ℂ), Continuous Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ →
    (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)),
    IsFundamentalDomain (ratGL E a).range 𝓕 μ → ∀ x : ℝ,
    ∫⁻ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ₑ) * ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ ≠ ⊤ →
    GlobalTheory.RSPole.thetaZ μ 𝓕 ℓ F F Φ J η x = (((∫⁻ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ₑ) * ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ).toReal : ℝ) : ℂ) := by
  intro E _ _ _ a ℓ π F _ hF Φ hΦc hΦs hΦ J η μ _ 𝓕 _ x hfin
  exact thetaZ_eq_toReal ℓ F hF Φ hΦc hΦs hΦ J η μ 𝓕 x hfin

end GlobalTheory.RSPoleToc
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.JSW

namespace GlobalTheory.JSW

section Block

variable {R S : Type} [CommRing R] [CommRing S] {j n : ℕ}

theorem blockGL_cornerGL (hj : j ≤ n) (s : R →ₙ+* S) (g : GL (Fin j) R) :
    GroundTheory.Automorphic.FourierWhittaker.blockGL hj (cornerGL j s g) =
      cornerGL n s (GroundTheory.Automorphic.FourierWhittaker.blockGL hj g) := by
  ext a b
  change GroundTheory.Automorphic.FourierWhittaker.blockMat hj
      ((1 : Matrix (Fin j) (Fin j) S) - (1 : Matrix (Fin j) (Fin j) R).map s + (g : Matrix (Fin j) (Fin j) R).map s) a b =
    (1 : Matrix (Fin n) (Fin n) S) a b - s ((1 : Matrix (Fin n) (Fin n) R) a b) +
      s (GroundTheory.Automorphic.FourierWhittaker.blockMat hj (g : Matrix (Fin j) (Fin j) R) a b)
  rw [GroundTheory.Automorphic.FourierWhittaker.blockMat_apply, GroundTheory.Automorphic.FourierWhittaker.blockMat_apply]
  by_cases ha : a.val < j
  · by_cases hb : b.val < j
    · simp only [dif_pos ha, dif_pos hb, Matrix.add_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.one_apply,
        Fin.ext_iff]
    · have hab : a ≠ b := fun h => hb (h ▸ ha)
      simp [ha, hb, hab, Matrix.one_apply]
  · by_cases hab : a = b
    · subst hab; simp [ha, Matrix.one_apply]
    · simp [ha, hab, Matrix.one_apply]

theorem blockGL_diagPow (hj : j ≤ n) (ϖ : Rˣ) (v : Fin j → ℕ) :
    GroundTheory.Automorphic.FourierWhittaker.blockGL hj (diagPow ϖ v) = diagPow ϖ (GlobalTheory.RSnmUnf.padNat (n := n) v) := by
  ext a b
  rw [GroundTheory.Automorphic.FourierWhittaker.coe_blockGL, GroundTheory.Automorphic.FourierWhittaker.blockMat_apply]
  simp only [diagPow, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, Matrix.diagonalRingHom_apply]
  by_cases ha : a.val < j
  · by_cases hb : b.val < j
    · simp [ha, hb, Matrix.diagonal_apply, GlobalTheory.RSnmUnf.padNat, Fin.ext_iff, MulEquiv.piUnits]
    · have hab : a ≠ b := fun h => hb (h ▸ ha)
      simp [ha, hb, hab, Matrix.diagonal_apply]
  · by_cases hab : a = b
    · subst hab; simp [ha, Matrix.diagonal_apply, GlobalTheory.RSnmUnf.padNat, MulEquiv.piUnits]
    · simp [ha, hab, Matrix.diagonal_apply]

theorem padNat_eq_zero_iff {m n : ℕ} (hmn : m ≤ n) (v : Fin m → ℕ) :
    GlobalTheory.RSnmUnf.padNat (n := n) v = 0 ↔ v = 0 := by
  constructor
  · intro h
    funext i
    have := congrFun h ⟨i.val, by omega⟩
    simpa [GlobalTheory.RSnmUnf.padNat, i.isLt] using this
  · rintro rfl
    exact GlobalTheory.RSnmUnf.padNat_zero

end Block

theorem blockGL_tl {E : Type} [Field E] [NumberField E] (m r : ℕ)
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ)) :
    GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) (GlobalTheory.JSW.tl ϖ l) =
      GlobalTheory.JSW.tl ϖ (l.mapRange GlobalTheory.RSnmUnf.padNat GlobalTheory.RSnmUnf.padNat_zero) := by
  have hsupp : (l.mapRange (GlobalTheory.RSnmUnf.padNat (n := m + r + 1 + 1)) GlobalTheory.RSnmUnf.padNat_zero).support = l.support := by
    ext w
    simp only [Finsupp.mem_support_iff, Finsupp.mapRange_apply, ne_eq]
    rw [padNat_eq_zero_iff (by omega)]
  unfold tl
  rw [hsupp, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro w _
  simp only [Function.comp_apply, Finsupp.mapRange_apply]
  rw [finGL, locGL, blockGL_cornerGL, blockGL_cornerGL, blockGL_diagPow]
  rfl

end GlobalTheory.JSW
end
end

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)

theorem _root_.GlobalTheory.T.fundamental_domain_poisson_cuspidal : ∀ (E : Type) [Field E] [NumberField E] (k m : ℕ) (hmk : m + 1 ≤ k) (φ : GA E (k + 1) → ℂ),
    Continuous φ → (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) → (∀ γ g, φ (ratGL E (k + 1) γ * g) = φ g) →
    (∀ r, 0 < r → r ≤ k → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (k + 1) r k)) (fun x => φ (blkU x * g)) = 0) →
    ∀ F ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi (K := E) (ι := Fin (m + 1)),
    ∀ γ : {ξ : Fin (m + 1) → E // ξ ≠ 0} → GL (Fin (m + 1)) E,
    (∀ ξ, Matrix.vecMul (Pi.single (Fin.last m) 1 : Fin (m + 1) → E) (γ ξ).val = ξ.1) → ∀ h : GA E (m + 1),
    HasSum (fun ξ : {ξ : Fin (m + 1) → E // ξ ≠ 0} =>
        GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (Matrix.vecMul (algebraMap E (Ad E) ∘ ξ.1) h.val) *
          partialCoeff φ (m + 1) (blockGL (by omega : m + 1 ≤ k + 1) (ratGL E (m + 1) (γ ξ) * h)))
      (partialCoeff (GlobalTheory.RSnm.colSmooth (m + 1) F φ) (m + 1 + 1) (blockGL (by omega : m + 1 ≤ k + 1) h)) := by
  first | (exact @GlobalTheory.ColFourier.hasSum_colSmooth) | (exact GlobalTheory.ColFourier.hasSum_colSmooth) | (intros; apply GlobalTheory.ColFourier.hasSum_colSmooth  <;> assumption)
end
