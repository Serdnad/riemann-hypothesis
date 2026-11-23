module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle866
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle156
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle248
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle239
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConcentrationTimeBound
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandOperatorNormal
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveTimeAverageIsWave
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterOperatorPreservesWave
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle236
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundaryTermGood
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle250
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle249
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype

@[expose] public section

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical

namespace GlobalTheory.CompanionTheory.HeckeChar

theorem exists_unit_model : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (μ : G E Ω →* (Qbar l)ˣ), Continuous μ →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
    ∃ (LL' : FinExt l) (ψ : ↥(Dec (F := E) A) →* (↥LL'.1)ˣ), Bw.LL.1 ≤ LL'.1 ∧
      IsModel Bw ((rk1 μ).comp (Dec (F := E) A).subtype) LL' ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL'.1).comp ψ) ∧
      (∀ g, ((ψ g : ↥LL'.1) : Qbar l) = ((μ (g : G E Ω) : (Qbar l)ˣ) : Qbar l)) ∧
      Continuous (fun g => ((ψ g : ↥LL'.1) : Qbar l)) ∧ ∀ g, ‖((ψ g : ↥LL'.1) : Qbar l)‖ = 1 := by
  intro E Ω _ _ _ _ _ l _ μ hμ w A _ O _ _ _ Bw
  have hc : Continuous fun g : G E Ω => ((μ g : (Qbar l)ˣ) : Qbar l) := Units.continuous_val.comp hμ
  have hent : ∀ (g : G E Ω) (i j : Fin 1),
      ((rk1 μ g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) i j = ((μ g : (Qbar l)ˣ) : Qbar l) := by
    intro g i j
    have hij : i = j := Subsingleton.elim i j
    subst hij
    simp [rk1]
  have hr : Continuous (fun g : G E Ω => ((rk1 μ g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l))) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact hc.congr fun g => (hent g i j).symm
  obtain ⟨L, hle, hL⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (G E Ω) 1 (rk1 μ) hr Bw.LL
  have hmem : ∀ g : G E Ω, ((μ g : (Qbar l)ˣ) : Qbar l) ∈ L.1 := fun g => by
    have h := hL g 0 0
    rwa [hent] at h
  let ψ : ↥(Dec (F := E) A) →* (↥L.1)ˣ :=
    { toFun := fun g =>
        ⟨⟨((μ (g : G E Ω) : (Qbar l)ˣ) : Qbar l), hmem _⟩,
          ⟨((μ ((g : G E Ω)⁻¹) : (Qbar l)ˣ) : Qbar l), hmem _⟩,
          Subtype.ext (by simp [← Units.val_mul, ← map_mul]),
          Subtype.ext (by simp [← Units.val_mul, ← map_mul])⟩
      map_one' := Units.ext (Subtype.ext (by simp))
      map_mul' := fun g h => Units.ext (Subtype.ext (by simp)) }
  have hψ : ∀ g, ((ψ g : ↥L.1) : Qbar l) = ((μ (g : G E Ω) : (Qbar l)ˣ) : Qbar l) := fun g => rfl
  refine ⟨L, ψ, hle, ⟨hle, ?_⟩, hψ, ?_, fun g => ?_⟩
  · refine MonoidHom.ext fun g => Units.ext ?_
    ext i j
    have hij : i = j := Subsingleton.elim i j
    subst hij
    simp [Formalism.MainNotions.N.mapRep, PositivityTheory.HodgeLocalCharacter.HLC.toGL1, rk1, hψ]
  · exact hc.comp continuous_subtype_val
  · exact GlobalTheory.ExpFrame.CharUnit.norm_eq_one_of_compact μ hc _

end GlobalTheory.CompanionTheory.HeckeChar
end
end

section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty ENNReal
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.functional_calculus_on_sobolev : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n),
    haveI := FiniteDimensional.complete ℂ E.V
    ∀ (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ) (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T),
      LgFacts → Unimod → RCalc → SobG → CalcSteps →
      (∀ (f : Mat n → E.V) (hf : cls μ f ∈ Msob μ E.V), Sob μ f → (Ω ⟨cls μ f, hf⟩ : Lp E.V 2 μ) = cls μ (Om f)) →
      ∀ (h : C₀(ℝ, ℂ)) (f : Mat n → E.V), Sob μ f → IsSec E f →
        ∃ f', Sob μ f' ∧ IsSec E f' ∧ cls μ f' = F.Φ h (cls μ f) := by
  first | exact @GlobalTheory.CompanionTheory.FcSmooth.phi_keeps_sections | exact GlobalTheory.CompanionTheory.FcSmooth.phi_keeps_sections | (intros; apply GlobalTheory.CompanionTheory.FcSmooth.phi_keeps_sections <;> assumption)
end

section

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff ZeroAtInfty InnerProductSpace

namespace GlobalTheory.CompanionTheory.WaveLoc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem mul_mem {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  have hx' : x.det ≠ 0 := hx
  have hy' : y.det ≠ 0 := hy
  show (x * y).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero hx' hy'

theorem inv_mem {x : Mat n} (hx : x ∈ GLs n) : x⁻¹ ∈ GLs n :=
  (Matrix.isUnit_nonsing_inv_det x (isUnit_iff_ne_zero.mpr hx)).ne_zero

theorem val_mem (y : G n) : y.val ∈ GLs n :=
  ((Matrix.isUnit_iff_isUnit_det _).mp y.isUnit).ne_zero

def step (r s : ℝ) : ℝ := Real.smoothTransition (r + 1 - s)

theorem step_contDiff (r : ℝ) : ContDiff ℝ ∞ (step r) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

theorem step_eq_one {r s : ℝ} (h : s ≤ r) : step r s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem step_eq_zero {r s : ℝ} (h : r + 1 ≤ s) : step r s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

def cutAt (r : ℝ) (x y : Mat n) : ℝ := step r (lg (x⁻¹ * y))

theorem cutAt_smooth (hL : LgFacts) (r : ℝ) {x : Mat n} (hx : x ∈ GLs n) :
    ContDiffOn ℝ ∞ (cutAt r x) (GLs n) := by
  have hm : ContDiff ℝ ∞ (fun y : Mat n => x⁻¹ * y) :=
    (LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ x⁻¹)).contDiff
  have h1 : ContDiffOn ℝ ∞ (fun y : Mat n => lg (x⁻¹ * y)) (GLs n) :=
    (hL n).2.2.2.1.comp hm.contDiffOn fun _ hy => mul_mem (inv_mem hx) hy
  exact (step_contDiff r).comp_contDiffOn h1

theorem cutAt_mul_unitary (hL : LgFacts) (r : ℝ) {x g : Mat n} (hx : x ∈ GLs n) (hg : g ∈ GLs n)
    (k : Matrix.unitaryGroup (Fin n) ℂ) : cutAt r x (g * k.1) = cutAt r x g := by
  have h := (hL n).2.2.1 (x⁻¹ * g) (mul_mem (inv_mem hx) hg) 1 k
  have e : ((1 : Matrix.unitaryGroup (Fin n) ℂ)).1 * (x⁻¹ * g) * k.1 = x⁻¹ * (g * k.1) := by
    rw [show ((1 : Matrix.unitaryGroup (Fin n) ℂ)).1 = 1 from rfl, one_mul, mul_assoc]
  rw [e] at h
  simp only [cutAt, h]

def cutSec {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (r : ℝ) (x : Mat n) (f : Mat n → V) : Mat n → V :=
  fun y => ((cutAt r x y : ℝ) : ℂ) • f y

theorem cutSec_mem (hL : LgFacts) (r : ℝ) {x : Mat n} (hx : x ∈ GLs n) {E : KMod n} {f : Mat n → E.V}
    (hf : f ∈ CE E) : cutSec r x f ∈ CE E := by
  refine ⟨?_, fun g hg k => ?_⟩
  · have hc : ContDiffOn ℝ ∞ (fun y => ((cutAt r x y : ℝ) : ℂ)) (GLs n) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (cutAt_smooth hL r hx)
    exact hc.smul hf.1
  · simp only [cutSec, cutAt_mul_unitary hL r hx hg k, hf.2 g hg k, map_smul]

theorem cutSec_cpt (hL : LgFacts) (r : ℝ) {x : Mat n} (hx : x ∈ GLs n) {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℂ V] (f : Mat n → V) : Cpt (cutSec r x f) := by
  refine ⟨lg x + (r + 1), fun y hy h => ?_⟩
  have e : x * (x⁻¹ * y) = y := Matrix.mul_nonsing_inv_cancel_left x y (isUnit_iff_ne_zero.mpr hx)
  have hs := (hL n).1 x hx (x⁻¹ * y) (mul_mem (inv_mem hx) hy)
  rw [e] at hs
  have h0 : cutAt r x y = 0 := step_eq_zero (by linarith)
  simp [cutSec, h0]

theorem cutSec_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {r : ℝ} {x y : Mat n} (hx : x ∈ GLs n)
    (f : Mat n → V) (h : lg y ≤ r) : cutSec r x f (x * y) = f (x * y) := by
  have e : x⁻¹ * (x * y) = y := Matrix.nonsing_inv_mul_cancel_left x y (isUnit_iff_ne_zero.mpr hx)
  have h1 : cutAt r x (x * y) = 1 := by
    rw [cutAt, e]
    exact step_eq_one h
  simp [cutSec, h1]

theorem wave_sub {E : KMod n} {u v : ℝ → Mat n → E.V} (hu : IsWave E u) (hv : IsWave E v) :
    IsWave E fun t y => u t y - v t y := by
  have h := GlobalTheory.CompanionTheory.WaveK.Lin.wave_add hu (GlobalTheory.CompanionTheory.WaveK.Lin.wave_smul (-1 : ℂ) hv)
  simpa [sub_eq_add_neg] using h

theorem kerLoc : KerLoc := by
  intro n _ _ μ _ E g T k hg hL _ _ hS hW hk hsupp heq hker
  refine ⟨hk, hsupp, heq, fun u hu x hx => ?_⟩
  obtain ⟨R, hR⟩ := hsupp
  obtain ⟨c, hc⟩ := hS n
  obtain ⟨r, hRr, hcr⟩ : ∃ r : ℝ, R ≤ r ∧ |c| * (1 + |T|) ≤ r :=
    ⟨max R (|c| * (1 + |T|)), le_max_left _ _, le_max_right _ _⟩
  have hf := cutSec_mem hL r hx (hu.2.1 0)
  have hcpt := cutSec_cpt hL r hx (u 0)
  obtain ⟨v, hv, hv0⟩ := hW n E _ hf hcpt
  have huv : ∀ t, |t| ≤ T → u t x = v t x := by
    intro t ht
    refine sub_eq_zero.mp (hc E _ (wave_sub hu hv) t x hx fun y hy hly => ?_)
    have hb : c * (1 + |t|) ≤ |c| * (1 + |T|) := by
      have h1 : |t| ≤ |T| := ht.trans (le_abs_self T)
      have h2 : (0 : ℝ) ≤ 1 + |t| := by positivity
      calc c * (1 + |t|) ≤ |c| * (1 + |t|) := mul_le_mul_of_nonneg_right (le_abs_self c) h2
        _ ≤ |c| * (1 + |T|) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg c)
    show u 0 (x * y) - v 0 (x * y) = 0
    rw [hv0 _ (mul_mem hx hy), cutSec_eq hx _ (hly.trans (hb.trans hcr)), sub_self]
  have h1 : act μ E k (u 0) x = act μ E k (cutSec r x (u 0)) x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show k y.val (u 0 (x * y.val)) = k y.val (cutSec r x (u 0) (x * y.val))
    by_cases h : R < lg y.val
    · simp [hR _ (val_mem y) h]
    · rw [cutSec_eq hx _ ((not_lt.mp h).trans hRr)]
  rw [h1, hker _ hf hcpt v hv hv0 x hx]
  show _ = ∫ t, (g t : ℂ) • u t x
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show (g t : ℂ) • v t x = (g t : ℂ) • u t x
  by_cases h : T < |t|
  · simp [hg.2.2 t h]
  · rw [huv t (not_lt.mp h)]

end GlobalTheory.CompanionTheory.WaveLoc
end
end

section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA.SupG

theorem norm_cls_sq_eq {n : ℕ} [MeasurableSpace (G n)] {μ : Measure (G n)} {V : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] {K : Mat n → V}
    (h : MemLp (fun y : G n => K y.val) 2 μ) :
    ‖cls μ K‖ ^ 2 = ∫ y : G n, ‖K y.val‖ ^ 2 ∂μ := by
  have h0 : 0 ≤ ∫ y : G n, ‖K y.val‖ ^ 2 ∂μ := integral_nonneg fun y => by positivity
  have hc : cls μ K = h.toLp _ := dif_pos h
  rw [hc, Lp.norm_toLp, h.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [ENNReal.toReal_ofReal (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul h0]
  norm_num

theorem exists_unit {n : ℕ} {x : Mat n} (hx : x ∈ GLs n) : ∃ g : G n, g.val = x :=
  ⟨((Matrix.isUnit_iff_isUnit_det x).2 (isUnit_iff_ne_zero.2 hx)).unit, rfl⟩

theorem sup_sq_bound : SobG → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure], ∃ (S : Finset (List (Bool × Fin n × Fin n))) (C : ℝ), 0 ≤ C ∧ ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (h : Mat n → V), ContDiffOn ℝ ∞ h (GLs n) → (∀ w, MemLp (fun y : G n => Rw w h y.val) 2 μ) → ∀ x ∈ GLs n, ‖h x‖ ^ 2 ≤ C * ∑ w ∈ S, ‖cls μ (Rw w h)‖ ^ 2 := by
  intro hS n _ _ μ _
  obtain ⟨S, r, C, hC⟩ := hS n μ
  refine ⟨S, max C 0, le_max_right _ _, fun V _ _ _ h hsm hL x hx => ?_⟩
  obtain ⟨g, rfl⟩ := exists_unit hx
  have h0 := hC V h hsm g.val hx
  have hw : ∀ w ∈ S, ∫ y in {y : G n | lg y.val ≤ r}, ‖Rw w h (g.val * y.val)‖ ^ 2 ∂μ ≤
      ‖cls μ (Rw w h)‖ ^ 2 := by
    intro w _
    set K := Rw w h with hK
    have hm : MemLp (fun y : G n => K y.val) 2 μ := hL w
    have hφ : Integrable (fun y : G n => ‖K y.val‖ ^ 2) μ :=
      (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).1 hm
    have hψ : Integrable (fun y : G n => ‖K (g.val * y.val)‖ ^ 2) μ := by
      simpa only [Units.val_mul] using hφ.comp_mul_left g
    have e1 : ∫ y : G n, ‖K (g.val * y.val)‖ ^ 2 ∂μ = ∫ y : G n, ‖K y.val‖ ^ 2 ∂μ := by
      simpa only [Units.val_mul] using
        integral_mul_left_eq_self (μ := μ) (fun y : G n => ‖K y.val‖ ^ 2) g
    rw [norm_cls_sq_eq hm, ← e1]
    exact setIntegral_le_integral hψ (Filter.Eventually.of_forall fun y => by positivity)
  have hI : 0 ≤ ∑ w ∈ S, ∫ y in {y : G n | lg y.val ≤ r}, ‖Rw w h (g.val * y.val)‖ ^ 2 ∂μ :=
    Finset.sum_nonneg fun w _ => integral_nonneg fun y => by positivity
  calc ‖h g.val‖ ^ 2
      ≤ C * ∑ w ∈ S, ∫ y in {y : G n | lg y.val ≤ r}, ‖Rw w h (g.val * y.val)‖ ^ 2 ∂μ := h0
    _ ≤ max C 0 * ∑ w ∈ S, ∫ y in {y : G n | lg y.val ≤ r}, ‖Rw w h (g.val * y.val)‖ ^ 2 ∂μ :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hI
    _ ≤ max C 0 * ∑ w ∈ S, ‖cls μ (Rw w h)‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hw) (le_max_right _ _)

end GlobalTheory.CompanionTheory.PresSobA.SupG
end
end

section


theorem _root_.GlobalTheory.T.concentration_time_bound : PositivityTheory.RgBcC.Fc.ConcT := by
  first | exact @GlobalTheory.CompanionTheory.FcConcT.concT | exact GlobalTheory.CompanionTheory.FcConcT.concT | (intros; apply GlobalTheory.CompanionTheory.FcConcT.concT <;> assumption)
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.wave_time_average_is_wave : WaveSpeed → ∀ (n : ℕ) (E : KMod n) (u : ℝ → Mat n → E.V) (g : ℝ → ℝ) (T : ℝ), IsWave E u → IsBump g T → IsWave E (fun t x => ∫ s, (g s : ℂ) • u (t + s) x) := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.WaveAvg.isWave_avg | exact GlobalTheory.CompanionTheory.WaveMult.WaveAvg.isWave_avg | (intros; apply GlobalTheory.CompanionTheory.WaveMult.WaveAvg.isWave_avg <;> assumption)
end

section


theorem _root_.GlobalTheory.T.gelfand_operator_normal : PositivityTheory.RgBcC.GelN := by
  first | exact @GlobalTheory.CompanionTheory.GelLevi.gelN | exact GlobalTheory.CompanionTheory.GelLevi.gelN | (intros; apply GlobalTheory.CompanionTheory.GelLevi.gelN <;> assumption)
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.center_operator_preserves_wave : RCalc → ∀ (n : ℕ) (E : KMod n) (u : ℝ → Mat n → E.V) (w : List (Bool × ℕ)), IsWave E u → IsWave E (fun t => zOp w (u t)) := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.WaveZ.isWave_zOp | exact GlobalTheory.CompanionTheory.WaveMult.WaveZ.isWave_zOp | (intros; apply GlobalTheory.CompanionTheory.WaveMult.WaveZ.isWave_zOp <;> assumption)
end

section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.KerSwap

theorem isKer_swap : WaveSpeed → RCalc → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (w w' : List (Bool × ℕ)) (g : ℝ → ℝ) (T : ℝ) (K : Mat n → (E.V →L[ℂ] E.V)), IsBump g T → IsKer μ E (w ++ w') g K → IsKer μ E (w' ++ w) g K := by
  intro hW hR n _ _ μ _ E w w' g T K hg hK
  refine ⟨hK.1, hK.2.1, hK.2.2.1, fun u hu x hx => ?_⟩
  rw [hK.2.2.2 u hu x hx]
  have hs : ContDiffOn ℝ ∞ (fun x' => ∫ t : ℝ, (g t : ℂ) • u t x') (GLs n) := by
    have h1 := ((GlobalTheory.CompanionTheory.WaveMult.WaveAvg.isWave_avg hW n E u g T hu hg).2.1 0).1
    simpa only [zero_add] using h1
  exact GlobalTheory.CompanionTheory.WaveMult.Swap.zOp_swap hR n w w' _ hs x hx

end GlobalTheory.CompanionTheory.WaveMult.KerSwap
end
end

section

open PositivityTheory.RgEis PositivityTheory.RgEis.MG

theorem _root_.GlobalTheory.T.boundary_term_good : BGood := by
  first | exact @GlobalTheory.CompanionTheory.RgEisLeft.bGood | exact GlobalTheory.CompanionTheory.RgEisLeft.bGood | (intros; apply GlobalTheory.CompanionTheory.RgEisLeft.bGood <;> assumption)
end

section

open PositivityTheory.RgEis PositivityTheory.RgEis.MG

theorem _root_.GlobalTheory.T.average_invariance : AvgMem → AvgInv := by
  first | exact @GlobalTheory.CompanionTheory.RgEisAvg.avgInv_of_avgMem | exact GlobalTheory.CompanionTheory.RgEisAvg.avgInv_of_avgMem | (intros; apply GlobalTheory.CompanionTheory.RgEisAvg.avgInv_of_avgMem <;> assumption)
end

section

open PositivityTheory.RgEis PositivityTheory.RgEis.MG

theorem _root_.GlobalTheory.T.zeta_integral_of_epstein_conv : EpConv → ZetaK := by
  first | exact @GlobalTheory.CompanionTheory.ZetaAlongK.zetaK | exact GlobalTheory.CompanionTheory.ZetaAlongK.zetaK | (intros; apply GlobalTheory.CompanionTheory.ZetaAlongK.zetaK <;> assumption)
end
