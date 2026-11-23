module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle286
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPolyBallOfCompact
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle130
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle124
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle367
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle338
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecomposition
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.InstCommRingBcris
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import GroundTheory.PAdicHodge.UnramifiedClosure
public import GroundTheory.PAdicHodge.BCrisRegularSenTate
import GroundTheory.PAdicHodge.BdRTGalois
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle381
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle223
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle214
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import GroundTheory.PAdicHodge.Bundle013
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

noncomputable section

namespace GlobalTheory.CompanionTheory.Conc

theorem lintegral_sq_le {Y : Type*} [MeasurableSpace Y] (P : Measure Y) [IsProbabilityMeasure P]
    (g : Y → ℝ≥0∞) (hg : AEMeasurable g P) : (∫⁻ y, g y ∂P) ^ 2 ≤ ∫⁻ y, g y ^ 2 ∂P := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P Real.HolderConjugate.two_two hg
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ] at h
  have h2 := pow_le_pow_left' h 2
  have h3 : ((∫⁻ y, g y ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ))) ^ 2 = ∫⁻ y, g y ^ (2 : ℝ) ∂P := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [h3] at h2
  simpa [ENNReal.rpow_ofNat] using h2

theorem enorm_sub_sm_sq_le (E : Type) [Field E] [NumberField E] (N : ℕ)
    [MeasurableSpace (archGroup E N)] [BorelSpace (archGroup E N)]
    (ν : Measure (archGroup E N)) [ν.IsHaarMeasure] (β : archGroup E N → ℝ) (hk : Ker ν β)
    (f : AdelicGLn.AdelicGL E N → ℂ) (hf : Continuous f) (x : AdelicGLn.AdelicGL E N) :
    ‖f x - sm ν β f x‖ₑ ^ 2 ≤ ∫⁻ y, ‖f (x * infEmb E N y) - f x‖ₑ ^ 2
      ∂(ν.withDensity fun y => ENNReal.ofReal (β y)) := by
  have hwm : Measurable fun y => ENNReal.ofReal (β y) := hk.cont.measurable.ennreal_ofReal
  have : IsProbabilityMeasure (ν.withDensity fun y => ENNReal.ofReal (β y)) := by
    refine ⟨?_⟩
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (hk.cont.integrable_of_hasCompactSupport hk.cpt)
        (Eventually.of_forall hk.nonneg), hk.mass, ENNReal.ofReal_one]
  have hc1 : Continuous fun y => f (x * infEmb E N y) :=
    hf.comp (continuous_const.mul continuous_infEmb)
  have hi1 : Integrable (fun y => (β y : ℂ) * f (x * infEmb E N y)) ν :=
    ((Complex.continuous_ofReal.comp hk.cont).mul hc1).integrable_of_hasCompactSupport
      (hk.cpt.comp_left Complex.ofReal_zero |>.mul_right)
  have hi2 : Integrable (fun y => (β y : ℂ) * f x) ν :=
    ((Complex.continuous_ofReal.comp hk.cont).mul continuous_const).integrable_of_hasCompactSupport
      (hk.cpt.comp_left Complex.ofReal_zero |>.mul_right)
  have hmass : ∫ y, (β y : ℂ) * f x ∂ν = f x := by
    rw [integral_mul_const, integral_complex_ofReal, hk.mass]
    simp
  have heq : f x - sm ν β f x = ∫ y, (β y : ℂ) * (f x - f (x * infEmb E N y)) ∂ν := by
    simp only [mul_sub]
    rw [integral_sub hi2 hi1, hmass]
    rfl
  have hgm : Measurable fun y => ‖f (x * infEmb E N y) - f x‖ₑ :=
    (continuous_enorm.comp (hc1.sub continuous_const)).measurable
  have hle : ‖f x - sm ν β f x‖ₑ ≤ ∫⁻ y, ‖f (x * infEmb E N y) - f x‖ₑ
      ∂(ν.withDensity fun y => ENNReal.ofReal (β y)) := by
    rw [heq, lintegral_withDensity_eq_lintegral_mul ν hwm hgm]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun y => ?_
    have hb : ‖(β y : ℂ)‖ₑ = ENNReal.ofReal (β y) := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (hk.nonneg y)]
    rw [enorm_mul, hb, enorm_sub_rev]
    rfl
  exact (pow_le_pow_left' hle 2).trans (lintegral_sq_le _ _ hgm.aemeasurable)

end GlobalTheory.CompanionTheory.Conc

theorem GlobalTheory.CompanionTheory.Conc.smNear : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure] [MeasurableSpace (archGroup E N)] [BorelSpace (archGroup E N)] (ν : Measure (archGroup E N)) [ν.IsHaarMeasure] (F : Set (GA E N)) (β : archGroup E N → ℝ) (c : ℝ≥0∞), IsFundamentalDomain (latticeGL E N) F μ → Ker ν β →
  ∀ f : GA E N → ℂ, Continuous f → (∀ y ∈ tsupport β, ∫⁻ x in F, ‖f (x * infEmb E N y) - f x‖ₑ ^ 2 ∂μ ≤ c) →
  ∫⁻ x in F, ‖f x - sm ν β f x‖ₑ ^ 2 ∂μ ≤ c := by
  intro E _ _ _ N _ _ μ _ _ _ ν _ F β c _ hk f hf hc
  have := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  have := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  have := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  have : LocallyCompactSpace (Matrix (Fin N) (Fin N) (Ad E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin N → Fin N → Ad E))
  have : LocallyCompactSpace (Matrix (Fin N) (Fin N) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  have : LocallyCompactSpace (GA E N) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  have : SecondCountableTopology (Matrix (Fin N) (Fin N) (Ad E)) :=
    inferInstanceAs (SecondCountableTopology (Fin N → Fin N → Ad E))
  have : SecondCountableTopology (Matrix (Fin N) (Fin N) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  have : SecondCountableTopology (GA E N) := Units.isEmbedding_embedProduct.secondCountableTopology
  have : SigmaCompactSpace (GA E N) := sigmaCompactSpace_of_locallyCompact_secondCountable
  have : SFinite μ := inferInstance
  have hwm : Measurable fun y => ENNReal.ofReal (β y) := hk.cont.measurable.ennreal_ofReal
  set P : Measure (archGroup E N) := ν.withDensity fun y => ENNReal.ofReal (β y) with hP
  have : IsProbabilityMeasure P := by
    refine ⟨?_⟩
    rw [hP, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (hk.cont.integrable_of_hasCompactSupport hk.cpt)
        (Eventually.of_forall hk.nonneg), hk.mass, ENNReal.ofReal_one]
  have hG : Continuous fun p : GA E N × archGroup E N => ‖f (p.1 * infEmb E N p.2) - f p.1‖ₑ ^ 2 :=
    (ENNReal.continuous_pow 2).comp (continuous_enorm.comp
      ((hf.comp (continuous_fst.mul (continuous_infEmb.comp continuous_snd))).sub
        (hf.comp continuous_fst)))
  have hae : ∀ᵐ y ∂P, y ∈ tsupport β := by
    rw [hP, ae_withDensity_iff hwm]
    refine Eventually.of_forall fun y hy => subset_tsupport _ ?_
    intro h0
    exact hy (by rw [h0, ENNReal.ofReal_zero])
  calc ∫⁻ x in F, ‖f x - sm ν β f x‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ x in F, ∫⁻ y, ‖f (x * infEmb E N y) - f x‖ₑ ^ 2 ∂P ∂μ :=
        lintegral_mono fun x => enorm_sub_sm_sq_le E N ν β hk f hf x
    _ = ∫⁻ y, ∫⁻ x in F, ‖f (x * infEmb E N y) - f x‖ₑ ^ 2 ∂μ ∂P :=
        lintegral_lintegral_swap hG.measurable.aemeasurable
    _ ≤ ∫⁻ _, c ∂P := lintegral_mono_ae (hae.mono fun y hy => hc y hy)
    _ = c := by simp
end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.LocC

open MeasureTheory GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.Rodier.SmIntEl GlobalTheory.CompanionTheory.MirFourier ValuativeRel

attribute [local instance] instMSpi instBSpi

section Final

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {i t : ℕ} {τ : MRep k (i + 1)} {σ : GRep k (t + 1)}

abbrev thL (ψ : AddChar k Circle) (s : kˣ) : Lball k i t s →* ℂˣ :=
  (mirChar k ψ ((i + 1) + t)).comp (Subgroup.inclusion (Lball_le s))

theorem thL_uEl (ψ : AddChar k Circle) (s : kˣ) (c : Fin (i + 1) → k) (d : Fin (t + 1) → k)
    (h : uEl k i t c d ∈ Lball k i t s) :
    thL ψ s ⟨uEl k i t c d, h⟩ = Circle.toUnits (ψ (d (Fin.last t))) :=
  mirChar_uEl ψ i t c d (Lball_le s h)

theorem isOpen_ker_thL (ψ : AddChar k Circle) (hψ : Continuous ψ) (s : kˣ) :
    IsOpen ((thL (i := i) (t := t) ψ s).ker : Set (Lball k i t s)) :=
  (GlobalTheory.CompanionTheory.BZPhiPG.Grp.mirChar_ker_open ψ hψ ((i + 1) + t)).preimage
    (show Continuous (Subgroup.inclusion (Lball_le (i := i) (t := t) s)) from continuous_subtype_val.subtype_mk _)

theorem iF_sub (ψ : AddChar k Circle) (hψ : Continuous ψ) (a b : XS τ σ) : iF ψ (a - b) = iF ψ a - iF ψ b :=
  (iL ψ hψ).map_sub a b

theorem iF_zero (ψ : AddChar k Circle) (hψ : Continuous ψ) : iF ψ (0 : XS τ σ) = 0 :=
  (iL ψ hψ).map_zero

theorem gen (ψ : AddChar k Circle) (hψ : Continuous ψ) (c : Fin (i + 1) → k) (d : Fin (t + 1) → k) (v : XS τ σ) :
    iF ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (uEl k i t c d) v - ((Circle.toUnits (ψ (d (Fin.last t))) : ℂˣ) : ℂ) • v) =
      ((Circle.toUnits (ψ (d (Fin.last t))) : ℂˣ) : ℂ) • (rU τ σ (Multiplicative.ofAdd c) (iF ψ v) - iF ψ v) := by
  have a1 := iF_smul ψ hψ ((Circle.toUnits (ψ (d (Fin.last t))) : ℂˣ) : ℂ) v
  have a2 := iF_translate ψ hψ v c d
  exact (iF_sub ψ hψ _ _).trans ((congrArg₂ (fun a b => a - b) a2 a1).trans (smul_sub _ _ _).symm)

theorem thL_eq (ψ : AddChar k Circle) (s : kˣ) (l : Mir k ((i + 1) + t + 1)) (hl : l ∈ Lball k i t s)
    (c : Fin (i + 1) → k) (d : Fin (t + 1) → k) (e : l = uEl k i t c d) :
    thL ψ s ⟨l, hl⟩ = Circle.toUnits (ψ (d (Fin.last t))) := by
  subst e
  exact thL_uEl ψ s c d hl

theorem mem_of_eq {V : Type} [AddCommGroup V] [Module ℂ V] (K : Submodule ℂ V) {z y : V} (h : z = y) (hy : y ∈ K) : z ∈ K :=
  h ▸ hy

theorem gen_mem (ψ : AddChar k Circle) (hψ : Continuous ψ) (s : kˣ) (l : Mir k ((i + 1) + (t + 1))) (hl : l ∈ Lball k i t s)
    (v : XS τ σ) :
    iF ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) l v - ((thL ψ s ⟨l, hl⟩ : ℂˣ) : ℂ) • v) ∈
      twKer (rU τ σ) (polyBall (i + 1) s) 1 := by
  have h := exists_of_mem_Lball hl
  refine Exists.elim h fun c h => Exists.elim h fun d h => ?_
  have hc := h.1
  have e := h.2.2
  have e1 : cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) l v = cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (uEl k i t c d) v :=
    congrArg (fun x => cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) x v) e
  have e2 : ((thL ψ s ⟨l, hl⟩ : ℂˣ) : ℂ) = ((Circle.toUnits (ψ (d (Fin.last t))) : ℂˣ) : ℂ) :=
    congrArg _ (thL_eq ψ s l hl c d e)
  have e3 := congrArg₂ (fun (a : XS τ σ) (b : ℂ) => iF ψ (a - b • v)) e1 e2
  refine mem_of_eq _ (e3.trans (gen ψ hψ c d v)) (Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨_, hc⟩, iF ψ v, ?_⟩))
  simp

theorem iF_twKer (ψ : AddChar k Circle) (hψ : Continuous ψ) (s : kˣ) (v : XS τ σ)
    (hv : v ∈ twKer (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ)) (Lball k i t s) (thL ψ s)) :
    iF ψ v ∈ twKer (rU τ σ) (polyBall (i + 1) s) 1 := by
  unfold twKer at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    refine Exists.elim hx fun l h => Exists.elim h fun v h => ?_
    exact mem_of_eq _ (congrArg (iF ψ) h) (gen_mem ψ hψ s l.1 l.2 v)
  | zero => exact mem_of_eq _ (iF_zero ψ hψ) (zero_mem _)
  | add x y _ _ hx hy => exact mem_of_eq _ (iF_add ψ hψ x y) (add_mem hx hy)
  | smul c x _ hx => exact mem_of_eq _ (iF_smul ψ hψ c x) (Submodule.smul_mem _ _ hx)

theorem eig_eval (ψ : AddChar k Circle) (s : kˣ) (g : XS τ σ)
    (g2 : ∀ l : Lball k i t s, cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (l : Mir k ((i + 1) + t + 1)) g = ((thL ψ s l : ℂˣ) : ℂ) • g)
    (c : Fin (i + 1) → k) (d : Fin (t + 1) → k) (hc : Multiplicative.ofAdd c ∈ polyBall (i + 1) s)
    (hd : Multiplicative.ofAdd d ∈ polyBall (t + 1) s) (x : Mir k ((i + 1) + t + 1)) :
    evX g (x * uEl k i t c d) = ((Circle.toUnits (ψ (d (Fin.last t))) : ℂˣ) : ℂ) • evX g x := by
  have hm := uEl_mem_Lball hc hd
  have e := congrArg (fun w : XS τ σ => evX w x) (g2 ⟨_, hm⟩)
  have e2 : ((thL ψ s ⟨_, hm⟩ : ℂˣ) : ℂ) = ((Circle.toUnits (ψ (d (Fin.last t))) : ℂˣ) : ℂ) :=
    congrArg _ (thL_uEl ψ s c d hm)
  exact (evX_cInd g _ x).symm.trans (e.trans ((evX_smul _ g x).trans (congrArg (fun b : ℂ => b • evX g x) e2)))

theorem supp_of (s : kˣ) (f : XS τ σ)
    (hF : ∀ d : Fin (t + 1) → k, evX f (dEmb k i t d * 1) ≠ 0 → Multiplicative.ofAdd d ∈ polyBall (t + 1) s)
    (l : Mir k ((i + 1) + t + 1)) (hl : l ∈ Lball k i t s) (d : Fin (t + 1) → k)
    (hne : evX f (dEmb k i t d * 1 * l) ≠ 0) : Multiplicative.ofAdd d ∈ polyBall (t + 1) s := by
  obtain ⟨c, d₁, hc, hd₁, rfl⟩ := exists_of_mem_Lball hl
  rw [dEmb_mul_uEl, evX_left] at hne
  have h3 : evX f (dEmb k i t (d + d₁) * 1) ≠ 0 := by
    intro h0
    exact hne (by rw [h0, map_zero])
  have h4 := (polyBall (t + 1) s).mul_mem (hF _ h3) ((polyBall (t + 1) s).inv_mem hd₁)
  have e : Multiplicative.ofAdd (d + d₁) * (Multiplicative.ofAdd d₁)⁻¹ = Multiplicative.ofAdd d := by
    rw [ofAdd_add, mul_inv_cancel_right]
  rwa [e] at h4

theorem avgVanish_of_data (ψ : AddChar k Circle) (hψ : Continuous ψ) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ)
    (f : XS τ σ) (s : kˣ) (hz : iF ψ f ∈ twKer (rU τ σ) (polyBall (i + 1) s) 1)
    (hF : ∀ d : Fin (t + 1) → k, evX f (dEmb k i t d * 1) ≠ 0 → Multiplicative.ofAdd d ∈ polyBall (t + 1) s)
    (g : XS τ σ) (g1 : f - g ∈ twKer (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ)) (Lball k i t s) (thL ψ s))
    (g2 : ∀ l : Lball k i t s, cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (l : Mir k ((i + 1) + t + 1)) g = ((thL ψ s l : ℂˣ) : ℂ) • g)
    (g3 : ∀ x : Mir k ((i + 1) + t + 1), evX g x ≠ 0 → ∃ l ∈ Lball k i t s, evX f (x * l) ≠ 0) :
    AvgVanish (HPG k (i + 1) (t + 1)) (sigX τ σ) (MirUin k ((i + 1) + t + 1)) (mirChar k ψ ((i + 1) + t)) f 1 := by
  have hsupp : ∀ d : Fin (t + 1) → k, evX g (dEmb k i t d * 1) ≠ 0 → Multiplicative.ofAdd d ∈ polyBall (t + 1) s := by
    intro d hd
    refine Exists.elim (g3 _ hd) fun l h => ?_
    exact supp_of s f hF l h.1 d h.2
  have hk : iF ψ g ∈ twKer (rU τ σ) (polyBall (i + 1) s) 1 := by
    have h5 := iF_twKer ψ hψ s (f - g) g1
    have e : iF ψ g = iF ψ f - iF ψ (f - g) := by
      have := iF_sub ψ hψ f g
      rw [this, sub_sub_cancel]
    exact mem_of_eq _ e (sub_mem hz h5)
  refine ⟨Lball k i t s, Lball_le s, isCompact_Lball s, g, g1, g2, fun u hu => ?_⟩
  refine Exists.elim (exists_uEl i t u hu) fun c h => Exists.elim h fun d e => ?_
  have h7 := vanish_of_eigen ψ hτ hσ s g (eig_eval ψ s g g2) hsupp hk c d
  have e2 : (1 : Mir k ((i + 1) + t + 1)) * u = uEl k i t c d := by rw [one_mul, e]
  exact (congrArg (evX g) e2).trans h7

theorem avgVanish_one (ψ : AddChar k Circle) (hψ : Continuous ψ) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ)
    (f : XS τ σ) (hq : qC τ σ (iF ψ f) = 0) :
    AvgVanish (HPG k (i + 1) (t + 1)) (sigX τ σ) (MirUin k ((i + 1) + t + 1)) (mirChar k ψ ((i + 1) + t)) f 1 := by
  obtain ⟨s₁, h₁⟩ := exists_polyBall_of_qC _ hq
  obtain ⟨s₂, h₂⟩ := exists_polyBall_of_compact
    (GlobalTheory.CompanionTheory.BZPhiPG.Fib.fibre_isLocallyConstant_hasCompactSupport k i t τ σ f 1).2
  obtain ⟨s, a, b⟩ := exists_val_ge s₁ s₂
  have hz : iF ψ f ∈ twKer (rU τ σ) (polyBall (i + 1) s) 1 := twKer_one_mono _ (polyBall_mono _ a) h₁
  have hF : ∀ d : Fin (t + 1) → k, evX f (dEmb k i t d * 1) ≠ 0 → Multiplicative.ofAdd d ∈ polyBall (t + 1) s :=
    fun d hd => polyBall_mono _ b (h₂ d (subset_tsupport _ hd))
  have hg := exists_avg (HPG k (i + 1) (t + 1)) (sigX τ σ) (Lball k i t s) (isCompact_Lball s)
    (thL ψ s) (isOpen_ker_thL ψ hψ s) f
  exact Exists.elim hg fun g h => avgVanish_of_data ψ hψ hτ hσ f s hz hF g h.1 h.2.1 h.2.2

theorem mirChar_sEmb_conj (ψ : AddChar k Circle) {n : ℕ} (m : Mir k n) (u : MirUin k (n + 1))
    (h : (sEmb k n m)⁻¹ * (u : Mir k (n + 1)) * sEmb k n m ∈ MirUin k (n + 1)) :
    mirChar k ψ n ⟨_, h⟩ = mirChar k ψ n u := by
  obtain ⟨w, hw⟩ := (Subgroup.mem_subgroupOf.1 u.2 : ((u : Mir k (n + 1)) : GL (Fin (n + 2)) k) ∈ MirU k (n + 1))
  rw [mirChar_eq k ψ n u w hw.symm]
  let mi : GL (Fin (n + 1)) k := ((m⁻¹ : Mir k n) : GL (Fin (n + 1)) k)
  have e0 : (((sEmb k n m)⁻¹ : Mir k (n + 1)) : GL (Fin (n + 2)) k) = glEmb k (n + 1) mi := by
    rw [← map_inv]
    rfl
  have e1 : ((sEmb k n m : Mir k (n + 1)) : GL (Fin (n + 2)) k) = (glEmb k (n + 1) mi)⁻¹ := by
    rw [← e0]
    simp
  have e : (((sEmb k n m)⁻¹ * (u : Mir k (n + 1)) * sEmb k n m : Mir k (n + 1)) : GL (Fin (n + 2)) k) =
      unip k (n + 1) (Multiplicative.ofAdd ((mi : Matrix _ _ k).mulVec w.toAdd)) := by
    simp only [Subgroup.coe_mul]
    rw [e0, e1, ← hw, glEmb_mul_unip', mul_inv_cancel_right]
  rw [mirChar_eq k ψ n ⟨_, h⟩ _ e, toAdd_ofAdd,
    mulVec_last_of_mem k mi (m⁻¹ : Mir k n).2 w.toAdd]

theorem avgVanish_cell (ψ : AddChar k Circle) (hψ : Continuous ψ) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ)
    (f : XS τ σ) (h0 : eC ψ f = 0) (h : Mir k ((i + 1) + t + 1)) (hh : h ∈ HPG k (i + 1) (t + 1))
    (d : Fin (t + 1) → k) (m : Mir k ((i + 1) + t)) :
    AvgVanish (HPG k (i + 1) (t + 1)) (sigX τ σ) (MirUin k ((i + 1) + t + 1)) (mirChar k ψ ((i + 1) + t)) f
      (h * dEmb k i t d * sEmb k ((i + 1) + t) m) := by
  have hq : qC τ σ (intC ψ f (sEmb k _ m)) = 0 := by
    have h1 : ((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) • qC τ σ (intC ψ f (sEmb k _ m)) = 0 := congrFun h0 m
    exact (smul_eq_zero.1 h1).resolve_left (Units.ne_zero _)
  have hp : phi ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sEmb k _ m) f) =
      fun d => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) • evX f (dEmb k i t d * sEmb k _ m) := by
    funext d
    simp only [phi]
    rw [evX_cInd, mul_one]
    rfl
  have hi : iF ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sEmb k _ m) f) = intC ψ f (sEmb k _ m) :=
    congrArg (GlobalTheory.CompanionTheory.Rodier.smInt (muD k (t + 1))) hp
  have A1 := avgVanish_one ψ hψ hτ hσ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sEmb k _ m) f)
    ((congrArg (qC τ σ) hi).trans hq)
  have hU : ∀ u ∈ MirUin k ((i + 1) + t + 1), sEmb k _ m * u * (sEmb k _ m)⁻¹ ∈ MirUin k ((i + 1) + t + 1) :=
    fun u hu => GlobalTheory.CompanionTheory.BZMirSeq.conj_mem_MirUin _ ⟨u, hu⟩
  have hU' : ∀ u ∈ MirUin k ((i + 1) + t + 1), (sEmb k _ m)⁻¹ * u * sEmb k _ m ∈ MirUin k ((i + 1) + t + 1) := by
    intro u hu
    have := GlobalTheory.CompanionTheory.BZMirSeq.conj_mem_MirUin (sEmb k _ m)⁻¹ ⟨u, hu⟩
    rwa [inv_inv] at this
  have A2 := avgVanish_conj _ _ _ _ (sEmb k _ m) hU hU' (fun u h => mirChar_sEmb_conj ψ m u h) f A1
  exact avgVanish_left _ _ _ _ f _ _ h hh (hU' _ (uEl_mem i t 0 d)) A2

end Final

theorem avgVanish_of_mem_Cl : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (f : XS τ σ) (h0 : eC ψ f = 0)
    (p : Mir k ((i + 1) + t + 1)) (hp : p ∈ Cl k i t),
  AvgVanish (HPG k (i + 1) (t + 1)) (sigX τ σ) (MirUin k ((i + 1) + t + 1)) (mirChar k ψ ((i + 1) + t)) f p := by
  intro k _ _ _ _ i t ψ hψ τ σ hτ hσ f h0 p hp
  refine Exists.elim ((GlobalTheory.CompanionTheory.BZPhiPG.Cells.cells k i t).1 p hp) fun h hh =>
    Exists.elim hh.2 fun d hd => Exists.elim hd fun m e => ?_
  exact (congrArg (AvgVanish (HPG k (i + 1) (t + 1)) (sigX τ σ) (MirUin k ((i + 1) + t + 1)) (mirChar k ψ ((i + 1) + t)) f) e).mpr
    (avgVanish_cell ψ hψ hτ hσ f h0 h hh.1 d m)

end GlobalTheory.CompanionTheory.BZPhiPG.LocC

end
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

theorem finite_units_zpow_eq {F : Type*} [Field F] {d : ℤ} (hd : d ≠ 0) (w : Fˣ) :
    {z : Fˣ | z ^ d = w}.Finite := by
  have hm : 0 < d.natAbs := Int.natAbs_pos.2 hd
  have key : ∀ c : F, {z : Fˣ | (z : F) ^ d.natAbs = c}.Finite := fun c =>
    ((Polynomial.nthRoots d.natAbs c).toFinset.finite_toSet.preimage
      (Units.val_injective (α := F)).injOn).subset fun z hz => by
        simpa [Polynomial.mem_nthRoots hm] using hz
  rcases Int.natAbs_eq d with h | h
  · refine (key (w : F)).subset fun z hz => ?_
    have hz' : z ^ d = w := hz
    rw [h, zpow_natCast] at hz'
    change (z : F) ^ d.natAbs = w
    rw [← Units.val_pow_eq_pow_val, hz']
  · refine (key ((w⁻¹ : Fˣ) : F)).subset fun z hz => ?_
    have hz' : z ^ d = w := hz
    rw [h, zpow_neg, zpow_natCast] at hz'
    change (z : F) ^ d.natAbs = ((w⁻¹ : Fˣ) : F)
    rw [← Units.val_pow_eq_pow_val, ← hz', inv_inv]

theorem eq_one_of_tpow_mul_unit_eigen {l : ℕ} [Fact l.Prime] (L : IntermediateField ℚ_[l] (Om l))
    [FiniteDimensional ℚ_[l] ↥L]
    (hI : ((GroundTheory.PAdicHodge.cycloChar L) ''
        {σ : Gal(Om l/↥L) | ∀ w ∈ GroundTheory.PAdicHodge.unramifiedClosure l, σ w = w}).Infinite)
    (u : (Formalism.Per6.BdRp l)ˣ) (n : ℕ) (a : Gal(Om l/↥L) → ℚ_[l])
    (hact : ∀ σ : Gal(Om l/↥L), σ • (GroundTheory.PAdicHodge.tBdR l ^ n * (u : Formalism.Per6.BdRp l)) =
      algebraMap ℚ_[l] (Formalism.Per6.BdRp l) (a σ) * (GroundTheory.PAdicHodge.tBdR l ^ n * (u : Formalism.Per6.BdRp l)))
    (hin : ∀ σ : Gal(Om l/↥L), (∀ w ∈ GroundTheory.PAdicHodge.unramifiedClosure l, σ w = w) →
      a σ = (((GroundTheory.PAdicHodge.cycloChar L σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])) :
    n = 1 := by
  by_contra hn
  have ht : GroundTheory.PAdicHodge.tBdR l ≠ 0 := (GroundTheory.PAdicHodge.irreducible_tBdR (p := l)).ne_zero
  let c : ℤ_[l]ˣ →* ℚ_[l]ˣ := Units.map (PadicInt.Coe.ringHom (p := l)).toMonoidHom
  have hc : Function.Injective c := fun x y h =>
    Units.ext (Subtype.ext (congrArg Units.val h))
  let χ : Gal(Om l/↥L) → ℚ_[l] := fun σ => (((GroundTheory.PAdicHodge.cycloChar L σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])
  have hχ : ∀ σ, χ σ ≠ 0 := fun σ => (c (GroundTheory.PAdicHodge.cycloChar L σ)).ne_zero
  let A : ℚ_[l] →+* Formalism.Per6.BdRp l := algebraMap ℚ_[l] (Formalism.Per6.BdRp l)
  have hu : ∀ σ : Gal(Om l/↥L), A (χ σ) ^ n * (σ • (u : Formalism.Per6.BdRp l)) = A (a σ) * u := by
    intro σ
    have h := hact σ
    rw [smul_mul', smul_pow', GroundTheory.PAdicHodge.gal_smul_tBdR, mul_pow] at h
    refine mul_left_cancel₀ (pow_ne_zero n ht) ?_
    change _ = _ at h
    linear_combination h
  have hu' : ∀ σ : Gal(Om l/↥L), σ • (u : Formalism.Per6.BdRp l) = A (a σ * (χ σ ^ n)⁻¹) * u := by
    intro σ
    have e : A ((χ σ ^ n)⁻¹) * A (χ σ) ^ n = 1 := by
      rw [← map_pow, ← map_mul, inv_mul_cancel₀ (pow_ne_zero n (hχ σ)), map_one]
    calc σ • (u : Formalism.Per6.BdRp l)
        = (A ((χ σ ^ n)⁻¹) * A (χ σ) ^ n) * (σ • (u : Formalism.Per6.BdRp l)) := by rw [e, one_mul]
      _ = A ((χ σ ^ n)⁻¹) * (A (a σ) * u) := by rw [mul_assoc, hu]
      _ = A (a σ * (χ σ ^ n)⁻¹) * u := by rw [map_mul]; ring
  have hx0 : GroundTheory.PAdicHodge.thetaAlgHom l (u : Formalism.Per6.BdRp l) ≠ 0 :=
    (u.isUnit.map (GroundTheory.PAdicHodge.thetaAlgHom l)).ne_zero
  have hθ : ∀ (σ : Gal(Om l/↥L)) (q : ℚ_[l]),
      σ • (u : Formalism.Per6.BdRp l) = algebraMap ℚ_[l] (Formalism.Per6.BdRp l) q * u →
        σ • GroundTheory.PAdicHodge.thetaAlgHom l (u : Formalism.Per6.BdRp l) =
          algebraMap ℚ_[l] ℂ_[l] q * GroundTheory.PAdicHodge.thetaAlgHom l (u : Formalism.Per6.BdRp l) := by
    intro σ q h
    rw [GroundTheory.PAdicHodge.thetaAlgHom_apply, ← GroundTheory.PAdicHodge.thetaBDeRhamPlusField_gal_smul, h,
      ← GroundTheory.PAdicHodge.thetaAlgHom_apply, map_mul, AlgHom.commutes]
    rfl
  obtain ⟨ψ, hψc, hψx⟩ := GroundTheory.PAdicHodge.EigenChar.exists_eigenChar hx0
    fun σ : Gal(Om l/↥L) => ⟨_, hθ σ _ (hu' σ)⟩
  have hfin := GroundTheory.PAdicHodge.ACris.senTateCharacters (p := l) L ψ hψc _ hx0 hψx
  have hd : (1 - (n : ℤ)) ≠ 0 := fun h => hn (by omega)
  have hψ : ∀ σ : Gal(Om l/↥L), (∀ w ∈ GroundTheory.PAdicHodge.unramifiedClosure l, σ w = w) →
      (c (GroundTheory.PAdicHodge.cycloChar L σ)) ^ (1 - (n : ℤ)) = ψ σ := by
    intro σ hσ
    have h2 : a σ * (χ σ ^ n)⁻¹ = ψ σ := GroundTheory.PAdicHodge.EigenChar.eq_of_mul_eq hx0
      ((hθ σ _ (hu' σ)).symm.trans (hψx σ))
    refine Units.ext ?_
    rw [Units.val_zpow_eq_zpow_val, ← h2, hin σ hσ]
    change χ σ ^ (1 - (n : ℤ)) = χ σ * (χ σ ^ n)⁻¹
    rw [zpow_sub₀ (hχ σ), zpow_one, zpow_natCast, div_eq_mul_inv]
  refine (hI.image hc.injOn) (Set.Finite.of_finite_fibers (fun z => z ^ (1 - (n : ℤ))) ?_ ?_)
  · refine hfin.subset ?_
    rintro _ ⟨_, ⟨_, ⟨σ, hσ, rfl⟩, rfl⟩, rfl⟩
    exact ⟨σ, hσ, (hψ σ hσ).symm⟩
  · intro w _
    refine (finite_units_zpow_eq hd w).subset fun z hz => ?_
    exact hz.2

end GlobalTheory.CompanionTheory.LTPer
end
end

section

open GlobalTheory.PRep PositivityTheory.SphericalProduct

theorem _root_.GlobalTheory.T.dominant_coset_reps_unipotent : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (D : PositivityTheory.SphericalProduct.CassData G), ∀ t : D.T, D.IsDom t → ∃ r : ℕ, 0 < r ∧ ∃ x : Fin r → G, (∀ i, x i ∈ D.J ⊓ D.N) ∧ ∀ y ∈ D.J, ∃! i, (x i)⁻¹ * y ∈ D.J ⊓ D.J.map (MulAut.conj (t : G)).toMonoidHom := by
  first | exact @GlobalTheory.CompanionTheory.Casselman.exists_fin_coset_reps_of_isDom | exact GlobalTheory.CompanionTheory.Casselman.exists_fin_coset_reps_of_isDom | (intros; apply GlobalTheory.CompanionTheory.Casselman.exists_fin_coset_reps_of_isDom <;> assumption)
end
