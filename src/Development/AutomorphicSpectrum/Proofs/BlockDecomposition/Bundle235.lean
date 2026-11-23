module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle045
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EpowTSucc
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveSolutionExistence
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.DiscreteSeriesTopClasses.IsInvOne
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Topology.Instances.Matrix
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle219
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle220
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Matrix.Normed
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle216
import Std.Tactic.BVDecide.Normalize.Bool
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.RightHolRightHolEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle206
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle205
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle214
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import GroundTheory.LocalFields.Bundle001
import GroundTheory.LocalFields.FormalGroups.Bundle001
import GroundTheory.PAdicHodge.Bundle004
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise

open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ConeHaar.OpenCone

variable {n : ℕ}

theorem hOf_herm (v : Fin n × Fin n → ℝ) : (hOf v).IsHermitian := by
  show (hOf v)ᴴ = hOf v
  simp [hOf, conjTranspose_sum, conjTranspose_smul, GlobalTheory.CompanionTheory.TwistHomotopy.hb_conjTranspose]

theorem im_form {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) (x : Fin n → ℂ) :
    (star x ⬝ᵥ M *ᵥ x).im = 0 := by
  have h : star (star x ⬝ᵥ M *ᵥ x) = star x ⬝ᵥ M *ᵥ x := by
    conv_rhs => rw [Matrix.star_dotProduct]
    rw [Matrix.star_mulVec, hM.eq, ← Matrix.dotProduct_mulVec]
  exact Complex.conj_eq_iff_im.mp h

theorem continuous_form :
    Continuous fun z : (Fin n × Fin n → ℝ) × (Fin n → ℂ) => (star z.2 ⬝ᵥ hOf z.1 *ᵥ z.2).re := by
  have hent : ∀ i j : Fin n, Continuous fun v : Fin n × Fin n → ℝ => hOf v i j := by
    intro i j
    have : (fun v : Fin n × Fin n → ℝ => hOf v i j) = fun v => ∑ p, (v p : ℂ) * hb p i j := by
      funext v
      simp [hOf, Matrix.sum_apply]
    rw [this]
    fun_prop
  have hent' : ∀ i j : Fin n,
      Continuous fun z : (Fin n × Fin n → ℝ) × (Fin n → ℂ) => hOf z.1 i j :=
    fun i j => (hent i j).comp continuous_fst
  simp only [dotProduct, mulVec, Pi.star_apply]
  refine Complex.continuous_re.comp ?_
  refine continuous_finsetSum _ fun i _ => ?_
  refine (continuous_star.comp ((continuous_apply i).comp continuous_snd)).mul ?_
  refine continuous_finsetSum _ fun j _ => ?_
  exact (hent' i j).mul ((continuous_apply j).comp continuous_snd)

theorem posDef_of_sphere {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian)
    (h : ∀ x ∈ Metric.sphere (0 : Fin n → ℂ) 1, 0 < (star x ⬝ᵥ M *ᵥ x).re) : M.PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨hM, fun x hx => ?_⟩
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hy : ((‖x‖⁻¹ : ℝ) : ℂ) • x ∈ Metric.sphere (0 : Fin n → ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul]
    simp [hn]
  have h1 := h _ hy
  have h2 : star (((‖x‖⁻¹ : ℝ) : ℂ) • x) ⬝ᵥ M *ᵥ (((‖x‖⁻¹ : ℝ) : ℂ) • x) =
      (((‖x‖⁻¹ ^ 2 : ℝ)) : ℂ) * (star x ⬝ᵥ M *ᵥ x) := by
    rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
    simp [smul_eq_mul, pow_two]
    ring
  rw [h2, Complex.re_ofReal_mul] at h1
  have h3 : 0 < (star x ⬝ᵥ M *ᵥ x).re := by
    have : 0 < ‖x‖⁻¹ ^ 2 := by positivity
    exact (pos_iff_pos_of_mul_pos h1).1 this
  exact Complex.pos_iff.2 ⟨h3, (im_form hM x).symm⟩

end GlobalTheory.CompanionTheory.ConeHaar.OpenCone

namespace GlobalTheory.CompanionTheory.ConeHaar

open OpenCone

theorem isOpen_cone : ∀ n : ℕ, IsOpen (PositivityTheory.RgBcC.cone n) := by
  intro n
  rw [isOpen_iff_eventually]
  intro v hv
  have hpos : ∀ x ∈ Metric.sphere (0 : Fin n → ℂ) 1, 0 < (star x ⬝ᵥ hOf v *ᵥ x).re := by
    intro x hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    have := (Matrix.posDef_iff_dotProduct_mulVec.1 hv).2 hx0
    exact (Complex.pos_iff.1 this).1
  have hev : ∀ᶠ w in 𝓝 v, ∀ x ∈ Metric.sphere (0 : Fin n → ℂ) 1,
      0 < (star x ⬝ᵥ hOf w *ᵥ x).re :=
    (isCompact_sphere (0 : Fin n → ℂ) 1).eventually_forall_of_forall_eventually fun x hx =>
      (continuous_form.continuousAt (x := (v, x))).eventually (lt_mem_nhds (hpos x hx))
  exact hev.mono fun w hw => posDef_of_sphere (hOf_herm w) hw

end GlobalTheory.CompanionTheory.ConeHaar
end
end

section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.Ibp

variable {n : ℕ}

section Int

variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

theorem integrable_of_cpt (hL : LgFacts) {φ : Mat n → ℂ} (hφ : ContinuousOn φ (GLs n)) (cφ : Cpt φ) :
    Integrable (fun y : G n => φ y.val) μ := by
  obtain ⟨R, hR⟩ := cφ
  have hc : Continuous (fun y : G n => φ y.val) :=
    hφ.comp_continuous Units.continuous_val val_mem
  refine hc.integrable_of_hasCompactSupport (HasCompactSupport.intro ((hL n).2.2.2.2.1 R) ?_)
  intro y hy
  exact hR _ (val_mem y) (not_le.1 hy)

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem sm_inner {f h : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hh : ContDiffOn ℝ ∞ h (GLs n)) :
    ContDiffOn ℝ ∞ (fun y => ⟪f y, h y⟫_ℂ) (GLs n) :=
  hf.inner ℂ hh

theorem Cpt_inner {f h : Mat n → V} (cf : Cpt f) : Cpt (fun y => ⟪f y, h y⟫_ℂ) := by
  obtain ⟨R, hR⟩ := cf
  exact ⟨R, fun y hy hl => by simp [hR y hy hl]⟩

theorem Cpt_inner' {f h : Mat n → V} (ch : Cpt h) : Cpt (fun y => ⟪f y, h y⟫_ℂ) := by
  obtain ⟨R, hR⟩ := ch
  exact ⟨R, fun y hy hl => by simp [hR y hy hl]⟩

theorem int_inner (hL : LgFacts) {f h : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hh : ContDiffOn ℝ ∞ h (GLs n)) (cf : Cpt f) :
    Integrable (fun y : G n => ⟪f y.val, h y.val⟫_ℂ) μ :=
  integrable_of_cpt μ hL (sm_inner hf hh).continuousOn (Cpt_inner cf)

theorem int_inner' (hL : LgFacts) {f h : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hh : ContDiffOn ℝ ∞ h (GLs n)) (ch : Cpt h) :
    Integrable (fun y : G n => ⟪f y.val, h y.val⟫_ℂ) μ :=
  integrable_of_cpt μ hL (sm_inner hf hh).continuousOn (Cpt_inner' ch)

theorem ibp_Rd (hL : LgFacts) (hR : RCalc) (X : Mat n) {f h : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (hh : ContDiffOn ℝ ∞ h (GLs n)) (cf : Cpt f) (ch : Cpt h) :
    ∫ y : G n, ⟪Rd X f y.val, h y.val⟫_ℂ ∂μ = -∫ y : G n, ⟪f y.val, Rd X h y.val⟫_ℂ ∂μ := by
  have h0 := (hR n).2.2 μ ℂ (fun y => ⟪f y, h y⟫_ℂ) (sm_inner hf hh) (Cpt_inner cf) X
  have e : ∀ y : G n, Rd X (fun y => ⟪f y, h y⟫_ℂ) y.val =
      ⟪f y.val, Rd X h y.val⟫_ℂ + ⟪Rd X f y.val, h y.val⟫_ℂ := by
    intro y
    exact fderiv_inner_apply ℂ (diffAt hf (val_mem y)) (diffAt hh (val_mem y)) _
  simp_rw [e] at h0
  rw [integral_add (int_inner' μ hL hf (sm_Rd hR X hh) (Cpt_Rd hL X ch))
    (int_inner μ hL (sm_Rd hR X hf) hh (Cpt_Rd hL X cf))] at h0
  exact eq_neg_of_add_eq_zero_right h0

theorem ibp_Eu (hL : LgFacts) (hR : RCalc) (s : Bool) (a b : Fin n) {f h : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (hh : ContDiffOn ℝ ∞ h (GLs n)) (cf : Cpt f) (ch : Cpt h) :
    ∫ y : G n, ⟪Eu s a b f y.val, h y.val⟫_ℂ ∂μ = -∫ y : G n, ⟪f y.val, Eu (!s) a b h y.val⟫_ℂ ∂μ := by
  set X : Mat n := Matrix.single a b 1
  set Y : Mat n := Matrix.single a b Complex.I
  set c : ℂ := if !s then -Complex.I else Complex.I with hc
  have hc' : conj (if s then -Complex.I else Complex.I) = c := by
    cases s <;> simp [hc]
  have e1 : ∀ y : G n, ⟪Eu s a b f y.val, h y.val⟫_ℂ =
      (1 / 2 : ℂ) * (⟪Rd X f y.val, h y.val⟫_ℂ + c * ⟪Rd Y f y.val, h y.val⟫_ℂ) := by
    intro y
    have h2 : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
      rw [map_div₀, map_one, map_ofNat]
    simp only [Eu, Pi.smul_apply, Pi.add_apply, inner_smul_left, inner_add_left, hc', h2]
    rfl
  have e2 : ∀ y : G n, ⟪f y.val, Eu (!s) a b h y.val⟫_ℂ =
      (1 / 2 : ℂ) * (⟪f y.val, Rd X h y.val⟫_ℂ + c * ⟪f y.val, Rd Y h y.val⟫_ℂ) := by
    intro y
    simp only [Eu, Pi.smul_apply, Pi.add_apply, inner_smul_right, inner_add_right]
    simp [X, Y, hc]
  simp_rw [e1, e2]
  rw [integral_const_mul, integral_const_mul,
    integral_add (int_inner μ hL (sm_Rd hR X hf) hh (Cpt_Rd hL X cf))
      ((int_inner μ hL (sm_Rd hR Y hf) hh (Cpt_Rd hL Y cf)).const_mul c),
    integral_add (int_inner' μ hL hf (sm_Rd hR X hh) (Cpt_Rd hL X ch))
      ((int_inner' μ hL hf (sm_Rd hR Y hh) (Cpt_Rd hL Y ch)).const_mul c),
    integral_const_mul, integral_const_mul, ibp_Rd μ hL hR X hf hh cf ch, ibp_Rd μ hL hR Y hf hh cf ch]
  ring

theorem ibp_Epow (hL : LgFacts) (hR : RCalc) (s : Bool) (m : ℕ) (a b : Fin n) {f h : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (hh : ContDiffOn ℝ ∞ h (GLs n)) (cf : Cpt f) (ch : Cpt h) :
    ∫ y : G n, ⟪Epow s m a b f y.val, h y.val⟫_ℂ ∂μ =
      (-1 : ℂ) ^ m * ∫ y : G n, ⟪f y.val, EpowT (!s) m b a h y.val⟫_ℂ ∂μ := by
  induction m generalizing a h with
  | zero =>
    by_cases hab : a = b
    · subst hab
      simp [Epow, EpowT]
    · simp [Epow, EpowT, hab, Ne.symm hab]
  | succ m ih =>
    have e1 : ∀ y : G n, ⟪Epow s (m + 1) a b f y.val, h y.val⟫_ℂ =
        ∑ c, ⟪Eu s a c (Epow s m c b f) y.val, h y.val⟫_ℂ := by
      intro y
      simp only [Epow, Finset.sum_apply, sum_inner]
    have e2 : ∀ y : G n, ⟪f y.val, EpowT (!s) (m + 1) b a h y.val⟫_ℂ =
        ∑ c, ⟪f y.val, EpowT (!s) m b c (Eu (!s) a c h) y.val⟫_ℂ := by
      intro y
      rw [EpowT_succ' hR (!s) m a b hh (val_mem y), Finset.sum_apply, inner_sum]
    simp_rw [e1, e2]
    rw [MeasureTheory.integral_finsetSum _ fun c _ => int_inner μ hL (sm_Eu hR s a c (sm_Epow hR s m c b hf)) hh
        (Cpt_Eu hL s a c (Cpt_Epow hL s m c b cf)),
      MeasureTheory.integral_finsetSum _ fun c _ => int_inner μ hL hf
        (sm_EpowT hR (!s) m b c (sm_Eu hR (!s) a c hh)) cf,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [ibp_Eu μ hL hR s a c (sm_Epow hR s m c b hf) hh (Cpt_Epow hL s m c b cf) ch,
      ih c (sm_Eu hR (!s) a c hh) (Cpt_Eu hL (!s) a c ch), pow_succ]
    ring

end Int

theorem ibp_gel : LgFacts → RCalc → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)]
    (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] (s : Bool) (m : ℕ) (f h : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) →
    ContDiffOn ℝ ∞ h (GLs n) → Cpt f → Cpt h →
    ∫ y : G n, ⟪gel s m f y.val, h y.val⟫_ℂ ∂μ =
      (-1 : ℂ) ^ m * ∫ y : G n, ⟪f y.val, gelT (!s) m h y.val⟫_ℂ ∂μ := by
  intro hL hR n _ _ μ _ V _ _ _ s m f h hf hh cf ch
  have e1 : ∀ y : G n, ⟪gel s m f y.val, h y.val⟫_ℂ = ∑ a, ⟪Epow s m a a f y.val, h y.val⟫_ℂ := by
    intro y
    simp only [gel, Finset.sum_apply, sum_inner]
  have e2 : ∀ y : G n, ⟪f y.val, gelT (!s) m h y.val⟫_ℂ =
      ∑ a, ⟪f y.val, EpowT (!s) m a a h y.val⟫_ℂ := by
    intro y
    simp only [gelT, Finset.sum_apply, inner_sum]
  simp_rw [e1, e2]
  rw [MeasureTheory.integral_finsetSum _ fun a _ => int_inner μ hL (sm_Epow hR s m a a hf) hh
      (Cpt_Epow hL s m a a cf),
    MeasureTheory.integral_finsetSum _ fun a _ => int_inner μ hL hf (sm_EpowT hR (!s) m a a hh) cf,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => ibp_Epow μ hL hR s m a a hf hh cf ch

end GlobalTheory.CompanionTheory.WaveMult.Ibp
end
end

section

noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveK GlobalTheory.CompanionTheory

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveK.Word

variable {n : ℕ}

section Defs

variable {L : Type} [NormedAddCommGroup L] [NormedSpace ℂ L]

structure Cl (K : Mat n → Mat n → L) : Prop where
  smooth : ContDiffOn ℝ ∞ (Function.uncurry K) (GLs n ×ˢ GLs n)
  supp : ∃ R, ∀ x ∈ GLs n, ∀ y ∈ GLs n, R + lg x < lg y → K x y = 0

def kK (k : Mat n → L) : Mat n → Mat n → L := fun x y => k (x⁻¹ * y)

def Iop {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [MeasurableSpace (G n)] (μ : Measure (G n))
    (K : Mat n → Mat n → (V →L[ℂ] V)) (φ : Mat n → V) : Mat n → V :=
  fun x => ∫ y : G n, K x y.val (φ y.val) ∂μ

end Defs

section ClB
variable {L : Type} [NormedAddCommGroup L] [NormedSpace ℂ L]

end ClB

section Lem
variable {L : Type} [NormedAddCommGroup L] [NormedSpace ℂ L]

theorem contDiff_ent (a b : Fin n) : ContDiff ℝ ∞ (fun y : Mat n => y a b) :=
  (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a b)).contDiff

theorem contDiffOn_invMul : ContDiffOn ℝ ∞ (fun p : Mat n × Mat n => p.1⁻¹ * p.2) (GLs n ×ˢ GLs n) := by
  have hinv : ContDiffOn ℝ ∞ (fun p : Mat n × Mat n => p.1⁻¹) (GLs n ×ˢ GLs n) :=
    (ReciprocityTheory.ChartRestriction.DS.Lap.LemK.contDiffOn_inv_det_ne_zero.restrict_scalars ℝ).comp (f := Prod.fst) contDiff_fst.contDiffOn
      fun p hp => hp.1
  refine contDiffOn_pi.2 fun a => contDiffOn_pi.2 fun b => ?_
  simp only [Matrix.mul_apply]
  refine ContDiffOn.sum fun c _ => ContDiffOn.mul ?_ ?_
  · exact (contDiff_ent a c).comp_contDiffOn hinv
  · exact ((contDiff_ent c b).comp contDiff_snd).contDiffOn

theorem cl_kK (hL : LgFacts) {k : Mat n → L} (hk : ContDiffOn ℝ ∞ k (GLs n)) {R : ℝ}
    (hR : ∀ y ∈ GLs n, R < lg y → k y = 0) : Cl (kK k) := by
  refine ⟨hk.comp contDiffOn_invMul fun p hp => GlobalTheory.CompanionTheory.WaveAll.mul_mem_GLs (GlobalTheory.CompanionTheory.WaveMult.inv_mem_GLs hp.1) hp.2,
    R, fun x hx y hy hl => ?_⟩
  have hz := GlobalTheory.CompanionTheory.WaveAll.mul_mem_GLs (GlobalTheory.CompanionTheory.WaveMult.inv_mem_GLs hx) hy
  refine hR _ hz ?_
  have h := (hL n).1 x hx _ hz
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 hx)] at h
  linarith

end Lem

section Lem2
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

end Lem2

section Lem3
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

end Lem3

section Basic
variable {L : Type} [NormedAddCommGroup L] [NormedSpace ℂ L]

end Basic

section Pairs

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

variable {μ} {φ : Mat n → V}

theorem act_eq_Iop (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V)) (f : Mat n → E.V) {x : Mat n} (hx : x ∈ GLs n) :
    act μ E k f x = Iop μ (kK k) f x := by
  let xG : G n := Matrix.GeneralLinearGroup.mkOfDetNeZero x hx
  have hv : xG.val = x := rfl
  have hdet : IsUnit x.det := isUnit_iff_ne_zero.2 hx
  have h := integral_mul_left_eq_self (μ := μ) (fun y : G n => k (x⁻¹ * y.val) (f y.val)) xG
  simp only [Iop, kK, act]
  rw [← h]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [Units.val_mul, hv, Matrix.nonsing_inv_mul_cancel_left _ _ hdet]

end Pairs

end GlobalTheory.CompanionTheory.WaveK.Word
end
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.skew_hermitian_unitary_flow : ∀ {n : ℕ} (Y : Mat n), Yᴴ = -Y → ∃ c : ℝ → Matrix.unitaryGroup (Fin n) ℂ, Continuous c ∧ c 0 = 1 ∧ (∀ s t, c (s + t) = c s * c t) ∧ HasDerivAt (fun t => (c t).1) Y 0 := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.UnitaryCurve.exists_unitary_curve | exact GlobalTheory.CompanionTheory.WaveSpd.UnitaryCurve.exists_unitary_curve | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.UnitaryCurve.exists_unitary_curve <;> assumption)
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

theorem GlobalTheory.CompanionTheory.LTHodge.isSepClosure_Om_of_range : ∀ {l : ℕ} [Fact l.Prime] {F : Type} [Field F] [Algebra F (Om l)] (K : FinExt l),
    Set.range (algebraMap F (Om l)) = (K.1 : Set (Om l)) → IsSepClosure F (Om l) := by
  intro l _ F _ _ K hK
  have hmem : ∀ q : ℚ_[l], algebraMap ℚ_[l] (Om l) q ∈ (algebraMap F (Om l)).fieldRange := by
    intro q
    have h : algebraMap ℚ_[l] (Om l) q ∈ Set.range (algebraMap F (Om l)) := by
      rw [hK]
      exact K.1.algebraMap_mem q
    obtain ⟨y, hy⟩ := h
    exact ⟨y, hy⟩
  let e := (algebraMap F (Om l)).rangeRestrictFieldEquiv
  let φ : ℚ_[l] →+* F :=
    e.symm.toRingHom.comp ((algebraMap ℚ_[l] (Om l)).codRestrict (algebraMap F (Om l)).fieldRange hmem)
  have hφ : ∀ q, algebraMap F (Om l) (φ q) = algebraMap ℚ_[l] (Om l) q := by
    intro q
    have h := congrArg Subtype.val (e.apply_symm_apply ⟨algebraMap ℚ_[l] (Om l) q, hmem q⟩)
    exact h
  have hcomp : (algebraMap F (Om l)).comp φ = algebraMap ℚ_[l] (Om l) := RingHom.ext hφ
  haveI : CharZero F := (algebraMap F (Om l)).charZero
  haveI halg : Algebra.IsAlgebraic F (Om l) := by
    constructor
    intro x
    obtain ⟨p, hp0, hpx⟩ := Algebra.IsAlgebraic.isAlgebraic (R := ℚ_[l]) x
    refine ⟨p.map φ, (Polynomial.map_ne_zero_iff φ.injective).mpr hp0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp, ← Polynomial.aeval_def]
    exact hpx
  exact IsSepClosure.mk inferInstance (Algebra.IsAlgebraic.isSeparable_of_perfectField)
end
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.continuous_one_param_differentiable : ∀ {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (Φ : ℝ → 𝔸), Continuous Φ → Φ 0 = 1 → (∀ s t, Φ (s + t) = Φ s * Φ t) → ∃ B, HasDerivAt Φ B 0 := by
  first | exact @GlobalTheory.CompanionTheory.OneParam.hasDerivAt_zero_of_continuous_oneParam | exact GlobalTheory.CompanionTheory.OneParam.hasDerivAt_zero_of_continuous_oneParam | (intros; apply GlobalTheory.CompanionTheory.OneParam.hasDerivAt_zero_of_continuous_oneParam <;> assumption)
end
