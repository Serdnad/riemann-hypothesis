module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle007
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle004
public import Mathlib.Algebra.MvPolynomial.Cardinal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Localization.Cardinality
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open scoped ContDiff

noncomputable section

namespace LeviHolPerturb

variable {J : Type} [Fintype J]

theorem hasDerivAt_of_contDiffAt_two {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ → F}
    (hf : ContDiffAt ℝ 2 f 0) :
    (∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt f (deriv f t) t) ∧ HasDerivAt (deriv f) (deriv (deriv f) 0) 0 := by
  refine ⟨?_, ?_⟩
  · filter_upwards [hf.eventually (by simp)] with t ht
    exact (ht.differentiableAt (by norm_num)).hasDerivAt
  · have h1 : ContDiffAt ℝ 1 (fun t => fderiv ℝ f t 1) 0 :=
      (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
    exact (h1.differentiableAt one_ne_zero).hasDerivAt

theorem deriv_deriv_mul {f g : ℝ → ℝ} (hf : ContDiffAt ℝ 2 f 0) (hg : ContDiffAt ℝ 2 g 0) :
    deriv (deriv fun t => f t * g t) 0 =
      deriv (deriv f) 0 * g 0 + 2 * (deriv f 0 * deriv g 0) + f 0 * deriv (deriv g) 0 := by
  obtain ⟨hf1, hf2⟩ := hasDerivAt_of_contDiffAt_two hf
  obtain ⟨hg1, hg2⟩ := hasDerivAt_of_contDiffAt_two hg
  have hev : deriv (fun t => f t * g t) =ᶠ[𝓝 0] fun t => deriv f t * g t + f t * deriv g t := by
    filter_upwards [hf1, hg1] with t h1 h2
    exact (h1.mul h2).deriv
  rw [hev.deriv_eq]
  refine ((hf2.mul hg1.self_of_nhds).add (hf1.self_of_nhds.mul hg2)).deriv.trans ?_
  ring

theorem deriv_line {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : (J → ℂ) → F} {z : J → ℂ}
    (hf : DifferentiableAt ℝ f z) (e : J → ℂ) :
    deriv (fun s : ℝ => f (z + s • e)) 0 = fderiv ℝ f z e := by
  have hline : HasDerivAt (fun s : ℝ => z + s • e) e 0 :=
    (((hasDerivAt_id (0 : ℝ)).smul_const e).const_add z).congr_deriv (one_smul ℝ e)
  have hz0 : z + (0 : ℝ) • e = z := by rw [zero_smul, add_zero]
  exact (hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline hz0.symm).deriv

theorem deriv_deriv_line {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : (J → ℂ) → F}
    {z : J → ℂ} (hf : ContDiffAt ℝ 2 f z) (e : J → ℂ) :
    deriv (deriv fun s : ℝ => f (z + s • e)) 0 = fderiv ℝ (fderiv ℝ f) z e e := by
  have hline : ∀ s : ℝ, HasDerivAt (fun s : ℝ => z + s • e) e s := fun s =>
    (((hasDerivAt_id s).smul_const e).const_add z).congr_deriv (one_smul ℝ e)
  have hz0 : z + (0 : ℝ) • e = z := by rw [zero_smul, add_zero]
  have hcont : Tendsto (fun s : ℝ => z + s • e) (𝓝 0) (𝓝 z) := by
    have h := (hline 0).continuousAt.tendsto
    rwa [hz0] at h
  have hfe : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ 2 f y := hf.eventually (by simp)
  have hev : deriv (fun s : ℝ => f (z + s • e)) =ᶠ[𝓝 0] fun s => fderiv ℝ f (z + s • e) e := by
    filter_upwards [hcont.eventually hfe] with s hs
    have h := (hs.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt s (hline s)
    exact h.deriv
  have hH : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) z) z :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hA : HasFDerivAt (fun y => fderiv ℝ f y e) ((fderiv ℝ (fderiv ℝ f) z).flip e) z := by
    have h := hH.clm_apply (hasFDerivAt_const e z)
    simpa using h
  have hd : HasDerivAt (fun s : ℝ => fderiv ℝ f (z + s • e) e) (fderiv ℝ (fderiv ℝ f) z e e) 0 :=
    hA.comp_hasDerivAt_of_eq (0 : ℝ) (hline 0) hz0.symm
  rw [hev.deriv_eq]
  exact hd.deriv

theorem contDiffAt_line {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : (J → ℂ) → F}
    {z : J → ℂ} (hf : ContDiffAt ℝ 2 f z) (e : J → ℂ) :
    ContDiffAt ℝ 2 (fun s : ℝ => f (z + s • e)) 0 := by
  have hl : ContDiffAt ℝ 2 (fun s : ℝ => z + s • e) 0 :=
    (contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffAt
  exact ContDiffAt.comp (g := f) (0 : ℝ) (by simpa using hf) hl

theorem sndDeriv_I_I {φ : (J → ℂ) → ℂ} {z : J → ℂ} (hφ : AnalyticAt ℂ φ z) (a : J → ℂ) :
    fderiv ℝ (fderiv ℝ φ) z (Complex.I • a) (Complex.I • a) = - fderiv ℝ (fderiv ℝ φ) z a a := by
  have hR : AnalyticAt ℝ φ z := hφ.restrictScalars
  have hT : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) z) z :=
    (((hR.contDiffAt (n := 2)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hlin : ∀ a b : J → ℂ, fderiv ℝ (fderiv ℝ φ) z a (Complex.I • b) =
      Complex.I • fderiv ℝ (fderiv ℝ φ) z a b := by
    intro a b
    have h1 := hT.clm_apply (hasFDerivAt_const (Complex.I • b) z)
    have h2 := (hT.clm_apply (hasFDerivAt_const b z)).const_smul Complex.I
    have hev : (fun y => fderiv ℝ φ y (Complex.I • b)) =ᶠ[𝓝 z]
        (fun y => Complex.I • fderiv ℝ φ y b) := by
      filter_upwards [hφ.eventually_analyticAt] with y hy
      rw [hy.differentiableAt.fderiv_restrictScalars ℝ]
      simp
    have h3 := (h1.congr_of_eventuallyEq hev.symm).unique h2
    have := congrArg (fun L => L a) h3
    simpa using this
  have hsymm : IsSymmSndFDerivAt ℝ φ z := (hR.contDiffAt (n := ω)).isSymmSndFDerivAt le_top
  calc fderiv ℝ (fderiv ℝ φ) z (Complex.I • a) (Complex.I • a)
      = Complex.I • fderiv ℝ (fderiv ℝ φ) z (Complex.I • a) a := hlin _ _
    _ = Complex.I • fderiv ℝ (fderiv ℝ φ) z a (Complex.I • a) := by rw [hsymm]
    _ = Complex.I • Complex.I • fderiv ℝ (fderiv ℝ φ) z a a := by rw [hlin]
    _ = - fderiv ℝ (fderiv ℝ φ) z a a := by rw [smul_smul, Complex.I_mul_I]; simp

theorem line_key {X : ℝ → ℝ} {A Φ : ℝ → ℂ} (hX : ContDiffAt ℝ 2 X 0) (hA : ContDiffAt ℝ 2 A 0)
    (hΦ : ContDiffAt ℝ 2 Φ 0) (h0 : Φ 0 = 0) (h1 : deriv Φ 0 = 0) :
    deriv (fun t => X t * (‖A t + Φ t‖ ^ 2 - ‖A t‖ ^ 2)) 0 = 0 ∧
      deriv (deriv fun t => X t * (‖A t + Φ t‖ ^ 2 - ‖A t‖ ^ 2)) 0 =
        2 * X 0 * inner ℝ (A 0) (deriv (deriv Φ) 0) := by
  have hg : (fun t => X t * (‖A t + Φ t‖ ^ 2 - ‖A t‖ ^ 2)) =
      fun t => X t * (2 * inner ℝ (A t) (Φ t) + inner ℝ (Φ t) (Φ t)) := by
    funext t
    rw [norm_add_sq_real, real_inner_self_eq_norm_sq]
    ring
  rw [hg]
  obtain ⟨hX1, hX2⟩ := hasDerivAt_of_contDiffAt_two hX
  obtain ⟨hA1, hA2⟩ := hasDerivAt_of_contDiffAt_two hA
  obtain ⟨hΦ1, hΦ2⟩ := hasDerivAt_of_contDiffAt_two hΦ
  have hN2 : ContDiffAt ℝ 2 (fun t => 2 * inner ℝ (A t) (Φ t) + inner ℝ (Φ t) (Φ t)) 0 :=
    (contDiffAt_const.mul (hA.inner ℝ hΦ)).add (hΦ.inner ℝ hΦ)
  have hN0 : (2 * inner ℝ (A 0) (Φ 0) + inner ℝ (Φ 0) (Φ 0) : ℝ) = 0 := by simp [h0]
  have hNd : HasDerivAt (fun t => 2 * inner ℝ (A t) (Φ t) + inner ℝ (Φ t) (Φ t)) 0 0 := by
    have h := ((hA1.self_of_nhds.inner ℝ hΦ1.self_of_nhds).const_mul 2).add
      (hΦ1.self_of_nhds.inner ℝ hΦ1.self_of_nhds)
    exact h.congr_deriv (by simp [h0, h1])
  have hev : deriv (fun t => 2 * inner ℝ (A t) (Φ t) + inner ℝ (Φ t) (Φ t)) =ᶠ[𝓝 0]
      fun t => 2 * (inner ℝ (A t) (deriv Φ t) + inner ℝ (deriv A t) (Φ t)) +
        (inner ℝ (Φ t) (deriv Φ t) + inner ℝ (deriv Φ t) (Φ t)) := by
    filter_upwards [hA1, hΦ1] with t ha hp
    exact (((ha.inner ℝ hp).const_mul 2).add (hp.inner ℝ hp)).deriv
  have hNdd : deriv (deriv fun t => 2 * inner ℝ (A t) (Φ t) + inner ℝ (Φ t) (Φ t)) 0 =
      2 * inner ℝ (A 0) (deriv (deriv Φ) 0) := by
    rw [hev.deriv_eq]
    have h := ((((hA1.self_of_nhds.inner ℝ hΦ2).add (hA2.inner ℝ hΦ1.self_of_nhds)).const_mul 2).add
      ((hΦ1.self_of_nhds.inner ℝ hΦ2).add (hΦ2.inner ℝ hΦ1.self_of_nhds)))
    refine h.deriv.trans ?_
    simp [h0, h1]
  have key := deriv_deriv_mul hX hN2
  beta_reduce at key
  refine ⟨?_, ?_⟩
  · refine (hX1.self_of_nhds.mul hNd).deriv.trans ?_
    simp [h0]
  · rw [key, hNdd, hN0, hNd.deriv]
    ring

theorem along {ξ : (J → ℂ) → ℝ} {a φ : (J → ℂ) → ℂ} {z : J → ℂ} (hξ : ContDiffAt ℝ 2 ξ z)
    (ha : AnalyticAt ℂ a z) (hφ : AnalyticAt ℂ φ z) (hφ0 : φ z = 0)
    (hu : ContDiffAt ℝ 2 (fun x => ξ x * (‖a x + φ x‖ ^ 2 - ‖a x‖ ^ 2)) z) (v : J → ℂ)
    (hv : fderiv ℂ φ z v = 0) :
    fderiv ℝ (fun x => ξ x * (‖a x + φ x‖ ^ 2 - ‖a x‖ ^ 2)) z v = 0 ∧
      fderiv ℝ (fderiv ℝ fun x => ξ x * (‖a x + φ x‖ ^ 2 - ‖a x‖ ^ 2)) z v v =
        2 * ξ z * inner ℝ (a z) (fderiv ℝ (fderiv ℝ φ) z v v) := by
  have haR : ContDiffAt ℝ 2 a z := ha.restrictScalars.contDiffAt
  have hφR : ContDiffAt ℝ 2 φ z := hφ.restrictScalars.contDiffAt
  have hz0 : z + (0 : ℝ) • v = z := by rw [zero_smul, add_zero]
  have h0 : (fun t : ℝ => φ (z + t • v)) 0 = 0 := by simp [hφ0]
  have h1 : deriv (fun t : ℝ => φ (z + t • v)) 0 = 0 := by
    rw [deriv_line (hφR.differentiableAt (by norm_num)) v,
      hφ.differentiableAt.fderiv_restrictScalars ℝ]
    simpa using hv
  obtain ⟨k1, k2⟩ := line_key (X := fun t => ξ (z + t • v)) (A := fun t => a (z + t • v))
    (Φ := fun t => φ (z + t • v)) (contDiffAt_line hξ v) (contDiffAt_line haR v)
    (contDiffAt_line hφR v) h0 h1
  refine ⟨?_, ?_⟩
  · rw [← deriv_line (hu.differentiableAt (by norm_num)) v]
    exact k1
  · rw [← deriv_deriv_line hu v, ← deriv_deriv_line hφR v]
    rw [show ξ z = ξ (z + (0 : ℝ) • v) by rw [hz0], show a z = a (z + (0 : ℝ) • v) by rw [hz0]]
    exact k2

theorem proof : LeviHolPerturb.Statement := by
  intro J _ ξ a φ z w hξ ha hφ hφ0 hdφ
  have haR : ContDiffAt ℝ 2 a z := ha.restrictScalars.contDiffAt
  have hφR : ContDiffAt ℝ 2 φ z := hφ.restrictScalars.contDiffAt
  have hu : ContDiffAt ℝ 2 (fun x => ξ x * (‖a x + φ x‖ ^ 2 - ‖a x‖ ^ 2)) z :=
    hξ.mul (((haR.add hφR).norm_sq ℝ).sub (haR.norm_sq ℝ))
  have hw := along hξ ha hφ hφ0 hu w hdφ
  have hIw := along hξ ha hφ hφ0 hu (Complex.I • w) (by rw [map_smul, hdφ, smul_zero])
  refine ⟨hu, by simp [hφ0], hw.1, hIw.1, ?_⟩
  unfold leviForm
  rw [hw.2, hIw.2, sndDeriv_I_I hφ w, inner_neg_right]
  ring

end LeviHolPerturb

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def RatioFieldDeg.Statement : Prop :=
  ∀ (ι : Type) (E₁ E₂ : Type) [Field E₁] [CharZero E₁] [Field E₂] [CharZero E₂] (u : ι → E₁) (v : ι → E₂)
    (D : ℕ) (e : Fin (D + 1) → ι), coordIdeal ℤ u = coordIdeal ℤ v → projDeg u e = projDeg v e

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def TranscRatioDeg.Statement : Prop :=
  ∀ (ι : Type) (E : Type) [Field E] [CharZero E] (u : ι → E) (D : ℕ) (e : Fin (D + 1) → ι) (w : Fin (D + 1) → E)
    (i₀ : ι) (Φ : Type) [Field Φ] [Algebra Φ E],
    u i₀ ≠ 0 → (∀ k, u (e k) ≠ 0) → (∀ k, w k * u (e 0) = w 0 * u (e k)) →
    Transcendental (Algebra.adjoin ℤ (Set.range u)) (w 0) →
    (algebraMap Φ E).fieldRange = Subfield.closure (Set.range w) →
    Module.finrank Φ (IntermediateField.adjoin Φ (Set.range fun i => u i / u i₀)) = projDeg u e

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

namespace SemiampleNefAlt

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem charOf_prime {W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)} [W.IsPrime]
    (h : ReciprocityTheory.ChartRestriction.G.Geo.charOf W ≠ 0) : (ReciprocityTheory.ChartRestriction.G.Geo.charOf W).Prime := by
  have hI : (W.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)).IsPrime := Ideal.comap_isPrime _ _
  have hg : Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)) ≠ 0 := by
    intro h0
    apply h
    unfold ReciprocityTheory.ChartRestriction.G.Geo.charOf
    rw [h0]
    rfl
  rw [← Submodule.IsPrincipal.span_singleton_generator
    (W.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι))] at hI
  exact Int.prime_iff_natAbs_prime.mp ((Ideal.span_singleton_prime hg).mp hI)


end SemiampleNefAlt


end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def PrimeZariskiDense.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (j : MRing ι),
    P.IsPrime → j ∉ P →
    ∀ g : MvPolynomial (Σ k, ι k) ℂ,
      (∀ z ∈ mcPts P, eval z (map (Int.castRingHom ℂ) j) ≠ 0 → eval z g = 0) →
      ∀ z ∈ mcPts P, eval z g = 0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Cardinal

noncomputable section

theorem exists_ringHom_complex_of_charZero (F : Type) [Field F] [CharZero F] (hF : #F ≤ 𝔠) :
    Nonempty (F →+* ℂ) := by
  let M := MvPolynomial ℂ F
  let E := FractionRing M
  let L := AlgebraicClosure E
  have : CharZero M := charZero_of_injective_algebraMap (R := F) (MvPolynomial.C_injective _ _)
  have : CharZero E := charZero_of_injective_algebraMap (R := M) (IsFractionRing.injective M E)
  have : CharZero L := charZero_of_injective_algebraMap (R := E) (algebraMap E L).injective
  have hM : #M ≤ 𝔠 := by
    refine MvPolynomial.cardinalMk_le_max.trans ?_
    rw [mk_complex]
    exact max_le (max_le hF le_rfl) aleph0_le_continuum
  have hE : #E = #M := Cardinal.mk_fractionRing M
  have hL : #L ≤ 𝔠 :=
    (Algebra.IsAlgebraic.cardinalMk_le_max E L).trans (max_le (hE ▸ hM) aleph0_le_continuum)
  have hinj : Function.Injective (fun c : ℂ => algebraMap E L (algebraMap M E (X c))) :=
    (algebraMap E L).injective.comp ((IsFractionRing.injective M E).comp MvPolynomial.X_injective)
  have hLc : #L = #ℂ :=
    le_antisymm (hL.trans_eq mk_complex.symm) (Cardinal.mk_le_of_injective hinj)
  obtain ⟨σ⟩ := IsAlgClosed.ringEquiv_of_equiv_of_charZero (K := L) (L := ℂ)
    (by rw [hLc, mk_complex]; exact aleph0_lt_continuum) (Cardinal.eq.1 hLc)
  exact ⟨σ.toRingHom.comp ((algebraMap E L).comp ((algebraMap M E).comp C))⟩

theorem exists_mcPts_not_mem_mcPts {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P J : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d) (hJ : ¬ J ≤ P) :
    ∃ z, z ∈ mcPts P ∧ z ∉ mcPts J := by
  obtain ⟨_, ⟨hprime, -, hrel⟩, hhor, -⟩ := hP
  obtain ⟨g, hgJ, hgP⟩ := SetLike.not_le_iff_exists.mp hJ
  have := hprime
  let Q := MRing ι ⧸ P
  let F := FractionRing Q
  have hQ : Function.Injective (algebraMap ℤ Q) := by
    have e : algebraMap ℤ Q = (Ideal.Quotient.mk P).comp C := RingHom.ext_int _ _
    rw [e, injective_iff_map_eq_zero]
    intro n hn
    have hn0 : (C n : MRing ι) ∈ P := Ideal.Quotient.eq_zero_iff_mem.mp hn
    have hn' : n ∈ P.comap (C : ℤ →+* MRing ι) := hn0
    rw [IsHorizontal] at hhor
    rw [hhor] at hn'
    exact (Ideal.mem_bot).mp hn'
  have : CharZero Q := charZero_of_injective_algebraMap hQ
  have : CharZero F := charZero_of_injective_algebraMap (R := Q) (IsFractionRing.injective Q F)
  have hcard : #F ≤ 𝔠 := by
    rw [Cardinal.mk_fractionRing]
    refine (Cardinal.mk_le_of_surjective (Ideal.Quotient.mk_surjective (I := P))).trans ?_
    refine MvPolynomial.cardinalMk_le_max.trans ?_
    exact max_le (max_le (mk_int.le.trans aleph0_le_continuum)
      (Cardinal.mk_le_aleph0.trans aleph0_le_continuum)) aleph0_le_continuum
  obtain ⟨ψ⟩ := exists_ringHom_complex_of_charZero F hcard
  let φ : MRing ι →+* ℂ := (ψ.comp (algebraMap Q F)).comp (Ideal.Quotient.mk P)
  have hker : ∀ f, φ f = 0 ↔ f ∈ P := by
    intro f
    have hi : Function.Injective (ψ.comp (algebraMap Q F)) :=
      ψ.injective.comp (IsFractionRing.injective Q F)
    rw [show φ f = (ψ.comp (algebraMap Q F)) (Ideal.Quotient.mk P f) from rfl,
      map_eq_zero_iff _ hi, Ideal.Quotient.eq_zero_iff_mem]
  let z : (Σ k, ι k) → ℂ := fun p => φ (X p)
  have hev : ∀ f : MRing ι, eval z (map (Int.castRingHom ℂ) f) = φ f := by
    intro f
    have h : (eval z).comp (map (Int.castRingHom ℂ)) = φ := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
      · exact RingHom.congr_fun
          (RingHom.ext_int (((eval z).comp (map (Int.castRingHom ℂ))).comp C) (φ.comp C)) r
      · simp [z]
    exact RingHom.congr_fun h f
  refine ⟨z, ⟨fun k => ?_, fun f hf => ?_⟩, fun hz => ?_⟩
  · obtain ⟨i, hi⟩ := hrel k
    exact ⟨i, fun h => hi ((hker _).mp h)⟩
  · rw [hev]
    exact (hker f).mpr hf
  · exact hgP ((hker g).mp (by rw [← hev]; exact hz.2 g hgJ))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
