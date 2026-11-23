module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle048
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle090
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle103
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.FiniteDimensionalHcSpace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle091
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle092
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle084
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle082
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle093
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle101
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

@[expose] public section

section

noncomputable section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

namespace GlobalTheory.CompanionTheory.TubeFourier.PhiInv

theorem dot_pt_eq (x y t : ℝ × ℝ) :
    dot (pt x y) t = ((rdot x t : ℝ) : ℂ) + Complex.I * ((rdot y t : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [dot, pt, rdot]

theorem integrable_gaussian_prod :
    Integrable (fun y : ℝ × ℝ => Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) := by
  have h1 : Integrable (fun x : ℝ => Real.exp (-1 * x ^ 2)) := integrable_exp_neg_mul_sq one_pos
  have h2 := h1.mul_prod h1
  rw [← Measure.volume_eq_prod] at h2
  refine h2.congr (Eventually.of_forall fun y => ?_)
  simp only
  rw [← Real.exp_add]
  congr 1
  ring

theorem phi_eq_smul {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (G : ℂ × ℂ → X) (x t : ℝ × ℝ) :
    phi G x t = Complex.exp (-((rdot x t : ℝ) : ℂ)) •
      ∫ y : ℝ × ℝ, Complex.exp (-(Complex.I * ((rdot y t : ℝ) : ℂ))) • G (pt x y) := by
  unfold phi
  rw [← integral_smul]
  congr 1
  funext y
  rw [smul_smul, dot_pt_eq, ← Complex.exp_add]
  congr 2
  ring

theorem hat_eq_smul {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (G : ℂ × ℂ → X) (x t : ℝ × ℝ) :
    (∫ y : ℝ × ℝ, Complex.exp (-(Complex.I * ((rdot y t : ℝ) : ℂ))) • G (pt x y)) =
      Complex.exp ((rdot x t : ℝ) : ℂ) • phi G x t := by
  rw [phi_eq_smul, smul_smul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_smul]

theorem inv_phi_eq : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (G : ℂ × ℂ → X)
    (x : ℝ × ℝ), Continuous (fun y => G (pt x y)) →
    (∃ M : ℝ, ∀ y : ℝ × ℝ, ‖G (pt x y)‖ ≤ M * Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) →
    Continuous (phi G x) →
    (∃ ε : ℝ, 0 < ε ∧ ∃ M : ℝ, ∀ t : ℝ × ℝ,
      ‖phi G x t‖ ≤ M * Real.exp (-rdot x t) * Real.exp (-ε * (|t.1| + |t.2|))) →
    ∀ y : ℝ × ℝ, inv (phi G x) (pt x y) = G (pt x y) := by
  intro X _ _ _ G x hc ⟨M, hM⟩ hphic ⟨ε, hε, M', hM'⟩ y
  have hint : Integrable (fun y : ℝ × ℝ => G (pt x y)) :=
    Integrable.mono' (integrable_gaussian_prod.const_mul M) hc.aestronglyMeasurable
      (Eventually.of_forall fun y => hM y)
  have hdx : ∀ t, dot (pt x 0) t = ((rdot x t : ℝ) : ℂ) := by
    intro t; rw [dot_pt_eq]; simp [rdot]
  have hl : ((pt x 0).1.re, (pt x 0).2.re) = x := by simp [pt]
  have hint2 : Integrable (fun t : ℝ × ℝ =>
      ∫ y : ℝ × ℝ, Complex.exp (-(Complex.I * ((rdot y t : ℝ) : ℂ))) • G (pt x y)) := by
    have h0 := (GlobalTheory.T.exponential_fourier_integral_bound X (phi G x) (pt x 0) ε M' hε hphic (by rw [hl]; exact hM')).1
    refine h0.congr (Eventually.of_forall fun t => ?_)
    show Complex.exp (dot (pt x 0) t) • phi G x t =
      ∫ y : ℝ × ℝ, Complex.exp (-(Complex.I * ((rdot y t : ℝ) : ℂ))) • G (pt x y)
    rw [hdx, hat_eq_smul]
  have key := GlobalTheory.T.fourier_inversion_real_plane X (fun y => G (pt x y)) hc hint hint2 y
  rw [key]
  unfold inv
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  beta_reduce
  rw [hat_eq_smul, smul_smul, dot_pt_eq, ← Complex.exp_add]
  congr 2
  ring

end GlobalTheory.CompanionTheory.TubeFourier.PhiInv
end
end

section

noncomputable section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

namespace GlobalTheory.CompanionTheory.TubeFourier

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem shiftFst_bound {Ω : Set (ℝ × ℝ)} {G : ℂ × ℂ → X} (hG : GaussTube G Ω) {a b c : ℝ}
    (hs : ∀ s ∈ Set.Icc a b, (s, c) ∈ Ω) (t : ℝ × ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ l : ℂ × ℂ, l.1.re ∈ Set.Icc a b → l.2.re = c →
      ‖Complex.exp (-dot l t) • G l‖ ≤ M * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2)) := by
  have hC : IsCompact ((fun s : ℝ => (s, c)) '' Set.Icc a b) :=
    isCompact_Icc.image (Continuous.prodMk continuous_id continuous_const)
  have hCΩ : (fun s : ℝ => (s, c)) '' Set.Icc a b ⊆ Ω := by
    rintro _ ⟨s, hs', rfl⟩
    exact hs s hs'
  obtain ⟨M₀, hM₀⟩ := hG.3 _ hCΩ hC
  refine ⟨Real.exp ((|a| + |b|) * |t.1| + |c| * |t.2|) * |M₀|, by positivity, ?_⟩
  intro l hl hlc
  have hmem : l ∈ PositivityTheory.RgEis.tube ((fun s : ℝ => (s, c)) '' Set.Icc a b) := by
    show (l.1.re, l.2.re) ∈ (fun s : ℝ => (s, c)) '' Set.Icc a b
    exact ⟨l.1.re, hl, Prod.ext rfl hlc.symm⟩
  have hGl := hM₀ l hmem
  have hre : (-GlobalTheory.CompanionTheory.TubeFourier.dot l t).re = -(l.1.re * t.1 + l.2.re * t.2) := by
    simp [GlobalTheory.CompanionTheory.TubeFourier.dot]
  have hx : |l.1.re| ≤ |a| + |b| :=
    abs_le.2 ⟨by linarith [neg_abs_le a, abs_nonneg b, hl.1], by linarith [le_abs_self b, abs_nonneg a, hl.2]⟩
  have hexp : ‖Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot l t)‖ ≤
      Real.exp ((|a| + |b|) * |t.1| + |c| * |t.2|) := by
    rw [Complex.norm_exp, hre, hlc]
    apply Real.exp_le_exp.2
    have e1 : -(l.1.re * t.1) ≤ (|a| + |b|) * |t.1| := by
      calc -(l.1.re * t.1) ≤ |l.1.re * t.1| := neg_le_abs _
        _ = |l.1.re| * |t.1| := abs_mul _ _
        _ ≤ (|a| + |b|) * |t.1| := mul_le_mul_of_nonneg_right hx (abs_nonneg _)
    have e2 : -(c * t.2) ≤ |c| * |t.2| := by
      rw [← abs_mul]
      exact neg_le_abs _
    linarith
  rw [norm_smul]
  calc ‖Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot l t)‖ * ‖G l‖
      ≤ Real.exp ((|a| + |b|) * |t.1| + |c| * |t.2|) *
          (|M₀| * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2))) :=
        mul_le_mul hexp (hGl.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le))
          (norm_nonneg _) (Real.exp_pos _).le
    _ = Real.exp ((|a| + |b|) * |t.1| + |c| * |t.2|) * |M₀| *
          Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2)) := by ring

theorem integrable_exp_neg_sq_prod :
    Integrable (fun y : ℝ × ℝ => Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2)) := by
  have h := (integrable_exp_neg_mul_sq one_pos).mul_prod (integrable_exp_neg_mul_sq one_pos)
  rw [← MeasureTheory.Measure.volume_eq_prod] at h
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [neg_mul, one_mul]

theorem shiftFst_integrable {Ω : Set (ℝ × ℝ)} {G : ℂ × ℂ → X} (hG : GaussTube G Ω) {a b c : ℝ}
    (hs : ∀ s ∈ Set.Icc a b, (s, c) ∈ Ω) (t : ℝ × ℝ) {s : ℝ} (hsm : s ∈ Set.Icc a b) :
    Integrable (fun y : ℝ × ℝ => Complex.exp (-dot (pt (s, c) y) t) • G (pt (s, c) y)) := by
  obtain ⟨M, -, hM⟩ := GlobalTheory.CompanionTheory.TubeFourier.shiftFst_bound hG hs t
  have htp : Continuous (GlobalTheory.CompanionTheory.TubeFourier.pt (s, c)) := by
    have h : GlobalTheory.CompanionTheory.TubeFourier.pt (s, c) = fun y : ℝ × ℝ =>
        ((s : ℂ) + (y.1 : ℂ) * Complex.I, (c : ℂ) + (y.2 : ℂ) * Complex.I) := by
      funext y
      simp only [GlobalTheory.CompanionTheory.TubeFourier.pt, Complex.mk_eq_add_mul_I]
    rw [h]
    fun_prop
  have hmem : ∀ y, GlobalTheory.CompanionTheory.TubeFourier.pt (s, c) y ∈ PositivityTheory.RgEis.tube Ω := fun _ => hs s hsm
  have hGc : Continuous (fun y => G (GlobalTheory.CompanionTheory.TubeFourier.pt (s, c) y)) := hG.2.comp_continuous htp hmem
  have hpair : Continuous (fun l : ℂ × ℂ => GlobalTheory.CompanionTheory.TubeFourier.dot l t) := by
    simp only [GlobalTheory.CompanionTheory.TubeFourier.dot]
    fun_prop
  have hE : Continuous (fun y => Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot (GlobalTheory.CompanionTheory.TubeFourier.pt (s, c) y) t)) :=
    (hpair.comp htp).neg.cexp
  refine MeasureTheory.Integrable.mono'
    (GlobalTheory.CompanionTheory.TubeFourier.integrable_exp_neg_sq_prod.const_mul M)
    (hE.smul hGc).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  refine (hM (GlobalTheory.CompanionTheory.TubeFourier.pt (s, c) y) hsm rfl).trans (le_of_eq ?_)
  show M * Real.exp (-(y.1 ^ 2 + y.2 ^ 2)) = M * (Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2))
  rw [← Real.exp_add]
  congr 2
  ring

theorem phi_eq_iterated {Ω : Set (ℝ × ℝ)} {G : ℂ × ℂ → X} (hG : GaussTube G Ω) {a b c : ℝ}
    (hs : ∀ s ∈ Set.Icc a b, (s, c) ∈ Ω) (t : ℝ × ℝ) {s : ℝ} (hsm : s ∈ Set.Icc a b) :
    phi G (s, c) t = ∫ y₂ : ℝ, ∫ y₁ : ℝ,
      Complex.exp (-dot (pt (s, c) (y₁, y₂)) t) • G (pt (s, c) (y₁, y₂)) := by
  have h := shiftFst_integrable hG hs t hsm
  unfold phi
  rw [Measure.volume_eq_prod] at h ⊢
  exact integral_prod_symm _ h

end GlobalTheory.CompanionTheory.TubeFourier

theorem GlobalTheory.CompanionTheory.TubeFourier.phi_shift_fst :
    ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (Ω : Set (ℝ × ℝ)) (G : ℂ × ℂ → X),
      GaussTube G Ω → ∀ a b c : ℝ, a ≤ b → (∀ s ∈ Set.Icc a b, (s, c) ∈ Ω) →
        ∀ t : ℝ × ℝ, phi G (a, c) t = phi G (b, c) t := by
  intro X _ _ _ Ω G hG a b c hab hs t
  rw [GlobalTheory.CompanionTheory.TubeFourier.phi_eq_iterated hG hs t (Set.left_mem_Icc.2 hab),
    GlobalTheory.CompanionTheory.TubeFourier.phi_eq_iterated hG hs t (Set.right_mem_Icc.2 hab)]
  obtain ⟨M, hM0, hM⟩ := GlobalTheory.CompanionTheory.TubeFourier.shiftFst_bound hG hs t
  refine integral_congr_ae (ae_of_all _ fun y₂ => ?_)
  have hline : DifferentiableOn ℂ (fun z : ℂ => G (z, ⟨c, y₂⟩)) {z : ℂ | z.re ∈ Set.Icc a b} := by
    have h1 := hG.1 ((0 : ℂ), (⟨c, y₂⟩ : ℂ)) ((1 : ℂ), (0 : ℂ))
    have heq : ∀ τ : ℂ, ((0 : ℂ), (⟨c, y₂⟩ : ℂ)) + τ • ((1 : ℂ), (0 : ℂ)) = (τ, ⟨c, y₂⟩) :=
      fun τ => Prod.ext (by simp) (by simp)
    simp only [heq] at h1
    refine h1.mono fun z hz => ?_
    exact hs z.re hz
  have hpair : Differentiable ℂ (fun z : ℂ => Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot (z, ⟨c, y₂⟩) t)) := by
    simp only [GlobalTheory.CompanionTheory.TubeFourier.dot]
    fun_prop
  have hdiff : DifferentiableOn ℂ
      (fun z : ℂ => Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot (z, ⟨c, y₂⟩) t) • G (z, ⟨c, y₂⟩))
      {z : ℂ | z.re ∈ Set.Icc a b} :=
    hpair.differentiableOn.smul hline
  have hbound : ∀ z : ℂ, z.re ∈ Set.Icc a b →
      ‖Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot (z, ⟨c, y₂⟩) t) • G (z, ⟨c, y₂⟩)‖ ≤
        M * Real.exp (-z.im ^ 2) := by
    intro z hz
    refine (hM (z, ⟨c, y₂⟩) hz rfl).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hM0)
    show -(z.im ^ 2 + y₂ ^ 2) ≤ -z.im ^ 2
    linarith [sq_nonneg y₂]
  exact GlobalTheory.T.contour_shift_gaussian_decay X
    (fun z : ℂ => Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot (z, ⟨c, y₂⟩) t) • G (z, ⟨c, y₂⟩))
    a b M hab hdiff hbound
end
end

section

noncomputable section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

namespace GlobalTheory.CompanionTheory.TubeFourier

theorem continuous_mk_im_shiftSnd (x : ℝ) : Continuous fun y : ℝ => (⟨x, y⟩ : ℂ) := by
  have h : (fun y : ℝ => (⟨x, y⟩ : ℂ)) = fun y : ℝ => (x : ℂ) + (y : ℂ) * Complex.I := by
    ext y
    apply Complex.ext <;> simp
  rw [h]
  fun_prop

theorem continuous_pt_shiftSnd (x : ℝ × ℝ) : Continuous fun y : ℝ × ℝ => pt x y := by
  unfold pt
  exact ((continuous_mk_im_shiftSnd x.1).comp continuous_fst).prodMk ((continuous_mk_im_shiftSnd x.2).comp continuous_snd)

theorem integrable_gauss_prod_shiftSnd (K : ℝ) :
    Integrable fun y : ℝ × ℝ => K * Real.exp (-(y.1 ^ 2 + y.2 ^ 2)) := by
  have h1 : Integrable fun x : ℝ => Real.exp (-1 * x ^ 2) := integrable_exp_neg_mul_sq one_pos
  have h2 := (h1.mul_prod h1).const_mul K
  rw [Measure.volume_eq_prod]
  refine h2.congr (Eventually.of_forall fun y => ?_)
  simp only
  rw [← Real.exp_add]
  congr 2
  ring

theorem phi_shift_snd (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (Ω : Set (ℝ × ℝ))
    (G : ℂ × ℂ → X) (hG : GaussTube G Ω) (a b c : ℝ) (hab : a ≤ b) (hs : ∀ s ∈ Set.Icc a b, (c, s) ∈ Ω)
    (t : ℝ × ℝ) : phi G (c, a) t = phi G (c, b) t := by
  set C : Set (ℝ × ℝ) := (fun s : ℝ => (c, s)) '' Set.Icc a b with hC
  have hCc : IsCompact C := isCompact_Icc.image (by fun_prop)
  have hCΩ : C ⊆ Ω := by
    rintro _ ⟨s, hs', rfl⟩
    exact hs s hs'
  obtain ⟨M, hM⟩ := hG.decay C hCΩ hCc
  obtain ⟨B, hB⟩ := (hCc.image (f := fun x : ℝ × ℝ => Real.exp (-(x.1 * t.1 + x.2 * t.2)))
    (by fun_prop)).bddAbove
  let H : ℂ × ℂ → X := fun l => Complex.exp (-dot l t) • G l
  have hexp : Continuous fun l : ℂ × ℂ => Complex.exp (-dot l t) := by
    unfold dot
    fun_prop
  have hbound : ∀ l ∈ tube C, ‖H l‖ ≤ (|B| * |M|) * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2)) := by
    intro l hl
    have h1 : ‖Complex.exp (-dot l t)‖ ≤ |B| := by
      rw [Complex.norm_exp]
      have h : (-dot l t).re = -(l.1.re * t.1 + l.2.re * t.2) := by simp [dot]
      rw [h]
      exact (hB ⟨(l.1.re, l.2.re), hl, rfl⟩).trans (le_abs_self B)
    have h2 : ‖G l‖ ≤ |M| * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2)) :=
      (hM l hl).trans (mul_le_mul_of_nonneg_right (le_abs_self M) (Real.exp_pos _).le)
    calc ‖H l‖ = ‖Complex.exp (-dot l t)‖ * ‖G l‖ := norm_smul _ _
      _ ≤ |B| * (|M| * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2))) := by gcongr
      _ = _ := by ring
  have hcont : ContinuousOn H (tube Ω) := hexp.continuousOn.smul hG.cont
  have hmem : ∀ s ∈ Set.Icc a b, ∀ y : ℝ × ℝ, pt (c, s) y ∈ tube C := fun s hs' y => ⟨s, hs', rfl⟩
  have hint : ∀ s ∈ Set.Icc a b, Integrable fun y : ℝ × ℝ => H (pt (c, s) y) := by
    intro s hs'
    have hc : Continuous fun y : ℝ × ℝ => H (pt (c, s) y) :=
      hcont.comp_continuous (continuous_pt_shiftSnd _) fun y => hs s hs'
    refine (integrable_gauss_prod_shiftSnd (|B| * |M|)).mono' hc.aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    exact hbound _ (hmem s hs' y)
  have hphi : ∀ s ∈ Set.Icc a b, phi G (c, s) t = ∫ y₁ : ℝ, ∫ y₂ : ℝ, H (⟨c, y₁⟩, ⟨s, y₂⟩) := by
    intro s hs'
    have h := hint s hs'
    rw [Measure.volume_eq_prod] at h
    have h' := integral_prod _ h
    rw [← Measure.volume_eq_prod] at h'
    exact h'
  rw [hphi a (Set.left_mem_Icc.2 hab), hphi b (Set.right_mem_Icc.2 hab)]
  refine integral_congr_ae (Eventually.of_forall fun y₁ => ?_)
  simp only
  refine GlobalTheory.T.contour_shift_gaussian_decay X (fun z => H (⟨c, y₁⟩, z)) a b (|B| * |M|) hab ?_ ?_
  · let p : ℂ × ℂ := (⟨c, y₁⟩, 0)
    let v : ℂ × ℂ := (0, 1)
    have e : ∀ τ : ℂ, p + τ • v = (⟨c, y₁⟩, τ) := by
      intro τ
      simp [p, v]
    have h1 : DifferentiableOn ℂ (fun τ : ℂ => G (⟨c, y₁⟩, τ)) {z : ℂ | z.re ∈ Set.Icc a b} := by
      have h := hG.hol p v
      simp only [e] at h
      exact h.mono fun z hz => hs _ hz
    have h2 : Differentiable ℂ fun τ : ℂ => Complex.exp (-dot ((⟨c, y₁⟩, τ) : ℂ × ℂ) t) := by
      unfold dot
      fun_prop
    exact h2.differentiableOn.smul h1
  · intro z hz
    have h := hbound (⟨c, y₁⟩, z) ⟨z.re, hz, rfl⟩
    refine h.trans ?_
    have hK : 0 ≤ |B| * |M| := by positivity
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hK
    have : 0 ≤ y₁ ^ 2 := sq_nonneg _
    simp only
    linarith

end GlobalTheory.CompanionTheory.TubeFourier
end
end

section

open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

theorem _root_.GlobalTheory.T.pattern_set_card_column_step : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ), j < d →
    (patSet (K := K) (colGe d j)).ncard =
      Fintype.card K ^ j * (patSet (K := K) (colGe d (j + 1))).ncard := by
  intro K _ _ _ d j hj
  classical
  have card_colGe (k : ℕ) :
      (patSet (K := K) (colGe d k)).ncard =
        Fintype.card K ^ Nat.card {p : Fin d × Fin d // colGe d k p.1 p.2} := by
    let A (f : {p : Fin d × Fin d // colGe d k p.1 p.2} → K) : Matrix (Fin d) (Fin d) K :=
      fun i l => if i = l then 1 else if h : colGe d k i l then f ⟨(i, l), h⟩ else 0
    have hunit (f) : IsUnit (A f).det := by
      have htri : (A f).IsUpperTriangular := by
        intro i l h
        change l < i at h
        have hnot : ¬ colGe d k i l := fun hcol => (not_lt_of_gt h) hcol.1
        simp [A, ne_of_gt h, hnot]
      rw [Matrix.det_of_isUpperTriangular htri]
      simp [A]
    let e : patSet (K := K) (colGe d k) ≃ ({p : Fin d × Fin d // colGe d k p.1 p.2} → K) :=
      { toFun := fun u p => (u.val : Matrix (Fin d) (Fin d) K) p.1.1 p.1.2
        invFun := fun f => ⟨Matrix.nonsingInvUnit (A f) (hunit f), by
          intro i l
          change (i = l → A f i l = 1) ∧ (i ≠ l → ¬ colGe d k i l → A f i l = 0)
          exact ⟨fun h => by simp [A, h], fun h hcol => by simp [A, h, hcol]⟩⟩
        left_inv := fun u => by
          apply Subtype.ext
          apply Units.ext
          ext i l
          change A (fun p => (u.val : Matrix (Fin d) (Fin d) K) p.1.1 p.1.2) i l =
            (u.val : Matrix (Fin d) (Fin d) K) i l
          have hu := u.property i l
          by_cases hil : i = l
          · simpa only [A, ite_eq_left hil] using (hu.1 hil).symm
          · by_cases hcol : colGe d k i l
            · simp [A, hil, hcol]
            · simp [A, hil, hcol, hu.2 hil hcol]
        right_inv := fun f => by
          funext p
          change A f p.1.1 p.1.2 = f p
          have hil : p.1.1 ≠ p.1.2 := ne_of_lt p.2.1
          simp [A, hil, p.2] }
    rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card (α := K)]
  rw [card_colGe j, card_colGe (j + 1), natCard_colGe d j hj, pow_add]
end

section

open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

theorem _root_.GlobalTheory.T.whittaker_vanishes_of_radical_sums : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (ψ₀ : AddChar K ℂ) (χ : GL (Fin d) K → ℂ),
    (∀ u : GL (Fin d) K, (open Classical in ∑ v : GL (Fin d) K,
      if v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j) then χ (u * v) else 0) = 0) →
    wh (colGe d j) (colGeR K d j 0) ψ₀ χ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.ColStep.Avg.wh_zero_row' | exact GlobalTheory.CompanionTheory.TyFin.ColStep.Avg.wh_zero_row' | (intros; apply GlobalTheory.CompanionTheory.TyFin.ColStep.Avg.wh_zero_row' <;> assumption)
end

section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix


theorem _root_.GlobalTheory.T.delta_eq_lattice_index : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (c : Matrix (Fin m) (Fin m) K), delta c ≠ 0 ∧ delta c = (intVec K m).toAddSubgroup.relIndex (lam c).toAddSubgroup := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DeltaIndex.delta_index | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DeltaIndex.delta_index | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DeltaIndex.delta_index <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

namespace GlobalTheory.CompanionTheory.Equi

private theorem forall_locMem_iff_exists_mem_ideal {F : Type} [Field F] [NumberField F] (I : Ideal (𝓞 F))
    (z : F) :
    (∀ v : HeightOneSpectrum (𝓞 F), GlobalTheory.CompanionTheory.Equi.LocMem I v z) ↔ ∃ y ∈ I, (y : F) = z := by
  constructor
  · intro h
    let J : Ideal (𝓞 F) :=
      { carrier := {s | ∃ y ∈ I, (s : F) * z = y}
        add_mem' := by
          rintro a b ⟨y₁, hy₁, h₁⟩ ⟨y₂, hy₂, h₂⟩
          exact ⟨y₁ + y₂, I.add_mem hy₁ hy₂, by push_cast; rw [add_mul, h₁, h₂]⟩
        zero_mem' := ⟨0, I.zero_mem, by simp⟩
        smul_mem' := by
          rintro c a ⟨y, hy, h₁⟩
          exact ⟨c * y, I.mul_mem_left c hy, by rw [smul_eq_mul]; push_cast; rw [mul_assoc, h₁]⟩ }
    have hJ : J = ⊤ := by
      by_contra hne
      obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hne
      have hM0 : M ≠ ⊥ :=
        Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField F)
      have hv := h ⟨M, hM.isPrime, hM0⟩
      unfold GlobalTheory.CompanionTheory.Equi.LocMem at hv
      obtain ⟨s, hs, y, hy, hsy⟩ := hv
      exact hs (hJM ⟨y, hy, hsy⟩)
    have h1 : (1 : 𝓞 F) ∈ J := hJ ▸ Submodule.mem_top
    obtain ⟨y, hy, hy1⟩ := h1
    exact ⟨y, hy, by simpa using hy1.symm⟩
  · rintro ⟨y, hy, rfl⟩ v
    unfold GlobalTheory.CompanionTheory.Equi.LocMem
    exact ⟨1, fun h1 => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1), y, hy, by simp⟩

theorem cosetOff_empty_eq_latCoset (F : Type) [Field F] [NumberField F] (ι : Type)
    (I : Ideal (𝓞 F)) (x0 : ι → F) :
    cosetOff (∅ : Finset (HeightOneSpectrum (𝓞 F))) I x0 = latCoset I x0 := by
  ext x
  simp only [GlobalTheory.CompanionTheory.Equi.cosetOff, GlobalTheory.CompanionTheory.Equi.latCoset, Set.mem_setOf_eq]
  constructor
  · intro h i
    exact (forall_locMem_iff_exists_mem_ideal I (x i - x0 i)).mp fun v => h v (by simp) i
  · intro h v _ i
    exact (forall_locMem_iff_exists_mem_ideal I (x i - x0 i)).mpr (h i) v

end GlobalTheory.CompanionTheory.Equi
end
