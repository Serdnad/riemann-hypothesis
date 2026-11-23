module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle032
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle004
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle026
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle036
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormRankZeroApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LowerParabolicCoordinates
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle048
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle062
import Aesop.Main
public import Formalism.FormalDegreeBessel.FinalG
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointLeibnizExpansion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

noncomputable section

open Matrix MeasureTheory
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEXMT

open Formalism.FourierDecayAlt

variable {n : ℕ}

theorem upper_utc {M : Matrix (Fin n) (Fin n) ℂ} (hM : M ∈ C2.UTset n) : G.upper (StabilizerDisintegration.utc M) = M := by
  ext i j
  simp only [G.upper, G.strictUpper, StabilizerDisintegration.utc, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · rw [dite_eq_left h, if_neg (ne_of_lt h), zero_add]
  · rw [dite_eq_right (lt_irrefl _), if_pos rfl, hM.2, add_zero]
  · rw [dite_eq_right (not_lt.2 h.le), if_neg (ne_of_gt h), hM.1 i j h, add_zero]

theorem upper_ut (v : G.UT n → ℂ) : G.upper v ∈ C2.UTset n := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · simp [G.upper, G.strictUpper, not_lt.2 h.le, ne_of_gt h]
  · simp [G.upper, G.strictUpper]

section gam

variable {r : ℕ} {X : Type}

def Gam (p : ((Fin r → Fin r → ℂ) × X) × (G.UT r → ℂ)) : (Fin r → Fin r → ℂ) × X :=
  (Matrix.of.symm (Matrix.of p.1.1 * Wm (Matrix.of p.1.1) * G.upper p.2), p.1.2)

theorem Gam_det (p : ((Fin r → Fin r → ℂ) × X) × (G.UT r → ℂ)) :
    (Matrix.of (Gam p).1).det = (Matrix.of p.1.1).det := by
  simp only [Gam, Equiv.apply_symm_apply]
  rw [Matrix.det_mul, Matrix.det_mul, C2x2.ut_det (Wm_ut _), C2x2.ut_det (upper_ut p.2), mul_one, mul_one]

theorem Gam_eq (q : (Fin r → Fin r → ℂ) × X) (u : Matrix (Fin r) (Fin r) ℂ) (hdet : (Matrix.of q.1).det ≠ 0)
    (hu : u ∈ C2.UTset r) : Gam ((Matrix.of.symm (Matrix.of q.1 * u), q.2), StabilizerDisintegration.utc (Sm (Matrix.of q.1))) = q := by
  simp only [Gam, Equiv.apply_symm_apply]
  rw [Wm_mul hdet hu, upper_utc (Sm_ut _), Matrix.mul_assoc (Matrix.of q.1) u,
    Matrix.mul_nonsing_inv_cancel_left _ _ (C2x2.ut_unit hu), Matrix.mul_assoc, Wm_mul_Sm, Matrix.mul_one]
  rfl

theorem Gam_cont [TopologicalSpace X] (S : Set (((Fin r → Fin r → ℂ) × X) × (G.UT r → ℂ)))
    (hS : ∀ p ∈ S, (Matrix.of p.1.1).det ≠ 0) : ContinuousOn Gam S := by
  have hW : ∀ a b : Fin r, ContinuousOn (fun p : ((Fin r → Fin r → ℂ) × X) × (G.UT r → ℂ) => Wm (Matrix.of p.1.1) a b) S :=
    fun a b => (cd_Wm a b).continuousOn.comp (continuous_fst.comp continuous_fst).continuousOn fun p hp => hS p hp
  refine ContinuousOn.prodMk (continuousOn_pi.2 fun a => continuousOn_pi.2 fun b => ?_)
    (continuous_snd.comp continuous_fst).continuousOn
  have e : ∀ p : ((Fin r → Fin r → ℂ) × X) × (G.UT r → ℂ),
      (Gam p).1 a b = ∑ c : Fin r, (∑ d : Fin r, p.1.1 a d * Wm (Matrix.of p.1.1) d c) * G.upper p.2 c b := by
    intro p
    simp only [Gam]
    rfl
  have key : ContinuousOn (fun p : ((Fin r → Fin r → ℂ) × X) × (G.UT r → ℂ) =>
      ∑ c : Fin r, (∑ d : Fin r, p.1.1 a d * Wm (Matrix.of p.1.1) d c) * G.upper p.2 c b) S := by
    refine continuousOn_finsetSum _ fun c _ => ContinuousOn.mul (continuousOn_finsetSum _ fun d _ => ?_) ?_
    · exact (((continuous_apply_apply a d).comp (continuous_fst.comp continuous_fst)).continuousOn).mul (hW d c)
    · exact ((continuous_apply_apply c b).comp (Formalism.FourierDecayAlt.P.Dx2.SL.cont_upper.comp continuous_snd)).continuousOn
  exact key.congr fun p _ => e p

end gam

theorem top_truncation_construction : MkTopCut := by
  intro r
  let φ : ContDiffBump (0 : G.UT r → ℂ) := ⟨1, 2, one_pos, one_lt_two⟩
  set β₀ : (G.UT r → ℂ) → ℝ := φ.normed volume with hβ₀
  have hcont : Continuous β₀ := φ.continuous_normed
  refine ⟨fun Z => β₀ (StabilizerDisintegration.utc (Sm (Matrix.of Z))), ?_, ?_, ?_⟩
  · have hS : ContDiffOn ℝ ∞ (fun Z : Fin r → Fin r → ℂ => StabilizerDisintegration.utc (Sm (Matrix.of Z)))
        {Z | (Matrix.of Z).det ≠ 0} :=
      contDiffOn_pi.2 fun q => cd_Sm q.1.1 q.1.2
    exact (φ.contDiff_normed (n := ⊤)).comp_contDiffOn hS
  · intro Z hZ
    have hmp := Formalism.FourierDecayAlt.P.StabilizerDisintegration.HC.mp_UTleft (Sm_ut (Matrix.of Z))
    have hfun : (fun v : G.UT r → ℂ => β₀ (StabilizerDisintegration.utc (Sm (Matrix.of (Matrix.of.symm (Matrix.of Z * G.upper v)))))) =
        fun v => β₀ (StabilizerDisintegration.utc (Sm (Matrix.of Z) * G.upper v)) := by
      funext v
      simp only [Equiv.apply_symm_apply]
      rw [Sm_mul hZ (upper_ut v)]
    show Integrable (fun v : G.UT r → ℂ => β₀ (StabilizerDisintegration.utc (Sm (Matrix.of (Matrix.of.symm (Matrix.of Z * G.upper v)))))) ∧
      ∫ v : G.UT r → ℂ, β₀ (StabilizerDisintegration.utc (Sm (Matrix.of (Matrix.of.symm (Matrix.of Z * G.upper v))))) = 1
    rw [hfun]
    constructor
    · have hi := (integrable_map_measure hcont.aestronglyMeasurable hmp.measurable.aemeasurable).1
        (by rw [hmp.map_eq]; exact φ.integrable_normed)
      exact hi
    · rw [← integral_map hmp.measurable.aemeasurable hcont.aestronglyMeasurable, hmp.map_eq]
      exact φ.integral_normed
  · intro X _ K hK hKdet
    have hC₀ : IsCompact (tsupport β₀) := φ.hasCompactSupport_normed
    refine ⟨Gam '' (K ×ˢ tsupport β₀), (hK.prod hC₀).image_of_continuousOn (Gam_cont _ fun p hp => hKdet _ hp.1), ?_, ?_⟩
    · rintro q ⟨⟨q', c⟩, ⟨hq', -⟩, rfl⟩
      exact ⟨by rw [Gam_det]; exact hKdet q' hq', q', hq', rfl⟩
    · rintro q hdet hβ ⟨u, hu, hK'⟩
      have huT : u ∈ C2.UTset r := ⟨fun i j h => hu.1 h, hu.2⟩
      exact ⟨((Matrix.of.symm (Matrix.of q.1 * u), q.2), StabilizerDisintegration.utc (Sm (Matrix.of q.1))),
        ⟨hK', subset_tsupport _ hβ⟩, Gam_eq q u hdet huT⟩

end Formalism.FourierDecayAlt.P.CutEXMT
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

open Formalism.QuantumDeterminants.WeylGroupFacts

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

section aux

variable {k r : ℕ}

def pOf (a b c d : B.Mat k r) : B.SS k r :=
  ((Matrix.of.symm a, Matrix.of.symm b), (Matrix.of.symm c, Matrix.of.symm d))

theorem level_zero_iff (g : B.Mat k r) : g ∈ Q.Glev k r 0 ↔ g ∈ B.GV k r := by
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, fun a ha => absurd ha (Nat.not_lt_zero _)⟩

theorem mat_inv_one : (1 : B.Mat k r)⁻¹ = 1 := by
  simp

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem rho_pOf (D : B.RealPlaceData k r Wp Wq) (a b c d : B.Mat k r) (F : B.Mat k r → (Wq →L[ℂ] Wp)) :
    B.rho D (pOf a b c d) F = fun x => (D.π a).comp ((F (a⁻¹ * b⁻¹ * x * d * c)).comp (D.π' c⁻¹)) := by
  funext x
  simp only [B.rho, B.sgs, pOf, Equiv.apply_symm_apply]

end aux

theorem equivariant_operators_holds : EquivOps := by
  intro hE k r Wp Wq _ _ _ _ _ D O P hDom hloc hsmul hsm hcomm J hJ
  obtain ⟨hS, hL, hR, hU⟩ := hJ
  have hext : ∀ g₀ ∈ B.GV k r, g₀ ∈ O → ∃ (f : B.Mat k r → (Wq →L[ℂ] Wp)) (U : Set (B.Mat k r)),
      B.CkOn ⊤ (B.GV k r) f ∧ HasCompactSupport f ∧ tsupport f ⊆ O ∧ IsOpen U ∧ g₀ ∈ U ∧
        ∀ x ∈ U, x ∈ B.GV k r → f x = J x :=
    fun g₀ hg hO => hE k r (Wq →L[ℂ] Wp) O J hDom.1 hS g₀ hg hO
  have one_N : (1 : B.Mat k r) ∈ Q.Nlev k r 0 := ⟨mem_n_one, (level_zero_iff _).2 uh_one⟩
  have one_S : ∀ z, (1 : B.Mat k r) ∈ Q.Slev k r z 0 :=
    fun z => ⟨1, Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r z, 1, one_N, by simp⟩
  have hπ1 : D.π 1 = 1 := D.π_rep.1
  have hπ'1 : D.π' 1 = 1 := D.π'_rep.1
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro g₀ hg₀
    have hgG := (level_zero_iff g₀).1 hg₀.1
    obtain ⟨f, U, hf, _, hfO, hUo, hgU, hfJ⟩ := hext g₀ hgG hg₀.2
    obtain ⟨U', F, hU', hgU', hF, hFe⟩ := hsm f hf hfO g₀ hg₀
    refine ⟨U ∩ U', F, hUo.inter hU', ⟨hgU, hgU'⟩, hF.mono Set.inter_subset_right, ?_⟩
    intro x hx hxG
    rw [← hFe x hx.2 hxG]
    exact hloc U J f hUo (fun y hy hyG => (hfJ y hy hyG).symm) x hx.1 ((level_zero_iff x).1 hxG)
  ·
    intro g hg n hn
    have hgG := (level_zero_iff g).1 hg.1
    have hnN : n ∈ Formalism.QuantumDeterminants.Nset k r := hn.1
    have hnG : n ∈ B.GV k r := hnN.1
    have hng : n * g ∈ O := by
      have := hDom.2 g hg n ⟨1, Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r D.z, n, hn, by simp⟩ 1 (one_S D.z')
      simpa using this
    have hngG : n * g ∈ B.GV k r := uh_mul hnG hgG
    obtain ⟨f1, U1, hf1, hf1c, hf1O, hU1, hngU1, hf1J⟩ := hext (n * g) hngG hng
    have hp : D.inSS (pOf 1 n⁻¹ 1 1) := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [pOf, Equiv.apply_symm_apply]
      · exact Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r D.z
      · exact mem_n_inv hnN
      · exact Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r D.z'
      · exact mem_n_one
    have hrho : ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.rho D (pOf 1 n⁻¹ 1 1) F = fun x => F (n * x) := by
      intro F
      rw [rho_pOf]
      funext x
      rw [Matrix.nonsing_inv_nonsing_inv n (isUnit_of_uh hnG), mat_inv_one, hπ1, hπ'1]
      ext v
      simp
    have hc := hcomm f1 hf1 hf1c hf1O _ hp g hg.2 hgG
    rw [hrho, hrho] at hc
    beta_reduce at hc
    have e1 : P f1 (n * g) = P J (n * g) := hloc U1 f1 J hU1 hf1J (n * g) hngU1 hngG
    have hV : IsOpen ((fun x : B.Mat k r => n * x) ⁻¹' U1 ∩ O) :=
      (hU1.preimage (continuous_const.matrix_mul continuous_id)).inter hDom.1
    have e2 : P (fun x => f1 (n * x)) g = P (Formalism.QuantumDeterminants.psi k r D.z Formalism.QuantumDeterminants.cStd n • J) g := by
      refine hloc _ _ _ hV ?_ g ⟨hngU1, hg.2⟩ hgG
      intro x hx hxG
      rw [hf1J (n * x) hx.1 (uh_mul hnG hxG), Pi.smul_apply]
      exact hL x ⟨(level_zero_iff x).2 hxG, hx.2⟩ n hn
    rw [← e1, ← hc, e2, hsmul _ J g hgG]
  ·
    intro g hg n hn
    have hgG := (level_zero_iff g).1 hg.1
    have hnN : n ∈ Formalism.QuantumDeterminants.Nset k r := hn.1
    have hnG : n ∈ B.GV k r := hnN.1
    have hgn : g * n ∈ O := by
      have := hDom.2 g hg 1 (one_S D.z) n ⟨1, Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r D.z', n, hn, by simp⟩
      simpa using this
    have hgnG : g * n ∈ B.GV k r := uh_mul hgG hnG
    obtain ⟨f1, U1, hf1, hf1c, hf1O, hU1, hgnU1, hf1J⟩ := hext (g * n) hgnG hgn
    have hp : D.inSS (pOf 1 1 1 n) := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [pOf, Equiv.apply_symm_apply]
      · exact Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r D.z
      · exact mem_n_one
      · exact Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r D.z'
      · exact hnN
    have hrho : ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.rho D (pOf 1 1 1 n) F = fun x => F (x * n) := by
      intro F
      rw [rho_pOf]
      funext x
      rw [mat_inv_one, hπ1, hπ'1]
      ext v
      simp
    have hc := hcomm f1 hf1 hf1c hf1O _ hp g hg.2 hgG
    rw [hrho, hrho] at hc
    beta_reduce at hc
    have e1 : P f1 (g * n) = P J (g * n) := hloc U1 f1 J hU1 hf1J (g * n) hgnU1 hgnG
    have hV : IsOpen ((fun x : B.Mat k r => x * n) ⁻¹' U1 ∩ O) :=
      (hU1.preimage (continuous_id.matrix_mul continuous_const)).inter hDom.1
    have e2 : P (fun x => f1 (x * n)) g = P (Formalism.QuantumDeterminants.psi k r D.z' Formalism.QuantumDeterminants.cStd n • J) g := by
      refine hloc _ _ _ hV ?_ g ⟨hgnU1, hg.2⟩ hgG
      intro x hx hxG
      rw [hf1J (x * n) hx.1 (uh_mul hxG hnG), Pi.smul_apply]
      exact hR x ⟨(level_zero_iff x).2 hxG, hx.2⟩ n hn
    rw [← e1, ← hc, e2, hsmul _ J g hgG]
  ·
    intro g hg h hh h' hh'
    have hgG := (level_zero_iff g).1 hg.1
    have hhG : h ∈ B.GV k r := hh.1
    have hh'G : h' ∈ B.GV k r := hh'.1
    have hu := isUnit_of_uh hhG
    have hu' := isUnit_of_uh hh'G
    have hhg : h * g * h' ∈ O := by
      have := hDom.2 g hg h ⟨h, hh, 1, one_N, by simp⟩ h' ⟨h', hh', 1, one_N, by simp⟩
      simpa using this
    have hhgG : h * g * h' ∈ B.GV k r := uh_mul (uh_mul hhG hgG) hh'G
    obtain ⟨f1, U1, hf1, hf1c, hf1O, hU1, hhgU1, hf1J⟩ := hext (h * g * h') hhgG hhg
    have hp : D.inSS (pOf h⁻¹ 1 h' 1) := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [pOf, Equiv.apply_symm_apply]
      · exact uw_inv hh
      · exact mem_n_one
      · exact hh'
      · exact mem_n_one
    have hrho : ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.rho D (pOf h⁻¹ 1 h' 1) F =
        fun x => (D.π h⁻¹).comp ((F (h * x * h')).comp (D.π' h'⁻¹)) := by
      intro F
      rw [rho_pOf]
      funext x
      rw [Matrix.nonsing_inv_nonsing_inv h hu, mat_inv_one]
      simp [Matrix.mul_assoc]

    have eL : (D.π h⁻¹).comp (D.π h) = 1 := by
      rw [← D.π_rep.2 _ (uw_inv hh) _ hh, Matrix.nonsing_inv_mul h hu, hπ1]
    have eL' : (D.π h).comp (D.π h⁻¹) = 1 := by
      rw [← D.π_rep.2 _ hh _ (uw_inv hh), Matrix.mul_nonsing_inv h hu, hπ1]
    have eR : (D.π' h').comp (D.π' h'⁻¹) = 1 := by
      rw [← D.π'_rep.2 _ hh' _ (uw_inv hh'), Matrix.mul_nonsing_inv h' hu', hπ'1]
    have eR' : (D.π' h'⁻¹).comp (D.π' h') = 1 := by
      rw [← D.π'_rep.2 _ (uw_inv hh') _ hh', Matrix.nonsing_inv_mul h' hu', hπ'1]
    have eLv : ∀ w, D.π h⁻¹ (D.π h w) = w := fun w => by simpa using congrArg (fun L => L w) eL
    have eL'v : ∀ w, D.π h (D.π h⁻¹ w) = w := fun w => by simpa using congrArg (fun L => L w) eL'
    have eRv : ∀ w, D.π' h' (D.π' h'⁻¹ w) = w := fun w => by simpa using congrArg (fun L => L w) eR
    have eR'v : ∀ w, D.π' h'⁻¹ (D.π' h' w) = w := fun w => by simpa using congrArg (fun L => L w) eR'
    have hc := hcomm f1 hf1 hf1c hf1O _ hp g hg.2 hgG
    rw [hrho, hrho] at hc
    have e1 : P f1 (h * g * h') = P J (h * g * h') := hloc U1 f1 J hU1 hf1J _ hhgU1 hhgG
    have hV : IsOpen ((fun x : B.Mat k r => h * x * h') ⁻¹' U1 ∩ O) :=
      (hU1.preimage ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)).inter hDom.1
    have e2 : P (fun x => (D.π h⁻¹).comp ((f1 (h * x * h')).comp (D.π' h'⁻¹))) g = P J g := by
      refine hloc _ _ _ hV ?_ g ⟨hhgU1, hg.2⟩ hgG
      intro x hx hxG
      rw [hf1J _ hx.1 (uh_mul (uh_mul hhG hxG) hh'G), hU x ⟨(level_zero_iff x).2 hxG, hx.2⟩ h hh h' hh']
      ext v
      simp [eLv, eRv]
    rw [e2] at hc
    beta_reduce at hc
    rw [e1] at hc

    rw [hc]
    ext v
    simp [eL'v, eR'v]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt MeasureTheory Filter Topology

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem rw_eq_zero_of_not_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (h : B.Mat k r → E) :
    ∀ (w : List (B.Mat k r)) (x : B.Mat k r), x ∉ tsupport h → B.Rw w h x = 0 := by
  intro w
  induction w with
  | nil =>
    intro x hx
    show h x = 0
    by_contra hne
    exact hx (subset_tsupport _ hne)
  | cons X w ih =>
    intro x hx
    show RdV X (B.Rw w h) x = 0
    have hO : IsOpen (tsupport h)ᶜ := (isClosed_tsupport h).isOpen_compl
    have hc : Continuous (fun t : ℝ => x * NormedSpace.exp ((t : ℂ) • X)) :=
      (Formalism.FourierDecayAlt.P.B5.curve_contDiff x X).continuous
    have h0 : (fun t : ℝ => x * NormedSpace.exp ((t : ℂ) • X)) 0 ∈ (tsupport h)ᶜ := by
      show x * NormedSpace.exp (((0 : ℝ) : ℂ) • X) ∈ _
      rw [Formalism.FourierDecayAlt.P.B5.curve_zero]
      exact hx
    have hev : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), x * NormedSpace.exp (((t : ℝ) : ℂ) • X) ∈ (tsupport h)ᶜ :=
      hc.continuousAt.preimage_mem_nhds (hO.mem_nhds h0)
    have heq : (fun t : ℝ => B.Rw w h (x * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 (0 : ℝ)] fun _ : ℝ => (0 : E) :=
      hev.mono fun t ht => ih _ ht
    unfold RdV
    rw [heq.deriv_eq]
    simp

theorem integrable_nn {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (B.GV k r) μ) {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
    {A : B.Mat k r → E₁} {C : B.Mat k r → E₂} (hA : ContinuousOn A (B.GV k r)) (hC : ContinuousOn C (B.GV k r))
    {K : Set (B.Mat k r)} (hK : IsCompact K) (hAz : ∀ x, x ∉ K → A x = 0) :
    Integrable (fun g : Mt k r => ‖A (Matrix.of g)‖ * ‖C (Matrix.of g)‖) μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨hμ.finite_compact⟩
  have hu : ContinuousOn (fun x => ‖A x‖ * ‖C x‖) (B.GV k r) :=
    (continuous_norm.comp_continuousOn hA).mul (continuous_norm.comp_continuousOn hC)
  have hKG : IsCompact (K ∩ B.GV k r) := hK.inter_right Formalism.FourierDecayAlt.P.B5.GV_closed
  obtain ⟨M, hM⟩ := hKG.exists_bound_of_continuousOn (hu.mono Set.inter_subset_right)
  have hmeas : AEStronglyMeasurable (fun g : Mt k r => ‖A (Matrix.of g)‖ * ‖C (Matrix.of g)‖) μ := by
    have h1 := Formalism.FourierDecayAlt.P.B5.aesm_of_continuousOn hμ (f := fun x => ((‖A x‖ * ‖C x‖ : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp_continuousOn hu)
    exact (Complex.continuous_re.comp_aestronglyMeasurable h1).congr (Eventually.of_forall fun g => by simp)
  have hKm : IsCompact (Matrix.of ⁻¹' K : Set (Mt k r)) := hK
  refine Integrable.mono' ((integrableOn_const hKm.measure_lt_top.ne).integrable_indicator
    hKm.isClosed.measurableSet) hmeas ?_
  filter_upwards [Formalism.FourierDecayAlt.P.B5.haar_ae hμ] with g hg
  by_cases hgK : Matrix.of g ∈ K
  · have hg' : g ∈ (Matrix.of ⁻¹' K : Set (Mt k r)) := hgK
    rw [Set.indicator_of_mem hg']
    exact hM _ ⟨hgK, hg⟩
  · have hg' : g ∉ (Matrix.of ⁻¹' K : Set (Mt k r)) := hgK
    simp only [Set.indicator, hg', if_false, hAz _ hgK, norm_zero, zero_mul, le_refl]

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

open Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem form_adjoint_holds : FormAdj := by
  intro k r Wp Wq _ _ _ _ _ _ D Θ hs hc F F' hF hFc hFs hF' hF'c hF's
  have e1 : (Matrix.of (Matrix.of.symm (1 : B.Mat k r)) : B.Mat k r) = 1 := Equiv.apply_symm_apply _ _
  have hp0 : D.inSS ((Matrix.of.symm 1, Matrix.of.symm 1), (Matrix.of.symm 1, Matrix.of.symm 1)) := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [e1]
    · exact Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r D.z
    · exact (Formalism.QuantumDeterminants.nSubgroup k r).1
    · exact Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r D.z'
    · exact (Formalism.QuantumDeterminants.nSubgroup k r).1
  have hrho : ∀ A : B.Mat k r → (Wq →L[ℂ] Wp),
      B.rho D ((Matrix.of.symm 1, Matrix.of.symm 1), (Matrix.of.symm 1, Matrix.of.symm 1)) A = A := by
    intro A
    funext g
    simp only [B.rho, B.sgs, e1, inv_one, mul_one, one_mul, D.π_rep.1, D.π'_rep.1]
    ext v
    simp
  have hI : B.IntClause D Θ F F' := by
    intro p hp T hT i j _ _
    have hcA : B.CkOn ⊤ (B.GV k r) (fun x => T.coefAdj x (F' x)) :=
      Formalism.FourierDecayAlt.P.B5.ckOn_coef (hs T hT).2 hF' hF's
    have hK : IsCompact (tsupport (fun x => T.coefAdj x (F' x))) :=
      IsCompact.of_isClosed_subset hF'c (isClosed_tsupport _)
        (closure_mono fun x hx h0 => hx (by show T.coefAdj x (F' x) = 0; rw [h0, map_zero]))
    exact integrable_nn D.haarG
      (Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn (Formalism.FourierDecayAlt.P.JFxI.ckOn_Rw_top' hcA _ fun X hX =>
        T.word_lie X (List.mem_of_mem_take (List.mem_reverse.1 hX))))
      (Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn (Formalism.FourierDecayAlt.P.JFxI.ckOn_Rw_top' (Formalism.FourierDecayAlt.P.B5.ckOn_rho D hp hF) _
        fun X hX => T.word_lie X (List.mem_of_mem_drop hX)))
      hK (fun x hx => rw_eq_zero_of_not_mem _ _ x hx)
  have key := Formalism.FourierDecayAlt.P.phase_function_adjoint k r Wp Wq D (B.GPos D) Θ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gPos_stable D) hs hc F F'
    (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hF) (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hF') hFs hF's hI _ hp0
  unfold B.Ph at key
  rwa [hrho, hrho] at key

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
end
