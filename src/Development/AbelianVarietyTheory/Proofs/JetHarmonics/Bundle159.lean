module

public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle075
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle138
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle154
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle156
public import Formalism.HermitianCurvature.Bundle008
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle131
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle134
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle115
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle128
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TLFinal
public import Formalism.HermitianCurvature.StatementD
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CccoefMono
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
public import Formalism.LocalToGlobal.CharacterGerms.Bundle027
public import Formalism.LocalToGlobal.CharacterGerms.Bundle023
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle085
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle155
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle090
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle074
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle064
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsIntegralGaugedFormalGroupLawSelfConjugateSquar
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle013
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsometryTriangularPeriodsOfFramePointMove
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NotAntiIsometryOfTriangularRelatedPeriods
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm

@[expose] public section

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem GlobalTheory.exists_sideFam_both_sides : Hyps → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r), Num P.k P.r lam P.u b bv ga h q0 → IsFam lam q0 R → ∃ (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ), (haveI := FiniteDimensional.complete ℂ Wp; SideFam p.T.base.z p.T.base.π p.T.base.μW p.T.base.μN p.T.base.μG q0 R l dg) ∧ (haveI := FiniteDimensional.complete ℂ Wq; SideFam p.T.base.z' p.T.base.π' p.T.base.μW' p.T.base.μN p.T.base.μG q0 R l' dg) := by
  intro hH P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 R hN hF
  have := FiniteDimensional.complete ℂ Wp
  have := FiniteDimensional.complete ℂ Wq
  obtain ⟨-, -, -, -, -, hu, hu'⟩ := p.hP
  obtain ⟨νq, νq', hS, hS'⟩ := GlobalTheory.T.besselDatum_both_sides_are_sides P.k P.r Wp Wq p.T.base P.u P.u' hu hu'
  obtain ⟨⟨-, -, -, -, hG⟩, hν⟩ := GlobalTheory.NumFam.num_fam P.k P.r lam P.u b bv ga h q0 hN
  obtain ⟨c, hc, hd⟩ := GlobalTheory.BesselDegree.schur_fdeg hH P.k P.r (PI.BesselPeriodGGP.eps48 P.k P.r) p.T.base.μG
    hS.2.2.2.2.2.2.1
  have h1 : ∀ ν, ∃ l : (R ν).H → Wp, n1 ν ≤ q0 →
      IsBeL (R ν) p.T.base.z p.T.base.π p.T.base.μW p.T.base.μN l := by
    intro ν
    by_cases hq : n1 ν ≤ q0
    · obtain ⟨l, hl⟩ := GlobalTheory.T.bessel_gap_exists_functional hH P.k P.r _ _ (h / 2) (R ν) Wp _ _ _ _ _ _ _ (hF ν hq) (hν ν hq).2.2.1 hG hS
      exact ⟨l, fun _ => hl⟩
    · exact ⟨0, fun h' => absurd h' hq⟩
  have h2 : ∀ ν, ∃ l : (R ν).H → Wq, n1 ν ≤ q0 →
      IsBeL (R ν) p.T.base.z' p.T.base.π' p.T.base.μW' p.T.base.μN l := by
    intro ν
    by_cases hq : n1 ν ≤ q0
    · obtain ⟨l, hl⟩ := GlobalTheory.T.bessel_gap_exists_functional hH P.k P.r _ _ (h / 2) (R ν) Wq _ _ _ _ _ _ _ (hF ν hq) (hν ν hq).2.2.1 hG hS'
      exact ⟨l, fun _ => hl⟩
    · exact ⟨0, fun h' => absurd h' hq⟩
  choose l hl using h1
  choose l' hl' using h2
  have hp : ∀ ν, n1 ν ≤ q0 → 0 < c * Formalism.QuantumDeterminants.fdegHC (fun a => lam a + (ν a : ℝ)) := fun ν hq =>
    mul_pos hc (GlobalTheory.FamilyDegreeRatio.degree_ratios P.k P.r lam P.u b bv ga h q0 hN ν hq).1
  exact ⟨l, l', fun ν => c * Formalism.QuantumDeterminants.fdegHC (fun a => lam a + (ν a : ℝ)),
    fun ν hq => ⟨hl ν hq, hp ν hq, (hd _ _ (hF ν hq)).1⟩,
    fun ν hq => ⟨hl' ν hq, hp ν hq, (hd _ _ (hF ν hq)).1⟩⟩
end

section

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

theorem _root_.GlobalTheory.T.mem_cuspForms_of_multiple_rational_isometry_move : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (a : GL (Fin r) E) (h : IsMatch X X' a) (la : Wt X.Ψ r) (la' : Wt X'.Ψ r), (∀ (τ : X'.Ψ) i, la' τ i = la ⟨τ.1, h.mem τ⟩ i) → ∀ (P : Frame X.Ψ r → ℂ) (Q : Frame X'.Ψ r → ℂ) (c : ℂ), X.IsSec la P → Q ∈ X'.SS la' → (∀ x ∈ X.dom, P x = c * Q (lact a (castFr h.psi x))) → P ∈ X.SS la := by
  first | exact @GlobalTheory.LevelCusp.mem_SS_of_isMatch | exact GlobalTheory.LevelCusp.mem_SS_of_isMatch | (intros; apply GlobalTheory.LevelCusp.mem_SS_of_isMatch <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

namespace GlobalTheory.TopVec

theorem Ew_cutF_eventually_eq : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) f → KB.CutWord P p.l0 w → ∀ᵐ c : Fin (P.r + 1) → ℂ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), TBB.Ew p (fun _ => 1) (D.cutF p.T.base χ f ε) (P.r + 1) w (TBB.bigPt P.r c) = TBB.Ew p (fun _ => 1) f (P.r + 1) w (TBB.bigPt P.r c) := by
  intro Wp Wq _ _ _ _ _ _ P p Cb f χ w hΘ hχ hf hw
  obtain ⟨δ, hδ, hδχ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ x, x < δ → χ x = 0 := by
    have h := hχ
    unfold C6.IsCut0 at h
    tauto
  refine Filter.Eventually.of_forall fun c => ?_
  simp only [Ew_eq_norm_tv_sq]
  by_cases hG : 0 < TBB.Gp p (TBB.bigPt P.r c)
  · filter_upwards [Ioo_mem_nhdsGT hG] with ε hε
    rw [(GlobalTheory.T.topVector_cutoff_eq_and_vanish Wp Wq P p Cb χ δ ε f w c hΘ hw hχ hδχ hε.1 hf).1 hε.2]
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : 0 < ε := hε
    have h := GlobalTheory.T.topVector_cutoff_eq_and_vanish Wp Wq P p Cb χ δ ε f w c hΘ hw hχ hδχ hε' hf
    rw [h.2.1 ((not_lt.1 hG).trans_lt (mul_pos hδ hε')), h.2.2 (not_lt.1 hG)]

end GlobalTheory.TopVec
end

section

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace GlobalTheory.WithRightAction

noncomputable def withRight {k r : ℕ} {Wp Wq Wq' : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq']
    (Bs : B.RealPlaceData k r Wp Wq) (π'' : B.Mat k r → (Wq' →L[ℂ] Wq')) (u' : ℕ → ℝ)
    (h : Q.IsType k r Bs.z' π'' u') : B.RealPlaceData k r Wp Wq' :=
  { z := Bs.z, z' := Bs.z', π := Bs.π, π' := π'', μG := Bs.μG, μW := Bs.μW, μN := Bs.μN, μW' := Bs.μW',
    μsec := Bs.μsec, χ := Bs.χ, k_pos := Bs.k_pos, z_mem := Bs.z_mem, z'_mem := Bs.z'_mem, T_pos := Bs.T_pos,
    T'_pos := Bs.T'_pos, π_rep := Bs.π_rep, π'_rep := h.2.1, π_unitary := Bs.π_unitary, π'_unitary := h.2.2.2.1,
    π_cont := Bs.π_cont, π'_cont := h.2.2.1, haarG := Bs.haarG, haarW := Bs.haarW, haarN := Bs.haarN,
    haarW' := Bs.haarW', sec := Bs.sec, χ_smooth := Bs.χ_smooth, χ_supp := Bs.χ_supp, χ_int := Bs.χ_int }

theorem exists_place_other_right_type : ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ (P : M.Par) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Wq' : Type) [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq'] (p : KB.Pl P Wp Wq) (u u' : ℕ → ℝ) (π'' : B.Mat P.k P.r → (Wq' →L[ℂ] Wq')) (l0 : ℕ), Q.IsPlace (⟨P.k, P.r, P.T, P.T', u, u'⟩ : M.Par) p.T.base.z p.T.base.z' p.T.base.π π'' → 1 ≤ l0 → l0 ≤ P.k → ∃ q : KB.Pl (⟨P.k, P.r, P.T, P.T', u, u'⟩ : M.Par) Wp Wq', q.l0 = l0 ∧ q.T.base.z = p.T.base.z ∧ q.T.base.z' = p.T.base.z' ∧ q.T.base.π = p.T.base.π ∧ q.T.base.π' = π'' ∧ q.ν' = p.ν' ∧ q.m₀ = p.m₀ ∧ KB.InDDplus2 (⟨P.k, P.r, P.T, P.T', u, u'⟩ : M.Par) q.l0 q.T.base Cb q.Θ := by
  obtain ⟨Cb, hCb, hTL⟩ := Formalism.FourierDecayAlt.P.top_lift_exists
  refine ⟨Cb, hCb, ?_⟩
  intro P Wp _ _ _ Wq _ _ _ Wq' _ _ _ p u u' π'' l0 hPl hl1 hl2
  obtain ⟨T, h1, h2, h3, h4, hN⟩ := Formalism.FourierDecayAlt.P.exists_normalized_tower P.k P.r Wp Wq'
    (withRight p.T.base π'' u' hPl.2.2.2.2.2.2)
  change T.base.z = p.T.base.z at h1
  change T.base.z' = p.T.base.z' at h2
  change T.base.π = p.T.base.π at h3
  change T.base.π' = π'' at h4
  have hPT : Q.IsPlace (⟨P.k, P.r, P.T, P.T', u, u'⟩ : M.Par) T.base.z T.base.z' T.base.π T.base.π' := by
    rw [h1, h2, h3, h4]; exact hPl
  have hF : D.IsBaseFrame T.base p.ν' p.m₀ := by
    have := p.hF
    unfold D.IsBaseFrame at this ⊢
    rw [h1, h2]; exact this
  obtain ⟨-, μ, -, -, ⟨-, hμ, -⟩, -⟩ := p.hΘ
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPT
  obtain ⟨L, st, g1, g2, g3, g4, g5, g6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPT X l0
  have hD : P5.IsData (⟨P.k, P.r, P.T, P.T', u, u'⟩ : M.Par) T.base.z T.base.z' T.base.π T.base.π' X μ L st l0 :=
    ⟨hPT, hμ, g1, g2, g3, g4, g5, g6⟩
  obtain ⟨f1, f2, f3⟩ := Formalism.FourierDecayAlt.P.HaarMassHermitianCurvature.frameVec_facts T.base p.ν' p.m₀ hF
  obtain ⟨Θ, hI, hC⟩ := hTL Wp Wq' (⟨P.k, P.r, P.T, P.T', u, u'⟩ : M.Par) T.base X μ L st l0 hl1 hl2 hD
  obtain ⟨TP⟩ := Formalism.FourierDecayAlt.P.type_projectors_exist Wp Wq' (⟨P.k, P.r, P.T, P.T', u, u'⟩ : M.Par)
    T.base.z T.base.z' T.base.π T.base.π' (p.m₀.mulVec p.ν') hPT f1 f2 f3
  exact ⟨⟨l0, T, p.ν', p.m₀, Θ, TP, ⟨hl1, hl2, p.hl.2.2⟩, hN, hF, hPT, ⟨X, μ, L, st, hD, hI⟩⟩,
    rfl, h1, h2, h3, h4, rfl, rfl, hC⟩

end GlobalTheory.WithRightAction
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory

theorem cutF_approximants_ccle :
    ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (χ : ℝ → ℝ) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (A₀ ε A : ℝ) (mm : ℕ), C6.IsCut0 χ → 0 < ε → B.CkOn ⊤ (B.GV k r) f → (∀ m : ℕ, B.InCC A₀ m f) → A + 1 + 2 * ((r : ℝ) + 1) * (mm : ℝ) ≤ A₀ → ∃ K : ℝ, 0 ≤ K ∧ B.CCle A mm (D.cutF Bs χ f ε) K ∧ ∀ n : ℕ, B.CCle A mm ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε g)) K ∧ B.CCle A mm ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε g) - (D.cutF Bs χ f ε)) (K / ((n : ℝ) + 1)) := by
  intro k r Wp Wq _ _ _ _ _ _ Bs χ f A₀ ε A mm hχ hε _ hfA hA
  obtain ⟨b, hb⟩ := Formalism.FourierDecayAlt.P.PBE.cutF_inCC Bs hχ hfA hε (A + 1) mm hA
  generalize D.cutF Bs χ f ε = H at hb ⊢
  have hb0 : 0 ≤ b := Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hb
  have hb' : B.CCle A mm H b := Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A (by linarith) hb
  obtain ⟨Kp, hKp0, hKp⟩ := Formalism.FourierDecayAlt.P.JCx2.pd_cut_ccle (k := k) (r := r) (E := Wq →L[ℂ] Wp) mm
  have hψ : ∀ n : ℕ, B.CCle A mm (fun g => Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g • H g)
      (Kp * b / ((n : ℝ) + 1)) := fun n => by
    have h := hKp ((n : ℝ) + 1) (by positivity) (A + 1) H b hb
    rwa [add_sub_cancel_right] at h
  have hc : ∀ (n : ℕ) (g : B.Mat k r), ((Real.smoothTransition
      ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)
        = 1 - Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g := fun n g =>
    Formalism.FourierDecayAlt.P.PBE.cut_eq (fun (n : ℕ) (g : B.Mat k r) => ((Real.smoothTransition
      ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) (fun _ _ => rfl) n g
  have hKb : 0 ≤ Kp * b := mul_nonneg hKp0 hb0
  refine ⟨b + Kp * b, by positivity, Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c hb' (by linarith), fun n => ⟨?_, ?_⟩⟩
  · have e : (fun g : B.Mat k r => ((Real.smoothTransition
        ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • H g)
          = fun g => H g + (-1 : ℂ) • (Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g • H g) := by
      funext g
      rw [hc n g, sub_smul, one_smul, neg_one_smul, sub_eq_add_neg]
    rw [e]
    refine Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c
      (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add hb' (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul (-1) (hψ n))) ?_
    have h1 : Kp * b / ((n : ℝ) + 1) ≤ Kp * b := div_le_self hKb (by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    simp only [norm_neg, norm_one, one_mul]
    linarith
  · have e : ((fun g : B.Mat k r => ((Real.smoothTransition
        ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • H g) - H)
          = fun g => (-1 : ℂ) • (Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g • H g) := by
      funext g
      rw [Pi.sub_apply, hc n g, sub_smul, one_smul, neg_one_smul, sub_sub_cancel_left]
    rw [e]
    refine Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul (-1) (hψ n)) ?_
    simp only [norm_neg, norm_one, one_mul]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)

end GlobalTheory
end

section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowAtSelf

theorem rowCondition_two_selfConjugate_of_nonDegenerate : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0), NDG Y → ∀ Hc : ∀ g, (Y.rawSelf p).CartHyp V g, RawChart.RankMaximalCondition Hc :=
  fun C _ _ V O _ _ dd Y d _ I0 _ p h Hc =>
    GlobalTheory.T.rawChart_tangent_maximalIdeal_of_nonDegenerate C V d _ _ (Y.rawSelf p) (GlobalTheory.RowLawSquare.rlaw_rawSelf C V O dd Y d I0 p)
      (GlobalTheory.T.hasGaugeAdjointLieProjectors_selfConjugatePlace C V O dd Y d I0 p) (GlobalTheory.T.nonDegenerate_formalBiextension_square C V O dd Y d I0 p h) Hc

end GlobalTheory.RowAtSelf
end

section

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_isometry_triangular_periods_of_framePointMove : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), FrMove ρ ν (U.un k x) y' → FrBor t (U.un k' x') y' → ∃ (gam : (U.X k).Λ ≃ₗ[𝓞 E] (U.X k').Λ) (A : (E →+* ℂ) → ℕ → ℕ → ℂ), (∀ u v : (U.X k).Λ, Algebra.trace ℚ E (-(U.X k').ξ0 * herm (U.X k').Gm (gam u : Fin r → E) (gam v : Fin r → E)) = Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (u : Fin r → E) (v : Fin r → E))) ∧ (∀ τ i j, j < i → A τ i j = 0) ∧ (∀ τ, ∀ i < Dw.mult τ, ∀ v : (U.X k).Λ, Formalism.L2.PjFree.perFr (U.X k') x'.1 (gam v : Fin r → E) (Formalism.L2.PjFree.relab c σ τ) i = ∑ j ∈ Finset.range (Dw.mult τ), A τ i j * Formalism.L2.PjFree.perFr (U.X k) x.1 (v : Fin r → E) (Formalism.L2.PjFree.relab c σ τ) j) ∧ ∀ τ (i : Fin (Dw.mult τ)), A τ i i = Formalism.L2.PjFree.toC (t (some ⟨τ, i⟩) : CAt σ) := by
  first | exact @GlobalTheory.LevelCusp.exists_isometry_tri_of_frMove | exact GlobalTheory.LevelCusp.exists_isometry_tri_of_frMove | (intros; apply GlobalTheory.LevelCusp.exists_isometry_tri_of_frMove <;> assumption)
end

section

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

theorem _root_.GlobalTheory.T.not_antiIsometry_of_triangular_related_periods : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r), X.Ψ = X'.Ψ → X.p0 = X'.p0 → 1 ≤ r → ∀ (a : GL (Fin r) E), (∀ u v, herm X'.Gm ((a : Matrix (Fin r) (Fin r) E) *ᵥ u) ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) = -1 * herm X.Gm u v) → ∀ (m : (E →+* ℂ) → ℕ), (∀ τ ∈ X.Ψ, m τ = r - X.p0) → (∀ τ ∉ X.Ψ, m τ = X.p0) → ∀ x ∈ X.dom, ∀ x' ∈ X'.dom, ∀ (A : (E →+* ℂ) → ℕ → ℕ → ℂ), (∀ τ i j, j < i → A τ i j = 0) → (∀ τ, ∀ i < m τ, ∀ v ∈ X.Λ, Formalism.L2.PjFree.perFr X' x' ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i = ∑ j ∈ Finset.range (m τ), A τ i j * Formalism.L2.PjFree.perFr X x v τ j) → False := by
  first | exact @GlobalTheory.AntiIsom.not_antiIsometry | exact GlobalTheory.AntiIsom.not_antiIsometry | (intros; apply GlobalTheory.AntiIsom.not_antiIsometry <;> assumption)
end
