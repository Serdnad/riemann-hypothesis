module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WordOperatorRadialPointwiseBound
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle005
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MirrorTodaRadialOperatorPolynomialCoefficientLif
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.Bundle001
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsNormBoundThreeFamilies
public import Formalism.HermitianCurvature.Bundle008
public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle038
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle162
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle149
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle149
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle090
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle115
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle179
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle128
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceCompactSupportCoefficient
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.wordOperator_radial_pointwise_bound : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ (S : Type) [Fintype S] [DecidableEq S], ∀ (T : Set (RA P Bs)) (a : ℕ), (∀ x ∈ basics d, x ∈ nfSpan d T 0 a 1) → ∀ w : List (Letter ℂ S), admitted st w → ∃ (C : ℝ) (J : ℕ) (Ts : List (List (RA P Bs))), 0 ≤ C ∧ (∀ H ∈ Ts, H.length = w.length ∧ ∀ h ∈ H, h ∈ T) ∧ ∀ (φ : ℝ → ℝ) (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')), LE.SmoothLog φ → IsMulG P Bs φ W → ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (e : Ix S), ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z', nv ((((ofWord L st w).F * TL.bTA L w) e e1).1 (W 0 Φ)) x ≤ C * ((dR P Bs x.1 x.2)⁻¹ ^ w.length * (gR P Bs x.1 x.2)⁻¹ ^ (a * w.length)) * (∑ j ∈ Finset.range (J + 1), |LE.ld j φ (gR P Bs x.1 x.2)|) * (Ts.map fun H => nv (H.prod.1 Φ) x).sum := by
  first | exact @GlobalTheory.HatNF.RadBound.word_bound | exact GlobalTheory.HatNF.RadBound.word_bound | (intros; apply GlobalTheory.HatNF.RadBound.word_bound <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.mirrorTodaRadialOperator_polynomialCoefficient_lift : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ y : ℝ, PolyLift P Bs (2 * P.r + P.k + 1) (8 * (P.r + 1) * (2 * P.r + P.k + 1)) (d.L.Ahatv y) := by
  first | exact @GlobalTheory.MirrorToda.polyLift_ahatv | exact GlobalTheory.MirrorToda.polyLift_ahatv | (intros; apply GlobalTheory.MirrorToda.polyLift_ahatv <;> assumption)
end

section


theorem _root_.GlobalTheory.T.wignerShiftedPlacesExist_proof : GlobalTheory.WigSh.ShiftExists := by
  first | exact @GlobalTheory.wignerShiftedPlacesExist_proof.shiftExists | exact GlobalTheory.wignerShiftedPlacesExist_proof.shiftExists | (intros; apply GlobalTheory.wignerShiftedPlacesExist_proof.shiftExists <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory


open scoped Matrix.Norms.Elementwise in
theorem ckOn_group_finset_sum {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type}
    (s : Finset ι) (Fi : ι → B.Mat k r → E) (h : ∀ i, B.CkOn ⊤ (B.GV k r) (Fi i)) :
    B.CkOn ⊤ (B.GV k r) (fun g => ∑ i ∈ s, Fi i g) := by
  intro g₀ hg₀
  choose U f hU hgU hf hff using fun i => h i g₀ hg₀
  refine ⟨⋂ i ∈ s, U i, fun g => ∑ i ∈ s, f i g, isOpen_biInter_finset fun i _ => hU i,
    Set.mem_iInter₂.2 fun i _ => hgU i, ?_, ?_⟩
  · exact ContDiffOn.sum fun i hi => (hf i).mono fun g hg => Set.mem_iInter₂.1 hg i hi
  · intro g hg hG
    exact Finset.sum_congr rfl fun i hi => hff i g (Set.mem_iInter₂.1 hg i hi) hG

theorem levelZero_form_le_normC_of_eigen_sum : GlobalTheory.HCXi.BesselXiIntegrable → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (d : ℕ) (A : ℝ) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ), B.AB P.k P.r ≤ A → (∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * P.r + P.k + 1) → ℤ), (∀ i s, |ν i s| ≤ ((d : ℕ) : ℤ)) ∧ (∀ i, (B.CkOn ⊤ (B.GV P.k P.r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A) m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV P.k P.r, Q.CV P.k P.r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ B.GV P.k P.r, (F) g = ∑ i, Fi i g) → (∀ y : ℝ, ∏ t, (|y + lam t| + (d : ℝ)) ≤ nn y) → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → (p.RR F 0 w [] []).re ≤ TBB.normC nn w * (B.beta p.T.base F F).re := by
  intro hXi Wp Wq _ _ _ _ _ _ P p lam d A nn F Y N hA hF hnn w hw _
  have hsm : B.CkOn ⊤ (B.GV P.k P.r) F := by
    obtain ⟨N₀, Fi, ν, -, hc, -, hsum⟩ := hF
    exact (ckOn_inCC_congr_on_group P.k P.r _ A (fun g => ∑ i, Fi i g) F
      (fun g hg => (hsum g hg).symm)).1 (ckOn_group_finset_sum Finset.univ Fi fun i => (hc i).1)
  have hs : M.sgn P p.l0 = 1 ∨ M.sgn P p.l0 = -1 := by
    unfold M.sgn
    exact neg_one_pow_eq_or ℂ _
  unfold KB.Pl.RR TBB.normC
  rw [Formalism.FourierDecayAlt.P.level_zero_holds _ _ _ _ _ _ _ _ _ _ _ hsm (Formalism.FourierDecayAlt.P.CutBP.good_positioned_of_cut hw.1)]
  exact GlobalTheory.levelZero_energy_le_of_eigen_sum hXi P.k P.r Wp Wq p.T.base lam d A _ nn F hs hA hF hnn w

end GlobalTheory
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.QuantumDeterminants NumberField MeasureTheory
open scoped ComplexOrder

namespace GlobalTheory.WeightedFormPos


open Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.Q in
theorem form_nonneg_of_cptCoef (hXi : B.XiExists) (hP : P5.ThmPActualCpt) {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter)
    (hc : KB.CutWord P p.l0 w) (x : Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (hxc : ∀ e, KB.CptCoef (p.T.bs j) (x e)) : 0 ≤ p.form j hj w x x := by
  obtain ⟨ε, hε, hx⟩ := PBL.nv_of_cv (Bs := p.T.bs j) (x := x) hxc
  have hOK : P.OK := p.hP.1
  obtain ⟨hl1, hlk, -⟩ := p.hl
  let jF : Fin (P.r + 1) := ⟨j, by omega⟩
  have hPl := Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P p.T jF p.hP
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl
  obtain ⟨L, st, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl X p.l0
  obtain ⟨μ0, hμ0⟩ := Formalism.FourierDecayAlt.P.JCTx5.exists_haar_level_zero (Nat.sub_self P.r) (p.T.bs P.r)
  set μ := μ0.map (Formalism.FourierDecayAlt.P.JCTx5.embL P.k (P.r - j)) with hμ
  have hD : IsData (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' X μ L st p.l0 :=
    ⟨hPl, Formalism.FourierDecayAlt.P.JCTx5.haar_glev μ0 hμ0, h1, h2, h3, h4, h5, h6⟩
  obtain ⟨K, hThm, -, -, hJ⟩ := hP Wp Wq (Fin w.length) (JC.parLev P jF) _ _ _ _ X μ L st p.l0
    (p.T.bs jF) _ _ hD hl1 hlk rfl rfl rfl rfl le_rfl le_rfl
  obtain ⟨Cst, hC, hform⟩ := radialModuleForm_of_xiExists hXi Wp Wq P p.T jF X μ L st p.l0 hD
  have hpic := fun a => (hxc a).2.1.elim fun R hR =>
    PBF.pic_of_cptClause (p.T.bs jF) (K 0) hJ hε (hx a) (R := R) hR
  choose Φ hΦK hΦ using hpic
  have hW := Formalism.FourierDecayAlt.P.JCTx5.wordOK_of (JC.parLev P jF) _ _ _ _ st p.l0 hPl.1 hl1 hlk h3 h4 w hc.1 hc.2
  have hpos := ((hThm (D.positionted w) hW).2.2 0 (fun _ => 1) (fun _ => one_ne_zero)).2 Φ (fun a _ => hΦK a)
  have hpos' : 0 ≤ P5.form μ 0 (P5.act (P5.RRi L st 0 (D.positionted w)) Φ) Φ 0 :=
    hpos.trans_eq (Formalism.FourierDecayAlt.P.JCx2.form_zero_indep μ _ _ _ _)
  have e := hform w x x Φ Φ ε hε hx hx hΦ hΦ
  show 0 ≤ D.formLev p.T (M.sgn P p.l0) jF w x x
  rw [e]
  exact mul_nonneg (by exact_mod_cast hC.le) hpos'

theorem posAt_of_cptCoef_of_xiExists (hXi : B.XiExists) : P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ), (∀ y, 0 ≤ nn y) → KB.CptCoef p.T.base F → TBB.PosAt p nn F Y N := by
  intro hA Wp Wq _ _ _ _ _ _ P p nn F Y N hnn hF
  refine Formalism.FourierDecayAlt.P.TBBx3.posAt_of_forms p nn F Y N hnn ?_
  intro j w h hj hw _
  by_cases hh : D.IsLocPt h j
  · rw [PBL.rr_eq_form p F j hj w h h hh hh]
    have h0 := form_nonneg_of_cptCoef hXi hA P p j hj w hw.1 _
      (fun e => Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F j hj w h hh hF e)
    exact (Complex.nonneg_iff.1 h0).1
  · unfold KB.Pl.RR D.RRplace
    rw [dite_eq_right (fun h1 => hh h1.1)]
    simp

theorem formPosCpt_of_xiExists (hXi : B.XiExists) : PBL.FormPosCpt :=
  fun hP _ _ _ _ _ _ _ _ P p j hj w hc x hx => form_nonneg_of_cptCoef hXi hP P p j hj w hc x hx

end GlobalTheory.WeightedFormPos
end
