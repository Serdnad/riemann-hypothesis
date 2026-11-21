import Formalism.SharpRestriction.GlobalSchurBounds.PrvFOfFamilyTheoremTiesEventualIncidenceTransport
import Formalism.SharpRestriction.GlobalSchurBounds.WeightVectorSmallSharesSeven

noncomputable section

namespace Formalism.MainNotions.Lnk

open Formalism.BasicNotions Formalism.D5 Formalism.FrobeniusOrbits Formalism.LFunctionChainParameters.LHost Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds
  Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain

variable {eps : ℝ}

def LossFS (Fm : FamP eps) (eL : ℝ) : Prop :=
  ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x ≥ x0, x ∈ Fm.Win → ∃ (i0 : Fm.Ix x) (av bv : ℕ → ℤ),
    (∀ t ∈ Fm.TTn x, aWin (Fm.L x i0) (av t) ∧ (Fm.L x i0).sc.b' ≤ (bv t : ℝ) ∧ (bv t : ℝ) ≤ Fm.bTop x) ∧
    (∃ i1 : Fm.Ix x, ∀ t : (Fm.D x i1).host.TT,
        (Fm.L x i1).aT t = av (t : (Fm.D x i1).R.A).val ∧
        (Fm.L x i1).bT t = bv (t : (Fm.D x i1).R.A).val) ∧
    ∀ i : Fm.Ix x, (∀ t : (Fm.D x i).host.TT,
        (Fm.L x i).aT t = av (t : (Fm.D x i).R.A).val ∧
        (Fm.L x i).bT t = bv (t : (Fm.D x i).R.A).val) → Loss_at (Fm.L x i) C eL

theorem lossFS_of_cover (Fm : FamP eps) (eL : ℝ) (h : LossF Fm eL) (hc : Fm.CoverAll) : LossFS Fm eL := by
  obtain ⟨C, x0, hC, hL⟩ := h
  refine ⟨C, max x0 (Fm.x1 + 1), hC, fun x hx hwin => ?_⟩
  obtain ⟨i0, av, bv, h1, h2⟩ := hL x (le_of_max_le_left hx) hwin
  have hx1 : Fm.x1 < x := by linarith [le_of_max_le_right hx]
  have hn : 0 < (Fm.D x i0).R.n := by
    have e1 := (Fm.D x i0).R.two_le_m
    have e2 := (Fm.D x i0).R.m_le_f
    unfold Formalism.BasicNotions.Ranks.n
    omega
  obtain ⟨i1, -, hi1⟩ := hc x hx1 i0 0 av bv hn h1
  exact ⟨i0, av, bv, h1, ⟨i1, hi1⟩, h2⟩

theorem linkCore (Fm : FamP eps) (Cabs CH eL C5 c6 : ℝ) (hCabs : 0 ≤ Cabs) (hCH : 0 ≤ CH) (heL : 0 ≤ eL) (hc6 : 0 < c6)
    (hCount : CountF Fm) (hSM : SlopesMF Fm) (hSN : SlopesNF Fm) (hLat : LatF Fm) (hNodes : NodesF Fm)
    (hFr : FrameF Fm CH) (hLoss : LossFS Fm eL) (hChar : CharF Fm) (hWin : WinF Fm)
    (cTT : ChosenTT Fm) (cQD : ChosenQD Fm C5) (cTh : ChosenThin Fm c6) (lI : LinkIRR Fm) (lD : LinkDIV Fm Cabs CH) :
    ∃ K cHH eK CL x0 : ℝ, ∀ x ≥ x0, x ∈ Fm.Win → ChainTied Fm Cabs eL K cHH eK CL x := by
  have lossCovered : LossWithHostCover Fm eL := by
    obtain ⟨C, x0, hC, hLossAt⟩ := hLoss
    refine ⟨C, max x0 (Fm.x1 + 1), hC, fun x hx hw => ?_⟩
    obtain ⟨i0, av, bv, hAdmissible, ⟨i1, hHost⟩, hBounds⟩ := hLossAt x (le_of_max_le_left hx) hw
    have hLarge : Fm.x1 < x := lt_of_lt_of_le (lt_add_one _) (le_of_max_le_right hx)
    refine ⟨i0, av, bv, fun u0 => ?_, hBounds⟩
    exact Fm.coverS_carry x hLarge i1 av bv hHost (hval _ u0) (by
      rw [Fm.R_eq x i1 i0]
      exact hval_lt _ u0)
  exact linkCoreOfCoveredLoss Fm Cabs CH eL C5 c6 hCabs hCH heL hc6 hCount hSM hSN hLat hNodes hFr
    lossCovered hChar hWin cTT cQD cTh lI lD

def LossesSmallShares (Fm : FamP eps) : Prop :=
  ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x ≥ x0, ∀ i : Fm.Ix x, ChW_at (Fm.Gx x i) Fm.GK → Loss_at (Fm.L x i) C 0

theorem lossF_of_7W (Fm : FamP eps) (h : LossesSmallShares Fm) (hW : ChosenW Fm) : LossF Fm 0 := by
  obtain ⟨C, x0, hC, hL⟩ := h
  obtain ⟨x1, hW⟩ := hW
  refine ⟨C, max x0 x1, hC, fun x hx hwin => ?_⟩
  obtain ⟨i0, av, bv, h1, h3⟩ := hW x (le_of_max_le_right hx) hwin
  exact ⟨i0, av, bv, h1, fun i hi => hL x (le_of_max_le_left hx) i (h3 i hi)⟩

theorem lossF_of_7 (Fm : FamP eps) (h : LossesSmallShares Fm) (hW : ChosenWS Fm) : LossFS Fm 0 := by
  obtain ⟨C, x0, hC, hL⟩ := h
  obtain ⟨x1, hW⟩ := hW
  refine ⟨C, max x0 x1, hC, fun x hx hwin => ?_⟩
  obtain ⟨i0, av, bv, h1, h2, h3⟩ := hW x (le_of_max_le_right hx) hwin
  exact ⟨i0, av, bv, h1, h2, fun i hi => hL x (le_of_max_le_left hx) i (h3 i hi)⟩

theorem size_windows_of_thick_density (Fm : FamP eps) (hT2 : ThickSetDensityEventually Fm) : WinF Fm := by
  intro c6 hc6
  have h0 : 0 < eps := fam_eps_pos Fm
  obtain ⟨aT, hT2⟩ := hT2
  obtain ⟨a1, h1⟩ := ev_pow_le_exp 1 (eps / 3) 5 one_pos (by positivity)
  obtain ⟨a3, h3⟩ := ev_pow_le_exp c6 (eps / 8) 7 hc6 (by positivity)
  obtain ⟨a4, h4⟩ := ev_pow_le_exp 1 eps 9 one_pos h0
  obtain ⟨a5, h5⟩ := ev_pow_le_exp (1 / 2) eps 5 (by norm_num) h0
  obtain ⟨a6, h6⟩ := ev_two_le_rpow (eps - (eps / 5 + eps / 100)) (by linarith)
  refine ⟨5, Fm.x1 + 3 + |a1| + |a3| + |a4| + |a5| + |a6| + |aT|, by norm_num, fun x hx i => ?_⟩
  have hpos := Fm.one_lt_family_threshold
  have n1 := abs_nonneg a1
  have n3 := abs_nonneg a3
  have n4 := abs_nonneg a4
  have n5 := abs_nonneg a5
  have n6 := abs_nonneg a6
  have nT := abs_nonneg aT
  have hx1 : Fm.x1 < x := by linarith
  have hx3 : 3 ≤ x := by linarith
  have hone : 1 ≤ x := by linarith
  have b1 : x ≥ a1 := by linarith [le_abs_self a1]
  have b3 : x ≥ a3 := by linarith [le_abs_self a3]
  have b4 : x ≥ a4 := by linarith [le_abs_self a4]
  have b5 : x ≥ a5 := by linarith [le_abs_self a5]
  have b6 : x ≥ a6 := by linarith [le_abs_self a6]
  have bT : x ≥ aT := by linarith [le_abs_self aT]
  have hsx := Fm.L_x x i hx1
  have hse := Fm.L_eps x i
  have hX : XL (Fm.L x i).sc c6 := by
    unfold XL
    rw [hsx, hse]
    exact ⟨hx3, h1 x b1 hone, h3 x b3 hone, h4 x b4 hone, h5 x b5 hone, h6 x b6⟩
  have hS := Fm.sizes x hx1 i
  have hNum := numN_at (Fm.params x hx1 i) hS (by rw [hsx]; exact hx3)
  obtain ⟨sN, sM, sK, -, -, -, sQD, -⟩ := hS
  have hLa := winE sN sQD hX.1 hX.2.2.2.2.1 hX.2.2.2.2.2
  exact size_window_at_five (Fm.params x hx1 i) sN sM sK hLa (winP sQD) hNum.1 (hT2 x bT i) c6 hX

theorem thick_density_of_construction (Fm : FamP eps) (hT2 : ThickSetEventually Fm) : ThickSetDensityEventually Fm := by
  obtain ⟨eK, x0, -, h⟩ := size_windows_of_thick_set Fm hT2 1 one_pos
  exact ⟨x0, fun x hx i => (h x hx i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem chosenBadp_of_old (Fm : FamP eps) (Cb : ℝ) (hCb : 0 ≤ Cb) (cTT : ChosenTT Fm) (cBad : ChosenBad Fm Cb) :
    ChosenBadp Fm := by
  have heps := fam_eps_pos Fm
  obtain ⟨a0, cTT⟩ := cTT
  obtain ⟨a1, cBad⟩ := cBad
  obtain ⟨a2, -, h2⟩ := ev_le_rpow (2 * eps / 3) (by positivity) (16 * Cb)
  refine ⟨Fm.x1 + 1 + |a0| + |a1| + |a2|, fun x hx i => ?_⟩
  have hpos := Fm.one_lt_family_threshold
  have n0 := abs_nonneg a0
  have n1 := abs_nonneg a1
  have n2 := abs_nonneg a2
  have hx1 : Fm.x1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hone : 1 ≤ x := by linarith
  have b0 : x ≥ a0 := by linarith [le_abs_self a0]
  have b1 : x ≥ a1 := by linarith [le_abs_self a1]
  have b2 : a2 ≤ x := by linarith [le_abs_self a2]
  have hsx := Fm.L_x x i hx1
  have hse := Fm.L_eps x i
  have hT := (cTT x b0 i).1
  have hB := cBad x b1 i
  unfold ChBad_at at hB
  unfold ChBadp_at
  have hX' : (Fm.L x i).sc.X' = Real.exp (x ^ (eps / 3)) := by
    show Real.exp ((Fm.L x i).sc.x ^ ((Fm.L x i).sc.eps / 3)) = _
    rw [hsx, hse]
  have hXone : 1 ≤ (Fm.L x i).sc.X' := by
    rw [hX']; exact Real.one_le_exp (Real.rpow_nonneg hx0.le _)
  have hM := Formalism.L2.GlobalTheoryTheory.Places.mertens (Fm.L x i).sc.X' hXone
  have hsub : ∑ p ∈ largeOrderResiduePrimes (Fm.L x i), Real.log p / p ≤
      ∑ p ∈ (Finset.range ⌈(Fm.L x i).sc.X'⌉₊).filter Nat.Prime, Real.log p / p := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      unfold largeOrderResiduePrimes at hp
      obtain ⟨h1, h2, -⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨h1, h2⟩
    · intro p _ _
      exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  have hS : ∑ p ∈ largeOrderResiduePrimes (Fm.L x i), Real.log p / p ≤ 2 * x ^ (eps / 3) := by
    refine le_trans hsub (le_trans hM ?_)
    rw [hX', Real.log_exp]
  rw [hsx] at hB
  rw [hsx, hse]
  have hx2 : 0 ≤ x ^ (-2 : ℝ) := Real.rpow_nonneg hx0.le _
  have hdn : (Fm.L x i).sc.delta1 * (Fm.D x i).R.n ≤ 2 * ((Fm.D x i).host.TT.card : ℝ) := by linarith
  have hdn0 : 0 ≤ (Fm.L x i).sc.delta1 * (Fm.D x i).R.n := by
    have : 0 ≤ (Fm.L x i).sc.delta1 := by unfold Scale.delta1; exact Real.rpow_nonneg (by rw [hsx]; exact hx0.le) _
    exact mul_nonneg this (Nat.cast_nonneg _)
  have hc0 : (0 : ℝ) ≤ ((Fm.D x i).host.TT.card : ℝ) := Nat.cast_nonneg _
  have hx3 : 0 ≤ x ^ (eps / 3) := Real.rpow_nonneg hx0.le _
  have hS0 : 0 ≤ ∑ p ∈ largeOrderResiduePrimes (Fm.L x i), Real.log p / p :=
    Finset.sum_nonneg (fun p _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
  have step : 4 * (Cb * x ^ (-2 : ℝ)) * (Fm.L x i).sc.delta1 * (Fm.D x i).R.n *
      ∑ p ∈ largeOrderResiduePrimes (Fm.L x i), Real.log p / p ≤
      ((Fm.D x i).host.TT.card : ℝ) * (x ^ (-2 : ℝ) * ((16 * Cb) * x ^ (eps / 3))) := by
    have e1 : 4 * (Cb * x ^ (-2 : ℝ)) * (Fm.L x i).sc.delta1 * (Fm.D x i).R.n *
        ∑ p ∈ largeOrderResiduePrimes (Fm.L x i), Real.log p / p =
        (4 * Cb * x ^ (-2 : ℝ)) * (((Fm.L x i).sc.delta1 * (Fm.D x i).R.n) *
          ∑ p ∈ largeOrderResiduePrimes (Fm.L x i), Real.log p / p) := by ring
    have e2 : ((Fm.L x i).sc.delta1 * (Fm.D x i).R.n) * ∑ p ∈ largeOrderResiduePrimes (Fm.L x i), Real.log p / p ≤
        (2 * ((Fm.D x i).host.TT.card : ℝ)) * (2 * x ^ (eps / 3)) :=
      mul_le_mul hdn hS hS0 (by linarith)
    rw [e1]
    calc (4 * Cb * x ^ (-2 : ℝ)) * (((Fm.L x i).sc.delta1 * (Fm.D x i).R.n) *
          ∑ p ∈ largeOrderResiduePrimes (Fm.L x i), Real.log p / p)
        ≤ (4 * Cb * x ^ (-2 : ℝ)) * ((2 * ((Fm.D x i).host.TT.card : ℝ)) * (2 * x ^ (eps / 3))) :=
          mul_le_mul_of_nonneg_left e2 (by positivity)
      _ = _ := by ring
  have hfin : x ^ (-2 : ℝ) * ((16 * Cb) * x ^ (eps / 3)) ≤ x ^ (-2 + eps) := by
    have h3 : (16 * Cb) * x ^ (eps / 3) ≤ x ^ (2 * eps / 3) * x ^ (eps / 3) :=
      mul_le_mul_of_nonneg_right (h2 x b2) hx3
    rw [← Real.rpow_add hx0] at h3
    have h4 : 2 * eps / 3 + eps / 3 = eps := by ring
    rw [h4] at h3
    calc x ^ (-2 : ℝ) * ((16 * Cb) * x ^ (eps / 3)) ≤ x ^ (-2 : ℝ) * x ^ eps := mul_le_mul_of_nonneg_left h3 hx2
      _ = x ^ (-2 + eps) := (Real.rpow_add hx0 _ _).symm
  exact le_trans hB (le_trans step (mul_le_mul_of_nonneg_left hfin hc0))

theorem muRank_of_proviso (Fm : FamP eps) {C0 : ℝ} (crystallineComparison : ℝ) (hC0 : 0 < C0)
    (cPr : ChosenProviso Fm C0) (hN : NuFullF Fm) (h10 : product_first_zeroth_parts.ConclusionOnFamily Fm crystallineComparison) (hS : GlobalTheoryTheory.SettingEventually Fm) :
    J.MuRank Fm := by
  obtain ⟨a3, hP⟩ := cPr
  obtain ⟨a0, hN⟩ := hN
  obtain ⟨a1, h10⟩ := h10
  obtain ⟨a2, hS⟩ := hS
  refine ⟨max (max a0 a1) (max (max a2 a3) (Fm.x1 + 1)), fun x hx i u => ?_⟩
  have b0 : a0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have b1 : a1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have b2 : a2 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have b3 : a3 ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have b4 : Fm.x1 < x := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
    linarith
  have hSet := hS x b2 b4 i u
  have h1 : ((Fm.D x i).div.Nu u).rank = ((Fm.D x i).mem u).A.du := (hN x b0 i).rank u
  rw [h1]
  exact GlobalTheoryTheory.jnt_du_pos _ u (h10 x b1 i u hSet).2.1 (GlobalTheoryTheory.jnt_duS_pos_of_proviso (Fm.L x i) C0 hC0 (hP x b3 i) u)
    (GlobalTheoryTheory.two_lt_level_prime _ u hSet)

end Formalism.MainNotions.Lnk

namespace Formalism.MainNotions

open Formalism.BasicNotions Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory

variable {eps : ℝ}

def LinkGLOBAL7 (Fm : FamP eps) (Cabs CH C0 eD eL : ℝ) : Prop :=
  WeightVectorSmallSharesSeven Fm C0 CH → GlobalTheoremInputs Fm Cabs CH C0 →
    ∃ K cHH eK CL x0 : ℝ, ∀ x ≥ x0, x ∈ Fm.Win → ChainTied Fm eD eL K cHH eK CL x

theorem linkGLOBAL7_pk (Fm : FamP eps) (Cabs CH C0 C3 crystallineComparison C22 : ℝ)
    (hCabs : 0 ≤ Cabs) (hCH : 0 < CH) (hC0 : 1 ≤ C0)
    (s59 : ∀ x : ℝ, Fm.x1 < x → ∀ i : Fm.Ix x, UnusedSlot33.division_rows_rational_lattice (Fm.D x i))
    (s22 : TaylorLogMetric.StatementFamilyConstant Fm C22) (s23 : flipTwoThree.KudlaFamilyStatement Fm) (s24 : StandardLattice.KudlaFamilyStatement Fm C3) (s10 : product_first_zeroth_parts.KudlaFamilyStatement Fm crystallineComparison)
    (hL7 : ChosenTT Fm → ChosenBadp Fm → LinkG Fm → LossesSmallShares Fm)
    (hF3 : StandardLattice.FamilyTheoremThreeAdmitted Fm)
    (tVol : StandardLattice.TiesF Fm)
    (tOm : ∀ x (i : Fm.Ix x), ∃ δ : ℂ, TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice (Fm.D x i) (Fm.D x i).host.ccK δ ∧
      OmLink (Fm.D x i) (TaylorLogMetric.tor0 (Fm.D x i) (Fm.D x i).host.ccK δ))
    (tFree : ∀ x (i : Fm.Ix x), ThFree (Fm.D x i))
    (tTh : ∀ x (i : Fm.Ix x), ExistsTwelfthRootCharacterThetaFamily (Fm.D x i) C22)
    (t7 : flipTwoThree.admF7 Fm)
    (tCV : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u))
    (t10 : ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word), IncidenceTransportConditions (Fm.D x i) u) :
    TuSize Fm → LinkGLOBAL7 Fm Cabs CH C0 Cabs 0 := by
  intro hTu hCh hIn
  obtain ⟨C5, c6, hC5, hc6, cT2, cTT, cBad, cW, cQD, cTh, cPr, cCo⟩ := hCh
  obtain ⟨lG, lS, lI, lD, lMu⟩ := hIn
  have h10 := prvF_of_familyTheorem_ties_eventualIncidenceTransport Fm C3 crystallineComparison C22 s59 s22 s24 s10 hF3 tVol t10
  have tSet : SettingEventually Fm := Formalism.L2.GlobalTheoryTheory.Places.settingF_of Fm hTu
  have hNF : NuFullF Fm := nuFullF_of Fm (nuCommensF_of Fm crystallineComparison h10 tSet)
  have hRank : J.MuRank Fm := muRank_of_proviso Fm crystallineComparison (by linarith) cPr hNF h10 tSet
  have hRR : RRRankF Fm := rrRankF_of Fm Cabs CH C0 (by linarith) lS cPr lI lD
  obtain ⟨C₅, h59a⟩ := UnusedSlot33.field_lemmas_except_seven
  have h59 : UnusedSlot33.ConclusionOnFamily Fm 100 C₅ := fun x hx i => by
    obtain ⟨p1, p2, p3, p4, p5, p5c, p6, p8⟩ := h59a (Fm.D x i) (Fm.L x i).sc
    exact ⟨p1, p2, p3, p4, p5, p5c, p6, s59 x hx i, p8⟩
  have h24 := s24 ⟨hF3, StandardLattice.column_lemma_family_of_definite Fm 100 C₅ h59 (fun _ _ => gram0Def _)⟩ tVol
  have h22 : TaylorLogMetric.ConclusionOnFamily Fm C22 := s22 (fun x i => TaylorLogMetric.first_hypothesis_of_lifting _ (UnusedSlot33.ramification_two_and_conjugation_at_q_and_d _))
  have h4p : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), StandardLattice.Conclusion4p (Fm.D x i) (Fm.ex x hx i).lev :=
    fun x hx i => (h24.2.2.2.2.2.1 x hx i).2.2.2.1
  have hCount : CountF Fm := countF_fam Fm h24.2.2.2.2.2.2.2
  have hDl := dl_of_chosen Fm C5 cQD
  have h23 := s23 ⟨flipTwoThree.theta_norm_family_of_linked Fm C22 h22 tOm, flipTwoThree.theta_condition_family_of_linked Fm C22 tFree tTh,
    flipTwoThree.stabiliser_family_of_column_lemma Fm 100 C₅ h59 h4p,
    flipTwoThree.injectivity_family_of_theorem Fm crystallineComparison h10 tSet, flipTwoThree.norm_bound_family_of_theorem Fm crystallineComparison h10 tSet, t7⟩
  have hSM : SlopesMF Fm := flipTwoThree.slopesMF_of_count_fam Fm h23.2.2.2.2.1 h23.2.2.2.2.2.1 hCount hDl tCV
  have hSN : SlopesNF Fm := slopesNF_of Fm (Formalism.L2.GlobalTheoryTheory.Places.placesF_of Fm crystallineComparison h10 tSet hTu hRank lG lMu)
  have hLat : LatF Fm := latF Fm lD hNF hRank hRR
  have hFr : FrameF Fm CH := frameF_of Fm CH C0 hCH hC0
    (frameRealF_of'' Fm Cabs CH C0 hCH.le lD lI lS cPr hNF hRank hTu (ramRankF_of Fm crystallineComparison h10 tSet)
      (matKF_of Fm Cabs CH C0 (by linarith) lS cPr lD)) hLat cPr cCo hNF
  exact linkCore Fm Cabs CH 0 C5 c6 hCabs hCH.le le_rfl hc6 hCount hSM hSN hLat (nodesF Fm) hFr
    (lossF_of_7 Fm (hL7 cTT cBad lG) cW) (charF Fm) (size_windows_of_thick_density Fm cT2) cTT cQD cTh lI lD

end Formalism.MainNotions

end
