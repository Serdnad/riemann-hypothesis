module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle037
public import CompanionTheory.AutomorphicTheory.BesselWaveGrids.Bundle003
public import CompanionTheory.AutomorphicTheory.BesselWaveGrids.PStarTie
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle053
public import CompanionTheory.AutomorphicTheory.BesselWaveGrids.KDecayOfGap
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle130
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle149
import Formalism.FormalDegreeBessel.Bundle002
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle097
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorVanishesBigCell
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WittOrthonormalBasis
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.Bundle004
public import Formalism.SharpRestriction.CuspSpanNormBounds.SpanMemOfImage
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace CompanionTheory.WaveGrid.Tied

open MeasureTheory Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.L2.SG.Pf.BesselExpansion Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open CompanionTheory.WaveGrid CompanionTheory.WaveGrid.Coef

def ExpBall : Prop :=
  ∀ C : ℝ, 0 ≤ C → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 a₁ : ℕ) (R0 : BranchingSupport.Rep P.k P.r)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (ν₀ : Fin (2 * P.r + P.k + 1) → ℤ),
    BranchingSupport.Num P.k P.r lam P.u b bv ga h q0 → BranchingSupport.Num P.k P.r lam P.u' b bv ga h q0 →
    P.T ≤ b ^ (C * ((2 * P.r + 2 : ℕ) : ℝ)) → P.T' ≤ b ^ (C * ((2 * P.r + 2 : ℕ) : ℝ)) →
    BranchingSupport.n1 ν₀ + (P.r + 1) * a₁ + (P.r + 1) * (P.r + 2) ≤ q0 →
    R0.IsDS (PI.BesselPeriodGGP.eps48 P.k P.r) (fun a => lam a + (ν₀ a : ℝ)) →
    (haveI := FiniteDimensional.complete ℂ Wp; PI.CapelliEig.IsKFinCoefT (k := P.k) (r := P.r) R0.σ f) →
    CutBP.BigCellDerivativeExpansion p f b (C / 2 + 6) a₁

section num

variable {k r : ℕ}

def gapY (k r : ℕ) : ℝ :=
  ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
    (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)

theorem pow_four_le_rpow_nine_halves (r : ℕ) : ((2 * r + 2 : ℕ) : ℝ) ^ 4 ≤ ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) := by
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ 2 * r + 2)) (by norm_num)

theorem thrX_le_gapY (k r : ℕ) : thrX k r ≤ gapY k r := by
  unfold thrX gapY
  have h1 : ((r : ℝ) + 1) ^ 4 ≤ ((2 * r + 2 : ℕ) : ℝ) ^ 4 :=
    pow_le_pow_left₀ (by positivity) (by push_cast; linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]) 4
  have e : ((2 * r + k + 1 : ℕ) : ℝ) = 2 * (r : ℝ) + k + 1 := by push_cast; ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (h1.trans (pow_four_le_rpow_nine_halves r)) (by positivity)

theorem mul_le_gapY (k r : ℕ) : ((2 * r + 2 : ℕ) : ℝ) ^ 4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ gapY k r :=
  mul_le_mul (pow_four_le_rpow_nine_halves r) (le_add_of_nonneg_left (by positivity)) (by positivity) (by positivity)

theorem fourth_power_le_gap (k r : ℕ) : ((2 * r + 2 : ℕ) : ℝ) ^ 4 ≤ gapY k r :=
  le_trans (le_mul_of_one_le_right (by positivity)
    (one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)))) (mul_le_gapY k r)

theorem cube_le_gap (k r : ℕ) : ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ gapY k r :=
  le_trans (le_mul_of_one_le_left (by positivity)
    (one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ 2 * r + 2)))) (mul_le_gapY k r)

theorem hypType_of (hk : 1 ≤ k) {lam : Fin (2 * r + k + 1) → ℝ} {u : Fin k → ℝ} {b : ℝ} (hlam : IsHCParam lam)
    (hu : IsHCParam u) (hI : InterlaceS (by omega) u lam) (hb : ∀ i, |u i| ≤ b) : HypType k r lam (lamN u) b := by
  refine { half := ?_, inter := ?_, u_le := ?_ }
  · intro i h1 h2
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [lamN_succ u ⟨j, by omega⟩]
    exact hu.2 _
  · refine ⟨fun s t hst => hlam.1 (by simpa using hst), fun s => ⟨fun hs => ?_, fun hs => ?_⟩⟩
    · have hs' : (s : ℕ) < k := by simpa using hs
      rw [lamN_succ u ⟨s, hs'⟩]
      by_cases h : (s : ℕ) + 1 < k
      · exact (hI.1 s h).1
      · have e : (s : ℕ) = k - 1 := by omega
        have := hI.2 (by omega)
        simp only [← e] at this
        exact this
    · have hs' : (s : ℕ) + 1 < k := by
        have : (s : ℕ) + 2 ≤ k := by simpa using hs
        omega
      rw [show (s : ℕ) + 2 = (s + 1) + 1 from rfl, lamN_succ u ⟨s + 1, hs'⟩]
      exact (hI.1 s hs').2
  · intro i h1 h2
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [lamN_succ u ⟨j, by omega⟩]
    exact hb _

theorem gap_of_lt {n : ℕ} {lam : Fin n → ℝ} {g : ℝ} (hlam : IsHCParam lam) (hg : AllGaps lam g) {a c : Fin n}
    (h : a < c) : g ≤ lam a - lam c := by
  have h1 := hg a c h.ne
  rwa [abs_of_pos (sub_pos.2 (hlam.1 h))] at h1

theorem shape_of (hk : 1 ≤ k) {lam : Fin (2 * r + k + 1) → ℝ} {u : Fin k → ℝ} {bv : ℝ} (hlam : IsHCParam lam)
    (hu : IsHCParam u) (hI : InterlaceS (by omega) u lam) (hS : ShapeS u lam bv) :
    (∀ a : Fin (2 * r + k + 1), a.val + 1 < k → 0 ≤ lam a ∧ lam a ≤ bv / 8) ∧
      ∀ a : Fin (2 * r + k + 1), k ≤ a.val + 1 → -2 * bv ≤ lam a ∧ lam a ≤ -bv := by
  refine ⟨fun a ha => (hS a).1 ⟨⟨_, (hI.1 a ha).1⟩, ⟨_, (hI.1 a ha).2⟩⟩, fun a ha => (hS a).2 ?_⟩
  rintro ⟨-, i, hi⟩
  have h1 := hI.2 (by omega)
  have h2 : lam a ≤ lam ⟨k - 1, by omega⟩ := hlam.1.antitone (by rw [Fin.le_def]; simp only; omega)
  have h3 : u ⟨k - 1, by omega⟩ ≤ u i := hu.1.antitone (by rw [Fin.le_def]; simp only; omega)
  linarith

theorem scaled_le {T ka b Ch : ℝ} (r : ℕ) (hb : 1 ≤ b) (hka : 0 < ka) (h1 : ka ≤ b ^ Ch)
    (hT : T * (1 / ka) ^ (2 * r) ≤ b ^ (Ch * ((2 * r + 2 : ℕ) : ℝ))) : T ≤ b ^ (2 * |Ch| * ((2 * r + 2 : ℕ) : ℝ)) := by
  have hb0 : 0 < b := by linarith
  have e : T = T * (1 / ka) ^ (2 * r) * ka ^ (2 * r) := by
    rw [mul_assoc, ← mul_pow, one_div, inv_mul_cancel₀ hka.ne', one_pow, mul_one]
  have h2 : ka ^ (2 * r) ≤ b ^ (|Ch| * ((2 * r + 2 : ℕ) : ℝ)) := by
    calc ka ^ (2 * r) ≤ (b ^ |Ch|) ^ (2 * r) :=
          pow_le_pow_left₀ hka.le (h1.trans (Real.rpow_le_rpow_of_exponent_le hb (le_abs_self _))) _
      _ ≤ (b ^ |Ch|) ^ (2 * r + 2) := pow_le_pow_right₀ (Real.one_le_rpow hb (abs_nonneg _)) (by omega)
      _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le]
  have h3 : b ^ (Ch * ((2 * r + 2 : ℕ) : ℝ)) ≤ b ^ (|Ch| * ((2 * r + 2 : ℕ) : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hb (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  calc T = _ := e
    _ ≤ b ^ (|Ch| * ((2 * r + 2 : ℕ) : ℝ)) * b ^ (|Ch| * ((2 * r + 2 : ℕ) : ℝ)) :=
        mul_le_mul (hT.trans h3) h2 (by positivity) (by positivity)
    _ = _ := by rw [← Real.rpow_add hb0]; congr 1; ring

end num


open CompanionTheory.LimBd.Main (ZuckT CoefCC) in
theorem coefCC1_of {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} {Ct : ℝ} (hCt : 0 ≤ Ct)
    (ht : ∀ n ε, 1 ≤ n → t n ε ≤ Ct * (n : ℝ) ^ 3) (hZ : ZuckT t) (hK : PI.KFinSmooth) (hC : CoefCC) :
    CoefCC1 (Ct + |Formalism.MainNotions.BigCellDensity.c3| + 2) := by
  intro k r L f _ hf hgap
  have hfK : CutBP.KFinDSCoef L.ε L.lam f := by
    obtain ⟨Pm, Qm, h1, h2, h3⟩ := hf
    exact ⟨L.Hs, _, _, _, L.σ, Pm, Qm, L.hlam, L.hσ, h1, h2, fun g _ => h3 g⟩
  have hc := abs_nonneg Formalism.MainNotions.BigCellDensity.c3
  have hX := thrX_nonneg k r
  have hY1 := thrX_le_gapY k r
  have hY2 := fourth_power_le_gap k r
  have hY3 := cube_le_gap k r
  have hm : (1 : ℝ) ≤ ((2 * r + 2 : ℕ) : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ 2 * r + 2))
  have h1 := ht (2 * r + k + 1) L.ε (by omega)
  have h2 := mul_le_mul_of_nonneg_left hY3 hCt
  have h3 := mul_le_mul_of_nonneg_left hY1 hc
  have hD := kDecay_of_gap hZ k r L.ε (X := |Formalism.MainNotions.BigCellDensity.c3| * thrX k r) (d := 0)
    (h := (Ct + |Formalism.MainNotions.BigCellDensity.c3| + 2) * gapY k r) (mul_nonneg hc hX) le_rfl (by nlinarith)
  have hg : PI.ZuckTensor.GapAtLeast L.ε L.lam ((Ct + |Formalism.MainNotions.BigCellDensity.c3| + 2) * gapY k r - 2 * 0) := by
    rw [mul_zero, sub_zero, gapY, ← mul_assoc]
    exact hgap
  exact JCx2.sq_inCC_mono (thr_conv k r (le_abs_self _) hc (by linarith)) le_rfl (kfin_inCC hK hC hD hg hfK 1)

end CompanionTheory.WaveGrid.Tied
end
end

section

noncomputable section

namespace CompanionTheory.WaveGrid.Ties

open MeasureTheory Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.L2.SG.Pf.BesselExpansion Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open scoped ENNReal

section energy

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {k r : ℕ}

theorem norm_JF_eq (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (d : Fin (r + 1) → ℂ)
    (hd : ∀ a, d a ≠ 0) {γ γ' : B.Mat k r} (hγ : γ ∈ B.GV k r) (hγ' : γ' ∈ B.GV k r)
    (hZ : Zhat k r Bs.z Bs.z' γ = D.ptMatN (PBJ.bigPt d) (r + 1))
    (hZ' : Zhat k r Bs.z Bs.z' γ' = D.ptMatN (PBJ.bigPt d) (r + 1)) (hpos : 0 < Gf k r Bs.z Bs.z' γ) :
    ‖B.hsVec (B.JF Bs F γ)‖ = ‖B.hsVec (B.JF Bs F γ')‖ := by
  have hl : D.IsLocPt (PBJ.bigPt d) (r + 1) := PBJ.Dens.isLocPt_bigPt d hd
  have hpos' : 0 < Gf k r Bs.z Bs.z' γ' := by
    rw [← ptG_spec k r _ _ (PBJ.bigPt d) _ hl hZ', ptG_spec k r _ _ (PBJ.bigPt d) _ hl hZ]
    exact hpos
  obtain ⟨s, hs, s', hs', hγs⟩ := fibre_orbit_description k r Bs.z Bs.z'
    ⟨Bs.k_pos, Dx2.VV.std_vector_z Bs, Dx2.VV.std_vector_z_prime Bs⟩ _ hγ _ hγ' hpos (hZ.trans hZ'.symm)
  obtain ⟨hA, hhA, nA, hnA, hfA, rfl⟩ := Dx2.VV.stabilizer_decomp_unitary_mul_unipotent (Dx2.VV.std_vector_z Bs) hs
  obtain ⟨hB, hhB, nB, hnB, hfB, rfl⟩ := Dx2.VV.stabilizer_decomp_unitary_mul_unipotent (Dx2.VV.std_vector_z_prime Bs) hs'
  have hlaw := Dx2.VV.orbJ_pt Bs (PBJ.bigPt d) hl hγ hZ hpos hhA hnA hfA hhB hnB hfB F
  rw [← hγs] at hlaw
  have hw : (hl.2 ▸ D.ptPerm (PBJ.bigPt d) : Equiv.Perm (Fin (r + 1))) = 1 :=
    PBM.cast_perm_eq_one _ _ (PBM.ptPerm_bigPt d hd)
  obtain ⟨hmono, hnz⟩ := Dx2.VV.ptMatN_monoP' (PBJ.bigPt d) (r + 1) hl.2 hl.1
  rw [hw] at hmono hlaw
  rw [PBM.orbJ_one_eq Bs hγ' hpos' hnz (hZ'.trans hmono) F, PBM.orbJ_one_eq Bs hγ hpos hnz (hZ.trans hmono) F] at hlaw
  rw [← hlaw, CutBP.hsVec_norm_CinL Bs hhA hhB]

theorem normSq_sec (hk : 2 ≤ k) (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hsec : IsSection k r Bs.z Bs.z' μsec) :
    B.normSq Bs F = jNormSq k r (Tz k r Bs.z) (Tz k r Bs.z')
      fun q => Real.sqrt (hsNormSq (B.JF Bs F (bigCell k r q.1 (μsec q.2)))) := by
  unfold B.normSq jNormSq
  refine lintegral_congr fun q => ?_
  by_cases hw0 : bcWeight k r (Tz k r Bs.z) (Tz k r Bs.z') q = 0
  · rw [hw0, zero_mul, zero_mul]
  obtain ⟨hc, hζ⟩ := Formalism.MainNotions.S.Pv.LemmaJ.bcWeight_ne hk hw0
  have hζ0 : q.2 ≠ 0 := by
    intro h
    rw [h, map_zero] at hζ
    exact absurd (mul_pos Bs.T_pos Bs.T'_pos) (not_lt.2 hζ.le)
  obtain ⟨d, hd1, hd2⟩ : ∃ d : Fin (r + 1) → ℂ, (fun i : Fin r => d i.castSucc) = q.1 ∧ d (Fin.last r) = q.2 :=
    ⟨Fin.snoc q.1 q.2, by funext i; simp, by simp⟩
  have hd : ∀ a, d a ≠ 0 := fun a => by
    refine Fin.lastCases ?_ (fun i => ?_) a
    · rw [hd2]; exact hζ0
    · rw [congrFun hd1 i]; exact hc i
  have hZ := PBM.zhat_bigCell_pt Bs d (by rw [hd2]; exact hζ)
  have hZ' := PBM.zhat_bigCell_pt { Bs with μsec := μsec, sec := hsec } d (by rw [hd2]; exact hζ)
  rw [hd1, hd2] at hZ hZ'
  have e := norm_JF_eq Bs F d hd (bigCellMem k r _ _ hc (Bs.sec.2 _ hζ).1) (bigCellMem k r _ _ hc (hsec.2 _ hζ).1) hZ hZ'
    (Formalism.MainNotions.S.Pv.LemmaJ.Gf_big Bs.z_mem Bs.z'_mem Bs.sec q.1 hc q.2 hζ)
  congr 2
  rw [Real.norm_eq_abs, sq_abs, Real.sq_sqrt (Formalism.MainNotions.BesselShellMomentBounds.hsNormSq_nonneg _), Formalism.MainNotions.BesselShellMomentBounds.hsNormSq_eq]
  change ‖B.hsVec (B.JF Bs F (bigCell k r q.1 (Bs.μsec q.2)))‖ ^ 2 = _
  rw [e, PiLp.norm_sq_eq_of_L2]
  rfl

end energy

theorem energy_identity : EnergyTie := by
  intro k r L f μsec u u' p _ hc _ _ htie _ _ hsec
  obtain ⟨hz, hz', hπ, hπ', hW, hN, hW'⟩ := htie
  have e : TBB.jN2 p f = jNorm2 L f μsec := by
    refine (GlobalTheory.T.jN2_eq_normSq_base (parOfL L u u') L.Wp L.Wq p f).trans ?_
    have h := normSq_sec (k := k) (r := r) p.hl.2.2 p.T.base f μsec (by
      have e1 : (p.T.base.z : Fin (2 * r + k + 1) → ℂ) = L.z := hz
      have e2 : (p.T.base.z' : Fin (2 * r + k + 1) → ℂ) = L.z' := hz'
      exact e1 ▸ e2 ▸ hsec)
    refine h.trans ?_
    unfold jNorm2 LocBessel.J B.JF
    rw [hc]
    simp only [hz, hz', hπ, hπ', hW, hN, hW']
  rw [e]
  refine le_mul_of_one_le_left' ?_
  rw [ENNReal.one_le_ofReal]
  exact one_le_pow₀ (by linarith [Real.pi_gt_three])

section scale

variable {k r : ℕ}

@[reducible] def withN (L : LocBessel k r) (κ : ℝ≥0∞) : LocBessel k r := { L with κN := κ }

theorem pairMeas_smul (L : LocBessel k r) (κ s : ℝ≥0∞) (h : L.μN = s • (withN L κ).μN) :
    pairMeas L = (s * s) • pairMeas (withN L κ) := by
  have i1 : SFinite (withN L κ).μN := Formalism.MainNotions.FrameBoundFromBesselTorus.sFinite_haarLie _ _
  have i2 : SigmaFinite L.μW := L.hμW.1.1
  have i3 : SigmaFinite L.μW' := L.hμW'.1.1
  unfold pairMeas
  rw [h]
  change (L.μW.prod (s • (withN L κ).μN)).prod (L.μW'.prod (s • (withN L κ).μN)) =
    (s * s) • (L.μW.prod (withN L κ).μN).prod (L.μW'.prod (withN L κ).μN)
  rw [Measure.prod_smul_right, Measure.prod_smul_right, Measure.prod_smul_right, Measure.prod_smul_left, smul_smul]

theorem orbSq_le (L : LocBessel k r) (κ s : ℝ≥0∞) (hs0 : s ≠ 0) (hs : s ≠ ⊤)
    (h : pairMeas L = s • pairMeas (withN L κ)) (f : Mx k r → (L.Wq →L[ℂ] L.Wp)) (γ : Point ℂ (r + 1)) :
    orbSq L f γ ≤ ENNReal.ofReal (s.toReal ^ 2) * orbSq (withN L κ) f γ := by
  unfold orbSq
  refine iSup_le fun g => iSup_le fun μR => iSup_le fun ν => iSup_le fun hc => ?_
  have hq : IsOrbQuot (withN L κ) g μR (s⁻¹ • ν) := by
    intro φ hφ
    have e := hc.2.2.2 φ hφ
    rw [h, lintegral_smul_measure] at e
    rw [lintegral_smul_measure, ← e, smul_eq_mul, smul_eq_mul, ← mul_assoc, ENNReal.inv_mul_cancel hs0 hs, one_mul]
  have e : OrbInt L f g ν = ((s.toReal : ℝ) : ℂ) • OrbInt (withN L κ) f g (s⁻¹ • ν) := by
    have e1 : ν = s • (s⁻¹ • ν) := by rw [smul_smul, ENNReal.mul_inv_cancel hs0 hs, one_smul]
    unfold OrbInt
    conv_lhs => rw [e1, integral_smul_measure]
    rw [Complex.coe_smul]
    rfl
  rw [e, Formalism.MainNotions.BesselShellMomentBounds.hsNormSq_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs, ENNReal.ofReal_mul (by positivity)]
  refine mul_le_mul' le_rfl ?_
  exact le_iSup_of_le g (le_iSup_of_le μR (le_iSup_of_le (s⁻¹ • ν) (le_iSup_of_le ⟨hc.1, hc.2.1, hc.2.2.1, hq⟩ le_rfl)))

theorem jNorm2_eq (L : LocBessel k r) (κ s : ℝ≥0∞) (h : pairMeas L = s • pairMeas (withN L κ))
    (f : Mx k r → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    jNorm2 L f μsec = ENNReal.ofReal (s.toReal ^ 2) * jNorm2 (withN L κ) f μsec := by
  have hJ : ∀ g, L.J f g = ((s.toReal : ℝ) : ℂ) • (withN L κ).J f g := fun g => by
    change ∫ x, besselIntg L f g x ∂(pairMeas L) = _ • ∫ x, besselIntg L f g x ∂(pairMeas (withN L κ))
    rw [h, integral_smul_measure, Complex.coe_smul]
  rw [Formalism.MainNotions.BesselShellMomentBounds.jNorm2_eq, Formalism.MainNotions.BesselShellMomentBounds.jNorm2_eq, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun q => ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  unfold Formalism.MainNotions.BesselShellMomentBounds.dens
  rw [hJ, Formalism.MainNotions.BesselShellMomentBounds.hsNormSq_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  change _ = _ * (bcWeight k r (Tz k r L.z) (Tz k r L.z') q * _)
  ring

end scale

end CompanionTheory.WaveGrid.Ties
end
end
