module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LoopsCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle020
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle030
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgePlace
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepPtRepPfA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeNC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierBase
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTieOf
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LoopTieOf Formalism.L2.SG.LoopsCut Formalism.FourierDecayAlt

namespace Formalism.L2.SG.LoopsEv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section One

variable {D : D7} {large₂ : SizeData₂ D} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

theorem loopsAmp_at {C' Cl Cg cb Cw cT CT C0 A C K₀ A₀ : ℝ}
    (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cw cT CT C0 A) (hT : ConcTie X Y) (hA : (Y.tO u u').AbsConv)
    (hC : 1 ≤ C) (hCT : CT ≤ C) (hK₀ : K₀ ≤ C') (hA₀1 : 1 ≤ A₀) (hCl4 : 4 ≤ Cl)
    (hClA : 3 + 6 * Real.log (3 * A₀) ≤ Cl)
    (hXiH : Formalism.HermitianLatticeCounting.LatticeSumBounds.XiHyp C D.R.k (2 * D.R.rS + 2) D.R.f large₂.sc.b D.host.v (NT D u)
      (Formalism.MainNotions.BridgeLemma.XiB D large₂ u C))
    (HS : ∀ s, 2 ≤ s → s ≤ D.R.k → ClassLe (Y.tO u u') (bigS (Y.tO u u') s)
      (A₀ * rowS C D.R.k D.R.rS D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v (GamS D large₂)
        (Formalism.MainNotions.BridgeLemma.XiB D large₂ u C) * ddC X Y u u'))
    (H1 : ClassLe (Y.tO u u') ((Y.tO u u').nsc (Y.tO u u').genSet)
      (A₀ * oneT C D.R.k D.R.rS D.R.f large₂.sc.b (X.B.g : ℝ) (GamS D large₂) * ddC X Y u u')) :
    ∃ (Al NT' Gam : ℝ) (Xi : ℕ → ℝ), 1 ≤ Al ∧
      Formalism.HermitianLatticeCounting.LatticeSumBounds.Params C K₀ D.R.k (2 * D.R.rS + 2) D.R.f large₂.sc.b (X.B.g : ℝ) D.host.v NT' Gam ∧
      Formalism.HermitianLatticeCounting.LatticeSumBounds.XiHyp C D.R.k (2 * D.R.rS + 2) D.R.f large₂.sc.b D.host.v NT' Xi ∧
      6 * Real.log (3 * Al) ≤ (D.R.k : ℝ) * D.R.f * Real.log D.R.k ∧
      Formalism.L2.SG.RowsOther.LoopsAmp (Y.tO u u') Al C D.R.k D.R.rS D.R.f large₂.sc.b (X.B.g : ℝ) D.host.v Gam Xi
        (ddC X Y u u') := by
  have hP := params_at hH.1 X u hCl4 hCT hC hK₀
  obtain ⟨hn1, hn2, hn3⟩ := hyp_nums hH.1
  have hL := Formalism.MainNotions.BridgeLemma.d_one_le_L D large₂
  have hM := unitM_nonneg D large₂
  have hCG := large₂.CGam_pos
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = GamS D large₂ / gamCap D large₂ C := ⟨_, rfl⟩
  have hρe : ρ = Real.exp ((large₂.CGam - min large₂.CGam C) * unitM D large₂) := by rw [hρ, gam_ratio]
  have hmin0 : 0 ≤ min large₂.CGam C := le_min hCG.le (by linarith)
  have hlogρ : Real.log ρ ≤ (D.R.k : ℝ) / 8 := by
    rw [hρe, Real.log_exp]
    have e1 : (large₂.CGam - min large₂.CGam C) * unitM D large₂ ≤ large₂.CGam * unitM D large₂ :=
      mul_le_mul_of_nonneg_right (by linarith) hM
    linarith
  have hρ1 : 1 ≤ ρ := by
    rw [hρe]; exact Real.one_le_exp (mul_nonneg (by linarith [min_le_left large₂.CGam C]) hM)
  have hρ0 : 0 ≤ ρ := by linarith
  have hGr : GamS D large₂ = ρ * gamCap D large₂ C := by
    rw [hρ]; field_simp [(gamCap_pos D large₂ C).ne']
  have hdd := dd_nonneg hT u u'
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hb := Formalism.MainNotions.BridgeLemma.d_two_le_b D large₂
  have hb0 : (0 : ℝ) < large₂.sc.b := by linarith
  have hg : 0 < (X.B.g : ℝ) := by
    have h5 : ((D.R.k : ℝ) * large₂.sc.b) ^ 8 ≤ (X.B.g : ℝ) := hP.2.2.2.2.1
    have h8 : 0 < ((D.R.k : ℝ) * large₂.sc.b) ^ 8 := by positivity
    linarith
  have hv : 0 ≤ D.host.v := by linarith [hP.2.2.2.2.2.2.1]
  have hC0 : (0 : ℝ) ≤ C := by linarith
  have hGc0 : 0 ≤ gamCap D large₂ C := (gamCap_pos D large₂ C).le
  refine ⟨A₀ * ρ ^ 3, NT D u, gamCap D large₂ C, Formalism.MainNotions.BridgeLemma.XiB D large₂ u C,
    one_le_mul_of_one_le_of_one_le hA₀1 (one_le_pow₀ hρ1), hP, hXiH,
    log_size hk1 hL hn3 hn2 hClA hA₀1 hρ1 hlogρ, ?_⟩
  refine loopsAmp_of_classes (Y.tO u u') (A₀ * ρ ^ 3) C D.R.k D.R.rS D.R.f large₂.sc.b (X.B.g : ℝ) D.host.v
    (gamCap D large₂ C) (Formalism.MainNotions.BridgeLemma.XiB D large₂ u C) (ddC X Y u u') hA.2.2.le hA.2.1 (corank_le_k Y u u') ?_ ?_
  · intro s hs2 hsk
    have hB := HS s hs2 hsk
    rw [hGr] at hB
    have hX0 := xi_nonneg hXiH s hs2 hsk
    have hnd : 0 ≤ Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow C D.R.k (2 * D.R.rS + 2) D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v
        (gamCap D large₂ C) (Formalism.MainNotions.BridgeLemma.XiB D large₂ u C) := ndRow_nonneg hC0 hb0 hg hv hGc0 hX0
    have hdg : 0 ≤ Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow C D.R.k (2 * D.R.rS + 2) D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v
        (gamCap D large₂ C) (Formalism.MainNotions.BridgeLemma.XiB D large₂ u C) := degRow_nonneg hC0 hb0 hg hv hGc0 hX0
    have hsc := rowS_scale C D.R.k D.R.rS D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v (gamCap D large₂ C) ρ
      (Formalism.MainNotions.BridgeLemma.XiB D large₂ u C) hρ1 hnd
    have hrow0 : 0 ≤ rowS C D.R.k D.R.rS D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v (gamCap D large₂ C)
        (Formalism.MainNotions.BridgeLemma.XiB D large₂ u C) := by
      unfold rowS; exact add_nonneg hnd (mul_nonneg (sq_nonneg _) hdg)
    exact le_trans hB (scale_le hA₀1 le_rfl hdd hsc hrow0 hρ0)
  · have hB := H1
    rw [hGr] at hB
    have h0 : 0 ≤ oneT C D.R.k D.R.rS D.R.f large₂.sc.b (X.B.g : ℝ) (gamCap D large₂ C) := oneT_nonneg hC0 hb0 hGc0
    have hsc := oneT_scale C D.R.k D.R.rS D.R.f large₂.sc.b (X.B.g : ℝ) (gamCap D large₂ C) ρ hρ1 h0
    exact le_trans hB (scale_le hA₀1 le_rfl hdd hsc h0 hρ0)

end One

section Fam

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ) (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Yt : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (At x hx i) u u' C1)
  (Cc : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ConcAt (Fm.D x i) (At x hx i))

end Fam

end Formalism.L2.SG.LoopsEv
end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.LocWSOf
open scoped ENNReal

namespace Formalism.L2.SG.Pf.JointAmplitudePoints

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Pt

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (u u' : D.what₂.Word)

def gamP (w : Point D.host.E (D.R.rS + 1)) (τ : D.what₂.Tau) : MatKR D.R.k D.R.rS :=
  Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) ((Formalism.L2.SG.RealObj.gamW X u u' w) (vOf X τ))

def nu1P (w : Point D.host.E (D.R.rS + 1)) (τ : D.what₂.Tau) : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) :=
  if h : ∃ ν, RMeas D (locW C u u' τ) (gamP C u u' w τ) 1 ν then h.choose else 0

variable {C} (hB : WuBessel C)

def localAmplitudeProduct (w : Point D.host.E (D.R.rS + 1)) : ℝ :=
  ∏ τ, hsNormSq ((locS hB u u' τ).J (nu1P C u u' w τ) (gamP C u u' w τ))

def thetaP (J2 : ℝ) (w : Point D.host.E (D.R.rS + 1)) : ℝ :=
  if 0 < J2 ∧ 0 < localAmplitudeProduct u u' hB w then
    (localAmplitudeProduct u u' hB w / J2) ^ ((1 : ℝ) / (2 * Fintype.card D.what₂.Tau))
  else 1

end Pt

section Stmts

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word) (ν : X.B.I.Ginf → Measure X.B.I.Ginf)
  {θ : ℝ} (C : Choice X θ) (hB : WuBessel C)

def RMeasExP : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u').A.T w →
    (∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) → ∀ τ, ∃ ν₁, RMeas D (locW C u u' τ) (gamP C u u' w τ) 1 ν₁

def LocalAmplitudesPositive : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u').A.T w →
    0 < J2of Y u u' ν (toPts w) → 0 < localAmplitudeProduct u u' hB w

def ThetaWinP (large₂ : SizeData₂ D) (C1 : ℝ) : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u').A.T w →
    0 < J2of Y u u' ν (toPts w) → normWin D large₂ C1 (thetaP u u' hB (J2of Y u u' ν (toPts w)) w)

end Stmts

section Proof

variable {D : D7} {X : HidaSetting D}

theorem card_pos' (D : D7) : 0 < Fintype.card D.what₂.Tau := by
  first
  | (haveI : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩; exact Fintype.card_pos)
  | (haveI : Nonempty D.what₂.Tau := ⟨D.eTau.symm ⟨1, one_mem _⟩⟩; exact Fintype.card_pos)

def ofPts {K : Type} {i : ℕ} (s : Σ c : Composition (i + 1), (Fin c.length → K)) : List (K × ℕ) :=
  List.ofFn fun a => (s.2 a, s.1.blocksFun a)

theorem ofPts_toPts {K : Type} [Zero K] {i : ℕ} (p : Point K (i + 1)) : ofPts (toPts p) = p.1 := by
  first
  | (apply List.ext_getElem <;> simp [ofPts, toPts, Composition.blocksFun, Composition.length])
  | (apply List.ext_get <;> simp [ofPts, toPts, Composition.blocksFun, Composition.length])

theorem toPts_injective {K : Type} [Zero K] {i : ℕ} :
    Function.Injective (toPts : Point K (i + 1) → Σ c : Composition (i + 1), (Fin c.length → K)) := by
  intro p q h
  have h' := congrArg ofPts h
  rw [ofPts_toPts, ofPts_toPts] at h'
  exact Subtype.ext h'

theorem isPtRep_of_J2of {Y : Full X} {u u' : D.what₂.Word} {ν : X.B.I.Ginf → Measure X.B.I.Ginf}
    {w : Point D.host.E (D.R.rS + 1)} (h : 0 < J2of Y u u' ν (toPts w)) :
    ∃ w' : Point D.host.E (D.R.rS + 1), toPts w' = toPts w ∧ ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w' g := by
  unfold J2of at h
  split_ifs at h with hc
  · exact hc
  · exact absurd h (lt_irrefl 0)

end Proof

end Formalism.L2.SG.Pf.JointAmplitudePoints
end
end

section

noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.Bridge

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting
open Formalism.L2.SG.RealObj.InfCut

section RelGen

theorem mulVec_single_apply {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m) :
    (M *ᵥ Pi.single j (1 : ℂ)) i = M i j := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

variable {n : ℕ} {ε : Fin n → Bool} {r k : ℕ} {F : PtRepPf.Fr ε r k}
  {Qm : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ} {Qim : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} {c : Fin r → ℂ}

theorem herm_smul_right' (H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (v w : Fin (2 * r + k + 1) → ℂ)
    (s : ℂ) : Formalism.QuantumDeterminants.herm H v (s • w) = star s * Formalism.QuantumDeterminants.herm H v w := by
  unfold Formalism.QuantumDeterminants.herm
  rw [star_smul, smul_dotProduct, smul_eq_mul]

theorem hJ_fd_Q (hT : TrHyp F Qm Qim c) (a : Fin r) (v : Fin (2 * r + k + 1) → ℂ) :
    hJ ε (F.fd a) (Qm *ᵥ v) = c a * v (Formalism.QuantumDeterminants.eI k r a) := by
  have e1 : F.fd a = Qm *ᵥ (Qim *ᵥ F.fd a) := by rw [Matrix.mulVec_mulVec, hT.h2, Matrix.one_mulVec]
  rw [e1, ← herm_Q hT, Qi_f hT, herm_smul_right', star_star, Formalism.L2.SG.Pf.CarrierBase.herm_bvec,
    Formalism.L2.SG.Pf.CarrierBase.hpk_mulVec_esI]

theorem rootCoord_Q (hT : TrHyp F Qm Qim c) {κ : ℂ} (hc : ∀ a : Fin r, c a = κ ^ (r - a.val)) (hκ0 : κ ≠ 0)
    (ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a : Fin r) :
    rootCoord ε F.e F.fd F.z (Qm * ρ * Qim) a =
      κ * (if h : a.val + 1 < r then ρ (Formalism.QuantumDeterminants.eI k r a) (Formalism.QuantumDeterminants.eI k r ⟨a.val + 1, h⟩)
        else (ρ *ᵥ (Qim *ᵥ F.z)) (Formalism.QuantumDeterminants.eI k r a)) := by
  unfold rootCoord nxt
  by_cases h : a.val + 1 < r
  · rw [dite_eq_left h, dite_eq_left h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Qi_e hT, Matrix.mulVec_smul,
      Matrix.mulVec_smul, PtRepPf.hJ_smul_right, hJ_fd_Q hT, hc, hc]
    unfold Formalism.QuantumDeterminants.bvec
    rw [mulVec_single_apply]
    have he : r - a.val = (r - (a.val + 1)) + 1 := by omega
    simp only
    rw [he, pow_succ]
    field_simp
  · rw [dite_eq_right h, dite_eq_right h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hJ_fd_Q hT, hc]
    have he : r - a.val = 1 := by have := a.2; omega
    rw [he, pow_one]

theorem sum_rootCoord (hT : TrHyp F Qm Qim c) {κ : ℂ} (hc : ∀ a : Fin r, c a = κ ^ (r - a.val)) (hκ0 : κ ≠ 0)
    (ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ∑ a, rootCoord ε F.e F.fd F.z (Qm * ρ * Qim) a = κ * Formalism.QuantumDeterminants.ell k r (Qim *ᵥ F.z) ρ := by
  simp only [rootCoord_Q hT hc hκ0, ← Finset.mul_sum]
  rfl

theorem psiR_Q (hT : TrHyp F Qm Qim c) (gg : ℕ) (hgg : 0 < gg) {κ : ℂ} (hc : ∀ a : Fin r, c a = κ ^ (r - a.val))
    (hκ : κ = -Complex.I * (((gg : ℝ) / (2 * Real.pi) : ℝ) : ℂ)) (ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    psiR ε gg F.e F.fd F.z (Qm * ρ * Qim) = Formalism.QuantumDeterminants.psi k r (Qim *ᵥ F.z) Formalism.QuantumDeterminants.cStd ρ := by
  have hg : (0 : ℝ) < gg := by exact_mod_cast hgg
  have hκ0 : κ ≠ 0 := by
    rw [hκ]
    refine mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) ?_
    have : (0 : ℝ) < (gg : ℝ) / (2 * Real.pi) := div_pos hg (by positivity)
    exact_mod_cast this.ne'
  unfold psiR Formalism.QuantumDeterminants.psi
  congr 1
  rw [Finset.sum_add_distrib, ← star_sum, sum_rootCoord hT hc hκ0]
  set ℓ := Formalism.QuantumDeterminants.ell k r (Qim *ᵥ F.z) ρ
  rw [show star (κ * ℓ) = (starRingEnd ℂ) (κ * ℓ) from rfl, Complex.add_conj]
  rw [hκ]
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, Formalism.QuantumDeterminants.cStd, Complex.div_re, Complex.div_im] <;>
    field_simp <;> ring

theorem psiR_conj {H Hi g : Matrix (Fin n) (Fin n) ℂ} (hH : Hᴴ * Formalism.REAL.Jm ε * H = Formalism.REAL.Jm ε)
    (hiH : Hi * H = 1) (hHe : ∀ a, H *ᵥ F.e a = F.e a) (hHf : ∀ a, H *ᵥ F.fd a = F.fd a) (hHz : H *ᵥ F.z = F.z)
    (gg : ℕ) : psiR ε gg F.e F.fd F.z (H * g * Hi) = psiR ε gg F.e F.fd F.z g := by
  have hHi : ∀ x, H *ᵥ x = x → Hi *ᵥ x = x := fun x hx => by
    conv_lhs => rw [← hx]
    rw [Matrix.mulVec_mulVec, hiH, Matrix.one_mulVec]
  have hrc : ∀ a, rootCoord ε F.e F.fd F.z (H * g * Hi) a = rootCoord ε F.e F.fd F.z g a := by
    intro a
    unfold rootCoord
    have hn : H *ᵥ nxt F.e F.z a = nxt F.e F.z a := by
      unfold nxt; split_ifs; · exact hHe _
      · exact hHz
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hHi _ hn, fixed_left hH (hHf a)]
  unfold psiR
  simp only [hrc]

theorem spanLt_map {H : Matrix (Fin n) (Fin n) ℂ} (hHe : ∀ a, H *ᵥ F.e a = F.e a) (m : ℕ) {x : Fin n → ℂ}
    (hx : x ∈ spanLt F.e m) : H *ᵥ x ∈ spanLt F.e m := by
  have hle : spanLt F.e m ≤ (spanLt F.e m).comap (Matrix.mulVecLin H) := by
    unfold spanLt
    rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply, hHe]
    exact Submodule.subset_span ⟨b, hb, rfl⟩
  exact hle hx

theorem span_range_le (hT : TrHyp F Qm Qim c) : Submodule.span ℂ (Set.range F.e) ≤ spanLt F.e r := by
  rw [Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  exact Submodule.subset_span ⟨a, a.2, rfl⟩

theorem inN_Q (hT : TrHyp F Qm Qim c) {ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hρ : ρ ∈ Formalism.QuantumDeterminants.Nset k r) : InN ε F.e F.z (Qm * ρ * Qim) := by
  have hsub : ∀ x, (Qm * ρ * Qim - 1) *ᵥ x = Qm *ᵥ ((ρ - 1) *ᵥ (Qim *ᵥ x)) := fun x => by
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.one_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ Qm Qim, hT.h2, Matrix.one_mulVec]
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
  · rw [hsub, Qi_e hT, Matrix.mulVec_smul, Matrix.mulVec_smul]
    refine Submodule.smul_mem _ _ ?_
    set v := (ρ - 1) *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) with hv
    have hva : ∀ i : Fin (2 * r + k + 1), a.val ≤ i.val → v i = 0 := by
      intro i hi
      rw [hv, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply]
      unfold Formalism.QuantumDeterminants.bvec
      rw [mulVec_single_apply, hρ.2.1 a i hi, sub_eq_zero]
      simp [Pi.single_apply]
    have hvX : IsXv v := fun i hi => hva i (by have := a.2; omega)
    rw [isXv_eq v hvX, Matrix.mulVec_sum]
    refine Submodule.sum_mem _ fun b _ => ?_
    by_cases hb : b.val < a.val
    · rw [Matrix.mulVec_smul, hT.he, smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
    · rw [hva _ (by simp only [Formalism.QuantumDeterminants.eI]; omega), zero_smul, Matrix.mulVec_zero]
      exact Submodule.zero_mem _
  · rw [hsub]
    exact span_range_le hT (Q_X hT _ (N_sub_X hρ _ (Qi_noXs hT F.z F.ez)))
  · rw [hsub]
    exact span_range_le hT (Q_X hT _ (N_sub_X hρ _ (Qi_noXs hT y hy)))

theorem inN_conj {H Hi g : Matrix (Fin n) (Fin n) ℂ} (hH : Hᴴ * Formalism.REAL.Jm ε * H = Formalism.REAL.Jm ε)
    (hHi : H * Hi = 1) (hiH : Hi * H = 1) (hHe : ∀ a, H *ᵥ F.e a = F.e a) (hHz : H *ᵥ F.z = F.z)
    (hg : InN ε F.e F.z g) : InN ε F.e F.z (H * g * Hi) := by
  have hHi' : ∀ x, H *ᵥ x = x → Hi *ᵥ x = x := fun x hx => by
    conv_lhs => rw [← hx]
    rw [Matrix.mulVec_mulVec, hiH, Matrix.one_mulVec]
  have hsub : ∀ x, (H * g * Hi - 1) *ᵥ x = H *ᵥ ((g - 1) *ᵥ (Hi *ᵥ x)) := fun x => by
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.one_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ H Hi, hHi, Matrix.one_mulVec]
  obtain ⟨⟨h1, h2⟩, h3⟩ := hg
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
  · rw [hsub, hHi' _ (hHe a)]; exact spanLt_map hHe _ (h1 a)
  · rw [hsub, hHi' _ hHz]; exact spanLt_map hHe _ h2
  · rw [hsub]
    refine spanLt_map hHe _ (h3 _ fun a => ?_)
    rw [← fixed_left hH (hHe a), Matrix.mulVec_mulVec, hHi, Matrix.one_mulVec, hy a]

end RelGen

end Formalism.L2.SG.Pf.Bridge
end
end

section

noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.Carrier

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting
open Formalism.L2.SG.RealObj.InfCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

section UMat

variable {n : ℕ} {ε : Fin n → Bool}

theorem uMat_inv_mul (a : Formalism.REAL.UJ ε) : Formalism.MainNotions.S.uMat a⁻¹ * Formalism.MainNotions.S.uMat a = 1 := by
  simp [Formalism.MainNotions.S.uMat]

theorem uMat_mul_inv (a : Formalism.REAL.UJ ε) : Formalism.MainNotions.S.uMat a * Formalism.MainNotions.S.uMat a⁻¹ = 1 := by
  simp [Formalism.MainNotions.S.uMat]

theorem uMat_unitary (a : Formalism.REAL.UJ ε) :
    (Formalism.MainNotions.S.uMat a)ᴴ * Formalism.REAL.Jm ε * Formalism.MainNotions.S.uMat a = Formalism.REAL.Jm ε := a.2

end UMat

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)

theorem dFrameBridge_carrierOf (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ)
    (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ) (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (T : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.D.LevTower D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (hT : ∀ j, Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z = ((D.mem u).A.T : ℝ) ∧
      Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z' = ((D.mem u').A.T : ℝ))
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (χ : ℝ → ℝ) (sg : Fin (nfE D) → ℂ) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (top : ∀ j : Fin (nfE D), (Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j))) →
      List Formalism.FourierDecayAlt.C.Letter → Formalism.FourierDecayAlt.C.LPt → Formalism.FourierDecayAlt.C.LPt → ℂ) (A₀ : ℝ)
    (Mo : ModelsFor (sOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀)))
    (sc : ℝ) (hsc : sc ≠ 0) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) :
    (CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo).DFrameBridge
      sc i0 i0' := by
  intro hFX hB γ h h' hDX v
  obtain ⟨hHu, hH'u, hDv⟩ := hDX
  obtain ⟨hQ, hz, hz', -⟩ := hFX v
  obtain ⟨hi, hν, hm⟩ := hB v
  have hTr : Bridge.TrHyp (PtRepPf.frU X u v) (Formalism.L2.SG.LocWSOf.Qcs C (X.pl v)) (Formalism.L2.SG.LocWSOf.Qics C (X.pl v))
      (fun a => cTor ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) D.R.rS a) :=
    ⟨hQ.1, hQ.2.1, hQ.2.2.1, fun a => (hQ.2.2.2 a a rfl).1, fun a => (hQ.2.2.2 a a rfl).2⟩
  have hTr' : Bridge.TrHyp (PtRepPf.frU X u' v) (Formalism.L2.SG.LocWSOf.Qcs C (X.pl v))
      (Formalism.L2.SG.LocWSOf.Qics C (X.pl v)) (fun a => cTor ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) D.R.rS a) :=
    ⟨hQ.1, hQ.2.1, hQ.2.2.1, fun a => (hQ.2.2.2 a a rfl).1, fun a => (hQ.2.2.2 a a rfl).2⟩
  have hfix : ∀ (w : D.what₂.Word) (s : X.B.I.Ginf), s ∈ HsetU X w →
      (∀ a, Formalism.MainNotions.S.uMat (s v) *ᵥ (PtRepPf.frU X w v).e a = (PtRepPf.frU X w v).e a) ∧
      (∀ a, Formalism.MainNotions.S.uMat (s v) *ᵥ (PtRepPf.frU X w v).fd a = (PtRepPf.frU X w v).fd a) ∧
      Formalism.MainNotions.S.uMat (s v) *ᵥ (PtRepPf.frU X w v).z = (PtRepPf.frU X w v).z := by
    intro w s hs
    refine ⟨fun a => hs v _ ?_, fun a => hs v _ ?_, hs v _ ?_⟩
    · exact Or.inl (Or.inl ⟨a, rfl⟩)
    · exact Or.inl (Or.inr ⟨a, rfl⟩)
    · exact Or.inr rfl
  obtain ⟨hHe, hHf, hHz⟩ := hfix u h hHu
  obtain ⟨hH'e, hH'f, hH'z⟩ := hfix u' h' hH'u
  have hD := hDv v
  rw [hi] at hD
  have key := Bridge.bridge_place hTr hTr' hsc (uMat_mul_inv (γ v)) (uMat_unitary (h v)) (uMat_mul_inv (h v))
    (uMat_inv_mul (h v)) hHe hHf hHz (uMat_unitary (h' v)) (uMat_mul_inv (h' v)) (uMat_inv_mul (h' v))
    hH'e hH'f hH'z hD (T ((tauE X e).symm v)).base hz hz' (m₀ ((tauE X e).symm v)) hm
  show Formalism.FourierDecayAlt.D.IsDFrame (T ((tauE X e).symm v)).base (ν' ((tauE X e).symm v)) (m₀ ((tauE X e).symm v))
    (Formalism.L2.SG.LocWSOf.Qics C (X.pl v) * Formalism.MainNotions.S.uMat ((h⁻¹ * γ * h') v) * Formalism.L2.SG.LocWSOf.Qcs C (X.pl v))
  rw [show ν' ((tauE X e).symm v) = _ from hν]
  exact key

end Formalism.L2.SG.Pf.Carrier
end
end
