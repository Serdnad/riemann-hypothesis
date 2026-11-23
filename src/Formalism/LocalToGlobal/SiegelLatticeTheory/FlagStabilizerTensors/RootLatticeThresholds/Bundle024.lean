module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTieOf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle049
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle019
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle022
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle018
import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.Algebra.FiniteSupport.Basic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle028
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle020
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierBase
public import Formalism.LocalToGlobal.LatticeGeometry.RealizationNorms.MkTauEmbInjective
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTop
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
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.SpectralTiesReal

@[expose] public section

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace Formalism.L2.SG.LoopTieOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ZsC1e

variable {D : D7} {X : HidaSetting D}

theorem gamma_one_eq_prod (Y : Full X) (u u' : D.what₂.Word) :
    (Y.tO u u').Gam1 = ∏ v, ((Fintype.card (GL (Fin D.R.k) (Y.TR.Fq v)) : ℝ) /
      (Formalism.L2.SG.GGMirabolic.cardU (Y.TR.Fq v) D.R.k : ℝ)) := by
  have h1 : Formalism.L2.SG.GGMirabolic.gamProd Y.TR.psi0 (1 : Iof Y.TR) =
      ((∏ v, ((Fintype.card (GL (Fin D.R.k) (Y.TR.Fq v)) : ℝ) /
        (Formalism.L2.SG.GGMirabolic.cardU (Y.TR.Fq v) D.R.k : ℝ)) : ℝ) : ℂ) := by
    simp only [Formalism.L2.SG.GGMirabolic.gamProd, Pi.one_apply, Formalism.L2.SG.GGMirabolic.gam_one]
    push_cast
    rfl
  show (Formalism.L2.SG.GGMirabolic.gamProd Y.TR.psi0 (1 : Iof Y.TR)).re = _
  rw [h1, Complex.ofReal_re]

theorem card_gl_div_unipotent (K : Type) [Field K] [Fintype K] (k : ℕ) :
    (Fintype.card (GL (Fin k) K) : ℝ) / (Formalism.L2.SG.GGMirabolic.cardU K k : ℝ) =
      ∏ i ∈ Finset.Icc 1 k, ((Fintype.card K : ℝ) ^ i - 1) := by
  have hU : Formalism.L2.SG.GGMirabolic.cardU K k = Nat.card (Formalism.DoubleCosetMeasures.upUniG K k) := by
    unfold Formalism.L2.SG.GGMirabolic.cardU
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    show Formalism.L2.SG.GGMirabolic.IsUni k x ↔ Formalism.DoubleCosetMeasures.IsUpUni (x : Matrix (Fin k) (Fin k) K)
    constructor
    · intro h
      refine ⟨?_, h.1⟩
      intro i j hij
      exact h.2 i j hij
    · intro h
      refine ⟨h.2, ?_⟩
      intro i j hij
      exact h.1 hij
  have hG := Formalism.FourierDecayAlt.P.gamma_factor_product K k
  have hq : 1 ≤ Fintype.card K := Fintype.card_pos
  have hpos : 0 < Nat.card (Formalism.DoubleCosetMeasures.upUniG K k) := Nat.card_pos
  rw [hU, ← Nat.card_eq_fintype_card, hG, Nat.cast_mul, mul_div_cancel_left₀ _ (by exact_mod_cast hpos.ne'),
    Nat.cast_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Nat.cast_sub (Nat.one_le_pow _ _ hq), Nat.cast_pow, Nat.cast_one]

theorem GamPin_of_split (Y : Full X) (h0 : Formalism.MainNotions.S.SplitsE D (D.host.g 0)) (h1 : Formalism.MainNotions.S.SplitsE D (D.host.g 1)) :
    GamPin Y := by
  intro u u'
  rw [gamma_one_eq_prod, Formalism.MainNotions.BridgeLemma.gaG_eq D h0 h1]
  simp_rw [card_gl_div_unipotent]
  rw [Formalism.L2.SG.Pf.SatGram.prod_two (fun v => Fintype.card (Y.TR.Fq v)) (D.host.g 0) (D.host.g 1) D.host.g_ne
    (fun v => Y.TR.card_q v) (fun n : ℕ => ∏ i ∈ Finset.Icc 1 D.R.k, ((n : ℝ) ^ i - 1)),
    Formalism.L2.SG.Pf.typed_count_holds X Y.TR 0, Formalism.L2.SG.Pf.typed_count_holds X Y.TR 1,
    Formalism.L2.SG.KappaOffDiagonal.PgLe.finrank_F]

theorem GamPin_of_data (Y : Full X) {C0 : ℝ} (h : StandingNumericalData D C0) : GamPin Y :=
  GamPin_of_split Y h.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.1

theorem gammaFixed_of_hypotheses (Y : Full X) {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT C0 : ℝ}
    (h : Formalism.MainNotions.S.Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) : GamPin Y :=
  GamPin_of_data Y h.2.1

end ZsC1e

end Formalism.L2.SG.LoopTieOf
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.Pf.WittFlags

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem WRowPin_holds {D : D7} {X : HidaSetting D} {Y : Formalism.L2.SG.Full.Full X} (hF : FinX Y)
    (hI : SIso D.s (_root_.Formalism.L2.SG.PackageTie2.sOf hF)) (W : Formalism.L2.SG.TermTieOf.WittDat X) (H : Formalism.L2.SG.TermTieOf.TieHyp W hI)
    (A : Formalism.L2.SG.TermTieOf.AmpDat X) (hV : Formalism.L2.SG.TermTieOf.PvalForm W hI A) :
    Formalism.L2.SG.LoopTieOf.WRowPin hF hI (Formalism.L2.SG.TermTieOf.termTieOf W hI H A hV) := by
  intro u u' p s hs
  have h2 : (Formalism.L2.SG.TermTieOf.tc hI (D.s.pfst p)).lam = s.lam :=
    (congrArg (fun t => t.lam) hs).symm
  show Formalism.MainNotions.S.wRow D (Formalism.L2.SG.TermTieOf.FlagOfWord W u) (Formalism.L2.SG.TermTieOf.lamOf W hI (D.s.pfst p)) = _
  unfold Formalism.L2.SG.TermTieOf.lamOf
  rw [h2]
  exact WRowIso_holds D (W.δ u) (W.isom u) (X.Fu u) s.lam

end Formalism.L2.SG.Pf.WittFlags
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf.CarrierXAll

open Formalism.L2.SG.Pf.Carrier

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)
  {Wp Wq : InfinitePlace D.host.E → Type} [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def JointTensorAt (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq)
    (T : ∀ j : Fin S.f, Formalism.FourierDecayAlt.D.LevTower S.G.k S.G.r (Wp (S.pl j)) (Wq (S.pl j)))
    (f : ∀ j : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j)))
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r)
    (τ : Fin S.f ≃ InfinitePlace X.B.I.F)
    (eP : ∀ v, Wp (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u v) (eQ : ∀ v, Wq (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u' v)
    (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) : Prop :=
  ∀ (p : Formalism.FourierDecayAlt.TB.Pt D.host.E) (w : Point D.host.E (D.R.rS + 1)),
    ptOfL (D := D) (D.R.rS + 1) p = some w → (∃ γ, IsPtRep X u u' w γ) →
    (∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v) →
    ∀ h h', IsDFrameX X u u' sc i0 i0' (gamW X u u' w) h h' →
    ∀ x : ∀ v, X.Vloc u' v,
      (X.piU u h⁻¹) ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
        Formalism.L2.SG.TermOp.OO (νq (gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (gamW X u u' w))
          (X.piU u' h' (X.tensU u' x))) =
        X.tensU u (fun v => eP v
          (((((Formalism.FourierDecayAlt.D.bSt (Formalism.FourierDecayAlt.D.kapG (S.g : ℝ) (Formalism.FourierDecayAlt.S6.rd D.host.E))
              (Formalism.FourierDecayAlt.C.loc (S.emb (τ.symm v)) p))⁻¹ : ℝ) : ℂ) •
            Formalism.FourierDecayAlt.D.vecV (T (τ.symm v)).base (ν' (τ.symm v)) (m₀ (τ.symm v)) (f (τ.symm v))
              (Formalism.FourierDecayAlt.D.toStd S.G.r S.g 1 (Formalism.FourierDecayAlt.C.loc (S.emb (τ.symm v)) p)))
            ((eQ v).symm (x v))))

theorem vJoint_of_tensorAt (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq)
    (T : ∀ j : Fin S.f, Formalism.FourierDecayAlt.D.LevTower S.G.k S.G.r (Wp (S.pl j)) (Wq (S.pl j)))
    (f : ∀ j : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j)))
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r)
    (τ : Fin S.f ≃ InfinitePlace X.B.I.F)
    (eP : ∀ v, Wp (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u v) (eQ : ∀ v, Wq (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u' v)
    (sc : ℝ) (hsc : 0 < sc) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (hi : ∀ v, i0 v = i0' v)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (h2 : JointTensorAt X u u' S T f ν' m₀ τ eP eQ sc i0 i0' νq) :
    VJoint X S u u' sc i0 i0' νq T f ν' m₀ τ eP eQ := by
  unfold JointTensorAt at h2
  unfold VJoint
  intro p w hpw hrep hpos x
  have hex : ∃ q : X.B.I.Ginf × X.B.I.Ginf, IsDFrameX X u u' sc i0 i0' (gamW X u u' w) q.1 q.2 := by
    have hii : i0' = i0 := funext fun v => (hi v).symm
    rw [hii]
    obtain ⟨h, h', hh⟩ := dual_frame_at_places X u u' sc i0 hsc w hrep hpos
    exact ⟨(h, h'), hh⟩
  refine Eq.trans ?_ (h2 p w hpw hrep hpos hex.choose.1 hex.choose.2 hex.choose_spec x)
  unfold unscaledOperatorAtPointRepresentative unscaledFrameConjugatedOperator
  rw [if_pos hrep, dite_eq_left hex]
  rfl

private theorem sign_flip_involutive {K : Type} [Ring K] (r b : ℕ) (x : Formalism.FourierDecayAlt.TB.Pt K) :
    Formalism.L2.SG.DataInst.signAux r b (Formalism.L2.SG.DataInst.signAux r b x) = x := by
  induction x generalizing b with
  | nil => rfl
  | cons a rest ih =>
    obtain ⟨s, t⟩ := a
    have hm : ∀ n : ℕ, ((-1 : K) ^ n) * ((-1 : K) ^ n * t) = t := by
      intro n
      rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
    simp only [Formalism.L2.SG.DataInst.signAux, hm, ih]

private theorem exists_pt_ptOfL_of_point (w : Point D.host.E (D.R.rS + 1)) :
    ∃ p : Formalism.FourierDecayAlt.TB.Pt D.host.E, ptOfL (D := D) (D.R.rS + 1) p = some w := by
  refine ⟨Formalism.L2.SG.DataInst.signPt D.R.rS (Formalism.L2.S.ptList w), ?_⟩
  have hs : Formalism.L2.SG.DataInst.signPt D.R.rS (Formalism.L2.SG.DataInst.signPt D.R.rS (Formalism.L2.S.ptList w)) =
      Formalism.L2.S.ptList w := sign_flip_involutive _ _ _
  unfold ptOfL Formalism.L2.SG.DataInst.ptOfList
  split_ifs with h
  · congr 1
    rw [Equiv.symm_apply_eq]
    exact Subtype.ext hs
  · exact (h (by rw [hs]; exact Formalism.L2.S.ptList_isPtL w)).elim

theorem vIndepAt_of_tensorAt (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq)
    (T : ∀ j : Fin S.f, Formalism.FourierDecayAlt.D.LevTower S.G.k S.G.r (Wp (S.pl j)) (Wq (S.pl j)))
    (f : ∀ j : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j)))
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r)
    (τ : Fin S.f ≃ InfinitePlace X.B.I.F)
    (eP : ∀ v, Wp (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u v) (eQ : ∀ v, Wq (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u' v)
    (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hJT : JointTensorAt X u u' S T f ν' m₀ τ eP eQ sc i0 i0' νq) : VIndepAt X u u' sc i0 i0' νq := by
  unfold JointTensorAt at hJT
  unfold VIndepAt
  intro w hrep hpos h₁ h₁' h₂ h₂' hf₁ hf₂
  obtain ⟨p, hp⟩ := exists_pt_ptOfL_of_point (D := D) w

  refine ContinuousLinearMap.coe_injective (LinearMap.ext_on_range (X.81 u') fun x => ?_)
  have e1 := hJT p w hp hrep hpos h₁ h₁' hf₁ x
  have e2 := hJT p w hp hrep hpos h₂ h₂' hf₂ x
  exact e1.trans e2.symm

end Formalism.L2.SG.Pf.CarrierXAll
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf

namespace Formalism.L2.SG.Pf.KernelOfEmbedding

variable {D : D7} {X : HidaSetting D} {Y : Formalism.L2.SG.Full.Full X} {hF : FinX Y} (W : WittDat X)
  (hI : SIso D.s (_root_.Formalism.L2.SG.PackageTie2.sOf hF))

theorem pvalForm_exists' (hC : AmpCov Y) (hK : PairAmpConst Y) (hN : FibreCountEq hF) :
    ∃ A : AmpDat X, PvalForm W hI A :=
  pvalForm_exists W hI (Formalism.L2.SG.Pf.WittFlags.WRowIso_holds D) hC hK hN

end Formalism.L2.SG.Pf.KernelOfEmbedding
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S IsDedekindDomain

namespace Formalism.L2.SG.Pf.Carrier.EnergyMS

open Formalism.L2.SG.LocVol Formalism.L2.SG.Pf.Carrier.EnergyConst Formalism.L2.SG.Pf.Carrier.EnergyConst2 Formalism.L2.SG.TypedSets Function

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Defs

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def dN (v : PlX X) : ℝ := ((Ideal.absNorm (v.maxPowDividing (differentIdeal ℤ (𝓞 X.B.I.F))) : ℕ) : ℝ)


open Classical in
def nT (v : PlX X) : ℝ :=
  if TypAt X v then ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ ((D.R.rS + 1) * (2 * D.R.rS + 3)) else 1

end Defs

def MSOrd : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ → IsStdChar ψ →
    ∀ v : PlX X, ¬ TypAt X v → localVolumeUnit X ψ v = dN X v ^ e1 D * ZZX X u u' ψ v

def MSTyp : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ → IsStdChar ψ →
    ∀ v : PlX X, TypAt X v → 0 < ZZX X u u' ψ v →
      localVolumeUnit X ψ v = dN X v ^ e1 D * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ ((D.R.rS + 1) * (2 * D.R.rS + 3)) *
        ZZX X u u' ψ v

def DiffProd : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D),
    HasFiniteMulSupport (dN X) ∧ ∏ᶠ v, dN X v = |((NumberField.discr X.B.I.F : ℤ) : ℝ)|

def DiscRd : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D), |((NumberField.discr X.B.I.F : ℤ) : ℝ)| = D.host.rdE ^ D.R.f

def TypNorm : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D),
    ∏ p : TypX X, ((Ideal.absNorm p.1.asIdeal : ℕ) : ℝ) = ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ D.R.f

theorem lemmaMSStd_of (hO : MSOrd) (hT : MSTyp) (hD : DiffProd) (hR : DiscRd) (hN : TypNorm)
    {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) : LemmaMSStd X u u' ψ := by
  classical
  intro hψ hstd hC
  set k := (D.R.rS + 1) * (2 * D.R.rS + 3) with hk
  have hZpos : ∀ v, 0 < ZZX X u u' ψ v := fun v => (hC.1 v).2.2.1
  have hU00m : Multipliable (fun v : OrdX X => localVolumeUnit X ψ v.1) := hC.2.2.2.1
  have hZm : Multipliable (ZZX X u u' ψ) := hC.2.2.2.2.2.1
  have hloc : ∀ v, localVolumeUnit X ψ v = (dN X v ^ e1 D * nT X v) * ZZX X u u' ψ v := by
    intro v
    by_cases hv : TypAt X v
    · rw [hT D X u u' ψ hψ hstd v hv (hZpos v)]
      simp only [nT, if_pos hv]
    · rw [hO D X u u' ψ hψ hstd v hv]
      simp only [nT, if_neg hv, mul_one]
  obtain ⟨hDf, hDp⟩ := hD D X

  set s : Set (PlX X) := ↑(Formalism.L2.SG.TypedSets.typSet X.B.I.F (D.host.g 0) (D.host.g 1)) with hs
  have hnTs : Function.mulSupport (nT X) ⊆ s := by
    intro v hv
    by_contra h
    exact hv (by unfold nT; exact if_neg (show ¬ TypAt X v from h))
  have hnTf : HasFiniteMulSupport (nT X) := (Finset.finite_toSet _).subset hnTs
  have hAf : HasFiniteMulSupport (fun v => dN X v ^ e1 D * nT X v) := (hDf.pow _).mul hnTf

  have h1 : (∏' v : OrdX X, localVolumeUnit X ψ v.1) * ∏ p : TypX X, localVolumeUnit X ψ p.1 = ∏' v, localVolumeUnit X ψ v := by
    have hsm : Multipliable ((localVolumeUnit X ψ) ∘ ((↑) : s → PlX X)) := Multipliable.of_finite
    have hscm : Multipliable ((localVolumeUnit X ψ) ∘ ((↑) : ↑sᶜ → PlX X)) := hU00m
    rw [← Multipliable.tprod_mul_tprod_compl hsm hscm, mul_comm]
    congr 1
    rw [tprod_fintype]
    rfl

  have h2 : ∏' v, localVolumeUnit X ψ v = (∏ᶠ v, (dN X v ^ e1 D * nT X v)) * ∏' v, ZZX X u u' ψ v := by
    rw [tprod_congr hloc, Multipliable.tprod_mul (multipliable_of_hasFiniteMulSupport hAf) hZm,
      tprod_eq_finprod hAf]

  have h3 : (∏ᶠ v, (dN X v ^ e1 D * nT X v)) =
      D.host.rdE ^ (D.R.f * e1 D) * ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (D.R.f * k) := by
    have hDpow : HasFiniteMulSupport (fun v => dN X v ^ e1 D) := hDf.pow _
    rw [finprod_mul_distrib hDpow hnTf, ← finprod_pow hDf, hDp, hR D X, ← pow_mul]
    congr 1
    rw [finprod_eq_prod_of_mulSupport_subset (nT X) hnTs, pow_mul, ← hN D X, ← Finset.prod_pow]
    rw [← Finset.prod_coe_sort]
    refine Finset.prod_congr rfl fun p _ => ?_
    unfold nT
    exact if_pos (show TypAt X p.1 from p.2)
  unfold LemmaMS
  show (∏' v : OrdX X, localVolumeUnit X ψ v.1) * ∏ p : TypX X, localVolumeUnit X ψ p.1 = _ * (∏' v : PlX X, ZZX X u u' ψ v)
  rw [h1, h2, h3]

end Formalism.L2.SG.Pf.Carrier.EnergyMS
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Classical
open Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full

namespace Formalism.L2.SG.Pf.Carrier.EnergyFinal

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.EnergyPf
  Formalism.L2.SG.Pf.Carrier.EnergyPlace Formalism.L2.SG.AdBridge Formalism.L2.SG.SpectralTiesReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {u u' : D.what₂.Word}

def PlaceNormG (P : Parts X u u') (hr : P.S.G.r = D.R.rS) : Prop :=
  ∀ (v : InfinitePlace X.B.I.F) (g : Formalism.REAL.UJ (X.B.I.ε v)) (cv : Fin (D.R.rS + 1) → ℂ), cv ∈ GoodV u u' →
    Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (uMat g) = Matrix.diagonal cv →
    hs2 (JvX X u u' v g) =
      ‖Formalism.FourierDecayAlt.B.hsVec (Formalism.FourierDecayAlt.B.JF (P.T (P.τ.symm v)).base (P.f (P.τ.symm v))
        (Formalism.FourierDecayAlt.B.gq (P.T (P.τ.symm v)).base (phiQ P hr cv)))‖ ^ 2

theorem placeNorm_of_G (P : Parts X u u') (hr : P.S.G.r = D.R.rS) (hG : PlaceNormG P hr)
    (L : InfinitePlace X.B.I.F → (Fin (D.R.rS + 1) → ℂ) → ℝ) (hL : LocRep X u u' L) : PlaceNorm P hr L := by
  intro v cv hcv
  let c : Cinf X := fun _ => cv
  have hc : c ∈ Good X u u' := fun _ => hcv
  obtain ⟨γ, hγ⟩ := InfCut.ProductExactness.StepReal_holds D X u u' 1 one_pos c hc
  have hex : ∃ γ, HasDiag X u u' 1 c γ := ⟨γ, hγ⟩
  have hd : HasDiag X u u' 1 c (hOf X u u' 1 c) := by
    unfold hOf
    rw [dite_eq_left hex]
    exact hex.choose_spec
  have h1 : hs2 (JvX X u u' v ((hOf X u u' 1 c) v)) = L v cv := hL.2 c hc v
  have h2 := hG v ((hOf X u u' 1 c) v) cv hcv (hd v)
  exact h1.symm.trans h2

end Formalism.L2.SG.Pf.Carrier.EnergyFinal
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.Carrier

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

open Formalism.L2.SG.RealObj

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem placeTie_ePl : PlaceTie X (Formalism.L2.Geo.Rec.StarEmbeddingNorm.ePl D).symm :=
  fun x => Formalism.L2.SG.Pf.CarrierTop.placeTie_ePl X x

theorem embE_apply (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (j : Fin (nfE D)) (x : X.B.I.E) :
    embE X e j (X.ιE x) = X.B.I.φ (tauE X e j) x := by
  show X.B.I.φ _ (X.ιE.symm (X.ιE x)) = _
  rw [RingEquiv.symm_apply_apply]

variable {X} {u u' : D.what₂.Word}

theorem G_sOf (I : CarrierIn X u u') (j : Fin I.nf) (q : Formalism.FourierDecayAlt.C.LPt) :
    ((sOf I).pd j).G q = Complex.normSq (Formalism.FourierDecayAlt.D.ptLast q).2 - Tw (D := D) u * Tw (D := D) u' := by
  show Complex.normSq _ - Formalism.QuantumDeterminants.Tz I.G.k I.G.r (I.T j).base.z * Formalism.QuantumDeterminants.Tz I.G.k I.G.r (I.T j).base.z' = _
  rw [(I.hT j).1, (I.hT j).2]
  rfl

theorem emb_carrierInOf (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ)
    (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ) (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (T : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.D.LevTower D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (hT : ∀ j, Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z = ((D.mem u).A.T : ℝ) ∧
      Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z' = ((D.mem u').A.T : ℝ))
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (χ : ℝ → ℝ) (sg : Fin (nfE D) → ℂ) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (top : ∀ j : Fin (nfE D), (Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j))) →
      List Formalism.FourierDecayAlt.C.Letter → Formalism.FourierDecayAlt.C.LPt → Formalism.FourierDecayAlt.C.LPt → ℂ) (A₀ : ℝ) :
    ∀ j x, (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀).emb j (X.ιE x) =
      X.B.I.φ ((carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀).τ j) x :=
  fun j x => embE_apply X e j x


open Matrix in
theorem base_carrierOf (I : CarrierIn X u u') (Mo : ModelsFor (sOf I)) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (hQ : ∀ v, I.Q v * I.Qi v = 1) (hi : ∀ v, i0 v = i0' v)
    (hν : ∀ j, I.ν' j = I.Qi (I.τ j) *ᵥ X.wfr u' (I.τ j) (i0' (I.τ j)))
    (hm : ∀ j, I.m₀ j = Formalism.L2.SG.Pf.CarrierBase.m0Of X u u' (I.τ j) (I.Q (I.τ j)) (I.Qi (I.τ j))) :
    (CarrierOf I Mo).Base i0 i0' := by
  have h := Formalism.L2.SG.Pf.CarrierBase.baseFromX_of X u u' (sOf I) i0 i0' I.τ I.Q I.Qi hQ hi
  have e1 : I.ν' = fun j => I.Qi (I.τ j) *ᵥ X.wfr u' (I.τ j) (i0' (I.τ j)) := funext hν
  have e2 : I.m₀ = fun j => Formalism.L2.SG.Pf.CarrierBase.m0Of X u u' (I.τ j) (I.Q (I.τ j)) (I.Qi (I.τ j)) := funext hm
  show BaseFromX X (sOf I) u u' i0 i0' I.τ I.Q I.Qi I.ν' I.m₀
  rw [e1, e2]
  exact h

end Formalism.L2.SG.Pf.Carrier
end
end
