module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle040
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardBaseFlagComplementIntegralLattice
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle021
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle033
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle032
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle029
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle007
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle034
public import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEstimateWords
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

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.Pf.NcReal.JX Formalism.L2.SG.TermOp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Defs

variable {D : D7} (X : HidaSetting D)

abbrev BV : Type := ∀ q : CBlk D.R.rS, CSpc (InfinitePlace X.B.I.F) D.R.k q

def iQ (D : D7) (b a : Fin D.R.rS) : Set D.host.E :=
  ((aaD D b * (aaD D a)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E)

def iP (D : D7) (b a : Fin D.R.rS) : Set D.host.E :=
  ((aaD D b * aaD D a : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E)

def pW (y : (VS D).V) : (VS D).V :=
  y - ∑ c, (VS D).hT (X.fY c) y • X.eX c - ∑ c, (VS D).hT (X.eX c) y • X.fY c

def InW (y : (VS D).V) : Prop := ∀ c, (VS D).hT (X.eX c) y = 0 ∧ (VS D).hT (X.fY c) y = 0

def Xq (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E :=
  fun b a => (VS D).hT (X.fY b) (n (X.eX a))

def Aq (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E :=
  fun b a => (VS D).hT (X.fY b) (n (X.fY a))

def Mq (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E :=
  (Xq X n)⁻¹ * Aq X n

def xq (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (b : Fin D.R.rS) : (VS D).V := pW X (n.symm (X.fY b))

def Gq (D : D7) (xs : Fin D.R.rS → (VS D).V) : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E :=
  fun b c => (VS D).hT (xs b) (xs c)

def Gp (D : D7) (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V) :
    Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E :=
  X0⁻¹ * Gq D xs * (X0⁻¹)ᴴ

def DataOK (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
    (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) : Prop :=
  (∀ b a : Fin D.R.rS, a < b → X0 b a = 0) ∧ (∀ a, X0 a a = 1) ∧ (∀ b, InW X (xs b)) ∧ M + Mᴴ = -Gp D X0 xs

def LatQ (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
    (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) : Prop :=
  (∀ b a : Fin D.R.rS, b < a → X0 b a ∈ iQ D b a) ∧ (∀ b, xs b ∈ aaLb X b) ∧ ∀ b a, M b a ∈ iP D b a

variable (u : D.what₂.Word)

def NFl (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop :=
  n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧
    (∀ j, ∀ x ∈ Xflag (lf D (X.Fu u)) (j + 1), n x - x ∈ Xflag (lf D (X.Fu u)) j) ∧
    ∀ x ∈ orth (VS D) (Xsp (lf D (X.Fu u))), n x - x ∈ Xsp (lf D (X.Fu u))

def blkQ (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
    (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) :
    ∀ p : CBlk D.R.rS, CSpc (InfinitePlace X.B.I.F) D.R.k p
  | Sum.inl (Sum.inl p) => embV X (X0 p.1.1 p.1.2)
  | Sum.inl (Sum.inr b) => rowV X u (xs b)
  | Sum.inr (Sum.inl p) => fun v =>
      (embS D (X.pl v) (M p.1.1 p.1.2) - star (embS D (X.pl v) (M p.1.2 p.1.1))) / 2
  | Sum.inr (Sum.inr a) => fun v => (embS D (X.pl v) (M a a)).im


open scoped Classical in
def theta (D : D7) : D.host.E :=
  if h : ∃ t : D.host.E, IsIntegral ℤ t ∧ t + D.host.conj t = 1 then h.choose else 0

def Xc (x : BV X) (v : InfinitePlace X.B.I.F) :
    Matrix (Fin D.R.rS) (Fin D.R.rS) ℂ :=
  fun b a => if h : b < a then x (Sum.inl (Sum.inl ⟨(b, a), h⟩)) v else if b = a then 1 else 0

def Gc (x : BV X) (v : InfinitePlace X.B.I.F) :
    Matrix (Fin D.R.rS) (Fin D.R.rS) ℂ :=
  fun b c => (∑ j : Fin D.R.k, x (Sum.inl (Sum.inr b)) v (Fin.castSucc j) *
      star (x (Sum.inl (Sum.inr c)) v (Fin.castSucc j))) -
    x (Sum.inl (Sum.inr b)) v (Fin.last D.R.k) * star (x (Sum.inl (Sum.inr c)) v (Fin.last D.R.k)) /
      (((D.mem u).A.T : ℕ) : ℂ)

def Hc (x : BV X) (v : InfinitePlace X.B.I.F) :
    Matrix (Fin D.R.rS) (Fin D.R.rS) ℂ :=
  (Xc X x v)⁻¹ * Gc X u x v * ((Xc X x v)⁻¹)ᴴ

def tauQ : ∀ p : CBlk D.R.rS, BV X → CSpc (InfinitePlace X.B.I.F) D.R.k p
  | Sum.inl (Sum.inl _) => fun _ => 0
  | Sum.inl (Sum.inr _) => fun _ => 0
  | Sum.inr (Sum.inl p) => fun x v => Hc X u x v p.1.1 p.1.2 / 2
  | Sum.inr (Sum.inr a) => fun x v => -((Hc X u x v a a).re * (embS D (X.pl v) (theta D)).im)

end Defs

def NOratC : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (s : X.B.I.Ginf),
    s ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u ↔
      ∃ (x : X.B.I.GA) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V), RatLink X x n ∧ x.1 = s ∧
        n ∈ NLam (VS D).L0 (lf D (X.Fu u))

def DictGram : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V),
    NFl X u n → DataOK X (Xq X n) (xq X n) (Mq X n)

def DictLat : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V),
    NFl X u n → (Formalism.HermitianLatticesTheory.gmap n (VS D).L0 = (VS D).L0 ↔ LatQ X (Xq X n) (xq X n) (Mq X n))

def DictEx : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (xs : Fin D.R.rS → (VS D).V) (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E), DataOK X X0 xs M →
    ∃ n : (VS D).V ≃ₗ[D.host.E] (VS D).V, NFl X u n ∧ Xq X n = X0 ∧ xq X n = xs ∧ Mq X n = M

def DictPlace : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (x : X.B.I.GA) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V),
    RatLink X x n → NFl X u n → blk X u x.1 = blkQ X u (Xq X n) (xq X n) (Mq X n)

def FibQ : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (xs : Fin D.R.rS → (VS D).V) (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E), DataOK X X0 xs M →
    ((∀ p, blkQ X u X0 xs M p - tauQ X u p (blkQ X u X0 xs M) ∈ cLat X u p) ↔ LatQ X X0 xs M)

def FibOnto : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (x : BV X),
    (∀ p, x p - tauQ X u p x ∈ cLat X u p) →
      ∃ (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
        (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E), DataOK X X0 xs M ∧ blkQ X u X0 xs M = x

def ThetaEx : Prop :=
  ∀ D : D7, ∃ t : D.host.E, IsIntegral ℤ t ∧ t + D.host.conj t = 1

theorem tauQ_lower {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (p : CBlk D.R.rS)
    (x x' : BV X) (h : ∀ q, cHgt q < cHgt p → x q = x' q) :
    tauQ X u p x = tauQ X u p x' := by
  rcases p with (p | b) | (p | a)
  · rfl
  · rfl
  all_goals
    have hX : ∀ q, x (Sum.inl q) = x' (Sum.inl q) := by
      intro q
      apply h
      rcases q with q | c
      · have := q.1.2.isLt
        simp only [cHgt]
        omega
      · have := c.isLt
        simp only [cHgt]
        omega
    have hH : Hc X u x = Hc X u x' := by
      funext v
      have hXc : Xc X x v = Xc X x' v := by
        funext i j
        simp only [Xc, hX]
      have hGc : Gc X u x v = Gc X u x' v := by
        funext i j
        simp only [Gc, hX]
      simp only [Hc, hXc, hGc]
    simp only [tauQ]
    rw [hH]

theorem nofibLat_of (hR : NOratC) (hG : DictGram) (hL : DictLat) (hE : DictEx) (hP : DictPlace) (hF : FibQ)
    (hO : FibOnto) : NOfibLat := by
  intro D X u
  refine ⟨tauQ X u, fun p x x' h => tauQ_lower X u p x x' h, fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨xA, n, hlink, hx1, hn⟩ := (hR X u s).1 hs
    have hNF : NFl X u n := ⟨hn.1.1, hn.2.1, hn.2.2⟩
    have hD := hG X u n hNF
    have hLat := (hL X u n hNF).1 hn.1.2
    rw [← hx1, hP X u xA n hlink hNF]
    exact (hF X u _ _ _ hD).2 hLat
  · intro hx
    obtain ⟨X0, xs, M, hD, rfl⟩ := hO X u x hx
    have hLat := (hF X u X0 xs M hD).1 hx
    obtain ⟨n, hNF, h1, h2, h3⟩ := hE X u X0 xs M hD
    subst h1 h2 h3
    have hgm := (hL X u n hNF).2 hLat
    have hn : n ∈ NLam (VS D).L0 (lf D (X.Fu u)) := ⟨⟨hNF.1, hgm⟩, hNF.2.1, hNF.2.2⟩
    obtain ⟨xA, hlink⟩ := ratPt_holds D X n hNF.1
    exact ⟨xA.1, (hR X u xA.1).2 ⟨xA, n, hlink, rfl, hn⟩, hP X u xA n hlink hNF⟩

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G8

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

theorem glueProd_of_iso (h1 : JordanExists) (h2 : JordanInv) (h6 : GlueLoc) (hI : IsomFixOfExp) :
    GlueProd := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc hpos M hM Λ₀ hΛ₀ T hT
  have hΛ₀full : Submodule.IsFullLattice K Λ₀ :=
    { toIsLattice := hΛ₀.1
      span_eq_top := GlobalTheory.LoopC.Base.span_eq_top_of_unimodular h hs (nondegenerate_of hs hnd)
        hΛ₀.1 hΛ₀.2.1 }
  refine ⟨⟨genus_of_fib h1 h2 h6 hI hK hF hs hnd hUc hpos hM hΛ₀ hT, fun hg 𝔭 h𝔭 =>
    fibP_ne_zero_of_genus hF hs hnd hUc hM hΛ₀ hg h𝔭⟩, card_glue hK hF hUc hM hΛ₀ hΛ₀full hT⟩

end Formalism.L2.SG.Pf.G8

namespace Formalism.L2.SG.Pf.Cnt

theorem glueProd_of (h1 : JordanExists) (h2 : JordanInv) (h3 : JordanIsom) (h6 : GlueLoc) : GlueProd :=
  G8.glueProd_of_iso h1 h2 h6 (G8.isomFixOfExp_of h3)

end Formalism.L2.SG.Pf.Cnt
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.NcX.OmVSt

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  MeasureTheory NumberField IsDedekindDomain

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem n_sub_a : X.B.I.n - (D.R.rS + 1 + D.R.rS) = D.R.k := by
  have h1 := X.n_eq
  have h2 := D.R.rS_two
  unfold Ranks.r at h1
  omega

theorem a_le_n : D.R.rS + 1 + D.R.rS ≤ X.B.I.n := by
  have h1 := X.n_eq
  have h2 := D.R.rS_two
  unfold Ranks.r at h1
  omega

theorem fac_nonneg (v : PlX X) (j : ℕ) :
    0 ≤ 1 - (etaV (E := X.B.I.E) v : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ)) := by
  have hq : (1 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    have : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have h1 : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ hq (by omega)
  have h0 : 0 ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ)) := by positivity
  have he : (etaV (E := X.B.I.E) v : ℝ) ^ j = 1 ∨ (etaV (E := X.B.I.E) v : ℝ) ^ j = -1 := by
    unfold etaV
    split_ifs
    · left; simp
    · push_cast; exact neg_one_pow_eq_or ℝ j
  rcases he with h | h <;> rw [h] <;> linarith

theorem val_nonneg (v : PlX X) (x : ℝ) (s : Finset ℕ) :
    0 ≤ absV v (dV v) ^ x * ∏ j ∈ s,
      (1 - (etaV (E := X.B.I.E) v : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ))) := by
  refine mul_nonneg (Real.rpow_nonneg ?_ _) (Finset.prod_nonneg fun j _ => fac_nonneg X v j)
  unfold absV
  split_ifs <;> positivity

theorem prod_eq (v : PlX X) (s : Finset ℕ) :
    ∏ j ∈ s, (1 - (etaV (E := X.B.I.E) v : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ))) =
      ∏ i ∈ s, (1 - ((etaV (E := X.B.I.E) v : ℤ) : ℝ) ^ i / ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ i) := by
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [zpow_neg, zpow_natCast, div_eq_mul_inv]

theorem exp_eq :
    (X.B.I.n : ℝ) * ((D.R.rS + 1 + D.R.rS : ℕ) : ℝ) - ((D.R.rS + 1 + D.R.rS : ℕ) : ℝ) ^ 2 / 2 =
      (X.B.I.n : ℝ) * (2 * D.R.rS + 1) - ((2 * (D.R.rS : ℝ) + 1) ^ 2) / 2 := by
  push_cast; ring

theorem omV_of (hStd : OmVStd X ψ) (hLat : OmVLat X) (hSD : OmVSD X) (hUn : OmVUnram X) (hPrim : OmVPrim X u')
    (hGram : OmVGram X u') (hDet : OmVDet X u') (hScale : OmVScale X u' ψ) (hBad : OmVBadT X u' ψ)
    (hLocU : OmVLocU X ψ) : Formalism.L2.SG.Pf.NcVal.OmV X u' ψ := by
  intro hψ hψ' v
  show (omAt X.B.I.cm.sig X.B.I.J ψ v (localGramMatrixFrame X u' v)
      {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (abelian₂ X) v, Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))}).toReal = _
  rw [hScale hψ hψ' v]
  by_cases hT : ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal
  · rw [hBad hψ hψ' v hT (hSD v) (hUn v) (hPrim v), ENNReal.toReal_ofReal (val_nonneg X v _ _), exp_eq X, prod_eq X v]
    unfold aP
    rw [if_pos hT, n_sub_a X]
  · have h := hLocU v _ (yTup X u' v) (hStd hψ hψ') hLat (hSD v) (hUn v) (a_le_n X) (hPrim v)
      (by rw [hGram v]; exact hDet v hT)
    rw [hGram v] at h
    rw [h, ENNReal.toReal_ofReal (val_nonneg X v _ _), exp_eq X, prod_eq X v]
    unfold aP
    rw [if_neg hT, n_sub_a X]

end Formalism.L2.SG.Pf.NcX.OmVSt
end
end

section

noncomputable section

open Classical

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.LocVol Formalism.L2.SG.MassDataConc Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def FieldDict {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) : Prop :=
  |(NumberField.discr X.B.I.F : ℝ)| = |(NumberField.discr D.host.F : ℝ)| ∧
  Fintype.card (NumberField.InfinitePlace X.B.I.F) = Module.finrank ℚ D.host.F ∧
  (∀ i : ℕ, 2 ≤ i → HasProd (fun v : PlX X =>
      (1 - ((etaV (E := X.B.I.E) v : ℤ) : ℝ) ^ i / ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ i)⁻¹)
      (Formalism.HermitianLattices.Ext.L3.lValEtaF D.host.E D.host.F i)) ∧
  HasProd (fun v : PlX X => if (((D.mem u).A.T : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal then
      1 - ((etaV (E := X.B.I.E) v : ℤ) : ℝ) ^ D.R.k / ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ D.R.k else 1)
    (∏' 𝔭 : {𝔭 : Ideal (𝓞 D.host.F) // 𝔭.IsMaximal},
      (if (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ 𝔭.1 then
        1 - Formalism.HermitianLattices.Ext.L3.etaF D.host.E D.host.F 𝔭.1 ^ D.R.k * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(D.R.k : ℤ)) else 1)) ∧
  Formalism.HermitianLatticesTheory.vInv D.host.E = |(NumberField.discr D.host.F : ℝ)| ^ ((1 : ℝ) / Module.finrank ℚ D.host.F) / 2 ∧
  Formalism.HermitianLatticesTheory.fDeg D.host.E = Module.finrank ℚ D.host.F ∧
  X.B.I.n = D.R.r ∧
  (∀ p : TypX X, absV p.1 (dV p.1) = 1) ∧
  (∀ p : TypX X, aP (E := X.B.I.E) p.1 D.R.k X.B.I.n (Tw u') = aP (E := X.B.I.E) p.1 D.R.k X.B.I.n (Tw u)) ∧
  ∏ p : TypX X, (gAt X p.1 : ℝ) = ((Lat.gS D : ℕ) : ℝ) ^ Module.finrank ℚ D.host.F

def NcArith : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
    (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
    {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
    (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (a' : ℝ),
    0 < a' → IsRowReps D F0 what₂ →
    (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μK * a' =
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μH' *
        ∏' v : PlX X,
          (omAt X.B.I.cm.sig X.B.I.J ψ v
            ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Fv X.B.I.F v)))
            {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) v,
              Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))}).toReal →
    Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 * (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volH *
              (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN *
              (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN' =
      a' * 2 ^ (D.R.k * Fintype.card (NumberField.InfinitePlace X.B.I.F)) *
        (Real.pi ^ D.R.k / (Nat.factorial (D.R.k - 1) : ℝ)) ^ Fintype.card (NumberField.InfinitePlace X.B.I.F) *
        ((Tw u : ℕ) : ℝ) ^ (-((D.R.k * Fintype.card (NumberField.InfinitePlace X.B.I.F) : ℕ) : ℤ)) *
        |(NumberField.discr X.B.I.F : ℝ)| ^
          (-(8 * (D.R.rS : ℝ) ^ 3 + 6 * (D.R.rS : ℝ) ^ 2 + 6 * D.R.k * (D.R.rS : ℝ) ^ 2 + D.R.rS) / 3) →
    IsCharAF X.B.I.F ψ → IsStdChar ψ → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    VolOrdV X u u' ψ → VolTypV X u u' ψ →
    (∀ p : TypX X,
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKnatp p /
          (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKp p =
        (gAt X p.1 : ℝ) ^ (-(((D.R.rS + 1) * (2 * D.R.k + 2 * D.R.rS + 1) : ℕ) : ℤ)) /
          aP (E := X.B.I.E) p.1 D.R.k X.B.I.n (Tw u)) →
    OmV X u' ψ → DiffProd X → Formalism.L2.SG.Pf.Cnt.RowsMass → FieldDict X u u' → ProdConv X u u' ψ →
    (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Pos →
    Formalism.L2.SG.Pf.NcAsm.NcValueC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq

end Formalism.L2.SG.Pf.NcVal
end
end

section

noncomputable section

open NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem traceRe_holds : TraceRe := by
  intro D X t
  have h1 : ∀ v, X.B.I.φ v (X.ιE.symm t) = embS D (X.pl v) t := fun v => by
    rw [X.φ_eq, RingEquiv.apply_symm_apply]
  simp only [h1]
  rw [Formalism.MainNotions.BlockEstimateWords.trace_tau D t, Finset.sum_div,
    Equiv.sum_comp X.pl (fun τ => ((embS D τ) t).re)]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [mul_div_cancel_left₀ _ two_ne_zero]
  rfl

end Formalism.L2.SG.Pf.NcReal.JX.CovB
end
end
