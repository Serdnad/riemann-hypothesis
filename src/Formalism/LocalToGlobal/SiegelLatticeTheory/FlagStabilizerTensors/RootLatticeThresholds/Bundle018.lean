module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeNC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FullExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.WuDefiniteHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDict
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictZPfG
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocalAdditiveCharContinuous
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocUnram
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellBru
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellFin
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellGeo
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle002
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle007
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle016
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.Bridge

section Std

variable {K : Type} [Field K] (σ : K →+* ℂ) (r : ℕ) (g : ℝ)

theorem blk_std (s o : ℕ) (hs : 1 ≤ s) (hos : o + s ≤ r + 1) :
    blkF (-Complex.I * ((g / (2 * Real.pi) : ℝ) : ℂ)) r o (o + s - 1) * (-1) ^ (r + 1 - (o + 1 + s - 1)) =
      (((g / (2 * Real.pi)) ^ Formalism.FourierDecayAlt.S6.nuBlock (r : ℤ) ((o + 1 : ℕ) : ℤ) (s : ℤ) : ℝ) : ℂ) *
        Complex.I ^ (s - 1) := by
  set a : ℝ := g / (2 * Real.pi)
  set m := (r - o) + (r - (o + s - 1)) with hm
  set e := r + 1 - (o + 1 + s - 1) with he
  have hnu : Formalism.FourierDecayAlt.S6.nuBlock (r : ℤ) ((o + 1 : ℕ) : ℤ) (s : ℤ) = (m : ℤ) := by
    unfold Formalism.FourierDecayAlt.S6.nuBlock; rw [hm]; push_cast; omega
  have hme : m = 2 * e + (s - 1) := by rw [hm, he]; omega
  rw [hnu, zpow_natCast]
  unfold blkF
  rw [← hm, mul_pow, ← mul_assoc, ← mul_pow, neg_mul, one_mul, neg_neg, Complex.ofReal_pow, hme, pow_add, pow_mul,
    Complex.I_sq]
  have h1 : ((-1 : ℂ) ^ e) * ((-1 : ℂ) ^ e) = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have h2 : ((-1 : ℂ) ^ e) = (-1) ^ e := rfl
  calc (-1 : ℂ) ^ e * Complex.I ^ (s - 1) * (a : ℂ) ^ (2 * e + (s - 1)) * (-1) ^ e
      = (((-1 : ℂ) ^ e) * ((-1 : ℂ) ^ e)) * ((a : ℂ) ^ (2 * e + (s - 1)) * Complex.I ^ (s - 1)) := by ring
    _ = (a : ℂ) ^ (2 * e + (s - 1)) * Complex.I ^ (s - 1) := by rw [h1, one_mul]

theorem lptOf_toStd : ∀ (L : Formalism.FourierDecayAlt.TB.Pt K) (o : ℕ), (∀ b ∈ L, 1 ≤ b.1) → o + (L.map Prod.fst).sum ≤ r + 1 →
    lptOf σ (-Complex.I * ((g / (2 * Real.pi) : ℝ) : ℂ)) r o ((Formalism.L2.SG.DataInst.signAux r (o + 1) L).map Prod.swap) =
      Formalism.FourierDecayAlt.D.toStd r g (o + 1) (Formalism.FourierDecayAlt.C.loc σ L)
  | [], _, _, _ => rfl
  | (s, t) :: rest, o, hL, ho => by
    simp only [List.map_cons, List.sum_cons] at ho
    have hs : 1 ≤ s := hL (s, t) (List.mem_cons_self)
    simp only [Formalism.L2.SG.DataInst.signAux, List.map_cons, Prod.swap_prod_mk, lptOf, Formalism.FourierDecayAlt.C.loc,
      Formalism.FourierDecayAlt.D.toStd, List.cons.injEq, true_and]
    constructor
    · rw [map_mul, map_pow, map_neg, map_one, ← mul_assoc, blk_std r g s o hs (by omega)]
    · have := lptOf_toStd rest (o + s) (fun b hb => hL b (List.mem_cons_of_mem _ hb)) (by omega)
      rw [show o + s + 1 = o + 1 + s by omega] at this
      exact this

end Std

end Formalism.L2.SG.Pf.Bridge
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier.EnergyConst

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.EnergyPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

def e1 (D : D7) : ℕ := (D.R.rS + 1) * (8 * D.R.rS ^ 2 + 10 * D.R.rS + 3) / 3

def rdExp (D : D7) : ℕ := 2 * D.R.rS * (D.R.rS + 1) * (D.R.k - 1) + e1 D

def Anum (D : D7) : ℝ := D.host.rdE ^ rdExp D * ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (3 * (D.R.rS + 1))

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def Kexp (P : Parts X u u') : ℝ := Anum D / P.Gam0


variable (X u u') in
def LemmaMS (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) : Prop :=
  (Formalism.L2.SG.LocVol.locOf X u u' ψ).localVolumeArchimedean * ∏ p, (Formalism.L2.SG.LocVol.locOf X u u' ψ).localVolumeAtPlace p =
    D.host.rdE ^ (D.R.f * e1 D) * ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (D.R.f * ((D.R.rS + 1) * (2 * D.R.rS + 3))) *
      (Formalism.L2.SG.LocVol.locOf X u u' ψ).volZZ

theorem anum_pow : Anum D ^ D.R.f =
    Formalism.L2.SG.MassDataConc.kapN D * (D.host.rdE ^ (D.R.f * e1 D) *
      ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (D.R.f * ((D.R.rS + 1) * (2 * D.R.rS + 3)))) := by
  have hb : ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ≠ 0 := by
    unfold Formalism.MainNotions.S.Lat.gS
    exact Nat.cast_ne_zero.mpr (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
  have key : ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (D.R.f * ((D.R.rS + 1) * (2 * D.R.rS + 3))) =
      ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (2 * D.R.f * D.R.rS * (D.R.rS + 1)) *
        ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (3 * (D.R.rS + 1) * D.R.f) := by
    rw [← pow_add]
    congr 1
    ring
  rw [key]
  simp only [Anum, rdExp, Formalism.L2.SG.MassDataConc.kapN]
  rw [mul_pow, ← pow_mul, ← pow_mul]
  field_simp
  ring

theorem rdE_pos' : 0 < D.host.rdE := by
  unfold Formalism.BasicNotions.Host.rdE
  apply Real.rpow_pos_of_pos
  have h := NumberField.discr_ne_zero (K := D.host.E)
  exact abs_pos.mpr (by exact_mod_cast h)

theorem energy_constant_nonneg (P : Parts X u u') : 0 ≤ P.Gam0 := by
  unfold Formalism.L2.SG.Pf.Carrier.Parts.Gam0 Formalism.FourierDecayAlt.D.GamLev
  apply Finset.prod_nonneg
  intro l _
  apply div_nonneg
  · apply zpow_nonneg
    unfold Formalism.FourierDecayAlt.D.kapG Formalism.FourierDecayAlt.S6.rd
    positivity
  · unfold Formalism.FourierDecayAlt.D.deG Formalism.FourierDecayAlt.S6.rd
    positivity

theorem constPin_of (P : Parts X u u') (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    (hC : Formalism.L2.SG.LocVol.ProdConv X u u' ψ) (hMS : LemmaMS X u u' ψ)
    (hf : Fintype.card (InfinitePlace X.B.I.F) = D.R.f) :
    ConstPin P ψ (fun _ => Kexp P) := by
  obtain ⟨-, -, -, -, -, -, hZZ, hPP, -⟩ := hC
  have hb : ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ≠ 0 := by
    unfold Formalism.MainNotions.S.Lat.gS
    exact Nat.cast_ne_zero.mpr (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
  have hrd : 0 < D.host.rdE := rdE_pos'
  have hA : 0 ≤ Anum D := by
    unfold Anum
    exact mul_nonneg (pow_nonneg hrd.le _) (pow_nonneg (Nat.cast_nonneg _) _)
  have hK0 : 0 ≤ Kexp P := div_nonneg hA (energy_constant_nonneg P)
  refine ⟨fun _ => hK0, ?_⟩
  have hfS : P.S.f = D.R.f := by
    rw [← hf, ← Fintype.card_fin P.S.f]
    exact Fintype.card_congr P.τ
  have hprod : ∏ _v : InfinitePlace X.B.I.F, Kexp P = Anum D ^ D.R.f / P.Gam0 ^ D.R.f := by
    rw [Finset.prod_const, Finset.card_univ, hf, Kexp, div_pow]
  have hvZZ : 0 < (Formalism.L2.SG.LocVol.locOf X u u' ψ).volZZ := hZZ
  have hvPP : 0 < (Formalism.L2.SG.LocVol.locOf X u u' ψ).volPP := by
    show 0 < ∏ l : Fin (D.R.rS + 1), ∏' v : Formalism.L2.SG.LocVol.PlX X, Formalism.L2.SG.LocVol.PPX X u u' ψ l v
    exact Finset.prod_pos (fun l _ => (hPP l).2)
  have hkap : Formalism.L2.SG.MassDataConc.kapN D ≠ 0 := by
    unfold Formalism.L2.SG.MassDataConc.kapN
    exact mul_ne_zero (pow_ne_zero _ hrd.ne') (inv_ne_zero (pow_ne_zero _ hb))
  have hM : D.host.rdE ^ (D.R.f * e1 D) *
      ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (D.R.f * ((D.R.rS + 1) * (2 * D.R.rS + 3))) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hrd.ne') (pow_ne_zero _ hb)
  rw [hprod, anum_pow, hMS, hfS]
  field_simp

end Formalism.L2.SG.Pf.Carrier.EnergyConst
end
end

section

namespace Formalism.L2.SG.Pf

open Formalism.BasicNotions

theorem latRowLat {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) : LatRowLat X u :=
  latRowLat_of LatDictZ.lattice_genus X u

theorem latSurj {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) : LatSurj X u :=
  latSurj_of LatDictZ.anisotropic_vector_orbit X u

theorem lattice_steps_hold : LatticeRowBijectionClassFinite := fun _ X hK u =>
  ⟨latRowLat X u, latSurj X u, latInj X u, Formalism.L2.SG.Closed.ClassFin_holds X u hK⟩

end Formalism.L2.SG.Pf
end

section

noncomputable section

open scoped Classical TensorProduct
open Matrix
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace Formalism.L2.SG.Pf.FullLocalDualAgreement

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LocalDualAgreement : Prop :=
  ∀ D : D7, Formalism.L2.SG.Pf.LocCP.LocTied D → ∃ (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Formalism.MainNotions.S.LocalSplitGroups.Agree δ M p) ∧
    ∀ (p : Formalism.MainNotions.S.LocalSplitGroups.PlF D) (i : Fin 2), ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal →
      δ p = (D.s.atP p).ιF (((D.host.g 0 : ℕ) : D.host.F) * ((D.host.g 1 : ℕ) : D.host.F) /
        ((D.host.g i : ℕ) : D.host.F))

theorem locCTied_of (h1 : Formalism.L2.SG.Pf.LocCP.LocDualC) (h2 : Formalism.L2.SG.Pf.LocCP.LocUnramC)
    (h4 : Formalism.L2.SG.Pf.LocCP.LocHaarC) : LocalDualAgreement := fun D hT => by
  obtain ⟨δ, M, hA, hpin⟩ := Formalism.L2.SG.Pf.LocCP.locBody_of D hT h1 h2 Formalism.L2.SG.Pf.LocCP.locPsiContC h4
  exact ⟨δ, M, hA, fun p i hi => hpin p i hi⟩

theorem locCTied_of' (h1 : Formalism.L2.SG.Pf.LocCP.LocDualC) (h4 : Formalism.L2.SG.Pf.LocCP.LocHaarC) : LocalDualAgreement :=
  locCTied_of h1 Formalism.L2.SG.Pf.LocUnramP.locUnramC h4

theorem locDualC_of' (hG : Formalism.L2.SG.Pf.LocCP.LocDualGenC) (hP : Formalism.L2.SG.Pf.LocCP.PinHostC) :
    Formalism.L2.SG.Pf.LocCP.LocDualC :=
  Formalism.L2.SG.Pf.LocCP.locDualC_of hG Formalism.L2.SG.Pf.LocUnramP.locUnramC hP

end Formalism.L2.SG.Pf.FullLocalDualAgreement

namespace Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem fullExists_tied (h1 : TRExistsC) (hR : LatticeRowBijectionClassFinite) (hL : FullLocalDualAgreement.LocalDualAgreement) :
    ∀ (D : D7) (X : HidaSetting D), X.LevelSubgroupCharacter → Formalism.L2.SG.Pf.LocCP.LocTied D → Nonempty (Full X) := by
  intro D X hK hT
  have hRS : RowStepsC := rowStepsC_of (fun D X hK u =>
    let ⟨a2, a3, a4, a5⟩ := hR D X hK u
    ⟨latSub X u, latRow_of X u a2, a3, a4, classFin_of X u hK a5, gamIsom_of X (inclInj_holds X) u⟩)
  obtain ⟨TR, hTR⟩ := h1 D X hK
  have h2 : ∀ u : D.what₂.Word, ∃ what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V), IsRowReps D (X.Fu u) what₂ ∧
      (∀ Λ ∈ what₂, Formalism.L2.SG.Saturated.IsSplitRow D (X.Fu u) Λ) ∧ ∃ cs : ColSys X u what₂, ColReps hK cs := by
    intro u
    obtain ⟨a0, a1, a2, a3, a4, a5, a6⟩ := hRS D X hK u
    exact rowsCols_of X u hK a0 a1 a2 a3 a4 a5 a6
  choose what₂ hrows hsplit cs hcs using h2
  choose Dt hDt using fun u => repsExist X u
  choose FN hFN using fundNC_holds D X hK
  obtain ⟨δ, M, hag, hpin⟩ := hL D hT
  exact ⟨⟨hK, TR, hTR, what₂, hrows, hsplit, cs, hcs, Dt, hDt, FN, hFN, δ, M, hag, hpin⟩⟩

end Formalism.L2.SG.Pf
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LatticeGluingRadicals

namespace Formalism.L2.SG.LeadingMinorsNonvanishing

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem leading_minor_ne_zero {D : D7} {T T' : ℕ} (hT : 0 < T) (F : LFlag (D.sp.Y 0) D.R.rS (T : D.host.E))
    (F' : LFlag (D.sp.Y 0) D.R.rS (T' : D.host.E)) (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z) (hG : Gval F F' ≠ 0) :
    Dr1 F F' ≠ 0 := by
  intro h0
  obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  have h1 := (b_G_pos (p_starConj D) hT F F' hz hz' hG (p_posX D T hT F) τ).1
  rw [b_tauG (p_starConj D) F F' τ, h0, map_zero, norm_zero, Complex.ofReal_re] at h1
  have h2 : (0:ℝ) ≤ (T:ℝ) * T' * ‖τ (Dr F F')‖ ^ 2 := by positivity
  nlinarith

theorem atSomeAll_holds : Formalism.L2.SG.TermTieOf.AtSomeAll := by
  intro D X Y u u' t hG hrel
  obtain ⟨F', ⟨hP, hmk⟩, hR⟩ := hrel
  have hf := Formalism.L2.SG.Closed.TermFun_holds D u u' (X.Fu u) _ ((Y.rowsOK u).1 t.lam t.mem)
  have hGv : Gval (lf D (X.Fu u)) F' ≠ 0 := by
    have e := Formalism.L2.SG.TermDef.Gt_mk hf.1 ⟨F', hP⟩
    rw [hmk] at e
    exact fun h0 => hG (e.trans h0)
  have hTu := tie_Tu_pos D u
  have hTu' := tie_Tu_pos D u'
  have hDr1 : Dl (lf D (X.Fu u)).fl F'.fl (D.R.rS + 1) ≠ 0 :=
    leading_minor_ne_zero hTu (lf D (X.Fu u)) F' rfl hP.1.2 hGv
  have geo := cell_geom D.host.F D.host.E (hS D) D.R.rS _ _ (lf D (X.Fu u)).fl F'.fl (tie_trace D.sp.cm)
    (tie_aniso D _ hTu (lf D (X.Fu u))) (tie_aniso D _ hTu' F') hR
  obtain ⟨p, hp⟩ := cell_of_matRel cell_inv cell_sign cell_bruhat cell_mono cell_point (le_refl (D.R.rS + 1))
    ((Zhat (lf D (X.Fu u)).fl F'.fl).submatrix (Fin.castLE (le_refl (D.R.rS + 1))) (Fin.castLE (le_refl (D.R.rS + 1))))
    (by rw [← tie_Dl_eq']; exact hDr1) (geo (D.R.rS + 1) le_rfl (Or.inr ⟨rfl, hGv⟩))
  refine ⟨p, F', ⟨hP, hmk⟩, hGv, ?_⟩
  obtain ⟨L, U, hL, hU, hZ⟩ := hp
  refine ⟨L, U, hL, hU, ?_⟩
  rw [← hZ]
  funext a b
  first
  | rfl
  | (simp [ZhatOM, ZhatL, Matrix.submatrix_apply]; rfl)

end Formalism.L2.SG.LeadingMinorsNonvanishing

end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf

namespace Formalism.L2.SG.Pf.KernelOfEmbedding

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {Y : Formalism.L2.SG.Full.Full X} {hF : FinX Y} (W : WittDat X)
  (hI : SIso D.s (sOf hF))

theorem tc_pfst {u u' : D.what₂.Word} (p : D.s.Pair u u') : tc hI (D.s.pfst p) = (hI.eP u u' p).1.1 :=
  hI.pfst p

theorem tc_psnd {u u' : D.what₂.Word} (p : D.s.Pair u u') : tc hI (D.s.psnd p) = (hI.eP u u' p).1.2 :=
  hI.psnd p

theorem wRowOf_eq (hW : WRowIso D) {u u' : D.what₂.Word} (p : D.s.Pair u u') :
    wRowOf W hI p = Formalism.MainNotions.S.wRow D (X.Fu u) (hI.eP u u' p).1.1.lam := by
  unfold wRowOf FlagOfWord lamOf
  refine (hW (W.δ u) (W.isom u) (X.Fu u) _).trans ?_
  rw [tc_pfst]

theorem jtOf_eq {u u' : D.what₂.Word} (t : D.s.Term u u') (s : _root_.Formalism.L2.SG.PackageTie2.TT Y u u') (hs : s.toTerm = tc hI t) :
    ∃ g : fib Y (tc hI t), JtOf hI t = amp Y g.1 := by
  have h : ∃ s : _root_.Formalism.L2.SG.PackageTie2.TT Y u u', s.toTerm = tc hI t := ⟨s, hs⟩
  exact ⟨⟨h.choose, h.choose_spec⟩, by unfold JtOf; rw [dite_eq_left h]⟩

theorem pair_form (hW : WRowIso D) (hC : AmpCov Y) (hK : PairAmpConst Y) (hN : FibreCountEq hF)
    (u u' : D.what₂.Word) (p : D.s.Pair u u') :
    ∃ (c : ℂ) (U : X.Vpi u' ≃ₗᵢ[ℂ] X.Vpi u'), ‖c‖ = 1 ∧
      D.s.pval p = (wRowOf W hI p : ℂ) * c *
        Formalism.MainNotions.S.hsInner ((JtOf hI (D.s.pfst p)).comp (cl U)) (JtOf hI (D.s.psnd p)) := by
  have h1 := tc_pfst hI p
  have h2 := tc_psnd hI p
  obtain ⟨g₁, hg₁⟩ := jtOf_eq hI (D.s.pfst p) (hI.eP u u' p).2.choose.1
    ((hI.eP u u' p).2.choose.2.trans h1.symm)
  obtain ⟨g₂, hg₂⟩ := jtOf_eq hI (D.s.psnd p) (hI.eP u u' p).2.choose_spec.choose.1
    ((hI.eP u u' p).2.choose_spec.choose.2.trans h2.symm)
  obtain ⟨c, U, hc, hv⟩ := pvR_form hF hC hK hN (hI.eP u u' p) ⟨g₁.1, g₁.2.trans h1⟩ ⟨g₂.1, g₂.2.trans h2⟩
  refine ⟨c, U, hc, ?_⟩
  rw [hI.pval p, wRowOf_eq W hI hW p, hg₁, hg₂]
  exact hv

theorem pvalForm_exists (hW : WRowIso D) (hC : AmpCov Y) (hK : PairAmpConst Y) (hN : FibreCountEq hF) :
    ∃ A : AmpDat X, PvalForm W hI A := by
  have H := fun (u u' : D.what₂.Word) (p : D.s.Pair u u') => pair_form W hI hW hC hK hN u u' p
  choose c U hc hv using H
  exact ⟨{ chi := fun {u u'} p => c u u' p
           chi_norm := fun {u u'} p => hc u u' p
           piB := fun {u u'} p => cl (U u u' p)
           piB_unit := fun {u u'} p x => (U u u' p).norm_map x },
    fun {u u'} p => hv u u' p⟩

end Formalism.L2.SG.Pf.KernelOfEmbedding
end
end
