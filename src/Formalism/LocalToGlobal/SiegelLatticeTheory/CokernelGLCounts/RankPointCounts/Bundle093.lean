module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataConc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle046
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle070
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle040
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle088
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle085
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle072
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle092
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle006
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle033
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle090
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalInvariants
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle074
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle069
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle091
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle077
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle035

@[expose] public section

section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.MassDataPos

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem glkC_pos (k g : ℕ) (hg : g.Prime) : 0 < glkC k g := by
  haveI : NeZero g := ⟨hg.ne_zero⟩
  unfold glkC
  exact Nat.card_pos

theorem ukC_pos (k g : ℕ) (hg : g.Prime) : 0 < ukC k g := by
  haveI : NeZero g := ⟨hg.ne_zero⟩
  unfold ukC
  exact Nat.card_pos

theorem ggC_pos (r k g : ℕ) (hg : g.Prime) : 0 < ggC r k g := by
  haveI : NeZero g := ⟨hg.ne_zero⟩
  unfold ggC
  exact Nat.card_pos

theorem nnC_pos (r k g : ℕ) (hg : g.Prime) : 0 < nnC r k g := by
  haveI : NeZero g := ⟨hg.ne_zero⟩
  unfold nnC
  rw [Nat.card_pos_iff]
  refine ⟨⟨⟨1, ?_⟩⟩, inferInstance⟩
  unfold Formalism.FourierDecayAlt.S3.IsN
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp only [Formalism.DoubleCosetMeasures.IsUpUni, Formalism.FourierDecayAlt.S3.b11, Formalism.FourierDecayAlt.S3.b33, Formalism.FourierDecayAlt.S3.b22, Formalism.FourierDecayAlt.S3.b21, Formalism.FourierDecayAlt.S3.b31, Formalism.FourierDecayAlt.S3.b32]
       exact ⟨fun i j hij => by simp [Matrix.one_apply, (show j < i from hij).ne'], fun a => by simp [Matrix.one_apply]⟩)
    | (simp [Formalism.FourierDecayAlt.S3.b11, Formalism.FourierDecayAlt.S3.b33, Formalism.FourierDecayAlt.S3.b22, Formalism.FourierDecayAlt.S3.b21, Formalism.FourierDecayAlt.S3.b31, Formalism.FourierDecayAlt.S3.b32, Matrix.one_apply]; done)
    | (ext i j; simp [Formalism.FourierDecayAlt.S3.b11, Formalism.FourierDecayAlt.S3.b33, Formalism.FourierDecayAlt.S3.b22, Formalism.FourierDecayAlt.S3.b21, Formalism.FourierDecayAlt.S3.b31, Formalism.FourierDecayAlt.S3.b32, Matrix.one_apply]; done)

section Main

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

abbrev bk : Formalism.FourierDecayAlt.S3.MassData (TypX X) := bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq

def MassDataPosC : Prop := (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Pos

def LocHaarPosC : Prop :=
  (∀ p, 0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKp p ∧
    0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKnatp p ∧
    0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKppp p ∧
    0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μSp p ∧
    0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μSp' p ∧
    0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μSppp p ∧
    0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μSppp' p) ∧
  0 < (X.measG.μGf (Formalism.L2.SG.Sub.Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)))).toReal ∧
  0 < ((X.measW u).μSf (Subtype.val ⁻¹' (Formalism.L2.SG.Sub.Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :
      Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))).toReal ∧
  0 < ((X.measW u').μSf (Subtype.val ⁻¹' (Formalism.L2.SG.Sub.Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :
      Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))).toReal ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μH ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μH' ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μHpp ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μHpp' ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μN ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μN'

def CovolPosC : Prop :=
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volG ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volHa ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volHa' ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volNa ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volNa' ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volB

def QuotVolPosC : Prop :=
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volH ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volH' ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN'

def RecPosC : Prop :=
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).deg ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).dimπ ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).dimπ' ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).ρ0 ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).ρ0' ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).d ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).d'

theorem gOf_prime (p : TypX X) : (gOf p).Prime := by
  unfold gOf
  split_ifs
  · exact D.host.g_prime 0
  · exact D.host.g_prime 1

theorem massDataPosC_of (hL : LocHaarPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (hCv : CovolPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (hQv : QuotVolPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (hR : RecPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (hP : Formalism.L2.SG.LocVol.ProdConv X u u' ψ) (hCoo : 0 < Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1)
    (hκ : 0 < Formalism.L2.SG.MassDataConc.kapN D) (hsd : 0 ≤ sd) (hC : 0 ≤ C) (hTh : 0 < Th) :
    MassDataPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq := by
  obtain ⟨hv, -, -, -, hUo, -, hZZ, hPP, -, hal, -⟩ := hP
  obtain ⟨hloc, hGf, hSf, hSf', hH, hH', hHpp, hHpp', hN, hN'⟩ := hL
  obtain ⟨hG, hHa, hHa', hNa, hNa', hB⟩ := hCv
  obtain ⟨hvH, hvH', hvN, hvN'⟩ := hQv
  obtain ⟨hdeg, hdp, hdp', hr0, hr0', hd, hd'⟩ := hR
  set B := bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq with hBdef
  have hMp : ∀ p, 0 < B.Mp p := fun p => (hv p.1).1 p.2
  have hU00p : ∀ p, 0 < B.localVolumeAtPlace p := fun p => (hv p.1).2.1
  have hKo : 0 < B.μKo := div_pos hGf (Finset.prod_pos fun p _ => (hloc p).1)
  have hSo : 0 < B.μSo := div_pos hSf (Finset.prod_pos fun p _ => (hloc p).2.2.2.1)
  have hSo' : 0 < B.μSo' := div_pos hSf' (Finset.prod_pos fun p _ => (hloc p).2.2.2.2.1)
  have hU00o : 0 < B.localVolumeArchimedean := hUo
  have hMo : 0 < B.Mo := div_pos (mul_pos hU00o (pow_pos hKo 2)) (mul_pos hSo hSo')
  have hZ : 0 < B.volZZ := hZZ
  have hPPp : 0 < B.volPP := by
    show 0 < ∏ l : Fin (D.R.rS + 1), ∏' v : Formalism.L2.SG.LocVol.PlX X, Formalism.L2.SG.LocVol.PPX X u u' ψ l v
    exact Finset.prod_pos fun l _ => (hPP l).2
  have hAl : 0 < B.al := mul_pos (Finset.prod_pos fun p _ => (hv p.1).2.2.2.2) hal
  have hCo : 0 < B.Coo := mul_pos hκ hCoo
  have hMM : 0 < B.MM := mul_pos hMo (Finset.prod_pos fun p _ => hMp p)
  have hμK : 0 < B.μK := mul_pos hKo (Finset.prod_pos fun p _ => (hloc p).1)
  have hAA : 0 < B.AA := div_pos (mul_pos (mul_pos hB hCo) (div_pos hMM hZ)) hμK
  have hn0c : 0 < B.n0c := div_pos hAA hr0
  have hgp : ∀ p, 0 < B.g p := fun p => by
    show (0 : ℝ) < ((gOf p : ℕ) : ℝ)
    exact_mod_cast (gOf_prime X p).pos
  have hglk : ∀ p, 0 < B.glk p := fun p => by
    show (0 : ℝ) < ((glkC D.R.k (gOf p) : ℕ) : ℝ)
    exact_mod_cast glkC_pos _ _ (gOf_prime X p)
  have huk : ∀ p, 0 < B.uk p := fun p => by
    show (0 : ℝ) < ((ukC D.R.k (gOf p) : ℕ) : ℝ)
    exact_mod_cast ukC_pos _ _ (gOf_prime X p)
  have hnn : ∀ p, 0 < B.nn p := fun p => by
    show (0 : ℝ) < ((nnC D.R.rS D.R.k (gOf p) : ℕ) : ℝ)
    exact_mod_cast nnC_pos _ _ _ (gOf_prime X p)
  have hgg : ∀ p, 0 < B.gg p := fun p => by
    show (0 : ℝ) < ((ggC D.R.rS D.R.k (gOf p) : ℕ) : ℝ)
    exact_mod_cast ggC_pos _ _ _ (gOf_prime X p)
  have hδ : 0 ≤ B.δ := by
    show 0 ≤ C * ((D.R.rS : ℝ) + 1) * (C / Th) ^ (Fintype.card (NumberField.InfinitePlace X.B.I.F))
    exact mul_nonneg (mul_nonneg hC (by positivity)) (pow_nonneg (div_nonneg hC hTh.le) _)
  unfold MassDataPosC Formalism.FourierDecayAlt.S3.MassData.Pos
  exact ⟨fun p => ⟨hgp p, hglk p, huk p, hnn p, hgg p, (hloc p).1, (hloc p).2.1, (hloc p).2.2.1, (hloc p).2.2.2.1,
      (hloc p).2.2.2.2.1, (hloc p).2.2.2.2.2.1, (hloc p).2.2.2.2.2.2, hMp p, hU00p p⟩,
    hKo, hSo, hSo', hMo, hU00o, hH, hH', hHpp, hHpp', hN, hN', hZ, hPPp, hAl, hG, hHa, hHa', hNa, hNa', hB, hvH, hvH',
    hvN, hvN', hCo, hdeg, hdp, hdp', hr0, hr0', hd, hd', hn0c, hsd, hδ⟩

end Main

theorem cooOf_pos {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) : 0 < Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 := by
  have h := Formalism.L2.SG.RealObj.InfCut.ProductExactness.haar_disintegration_real_holds D X u u' 1 one_pos
  have h' : ∃ C, 0 < C ∧ Formalism.L2.SG.RealObj.Disint X u u' 1 C := h
  unfold Formalism.L2.SG.RealObj.DisintegrationConstant
  rw [dite_eq_left h']
  exact h'.choose_spec.1

theorem quotVolPosC_of {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Formalism.L2.SG.Full.Full X)
    (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
    {F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
    (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hK2 : X.LevelSubgroupNormalized) (hV : 0 < X.volK2) :
    QuotVolPosC X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq := by
  obtain ⟨hN, hH⟩ := Formalism.L2.SG.Closed.VolPosC_holds D X Y u hK2
  obtain ⟨hN', hH'⟩ := Formalism.L2.SG.Closed.VolPosC_holds D X Y u' hK2
  refine ⟨hH, hH', ?_, ?_⟩
  · show 0 < ((X.muN u) (Y.FN u)).toReal
    exact pos_of_mul_pos_right hN hV.le
  · show 0 < ((X.muN u') (Y.FN u')).toReal
    exact pos_of_mul_pos_right hN' hV.le

end Formalism.L2.SG.Pf.MassDataPos
end
end

section

noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.BlockPermutation Formalism.L2.SG.Pf.StabIntSh

namespace Formalism.L2.SG.Pf.StabIntLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (w : Point D.host.E (D.R.rS + 1))

def coordX (X : MatR D) : FreeE w → D.host.E := fun q => X q.1.1 q.1.2

theorem Xmat_coordX {X : MatR D} (hU : UpU X) (hB : IsBlockDiagonalMatrix w X) : Xmat w (coordX w X) = X := by
  funext a c
  by_cases h : a = c
  · subst h; simp [Xmat, (hU a a).2 rfl]
  · simp only [Xmat, h, if_false]
    by_cases h2 : a < c ∧ blkOf w.1 a.val = blkOf w.1 c.val
    · rw [dite_eq_left h2]; rfl
    · rw [dite_eq_right h2]
      by_cases h3 : a < c
      · exact (hB a c (fun e => h2 ⟨h3, e⟩)).symm
      · exact ((hU a c).1 (lt_of_le_of_ne (not_lt.1 h3) (Ne.symm h))).symm

theorem coordX_Xmat (y : FreeE w → D.host.E) : coordX w (Xmat w y) = y := by
  funext q; exact Xmat_q w y q

theorem mem_stabInt_iff_twist (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (hA : ∀ p, Agree δ M p) (hodd : Odd (gS D))
    (u u' : D.what₂.Word) (β : GLR D) (hβ : IsLoUni (β : MatR D)) {b : MatR D} (hb : IsUpUni b)
    (hW : (β : MatR D) * ptMat w * b = ptMat w) :
    β ∈ stabInt D u u' δ M w ↔
      ∀ q, coordX w ((ptMat w)⁻¹ * (β : MatR D) * ptMat w) q -
        τA w q (coordX w ((ptMat w)⁻¹ * (β : MatR D) * ptMat w)) ∈ Λq w q := by
  obtain ⟨-, hU, hB⟩ := X_of_st w hβ hb hW
  rw [mem_stabInt_iff_X δ M hA u u' w β hβ hb hW, ← Xmat_coordX w hU hB, coordX_Xmat]
  exact twistC δ M hA hodd w _

theorem exists_of_coord (y : FreeE w → D.host.E) :
    ∃ β : GLR D, IsLoUni (β : MatR D) ∧ IsUpUni (Xmat w y)⁻¹ ∧
      (β : MatR D) * ptMat w * (Xmat w y)⁻¹ = ptMat w ∧ (ptMat w)⁻¹ * (β : MatR D) * ptMat w = Xmat w y := by
  obtain ⟨hlo, hXi, hW, hdet⟩ := st_of_X w (Xmat_upU w y) (Xmat_blk w y)
  set B := ptMat w * Xmat w y * (ptMat w)⁻¹
  have hd : IsUnit B.det := by rw [hdet]; exact isUnit_one
  refine ⟨⟨B, B⁻¹, Matrix.mul_nonsing_inv B hd, Matrix.nonsing_inv_mul B hd⟩, hlo, hXi, hW, ?_⟩
  have hu := ptMat_isUnit w
  show (ptMat w)⁻¹ * (ptMat w * Xmat w y * (ptMat w)⁻¹) * ptMat w = Xmat w y
  rw [show (ptMat w)⁻¹ * (ptMat w * Xmat w y * (ptMat w)⁻¹) * ptMat w =
      ((ptMat w)⁻¹ * ptMat w) * Xmat w y * ((ptMat w)⁻¹ * ptMat w) by simp only [Matrix.mul_assoc],
    Matrix.nonsing_inv_mul _ hu, Matrix.one_mul, Matrix.mul_one]

theorem hpr_lt {p q : FreeE w} (h : hgt w q < hgt w p) : hpr w q < hpr w p := by
  unfold hpr; split_ifs <;> omega

theorem trunc_eq {y y' : FreeE w → D.host.E} (q : FreeE w) (h : ∀ p, hpr w p < hpr w q → y p = y' p) :
    trunc w y (hgt w q) = trunc w y' (hgt w q) := by
  funext p
  unfold trunc
  split_ifs with hp
  · exact h p (hpr_lt w hp)
  · rfl

theorem τA_lowdep (q : FreeE w) {y y' : FreeE w → D.host.E} (h : ∀ p, hpr w p < hpr w q → y p = y' p) :
    τA w q y = τA w q y' := by
  unfold τA
  by_cases h1 : selfP w q
  · simp only [h1, if_true, cf, trunc_eq w q h]
  · by_cases h2 : upperM w q
    · obtain ⟨hp1, hp2⟩ := upper_qbar w h2
      have hlt : hpr w (qbar w q) < hpr w q := by
        unfold hpr; rw [hgt_qbar]; simp only [h2, hp2, if_true, if_false]; omega
      have hc : cf w y (qbar w q) = cf w y' (qbar w q) := by
        unfold cf
        rw [trunc_eq w (qbar w q) (fun p hp => h p (lt_trans hp hlt))]
      simp only [h1, h2, if_false, if_true, h _ hlt, hc]
    · simp only [h1, h2, if_false]

end Formalism.L2.SG.Pf.StabIntLat
end
end

section

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

open Formalism.MainNotions.S.LocalSplitGroups

theorem LiftOrb_holds : LiftOrb := liftOrb_of RF.srLift_holds

theorem GaPlusTh_holds {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) : GaPlusTh M δ u u' :=
  gaPlusTh_of LiftOrb_holds M δ u u'

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (p : PlF D)

def tauU : UP p →* UP p where
  toFun x := ⟨tau p x, tau_mem_UP p x.2⟩
  map_one' := by ext1; exact (tau p).map_one
  map_mul' x y := by ext1; exact (tau p).map_mul x y

theorem tauU_tauU (x : UP p) : tauU p (tauU p x) = x := by
  ext1; exact tau_tau p x

def piU (πa : UP p →* UP p) : UP p →* UP p := (tauU p).comp (πa.comp (tauU p))

def piG (πa : UP p →* UP p) (x : GG p) : GG p :=
  if h : x ∈ UP p then ((piU p πa ⟨x, h⟩ : UP p) : GG p) else 1

theorem piG_of (πa : UP p →* UP p) (x : UP p) : piG p πa x = ((piU p πa x : UP p) : GG p) := by
  unfold piG; rw [dite_eq_left x.2]

theorem mem_StP_iff (x : GG p) :
    x ∈ StP M δ u u' w p ↔ x ∈ UP p ∧ x • Y0 M δ u u' w p = Y0 M δ u u' w p :=
  ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩

theorem fixes_base_iff (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (hB : BaseAt M δ u u' w p a) (x : UP p) :
    (x : GG p) • Y0 M δ u u' w p = Y0 M δ u u' w p ↔ ((tauU p x : UP p) : GG p) • a.mat = a.mat := by
  rw [← (hB.choose_spec.2 (tauU p x))]
  constructor
  · intro h
    show tau p x • _ = _
    rw [← phi_smul p δ _ _ w x.2, h]
  · intro h
    apply phi_inj p δ (D.mem u).A.T (D.mem u').A.T w
    rw [phi_smul p δ _ _ w x.2]
    exact h

theorem retr_of (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (πa : UP p →* UP p)
    (hD : CountAb.Data (a.mat) (MulAction.stabilizer (UP p) a.mat) πa.ker (KU M p) πa)
    (hB : BaseAt M δ u u' w p a) :
    Formalism.L2.SG.Pf.ProdEP2Core.Retr (StP M δ u u' w p) (UP p) (piG p πa) := by
  refine ⟨fun x hx => ((mem_StP_iff M δ u u' w p x).1 hx).1, fun x hx y hy => ?_, fun x hx => ?_, fun s hs => ?_⟩
  · have ex : piG p πa x = ((piU p πa ⟨x, hx⟩ : UP p) : GG p) := piG_of p πa ⟨x, hx⟩
    have ey : piG p πa y = ((piU p πa ⟨y, hy⟩ : UP p) : GG p) := piG_of p πa ⟨y, hy⟩
    have exy : piG p πa (x * y) = ((piU p πa (⟨x, hx⟩ * ⟨y, hy⟩) : UP p) : GG p) :=
      piG_of p πa (⟨x, hx⟩ * ⟨y, hy⟩)
    rw [exy, ex, ey, map_mul]
    rfl
  · rw [show x = ((⟨x, hx⟩ : UP p) : GG p) from rfl, piG_of]
    refine (mem_StP_iff M δ u u' w p _).2 ⟨(piU p πa ⟨x, hx⟩).2, ?_⟩
    rw [fixes_base_iff M δ u u' w p a hB]
    have h1 : tauU p (piU p πa ⟨x, hx⟩) = πa (tauU p ⟨x, hx⟩) := by
      simp only [piU, MonoidHom.comp_apply, tauU_tauU]
    rw [h1]
    exact hD.mem _
  · obtain ⟨hsU, hsY⟩ := (mem_StP_iff M δ u u' w p s).1 hs
    rw [show s = ((⟨s, hsU⟩ : UP p) : GG p) from rfl, piG_of]
    have hfix : tauU p ⟨s, hsU⟩ ∈ MulAction.stabilizer (UP p) a.mat :=
      (fixes_base_iff M δ u u' w p a hB ⟨s, hsU⟩).1 hsY
    have h2 : piU p πa ⟨s, hsU⟩ = ⟨s, hsU⟩ := by
      simp only [piU, MonoidHom.comp_apply, hD.id _ hfix, tauU_tauU]
    rw [h2]

end Formalism.L2.SG.Pf.CountAt
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) {p : PlF D}
  (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (πa : UP p →* UP p)
  (hker : ∀ x : UP p, πa x = 1 ↔ ((x : GG p).1 : GLp p).val ∈ Va p a) (g : UP p)

theorem fC_inj : Function.Injective (fC M a πa hker g) := by
  intro X Y hXY
  induction X using Quotient.inductionOn with
  | h x =>
    induction Y using Quotient.inductionOn with
    | h y =>
      apply Quotient.sound
      obtain ⟨⟨l, hl, e1⟩, ⟨ρ, hρ, e2⟩⟩ := Quotient.exact hXY
      have e1' : (((y : UP p) : GG p).1 : GLp p).val = l * (((x : UP p) : GG p).1 : GLp p).val := e1
      have e2' : ((((y : UP p) : GG p).2.unop : GLp p)).val = ((((x : UP p) : GG p).2.unop : GLp p)).val * ρ := e2
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · show Formalism.MainNotions.S.TieN.IntLow (M p) ((((y : UP p) * (x : UP p)⁻¹ : UP p) : GG p).1 : GLp p).val
        rw [first_value_mul]
        have : (((((x : UP p)⁻¹ : UP p) : GG p).1 : GLp p)).val * (((x : UP p) : GG p).1 : GLp p).val = 1 := by
          rw [← first_value_mul, inv_mul_cancel]; rfl
        rw [e1', Matrix.mul_assoc]
        rw [show (((x : UP p) : GG p).1 : GLp p).val * (((((x : UP p)⁻¹ : UP p) : GG p).1 : GLp p)).val = 1 by
          rw [← first_value_mul, mul_inv_cancel]; rfl, Matrix.mul_one]
        exact hl
      · show Formalism.MainNotions.S.TieN.IntUp (M p) (((((y : UP p) * (x : UP p)⁻¹ : UP p) : GG p).2.unop : GLp p)).val
        rw [second_value_mul, e2', ← Matrix.mul_assoc]
        rw [show ((((((x : UP p)⁻¹ : UP p) : GG p).2.unop : GLp p))).val *
            ((((x : UP p) : GG p).2.unop : GLp p)).val = 1 by rw [← second_value_mul, mul_inv_cancel]; rfl, Matrix.one_mul]
        exact hρ
      · show (y : UP p) * (x : UP p)⁻¹ ∈ πa.ker
        rw [MonoidHom.mem_ker, map_mul, map_inv, MonoidHom.mem_ker.1 x.2.1, MonoidHom.mem_ker.1 y.2.1, inv_one,
          mul_one]

end Formalism.L2.SG.Pf.CountAt
end
end

section

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

theorem NmlInv_holds : Formalism.L2.SG.NGCut.NormalInvariants.NmlInv :=
  nmlInv_of NmlLine_holds Formalism.L2.SG.NGCut.NormalIntegrality.NmlInt_holds NmlSep_holds

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
