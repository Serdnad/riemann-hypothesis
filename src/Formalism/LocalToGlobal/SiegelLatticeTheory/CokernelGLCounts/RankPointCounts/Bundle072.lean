module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle065
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle009
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilySeparationBound
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FiberCount
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqClass
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle035
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle066
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut
  Formalism.L2.SG.Pf.MainEqAna

namespace Formalism.L2.SG.Pf.MainEqLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LocalInputLeG {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁) {E : Type} [Field E] {r : ℕ}
    {Cl Nu : Type} (N : PN.NGData τ E r Cl Nu) (C1 C0 : ℕ) (AAre : ℝ) : Prop :=
  ∀ γ, PN.IsPt X N γ → ∀ S : Finset (Cl × Nu), ∃ L : PN.LocalNG Cl Nu, L.Basic ∧ ZAt L C1 r ∧
    L.MassRatioAt C0 r ∧ L.Unfold ∧ (∀ x ∈ S, N.a2 x.1 γ x.2 = weightedGenericAmplitudeSq L x.1 x.2) ∧ N.Hh γ = L.Htot ∧
    0 < L.ngenTot ∧ L.ngenTot ≤ AAre * 2 * N.Hh γ ^ PN.eN r * N.n γ

theorem localInputG_of_le {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁) {E : Type} [Field E] {r : ℕ}
    {Cl Nu : Type} (N : PN.NGData τ E r Cl Nu) (C1 C0 : ℕ) (AAre : ℝ) (h : LocalInputLeG X N C1 C0 AAre)
    (hng : ∀ γ, N.ngen γ = AAre * 2 * N.Hh γ ^ PN.eN r * N.n γ) : LocalInputG X N C1 C0 := by
  intro γ hγ S
  obtain ⟨L, hB, hZ, hM, hU, ha, hH, hpos, hle⟩ := h γ hγ S
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = AAre * 2 * N.Hh γ ^ PN.eN r * N.n γ / L.ngenTot := ⟨_, rfl⟩
  have hc1 : 1 ≤ c := by
    rw [hc, le_div_iff₀ hpos, one_mul]
    exact hle
  have hV0 : 0 ≤ L.V0 := hB.2.2.2.2.2.1
  refine ⟨{ L with V0 := L.V0 * c }, ?_, hZ, hM, ?_, ?_, hH, ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hB
    unfold Formalism.FourierDecayAlt.PN.LocalNG.Basic
    exact ⟨h1, h2, h3, h4, h5, mul_nonneg h6 (by linarith), h7⟩
  · intro d S' hS'
    have h0 := hU d S' hS'
    have hw : 0 ≤ L.V0 * ∏ p, L.wt p (d p) :=
      mul_nonneg hV0 (Finset.prod_nonneg fun p _ => hB.1 p (d p))
    calc ∑ x ∈ S', L.rw x.1 ≤ L.V0 * ∏ p, L.wt p (d p) := h0
      _ ≤ L.V0 * c * ∏ p, L.wt p (d p) := by nlinarith
  · intro x hx
    rw [ha x hx]
    first
      | rfl
      | (unfold Formalism.L2.SG.Pf.MainEqCut.weightedGenericAmplitudeSq Formalism.L2.SG.Pf.MainEqCut.ampGen; rfl)
      | (cases hd : L.dat x.1 x.2 <;> simp [Formalism.L2.SG.Pf.MainEqCut.weightedGenericAmplitudeSq, Formalism.L2.SG.Pf.MainEqCut.ampGen, hd])
  · show N.ngen γ = L.V0 * c * ∏ p, L.ngen p
    rw [hng γ]
    have e : L.ngenTot = L.V0 * ∏ p, L.ngen p := rfl
    have hne : L.ngenTot ≠ 0 := hpos.ne'
    rw [show L.V0 * c * ∏ p, L.ngen p = L.ngenTot * c by rw [e]; ring, hc, mul_div_assoc',
      mul_div_cancel_left₀ _ hne]

def StepLocPinnedG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C1 C0n : ℕ, ∃ CSt : ℝ, 0 ≤ CSt ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ ν, Pinned X u u ν →
      ∃ s : X.B.I.Ginf → NNReal,
        (∀ γ, Formalism.L2.SG.RealObj.RegX X u u γ → s γ = 1) ∧ (∀ γ, 0 < s γ) ∧
        (∀ γ, (s γ : ℝ) ^ 2 ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f)) ∧
        LocalInputLeG (genT (Y.tO u u)) (NOfG Y u (sc s ν) ν (fun _ => 0)) C1 C0n
          (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq).AA)

end Formalism.L2.SG.Pf.MainEqLoc

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.MainEqLoc

theorem stepLocGenPinnedG_of_loc (h : StepLocPinnedG) : StepLocGenPinnedG := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C1, C0n, CSt, hCSt, C'₀, Cl₀, H⟩ := h Cg cb Cw cT CT C0
  refine ⟨C1, C0n, CSt, hCSt, C'₀, Cl₀, ?_⟩
  intro C' Cl hC' hCl D large₂ X Y u hctx hb X0 ψ hbt sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hok ν hpin
  obtain ⟨s, hs1, hs2, hs3, hloc⟩ :=
    H C' Cl hC' hCl D large₂ X Y u hctx hb X0 ψ hbt sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hok ν hpin
  let AAre : ℝ := PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq).AA
  let N0 := NOfG Y u (sc s ν) ν (fun _ => 0)
  let ng : PN.Pts D.host.E D.R.rS → ℝ := fun γ => AAre * 2 * N0.Hh γ ^ PN.eN D.R.rS * N0.n γ
  refine ⟨s, ng, 2, hs1, hs2, hs3, by norm_num, le_refl _, ?_, ?_⟩
  · exact localInputG_of_le _ _ C1 C0n AAre hloc (fun γ => rfl)
  · intro γ _
    refine ⟨?_, le_refl _⟩
    change 0 ≤ Formalism.L2.SG.RowsConc.nPt _ _ _ γ
    unfold Formalism.L2.SG.RowsConc.nPt
    apply Finset.prod_nonneg
    intro w _
    apply mul_nonneg
    · exact pow_nonneg (mul_nonneg (inv_nonneg.2 (Even.pow_nonneg (Even.mul_right (even_two_mul _) _) _))
        (w.1.nonneg _)) _
    · apply Finset.prod_nonneg
      intro a _
      exact Even.pow_nonneg (Even.mul_right (even_two_mul _) _) _

end Formalism.L2.SG.Pf
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.PCount

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

theorem shUnit_holds (D : Formalism.BasicNotions.D7) : ShUnit D := by
  intro p c
  haveI : CharZero (D.s.atP p).Fp := (D.s.atP p).char0
  haveI : Module.Free (D.s.atP p).Fp (D.s.atP p).Ep := (D.s.atP p).free
  haveI : FiniteDimensional (D.s.atP p).Fp (D.s.atP p).Ep :=
    Module.finite_of_finrank_pos (by rw [(D.s.atP p).rank]; norm_num)
  by_contra hcon
  simp only [not_exists] at hcon
  let f : Module.End (D.s.atP p).Fp (D.s.atP p).Ep := LinearMap.mulLeft (D.s.atP p).Fp c
  have hev : ∀ n : Fin 3, ∃ y : (D.s.atP p).Ep, f.HasEigenvector (-(((n : ℕ) : (D.s.atP p).Fp))) y := by
    intro n
    have hnu := hcon n
    have hni : ¬ Function.Injective
        (LinearMap.mulLeft (D.s.atP p).Fp (c + (((n : ℕ)) : (D.s.atP p).Ep))) := by
      intro hinj
      obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.1 hinj) 1
      exact hnu (isUnit_iff_exists_inv.2 ⟨y, hy⟩)
    rw [← LinearMap.ker_eq_bot, ← ne_eq, Submodule.ne_bot_iff] at hni
    obtain ⟨y, hyk, hy0⟩ := hni
    refine ⟨y, ?_, hy0⟩
    rw [Module.End.mem_eigenspace_iff]
    have h1 : (c + (((n : ℕ)) : (D.s.atP p).Ep)) * y = 0 := hyk
    rw [add_mul] at h1
    show c * y = _
    rw [eq_neg_of_add_eq_zero_left h1, neg_smul, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  choose y hy using hev
  have hinj : Function.Injective (fun n : Fin 3 => -(((n : ℕ) : (D.s.atP p).Fp))) := fun a b h => by
    have h' : ((a : ℕ) : (D.s.atP p).Fp) = ((b : ℕ) : (D.s.atP p).Fp) := neg_inj.1 h
    exact Fin.ext (Nat.cast_injective h')
  have hli := Module.End.eigenvectors_linearIndependent' f _ hinj y hy
  have hc := hli.fintype_card_le_finrank
  rw [Fintype.card_fin, (D.s.atP p).rank] at hc
  omega

theorem partnerCount_of_integral {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (hT2 : Formalism.MainNotions.ThinScalesBound.T2 D) (hI : IntGenP Zd)
    (hB : BridgeBA) : PartnerIsomorphismCount Zd :=
  partnerCount_of_shUnit Zd hT2 hI (shUnit_holds D) hB

end Formalism.L2.SG.Pf.PCount
end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs Formalism.L2.SG.NGCut
  Formalism.L2.SG.NGData

namespace Formalism.L2.SG.NGHTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def nDelta {E : Type} [Field E] (r : ℕ) (γ : PN.Pts E r) : ℕ :=
  r * (r + 1) + ∑ a : Fin γ.1.length, endIdx γ a * (2 * r + 1 - endIdx γ a)

def HTPlace : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ {Cl' Nu : Type} (TS : Set (TauC Y u u')) (cls : TauC Y u u' → Cl') (nml : TauC Y u u' → Nu)
        (γ : PN.Pts D.host.E D.R.rS) (Fm : LocFam (zOf Y) Cl' Nu), FamTie TS cls nml γ Fm →
        (GPt ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ ≠ 0 ∧ ∀ a, endMin γ a ≠ 0) ∧ ∀ p : PlF D,
        ((Fm.FP p).PrimeTo → (Fm.FP p).Hp = 1) ∧
        (Fm.FP p).Hp =
          ((zOf Y).M p).modK (algebraMap _ _ (LocNG.theta ((zOf Y).M p))) ^ ((2 * D.R.rS + 1 : ℝ) / 2) *
          ((zOf Y).M p).modK (algebraMap _ _ ((zOf Y).δ p)) ^ (nDelta D.R.rS γ : ℝ) *
          ((zOf Y).M p).modK ((D.s.atP p).ιE (GPt ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ)) ^ (-(1 / 2 : ℝ)) *
          ∏ a : Fin γ.1.length, (((zOf Y).M p).modK ((D.s.atP p).ιE (endMin γ a)))⁻¹

def HTDelta : Prop :=
  ∀ (D : D7) (Z : LocDat D),
    (Function.mulSupport fun p : PlF D => (Z.M p).modK (algebraMap _ _ (Z.δ p))).Finite ∧
    ∏ᶠ p : PlF D, (Z.M p).modK (algebraMap _ _ (Z.δ p)) =
      (D.host.rdE ^ (2 * Fintype.card (InfinitePlace D.host.E)))⁻¹

def HTTheta : Prop :=
  ∀ (D : D7) (Z : LocDat D),
    (Function.mulSupport fun p : PlF D => (Z.M p).modK (algebraMap _ _ (LocNG.theta (Z.M p)))).Finite ∧
    ∏ᶠ p : PlF D, (Z.M p).modK (algebraMap _ _ (LocNG.theta (Z.M p))) =
      (((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) ^ (2 * Fintype.card (InfinitePlace D.host.E)))⁻¹

section Asm

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem prod_inf_sq (x : E) : ∏ w : InfinitePlace E, w x ^ 2 = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  rw [← Rat.cast_abs, ← InfinitePlace.prod_eq_abs_norm]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [(IsTotallyComplex.isComplex w).mult_eq_two]

theorem prod_inf (x : E) : ∏ w : InfinitePlace E, w x = Real.sqrt |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  rw [← prod_inf_sq, Finset.prod_pow, Real.sqrt_sq (Finset.prod_nonneg fun w _ => (w.1.nonneg x))]

theorem g_pow (g : ℝ) (hg : 0 < g) (f r : ℕ) :
    ((g ^ (2 * f))⁻¹) ^ ((2 * r + 1 : ℝ) / 2) = (g ^ ((2 * r + 1) * f))⁻¹ := by
  rw [Real.inv_rpow (by positivity), ← Real.rpow_natCast g (2 * f), ← Real.rpow_mul hg.le, ← Real.rpow_natCast g]
  congr 2
  push_cast
  ring

theorem inv_rpow_half (x : ℝ) (hx : 0 ≤ x) : (x⁻¹) ^ (-(1 / 2 : ℝ)) = Real.sqrt x := by
  rw [Real.inv_rpow hx, Real.rpow_neg hx, inv_inv, Real.sqrt_eq_rpow]

theorem hpt_eq [StarRing E] (r : ℕ) (γ : PN.Pts E r) (rd g : ℝ) (hg : 0 < g) (TT : ℕ) :
    HPt rd g TT γ =
      ((g ^ (2 * Fintype.card (InfinitePlace E)))⁻¹) ^ ((2 * r + 1 : ℝ) / 2) *
      ((rd ^ (2 * Fintype.card (InfinitePlace E)))⁻¹) ^ (nDelta r γ : ℝ) *
      (|((Algebra.norm ℚ (GPt TT γ) : ℚ) : ℝ)|⁻¹) ^ (-(1 / 2 : ℝ)) *
      ∏ a : Fin γ.1.length, (|((Algebra.norm ℚ (endMin γ a) : ℚ) : ℝ)|⁻¹)⁻¹ := by
  set f := Fintype.card (InfinitePlace E) with hf
  rw [g_pow g hg f r, inv_rpow_half _ (abs_nonneg _), Real.rpow_natCast]
  simp only [inv_inv]
  unfold HPt NGPt NDPt
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← hf, prod_inf]
  have hD : ∀ a : Fin γ.1.length, ∏ w : InfinitePlace E,
      (rd ^ (2 * (endIdx γ a * (2 * r + 1 - endIdx γ a))))⁻¹ * w (endMin γ a) ^ 2 =
      ((rd ^ (2 * (endIdx γ a * (2 * r + 1 - endIdx γ a))))⁻¹) ^ f * |((Algebra.norm ℚ (endMin γ a) : ℚ) : ℝ)| := by
    intro a
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← hf, prod_inf_sq]
  simp_rw [hD]
  rw [Finset.prod_mul_distrib]
  have hrd : ((rd ^ (2 * r * (r + 1)))⁻¹) ^ f *
      ∏ a : Fin γ.1.length, ((rd ^ (2 * (endIdx γ a * (2 * r + 1 - endIdx γ a))))⁻¹) ^ f =
      ((rd ^ (2 * f))⁻¹) ^ nDelta r γ := by
    simp only [← inv_pow, ← pow_mul, Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum, ← mul_inv, ← pow_add]
    congr 2
    unfold nDelta
    have e : ∀ i : Fin γ.1.length, 2 * (endIdx γ i * (2 * r + 1 - endIdx γ i)) * f =
        2 * f * (endIdx γ i * (2 * r + 1 - endIdx γ i)) := fun i => by ring
    simp only [e, ← Finset.mul_sum]
    ring
  rw [← hrd]
  ring

end Asm

section Main

open Formalism.MainNotions.S.LocNG

theorem hTie_of (hP : HTPlace) (hD : HTDelta) (hT : HTTheta) : Formalism.L2.SG.FamDefs.HTie := by
  intro Cg cb Cw cT CT C0
  obtain ⟨a0, b0, hP2⟩ := hP Cg cb Cw cT CT C0
  refine ⟨a0, b0, ?_⟩
  intro C' Cl e1 e2 D large₂ X Y u u' hc Cl' Nu TS cls nml γ Fm hFT
  obtain ⟨⟨hG0, hD0⟩, hloc⟩ := hP2 C' Cl e1 e2 D large₂ X Y u u' hc TS cls nml γ Fm hFT
  haveI : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  obtain ⟨w, F00, F'0, F'1, hw, -, -, -, -, -, -, hgood, -⟩ := hFT
  have hOK : ∀ p, ((zOf Y).M p).OK := fun p => ((zOf Y).agree p).1
  have hPF := (product_formula_e D.host.F D.host.E _ (Formalism.MainNotions.BridgeLemma.szf_finrankFE D) D.s.atP).1 (zOf Y).M hOK
  obtain ⟨hAf, hAv⟩ := hT D (zOf Y)
  obtain ⟨hBf, hBv⟩ := hD D (zOf Y)
  obtain ⟨hCf, hCv⟩ := hPF _ hG0
  have hDf := fun a => hPF _ (hD0 a)
  classical
  set S : Finset (PlF D) := Fm.P ∪ hAf.toFinset ∪ hBf.toFinset ∪ hCf.toFinset ∪
    Finset.univ.biUnion (fun a => (hDf a).1.toFinset) with hS
  have hPS : Fm.P ⊆ S := fun p hp => by simp [hS, hp]
  have hsA : (Function.mulSupport fun p : PlF D =>
      ((zOf Y).M p).modK (algebraMap _ _ (LocNG.theta ((zOf Y).M p)))) ⊆ ↑S := fun p hp => by
    simp [hS, Set.Finite.mem_toFinset, hp]
  have hsB : (Function.mulSupport fun p : PlF D => ((zOf Y).M p).modK (algebraMap _ _ ((zOf Y).δ p))) ⊆ ↑S :=
    fun p hp => by simp [hS, Set.Finite.mem_toFinset, hp]
  have hsC : (Function.mulSupport fun p : PlF D =>
      ((zOf Y).M p).modK ((D.s.atP p).ιE (GPt ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ))) ⊆ ↑S :=
    fun p hp => by simp [hS, Set.Finite.mem_toFinset, hp]
  have hsD : ∀ a, (Function.mulSupport fun p : PlF D => ((zOf Y).M p).modK ((D.s.atP p).ιE (endMin γ a))) ⊆ ↑S :=
    fun a p hp => by
      simp only [hS, Finset.coe_union, Finset.coe_biUnion, Finset.coe_univ, Set.mem_union, Set.mem_iUnion,
        Set.Finite.coe_toFinset, Set.mem_univ, true_and]
      exact Or.inr ⟨a, trivial, hp⟩
  have hnn : ∀ p (x : (D.s.atP p).Ep), 0 ≤ ((zOf Y).M p).modK x := fun p x => ENNReal.toReal_nonneg

  have h1 : Fm.toL.Htot = ∏ p ∈ S, (Fm.FP p).Hp := by
    show ∏ p : {p // p ∈ Fm.P}, (Fm.FP p.1).Hp = _
    rw [Finset.prod_coe_sort Fm.P (fun p => (Fm.FP p).Hp)]
    exact Finset.prod_subset hPS fun p _ hp => (hloc p).1 (hgood p hp)
  rw [h1, Finset.prod_congr rfl fun p _ => (hloc p).2, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, Finset.prod_comm (s := S) (t := Finset.univ),
    Real.finsetProd_rpow S (fun p => ((zOf Y).M p).modK (algebraMap _ _ (LocNG.theta ((zOf Y).M p))))
      (fun p _ => hnn p _),
    Real.finsetProd_rpow S (fun p => ((zOf Y).M p).modK (algebraMap _ _ ((zOf Y).δ p))) (fun p _ => hnn p _),
    Real.finsetProd_rpow S (fun p => ((zOf Y).M p).modK ((D.s.atP p).ιE (GPt ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ)))
      (fun p _ => hnn p _)]
  simp_rw [Finset.prod_inv_distrib]
  rw [← finprod_eq_prod_of_mulSupport_subset _ hsA, ← finprod_eq_prod_of_mulSupport_subset _ hsB,
    ← finprod_eq_prod_of_mulSupport_subset _ hsC, hAv, hBv, hCv]
  have hDv : ∀ a, ∏ p ∈ S, ((zOf Y).M p).modK ((D.s.atP p).ιE (endMin γ a)) =
      |((Algebra.norm ℚ (endMin γ a) : ℚ) : ℝ)|⁻¹ := fun a => by
    rw [← finprod_eq_prod_of_mulSupport_subset _ (hsD a), (hDf a).2]
  simp_rw [hDv]
  have hg : (0 : ℝ) < ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) := by
    have h0 := (D.host.g_prime 0).pos
    have h1 := (D.host.g_prime 1).pos
    exact_mod_cast Nat.mul_pos h0 h1
  have hXg : (X.B.g : ℝ) = ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) := by rw [X.g_eq]
  rw [hXg, ← Finset.prod_inv_distrib]
  exact hpt_eq D.R.rS γ D.host.rdE _ hg _

end Main

end Formalism.L2.SG.NGHTie
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def DensCong : Prop :=
  ∀ (F E : Type) {_ : Field F} {_ : ValuativeRel F} {_ : TopologicalSpace F} {_ : CommRing E} {_ : Algebra F E}
    {_ : TopologicalSpace E} {_ : MeasurableSpace E} (M : Loc.Model F E) (V : Type) {_ : AddCommGroup V}
    {_ : Module E V} (H : Loc.HermSp M V) (ϖ : 𝒪[F]) (abelian₂ : Submodule M.L.O V) (ι : Type) {_ : Fintype ι}
    {_ : DecidableEq ι} (G A : Matrix ι ι E),
    (∀ i j, A i j ∈ M.L.O) → (∃ y ∈ M.L.O, A.det * y = 1) →
      H.dens ϖ abelian₂ ((A.map M.L.cj).transpose * G * A) = H.dens ϖ abelian₂ G

section Steps

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)

def GaPlusTh : Prop :=
  (∀ p, Agree δ M p) → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] → PrimeHyp D u (Tu D u') →
  ∀ (w w' : Point D.host.E (D.R.rS + 1)) (Z Z' : PairVal.MatR D), kind w = kind w' → AtMat w Z → AtMat w' Z' →
  ∀ p, FCount.thZ M δ u u' w Z p ≠ none → FCount.thZ M δ u u' w Z p = FCount.thZ M δ u u' w' Z' p →
    ∃ A : Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (D.s.atP p).Ep,
      (∀ i j, A i j ∈ (M p).L.O) ∧ (∃ y ∈ (M p).L.O, A.det * y = 1) ∧
      CntLocal.GaPlus M δ p (CntLocal.Tn u) (CntLocal.Tn u') Z' =
        (A.map (M p).L.cj).transpose * CntLocal.GaPlus M δ p (CntLocal.Tn u) (CntLocal.Tn u') Z * A

end Steps

theorem densTh_of {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    {δ : ∀ p : PlF D, (D.s.atP p).Fp} {L : CntLocal.LocSp D M} {u u' : D.what₂.Word}
    (hC : DensCong) (hG : GaPlusTh M δ u u') : FCount.DensTh M δ L u u' := by
  intro hA hT hPH ϖ _ w w' Z Z' hk hZ hZ' p hne heq
  obtain ⟨A, hAO, hAd, hGa⟩ := hG hA hT hPH w w' Z Z' hk hZ hZ' p hne heq
  unfold CntLocal.densP
  rw [hGa]
  exact (hC (D.s.atP p).Fp (D.s.atP p).Ep (M p) (L.V p) (L.H p) (ϖ p) (CntLocal.lattice₂ L p (VS D).L0)
    (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (CntLocal.GaPlus M δ p (CntLocal.Tn u) (CntLocal.Tn u') Z) A hAO hAd).symm

end Formalism.L2.SG.Pf.Coef
end
end

section

noncomputable section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc
  Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqClass

namespace Formalism.L2.SG.Pf

theorem liftIotaEqC_holds : LiftIotaEqC :=
  fun _ _ Y u _ s₁ s₂ _ _ _ _ hr =>
    Formalism.L2.SG.Pf.iotaDict_fwd Y s₁ s₂ (lam_eq Y u hr) (lam'_eq Y u hr) (congrArg (fun r => r.2.2) hr)

theorem stepClassG_holds : StepClassG := stepClassG_of_liftIota liftIotaEqC_holds

end Formalism.L2.SG.Pf
end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem toPts_inj {K : Type} [Zero K] {i : ℕ} (p q : Point K (i + 1)) (h : toPts p = toPts q) : p = q := by
  have key : ∀ r : Point K (i + 1),
      List.ofFn (fun a : Fin (toPts r).1.length =>
        ((toPts r).2 a, (toPts r).1.blocks.get ⟨a.1, a.2⟩)) = r.1 := by
    intro r
    apply List.ext_get
    · simp [toPts, Composition.length]
    · intro n h1 h2
      simp [toPts]
  apply Subtype.ext
  rw [← key p, ← key q, h]

variable {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}

theorem at_ptOf (t : TauC Y u u') (hG : 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) (ptPN t)) :
    t.toTerm.atPt (Formalism.L2.SG.PairVal.ptOf t.toTerm) := by
  by_cases hex : ∃ w, t.toTerm.atPt w ∧ t.toTerm.relevant
  · exact Formalism.L2.SG.PairVal.ptOf_spec _ hex
  · exfalso
    have hj : Formalism.L2.SG.PairVal.ptOf t.toTerm = Formalism.L2.SG.PairVal.junkPoint D u u' := by
      unfold Formalism.L2.SG.PairVal.ptOf
      rw [dite_eq_right hex]
    have h0 : NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) (ptPN t) = 0 := by
      unfold ptPN
      rw [hj]
      unfold NGPt
      obtain ⟨w0⟩ : Nonempty (InfinitePlace D.host.E) := by
        first | exact inferInstance | infer_instance
      apply Finset.prod_eq_zero (Finset.mem_univ w0)
      rw [GPt_junk]
      first | simp | rw [map_zero, mul_zero]
    linarith

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end
