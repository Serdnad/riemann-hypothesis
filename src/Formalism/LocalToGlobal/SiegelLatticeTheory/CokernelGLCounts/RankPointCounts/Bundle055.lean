module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle049
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle040
import Formalism.DoubleCosetMeasures.LatticeCoset
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbSumGlue
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle043
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle046
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocUnramB
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle051
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
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
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbCut

@[expose] public section

section

noncomputable section

namespace Formalism.L2.SG.Pf.LocOrbCut

open MeasureTheory Formalism.MainNotions.S Formalism.L2.SG.Pf.LocOrbSumPf
open Classical

section Val2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] [IsTopologicalRing E]

theorem local_phase_orbit_eq (M : Loc.Model F E) (hOK : M.OK) {m : ℕ} (a : Loc.Pt E (m + 1))
    (xy xy' : (Loc.IL (m + 1) → E) × (Loc.IN a → E))
    (l ρ : Matrix (Fin (m + 1)) (Fin (m + 1)) E) (hl : Formalism.MainNotions.S.TieN.IntLow M l) (hρ : Formalism.MainNotions.S.TieN.IntUp M ρ)
    (hq : zAt a xy' = l * zAt a xy * ρ) :
    M.psiR (Loc.simpleLow (Loc.uLow xy'.1) + Loc.simpleUp (Loc.uUp a xy'.2)) = M.psiR (Loc.simpleLow (Loc.uLow xy.1) + Loc.simpleUp (Loc.uUp a xy.2)) := by
  have hψ : ∀ x ∈ M.R, M.psiR x = 1 := fun r hr => by
    simpa using (Formalism.MainNotions.LocalModelPeriodLattices.selfDual_of_core M hOK 1).2 M.R.one_mem r hr
  have hLo : Formalism.DoubleCosetMeasures.IsLowUni (rI a l * rI a (Loc.uLow xy.1)) :=
    Formalism.DoubleCosetMeasures.isLowUni_mul E (lowUni_rI a (lowUni_of M hl)) (lowUni_rI a (uLow_lowUni xy.1))
  have hUp : Formalism.DoubleCosetMeasures.IsUpUni (rI a (Loc.uUp a xy.2) * rI a ρ) :=
    Formalism.DoubleCosetMeasures.isUpUni_mul E (upUni_rI a (uUp_upUni a xy.2)) (upUni_rI a (upUni_of M hρ))
  have hv : Formalism.DoubleCosetMeasures.IsLowUni (rI a (Loc.uLow xy'.1)) := lowUni_rI a (uLow_lowUni xy'.1)
  have hu : Formalism.DoubleCosetMeasures.IsUpUni (rI a (Loc.uUp a xy'.2)) := upUni_rI a (uUp_upUni a xy'.2)
  have hvPu : rI a (Loc.uLow xy'.1) *
      Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 * rI a (Loc.uUp a xy'.2) =
      (rI a l * rI a (Loc.uLow xy.1)) * Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 *
        (rI a (Loc.uUp a xy.2) * rI a ρ) := by
    have h := congrArg (rI a) hq
    unfold zAt at h
    simp only [rI_mul, rI_mat] at h
    rw [h]
    simp only [Matrix.mul_assoc]
  have hLd : IsUnit (rI a l * rI a (Loc.uLow xy.1)).det := by rw [Formalism.DoubleCosetMeasures.isLowUni_det E hLo]; exact isUnit_one
  have hUd : IsUnit (rI a (Loc.uUp a xy.2) * rI a ρ).det := by rw [Formalism.DoubleCosetMeasures.isUpUni_det E hUp]; exact isUnit_one
  have hfix : ((rI a l * rI a (Loc.uLow xy.1))⁻¹ * rI a (Loc.uLow xy'.1)) *
      Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 *
      (rI a (Loc.uUp a xy'.2) * (rI a (Loc.uUp a xy.2) * rI a ρ)⁻¹) =
      Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 := by
    calc _ = (rI a l * rI a (Loc.uLow xy.1))⁻¹ * (rI a (Loc.uLow xy'.1) *
          Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 *
          rI a (Loc.uUp a xy'.2)) * (rI a (Loc.uUp a xy.2) * rI a ρ)⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = ((rI a l * rI a (Loc.uLow xy.1))⁻¹ * (rI a l * rI a (Loc.uLow xy.1))) *
          Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 *
          ((rI a (Loc.uUp a xy.2) * rI a ρ) * (rI a (Loc.uUp a xy.2) * rI a ρ)⁻¹) := by
          rw [hvPu]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [Matrix.nonsing_inv_mul _ hLd, Matrix.mul_nonsing_inv _ hUd, Matrix.one_mul, Matrix.mul_one]
  have h0 := Formalism.DoubleCosetMeasures.Final.phaseWellDef E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 _ _
    (Formalism.DoubleCosetMeasures.isLowUni_mul E (Formalism.DoubleCosetMeasures.isLowUni_inv E hLo) hv) (Formalism.DoubleCosetMeasures.isUpUni_mul E hu (Formalism.DoubleCosetMeasures.isUpUni_inv E hUp)) hfix
  have sa := Formalism.DoubleCosetMeasures.Final.simpleAdd E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum
  rw [(sa _ _).1 (Formalism.DoubleCosetMeasures.isLowUni_inv E hLo) hv, (sa _ _).2 hu (Formalism.DoubleCosetMeasures.isUpUni_inv E hUp)] at h0
  have hLi := (sa (rI a l * rI a (Loc.uLow xy.1))⁻¹ (rI a l * rI a (Loc.uLow xy.1))).1
    (Formalism.DoubleCosetMeasures.isLowUni_inv E hLo) hLo
  rw [Matrix.nonsing_inv_mul _ hLd, sLow_one] at hLi
  have hUi := (sa (rI a (Loc.uUp a xy.2) * rI a ρ) (rI a (Loc.uUp a xy.2) * rI a ρ)⁻¹).2
    hUp (Formalism.DoubleCosetMeasures.isUpUni_inv E hUp)
  rw [Matrix.mul_nonsing_inv _ hUd, sUp_one] at hUi
  rw [(sa _ _).1 (lowUni_rI a (lowUni_of M hl)) (lowUni_rI a (uLow_lowUni xy.1))] at hLi
  rw [(sa _ _).2 (upUni_rI a (uUp_upUni a xy.2)) (upUni_rI a (upUni_of M hρ))] at hUi
  have hph : Formalism.DoubleCosetMeasures.sLow (rI a (Loc.uLow xy'.1)) + Formalism.DoubleCosetMeasures.sUp (rI a (Loc.uUp a xy'.2)) =
      Formalism.DoubleCosetMeasures.sLow (rI a l) + Formalism.DoubleCosetMeasures.sUp (rI a ρ) +
      (Formalism.DoubleCosetMeasures.sLow (rI a (Loc.uLow xy.1)) + Formalism.DoubleCosetMeasures.sUp (rI a (Loc.uUp a xy.2))) := by
    linear_combination h0 + hLi + hUi
  have h1 : Formalism.DoubleCosetMeasures.sLow (rI a l) + Formalism.DoubleCosetMeasures.sUp (rI a ρ) ∈ M.R :=
    add_mem (by rw [sLow_rI]; exact sLow_mem M.R _ hl.2.2) (by rw [sUp_rI]; exact sUp_mem M.R _ hρ.2.2)
  rw [Formalism.MainNotions.LocalOrbitGerms.Cls.simpleLow_eq, Formalism.MainNotions.LocalOrbitGerms.Cls.simpleUp_eq, Formalism.MainNotions.LocalOrbitGerms.Cls.simpleLow_eq,
    Formalism.MainNotions.LocalOrbitGerms.Cls.simpleUp_eq, ← sLow_rI a (Loc.uLow xy'.1), ← sUp_rI a (Loc.uUp a xy'.2),
    ← sLow_rI a (Loc.uLow xy.1), ← sUp_rI a (Loc.uUp a xy.2), hph, AddChar.map_add_eq_mul, hψ _ h1, one_mul]

end Val2

end Formalism.L2.SG.Pf.LocOrbCut

namespace Formalism.L2.SG.Pf.Coef

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.LocOrbSumPf
open Classical ValuativeRel

theorem phase_class_holds {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (δ : ∀ p : PlF D, (D.s.atP p).Fp) : PhCls M δ := by
  intro T T' p w Y Y' hOK hY hO hO' hmem
  obtain ⟨w₀, hw₀, xy0, hxy0⟩ := hO
  obtain ⟨l, ρ, hl, hρ, hY'⟩ := hmem
  have hmat : w₀.mat = modMat δ T T' p w + shM δ T T' p w := modShift_holds δ T T' p w w₀ hw₀
  unfold phL
  rw [hw₀]
  try dsimp only
  by_cases h' : ∃ xy : (Loc.IL (D.R.rS + 1) → (D.s.atP p).Ep) × (Loc.IN w₀ → (D.s.atP p).Ep),
      Y' = Loc.uLow xy.1 * modMat δ T T' p w * Loc.uUp w₀ xy.2
  · by_cases h : ∃ xy : (Loc.IL (D.R.rS + 1) → (D.s.atP p).Ep) × (Loc.IN w₀ → (D.s.atP p).Ep),
        Y = Loc.uLow xy.1 * modMat δ T T' p w * Loc.uUp w₀ xy.2
    · rw [dite_eq_left h', dite_eq_left h]
      congr 1
      have e1 := zAt_eq hmat h.choose
      have e2 := zAt_eq hmat h'.choose
      rw [← h.choose_spec] at e1
      rw [← h'.choose_spec] at e2
      have hq : zAt w₀ h'.choose = l * zAt w₀ h.choose * ρ := by
        rw [e1, e2, hY', mul_add, add_mul,
          mul_shM l ρ (last_of_low l hl.1 hl.2.1) (last_of_up ρ hρ.1 hρ.2.1)]
      haveI := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK (M p) hOK
      exact LocOrbCut.local_phase_orbit_eq (M p) hOK w₀ h.choose h'.choose l ρ hl hρ hq
    · exact absurd ⟨xy0, hxy0⟩ h
  · obtain ⟨w₁, hw₁, xy, hxy⟩ := hO'
    rw [hw₀] at hw₁
    cases hw₁
    exact absurd ⟨xy, hxy⟩ h'

end Formalism.L2.SG.Pf.Coef
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB MeasureTheory
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section VolStep

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def VolIdxProd : Prop :=
  (∀ p, Agree δ M p) → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] → IsRowReps D F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : PairVal.MatR D),
    EligAt γ w → PairVal.NormRep γ w F' L U →
      PairVal.volIdx D u u' F0 what₂ δ M γ w F' L =
        ((PairVal.orbT D u u' F0 what₂ γ (ZhatL (lf D F0) F')).ncard : ℝ) *
          ∏ᶠ p, wtL M δ (D.mem u).A.T (D.mem u').A.T p w
            (CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * sgnP p)

end VolStep

section Good

variable {D : Formalism.BasicNotions.D7} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
  {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}


open Formalism.L2.SG.Pf.LocUnramB in
theorem wtL_good (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) (p : PlF D) (hA : Agree δ M p)
    (hg : Good δ M w p) {Y : MatP D p} (hYi : IntP M p Y) (hYo : InOrbP δ T T' p w Y) :
    wtL M δ T T' p w Y = 1 := by
  obtain ⟨w₀, hw₀, xy0, hxy0⟩ := hYo
  have hint := orb_int T T' w p hA hg w₀ hw₀
  obtain ⟨h1, h2⟩ := hint xy0.1 xy0.2 (by rw [← hxy0]; exact hYi)
  have hO : kkOrb M p Y = kkOrb M p (modMat δ T T' p w) :=
    kkOrb_eq p (isLoU_of (Formalism.MainNotions.LocalModelPeriodLattices.isLowUni_uLow _)) h1
      (isUpU_of (Formalism.MainNotions.LocalModelPeriodLattices.isUpUni_uUp _ _)) h2 hxy0
  set H := monoW T T' w p hA hg
  have hOK := hA.1
  have := hOK.haar.sf
  unfold wtL
  rw [hw₀]
  simp only
  have hset : {xy : (Loc.IL (D.R.rS + 1) → (D.s.atP p).Ep) × (Loc.IN w₀ → (D.s.atP p).Ep) |
      Loc.uLow xy.1 * modMat δ T T' p w * Loc.uUp w₀ xy.2 ∈ kkOrb M p Y} =
      (Set.univ.pi fun _ => ((M p).R : Set (D.s.atP p).Ep)) ×ˢ
        (Set.univ.pi fun _ => ((M p).R : Set (D.s.atP p).Ep)) := by
    ext ⟨x, y⟩
    simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ_pi, SetLike.mem_coe]
    rw [hO]
    constructor
    · rintro ⟨l, ρ, hl, hρ, he⟩
      have hYint : ∀ i j, (Loc.uLow x * modMat δ T T' p w * Loc.uUp w₀ y) i j ∈ (M p).R := by
        rw [he]; exact int_mul _ (int_mul _ hl.2.2 H.int) hρ.2.2
      obtain ⟨h1, h2⟩ := hint x y hYint
      refine ⟨fun i => ?_, fun i => ?_⟩
      · have := h1 i.1.1 i.1.2
        simp only [Loc.uLow, if_neg (ne_of_gt i.2), dif_pos i.2] at this
        exact this
      · have := h2 i.1.1 i.1.2
        simp only [Loc.uUp, if_neg (ne_of_lt i.2.1), dif_pos i.2] at this
        exact this
    · rintro ⟨hx, hy⟩
      have hL := isLoU_of (Formalism.MainNotions.LocalModelPeriodLattices.isLowUni_uLow x)
      have hN := isUpU_of (Formalism.MainNotions.LocalModelPeriodLattices.isUpUni_uUp w₀ y)
      refine ⟨Loc.uLow x, Loc.uUp w₀ y, ⟨hL.1, hL.2, fun a b => ?_⟩, ⟨hN.1, hN.2, fun a b => ?_⟩, rfl⟩
      · unfold Loc.uLow
        split_ifs
        · exact (M p).R.one_mem
        · exact hx _
        · exact (M p).R.zero_mem
      · unfold Loc.uUp
        split_ifs
        · exact (M p).R.one_mem
        · exact hy _
        · exact (M p).R.zero_mem
  rw [hset, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi]
  simp [hOK.haar.volR]

variable {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem wtL_finite (hA : ∀ p, Agree δ M p) (hC : LocClsE M δ u u' F0 what₂)
    {γ : TermDef.Term D u u' F0 what₂} {w : Point D.host.E (D.R.rS + 1)} (hγ : EligAt γ w) :
    (Function.mulSupport fun p =>
      (wtL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p) : ℂ)).Finite := by
  have hall := LocModel.good_cofinite δ M hA (w.1.map Prod.fst).toFinset
  rw [Filter.eventually_cofinite] at hall
  refine hall.subset fun p hp => ?_
  simp only [Set.mem_ofPred_eq]
  intro hg
  apply hp
  obtain ⟨hyI, hyO⟩ := hC γ w hγ p
  show (wtL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p) : ℂ) = 1
  rw [wtL_good _ _ w p (hA p) hg hyI hyO, Complex.ofReal_one]

theorem volProd_of (hA : ∀ p, Agree δ M p)
    (hT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2]) (hrows : IsRowReps D F0 what₂)
    (hN : PairVal.NormRepExists D u u' F0 what₂) (hC : LocClsE M δ u u' F0 what₂)
    (hVP : VolIdxProd M δ u u' F0 what₂) : VolProd M δ u u' F0 what₂ := by
  intro γ w hγ
  refine ⟨wtL_finite hA hC hγ, ?_⟩
  have hγ0 := hγ
  have hrel : γ.relevant := PCount.eligRel_holds γ w hγ
  obtain ⟨⟨hgen, -⟩, hat⟩ := hγ
  obtain ⟨y, hy⟩ := hN γ w hat hrel hgen
  have hex : ∃ x : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) × PairVal.MatR D ×
      PairVal.MatR D, PairVal.NormRep γ x.1 x.2.1 x.2.2.1 x.2.2.2 := ⟨(w, y), hy⟩
  have hn : nrep γ = some hex.choose := dif_pos hex
  have hz : zT γ = ZhatL (lf D F0) hex.choose.2.1 := by unfold zT; rw [hn]
  have hv : PairVal.vRdef D u u' F0 what₂ δ M γ =
      PairVal.volIdx D u u' F0 what₂ δ M γ hex.choose.1 hex.choose.2.1 hex.choose.2.2.1 := by
    unfold PairVal.vRdef; rw [dif_pos ⟨hrel, hgen, hex⟩]
  have hspec := hex.choose_spec
  obtain ⟨hRep, -, hL, hU, e⟩ := hspec
  obtain ⟨F₁, hR₁, -, hc₁⟩ := hat
  have hw : w = hex.choose.1 := pt_eq_of_cells cell_point_uniqueness (Formalism.L2.SG.Closed.TermFun_holds D u u') hrows γ
    hR₁ hRep hc₁ ⟨_, _, hL, hU, e⟩
  have hγ' : EligAt γ hex.choose.1 := hw ▸ hγ0
  have key := hVP hA hT hrows γ hex.choose.1 hex.choose.2.1 hex.choose.2.2.1 hex.choose.2.2.2 hγ' hex.choose_spec
  have hcast : ((∏ᶠ p, wtL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p) : ℝ) : ℂ) =
      ∏ᶠ p, (wtL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p) : ℂ) :=
    Complex.ofRealHom.toMonoidHom.map_finprod_of_injective Complex.ofReal_injective _
  rw [← hcast, hv, key, ← hw]
  simp only [yT, hz, Complex.ofReal_mul, Complex.ofReal_natCast]
  rfl

end Good

end Formalism.L2.SG.Pf.Coef
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.FibPart

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount
open Classical ValuativeRel
open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Part

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def clsSet (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (u' : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (Z : PairVal.MatR D) : Set (Set (LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))) :=
  {O | ∃ F' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z,
    O = {F'' | F'' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z ∧ CntLocal.NilradicalFlagMoved F0 Λ F' F''}}

theorem cntE_eq (Λ : Submodule (𝓞 D.host.E) (VS D).V) (Z : PairVal.MatR D) :
    CntLocal.cntE (CntLocal.Tn u') F0 Λ Z = (clsSet F0 u' Λ Z).encard := rfl

theorem pd_of_ez {Λ : Submodule (𝓞 D.host.E) (VS D).V} {Z : PairVal.MatR D}
    {F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)}
    (h : F' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z) : PD D Λ (lf D F0) u' F' :=
  ⟨h.1.1, h.1.2.1, h.2.2.2.1⟩

def termOf (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ ∈ what₂) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (h : PD D Λ (lf D F0) u' F') : TermDef.Term D u u' F0 what₂ :=
  ⟨Λ, hΛ, TermDef.mk Λ (lf D F0) (PD D Λ (lf D F0) u') ⟨F', h⟩⟩

theorem n0rel_refl (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) :
    CntLocal.NilradicalFlagMoved F0 Λ F' F' :=
  ⟨1, ⟨TermDef.one_mem_NLam Λ (lf D F0), fun _ => rfl, rfl⟩, fun _ => rfl, rfl⟩

theorem dcrel_of_n0rel {Λ : Submodule (𝓞 D.host.E) (VS D).V} {F₁ F₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)}
    (hl₁ : IsLift Λ F₁) (hl₂ : IsLift Λ F₂) (h : CntLocal.NilradicalFlagMoved F0 Λ F₁ F₂) : DCRel Λ (lf D F0) F₁ F₂ := by
  obtain ⟨n, hn, he, hz⟩ := h
  refine ⟨n, hn.1, 1, TermDef.one_mem_NLam Λ F₁, fun a => ?_, ?_⟩
  · refine Fin.lastCases ?_ (fun i => ?_) a
    · rw [Formalism.L2.SG.Pf.frame_last_td, Formalism.L2.SG.Pf.frame_last_td]
      exact hz.symm
    · rw [Formalism.L2.SG.Pf.frame_castSucc_td, Formalism.L2.SG.Pf.frame_castSucc_td]
      exact (he i).symm
  · rw [hl₂.2, hl₁.2]
    exact hz.symm

theorem orbT_disj {Z : PairVal.MatR D} {γ₁ γ₂ : TermDef.Term D u u' F0 what₂} (hl : γ₁.lam = γ₂.lam)
    {O : Set (LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))}
    (h₁ : O ∈ PairVal.orbT D u u' F0 what₂ γ₁ Z) (h₂ : O ∈ PairVal.orbT D u u' F0 what₂ γ₂ Z) : γ₁ = γ₂ := by
  obtain ⟨Λ₁, m₁, c₁⟩ := γ₁
  obtain ⟨Λ₂, m₂, c₂⟩ := γ₂
  simp only at hl
  subst hl
  obtain ⟨F₁, hF₁, ⟨p₁, hc₁⟩, rfl⟩ := h₁
  obtain ⟨F₂, hF₂, ⟨p₂, hc₂⟩, hO⟩ := h₂
  have hmem := (Set.ext_iff.1 hO F₁).1 ⟨hF₁, n0rel_refl Λ₁ F₁⟩
  have hdc := dcrel_of_n0rel hF₂.1.1 hF₁.1.1 hmem.2
  have e : TermDef.mk Λ₁ (lf D F0) (PD D Λ₁ (lf D F0) u') ⟨F₂, p₂⟩ =
      TermDef.mk Λ₁ (lf D F0) (PD D Λ₁ (lf D F0) u') ⟨F₁, p₁⟩ := Quot.sound hdc
  have hcc : c₁ = c₂ := hc₁.symm.trans (e.symm.trans hc₂)
  subst hcc
  rfl

theorem mem_orbT_termOf (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ ∈ what₂) {Z : PairVal.MatR D}
    {F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)}
    (hF : F' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z) :
    {F'' | F'' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z ∧ CntLocal.NilradicalFlagMoved F0 Λ F' F''} ∈
      PairVal.orbT D u u' F0 what₂ (termOf Λ hΛ F' (pd_of_ez hF)) Z :=
  ⟨F', hF, ⟨pd_of_ez hF, rfl⟩, rfl⟩

theorem repIn_termOf (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ ∈ what₂) {Z : PairVal.MatR D}
    {F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)}
    (hF : F' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z) :
    RepIn u u' F0 what₂ (termOf Λ hΛ F' (pd_of_ez hF)) Z :=
  ⟨F', hF, ⟨pd_of_ez hF, rfl⟩⟩

theorem eligAt_termOf (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ ∈ what₂) {Z : PairVal.MatR D}
    {w : Point D.host.E (D.R.rS + 1)} (hZ : AtMat w Z) {F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)}
    (hF : F' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z) :
    EligAt (termOf Λ hΛ F' (pd_of_ez hF)) w := by
  refine ⟨⟨⟨F', ⟨pd_of_ez hF, rfl⟩, hF.2.2.1⟩, ?_⟩, ⟨F', ⟨pd_of_ez hF, rfl⟩, hF.1.2.2, ?_⟩⟩
  · show TermDef.Gt Λ (lf D F0) (PD D Λ (lf D F0) u') (TermDef.mk Λ (lf D F0) (PD D Λ (lf D F0) u') ⟨F', _⟩) ≠ 0
    rw [TermDef.Gt_mk (Formalism.L2.SG.Pf.g_value_function _ _ _)]
    exact hF.1.2.2
  · obtain ⟨L, U, hL, hU, he⟩ := hZ
    refine ⟨L, U, hL, hU, ?_⟩
    rw [← he]
    congr 1
    exact hF.2.2.2.2

end Part

end Formalism.L2.SG.Pf.FibPart
end
end
