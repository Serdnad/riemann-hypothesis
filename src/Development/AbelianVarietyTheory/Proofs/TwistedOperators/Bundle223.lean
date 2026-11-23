module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdeles
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrbitStepSpace
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeInfinitesimalCharLargeGap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle299
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle296
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVectorsLieIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1194
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle216
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1449
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle215
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle214
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle191
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle190
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle192
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle201
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IteratedLiftChains

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeFinRam

theorem finite_ramified : ∀ (D : D7) (χ : (AE D)ˣ →* Circle), IsHeckeChar D χ →
    {w : HeightOneSpectrum (𝓞 D.host.E) | ¬ GlobalTheory.LFun.UnrAt χ w}.Finite := by
  intro D χ hχ
  obtain ⟨H, hH⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D χ hχ
  refine (GlobalTheory.Mem.UnrAe.finite_ramified H).subset fun w hw => ?_
  exact fun h => hw ((GlobalTheory.LFun.unrAt_iff_of_chrEq hH w).2 h)

end GlobalTheory.HeckeFinRam
end

section

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Links
open GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains GlobalTheory.PRep GlobalTheory.LFun
open Formalism.UG (IsCommensurated Hecke)
open Formalism.MainNotions.SchurIrreducible (IsSplit)

namespace GlobalTheory.ChrTie

theorem unrAt_iff_and_val_eq : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → ∀ w : HeightOneSpectrum (𝓞 D.host.E), (UnrAt c w ↔ χ.UnrAt w) ∧ val c w = χ.val w :=
  fun _ _ _ h w => ⟨GlobalTheory.LFun.unrAt_iff_of_chrEq h w, GlobalTheory.LFun.val_eq_of_chrEq h w⟩

end GlobalTheory.ChrTie
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridJoin

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}

structure NodeAgree (N : GlobalTheory.Grid.Node D) {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil) (X : GlobalTheory.ChiGrid.Node) :
    Prop where

  sp : N.V = G'.V X

  lat : HEq N.Λ (G'.Λ X)

  cart : HEq (Formalism.IndefR.Links.cart N.M) (W.cart X)

  onb : HEq (Formalism.IndefR.Links.onb N.M) (W.onb X)

structure SpAgree (G : GlobalTheory.Grid.GridPre R) {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil) : Prop where

  vert : ∀ i j, i ≤ D.R.m → j ≤ D.R.m → NodeAgree (G.V i j) W (.grid i j)

  core : ∀ i, i ≤ D.R.m → NodeAgree (G.P i) W (.core i)

  top : ∀ j, j ≤ D.R.m → NodeAgree (G.Xp j) W (.top j)

  q0 : G.q0 = GlobalTheory.ChiGrid.q0 D

  w0 : G.w0 = G'.pl.w G'.pl.v0

  e0 : G.e0 = G'.pl.depth sc G'.pl.v0

  places : G.toPlaceDat.W R.Pg = G'.pl.W0

  lvl : G.lvl R = G'.modul

  chiH : ∀ i, 1 ≤ i → i ≤ D.R.m → G.chiH i = G'.ch.chiH i

  chi : ∀ i, 1 ≤ i → i ≤ D.R.m → G.chi i = G'.ch.chi i

structure ArrAgree (G : GlobalTheory.Grid.GridPre R) {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil) : Prop where

  omX : ∀ i j, i < D.R.m → j ≤ D.R.m → HEq ((G.X i j).ω.toSgn true) (W.om (.chi i j))

  omT : ∀ t i j, i ≤ D.R.m → j < D.R.m → HEq (G.th t i j).ω (W.om (.mu t i j))

  omC : ∀ t j, j < D.R.m → HEq (G.col t j).ω (W.om (.top t j))

  omD : ∀ i, i < D.R.m → HEq ((G.dn i).ω.toSgn true) (W.om (.core i))

  vacX : ∀ i, i < D.R.m → HEq (G.X i 0).vac (W.vac i)

  cos : ∀ i, i < D.R.m → (∀ c, ∃ κ, HEq (G.vC i c) (W.cosVec i κ)) ∧ ∀ κ, ∃ c, HEq (G.vC i c) (W.cosVec i κ)

def Agree (G : GlobalTheory.Grid.GridPre R) {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil) : Prop :=
  SpAgree G W ∧ ArrAgree G W

end GlobalTheory.GridJoin

namespace GlobalTheory.GridJoin

open GlobalTheory.Grid

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

def withArr (G : GridPre R) (X : ∀ i j, ArrS (G.V (i + 1) j) (G.V i j))
    (ωT : T → ∀ i j, WRep (G.nV i j).V (G.nV i (j + 1)).V) (vacT : ∀ i j, WO (G.nV i j).V (G.nV i (j + 1)).V → ℂ)
    (ItT : ∀ i j, Pol (G.nV i j) (G.nV i (j + 1)) →ₗ[ℂ] SmT (G.nV i (j + 1)).M →ₗ[ℂ] SmT (G.nV i j).M)
    (ωC : T → ∀ j, WRep (G.Xp j).V (G.nX j).V) (vacC : ∀ j, WO (G.Xp j).V (G.nX j).V → ℂ)
    (ItC : ∀ j, Pol (G.Xp j) (G.nX j) →ₗ[ℂ] SmT (G.Xp j).M →ₗ[ℂ] SmT (G.nX j).M)
    (dn : ∀ i, ArrT (G.P (i + 1)) (G.P i))
    (ItU : ∀ i, Pol (G.P (i + 1)) (G.P i) →ₗ⋆[ℂ] SmT (G.P i).M →ₗ[ℂ] SmT (G.P (i + 1)).M)
    (vC : ∀ i, G.toGridSp.Cos R i → (WO (G.V (i + 1) 0).V (G.V i 0).V → ℂ)) : GridPre R :=
  { G with X := X, ωT := ωT, vacT := vacT, ItT := ItT, ωC := ωC, vacC := vacC, ItC := ItC, dn := dn, ItU := ItU, vC := vC }

def withMeas (G : GridPre R) (m00 : (G.V 0 0).MeasDat) (mV : ∀ i j, (G.nV i j).MeasDat) (mP : ∀ i, (G.P i).MeasDat)
    (mX : ∀ j, (G.nX j).MeasDat) : GridPre R :=
  { G with m00 := m00, mV := mV, mP := mP, mX := mX }

end GlobalTheory.GridJoin
end
end

section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal

namespace GlobalTheory.SepReal.LieWords

theorem dR_eq_dAct {m : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : Mat m → (H →L[ℂ] H)) : dR π = GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct π := by
  funext X w
  unfold dR GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit
  congr 1

theorem one_le_of_bound {m : ℕ} (hm : 3 ≤ m) {lam : Fin m → ℝ} (hc : IsHCParam lam) {B : ℝ}
    (hB : ∀ a, |lam a| ≤ B) : 1 ≤ B := by
  have hint : ∀ a c : Fin m, a < c → 1 ≤ lam a - lam c := by
    intro a c hac
    obtain ⟨ka, hka⟩ := hc.2 a
    obtain ⟨kc, hkc⟩ := hc.2 c
    have e : lam a - lam c = ((ka - kc : ℤ) : ℝ) := by push_cast; linarith
    have hpos : (0 : ℝ) < ((ka - kc : ℤ) : ℝ) := by rw [← e]; linarith [hc.1 hac]
    have h1 : (0 : ℤ) < ka - kc := by exact_mod_cast hpos
    have h2 : (1 : ℝ) ≤ ((ka - kc : ℤ) : ℝ) := by exact_mod_cast h1
    linarith
  have h01 := hint ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.lt_def])
  have h12 := hint ⟨1, by omega⟩ ⟨2, by omega⟩ (by simp [Fin.lt_def])
  have a0 := abs_le.mp (hB ⟨0, by omega⟩)
  have a2 := abs_le.mp (hB ⟨2, by omega⟩)
  linarith [a0.1, a0.2, a2.1, a2.2]

theorem stepConst_le {m : ℕ} (hm : 3 ≤ m) {B : ℝ} (hB : 1 ≤ B) (P : ℕ) (hP : P ≤ m + 1) :
    GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst m (Real.sqrt B) P ≤ (8 * (m : ℝ) * B) ^ 2 := by
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hB0 : (0 : ℝ) ≤ B := by linarith
  unfold GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst
  rw [Real.sq_sqrt hB0]
  have h12 : (m : ℝ) ^ (1 / 2 : ℝ) ≤ m := by
    calc (m : ℝ) ^ (1 / 2 : ℝ) ≤ (m : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = m := Real.rpow_one _
  have h32 : (m : ℝ) ^ (3 / 2 : ℝ) ≤ (m : ℝ) ^ 2 := by
    calc (m : ℝ) ^ (3 / 2 : ℝ) ≤ (m : ℝ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = (m : ℝ) ^ 2 := Real.rpow_two _
  have hPr : (P : ℝ) ≤ m + 1 := by exact_mod_cast hP
  have a1 : (m : ℝ) ^ (1 / 2 : ℝ) * B ≤ m * B := mul_le_mul_of_nonneg_right h12 hB0
  have hmB : 1 ≤ (m : ℝ) * B := by nlinarith
  have a2 : (m : ℝ) * B ≤ (m * B) ^ 2 := by nlinarith
  have a3 : (m : ℝ) ^ 2 ≤ (m * B) ^ 2 := by
    have hB2 : 1 ≤ B ^ 2 := one_le_pow₀ hB
    rw [mul_pow]
    calc (m : ℝ) ^ 2 = (m : ℝ) ^ 2 * 1 := (mul_one _).symm
      _ ≤ (m : ℝ) ^ 2 * B ^ 2 := mul_le_mul_of_nonneg_left hB2 (sq_nonneg _)
  have a4 : 3 * (P : ℝ) ≤ 2 * (m : ℝ) ^ 2 := by nlinarith
  have e : (8 * (m : ℝ) * B) ^ 2 = 64 * (m * B) ^ 2 := by ring
  rw [e]
  nlinarith [sq_nonneg ((m : ℝ) * B)]

theorem rk_le {m : ℕ} (hm : 3 ≤ m) (ε : Fin m → Bool) :
    120 * (m : ℝ) * ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 1000 * (m : ℝ) ^ 3 := by
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hrk : GlobalTheory.Count.rkR ε ≤ m := by
    unfold GlobalTheory.Count.rkR
    exact (min_le_left _ _).trans ((Finset.card_filter_le _ _).trans (by simp))
  have h1 : ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hrk) (by norm_num)
  have h32 : (m : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ 2 := by
    calc (m : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = (m : ℝ) ^ 2 := Real.rpow_two _
  have h0 : 0 ≤ ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) := by positivity
  have h2 : 120 * (m : ℝ) * ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 120 * (m : ℝ) * (m : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left (h1.trans h32) (by positivity)
  nlinarith

end GlobalTheory.SepReal.LieWords


open GlobalTheory.SepReal.LieWords in
theorem GlobalTheory.SepReal.lieBound : LieBound := by
  intro m ε lam B hm hc hgap hB H _ _ π hDS v₀ hv₀
  haveI : CompleteSpace H := hDS.1
  have hU : IsURepOn (UJset ε) π := hDS.2.2.1
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hgap2 : ∀ a b : Fin m, ε a ≠ ε b → 2 * (m : ℝ) < |lam a - lam b| := by
    intro a b hab
    have h := hgap a b hab
    nlinarith [sq_nonneg (m : ℝ)]
  have hK := GlobalTheory.Jet.MultGap.isKTypeOf_lowKSub m ε lam H π hc hDS hgap2
  have hZ := GlobalTheory.DSId.LowCharGap.lowChar m ε lam H π hc hDS _ hgap (rk_le hm ε)
  have hB1 : 1 ≤ B := one_le_of_bound hm hc hB
  have hb : ∀ a, |lam a| ≤ (Real.sqrt B) ^ 2 := by
    rw [Real.sq_sqrt (by linarith)]; exact hB
  have hSB := GlobalTheory.StepBoundOneRep.stepBound_of_eigen m ε H π lam (Real.sqrt B) hU hK hZ hb
  refine ⟨?_, ?_⟩
  · have hs := GlobalTheory.StepBoundOneRep.smooth_of_mem_lowKSub ε lam π hU hK v₀ hv₀.2
    have hJ : IsUnit (Jm ε) := (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse (Jm_mul_self ε))
    exact (GlobalTheory.SmChart.smV_iff_smoothOnH hJ hU.1 v₀).2 hs
  · rw [dR_eq_dAct]
    intro l
    induction l with
    | nil => intro _ _; simp [hv₀.1]
    | cons X l ih =>
      intro hl hlen
      have hX : inG ε X := hl X List.mem_cons_self
      have hl' : ∀ Y ∈ l, Y ∈ lieOf (Jm ε) := fun Y hY => hl Y (List.mem_cons_of_mem _ hY)
      have hlen' : l.length ≤ m + 2 := by simp at hlen; omega
      have hmem : l.foldr (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct π) v₀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam π l.length :=
        Submodule.subset_span ⟨l, v₀, le_rfl, hl', hv₀.2, rfl⟩
      have h1 := (hSB l.length).2.2.2 X hX _ hmem
      have hcst := stepConst_le hm hB1 l.length (by simp at hlen; omega)
      have hrest := ih hl' hlen'
      have hsq : Real.sqrt (hs X) = hsn X := rfl
      have hh : 0 ≤ hsn X := Real.sqrt_nonneg _
      rw [List.foldr_cons, List.map_cons, List.prod_cons]
      calc ‖GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct π X (l.foldr (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct π) v₀)‖
          ≤ Real.sqrt (hs X) * GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst m (Real.sqrt B) l.length *
              ‖l.foldr (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct π) v₀‖ := h1
        _ ≤ ((8 * (m : ℝ) * B) ^ 2 * hsn X) * (l.map fun X => (8 * (m : ℝ) * B) ^ 2 * hsn X).prod := by
          rw [hsq]
          refine mul_le_mul ?_ hrest (norm_nonneg _) (by positivity)
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right hcst hh
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical

theorem _root_.GlobalTheory.T.archimedeanLine_intertwines_realSchrodinger : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsStd ψ → M.IsWeil ψ χX χW om → ∀ γ ∈ Lines σ W, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
    (∀ t (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑(T t f)) →
    ∃ A : ℝ → ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
        ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
      (∀ v, Continuous fun t => A t v) ∧
      ∀ t v (f f₁ : SInf F (Fin n × Fin d)), ⇑f₁ = schrF (trP F (Fin n × Fin d)) v ⇑f →
        ⇑(T t f₁) = schrF (trP F (Fin n × Fin d)) (A t v) ⇑(T t f) := by
  first | exact @GlobalTheory.ArchFam.schr_equiv | exact GlobalTheory.ArchFam.schr_equiv | (intros; apply GlobalTheory.ArchFam.schr_equiv <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix


theorem _root_.GlobalTheory.T.hermitian_selfDual_lattice_split_place_dictionary : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (V : Spc F E d) (r s : ℕ), B.IsGood σ → V.IsHerm σ B r s →
    ∀ (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v →
    ∃ (π₁ π₂ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
      ((∀ z, π₁ (cA σ z) = π₂ z) ∧ (∀ z, π₂ (cA σ z) = π₁ z) ∧
      (∀ a : AF F, π₁ (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) a) = evFin F v a) ∧
      (∀ a : AF F, π₂ (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) a) = evFin F v a) ∧
      (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z → π₁ z = 0 → π₂ z = 0 → z = 0) ∧
      (∀ x₁ x₂ : Fv F v, ∃ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) ∧
      (∀ z : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), z ∈ GlobalTheory.InertSph.latAt V v ↔ At (evFin F v) z ∧
        (∀ i, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₁ (z j)) i ∈
          v.adicCompletionIntegers F) ∧
        (∀ i, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₂ (z j)) i ∈
          v.adicCompletionIntegers F))) ∧
      ∃ S : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), IsUnit S.det ∧
        S.map (fun x => (x : Fv F v)) =
          (b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F V.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) := by
  first | exact @GlobalTheory.SplitDictHerm.split_dict_herm | exact GlobalTheory.SplitDictHerm.split_dict_herm | (intros; apply GlobalTheory.SplitDictHerm.split_dict_herm <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix


theorem _root_.GlobalTheory.T.doubledFirstFactor_mem_doubledLatticeStabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (W : Spc F E d) (v : Pl (F := F)),
    ∀ k ∈ GlobalTheory.InertSph.KAt σ W v, GlobalTheory.InertDbl.inlD σ W k ∈ GlobalTheory.InertDbl.KAtD σ W v := by
  first | exact @GlobalTheory.InertDbl.inlD_mem_KAtD | exact GlobalTheory.InertDbl.inlD_mem_KAtD | (intros; apply GlobalTheory.InertDbl.inlD_mem_KAtD <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.conjugateDatum_fockVectors_isVacuum_off_level : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.models_inf → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) f₀ f B, GlobalTheory.GalLift.VecData R i σ f₀ f B → ∀ P, GlobalTheory.Hk3.Good R A.μ0 P → ∀ φ, GlobalTheory.Hk3.IsVacAt R.ψ _ _ P (GlobalTheory.GalLift.ptAt R i σ B f φ) := by
  first | exact @GlobalTheory.ConjVacua.isVacAt_ptAt | exact GlobalTheory.ConjVacua.isVacAt_ptAt | (intros; apply GlobalTheory.ConjVacua.isVacAt_ptAt <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.SplitPlaceBigCell

theorem splitPlace_bigCell_exists_admissible_inverse : (∀ {R : Type} [CommRing R] [IsLocalRing R], IsUnit (2 : R) → ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) R), IsUnit S.det →
    ∀ (G₁ G₂ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R), IsUnit G₁.det →
      G₁ᵀ * Matrix.fromBlocks S 0 0 (-S) * G₂ = Matrix.fromBlocks S 0 0 (-S) →
      ∃ X₁ X₂ : Matrix (Fin n) (Fin n) R, X₁ᵀ * S + S * X₂ = 0 ∧
        IsUnit (G₁.toBlocks₁₁ + G₁.toBlocks₁₂ + G₁.toBlocks₂₁ + G₁.toBlocks₂₂ +
          X₁ * (G₁.toBlocks₁₁ + G₁.toBlocks₁₂ - G₁.toBlocks₂₁ - G₁.toBlocks₂₂)).det ∧
        IsUnit (G₂.toBlocks₁₁ + G₂.toBlocks₁₂ + G₂.toBlocks₂₁ + G₂.toBlocks₂₂ +
          X₂ * (G₂.toBlocks₁₁ + G₂.toBlocks₁₂ - G₂.toBlocks₂₁ - G₂.toBlocks₂₂)).det) →
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {d : ℕ} (W : Spc F E d) (v : Pl (F := F)), (∀ i j, σ (W.J j i) = -W.J i j) →
    IsUnit (2 : v.adicCompletionIntegers F) →
    ∀ (π₁ π₂ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
      ((∀ z, π₁ (cA σ z) = π₂ z) ∧ (∀ z, π₂ (cA σ z) = π₁ z) ∧
      (∀ a : AF F, π₁ (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) a) = evFin F v a) ∧
      (∀ a : AF F, π₂ (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) a) = evFin F v a) ∧
      (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z → π₁ z = 0 → π₂ z = 0 → z = 0) ∧
      (∀ x₁ x₂ : Fv F v, ∃ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) ∧
      (∀ z : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), z ∈ GlobalTheory.InertSph.latAt W v ↔ At (evFin F v) z ∧
        (∀ i, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₁ (z j)) i ∈
          v.adicCompletionIntegers F) ∧
        (∀ i, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₂ (z j)) i ∈
          v.adicCompletionIntegers F))) →
      (∃ S : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), IsUnit S.det ∧
        S.map (fun x => (x : Fv F v)) =
          (b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) →
      ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
      ∃ Y : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) Y ∧
        (∀ z ∈ GlobalTheory.InertSph.latAt W v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
        Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) = 0 ∧
        ∃ M : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), M * (GlobalTheory.DblVac.diagonalBlockOfMatrix g + Y * (⅟(2 : AF F) • ((GlobalTheory.DblVac.matD g).toBlocks₁₁ +
          (GlobalTheory.DblVac.matD g).toBlocks₁₂ - (GlobalTheory.DblVac.matD g).toBlocks₂₁ - (GlobalTheory.DblVac.matD g).toBlocks₂₂))) = 1 ∧
          ∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  intro hLoc F E _ _ _ _ _ σ d W v hskew h2 π₁ π₂ b₁ b₂ hd hSx g hg
  obtain ⟨hc₁, hc₂, ha₁, ha₂, hinj, hsurj, hlat⟩ := hd
  obtain ⟨S, hSdet, hS⟩ := hSx
  obtain ⟨k11, k12, k21, k22, k11', k12', k21', k22'⟩ := GlobalTheory.T.doubledVacuumLatticeStabilizer_blocks_keep_lattice σ W v g hg
  have I := fun A hA => GlobalTheory.T.integral_localBasisConjugates_of_keepsLatticeAtPlace W v π₁ π₂ b₁ b₂ hlat hsurj A hA
  have hinv : GlobalTheory.DblVac.matD g⁻¹ * GlobalTheory.DblVac.matD g = 1 := g.1.inv_mul
  obtain ⟨G₁, hG₁, hG₁u⟩ := GlobalTheory.T.integralBlocks_leftInverse_isUnit_det_splitPlace v π₁ b₁ (GlobalTheory.DblVac.matD g) (GlobalTheory.DblVac.matD g⁻¹) hinv
    (I _ k11).1 (I _ k12).1 (I _ k21).1 (I _ k22).1 (I _ k11').1 (I _ k12').1 (I _ k21').1 (I _ k22').1
  obtain ⟨G₂, hG₂, -⟩ := GlobalTheory.T.integralBlocks_leftInverse_isUnit_det_splitPlace v π₂ b₂ (GlobalTheory.DblVac.matD g) (GlobalTheory.DblVac.matD g⁻¹) hinv
    (I _ k11).2 (I _ k12).2 (I _ k21).2 (I _ k22).2 (I _ k11').2 (I _ k12').2 (I _ k21').2 (I _ k22').2
  have hU := GlobalTheory.T.unitary_at_splitPlace_localBases σ W v π₁ π₂ b₁ b₂ hc₁ g
  have e : ∀ {m n o : Type} [Fintype n] (A : Matrix m n (v.adicCompletionIntegers F))
      (B : Matrix n o (v.adicCompletionIntegers F)),
      (A * B).map (fun x => (x : Fv F v)) = A.map (fun x => (x : Fv F v)) * B.map (fun x => (x : Fv F v)) :=
    fun A B => Matrix.map_mul (f := (v.adicCompletionIntegers F).subtype)
  have hUO : G₁ᵀ * Matrix.fromBlocks S 0 0 (-S) * G₂ = Matrix.fromBlocks S 0 0 (-S) := by
    apply Matrix.map_injective (f := fun x : v.adicCompletionIntegers F => (x : Fv F v)) Subtype.coe_injective
    beta_reduce
    have en : (-S).map (fun x => (x : Fv F v)) = -(S.map (fun x => (x : Fv F v))) := by ext i j; rfl
    have ez : (0 : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F)).map (fun x => (x : Fv F v)) = 0 := by
      ext i j; rfl
    rw [e, e, Matrix.transpose_map, Matrix.fromBlocks_map, en, ez, hG₁, hG₂, hS]
    exact hU
  obtain ⟨X₁, X₂, hX, hP₁, hP₂⟩ := hLoc h2 S hSdet G₁ G₂ hG₁u hUO
  obtain ⟨Y, hYat, hY₁, hY₂, hYadm⟩ :=
    GlobalTheory.T.exists_admissible_lift_splitPlaceConjugatePair σ W v hskew π₁ π₂ b₁ b₂ hc₁ hc₂ hinj hsurj S hS X₁ X₂ hX
  obtain ⟨N₁, hN₁, hN₁i⟩ := GlobalTheory.T.halfBlockSum_exists_inverse_integral_splitPlace v π₁ b₁ ha₁ (GlobalTheory.DblVac.matD g) G₁ hG₁ X₁ hP₁ Y hY₁
  obtain ⟨N₂, hN₂, hN₂i⟩ := GlobalTheory.T.halfBlockSum_exists_inverse_integral_splitPlace v π₂ b₂ ha₂ (GlobalTheory.DblVac.matD g) G₂ hG₂ X₂ hP₂ Y hY₂
  have hK := GlobalTheory.T.halfBlockSumTwist_sub_one_supportedAtPlace v (GlobalTheory.DblVac.matD g) Y hg.1 hYat
  obtain ⟨M, hMK, hM₁, hM₂⟩ := GlobalTheory.T.exists_leftInverse_lifting_splitPlaceInverses v π₁ π₂ hinj hsurj _ hK N₁ N₂ hN₁ hN₂
  have hYi : ∀ (b : GL (Fin d) (Fv F v)) (X : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F)),
      ∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *
        ((b : Matrix (Fin d) (Fin d) (Fv F v)) * X.map (fun x => (x : Fv F v)) *
          ((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v))) *
        (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F := by
    intro b X i j
    have : ((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *
        ((b : Matrix (Fin d) (Fin d) (Fv F v)) * X.map (fun x => (x : Fv F v)) *
          ((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v))) *
        (b : Matrix (Fin d) (Fin d) (Fv F v)) = X.map (fun x => (x : Fv F v)) := by
      simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [this]; exact (X i j).2
  refine ⟨Y, hYat, GlobalTheory.T.keepsLatticeAtPlace_of_integral_localBasisConjugates W v π₁ π₂ b₁ b₂ hlat Y ?_ ?_, hYadm, M, hMK,
    GlobalTheory.T.keepsLatticeAtPlace_of_integral_localBasisConjugates W v π₁ π₂ b₁ b₂ hlat M ?_ ?_⟩
  · rw [hY₁]; exact hYi b₁ X₁
  · rw [hY₂]; exact hYi b₂ X₂
  · rw [hM₁]; exact hN₁i
  · rw [hM₂]; exact hN₂i

end GlobalTheory.SplitPlaceBigCell
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix


theorem _root_.GlobalTheory.T.exists_unipotent_doubledStabilizer_adds_diagonalBlock : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {d : ℕ} (W : Spc F E d) (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal → ∀ Y : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      At (evFin F v) Y → (∀ z ∈ GlobalTheory.InertSph.latAt W v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
      Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) = 0 →
      ∃ p ∈ GlobalTheory.DblVac.KD σ W v, p ∈ GlobalTheory.DblVac.PDiag σ W ∧ ∀ g ∈ GlobalTheory.DblVac.KD σ W v, p * g ∈ GlobalTheory.DblVac.KD σ W v ∧
        GlobalTheory.DblVac.diagonalBlockOfMatrix (p * g) = GlobalTheory.DblVac.diagonalBlockOfMatrix g + Y * (⅟(2 : AF F) • ((GlobalTheory.DblVac.matD g).toBlocks₁₁ +
          (GlobalTheory.DblVac.matD g).toBlocks₁₂ - (GlobalTheory.DblVac.matD g).toBlocks₂₁ - (GlobalTheory.DblVac.matD g).toBlocks₂₂)) := by
  first | exact @GlobalTheory.DblVacUnip.exists_unip | exact GlobalTheory.DblVacUnip.exists_unip | (intros; apply GlobalTheory.DblVacUnip.exists_unip <;> assumption)
end
