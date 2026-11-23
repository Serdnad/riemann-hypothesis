module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2001
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle181
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle319
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle396
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle144
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2035
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Order.Interval.Finset.Box
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
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1942
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFinsetSelfDualClassesHerm
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

namespace GlobalTheory.BottomLVal

open GlobalTheory.LFun

private theorem par_eq_trivPar {D : D7} {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E)
    (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (S : Set (FinPl D)) (par : Fam D.host.E)
    (h : IsParamFun D.sp.cm.sig J L S (fun _ => (1 : ℂ)) par) :
    ∀ w ∉ above D.host.E S, par w = GlobalTheory.BottomRallis.trivPar (D := D) n w := by
  intro w hw
  have hx := h _ hw w rfl
  have h0 : (fun _ : GAd D.sp.cm.sig J => (1 : ℂ)) ≠ 0 := fun e => one_ne_zero (congrFun e 1)
  refine hx.unique ?_
  rcases hx with ⟨hs, e, he, -⟩ | ⟨hw', τ, ϖ, e, α, hϖ, he, -, -⟩
  · exact Or.inl ⟨hs, e, he, ((LFun.Model.hasSatGL_trivial w n).2 1 (GlobalTheory.LGrp.mem_fixed.2 fun _ _ => rfl)
      one_ne_zero).map (LFun.Model.constMap (GAd D.sp.cm.sig J)) (fun _ _ => rfl) h0⟩
  · refine Or.inr ⟨hw', τ, ϖ, e, _, hϖ, he, ((LFun.Model.hasSatU_trivial hϖ (LFun.qV_ne_zero _) n).2 1
      (GlobalTheory.LGrp.mem_fixed.2 fun _ _ => rfl) one_ne_zero).map hϖ (LFun.Model.constMap (GAd D.sp.cm.sig J)) (fun _ _ => rfl) h0, ?_⟩
    rw [GlobalTheory.Core.Rk.Exh.Model.bcParam_rho]
    exact GlobalTheory.Core.Rk.Exh.Model.seg_eq_str (LFun.qV_ne_zero _) (LFun.InertChart.absNorm_eq D.sp.cm.deg2 hw') _

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}

private theorem mem_sfB (G : GridData L sc) (t : T) (v : FinPl D) :
    v ∈ GlobalTheory.BottomIPData.sfB G t ↔ v ∈ G.pl.S0 ∨ ∃ P ∈ L.Q t, P.under (𝓞 D.host.F) = v := by
  classical
  simp only [GlobalTheory.BottomIPData.sfB, GlobalTheory.FunObj.locPl, GlobalTheory.ChiGrid.Places.W0, Finset.mem_image, Finset.mem_union]
  constructor
  · rintro ⟨w, ⟨u, hu, rfl⟩ | hw, rfl⟩
    · exact Or.inl ((G.pl.under_w hu).symm ▸ hu)
    · exact Or.inr ⟨w, hw, rfl⟩
  · rintro (hv | ⟨P, hP, rfl⟩)
    · exact ⟨_, Or.inl ⟨v, hv, rfl⟩, G.pl.under_w hv⟩
    · exact ⟨P, Or.inr hP, rfl⟩

private theorem nuH_unrAt_iff (G : GridData L sc) (t : T) (i j : Fin D.R.m) (P : HeightOneSpectrum (𝓞 D.host.E))
    (hS0 : P.under (𝓞 D.host.F) ∉ G.pl.S0) : (nuH G t i j).UnrAt P ↔ (L.xiH t).UnrAt P := by
  have hS1 : P.under (𝓞 D.host.F) ∉ S1 D := fun h => hS0 (G.pl.mem_S0_of_sum_eq.2 (Or.inr h))
  have a1 : 1 ≤ D.R.m - i := by have := i.2; omega
  have a2 : D.R.m - i ≤ D.R.m := by omega
  have hchi : (G.ch.chiH (D.R.m - i)).UnrAt P := G.ch.unr _ a1 a2 P hS0
  have hmu : (L.C.mu0 j).UnrAt P := (L.C.isMu0 j).unr P fun k hk => hS1 ((S1_mem_OmF D).2 (by
    have : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal := by
      show algebraMap _ (𝓞 D.host.E) _ ∈ P.asIdeal
      rw [map_natCast]; exact hk
    fin_cases k
    · exact Or.inl this
    · exact Or.inr (Or.inl this)))
  refine ⟨fun hnu => ?_, fun hxi => ?_⟩
  · have e : L.xiH t = nuH G t i j * (L.C.mu0 j)⁻¹ * G.ch.chiH (D.R.m - i) := by
      rw [nuH]
      have key : ∀ {M : Type} [CommGroup M] (a x c : M), x = a * x / c * a⁻¹ * c := fun a x c => by
        rw [div_mul_eq_mul_div, div_mul_cancel, mul_comm a x, mul_inv_cancel_right]
      exact key _ _ _
    rw [e]
    exact (hnu.mul hmu.inv).mul hchi
  · rw [nuH, div_eq_mul_inv]
    exact (hmu.mul hxi).mul hchi.inv

private theorem nuH_not_unrAt_iff {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (t : T) (i j : Fin D.R.m)
    (P : HeightOneSpectrum (𝓞 D.host.E)) :
    ¬ (nuH G t i j).UnrAt P ↔ P.under (𝓞 D.host.F) ∈ GlobalTheory.BottomIPData.sfB G t := by
  rw [mem_sfB]
  by_cases h0 : P.under (𝓞 D.host.F) ∈ G.pl.S0
  · exact iff_of_true (GlobalTheory.SqStep.nuH_not_unrAt_above hL G t i j P h0) (Or.inl h0)
  · rw [nuH_unrAt_iff G t i j P h0, hL.Q_ram t P, or_iff_right h0]
    constructor
    · rintro (h | ⟨Q, h, hc⟩)
      · exact ⟨P, h, rfl⟩
      · exact ⟨Q, h, GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc⟩
    · rintro ⟨Q, h, e⟩
      by_cases hq : Q = P
      · exact Or.inl (hq ▸ h)
      · exact Or.inr ⟨Q, h, GlobalTheory.UnderConj.isConjPl_of_under_eq_of_ne D Q P e hq⟩

private theorem prod_range_sub (f : ℤ → ℂ) (a h : ℕ) (e : ℤ) (he : (a : ℤ) = h + e) :
    ∏ i ∈ Finset.range a, f ((h : ℤ) - i) = ∏ s ∈ Finset.Icc (1 - e) (h : ℤ), f s := by
  refine Finset.prod_nbij' (fun i => (h : ℤ) - i) (fun s => ((h : ℤ) - s).toNat) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_range] at hi
    simp only [Finset.mem_Icc]
    omega
  · intro s hs
    simp only [Finset.mem_Icc] at hs
    simp only [Finset.mem_range]
    omega
  · intro i _
    simp
  · intro s hs
    simp only [Finset.mem_Icc] at hs
    omega
  · intro i _
    rfl

private theorem bot_ranks (D : D7) (i j : ℕ) : 1 ≤ botSmall D i j ∧ botBig D i j + botSmall D i j = 2 * h0 D i j ∧
    botBig D i j = h0 D i j + e0 D i j := by
  obtain ⟨h1, h2, h3⟩ := ranks_exact D i j
  have e : rankV D (i + 1) (j + 1) = rankV D i j + D.R.t + sLen D := by simp only [rankV]; ring
  have h4 : D.R.r ≤ rankV D i j := by simp only [rankV]; omega
  have h5 : D.R.m < D.R.r := by have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  simp only [h0, e0]
  omega

end GlobalTheory.BottomLVal

theorem _root_.GlobalTheory.T.partialLFunction_eq_normalizingFactor_definiteBottom : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, ∀ par : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsParamFun D.sp.cm.sig (GlobalTheory.Grid.neg A).gram X.rA.Λ ((GlobalTheory.BottomIPData.sfB G t : Finset (FinPl D)) : Set (FinPl D)) (fun _ => (1 : ℂ)) par →
  ∃ κ : ℂ, κ ≠ 0 ∧ ∀ Λ : ℂ → ℂ, GlobalTheory.CMVal.IsHeckeL (nuH G t i j) Λ →
    HolValueAt (fun s => GlobalTheory.LFun.LSD D (GlobalTheory.BottomIPData.sfB G t) par (GlobalTheory.BottomIPData.betaB G i j / GlobalTheory.BottomIPData.alphaB Lc i j t) (s + 1 / 2)) ((A'.rank : ℂ) / 2)
      (κ * GlobalTheory.LFun.dSfun D.host.E ((GlobalTheory.BottomIPData.sfB G t : Finset (FinPl D)) : Set (FinPl D)) (GlobalTheory.Grid.neg A).rank WW.rank ((A'.rank : ℂ) / 2) *
        ∏ s ∈ Icc (1 - (e0 D i j : ℤ)) (h0 D i j : ℤ), Λ s) := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D _ _ _ _ T Lc μ₀ hL G W i j A A' WW X hX t par hpar => ?_⟩⟩
  obtain ⟨r1, r2, r3⟩ := GlobalTheory.BottomLVal.bot_ranks D i j
  rw [← hX.rank'] at r1 r2
  rw [← hX.rank] at r2 r3
  have hd := GlobalTheory.LFun.dSfun_ne_zero_of_re_pos (E := D.host.E)
    ((GlobalTheory.BottomIPData.sfB G t : Finset (FinPl D)) : Set (FinPl D)) (GlobalTheory.Grid.neg A).rank WW.rank
    (s := (A'.rank : ℂ) / 2) (by
      have : (1 : ℝ) ≤ A'.rank := by exact_mod_cast r1
      simp only [Complex.div_ofNat_re, Complex.natCast_re]
      linarith)
  refine ⟨_, inv_ne_zero hd, fun Λ hΛ => ?_⟩
  rw [inv_mul_cancel₀ hd, one_mul]
  have hν : (GlobalTheory.BottomIPData.betaB G i j / GlobalTheory.BottomIPData.alphaB Lc i j t)⁻¹ = G.nu t i (j + 1) := by
    rw [inv_div]
    exact mul_div_mul_right_eq_div _ _ _
  have hc := chrEq_nu G t i j hL
  have hU : GlobalTheory.LFun.UnrOff (GlobalTheory.BottomIPData.betaB G i j / GlobalTheory.BottomIPData.alphaB Lc i j t)
      ((GlobalTheory.BottomIPData.sfB G t : Finset (FinPl D)) : Set (FinPl D)) := fun w hw => by
    rw [← inv_inv (GlobalTheory.BottomIPData.betaB G i j / GlobalTheory.BottomIPData.alphaB Lc i j t), hν]
    exact ((GlobalTheory.LFun.unrAt_iff_of_chrEq hc w).2
      (not_not.1 (mt (GlobalTheory.BottomLVal.nuH_not_unrAt_iff hL G t i j w).1 hw))).inv
  obtain ⟨σ, hσ⟩ := GlobalTheory.RallisEuler.trivPar_euler _ _ A.rank hU
  have hH : Differentiable ℂ fun s : ℂ => ∏ k ∈ range A.rank, Λ (s + (A.rank : ℂ) / 2 - k) :=
    by
      generalize range A.rank = S
      induction S using Finset.induction_on with
      | empty => simp
      | @insert k S hk ih =>
        simp only [Finset.prod_insert hk]
        exact (hΛ.1.comp (by fun_prop)).mul ih
  refine ⟨fun s : ℂ => ∏ k ∈ range A.rank, Λ (s + (A.rank : ℂ) / 2 - k),
    ⟨Set.univ, trivial, isRightDomain_univ, fun s _ => (hH.analyticAt s).meromorphicAt,
      max σ ((A.rank : ℝ) / 2 + 1), fun s hs => ?_⟩, hH.analyticAt _, ?_⟩
  · have hs1 : σ < s.re := (le_max_left _ _).trans_lt hs
    have hs2 : (A.rank : ℝ) / 2 + 1 < s.re := (le_max_right _ _).trans_lt hs
    refine Eq.trans ?_ ((hσ hs1).trans
      (GlobalTheory.LFun.LSTw_congr (GlobalTheory.BottomLVal.par_eq_trivPar _ _ _ par hpar) _ _).symm)
    refine Finset.prod_congr rfl fun k hk => ?_
    have hk' : (k : ℝ) + 1 ≤ A.rank := by exact_mod_cast Finset.mem_range.1 hk
    rw [hν, GlobalTheory.LFun.charL_eq_of_chrEq hc]
    refine (GlobalTheory.SqStep.heckeL_eq_of_ram
      (fun w hw => (GlobalTheory.BottomLVal.nuH_not_unrAt_iff hL G t i j w).2 hw) hΛ ?_).symm
    simp only [Complex.sub_re, Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re]
    linarith
  · rw [← GlobalTheory.BottomLVal.prod_range_sub (fun s => Λ s) A.rank (h0 D i j) (e0 D i j) (by exact_mod_cast r3)]
    refine Finset.prod_congr rfl fun k _ => congrArg Λ ?_
    have : (A.rank : ℂ) + A'.rank = 2 * (h0 D i j : ℕ) := by exact_mod_cast r2
    push_cast
    linear_combination this / 2
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport

noncomputable section

namespace GlobalTheory.FrameTransport.Onto

open scoped TensorProduct

theorem swapAE_sigR (D : D7) (z : TensorProduct D.host.F (Af D.host.F) D.host.E) :
    Lev.swapAE D (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af D.host.F) D.sp.cm.sig z) =
      Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (Lev.swapAE D z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]
  | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb, RingHom.map_add (f := _), RingHom.map_add (f := _)]
  | tmul a e => rfl

theorem adSwap_sgA (D : D7) (y : StandardLatticesGL3.AE D) :
    adSwap D (StandardLatticesGL3.sgA D y) = Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (adSwap D y) := by
  show Lev.swapAE D (GlobalTheory.BotFormula.toAfE D (StandardLatticesGL3.sgA D y)) = _
  rw [GlobalTheory.BotFormula.toAfE_sgA]
  exact swapAE_sigR D _

def adSwapEquiv (D : D7) : StandardLatticesGL3.AE D ≃+* Lev.EAf D :=
  (GlobalTheory.BotFormula.toAfE D).trans (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toRingEquiv

theorem adSwapEquiv_apply (D : D7) (y : StandardLatticesGL3.AE D) : adSwapEquiv D y = adSwap D y := rfl

theorem sigR_inclEAf (D : D7) (e : D.host.E) :
    Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (inclEAf D e) = inclEAf D (D.sp.cm.sig e) := rfl

end GlobalTheory.FrameTransport.Onto

namespace GlobalTheory.FrameTransport.Onto

theorem cT_map_inclEAf (D : D7) {n : ℕ} (A : Matrix (Fin n) (Fin n) D.host.E) :
    (Formalism.UG.cT (↑D.sp.cm.sig) A).map (inclEAf D) =
      Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) (A.map (inclEAf D)) := by
  ext i j
  exact (sigR_inclEAf D (A j i)).symm

theorem cT_map_adSwap (D : D7) {n : ℕ} (A : Matrix (Fin n) (Fin n) (StandardLatticesGL3.AE D)) :
    (Formalism.UG.cT (StandardLatticesGL3.sgA D) A).map (adSwap D) =
      Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) (A.map (adSwap D)) := by
  ext i j
  exact adSwap_sgA D (A j i)

theorem conj_unitary {R : Type} [CommRing R] (s : R →+* R) {n : ℕ} (J P Pi M : Matrix (Fin n) (Fin n) R)
    (hPPi : P * Pi = 1) (hP : Formalism.UG.cT s P * J * P = 1) (hM : Formalism.UG.cT s M * J * M = J) :
    Formalism.UG.cT s (Pi * M * P) * (Pi * M * P) = 1 := by
  have h2 : Formalism.UG.cT s Pi * Formalism.UG.cT s P = 1 := by rw [← Formalism.UG.cT_mul, hPPi, Formalism.UG.cT_one]
  have hJ : J = Formalism.UG.cT s Pi * Pi := by
    calc J = (Formalism.UG.cT s Pi * Formalism.UG.cT s P) * J * (P * Pi) := by rw [h2, hPPi, Matrix.one_mul, Matrix.mul_one]
      _ = Formalism.UG.cT s Pi * (Formalism.UG.cT s P * J * P) * Pi := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hP, Matrix.mul_one]
  rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, ← hP]
  calc _ = Formalism.UG.cT s P * (Formalism.UG.cT s M * (Formalism.UG.cT s Pi * Pi) * M) * P := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [← hJ, hM]

theorem _root_.GlobalTheory.FrameTransport.exists_frConj_eq : ∀ {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E), Formalism.UG.cT (↑D.sp.cm.sig) (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram * (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1 → ∀ M : GL (Fin V.rank) (Lev.EAf D), M ∈ UA D.sp.cm V.gram → ∃ h : StandardLatticesGL3.GA D V.rank, GlobalTheory.FrameTransport.frConj fr h.1 = M := by
  intro D V fr hfr M hM
  let P : GL (Fin V.rank) (Lev.EAf D) := Formalism.UG.bc (inclEAf D) fr
  let N : GL (Fin V.rank) (Lev.EAf D) := P⁻¹ * M * P
  let h0 : GL (Fin V.rank) (StandardLatticesGL3.AE D) := Formalism.UG.bc (adSwapEquiv D).symm.toRingHom N
  have hbc : Formalism.UG.bc (adSwap D) h0 = N := by
    ext i j
    show adSwap D ((adSwapEquiv D).symm _) = _
    rw [← adSwapEquiv_apply, RingEquiv.apply_symm_apply]
  have hbcm : h0.val.map (adSwap D) = N.val := congrArg Units.val hbc
  have hPPi : P.val * (P⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hfr' : Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) P.val * V.gram.map (inclEAf D) * P.val = 1 := by
    have := congrArg (fun X => X.map (inclEAf D)) hfr
    simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at this
    rw [cT_map_inclEAf] at this
    exact this
  have hN : Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) N.val * N.val = 1 := by
    have hNv : N.val = (P⁻¹).val * M.val * P.val := by simp only [N, Units.val_mul]
    rw [hNv]
    exact conj_unitary _ _ _ _ _ hPPi hfr' hM
  refine ⟨⟨h0, ?_⟩, ?_⟩
  · show Formalism.UG.cT (StandardLatticesGL3.sgA D) h0.val *
        (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (Formalism.UG.inclE (F := ℚ) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) *
        h0.val = (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (Formalism.UG.inclE (F := ℚ) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ))
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
    apply Matrix.map_injective (adSwapEquiv D).injective
    change (Formalism.UG.cT (StandardLatticesGL3.sgA D) h0.val * h0.val).map (adSwap D) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (StandardLatticesGL3.AE D)).map (adSwap D)
    rw [Matrix.map_mul, cT_map_adSwap, hbcm, hN, Matrix.map_one _ (map_zero _) (map_one _)]
  · show frConj fr h0 = M
    rw [frConj_apply, hbc]
    show P * (P⁻¹ * M * P) * P⁻¹ = M
    group

end GlobalTheory.FrameTransport.Onto
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport


noncomputable section

namespace GlobalTheory.FrameTransport

theorem colLat_inv_mulVec_int {K : Type} [Field K] [NumberField K] {n : ℕ} (fr : GL (Fin n) K)
    (x : Fin n → K) (hx : x ∈ colLat fr) : ∀ i, (fr⁻¹.val *ᵥ x) i ∈ Formalism.UG.intOE K := by
  let M : Submodule (𝓞 K) (Fin n → K) :=
    { carrier := {x | ∀ i, (fr⁻¹.val *ᵥ x) i ∈ Formalism.UG.intOE K}
      add_mem' := fun {a b} ha hb i => by
        simp only [Set.mem_setOf_eq, Matrix.mulVec_add, Pi.add_apply] at ha hb ⊢
        exact add_mem (ha i) (hb i)
      zero_mem' := fun i => by simp
      smul_mem' := fun c a ha i => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        have : fr⁻¹.val *ᵥ (c • a) = (algebraMap (𝓞 K) K c) • (fr⁻¹.val *ᵥ a) := by
          rw [← Matrix.mulVec_smul, algebraMap_smul]
        rw [this, Pi.smul_apply, smul_eq_mul]
        exact mul_mem ⟨c, rfl⟩ (ha i) }
  have hle : colLat fr ≤ M := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩ i
    have hcol : (fun a : Fin n => (fr : Matrix (Fin n) (Fin n) K) a j) = fr.val *ᵥ Pi.single j 1 := by
      rw [Matrix.mulVec_single_one]; rfl
    show (fr⁻¹.val *ᵥ (fun a : Fin n => (fr : Matrix (Fin n) (Fin n) K) a j)) i ∈ _
    rw [hcol, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    by_cases h : i = j
    · subst h; simp only [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _
  exact hle hx

theorem inclEAf_intOE_mem {D : D7} (e : D.host.E) (he : e ∈ Formalism.UG.intOE D.host.E) :
    inclEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
  Subring.subset_closure (Or.inl ⟨⟨e, he⟩, rfl⟩)



theorem hatL_colLat_coord_int {D : D7} {n : ℕ} (fr : GL (Fin n) D.host.E) (y : Fin n → Lev.EAf D)
    (hy : y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr)) :
    ∀ i, ((Formalism.UG.bc (inclEAf D) fr)⁻¹.val *ᵥ y) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  let S := Formalism.L2.Herm.intAf D.host.F D.host.E
  let P : Matrix (Fin n) (Fin n) (Lev.EAf D) := (Formalism.UG.bc (inclEAf D) fr)⁻¹.val
  have hP : P = (fr⁻¹.val).map (inclEAf D) := rfl
  let M : Submodule S (Fin n → Lev.EAf D) :=
    { carrier := {y | ∀ i, (P *ᵥ y) i ∈ S}
      add_mem' := fun {a b} ha hb i => by
        simp only [Set.mem_setOf_eq, Matrix.mulVec_add, Pi.add_apply] at ha hb ⊢
        exact add_mem (ha i) (hb i)
      zero_mem' := fun i => by simp
      smul_mem' := fun c a ha i => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        have : P *ᵥ (c • a) = (c : Lev.EAf D) • (P *ᵥ a) := by
          rw [← Matrix.mulVec_smul]; rfl
        rw [this, Pi.smul_apply, smul_eq_mul]
        exact mul_mem c.2 (ha i) }
  have hle : Submodule.span S ((fun x : Fin n → D.host.E => fun i =>
      Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (x i)) '' (colLat fr : Set (Fin n → D.host.E))) ≤ M := by
    refine (Submodule.span_le (p := M)).2 ?_
    rintro _ ⟨x, hx, rfl⟩ i
    have h1 := colLat_inv_mulVec_int fr x hx i
    have h2 : (P *ᵥ (fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (x i))) i =
        inclEAf D ((fr⁻¹.val *ᵥ x) i) := by
      rw [hP, RingHom.map_mulVec]; rfl
    show (P *ᵥ (fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (x i))) i ∈ S
    rw [h2]
    exact inclEAf_intOE_mem _ h1
  exact hle hy

end GlobalTheory.FrameTransport

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport

noncomputable section

namespace GlobalTheory.FrameTransport

theorem cT_map' {A B : Type} [CommRing A] [CommRing B] {m p : Type} (s : A →+* A) (t : B →+* B) (ι : A →+* B)
    (h : ∀ a, t (ι a) = ι (s a)) (M : Matrix m p A) :
    Formalism.UG.cT t (M.map ι) = (Formalism.UG.cT s M).map ι := by
  ext i j
  simp [Formalism.UG.cT, h]

theorem conj_unitary {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {n : Type} [Fintype n] [DecidableEq n]
    (s : A →+* A) (t : C →+* C) (u : B →+* B) (ι : A →+* B) (φ : C →+* B)
    (hι : ∀ a, u (ι a) = ι (s a)) (hφ : ∀ c, u (φ c) = φ (t c))
    (P Q J : Matrix n n A) (H : Matrix n n C) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hfr : Formalism.UG.cT s P * J * P = 1) (hH : Formalism.UG.cT t H * H = 1) :
    Formalism.UG.cT u (P.map ι * H.map φ * Q.map ι) * J.map ι * (P.map ι * H.map φ * Q.map ι) = J.map ι := by
  have hJ : J = Formalism.UG.cT s Q * Q := by
    calc J = Formalism.UG.cT s (P * Q) * J * (P * Q) := by
            rw [hPQ, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
      _ = Formalism.UG.cT s Q * (Formalism.UG.cT s P * J * P) * Q := by
            rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT s Q * Q := by rw [hfr, Matrix.mul_one]
  have hHu : Formalism.UG.cT u (H.map φ) * H.map φ = 1 := by
    rw [cT_map' t u φ hφ, ← Matrix.map_mul, hH, Matrix.map_one _ (map_zero _) (map_one _)]
  have hQP' : Q.map ι * P.map ι = 1 := by
    rw [← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero _) (map_one _)]
  have hPQc : Formalism.UG.cT u (P.map ι) * Formalism.UG.cT u (Q.map ι) = 1 := by
    rw [← Formalism.UG.cT_mul, hQP', Formalism.UG.cT_one]
  have hJ' : J.map ι = Formalism.UG.cT u (Q.map ι) * Q.map ι := by
    rw [hJ, Matrix.map_mul, cT_map' s u ι hι]
  rw [hJ']
  calc Formalism.UG.cT u (P.map ι * H.map φ * Q.map ι) * (Formalism.UG.cT u (Q.map ι) * Q.map ι) * (P.map ι * H.map φ * Q.map ι)
      = Formalism.UG.cT u (Q.map ι) * (Formalism.UG.cT u (H.map φ) * (Formalism.UG.cT u (P.map ι) * Formalism.UG.cT u (Q.map ι))
          * (Q.map ι * P.map ι) * H.map φ) * Q.map ι := by
        rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT u (Q.map ι) * Q.map ι := by
        rw [hPQc, hQP', Matrix.mul_one, Matrix.mul_one, hHu, Matrix.mul_one]

theorem adSwap_sgA (D : D7) (y : StandardLatticesGL3.AE D) :
    adSwap D (StandardLatticesGL3.sgA D y) = Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (adSwap D y) := by
  unfold adSwap
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  rw [GlobalTheory.BotFormula.toAfE_sgA]
  generalize (GlobalTheory.BotFormula.toAfE D) y = x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp [Lev.swapAE, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.UG.sigR, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), hx, hy, RingHom.map_add (f := _)]

theorem sigR_inclEAf (D : D7) (a : D.host.E) :
    Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (inclEAf D a) = inclEAf D (D.sp.cm.sig a) := by
  simp only [inclEAf, Formalism.UG.sigR, Formalism.UG.inclE, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]

theorem frConj_mem_UA {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E)
    (hfr : Formalism.UG.cT (↑D.sp.cm.sig) (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram
      * (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1)
    (h : StandardLatticesGL3.GA D V.rank) : GlobalTheory.FrameTransport.frConj fr h.1 ∈ UA D.sp.cm V.gram := by
  have h2 : Formalism.UG.cT (StandardLatticesGL3.sgA D) (h.1 : Matrix (Fin V.rank) (Fin V.rank) (StandardLatticesGL3.AE D))
      * (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (StandardLatticesGL3.inc D) * (h.1 : Matrix (Fin V.rank) (Fin V.rank) (StandardLatticesGL3.AE D)) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (StandardLatticesGL3.inc D) := h.2
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at h2
  have key := conj_unitary (D.sp.cm.sig : D.host.E →+* D.host.E) (StandardLatticesGL3.sgA D) (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
    (inclEAf D) (adSwap D) (sigR_inclEAf D) (fun y => (adSwap_sgA D y).symm)
    (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) ((fr⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E)
    V.gram (h.1 : Matrix (Fin V.rank) (Fin V.rank) (StandardLatticesGL3.AE D))
    (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]) (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]) hfr h2
  exact key

end GlobalTheory.FrameTransport

end
end
