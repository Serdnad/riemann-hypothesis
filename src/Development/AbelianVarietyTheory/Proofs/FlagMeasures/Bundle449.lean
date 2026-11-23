module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle444
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle414
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle376
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle417
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle426
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle348
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle396
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle017
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle005
public import Formalism.LocalRingCardinality.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle446
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle133
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
public import Formalism.SharpRestriction.CuspSpanNormBounds.TheoremBConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle004
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting

@[expose] public section

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AmpTerm

theorem gval_of_movesTo {D : D7} {T T' : D.host.E} {F00 F : LFlag (D.sp.Y 0) D.R.rS T}
    {F'0 F' : LFlag (D.sp.Y 0) D.R.rS T'} {ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    {U U' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E}
    (h : MovesTo F00 F'0 F F' ρ U U') : Gval F F' = Gval F00 F'0 := by
  obtain ⟨hρ, hU, hU', hF, hF'⟩ := h
  have hZ : ZhatL F F' = U.conjTranspose * ZhatL F00 F'0 * U' := by
    ext a b
    have e1 : ZhatL F F' a b = (VS D).hT (ρ (frame F a)) (ρ (frame F' b)) := by
      rw [hρ]; rfl
    have hz : ∀ c d, ZhatL F00 F'0 c d = (VS D).hT (frame F00 c) (frame F'0 d) := fun _ _ => rfl
    rw [e1, hF a, hF' b]

    simp only [Matrix.mul_apply, hz, map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, Matrix.conjTranspose_apply, starRingEnd_apply, Finset.sum_mul, Finset.mul_sum]
    simp only [RingHom.id_apply]
    refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => ?_))
    ring
  have hD : ∀ l, Dl F.fl F'.fl l = Dl F00.fl F'0.fl l := by
    intro l
    have := Formalism.L2.SG.Pf.leadMinor_uni U.conjTranspose (ZhatL F00 F'0) U'
      (fun a c hac => by simp [Matrix.conjTranspose_apply, (hU c a).1 hac])
      (fun a => by simp [Matrix.conjTranspose_apply, (hU a a).2 rfl])
      (fun d b hbd => (hU' d b).1 hbd) (fun b => (hU' b b).2 rfl) l
    rw [← hZ] at this
    exact this
  simp only [Gval, Gflag, hD]

theorem G_eq_gval {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word} (t : TauC Y u u') :
    t.G = Gval (lf D (X.Fu u)) t.frame :=
  Formalism.L2.SG.TermDef.Gt_mk (Formalism.L2.SG.Pf.g_value_function _ _ _) ⟨t.frame, t.rep.2.2.2.2⟩

theorem lam_eq_of_row {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word} {t t₀ : TauC Y u u'}
    (h : (Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀) : t.lam = t₀.lam ∧ t.lam' = t₀.lam' :=
  ⟨congrArg (fun r => r.1.1) h, congrArg (fun r => r.2.1.1) h⟩

theorem exists_admissibleWitness_rowTerm {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word} (t : TauC Y u u') :
    ∃ ξ, AdmWit t.lam (gS D) (lf D (X.Fu u)) t.frame ξ :=
  t.rep.2.2.2.2.2.1

end GlobalTheory.AmpTerm

namespace GlobalTheory.AmpTerm


open Formalism.L2.SG.PairVal in
theorem amp_eq_mass_phase : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ ν, Formalism.L2.SG.RealObj.NuQPin X u u' ν → ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → t₀.relevant → Formalism.L2.SG.PairVal.ptOf t₀.toTerm = w → ∃ T : X.Vpi u' →L[ℂ] X.Vpi u, ‖Formalism.L2.SG.PackageTie.hsEmb T‖ = ‖Formalism.L2.SG.PackageTie.hsEmb (Jw Y u u' ν w)‖ ∧ ∀ (t : TauC Y u u') (n m : ((VS D).V ≃ₗ[D.host.E] (VS D).V)), (Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀ → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t = ((((((X.B.g : ℝ) ^ (D.R.f * Fintype.card (Formalism.L2.SG.RealObj.FreeE w)))⁻¹) * G.mu (c.lat (ρ * n) t.lam) : ℝ) : ℂ) * G.om (G.datOf (c.lat ρ t₀.lam)) (c.lat (ρ * n) t.lam)) • T := by
  intro D X Y u u' hS hk w F00 F'0 FP hZ hG hAt G c ν hν t₀ ρ U U' hmv hrel hpt
  have hG0 : t₀.G ≠ 0 := by
    rw [G_eq_gval]; exact fun h => hG ((gval_of_movesTo hmv).symm.trans h)
  obtain ⟨-, T0, hT0, hform⟩ := GlobalTheory.T.orbital_integrals_terms_one_doubleCoset D X Y u u' hS ν hν t₀ hrel hG0 w hpt.symm
  have hpU : psiInf (gS D) (sgUp U) ≠ 0 := by
    intro h; have := norm_psiInf (gS D) (sgUp U); rw [h, norm_zero] at this; exact zero_ne_one this
  have hpU' : psiInf (gS D) (sgUp U') ≠ 0 := by
    intro h; have := norm_psiInf (gS D) (sgUp U'); rw [h, norm_zero] at this; exact zero_ne_one this
  refine ⟨(((scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2 : ℝ) : ℂ) *
      psiInf (gS D) (sgUp U) * (psiInf (gS D) (sgUp U'))⁻¹) • T0, ?_, ?_⟩
  · rw [map_smul, norm_smul, hT0]
    unfold Jw
    rw [map_smul, norm_smul, norm_mul, norm_mul, norm_inv, norm_psiInf, norm_psiInf]
    simp
  · rintro t n m hrow ⟨hn, hm, hlin⟩
    obtain ⟨hlam, hlam'⟩ := lam_eq_of_row hrow
    have hL := GlobalTheory.RatIsomPoint.ratLink_points D X
    obtain ⟨xn, hxn, -⟩ := hL.1 n hn.1
    obtain ⟨xm, hxm, -⟩ := hL.1 m hm.1
    obtain ⟨μR, K, hpin, hK, hOO⟩ := hform t n m xn xm ⟨hn, hm, hlin⟩ hxn hxm
    obtain ⟨-, -, -, -, -, hgrp⟩ :=
      GlobalTheory.T.rational_unipotent_groups_lattices_global_coordinates D X Y u u' hS hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hmv
    obtain ⟨A, A', hA, hA', hnA, hmA', hmv'⟩ := hgrp t n m ⟨hn, hm, hlin⟩
    have hcos := GlobalTheory.T.flagTerm_invariants_const_on_rationalDoubleCoset D X Y u u' hS t₀ t n m hrel hG0 ⟨hn, hm, hlin⟩
    have hvol := GlobalTheory.T.automorphismCovolume_eq_latticeMass D X Y u u' hS hk w F00 F'0 FP hZ hG hAt G c t (ρ * n) (U * A) (U' * A')
      hmv' hcos.1 μR hpin K hK
    obtain ⟨ξ, hξ⟩ := exists_admissibleWitness_rowTerm t
    have hchi := GlobalTheory.T.levelCharacter_unipotentPart_of_admissibilityWitness D X Y u u' hS t ξ hξ
    have hterm := (GlobalTheory.T.movedTermLattice_isGlobalTerm_phase D X Y u u' hS hk w F00 F'0 FP hZ hG hAt G c t (ρ * n) (U * A) (U' * A')
      hmv').2 ξ hξ
    have hdat := (GlobalTheory.T.termRow_eq_iff_movedLatticeInnerData_eq D X Y u u' hS hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hmv t n m hlam hlam'
      ⟨hn, hm, hlin⟩).1 hrow
    rw [hdat] at hterm
    have hpn := (hL.2.2 u xn n hxn).2 hn A hnA
    have hpm := (hL.2.2 u' xm m hxm).2 hm A' hmA'
    have hU := hmv.2.1
    have hU' := hmv.2.2.1
    unfold ampN
    rw [hchi, hOO, hpn, hpm, hvol, hterm, Formalism.L2.SG.Pf.sgUp_mul hU hA, Formalism.L2.SG.Pf.sgUp_mul hU' hA',
      Formalism.L2.SG.Pf.psiInf_add, Formalism.L2.SG.Pf.psiInf_add, smul_smul, smul_smul, smul_smul]
    congr 1
    field_simp

end GlobalTheory.AmpTerm
end

section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DegLine

open Formalism.QuantumDeterminants Formalism.MainNotions.S

theorem gap_near {N : ℕ} (ε : Fin N → Bool) (l ν : Fin N → ℝ) (G ρ : ℝ) (hg : GapAtLeast ε l G)
    (hν : l1dist ν l ≤ ρ) : GapAtLeast ε ν (G - 2 * ρ) := by
  intro a b hab
  have hco : ∀ j, |ν j - l j| ≤ ρ := fun j =>
    le_trans (Finset.single_le_sum (f := fun j => |ν j - l j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)) hν
  have h1 := hg a b hab
  have h2 := hco a
  have h3 := hco b
  have h4 : |l a - l b| ≤ |ν a - ν b| + |ν a - l a| + |ν b - l b| := by
    have e : l a - l b = (ν a - ν b) - (ν a - l a) + (ν b - l b) := by ring
    rw [e]
    exact le_trans (abs_add_le _ _) (by have := abs_sub (ν a - ν b) (ν a - l a); linarith)
  linarith

theorem gap_lamD (D : D7) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT C0 : ℝ}
    (hH : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (τ : D.what₂.Tau) :
    GapAtLeast (epsSH D.R) (lamD D τ) (Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hbnd, _, _, _, _, hstep, _, _, _, hCl⟩ := hH.1
  have hL := one_lt_scL large₂
  have hG0 : 0 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by
    have : 0 ≤ Cl := hCl.le
    have : 0 ≤ large₂.sc.L := by linarith
    positivity
  have hv : ∀ l, 1 ≤ l → l ≤ D.R.k - 1 → 0 ≤ vOne D τ l := fun l h1 h2 => (hH.2.1.1 τ l h1 h2).1
  have hm := D.R.two_le_m
  have hb1 : 0 ≤ bOne D τ 1 := by
    have h := (hbnd τ 1 le_rfl (by omega)).1
    exact le_trans (le_trans (Real.rpow_nonneg (Nat.cast_nonneg _) _) (le_max_left _ _)) h
  have g := gapAtLeast_of τ _ hG0 hv hb1 (hstep τ)
  intro a b hab
  exact g (Fin.cast (dimS_eq D.R) a) (Fin.cast (dimS_eq D.R) b) hab

theorem deg_eq_fdegHC (D : D7) (ht : cdScaleTie D) {W : LocW D.R.k D.R.rS}
    (l : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W) (hA : GoodS D l A) (h : ℝ)
    (hg : GapAtLeast (epsSH D.R) l h) (hth : Formalism.MainNotions.GapDS.thrE (epsSH D.R) + 1 < h) : A.deg = fdegHC l := by
  obtain ⟨P, hP, hd⟩ := hA.2.2.2.2.2.2.2.2.2.2
  obtain ⟨Q, ⟨hQ, -⟩, hDS⟩ := hA.2.1
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1
  have hQd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ.1
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPd
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPd
  have hQQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQd
  have hQQ' : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hQd
  let u : (Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ)ˣ := ⟨Q * P⁻¹, P * Q⁻¹,
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc P⁻¹, hPP', Matrix.one_mul, hQQ],
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q⁻¹, hQQ', Matrix.one_mul, hPP]⟩
  let a : Formalism.REAL.UJ (epsSH D.R) := ⟨u, GlobalTheory.FormalDegreeDatum.inUJ_of_cayley _ P Q _ hP.1 hP.2 hQ.2⟩
  have hsc := (GlobalTheory.Mem.Vol.cdScaleTie_iff D).1 ht
  obtain ⟨a1, b1, hab⟩ := Formalism.MainNotions.TheoremBConstants.epsSH_both D
  have ht1 : ∃ x, epsSH D.R x = true := by
    cases h1 : epsSH D.R a1
    · exact ⟨b1, by cases h2 : epsSH D.R b1 <;> simp_all⟩
    · exact ⟨a1, h1⟩
  have hf1 : ∃ x, epsSH D.R x = false := by
    cases h1 : epsSH D.R a1
    · exact ⟨a1, h1⟩
    · exact ⟨b1, by cases h2 : epsSH D.R b1 <;> simp_all⟩
  have hF := GlobalTheory.T.harishChandra_formalDegree_compactDual_large_gaps D.cd D.s.cdScale hsc _ (epsSH D.R) l h hA.1 ht1 hf1 hg hth A.H
    (fun g => A.σ (Q⁻¹ * g * Q)) hDS
  haveI := hDS.2.1
  obtain ⟨w, hw⟩ := exists_ne (0 : A.H)
  have h2 := GlobalTheory.FormalDegreeDatum.fdeg_of_conj _ (fun g => A.σ (P⁻¹ * g * P))
    (fun g => A.σ (Q⁻¹ * g * Q)) a (fun g => by
      have e : umat (a * g * a⁻¹) = Q * P⁻¹ * umat g * (P * Q⁻¹) := rfl
      have e2 : Q⁻¹ * (Q * P⁻¹ * umat g * (P * Q⁻¹)) * Q =
          (Q⁻¹ * Q) * (P⁻¹ * umat g * P) * (Q⁻¹ * Q) := by
        simp only [Matrix.mul_assoc]
      simp only [e, e2, hQQ', Matrix.one_mul, Matrix.mul_one]) hDS.2.2.1 A.deg hd w hw
  have h3 := GlobalTheory.FormalDegreeDatum.fdeg_of_conj _ (fun g => A.σ (Q⁻¹ * g * Q))
    (fun g => A.σ (Q⁻¹ * g * Q)) 1 (fun g => by simp) hDS.2.2.1 (fdegHC l) hF w hw
  exact h2.symm.trans h3

theorem deg_eq_near (D : D7) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT C0 Cn : ℝ} (hCl : 2 * |Cn| + 8 ≤ Cl)
    (hH : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (ht : cdScaleTie D) (τ : D.what₂.Tau) {W : LocW D.R.k D.R.rS}
    (ν : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (hν : l1dist ν (lamD D τ) ≤ |Cn| * (D.R.r : ℝ) ^ 4 + D.R.r)
    (A : LocS W) (hA : GoodS D ν A) : A.deg = fdegHC ν := by
  refine deg_eq_fdegHC D ht ν A hA _ (gap_near _ _ _ _ _ (gap_lamD D large₂ hH τ) hν) ?_
  obtain ⟨_, _, hmf, _⟩ := hH.1
  have hL := one_lt_scL large₂
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hr6 : (6 : ℝ) ≤ D.R.r := by
    have : 6 ≤ D.R.r := by unfold Formalism.BasicNotions.Ranks.r; omega
    exact_mod_cast this
  have hthr := Formalism.MainNotions.GapDS.thrE_le (epsSH D.R) (by rw [Formalism.MainNotions.BridgeLemma₂.deg_cast_r]; linarith)
  rw [Formalism.MainNotions.BridgeLemma₂.deg_cast_r] at hthr
  have hf : (1 : ℝ) ≤ D.R.f := by
    have : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (by omega)) hmf
    exact_mod_cast this
  have hn1 : (1 : ℝ) ≤ D.R.r := by linarith
  have h419 : (D.R.r : ℝ) ^ 4 ≤ (D.R.r : ℝ) ^ 19 := pow_le_pow_right₀ hn1 (by norm_num)
  have h319 : (D.R.r : ℝ) ^ 3 ≤ (D.R.r : ℝ) ^ 19 := pow_le_pow_right₀ hn1 (by norm_num)
  have h119 : (D.R.r : ℝ) ≤ (D.R.r : ℝ) ^ 19 := by
    simpa using pow_le_pow_right₀ hn1 (show 1 ≤ 19 by norm_num)
  have hf5 : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := one_le_pow₀ hf
  have hfl : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 5 * large₂.sc.L := by nlinarith
  have hCl0 : 0 ≤ Cl * (D.R.r : ℝ) ^ 19 := mul_nonneg (by linarith [abs_nonneg Cn]) (by positivity)
  have e1 : Cl * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by
    have := mul_le_mul_of_nonneg_left hfl hCl0
    have e : Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L = Cl * (D.R.r : ℝ) ^ 19 * ((D.R.f : ℝ) ^ 5 * large₂.sc.L) := by
      ring
    rw [e]; linarith
  have e2 : (2 * |Cn| + 8) * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 :=
    mul_le_mul_of_nonneg_right hCl (by positivity)
  have e3 : |Cn| * (D.R.r : ℝ) ^ 4 ≤ |Cn| * (D.R.r : ℝ) ^ 19 := mul_le_mul_of_nonneg_left h419 (abs_nonneg _)
  nlinarith

theorem deg_VandLine_of_gap : ∀ Cn : ℝ, ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 C1 : ℝ),
    thr ≤ C' → thr ≤ Cl → Ties D → Formalism.MainNotions.BridgeLemma₂.deg_VandLine D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 := by
  intro Cn
  refine ⟨2 * |Cn| + 8, fun D large₂ C' Cl Cg cb Cu cT CT C0 C1 _ hCl hT => ?_⟩
  intro hH τ w w' _ θ _ W _ lam' hl A hA I s hs A' hA'
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hkr : (D.R.k : ℝ) ≤ D.R.r := by
    have : D.R.k ≤ D.R.r := by unfold Formalism.BasicNotions.Ranks.r; omega
    exact_mod_cast this
  have hmr : (D.R.m : ℝ) ≤ D.R.r := by
    have : D.R.m ≤ D.R.r := by unfold Formalism.BasicNotions.Ranks.r; omega
    exact_mod_cast this
  have hn : (D.R.k : ℝ) * (D.R.m : ℝ) ^ 3 ≤ (D.R.r : ℝ) ^ 4 := by
    calc (D.R.k : ℝ) * (D.R.m : ℝ) ^ 3 ≤ (D.R.r : ℝ) * (D.R.r : ℝ) ^ 3 :=
          mul_le_mul hkr (pow_le_pow_left₀ (by positivity) hmr 3) (by positivity) (by positivity)
      _ = (D.R.r : ℝ) ^ 4 := by ring
  have hcard : (I.card : ℝ) ≤ D.R.r := by
    rw [← Formalism.MainNotions.BridgeLemma₂.deg_cast_r]
    have : I.card ≤ 2 * D.R.rS + D.R.k + 1 := by
      have := Finset.card_le_univ I
      rwa [Fintype.card_fin] at this
    exact_mod_cast this
  have hl' : Cn * D.R.k * (D.R.m : ℝ) ^ 3 ≤ |Cn| * (D.R.r : ℝ) ^ 4 := by
    have e : Cn * D.R.k * (D.R.m : ℝ) ^ 3 = Cn * ((D.R.k : ℝ) * (D.R.m : ℝ) ^ 3) := by ring
    rw [e]
    exact le_trans (mul_le_mul_of_nonneg_right (le_abs_self Cn) (by positivity))
      (mul_le_mul_of_nonneg_left hn (abs_nonneg _))
  have hr0 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
  have h1 : l1dist lam' (lamD D τ) ≤ |Cn| * (D.R.r : ℝ) ^ 4 + D.R.r := by linarith
  have h2 : l1dist (lam' + s • epsI I) (lamD D τ) ≤ |Cn| * (D.R.r : ℝ) ^ 4 + D.R.r :=
    le_trans (Formalism.MainNotions.BridgeLemma.l1_distance_sign_step _ _ s hs I) (by linarith)
  rw [deg_eq_near D large₂ hCl hH hT.cdScale_tie τ lam' h1 A hA,
    deg_eq_near D large₂ hCl hH hT.cdScale_tie τ _ h2 A' hA']

end GlobalTheory.DegLine
end
end
