module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle064
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EmbeddingIntegerAlgebraMap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle080
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocalDenominators
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle008
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdECut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle011
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.VolPinAsm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.PtMatIsUnit
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle070
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxAt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle037
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle067
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle075
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle063
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle081
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle071
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RealDecompL
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RelCharPfRat
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle018
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PcBridgeB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle051
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle078

@[expose] public section

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching ValuativeRel

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open CohCut

namespace CohGoodPf

variable {D : Formalism.BasicNotions.D7} {u : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}

def wG (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) {T' : D.host.E} (F'₂ : LFlag (D.sp.Y 0) D.R.rS T') :
    Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → (VS D).V :=
  Sum.elim (frame (lf D F0)) (frame F'₂)

def gramG (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) {T' : D.host.E} (F'₂ : LFlag (D.sp.Y 0) D.R.rS T') :
    Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) D.host.E :=
  Matrix.of fun i j => brS (VS D) (wG F0 F'₂ j) (wG F0 F'₂ i)

variable (Zd : LocDat D) (p : PlF D)

def sK : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → (D.s.atP p).Ep :=
  Sum.elim (fun a => sgnP D p a * frFac Zd.δ p a) (fun b => sgnP' D p b * frFac Zd.δ p b)

def sI : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → (D.s.atP p).Ep :=
  Sum.elim (fun a => sgnP D p a * Formalism.L2.SG.Pf.BBTie.btT Zd p ^ (D.R.rS - a.val))
    (fun b => sgnP' D p b * Formalism.L2.SG.Pf.BBTie.btT Zd p ^ (D.R.rS - b.val))

theorem frFac_mul (a : Fin (D.R.rS + 1)) :
    frFac Zd.δ p a * Formalism.L2.SG.Pf.BBTie.btT Zd p ^ (D.R.rS - a.val) = 1 := by
  unfold frFac
  exact Ring.inverse_mul_cancel _ ((Formalism.L2.SG.Pf.BBTie.bt_T_unit Zd p).pow _)

theorem sI_mul (k : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) : sI Zd p k * sK Zd p k = 1 := by
  cases k with
  | inl a =>
    show sgnP D p a * Formalism.L2.SG.Pf.BBTie.btT Zd p ^ (D.R.rS - a.val) * (sgnP D p a * frFac Zd.δ p a) = 1
    calc _ = (sgnP D p a * sgnP D p a) * (frFac Zd.δ p a * Formalism.L2.SG.Pf.BBTie.btT Zd p ^ (D.R.rS - a.val)) := by ring
      _ = 1 := by rw [localSign_sq, frFac_mul, one_mul]
  | inr b =>
    show sgnP' D p b * Formalism.L2.SG.Pf.BBTie.btT Zd p ^ (D.R.rS - b.val) * (sgnP' D p b * frFac Zd.δ p b) = 1
    calc _ = (sgnP' D p b * sgnP' D p b) * (frFac Zd.δ p b * Formalism.L2.SG.Pf.BBTie.btT Zd p ^ (D.R.rS - b.val)) := by ring
      _ = 1 := by rw [sgnP'_sq, frFac_mul, one_mul]

variable {Zd p}

theorem split_none (hs : (Zd.M p).split = none) : (D.s.atP p).split = none := by
  have hA := (Zd.agree p).2.2.2.2.2
  rw [hs] at hA
  cases h2 : (D.s.atP p).split with
  | none => rfl
  | some sg =>
    rw [h2] at hA
    exact (hA : False).elim

theorem sI_mem (hs : (Zd.M p).split = none) (hδ : Zd.δ p ∈ 𝒪[(D.s.atP p).Fp])
    (hu : (D.s.atP p).ιE (uP p : D.host.E) ∈ (D.s.atP p).O) (k : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) :
    sI Zd p k ∈ (D.s.atP p).O := by
  have hs' := split_none hs
  have hT : Formalism.L2.SG.Pf.BBTie.btT Zd p ∈ (D.s.atP p).O :=
    Subring.mul_mem _ (Formalism.L2.SG.Pf.LocalDenominators.alg_mem_O (D.s.atP p) hδ) hu
  cases k with
  | inl a =>
    refine Subring.mul_mem _ ?_ (Subring.pow_mem _ hT _)
    show sgnP D p a ∈ _
    unfold TermLoc.sgnP
    rw [hs']
    exact Subring.one_mem _
  | inr b =>
    refine Subring.mul_mem _ ?_ (Subring.pow_mem _ hT _)
    show sgnP' D p b ∈ _
    unfold TermLoc.sgnP'
    rw [hs']
    exact Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _

theorem cj_mem (y : (D.s.atP p).Ep) (hy : y ∈ (D.s.atP p).O) : (D.s.atP p).cj y ∈ (D.s.atP p).O := by
  rw [(D.s.atP p).O_def] at hy ⊢
  exact hy.map (((D.s.atP p).cj : (D.s.atP p).Ep →ₐ[(D.s.atP p).Fp] (D.s.atP p).Ep).restrictScalars
    𝒪[(D.s.atP p).Fp])

variable {u' : D.what₂.Word} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem vP_eq' (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (hs : (Zd.M p).split = none) : vP Zd p γ F'₂ = fun k => sK Zd p k • baseChange₂ D p (wG F0 F'₂ k) := by
  rw [vP_eq Zd γ F'₂ hs]
  funext k
  cases k <;> rfl

theorem gram_vP (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (hs : (Zd.M p).split = none) :
    (locH Zd p).gram (vP Zd p γ F'₂) = Matrix.diagonal (fun k => (Zd.M p).L.cj (sK Zd p k)) *
      (gramG F0 F'₂).map (D.s.atP p).ιE * Matrix.diagonal (sK Zd p) := by
  rw [vP_eq' γ F'₂ hs]
  ext i j
  simp only [Formalism.MainNotions.S.Loc.HermSp.gram, Matrix.of_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.map_apply,
    gramG]
  rw [Formalism.L2.SG.Pf.ScalarFramePf.h_bcP]
  ring

theorem gramInv_at (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (hdet : (gramG F0 F'₂).det ≠ 0) (hs : (Zd.M p).split = none) (hδ : Zd.δ p ∈ 𝒪[(D.s.atP p).Fp])
    (hu : (D.s.atP p).ιE (uP p : D.host.E) ∈ (D.s.atP p).O)
    (hent : ∀ i j, (D.s.atP p).ιE ((gramG F0 F'₂)⁻¹ i j) ∈ (D.s.atP p).O) :
    Formalism.MainNotions.S.Loc.HermSp.CohU.GramInv (locH Zd p) (vP Zd p γ F'₂) := by
  have hO : (Zd.M p).L.O = (D.s.atP p).O := Formalism.L2.SG.Pf.LocalDenominators.hO Zd p
  have hcj : (Zd.M p).L.cj = (D.s.atP p).cj := Zd.hcj p
  set M := gramG F0 F'₂ with hMdef
  set ι := (D.s.atP p).ιE with hι
  refine ⟨Matrix.diagonal (sI Zd p) * M⁻¹.map ι * Matrix.diagonal (fun k => (Zd.M p).L.cj (sI Zd p k)),
    fun i j => ?_, ?_⟩
  · simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.map_apply]
    rw [hO, hcj]
    exact Subring.mul_mem _ (Subring.mul_mem _ (sI_mem hs hδ hu i) (hent i j)) (cj_mem _ (sI_mem hs hδ hu j))
  · rw [gram_vP γ F'₂ hs]
    have hM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet)
    have hmap : M⁻¹.map ι * M.map ι = 1 := by
      rw [← Matrix.map_mul, hM, Matrix.map_one _ (map_zero ι) (map_one ι)]
    have hc1 : (fun k => (Zd.M p).L.cj (sI Zd p k) * (Zd.M p).L.cj (sK Zd p k)) = fun _ => 1 := by
      funext k; rw [← map_mul, sI_mul, map_one]
    have hs1 : (fun k => sI Zd p k * sK Zd p k) = fun _ => 1 := funext fun k => sI_mul Zd p k
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Matrix.diagonal fun k => (Zd.M p).L.cj (sI Zd p k)), Matrix.diagonal_mul_diagonal, hc1,
      Matrix.diagonal_one, Matrix.one_mul, ← Matrix.mul_assoc (M⁻¹.map ι), hmap, Matrix.one_mul,
      Matrix.diagonal_mul_diagonal, hs1, Matrix.diagonal_one]

end CohGoodPf

open CohGoodPf

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}


variable (u u' F0 what₂) in
def GlobGramNe : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)),
    Ctx γ Z → ZhatL (lf D F0) F'₂ = Z → (gramG F0 F'₂).det ≠ 0

theorem cohGood_of (hGG : GlobGramNe u u' F0 what₂) : CohGood Zd u u' F0 what₂ := by
  intro hP γ Z F'₂ φ' hH
  have hdet := hGG hP γ Z F'₂ hH.1 hH.2.1
  set X : Finset D.host.E := Finset.univ.image (fun ij : (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) ×
    (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) => (gramG F0 F'₂)⁻¹ ij.1 ij.2) with hX
  have hgood := Formalism.L2.SG.Pf.LocModel.good_cofinite Zd.δ Zd.M Zd.agree X
  rw [Filter.eventually_cofinite] at hgood
  refine hgood.subset fun p hp => ?_
  by_contra hn
  simp only [Set.mem_ofPred_eq, not_not] at hn
  apply hp
  obtain ⟨hs, hδ, hu, hXm⟩ := hn
  refine gramInv_at γ F'₂ hdet hs hδ.1 hu.1 fun i j => ?_
  by_cases h0 : (gramG F0 F'₂)⁻¹ i j = 0
  · rw [h0, map_zero]; exact Subring.zero_mem _
  · have hmem : (gramG F0 F'₂)⁻¹ i j ∈ X := Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩
    have h := (hXm _ hmem 0 (by simpa using h0)).1
    simpa using h

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section

noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section CloseAt

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

theorem diag_mul_diag_apply {K : Type*} [CommRing K] {n : ℕ} (a b : Fin n → K) (X : Matrix (Fin n) (Fin n) K)
    (i j : Fin n) : (Matrix.diagonal a * X * Matrix.diagonal b) i j = a i * X i j * b j := by
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal]


theorem close_at {p : PlF D} (hA : Agree δ M p) (h : ProdE.StP M δ u u' w p) (c : (D.s.atP p).Fp) (hc0 : c ≠ 0)
    (hc : c ∈ 𝒪[(D.s.atP p).Fp]) :
    ∃ τ : ProdE.MP p, (∀ i j, i < j → τ i j = 0) ∧ (∀ i, τ i i = 1) ∧
      (∀ i j, Formalism.L2.SG.Pf.fσ w j < Formalism.L2.SG.Pf.fσ w i → τ i j = 0) ∧
      ∃ c' : (D.s.atP p).Fp, c' ≠ 0 ∧ c' ∈ 𝒪[(D.s.atP p).Fp] ∧ ∀ g : Formalism.L2.SG.Pf.VolPinAsm.StG w,
        EntIn (latS (D.s.atP p) c') (((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D).map (D.s.atP p).ιE - τ) →
        EntIn (latS (D.s.atP p) c) (((h⁻¹ * ProdE.πP M δ u u' w hA g).1.1 : ProdE.MP p) - 1) ∧
          EntIn (latS (D.s.atP p) c) (((h⁻¹ * ProdE.πP M δ u u' w hA g).1.2.unop : ProdE.MP p) - 1) := by
  obtain ⟨ex, ey, d, di, gg, ggi, hexO, heyO, hxx, hyy, hsum, hxy, hd, hg, hlin⟩ := mode_data M δ hA
  obtain ⟨N, Ni, hN, hN', ⟨ν, hν, hNν⟩, hfix⟩ := exists_unit_monomial_stable_of_Y0 M δ u u' w hA
  set σ := Formalism.L2.SG.Pf.fσ w with hσd
  have hσ : ∀ a, σ (σ a) = a := Formalism.L2.SG.Pf.fσ_fσ w
  set h1 : ProdE.GLp p := h.1.1 with hh1d
  set h2 : ProdE.GLp p := h.1.2.unop with hh2d
  obtain ⟨hh1, hh2, hh3⟩ := h.2
  have hh : (h1 : ProdE.MP p) * N * (h2 : ProdE.MP p) = N := hfix _ _ hh1 hh2 hh3
  obtain ⟨hi1, hi2, -⟩ := (h⁻¹).2
  have hΔ : Matrix.diagonal d * Matrix.diagonal di = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact hd i
  have hΓ : Matrix.diagonal gg * Matrix.diagonal ggi = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact hg i
  have hΓ' : Matrix.diagonal ggi * Matrix.diagonal gg = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; rw [mul_comm]; exact hg i
  obtain ⟨c', hc'0, hc'O, hcl⟩ := close ex ey hexO heyO hxx hyy hsum hxy N Ni (Matrix.diagonal d) (Matrix.diagonal di)
    (Matrix.diagonal gg) (Matrix.diagonal ggi) hN hN' hΔ hΓ hΓ' h1 h2 hh c hc0 hc

  have h1inv : ((h1⁻¹ : ProdE.GLp p) : ProdE.MP p) * (h1 : ProdE.MP p) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2inv : (h2 : ProdE.MP p) * ((h2⁻¹ : ProdE.GLp p) : ProdE.MP p) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have rel1 : (h1 : ProdE.MP p) * mono σ ν = mono σ ν * ((h2⁻¹ : ProdE.GLp p) : ProdE.MP p) := by
    rw [← hNν]
    calc (h1 : ProdE.MP p) * N = (h1 : ProdE.MP p) * N * ((h2 : ProdE.MP p) * ((h2⁻¹ : ProdE.GLp p) : ProdE.MP p)) := by
          rw [h2inv, Matrix.mul_one]
      _ = N * ((h2⁻¹ : ProdE.GLp p) : ProdE.MP p) := by rw [← Matrix.mul_assoc, hh]
  have rel2 : ((h1⁻¹ : ProdE.GLp p) : ProdE.MP p) * mono σ ν = mono σ ν * (h2 : ProdE.MP p) := by
    rw [← hNν]
    calc ((h1⁻¹ : ProdE.GLp p) : ProdE.MP p) * N
        = ((h1⁻¹ : ProdE.GLp p) : ProdE.MP p) * ((h1 : ProdE.MP p) * N * (h2 : ProdE.MP p)) := by rw [hh]
      _ = N * (h2 : ProdE.MP p) := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1inv, Matrix.one_mul]
  refine ⟨ex • (Matrix.diagonal di * (h1 : ProdE.MP p) * Matrix.diagonal d) +
      ey • (Matrix.diagonal gg * (h2 : ProdE.MP p) * Matrix.diagonal ggi).transpose, ?_, ?_, ?_, c', hc'0, hc'O, ?_⟩
  · intro i j hij
    have a1 : (h1 : ProdE.MP p) i j = 0 := (hh1 i j).1 hij
    have a2 : (h2 : ProdE.MP p) j i = 0 := (hh2 j i).1 hij
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.transpose_apply, diag_mul_diag_apply,
      diag_mul_diag_apply, a1, a2]
    simp
  · intro i
    have a1 : (h1 : ProdE.MP p) i i = 1 := (hh1 i i).2 rfl
    have a2 : (h2 : ProdE.MP p) i i = 1 := (hh2 i i).2 rfl
    have t1 : (Matrix.diagonal di * (h1 : ProdE.MP p) * Matrix.diagonal d) i i = 1 := by
      rw [diag_mul_diag_apply, a1, mul_one, mul_comm, hd i]
    have t2 : (Matrix.diagonal gg * (h2 : ProdE.MP p) * Matrix.diagonal ggi) i i = 1 := by
      rw [diag_mul_diag_apply, a2, mul_one, hg i]
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.transpose_apply, t1, t2, smul_eq_mul,
      smul_eq_mul, mul_one, mul_one, hsum]
  · intro i j hij
    have e1 : (h1 : ProdE.MP p) i j = 0 :=
      fix_pat hσ ν hν (fun a b hab => (hi2 a b).1 hab) rel1 i j hij
    have e2 : (h2 : ProdE.MP p) j i = 0 := by
      have z : ((h1⁻¹ : ProdE.GLp p) : ProdE.MP p) (σ j) (σ i) = 0 := (hi1 (σ j) (σ i)).1 hij
      have := fix_entry hσ ν rel2 (σ j) (σ i)
      rw [hσ, hσ, z, zero_mul] at this
      exact (hν (σ j)).mul_right_eq_zero.1 this.symm
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.transpose_apply, diag_mul_diag_apply,
      diag_mul_diag_apply, e1, e2]
    simp
  · intro g hG
    set π := ProdE.πP M δ u u' w hA g with hπd
    set l : ProdE.GLp p := π.1.1 with hld
    set ρ : ProdE.GLp p := π.1.2.unop with hρd
    obtain ⟨hk1, hk2, -⟩ := (h⁻¹ * π).2
    obtain ⟨hπl, hπρ, hπ⟩ := π.2
    have ek1 : ((h⁻¹ * π).1.1 : ProdE.GLp p) = h1⁻¹ * l := rfl
    have ek2 : ((h⁻¹ * π).1.2.unop : ProdE.GLp p) = ρ * h2⁻¹ := rfl
    have hk1' : Formalism.MainNotions.S.IsLoUni (((h1⁻¹ * l : ProdE.GLp p)) : ProdE.MP p) := by rw [← ek1]; exact hk1
    have hk2' : Formalism.MainNotions.S.IsUpUni (((ρ * h2⁻¹ : ProdE.GLp p)) : ProdE.MP p) := by rw [← ek2]; exact hk2
    have hl : ex • ((l : ProdE.GLp p) : ProdE.MP p) =
        ex • (Matrix.diagonal d * ((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D).map (D.s.atP p).ιE *
          Matrix.diagonal di) :=
      (hlin (g : Formalism.L2.SG.PairVal.GLR D) (Formalism.L2.SG.Pf.VolPinAsm.bOf w g)).1
    have hρ : ey • ((ρ : ProdE.GLp p) : ProdE.MP p) =
        ey • (Matrix.diagonal ggi * (((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D).map
          (D.s.atP p).ιE).transpose * Matrix.diagonal gg) :=
      (hlin (g : Formalism.L2.SG.PairVal.GLR D) (Formalism.L2.SG.Pf.VolPinAsm.bOf w g)).2
    have hlN : ((l : ProdE.GLp p) : ProdE.MP p) * N * ((ρ : ProdE.GLp p) : ProdE.MP p) = N := hfix _ _ hπl hπρ hπ
    have res := hcl l ρ (((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D).map (D.s.atP p).ιE)
      (fun i j hij => by
        rcases lt_or_eq_of_le hij with h' | h'
        · rw [Matrix.sub_apply, (hk1' i j).1 h', Matrix.one_apply_ne (ne_of_lt h'), sub_zero]
        · subst h'
          rw [Matrix.sub_apply, (hk1' i i).2 rfl, Matrix.one_apply_eq, sub_self])
      (fun i j hij => by
        rcases lt_or_eq_of_le hij with h' | h'
        · rw [Matrix.sub_apply, (hk2' i j).1 h', Matrix.one_apply_ne (ne_of_gt h'), sub_zero]
        · subst h'
          rw [Matrix.sub_apply, (hk2' j j).2 rfl, Matrix.one_apply_eq, sub_self])
      hlN hl hρ hG
    rw [ek1, ek2]
    exact res

end CloseAt

end Formalism.L2.SG.Pf.ProdEApprox
end
end

section

noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Good2

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

theorem mem_R_none {p : PlF D} (hA : Agree δ M p) (hs : (M p).split = none) (x : (D.s.atP p).Ep) :
    x ∈ (M p).R ↔ x ∈ (D.s.atP p).O := by
  obtain ⟨-, -, -, hO, -, -⟩ := hA
  show x ∈ (⟨(M p).L, (M p).split, (M p).mu⟩ : Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep).R ↔ _
  rw [hs]
  show x ∈ (M p).L.O ↔ _
  rw [hO]

theorem bOf_int {p : PlF D} (g : Formalism.L2.SG.Pf.VolPinAsm.StG w)
    (hg : ∀ i j, (D.s.atP p).ιE (((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) i j) ∈ (D.s.atP p).O)
    (hpv : ∀ a : Fin (D.R.rS + 1), (D.s.atP p).ιE (Formalism.L2.SG.Pf.pv w.1 a) ∈ (D.s.atP p).O ∧
      (D.s.atP p).ιE ((Formalism.L2.SG.Pf.pv w.1 a)⁻¹) ∈ (D.s.atP p).O) :
    ∀ i j, (D.s.atP p).ιE (Formalism.L2.SG.Pf.VolPinAsm.bOf w g i j) ∈ (D.s.atP p).O := by
  set σ := Formalism.L2.SG.Pf.fσ w
  have hσ : ∀ x, σ (σ x) = x := Formalism.L2.SG.Pf.fσ_fσ w
  set ν : Fin (D.R.rS + 1) → D.host.E := fun x => Formalism.L2.SG.Pf.pv w.1 x
  have hν : ∀ x, IsUnit (ν x) := fun x => isUnit_iff_ne_zero.2 (Formalism.L2.SG.Pf.pv_ne' w x)
  set a := ((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D)
  set b := Formalism.L2.SG.Pf.VolPinAsm.bOf w g
  obtain ⟨-, hb, hW⟩ := ProdE.bOf_spec w g
  have hfix := fix_cOf hσ ν hν a
  have hWu : IsUnit (ptMat w).det := Formalism.L2.SG.Pf.StabilizerIndexVolumes.ptMat_isUnit w
  have hcb : cOf σ ν a * b = 1 := by
    have h1 : ptMat w * (cOf σ ν a * b) = ptMat w * 1 := by
      rw [Matrix.mul_one, ← Matrix.mul_assoc]
      conv_lhs => rw [ptMat_mono]
      rw [← hfix, ← ptMat_mono]
      exact hW
    have := congrArg (fun X => (ptMat w)⁻¹ * X) h1
    simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hWu, Matrix.one_mul] using this
  have hbinv : b = (cOf σ ν a)⁻¹ := (Matrix.inv_eq_right_inv hcb).symm
  have hcU : IsUpUni (cOf σ ν a) := by
    have := (ZsVolGrp.isUpUni_inv hb).1
    rwa [show b⁻¹ = cOf σ ν a from Matrix.inv_eq_left_inv hcb] at this
  have hdet : (cOf σ ν a).det = 1 :=
    ZsVolGrp.det_up (fun x => (hcU x x).2 rfl) (fun x y hxy => (hcU x y).1 hxy)
  have hcO : ∀ x y, (D.s.atP p).ιE (cOf σ ν a x y) ∈ (D.s.atP p).O := by
    intro x y
    simp only [cOf, Matrix.of_apply, Ring.inverse_eq_inv', map_mul]
    exact (D.s.atP p).O.mul_mem ((D.s.atP p).O.mul_mem (hpv (σ x)).2 (hg _ _)) (hpv (σ y)).1
  intro i j
  rw [hbinv, ZsVolGrp.inv_eq_adj hdet]
  have e := congrFun (congrFun (RingHom.map_adjugate (D.s.atP p).ιE (cOf σ ν a)) i) j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at e
  rw [e]
  exact ZsVolGrp.adj_mem (D.s.atP p).O (fun x y => by simpa using hcO x y) i j

end Good2

end Formalism.L2.SG.Pf.ProdEApprox
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolOrb

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem stabilizer_in_congruence_holds : StabInCZ M δ u u' F0 what₂ :=
  Formalism.L2.SG.Pf.ZsVolIn.stabInCZ_of M δ u u' F0 what₂ (Formalism.L2.SG.Pf.ZsVolLat.frameShape_holds M δ u u' F0 what₂)

theorem orbStabE_of_act (h : OrbActE M δ u u' F0 what₂) : Formalism.L2.SG.Pf.ZsVolCut.OrbStabE M δ u u' F0 what₂
    (Formalism.L2.SG.Pf.ZsVolCut.CZ M δ u u') :=
  orbStabE_of M δ u u' F0 what₂ (stabilizer_in_congruence_holds M δ u u' F0 what₂) h
    (Formalism.L2.SG.Pf.ZsVolFin.orbitFinite_holds M δ u u' F0 what₂)

end Formalism.L2.SG.Pf.ZsVolOrb

end
end

section

namespace Formalism.L2.SG.Pf

theorem formRelC_holds : Formalism.L2.SG.Pf.FormRel.FormRelC :=
  formRelC_of (fun D X Y u u' => Formalism.L2.SG.Pf.RowForm.RealDecompL.realDecompC_of X Y u u'
    (Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u')) Formalism.L2.SG.Pf.RelChar.relCharC_holds

theorem formNGC_holds : Formalism.L2.SG.NGVanish.FormNGC := formNGC_of_rel formRelC_holds

theorem formGC_holds : Formalism.L2.SG.Pf.MainEqVanish.FormGC := formGC_of_rel formRelC_holds

end Formalism.L2.SG.Pf
end

section

namespace Formalism.L2.SG.Pf.PCount

theorem partnerCount_holds_all {D : Formalism.BasicNotions.D7} (Zd : Formalism.L2.SG.TermLoc.LocDat D) : PartnerIsomorphismCount Zd :=
  partnerCount_of_iso Zd (Formalism.L2.SG.LsDatumA.integralClosureRank_and_residueTrdegLe D) (intGenP_holds Zd) BI.integralIsomorphism_holds

end Formalism.L2.SG.Pf.PCount
end
