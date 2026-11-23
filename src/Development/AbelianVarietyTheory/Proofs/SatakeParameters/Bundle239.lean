module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle018
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle205
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle210
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle741
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle149
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle010
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle235
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle224
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle020
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle232
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle163
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle236
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaUnitFunctionShortModelIntegral
public import Formalism.LocalToGlobal.KernelLattices.Bundle003
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle015
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle237
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.InertOkH

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem csum_zero_left {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) (g : S.Cl → S.V) : S.csum 0 g = 0 := by
  simp [CSD.csum]

theorem csum_zero_right {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) (f : S.Cl → S.V) : S.csum f 0 = 0 := by
  simp [CSD.csum]



theorem inertHeckeOperators_rows_rational_adjointClosed (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hW : R.WeakCharacterisation F) (hJ : InertJunk A3) (t : T) :
    (A3.rowI t).InertRationalAdjoint := by
  obtain ⟨tie⟩ := hW.inert.hR t
  have hrk : D.sp.X'.rank = A3.A.r + D.R.m * A3.A.t := R.toRealDat.B.rankR
  have hpl := (GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hW).2.2.1 t
  have key := GlobalTheory.T.inertHeckeOperators_rows_rational_selfAdjoint_labels R.toRealDat F.lv2 hW.base.lev hW.base.fam hW.base.models t (A3.okI t × List ℕ)
    (fun i => R.plI i.1) (fun i => Formalism.IndefR.Links.labIn D.sp.X'.rank i.2) (A3.heckeRI t)
    (fun i => Formalism.L2.Col.InertTypeOk D.sp.X'.rank i.2)
    (fun i hi => ⟨(hpl i.1 i.1.2).1, (hpl i.1 i.1.2).2,
      ((GlobalTheory.T.selfDual_antitone_list_iff_inertPrimeHeckeExponents D.sp.X'.rank (Formalism.IndefR.Links.labIn D.sp.X'.rank i.2)).mpr ⟨i.2, hi.2.2, hi.1, hi.2.1, rfl⟩).2.1⟩) tie
  have hop : ∀ k : A3.okI t × List ℕ, A3.heckeRI t k = 0 ∨
      ∃ s', Formalism.L2.Col.InertTypeOk D.sp.X'.rank s' ∧ A3.heckeRI t k = A3.heckeRI t (k.1, s') := by
    rintro ⟨Q, s⟩
    rcases hJ.R t Q s with h | ⟨s', hs', h⟩
    · exact Or.inl h
    · exact Or.inr ⟨s', hrk ▸ hs', h⟩
  refine ⟨fun k a b => ?_, fun k => ⟨k, fun f g => ?_⟩⟩
  · show LinearMap.toMatrix (A3.A.MtildeCSD t).basis (A3.A.MtildeCSD t).basis (A3.heckeRI t k) a b ∈ cmMax D.what₂.LL
    rcases hop k with h | ⟨s', hs', h⟩
    · rw [h]
      simp only [map_zero]
      exact zero_mem _
    · rw [h]
      exact (key (k.1, s') hs').1 a b
  · rcases hop k with h | ⟨s', hs', h⟩
    · have h0 : (A3.rowI t).opI k = 0 := h
      rw [h0]
      simp only [LinearMap.zero_apply, ZeroMemClass.coe_zero, csum_zero_left, csum_zero_right]
    · have h1 : (A3.rowI t).opI k = A3.heckeRI t (k.1, s') := h
      rw [h1]
      exact (key (k.1, s') hs').2.1 f g



theorem inertHeckeOperators_lifts_rational_adjointClosed (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hW : R.WeakCharacterisation F) (hJ : InertJunk A3) (j : Fin D.R.m) (t : T) :
    (A3.liftI j t).InertRationalAdjoint := by
  obtain ⟨tie⟩ := hW.inert.hL j t
  have hrk : (Vc D j).rank = A3.A.r + A3.A.t := R.toRealDat.B.rankL j
  have hpl := (GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hW).2.2.1 t
  have key := GlobalTheory.T.inertHeckeOperators_lifts_rational_selfAdjoint_labels R.toRealDat F.lv2 hW.base.lev hW.base.fam hW.base.models j t (A3.okI t × List ℕ)
    (fun i => R.plI i.1) (fun i => Formalism.IndefR.Links.labIn (Vc D j).rank i.2) (A3.heckeLI j t)
    (fun i => Formalism.L2.Col.InertTypeOk (Vc D j).rank i.2)
    (fun i hi => ⟨(hpl i.1 i.1.2).1, (hpl i.1 i.1.2).2,
      ((GlobalTheory.T.selfDual_antitone_list_iff_inertPrimeHeckeExponents (Vc D j).rank (Formalism.IndefR.Links.labIn (Vc D j).rank i.2)).mpr ⟨i.2, hi.2.2, hi.1, hi.2.1, rfl⟩).2.1⟩) tie
  have hop : ∀ k : A3.okI t × List ℕ, A3.heckeLI j t k = 0 ∨
      ∃ s', Formalism.L2.Col.InertTypeOk (Vc D j).rank s' ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, s') := by
    rintro ⟨Q, s⟩
    rcases hJ.L j t Q s with h | ⟨s', hs', h⟩
    · exact Or.inl h
    · exact Or.inr ⟨s', hrk ▸ hs', h⟩
  refine ⟨fun k a b => ?_, fun k => ⟨k, fun f g => ?_⟩⟩
  · show LinearMap.toMatrix (A3.A.MtCSD j t).basis (A3.A.MtCSD j t).basis (A3.heckeLI j t k) a b ∈ cmMax D.what₂.LL
    rcases hop k with h | ⟨s', hs', h⟩
    · rw [h]
      simp only [map_zero]
      exact zero_mem _
    · rw [h]
      exact (key (k.1, s') hs').1 a b
  · rcases hop k with h | ⟨s', hs', h⟩
    · have h0 : (A3.liftI j t).opI k = 0 := h
      rw [h0]
      simp only [LinearMap.zero_apply, ZeroMemClass.coe_zero, csum_zero_left, csum_zero_right]
    · have h1 : (A3.liftI j t).opI k = A3.heckeLI j t (k.1, s') := h
      rw [h1]
      exact (key (k.1, s') hs').2.1 f g

theorem heckeOperators_rows_lifts_rational_adjointClosed : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → InertJunk A3 → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) ∧ (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hW hJ
  have h2 := hecke_operators_rational_adjoint_closed_of_weak_char R F hW
  exact ⟨fun t => ⟨h2.1 t, inertHeckeOperators_rows_rational_adjointClosed R F hW hJ t⟩, fun j t => ⟨h2.2 j t, inertHeckeOperators_lifts_rational_adjointClosed R F hW hJ j t⟩⟩

end GlobalTheory.InertOkH

end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelA

theorem adjugate_transpose_rev {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (h : A.det ≠ 0) :
    (A.transpose.submatrix Fin.rev id).adjugate = (sgRev n * A.det) • (A⁻¹.transpose.submatrix id Fin.rev) := by
  have hB : (A.transpose.submatrix Fin.rev id).det = sgRev n * A.det := by
    show (A.transpose.submatrix (Fin.revPerm : Equiv.Perm (Fin n)) id).det = _
    rw [Matrix.det_permute, Matrix.det_transpose, sgRev]
  have hI : (A.transpose.submatrix Fin.rev id)⁻¹ = A⁻¹.transpose.submatrix id Fin.rev := by
    show (A.transpose.submatrix (Fin.revPerm : Equiv.Perm (Fin n)) (Equiv.refl _))⁻¹ = _
    rw [Matrix.inv_submatrix_equiv, Matrix.transpose_nonsing_inv]
    rfl
  have hne : (A.transpose.submatrix Fin.rev id).det ≠ 0 := by
    rw [hB]
    refine mul_ne_zero ?_ h
    unfold sgRev
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))) with h1 | h1 <;> rw [h1] <;> norm_num
  rw [← hI, ← hB, Matrix.inv_def, smul_smul, Ring.inverse_eq_inv', mul_inv_cancel₀ hne, one_smul]

end GlobalTheory.TwV.DelA

namespace GlobalTheory.TwV.DelA

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)

theorem posJ_blkJ (j : ℕ) (x : Σ v : Fin (X.Fl.Pj j).nV, Fin ((X.Fl.Pj j).n' v) × (Fin ((X.Fl.Pj j).m + 1) × Fin ((X.Fl.Pj j).m + 1))) :
    posJ X D pos j ⟨x.1, x.2.1⟩ = pos (blkJ X j x) := by
  cases j <;> rfl

theorem levelIndex_row_val_eq (j : ℕ) (x : Σ v : Fin (X.Fl.Pj j).nV, Fin ((X.Fl.Pj j).n' v) × (Fin ((X.Fl.Pj j).m + 1) × Fin ((X.Fl.Pj j).m + 1))) :
    ((idxJ X j x).2.2.1 : ℕ) = x.2.2.1 := by
  cases j <;> rfl

theorem levelIndex_col_val_eq (j : ℕ) (x : Σ v : Fin (X.Fl.Pj j).nV, Fin ((X.Fl.Pj j).n' v) × (Fin ((X.Fl.Pj j).m + 1) × Fin ((X.Fl.Pj j).m + 1))) :
    ((idxJ X j x).2.2.2 : ℕ) = x.2.2.2 := by
  cases j <;> rfl

def kOdd {j : ℕ} (hN : RankTie X D j) (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ)
    (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ) (τ : D.what₂.Tau) : ℂ :=
  (zT X D pos f' τ).det ^ ((D.R.N j : ℤ) - 1) * sgRev (D.R.N j) * (dfr X D hN d f' τ).det

theorem evD_ySub (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) {j : ℕ} (hN : RankTie X D j)
    (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ)
    (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ)
    (hf : ∀ τ, (f' τ).det ≠ 0) (hd : ∀ τ, (dfr X D hN d f' τ).det ≠ 0) (v : X.Pl) (s : Fin (X.G.P.n' v))
    (a t : Fin (NN X.G.P.m X.t j)) :
    evD X D pos ι hN d f' (ySub X Kc j v s a t) =
      (if IsOddPos s then ι (kOdd X D pos hN d f' (pos ⟨v, s⟩)) else 1) *
        ι (zT X D pos (dfr X D hN d f') (pos ⟨v, s⟩) (Fin.cast hN.1.symm a) (Fin.cast hN.1.symm t)) := by
  obtain ⟨_, hE, hO⟩ := GlobalTheory.T.operatorMatrices_at_complexPoint X D pos Kc ι j hN d f' hf hd v s
  have hsym : IsOddPos (pos.symm (pos ⟨v, s⟩)).2 ↔ IsOddPos s := by
    have hb : ∀ b : (Σ v : X.Pl, Fin (X.G.P.n' v)), b = ⟨v, s⟩ → (IsOddPos b.2 ↔ IsOddPos s) := by
      rintro _ rfl; exact Iff.rfl
    exact hb _ (Equiv.symm_apply_apply _ _)
  by_cases ho : IsOddPos s
  · rw [if_pos ho, ySub_odd X Kc j v s ho]
    have h1 := RingHom.map_adjugate (evD X D pos ι hN d f') (YtMat X Kc j v s)
    simp only [RingHom.mapMatrix_apply] at h1
    have h2 := congrFun (congrFun h1 a) t
    rw [Matrix.map_apply] at h2
    rw [h2, hO ho, Matrix.adjugate_smul, Fintype.card_fin,
      show (Fin.cast hN.1.symm : Fin (NN X.G.P.m X.t j) → Fin (D.R.N j)) = ⇑(finCongr hN.1.symm) from rfl,
      Matrix.adjugate_submatrix_equiv_self]
    have h3 := RingHom.map_adjugate ι ((dfr X D hN d f' (pos ⟨v, s⟩)).transpose.submatrix Fin.rev id)
    simp only [RingHom.mapMatrix_apply] at h3
    rw [← h3, adjugate_transpose_rev _ (hd _)]
    have hz : zT X D pos (dfr X D hN d f') (pos ⟨v, s⟩) = ((dfr X D hN d f' (pos ⟨v, s⟩))⁻¹).transpose.submatrix id Fin.rev := by
      unfold zT; rw [if_pos (hsym.2 ho)]
    have hpos : 1 ≤ D.R.N j := by have := rkS X D hN; omega
    have he : ((D.R.N j : ℤ) - 1) = ((NN X.G.P.m X.t j - 1 : ℕ) : ℤ) := by
      rw [← hN.1]; push_cast [Nat.cast_sub hpos]; ring
    rw [hz, kOdd, he, zpow_natCast]
    simp only [Matrix.smul_apply, Matrix.submatrix_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_pow, mul_assoc]
  · rw [if_neg ho, one_mul]
    have h0 : ySub X Kc j v s = dyMat X Kc j v s := by unfold ySub; rw [if_neg ho]
    have hz : zT X D pos (dfr X D hN d f') (pos ⟨v, s⟩) = dfr X D hN d f' (pos ⟨v, s⟩) := by
      unfold zT; rw [if_neg (fun h => ho (hsym.1 h))]
    have h2 := congrFun (congrFun (hE ho) a) t
    rw [Matrix.map_apply] at h2
    rw [h0, h2, hz]
    rfl

end GlobalTheory.TwV.DelA

namespace GlobalTheory.TwV.DelA

theorem evD_subD : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (Gc : XR (X.Pj j) ℂ) (G : (X.Pj j).Xsp), MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι Gc → OddDeg X j G → ∀ (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ) (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ), (∀ τ, (f' τ).det ≠ 0) → (∀ τ, (dfr X D hN d f' τ).det ≠ 0) → evD X D pos ι hN d f' (subD X Kc j G) = ι ((∏ τ, if IsOddPos (pos.symm τ).2 then ((zT X D pos f' τ).det ^ ((D.R.N j : ℤ) - 1) * sgRev (D.R.N j) * (dfr X D hN d f' τ).det) ^ ((D.R.N j : ℤ) * cT1 X D pos j τ - szT X D pos j τ) else 1) * valZ X D pos j (rkS X D hN) Gc (dfr X D hN d f')) := by
  intro p _ X D pos Kc _ _ ι j hN Gc G hG hO d f' hf hd
  let g : Var (X.Pj j) → ℂ := fun y => zT X D pos (dfr X D hN d f') (posJ X D pos j ⟨y.1, y.2.1⟩)
    (Fin.cast (rkS X D hN) y.2.2.1) (Fin.cast (rkS X D hN) y.2.2.2)
  let φ : (X.Pj j).Xsp →+* Kc := (evD X D pos ι hN d f').comp (subD X Kc j : (X.Pj j).Xsp →+* DA X Kc j)
  let ψ : (X.Pj j).Xsp →+* Kc := MvPolynomial.eval₂Hom (algebraMap X.G.Kf Kc) (fun y => ι (g y))
  have hR : ι (valZ X D pos j (rkS X D hN) Gc (dfr X D hN d f')) = ψ G := by
    show ι (MvPolynomial.eval g Gc) = MvPolynomial.eval₂ (algebraMap X.G.Kf Kc) (fun y => ι (g y)) G
    rw [MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left, RingHom.comp_id,
      ← MvPolynomial.eval_map, ← hG, MvPolynomial.eval_map]
    rfl
  have hC : ∀ a, φ (MvPolynomial.C a) = ψ (MvPolynomial.C a) := by
    intro a
    show evD X D pos ι hN d f' (subD X Kc j (MvPolynomial.C a)) = MvPolynomial.eval₂ _ _ (MvPolynomial.C a)
    rw [MvPolynomial.eval₂_C, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, MvPolynomial.algebraMap_apply,
      MvPolynomial.algebraMap_apply]
    simp [evD]
  have hX : ∀ x, φ (MvPolynomial.X x) =
      (if IsOddPos (blkJ X j x).2 then ι (kOdd X D pos hN d f' (pos (blkJ X j x))) else 1) * ψ (MvPolynomial.X x) := by
    intro x
    show evD X D pos ι hN d f' (subD X Kc j (MvPolynomial.X x)) = _ * MvPolynomial.eval₂ _ _ (MvPolynomial.X x)
    rw [subD_X, MvPolynomial.eval₂_X, evD_ySub X D pos Kc ι hN d f' hf hd]
    congr 2
    show _ = zT X D pos (dfr X D hN d f') (posJ X D pos j ⟨x.1, x.2.1⟩) _ _
    rw [posJ_blkJ]
    congr 1 <;> ext <;> simp [levelIndex_row_val_eq, levelIndex_col_val_eq]
  have key := ringHom_scale φ ψ
    (fun x => if IsOddPos (blkJ X j x).2 then ι (kOdd X D pos hN d f' (pos (blkJ X j x))) else 1) hC hX
    (ι (∏ τ, if IsOddPos (pos.symm τ).2 then ((zT X D pos f' τ).det ^ ((D.R.N j : ℤ) - 1) * sgRev (D.R.N j) * (dfr X D hN d f' τ).det) ^ ((D.R.N j : ℤ) * cT1 X D pos j τ - szT X D pos j τ) else 1)) G ?_
  · rw [map_mul, hR]
    exact key
  · intro m hm
    let H : (Σ v : X.Pl, Fin (X.G.P.n' v)) → ℂ := fun b =>
      if IsOddPos b.2 then kOdd X D pos hN d f' (pos b) ^ ((D.R.N j : ℤ) * cMu X j b.1 b.2 - szMu X j b.1 b.2) else 1
    have hF : ∀ τ, (if IsOddPos (pos.symm τ).2 then ((zT X D pos f' τ).det ^ ((D.R.N j : ℤ) - 1) * sgRev (D.R.N j) * (dfr X D hN d f' τ).det) ^ ((D.R.N j : ℤ) * cT1 X D pos j τ - szT X D pos j τ) else 1) = H (pos.symm τ) := by
      intro τ
      simp only [H, cT1, szT, Equiv.apply_symm_apply]
      rfl
    rw [Finset.prod_congr rfl (fun τ _ => hF τ), Fintype.prod_equiv pos.symm (fun τ => H (pos.symm τ)) H (fun _ => rfl),
      map_prod, ← Finset.prod_fiberwise Finset.univ (blkJ X j)]
    refine Finset.prod_congr rfl fun b _ => ?_
    have h2 : ∏ x ∈ Finset.univ.filter (fun x => blkJ X j x = b),
        (if IsOddPos (blkJ X j x).2 then ι (kOdd X D pos hN d f' (pos (blkJ X j x))) else 1) ^ m x =
        (if IsOddPos b.2 then ι (kOdd X D pos hN d f' (pos b)) else 1) ^
          (∑ x ∈ Finset.univ.filter (fun x => blkJ X j x = b), m x) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_congr rfl fun x hx => ?_
      rw [(Finset.mem_filter.1 hx).2]
    rw [h2]
    by_cases hb : IsOddPos b.2
    · simp only [H]
      rw [if_pos hb, if_pos hb, hN.1, ← hO m hm b hb, zpow_natCast, map_pow]
    · simp only [H]
      rw [if_neg hb, if_neg hb, one_pow, map_one]

end GlobalTheory.TwV.DelA
end
end

section

noncomputable section

namespace GlobalTheory.TwV.DelA

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)

theorem pow_toNat_split {K : Type} [Field K] {a : K} (ha : a ≠ 0) (e : ℤ) :
    a ^ e.toNat = a ^ (-e).toNat * a ^ e := by
  have h := Int.toNat_sub_toNat_neg e
  calc a ^ e.toNat = a ^ (-e).toNat * a ^ ((e.toNat : ℤ) - ((-e).toNat : ℤ)) := by
        rw [zpow_sub₀ ha, zpow_natCast, zpow_natCast]
        field_simp
    _ = _ := by rw [h]

theorem zT_det_ne {n : ℕ} (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (hf : ∀ τ, (f τ).det ≠ 0) (τ : D.what₂.Tau) :
    (zT X D pos f τ).det ≠ 0 := by
  unfold zT
  split_ifs
  · have h1 : (((f τ)⁻¹).transpose.submatrix id Fin.rev).det
        = ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤˣ) : ℤ) * (((f τ)⁻¹).transpose).det := by
      exact Matrix.det_permute' (Fin.revPerm : Equiv.Perm (Fin n)) (((f τ)⁻¹).transpose)
    rw [h1, Matrix.det_transpose, Matrix.det_nonsing_inv]
    refine mul_ne_zero (by simp) ?_
    rw [Ring.inverse_eq_inv']
    exact inv_ne_zero (hf τ)
  · exact hf τ

theorem det_rev_transpose {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (A.transpose.submatrix Fin.rev id).det = sgRev n * A.det := by
  have : (A.transpose.submatrix Fin.rev id).det = _ := Matrix.det_permute (Fin.revPerm : Equiv.Perm (Fin n)) A.transpose
  rw [this, Matrix.det_transpose, sgRev]

theorem evD_det {Kc : Type} [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) {j : ℕ} (hN : RankTie X D j)
    (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ)
    (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ) {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n (DA X Kc j)) : evD X D pos ι hN d f' M.det = (M.map (evD X D pos ι hN d f')).det :=
  RingHom.map_det _ M

theorem det_map_cast {Kc : Type} [Field Kc] (ι : ℂ →+* Kc) {a b : ℕ} (h : a = b) (B : Matrix (Fin b) (Fin b) ℂ) :
    ((B.map ι).submatrix (Fin.cast h) (Fin.cast h)).det = ι B.det := by
  have : ((B.map ι).submatrix (Fin.cast h) (Fin.cast h)).det = (B.map ι).det :=
    Matrix.det_submatrix_equiv_self (finCongr h) (B.map ι)
  rw [this, RingHom.map_det]
  rfl

theorem evD_numD_denD : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ) (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ), (∀ τ, (f' τ).det ≠ 0) → (∀ τ, (dfr X D hN d f' τ).det ≠ 0) → evD X D pos ι hN d f' (numD X Kc j) = evD X D pos ι hN d f' (denD X Kc j) * ι (∏ τ, if IsOddPos (pos.symm τ).2 then (zT X D pos f' τ).det ^ (cT1 X D pos j τ - szT X D pos j τ) * ((zT X D pos f' τ).det ^ (D.R.N j) * sgRev (D.R.N j) * (dfr X D hN d f' τ).det) ^ (cT1 X D pos j τ - (D.R.N j : ℤ) * cT1 X D pos j τ + szT X D pos j τ) else (dfr X D hN d f' τ).det ^ (X.nuv (pos.symm τ).1 (j + 1) (pos.symm τ).2 (NN X.G.P.m X.t j)).toNat) := by
  intro p _ X D pos Kc _ _ ι j hN d f' hf hd
  classical
  have key := GlobalTheory.T.operatorMatrices_at_complexPoint X D pos Kc ι j hN d f' hf hd
  have e : ∀ G : D.what₂.Tau → ℂ, ∏ τ, G τ = ∏ v, ∏ s, G (pos ⟨v, s⟩) := fun G => by
    rw [← Equiv.prod_comp pos G, Fintype.prod_sigma]
  rw [e, map_prod]
  unfold numD denD
  simp only [map_prod]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  simp only [cT1, szT]
  rw [Equiv.symm_apply_apply]
  obtain ⟨k1, k2, k3⟩ := key v s
  by_cases hs : IsOddPos s
  · simp only [if_pos hs]
    have hY : evD X D pos ι hN d f' (YtMat X Kc j v s).det
        = ι ((zT X D pos f' (pos ⟨v, s⟩)).det ^ D.R.N j * sgRev (D.R.N j) * (dfr X D hN d f' (pos ⟨v, s⟩)).det) := by
      rw [evD_det, k3 hs, Matrix.det_smul, det_map_cast, det_rev_transpose, Fintype.card_fin,
        show NN X.G.P.m X.t j = D.R.N j from hN.1.symm]
      simp only [map_mul, map_pow]
      ring
    have ha : ι (zT X D pos f' (pos ⟨v, s⟩)).det ≠ 0 := (map_ne_zero ι).2 (zT_det_ne X D pos f' hf _)
    have hb : ι ((zT X D pos f' (pos ⟨v, s⟩)).det ^ D.R.N j * sgRev (D.R.N j) * (dfr X D hN d f' (pos ⟨v, s⟩)).det) ≠ 0 := by
      refine (map_ne_zero ι).2 (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (zT_det_ne X D pos f' hf _)) ?_) (hd _))
      simp [sgRev]
    rw [map_mul ι ((zT X D pos f' (pos ⟨v, s⟩)).det ^ _), map_zpow₀, map_zpow₀]
    rw [map_mul (evD X D pos ι hN d f'), map_mul (evD X D pos ι hN d f'), map_pow (evD X D pos ι hN d f'),
      map_pow (evD X D pos ι hN d f'), map_pow (evD X D pos ι hN d f'), map_pow (evD X D pos ι hN d f'), k1, hY,
      pow_toNat_split ha (exY X j v s), pow_toNat_split hb (exT X j v s)]
    have h1 : exY X j v s = cMu X j v s - szMu X j v s := rfl
    have h2 : exT X j v s = cMu X j v s - (D.R.N j : ℤ) * cMu X j v s + szMu X j v s := by
      rw [exT, show NN X.G.P.m X.t j = D.R.N j from hN.1.symm]
    rw [h1, h2]
    ring
  · simp only [if_neg hs]
    rw [map_one, one_mul, map_pow (evD X D pos ι hN d f'), evD_det, k2 hs, det_map_cast, map_pow]

end GlobalTheory.TwV.DelA
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

theorem _root_.GlobalTheory.T.weaklyAttachedGaloisRepresentation_baseChange_restrict : ∀ (E M Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M] [Algebra E M] [Field Ω] [Algebra E Ω] [Algebra M Ω] [IsScalarTower E M Ω] [IsAlgClosure E Ω] [IsAlgClosure M Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : CuspSub E a) (P : CuspSub M a), IsLift π P → ∀ r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l), Weak π ι r → Weak P ι (r.comp (UpperTheory.V.Af.Bc.res E Ω M)) := by
  first | exact @GlobalTheory.GalCut.weak_comp_res | exact GlobalTheory.GalCut.weak_comp_res | (intros; apply GlobalTheory.GalCut.weak_comp_res <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem petersson_form_classSum_comparison :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n)
      (β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ), GlobalTheory.CoefDuty.IsInvForm a β → ∃ B, GlobalTheory.CoefDuty.IsPetersson a B ∧
      ∀ (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (T : Finset (GAf L n)), GlobalTheory.CoefDuty.IsBounded J →
        (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) →
        GlobalTheory.CoefDuty.IsClassReps J T → ∃ c : ℝ, 0 < c ∧ ∀ f ∈ NG.TypeSp a.ρ J χ,
          ∀ f' ∈ NG.TypeSp a.ρ J χ, GlobalTheory.CoefDuty.classSum a β J T f f' = (c : ℂ) * B f f' :=
  GlobalTheory.T.class_sum_eq_const_mul_petersson

end GlobalTheory
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

theorem _root_.GlobalTheory.T.norm_localBasis_standardCoord_le_one_inert : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → (IsResidueClassZero D p ∨ IsSg D p) → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), StdBases D lam L P → StdBases D lam L' P' → ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), LocBasis D p (YYl D L L') b → ∀ w a b₀ i, ‖hK D lam P P' b w a b₀ i‖ ≤ 1 := by
  first | exact @GlobalTheory.KerStd.HypCoord.norm_hK_le_one | exact GlobalTheory.KerStd.HypCoord.norm_hK_le_one | (intros; apply GlobalTheory.KerStd.HypCoord.norm_hK_le_one <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.oddTwistedFrameDetFunction_mul_det_pow_polynomial : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) {n : ℕ}, 0 < n → ∀ (ν : D.what₂.Tau → Fin n → ℕ) (c : D.what₂.Tau → ℤ), (∀ τ r, (ν τ r : ℤ) ≤ c τ) → ∀ Q : MvPolynomial (GL3Theta.FrV D n) ℂ, Q ∈ WtPol ℂ ν → ∃ (K : D.what₂.Tau → ℕ) (P : MvPolynomial (GL3Theta.FrV D n) ℂ), ∀ x : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ, (∀ τ, (x τ).det ≠ 0) → MvPolynomial.eval (fun k : GL3Theta.FrV D n => x k.1 k.2.1 k.2.2) P = twF X D pos c Q x * ∏ τ, (x τ).det ^ K τ := by
  first | exact @GlobalTheory.TwV.DelA.twF_mul_det_poly | exact GlobalTheory.TwV.DelA.twF_mul_det_poly | (intros; apply GlobalTheory.TwV.DelA.twF_mul_det_poly <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.complex_block_action_inv_read_as_substitution : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), PosTie X D pos Kc ι ρ → ∀ (fd : FData X D) (j : ℕ) (hN : RankTie X D j) (La' : X.Lt (j + 1)) (M : GL (Fin (D.R.N (j + 1))) D.host.E), StdU D M → FrIs fd ρ (j + 1) La' (rkT X D hN) M → ∀ R : XR (X.Pj (j + 1)) ℂ, MvPolynomial.map ι (actC X D pos (j + 1) (rkT X D hN) M⁻¹ R) = ι (∏ τ, embT D τ (M : Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) D.host.E).det ^ (if IsOddPos (pos.symm τ).2 then cT1 X D pos j τ - wT X D pos j τ else -wT X D pos j τ)) • GlobalTheory.FrameB.tau0 X Kc j (GlobalTheory.FrameB.mk Kc fd j La') (MvPolynomial.map ι R) := by
  first | exact @GlobalTheory.TwV.DelA.actC_inv_read | exact GlobalTheory.TwV.DelA.actC_inv_read | (intros; apply GlobalTheory.TwV.DelA.actC_inv_read <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory NumberField IsDedekindDomain Classical

theorem _root_.GlobalTheory.T.memberBadPrimes_no_conjugatePair : ∀ {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S), X.Ok → Pr.Ok → IsSel X sel → ∀ u : Pr.Word, Pr.T u ∈ S → (∀ i, Pr.g i ∈ S) → ∀ P ∈ Sall sel mu u, conjPrime₂ P ∉ Sall sel mu u := by
  first | exact @GlobalTheory.BadNoConj.sall_noConj_ok | exact GlobalTheory.BadNoConj.sall_noConj_ok | (intros; apply GlobalTheory.BadNoConj.sall_noConj_ok <;> assumption)
end

section


theorem _root_.GlobalTheory.T.thetaUnitFunction_shortModel_integral : Formalism.L2.KerInert.BeCob.ThetaTie := by
  first | exact @GlobalTheory.ShortModelTheta.thetaTie_holds | exact GlobalTheory.ShortModelTheta.thetaTie_holds | (intros; apply GlobalTheory.ShortModelTheta.thetaTie_holds <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

theorem _root_.GlobalTheory.T.normalisedThetaFamily_normalised_all_places : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → ∀ (X : Fields) (s : Seam D X), s.Ok → ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ D.host.d → (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), TaylorLogMetric.admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), GlobalTheory.ThLoc.LatAt a₀ b₀ c₀ D.host.d ha hd lam hlam (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹) (s.laF B.tor L L') (fun z => B.eNat χ N N' L L' (s.flatV N N' z)) p ι := by
  first | exact @GlobalTheory.ThLoc.latAt_all | exact GlobalTheory.ThLoc.latAt_all | (intros; apply GlobalTheory.ThLoc.latAt_all <;> assumption)
end
