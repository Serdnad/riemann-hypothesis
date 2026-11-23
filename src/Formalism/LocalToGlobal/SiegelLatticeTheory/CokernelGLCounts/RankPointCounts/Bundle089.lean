module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle083
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.GramNondeg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefPhaseL
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle061
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle055
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FiberCount
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle084
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle075
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle069
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FiberCountTh
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle049
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ScalKindPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle051
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle074
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PsiProdE
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBetaK
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdECut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.StabMul
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle011
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle070
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle010
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle086
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle079
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle053
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle048

@[expose] public section

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open CohGoodPf

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

namespace GramNePf

theorem sign_norm {l : ℕ} (hl : l ≤ D.R.rS + 1) :
    leadMinorE (ZhatOM (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)) l *
      star (leadMinorE (ZhatOM (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)) l) = 1 := by
  have hsub : (ZhatOM (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)).submatrix
      (Fin.castLE hl) (Fin.castLE hl) =
      Matrix.diagonal (fun i : Fin l => (-1 : D.host.E) ^ (D.R.rS - (Fin.castLE hl i).val)) := by
    ext i j
    rcases eq_or_ne i j with rfl | h
    · simp [ZhatOM]
    · have h' : Fin.castLE hl i ≠ Fin.castLE hl j := fun e => h (Fin.castLE_injective hl e)
      simp [ZhatOM, Matrix.one_apply_ne h', Matrix.diagonal_apply_ne _ h]
  have hdet : Formalism.MainNotions.S.leadMinorE (ZhatOM (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)) l =
      (-1 : D.host.E) ^ (∑ i : Fin l, (D.R.rS - (Fin.castLE hl i).val)) := by
    unfold Formalism.MainNotions.S.leadMinorE
    rw [dif_pos hl, hsub, Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum]
  rw [hdet, star_pow, star_neg, star_one, ← pow_add]
  exact Even.neg_one_pow ⟨_, rfl⟩

theorem conjF_star (x : D.host.E) : D.conjF x = star x := by
  rw [D.conjF_eq]
  exact (Formalism.BasicNotions.Examples₂.star_eq_conj D.host x).symm

private lemma submatrix_castLE_mul_of_upper {K : Type*} [Field K] {n l : ℕ} (hl : l ≤ n) (A B : Matrix (Fin n) (Fin n) K)
    (hB : ∀ i j, j < i → B i j = 0) :
    (A * B).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      A.submatrix (Fin.castLE hl) (Fin.castLE hl) * B.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hl) (Fin.castLE_injective hl) _ _ ?_ (fun k => rfl)
  intro k hk
  have hkl : l ≤ k.val := by
    by_contra h
    exact hk ⟨⟨k.val, by omega⟩, Fin.ext rfl⟩
  rw [hB k (Fin.castLE hl j) (by rw [Fin.lt_def, Fin.val_castLE]; exact lt_of_lt_of_le j.isLt hkl), mul_zero]

private lemma submatrix_castLE_mul_of_lower {K : Type*} [Field K] {n l : ℕ} (hl : l ≤ n) (A B : Matrix (Fin n) (Fin n) K)
    (hA : ∀ i j, i < j → A i j = 0) :
    (A * B).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      A.submatrix (Fin.castLE hl) (Fin.castLE hl) * B.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hl) (Fin.castLE_injective hl) _ _ ?_ (fun k => rfl)
  intro k hk
  have hkl : l ≤ k.val := by
    by_contra h
    exact hk ⟨⟨k.val, by omega⟩, Fin.ext rfl⟩
  rw [hA (Fin.castLE hl i) k (by rw [Fin.lt_def, Fin.val_castLE]; exact lt_of_lt_of_le i.isLt hkl), zero_mul]

private lemma det_submatrix_castLE_of_isLoUni {K : Type*} [Field K] {n l : ℕ} (hl : l ≤ n) (L : Matrix (Fin n) (Fin n) K)
    (hL : IsLoUni L) : (L.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
  have hb : (L.submatrix (Fin.castLE hl) (Fin.castLE hl)).BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := by simpa using hij
    show L (Fin.castLE hl i) (Fin.castLE hl j) = 0
    exact (hL _ _).1 (by rw [Fin.lt_def, Fin.val_castLE, Fin.val_castLE]; exact hij')
  rw [Matrix.det_of_lowerTriangular _ hb]
  exact Finset.prod_eq_one (fun i _ => (hL _ _).2 rfl)

private lemma det_submatrix_castLE_of_isUpUni {K : Type*} [Field K] {n l : ℕ} (hl : l ≤ n) (U : Matrix (Fin n) (Fin n) K)
    (hU : IsUpUni U) : (U.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
  have hb : (U.submatrix (Fin.castLE hl) (Fin.castLE hl)).BlockTriangular id := by
    intro i j hij
    have hij' : j < i := by simpa using hij
    show U (Fin.castLE hl i) (Fin.castLE hl j) = 0
    exact (hU _ _).1 (by rw [Fin.lt_def, Fin.val_castLE, Fin.val_castLE]; exact hij')
  rw [Matrix.det_of_upperTriangular hb]
  exact Finset.prod_eq_one (fun i _ => (hU _ _).2 rfl)

private lemma det_submatrix_castLE_LPU_eq {K : Type*} [Field K] {n l : ℕ} (hl : l ≤ n) (L P U : Matrix (Fin n) (Fin n) K)
    (hL : IsLoUni L) (hU : IsUpUni U) :
    ((L * P * U).submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      (P.submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
  rw [submatrix_castLE_mul_of_upper hl _ _ (fun i j h => (hU i j).1 h), submatrix_castLE_mul_of_lower hl _ _ (fun i j h => (hL i j).1 h),
    Matrix.det_mul, Matrix.det_mul, det_submatrix_castLE_of_isLoUni hl L hL, det_submatrix_castLE_of_isUpUni hl U hU, one_mul, mul_one]

private lemma zhatOM_eq_mul_zhatOM_one {K : Type*} [CommRing K] {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    ZhatOM Z = Z * ZhatOM (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) K) := by
  ext a b
  simp [ZhatOM, Matrix.mul_apply, Matrix.one_apply]
  try ring

theorem gflag_ne (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D)
    (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (hC : Ctx γ Z) (hZ : ZhatL (lf D F0) F'₂ = Z) :
    Gflag (lf D F0).fl F'₂.fl ≠ 0 := by
  obtain ⟨w, -, w', hG, -, hA⟩ := hC
  obtain ⟨L, U, hL, hU, hM⟩ := hA
  have hS : ∀ i j : Fin (D.R.rS + 1), j < i →
      ZhatOM (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) i j = 0 := by
    intro i j h
    simp [ZhatOM, Matrix.one_apply_ne (ne_of_gt h)]
  have hsq : ∀ l, l ≤ D.R.rS + 1 →
      Formalism.MainNotions.S.leadMinorE Z l * star (Formalism.MainNotions.S.leadMinorE Z l) = Dmin w' l * D.conjF (Dmin w' l) := by
    intro l hl
    have h1 : Dmin w' l = Formalism.MainNotions.S.leadMinorE Z l *
        Formalism.MainNotions.S.leadMinorE (ZhatOM (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)) l := by
      unfold Dmin Formalism.MainNotions.S.leadMinorE
      simp only [dif_pos hl]
      rw [← Matrix.det_mul, ← submatrix_castLE_mul_of_upper hl _ _ hS, ← zhatOM_eq_mul_zhatOM_one, hM, det_submatrix_castLE_LPU_eq hl _ _ _ hL hU]
    rw [h1, conjF_star, star_mul']
    linear_combination (-(Formalism.MainNotions.S.leadMinorE Z l * star (Formalism.MainNotions.S.leadMinorE Z l))) * sign_norm hl
  intro h0
  apply hG
  unfold Formalism.MainNotions.S.LocalSplitGroups.Gpt
  rw [← hsq _ le_rfl, ← hsq _ (Nat.le_succ _)]
  refine Eq.trans ?_ h0
  unfold Formalism.MainNotions.S.Gflag Formalism.MainNotions.S.Dl
  rw [show Formalism.MainNotions.S.Zhat (lf D F0).fl F'₂.fl = Z from hZ]

end GramNePf

open GramNePf

theorem globGramNe_holds : GlobGramNe u u' F0 what₂ := by
  intro _ γ Z F'₂ hC hZ hdet
  have hG := gflag_ne γ Z F'₂ hC hZ
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hw : ∀ k, (VS D).hT (wG F0 F'₂ k) (∑ j, v j • wG F0 F'₂ j) = 0 := by
    intro k
    have hk := congr_fun hv k
    simp only [Matrix.mulVec, dotProduct, gramG, Matrix.of_apply, brS, Pi.zero_apply] at hk

    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    exact (Finset.sum_congr rfl (fun j _ => mul_comm _ _)).trans hk
  obtain ⟨h1, h2⟩ := PI.UnitaryGroupMassFormula.BetaLUniq.GN.coeffs_zero F0 F'₂.fl (v ∘ Sum.inl) (v ∘ Sum.inr)
    (∑ j, v j • wG F0 F'₂ j) (by rw [Fintype.sum_sum_type]; rfl)
    (fun a => hw (Sum.inl a)) (fun b => hw (Sum.inr b)) hG
  apply hv0
  funext k
  rcases k with a | b
  · exact congr_fun h1 a
  · exact congr_fun h2 b

variable (Zd : LocDat D)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cutAt_of_leaves {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    {δ : ∀ p : PlF D, (D.s.atP p).Fp} {L : CntLocal.LocSp D M} {u u' : D.what₂.Word}
    {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (hA : ∀ p, Agree δ M p) (hc : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2])
    (hP : PrimeHyp D u (Tu D u')) (hrows : IsRowReps D F0 what₂)
    (hN : PairVal.NormRepExists D u u' F0 what₂) (hM : Formalism.L2.SG.Pf.NormRepMove D u u')
    (hPG : PhaseLocG M δ u u' F0 what₂) (hVP : VolIdxProd M δ u u' F0 what₂)
    (hE : PCount.ExistP ⟨δ, M, hA⟩ u u' F0 what₂) (hS : PCount.SumFrP ⟨δ, M, hA⟩ u u' F0 what₂)
    (hG : PCount.FrGlobP ⟨δ, M, hA⟩ u u' F0 what₂) (hI : PCount.IntGenP ⟨δ, M, hA⟩)
    (hτ : PCount.TauOneReduction ⟨δ, M, hA⟩ u u' F0 what₂) (hT : PCount.PartnerIsomorphismCount ⟨δ, M, hA⟩)
    (hFS : FCount.FibSum M δ u u' F0 what₂) (hDT : FCount.DensTh M δ L u u') :
    CutAt M δ L u u' F0 what₂ := by
  have hNR := normRepElig_of hN
  have hU := Formalism.L2.SG.Pf.locUnram_holds hA u u'
  have hR := Formalism.L2.SG.Pf.thRestricted_holds_of hA hrows hN PCount.eligRel_holds
  have hTS := Formalism.L2.SG.Pf.thSome_holds hA hc hrows hNR
  refine ⟨LocOrbSumPf.localOrbitSum_holds M δ u u' hA, Formalism.L2.SG.Pf.scalKind_of hrows,
    coefficient_product_of_local hA hc hrows hN hM (phaseLoc_of hA hPG) (psi_product_e D) hVP,
    Formalism.L2.SG.Pf.partnerCount_holds hA hc hrows hP hU hR hE hS hG hI hτ hT,
    FCount.fiberCount_of_rest hA hc hP hU hR hrows hN PCount.eligRel_holds (hE ⟨hc, hrows, hP⟩) hTS hFS
      nu_not_class_holds hDT (FCount.eligible_totally_positive u u' F0 what₂),
    hNR, hTS, ⟨LocModel.thTriv M, hU, hR⟩⟩

end Formalism.L2.SG.Pf.Coef
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdCut BwdBetaCut BwdNP BetaI

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

namespace BetaI

def SendsB (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (ψ : (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
    (β₀ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (m : (VS D).V) : Prop :=
  ∀ (hm : baseChange₂ D p m ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f'))
    (hm₂ : baseChange₂ D p (β₀ m) ∈ (locH Zd p).perp ((locH Zd p).X (locF' Zd p F'₂))),
    ψ ((locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p m, hm⟩) = (locH Zd p).mkW (locF' Zd p F'₂) ⟨baseChange₂ D p (β₀ m), hm₂⟩

end BetaI

variable (u u' F0 what₂)

def PinOm : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V), BHyp Zd u u' F0 what₂ γ Z F'₂ φ φ' Λ₂ →
    ∀ β₀ : (VS D).V ≃ₗ[D.host.E] (VS D).V, β₀ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
      (∀ b, β₀ (frame (repF γ) b) = frame (liftF F'₂) b) →
      W0₂ γ.lam Λ₂ (lf D F0) (repF γ) (liftF F'₂) β₀ → OmB (lf D F0) (repF γ) (liftF F'₂) β₀ →
      ∀ p : PlF D, BetaI.SendsB Zd p γ F'₂ (φ' p) β₀ (Gom (frame (lf D F0)) (frame (repF γ)))

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section

noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Fin2

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))


theorem finIdx_at {p : PlF D} (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U) :
    (ProdE.CPL M δ u u' w hA L U hL hU).relIndex (ProdE.AP M δ u u' w p) ≠ 0 ∧
      (ProdE.AP M δ u u' w p).relIndex (ProdE.CPL M δ u u' w hA L U hL hU) ≠ 0 := by
  classical
  obtain ⟨c0, hc00, hc0O, hcong⟩ := cong_at M δ u u' w hA L U hL hU
  set Lp := lOf δ M p L U with hLpd
  set Lpi := lOf δ M p L⁻¹ U⁻¹ with hLpid
  set Up := ρOf δ M p L U with hUpd
  set Upi := ρOf δ M p L⁻¹ U⁻¹ with hUpid
  have hLi := ZsVolGrp.isLoUni_inv hL
  have hUi := ZsVolGrp.isUpUni_inv hU
  have hLL : Lp * Lpi = 1 := by rw [hLpd, hLpid, ← lOf_mul δ M hA, hLi.2.2, hUi.2.1, lOf_one δ M hA]
  have hLL' : Lpi * Lp = 1 := ProdE.lp_inv M δ hA L U hL hU
  have hUU : Up * Upi = 1 := ProdE.up_inv M δ hA L U hL hU
  have hUU' : Upi * Up = 1 := by rw [hUpd, hUpid, ← ρOf_mul δ M hA, hLi.2.2, hUi.2.1, ρOf_one δ M hA]
  obtain ⟨s1, hs10, hs1O, hs1⟩ := bounded_mat (L := D.s.atP p) Lp
  obtain ⟨s2, hs20, hs2O, hs2⟩ := bounded_mat (L := D.s.atP p) Lpi
  obtain ⟨s3, hs30, hs3O, hs3⟩ := bounded_mat (L := D.s.atP p) Up
  obtain ⟨s4, hs40, hs4O, hs4⟩ := bounded_mat (L := D.s.atP p) Upi
  have hRO : ∀ {x : (D.s.atP p).Ep}, x ∈ (M p).R → x ∈ (D.s.atP p).O := fun hx => R_sub_O M δ hA hx
  refine ⟨?_, ?_⟩
  · haveI := finite_quot M δ hA c0 hc00 hc0O
    refine relIndex_ne_zero_of_code _ _
      (fun k : ProdE.AP M δ u u' w p =>
        ((fun i j => (QuotientAddGroup.mk (⟨((k : ProdE.StP M δ u u' w p).1.1 : ProdE.MP p) i j,
            hRO (k.2.1.2.2 i j)⟩ : (D.s.atP p).O) : (D.s.atP p).O ⧸ (Ideal.span {dO c0 hc0O}).toAddSubgroup)),
         (fun i j => (QuotientAddGroup.mk (⟨((k : ProdE.StP M δ u u' w p).1.2.unop : ProdE.MP p) i j,
            hRO (k.2.2.2.2 i j)⟩ : (D.s.atP p).O) : (D.s.atP p).O ⧸ (Ideal.span {dO c0 hc0O}).toAddSubgroup))))
      (fun k k' heq => ?_)
    have e1 : ∀ i j, (((k' : ProdE.StP M δ u u' w p).1.1 : ProdE.MP p) - ((k : ProdE.StP M δ u u' w p).1.1 : ProdE.MP p))
        i j ∈ latS (D.s.atP p) c0 := fun i j => by
      rw [Matrix.sub_apply]; exact quot_eq (congrFun (congrFun (congrArg Prod.fst heq) i) j)
    have e2 : ∀ i j, (((k' : ProdE.StP M δ u u' w p).1.2.unop : ProdE.MP p) -
        ((k : ProdE.StP M δ u u' w p).1.2.unop : ProdE.MP p)) i j ∈ latS (D.s.atP p) c0 := fun i j => by
      rw [Matrix.sub_apply]; exact quot_eq (congrFun (congrFun (congrArg Prod.snd heq) i) j)
    have hki := (k⁻¹).2
    clear heq
    set a := ((k : ProdE.StP M δ u u' w p).1.1 : ProdE.GLp p)
    set a' := ((k' : ProdE.StP M δ u u' w p).1.1 : ProdE.GLp p)
    set b := ((k : ProdE.StP M δ u u' w p).1.2.unop : ProdE.GLp p)
    set b' := ((k' : ProdE.StP M δ u u' w p).1.2.unop : ProdE.GLp p)
    have ha : ((a⁻¹ : ProdE.GLp p) : ProdE.MP p) * (a : ProdE.MP p) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hb : (b : ProdE.MP p) * ((b⁻¹ : ProdE.GLp p) : ProdE.MP p) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have m := hcong ((k⁻¹ * k' : ProdE.AP M δ u u' w p) : ProdE.StP M δ u u' w p) ?_ ?_
    · exact m.2
    · show EntIn _ (((a⁻¹ * a' : ProdE.GLp p) : ProdE.MP p) - 1)
      rw [Units.val_mul, show ((a⁻¹ : ProdE.GLp p) : ProdE.MP p) * (a' : ProdE.MP p) - 1 =
        ((a⁻¹ : ProdE.GLp p) : ProdE.MP p) * ((a' : ProdE.MP p) - (a : ProdE.MP p)) by rw [Matrix.mul_sub, ha]]
      exact entIn_int_mul (fun i j => hRO (hki.1.2.2 i j)) e1
    · show EntIn _ (((b' * b⁻¹ : ProdE.GLp p) : ProdE.MP p) - 1)
      rw [Units.val_mul, show (b' : ProdE.MP p) * ((b⁻¹ : ProdE.GLp p) : ProdE.MP p) - 1 =
        ((b' : ProdE.MP p) - (b : ProdE.MP p)) * ((b⁻¹ : ProdE.GLp p) : ProdE.MP p) by rw [Matrix.sub_mul, hb]]
      exact entIn_mul_int (fun i j => hRO (hki.2.2.2 i j)) e2
  · set c1 := s2 * (s1 * c0) * (s3 * s4) with hc1d
    have hc1O : c1 ∈ 𝒪[(D.s.atP p).Fp] := Subring.mul_mem _ (Subring.mul_mem _ hs2O (Subring.mul_mem _ hs1O hc0O))
      (Subring.mul_mem _ hs3O hs4O)
    have hc10 : c1 ≠ 0 := mul_ne_zero (mul_ne_zero hs20 (mul_ne_zero hs10 hc00)) (mul_ne_zero hs30 hs40)
    haveI := finite_quot M δ hA c1 hc10 hc1O
    refine relIndex_ne_zero_of_code _ _
      (fun k : ProdE.CPL M δ u u' w hA L U hL hU =>
        ((fun i j => (QuotientAddGroup.mk (⟨(Lp * ((k : ProdE.StP M δ u u' w p).1.1 : ProdE.MP p) * Lpi) i j,
            hRO (k.2.1.2.2 i j)⟩ : (D.s.atP p).O) : (D.s.atP p).O ⧸ (Ideal.span {dO c1 hc1O}).toAddSubgroup)),
         (fun i j => (QuotientAddGroup.mk (⟨(Upi * ((k : ProdE.StP M δ u u' w p).1.2.unop : ProdE.MP p) * Up) i j,
            hRO (k.2.2.2.2 i j)⟩ : (D.s.atP p).O) : (D.s.atP p).O ⧸ (Ideal.span {dO c1 hc1O}).toAddSubgroup))))
      (fun k k' heq => ?_)
    have e1 : EntIn (latS (D.s.atP p) c1) (Lp * (((k' : ProdE.StP M δ u u' w p).1.1 : ProdE.MP p) -
        ((k : ProdE.StP M δ u u' w p).1.1 : ProdE.MP p)) * Lpi) := fun i j => by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply]
      exact quot_eq (congrFun (congrFun (congrArg Prod.fst heq) i) j)
    have e2 : EntIn (latS (D.s.atP p) c1) (Upi * (((k' : ProdE.StP M δ u u' w p).1.2.unop : ProdE.MP p) -
        ((k : ProdE.StP M δ u u' w p).1.2.unop : ProdE.MP p)) * Up) := fun i j => by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply]
      exact quot_eq (congrFun (congrFun (congrArg Prod.snd heq) i) j)
    clear heq
    set a := ((k : ProdE.StP M δ u u' w p).1.1 : ProdE.GLp p)
    set a' := ((k' : ProdE.StP M δ u u' w p).1.1 : ProdE.GLp p)
    set b := ((k : ProdE.StP M δ u u' w p).1.2.unop : ProdE.GLp p)
    set b' := ((k' : ProdE.StP M δ u u' w p).1.2.unop : ProdE.GLp p)
    have hki := (k⁻¹).2
    have ha : ((a⁻¹ : ProdE.GLp p) : ProdE.MP p) * (a : ProdE.MP p) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hb : (b : ProdE.MP p) * ((b⁻¹ : ProdE.GLp p) : ProdE.MP p) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have m := hcong ((k⁻¹ * k' : ProdE.CPL M δ u u' w hA L U hL hU) : ProdE.StP M δ u u' w p) ?_ ?_
    · exact m.1
    · show EntIn _ (((a⁻¹ * a' : ProdE.GLp p) : ProdE.MP p) - 1)
      have eq1 : ((a⁻¹ * a' : ProdE.GLp p) : ProdE.MP p) - 1 =
          Lpi * ((Lp * ((a⁻¹ : ProdE.GLp p) : ProdE.MP p) * Lpi) * (Lp * ((a' : ProdE.MP p) - (a : ProdE.MP p)) * Lpi)) *
            Lp := by
        rw [show Lpi * ((Lp * ((a⁻¹ : ProdE.GLp p) : ProdE.MP p) * Lpi) *
            (Lp * ((a' : ProdE.MP p) - (a : ProdE.MP p)) * Lpi)) * Lp =
            (Lpi * Lp) * ((a⁻¹ : ProdE.GLp p) : ProdE.MP p) * (Lpi * Lp) * ((a' : ProdE.MP p) - (a : ProdE.MP p)) *
              (Lpi * Lp) by simp only [Matrix.mul_assoc], hLL', Matrix.one_mul, Matrix.mul_one, Matrix.mul_one,
          Units.val_mul, Matrix.mul_sub, ha]
      rw [eq1]
      exact entIn_sandwich hs2 hs1 (entIn_latS_of_eq (t := s3 * s4) rfl (Subring.mul_mem _ hs3O hs4O)
        (entIn_int_mul (fun i j => hRO (hki.1.2.2 i j)) e1))
    · show EntIn _ (((b' * b⁻¹ : ProdE.GLp p) : ProdE.MP p) - 1)
      have eq2 : ((b' * b⁻¹ : ProdE.GLp p) : ProdE.MP p) - 1 =
          Up * ((Upi * ((b' : ProdE.MP p) - (b : ProdE.MP p)) * Up) * (Upi * ((b⁻¹ : ProdE.GLp p) : ProdE.MP p) * Up)) *
            Upi := by
        rw [show Up * ((Upi * ((b' : ProdE.MP p) - (b : ProdE.MP p)) * Up) *
            (Upi * ((b⁻¹ : ProdE.GLp p) : ProdE.MP p) * Up)) * Upi =
            (Up * Upi) * ((b' : ProdE.MP p) - (b : ProdE.MP p)) * (Up * Upi) * ((b⁻¹ : ProdE.GLp p) : ProdE.MP p) *
              (Up * Upi) by simp only [Matrix.mul_assoc], hUU, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one,
          Units.val_mul, Matrix.sub_mul, hb]
      rw [eq2]
      exact entIn_sandwich hs3 hs4 (entIn_latS_of_eq (t := s2 * s1) (by rw [hc1d]; ring)
        (Subring.mul_mem _ hs2O hs1O) (entIn_mul_int (fun i j => hRO (hki.2.2.2 i j)) e2))

end Fin2

end Formalism.L2.SG.Pf.ProdEApprox
end
end
