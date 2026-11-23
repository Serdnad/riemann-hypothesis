module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle068
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CloseOfTarget
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModelKS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle056
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle008
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle067
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle070
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EmbeddingIntegerAlgebraMap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarUniq
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.Bundle001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RelativeEquivalence.DCRelEquivAllHolds
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle048

@[expose] public section

section

noncomputable section

namespace Formalism.L2.SG.Pf.TupGlobApprox

open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.Pf.ProdEApprox Formalism.L2.SG.Pf.PCount ValuativeRel

section Free

def Free {n : ℕ} (σ : Fin n → Fin n) (i j : Fin n) : Prop := j < i ∧ σ i < σ j

theorem off_free {K : Type*} [CommRing K] {n : ℕ} {σ : Fin n → Fin n} (hσ : ∀ a, σ (σ a) = a)
    {T : Matrix (Fin n) (Fin n) K} (hT : IsLo T) (hpat : ∀ i j, σ j < σ i → T i j = 0) {i j : Fin n}
    (h : ¬ Free σ i j) : T i j = (1 : Matrix (Fin n) (Fin n) K) i j := by
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [hT.2 i j hij, Matrix.one_apply_ne hij.ne]
  · rw [hT.1 i, Matrix.one_apply_eq]
  · have hne : σ i ≠ σ j := fun e => hij.ne' (by rw [← hσ i, e, hσ])
    have : σ j < σ i := by
      rcases lt_or_gt_of_ne hne with h' | h'
      · exact absurd ⟨hij, h'⟩ h
      · exact h'
    rw [hpat i j this, Matrix.one_apply_ne hij.ne']

theorem ent_free {E K : Type*} [Field E] [CommRing K] (ψ : E →+* K) {n : ℕ} {σ : Fin n → Fin n}
    (hσ : ∀ a, σ (σ a) = a) {X' : Matrix (Fin n) (Fin n) E} (hX' : IsLo X') (hpX : ∀ i j, σ j < σ i → X' i j = 0)
    {T : Matrix (Fin n) (Fin n) K} (hT : IsLo T) (hpT : ∀ i j, σ j < σ i → T i j = 0) {J : AddSubgroup K}
    (h : ∀ i j, Free σ i j → ψ (X' i j) - T i j ∈ J) : EntIn J (X'.map ψ - T) := by
  intro i j
  rw [Matrix.sub_apply, Matrix.map_apply]
  by_cases hf : Free σ i j
  · exact h i j hf
  · rw [off_free hσ hX' hpX hf, off_free hσ hT hpT hf, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

theorem bnd_mats {Fp : Type*} [Field Fp] {K : Type*} [CommRing K] [Algebra Fp K] {I : Subring K} (O : Subring Fp)
    (hI : ∀ s ∈ O, algebraMap Fp K s ∈ I) (hx : ∀ x : K, ∃ s : Fp, s ≠ 0 ∧ s ∈ O ∧ algebraMap Fp K s * x ∈ I)
    {n k : ℕ} (Ms : Fin k → Matrix (Fin n) (Fin n) K) :
    ∃ s : Fp, s ≠ 0 ∧ s ∈ O ∧ ∀ m i j, algebraMap Fp K s * Ms m i j ∈ I := by
  obtain ⟨s, hs0, hsO, hs⟩ := bnd_fin O hI (fun q : Fin k × Fin n × Fin n => Ms q.1 q.2.1 q.2.2) (fun q => hx _)
  exact ⟨s, hs0, hsO, fun m i j => hs (m, i, j)⟩

theorem int_of_close {K : Type*} [CommRing K] {I : Subring K} {n : ℕ} {a : Matrix (Fin n) (Fin n) K}
    (h : EntIn (lat I 1) (a - 1)) (i j : Fin n) : a i j ∈ I := by
  have e : a i j = (a - 1) i j + (1 : Matrix (Fin n) (Fin n) K) i j := by rw [Matrix.sub_apply]; ring
  rw [e]
  refine I.add_mem (lat_one (h i j)) ?_
  rw [Matrix.one_apply]
  split_ifs
  · exact I.one_mem
  · exact I.zero_mem

end Free

section BadL

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.TupGlob
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

def GoodAt (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (L₁ U₁ A₀ B₀ X' : PairVal.MatR D) : Prop :=
  TieN.IntLow (Zd.M p) (locL Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀)) ∧
    TieN.IntUp (Zd.M p) (locR Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀))

def LocTarget (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (L₁ U₁ A₀ B₀ : PairVal.MatR D) : Prop :=
  ∃ (T : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) (c : (D.s.atP p).Fp), c ≠ 0 ∧
    ∀ X' : PairVal.MatR D, IsLo X' → (∀ i j, fσ w j < fσ w i → X' i j = 0) →
      (∀ i j, Free (fσ w) i j → ∃ y ∈ (D.s.atP p).O,
        (D.s.atP p).ιE (X' i j) - T i j = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c * y) →
      GoodAt Zd p w L₁ U₁ A₀ B₀ X'

theorem isLo_of_intLow {p : PlF D} {l : MatP D p} (h : TieN.IntLow (Zd.M p) l) : IsLo l := ⟨h.1, h.2.1⟩

theorem isUp_of_intUp {p : PlF D} {ρ : MatP D p} (h : TieN.IntUp (Zd.M p) ρ) : IsUp ρ :=
  ⟨h.1, fun a b hab => h.2.1 b a hab⟩

theorem target_L (u u' : D.what₂.Word) (p : PlF D) (hM : (Zd.M p).split = none) (w : Point D.host.E (D.R.rS + 1))
    {Z₁ L₁ U₁ A₀ B₀ : PairVal.MatR D} (hL₁ : IsLo L₁) (hU₁ : IsUp U₁)
    (hZ : Z₁ * Sg D.host.E D.R.rS = L₁ * ptMat w * U₁) (hA₀ : IsLo A₀) (hB₀ : IsUp B₀) {l ρ : MatP D p}
    (hl : TieN.IntLow (Zd.M p) l) (hρ : TieN.IntUp (Zd.M p) ρ)
    (h : locL Zd p A₀ B₀ * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * locR Zd p A₀ B₀ =
      l * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * ρ) :
    LocTarget Zd p w L₁ U₁ A₀ B₀ := by
  have hcv : ∀ a, (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) a *
      (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) a = 1 :=
    fun a => by simp only [← map_mul, cf_cfi, map_one]
  have hσ : ∀ a, fσ w (fσ w a) = a := fσ_fσ w
  have hν : ∀ a : Fin (D.R.rS + 1), pv w.1 a ≠ 0 := fun a => pv_ne' w a
  have hYp : CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p =
      (1 : (D.s.atP p).Ep) • (Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) *
        (L₁ * mono (fσ w) (fun a => pv w.1 a) * U₁).map (D.s.atP p).ιE *
        Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a))) -
      (0 : (D.s.atP p).Ep) • Ecorner D.R.rS := by
    rw [one_smul, zero_smul, sub_zero, zzp_sgn_ord Zd u u' p hM Z₁, hZ, ptMat_mono']
  obtain ⟨hli, -, hll'⟩ := ZsVolGrp.intLow_inv (Zd.M p) hl
  obtain ⟨hρi, -, hρρ⟩ := ZsVolGrp.intUp_inv (Zd.M p) hρ
  have hkL : IsLo (l⁻¹ * locL Zd p A₀ B₀) := isLo_mul (isLo_of_intLow Zd hli) (locL_lo Zd p hA₀ hB₀)
  have hkR : IsUp (locR Zd p A₀ B₀ * ρ⁻¹) := isUp_mul (locR_up Zd p hA₀ hB₀) (isUp_of_intUp Zd hρi)
  have hk := key_stab Zd p hl hρ h
  rw [hYp] at hk
  obtain ⟨hTlo, hTpat, -⟩ := comp_target (D.s.atP p).ιE hcv hL₁ hU₁ hσ hν isUnit_one hkL hkR hk
  obtain ⟨t, ht0, htO, hb⟩ := bnd_mats 𝒪[(D.s.atP p).Fp] (fun s hs => alg_mem_O hs) (fun x => bounded x)
    ![cP (D.s.atP p).ιE (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) L₁,
      cP' (D.s.atP p).ιE (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) L₁,
      cQ (D.s.atP p).ιE (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) U₁,
      cQ' (D.s.atP p).ιE (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) U₁,
      Matrix.of fun i _ => (D.s.atP p).ιE (pv w.1 i), Matrix.of fun i _ => (D.s.atP p).ιE (pv w.1 i)⁻¹,
      cP' (D.s.atP p).ιE (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) L₁ *
        (l⁻¹ * locL Zd p A₀ B₀) * cP (D.s.atP p).ιE (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) L₁]
  refine ⟨(cP' (D.s.atP p).ιE (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) L₁ *
        (l⁻¹ * locL Zd p A₀ B₀) * cP (D.s.atP p).ιE (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) L₁)⁻¹,
    t * (t * (t * (t * (t * 1)))), by simp [ht0], ?_⟩
  intro X' hX' hpat hfree
  obtain ⟨hgX, hgY, hst⟩ := glob_stab w hL₁ hU₁ hZ hX' hpat
  have hab := key_stab Zd p hl hρ ((corr_move Zd u u' p hA₀ hB₀ hgX hgY hst).trans h)
  rw [hYp] at hab
  have ha : IsLo (l⁻¹ * locL Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀)) :=
    isLo_mul (isLo_of_intLow Zd hli) (locL_lo Zd p (isLo_mul hA₀ hgX) (isUp_mul hgY hB₀))
  have hb' : IsUp (locR Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀) * ρ⁻¹) :=
    isUp_mul (locR_up Zd p (isLo_mul hA₀ hgX) (isUp_mul hgY hB₀)) (isUp_of_intUp Zd hρi)
  have haX : l⁻¹ * locL Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀) = (l⁻¹ * locL Zd p A₀ B₀) *
      (Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) *
        (L₁ * X' * L₁⁻¹).map (D.s.atP p).ιE *
        Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a))) := by
    rw [locL_L Zd p hM, locL_L Zd p hM, gX, Matrix.map_mul (L := A₀)]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)))
      (Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a))), diag_one (hcv'_of hcv),
      Matrix.one_mul]
  have hG : EntIn (lat (D.s.atP p).O (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep t *
      (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep t * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep t *
        (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep t * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep t * 1))))))
      (X'.map (D.s.atP p).ιE - (cP' (D.s.atP p).ιE (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) L₁ *
        (l⁻¹ * locL Zd p A₀ B₀) * cP (D.s.atP p).ιE (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) L₁)⁻¹) := by
    refine ent_free (D.s.atP p).ιE hσ hX' hpat hTlo hTpat fun i j hf => ?_
    obtain ⟨y, hy, e⟩ := hfree i j hf
    refine ⟨y, hy, ?_⟩
    rw [e]
    simp only [map_mul, map_one]
  have hcl := comp_main (D.s.atP p).ιE hcv hL₁ hU₁ hσ hν isUnit_one hkL hkR hk ha hb' hab haX
    (alg_mem_O htO) (D.s.atP p).O.one_mem
    (fun a => by simpa using hb 4 a a) (fun a => by simpa using hb 5 a a)
    (fun i j => by simpa using hb 0 i j) (fun i j => by simpa using hb 1 i j)
    (fun i j => by simpa using hb 2 i j) (fun i j => by simpa using hb 3 i j)
    (fun i j => by simpa using hb 6 i j) hG
  have hR : (Zd.M p).R = (D.s.atP p).O := Formalism.L2.SG.Pf.LMK.R_eq_O (Zd.agree p) hM
  refine ⟨?_, ?_⟩
  · have e : locL Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀) =
        l * (l⁻¹ * locL Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀)) := by
      rw [← Matrix.mul_assoc, hll', Matrix.one_mul]
    rw [e]
    refine ZsVolGrp.intLow_mul (Zd.M p) hl ⟨ha.1, ha.2, fun i j => ?_⟩
    rw [hR]
    exact int_of_close hcl.1 i j
  · have e : locR Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀) =
        (locR Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀) * ρ⁻¹) * ρ := by
      rw [Matrix.mul_assoc, (ZsVolGrp.intUp_inv (Zd.M p) hρ).2.1, Matrix.mul_one]
    rw [e]
    refine ZsVolGrp.intUp_mul (Zd.M p) ⟨hb'.1, fun a b hab => hb'.2 b a hab, fun i j => ?_⟩ hρ
    rw [hR]
    exact int_of_close hcl.2 i j

end BadL

end Formalism.L2.SG.Pf.TupGlobApprox
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdCut

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def BtSit (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V) : Prop :=
  Ctx γ Z ∧ StarHyp Zd γ Z F'₂ φ φ' ∧ Λ₂ ∈ GlobSet Zd γ F'₂ φ φ' ∧
    ∃ n ∈ unipotentFrameFixers F0, (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) = (γ.lam : Set (VS D).V)

variable (u u' F0 what₂)

def BtStep (P : Submodule (𝓞 D.host.E) (VS D).V → LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) → Prop) : Prop :=
  CtxP u u' F0 what₂ → ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D)
    (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V), BtSit Zd γ Z F'₂ φ φ' Λ₂ → P Λ₂ (liftF F'₂)

def BtLift : Prop := BtStep Zd u u' F0 what₂ fun Λ₂ F' => IsLift Λ₂ F'

def BtAdm : Prop := BtStep Zd u u' F0 what₂ fun Λ₂ F' => AdmWit Λ₂ (gS D) (lf D F0) F' 1

def BtG : Prop := BtStep Zd u u' F0 what₂ fun _ F' => Gval (lf D F0) F' ≠ 0

def BtOK : Prop := BtStep Zd u u' F0 what₂ fun Λ₂ F' => FrameOK D Λ₂ F'

def BtGen : Prop := BtStep Zd u u' F0 what₂ fun Λ₂ F' => IsGeneric Λ₂ (gS D) (lf D F0) F'

variable {u u' F0 what₂}

theorem bwdTerm'_of (h1 : BtLift Zd u u' F0 what₂) (h2 : BtAdm Zd u u' F0 what₂) (h3 : BtG Zd u u' F0 what₂)
    (h4 : BtOK Zd u u' F0 what₂) (h5 : BtGen Zd u u' F0 what₂) : BwdTerm' Zd u u' F0 what₂ := by
  intro hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂ hn
  have hs : BtSit Zd γ Z F'₂ φ φ' Λ₂ := ⟨hZ, hS, hΛ₂, hn⟩
  exact ⟨⟨h1 hC γ Z F'₂ φ φ' Λ₂ hs, ⟨1, h2 hC γ Z F'₂ φ φ' Λ₂ hs⟩, h3 hC γ Z F'₂ φ φ' Λ₂ hs⟩,
    h2 hC γ Z F'₂ φ φ' Λ₂ hs, h5 hC γ Z F'₂ φ φ' Λ₂ hs, h4 hC γ Z F'₂ φ φ' Λ₂ hs⟩

theorem btG_holds : BtG Zd u u' F0 what₂ := by
  intro _ γ Z F'₂ φ φ' Λ₂ hs
  obtain ⟨⟨w, _, w', hGw', _, hZw'⟩, hS, _, _⟩ := hs
  have h1 : Gval (lf D F0) (liftF F'₂) =
      Formalism.L2.SG.CntLocal.GZ (((Tu D u : ℕ) : D.host.E)) (((Tu D u' : ℕ) : D.host.E)) Z := by
    rw [← hS.1]; rfl
  intro hz
  apply hGw'
  calc
    _ = Formalism.L2.SG.CntLocal.GZ (((Tu D u : ℕ) : D.host.E)) (((Tu D u' : ℕ) : D.host.E)) Z :=
      (Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.Uniq.gz_atMat hZw' (Tu D u) (Tu D u')).symm
    _ = Gval (lf D F0) (liftF F'₂) := h1.symm
    _ = 0 := hz

theorem sgnP'_last (p : PlF D) : sgnP' D p (Fin.last D.R.rS) = 1 := by
  unfold sgnP'
  split
  · unfold TermLoc.sgnP; split
    · simp
    · rfl
  · simp

theorem frFac_last (p : PlF D) : frFac Zd.δ p (Fin.last D.R.rS) = 1 := by
  unfold frFac; simp

theorem locF'_last (p : PlF D) {T' : D.host.E} (F' : LFlag (D.sp.Y 0) D.R.rS T') :
    locF' Zd p F' (Fin.last D.R.rS) = baseChange₂ D p F'.fl.z := by
  unfold locF'
  rw [sgnP'_last, frFac_last, one_mul, one_smul]
  congr 1
  simp [frame, FlagG.fvec]

theorem mem_of_baseChange_mem {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsFullLattice D.host.E Λ) {x : (VS D).V}
    (h : ∀ p, baseChange₂ D p x ∈ lattice₂ D Zd.M p Λ) : x ∈ Λ := by
  refine PI.UnitaryGroupMassFormula.UJClassMass.interLocF (F := D.host.F) Λ hΛ.toIsLattice x fun v => ?_
  haveI := v.isPrime
  letI := hΛ
  have h2 := (Formalism.L2.SG.Pf.LocalDenominators.baseChangeAt_mem_localLattice_iff Zd v (Λ := Λ) (by infer_instance) x).1 (h v)
  exact (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF v.asIdeal Λ x).1 h2

theorem btLift_holds : BtLift Zd u u' F0 what₂ := by
  intro _ γ Z F'₂ φ φ' Λ₂ hs
  obtain ⟨_, _, ⟨hlat, hloc⟩, _⟩ := hs
  refine ⟨mem_of_baseChange_mem Zd hlat fun p => ?_, rfl⟩
  have hfr := (hloc p).1.1.2.2.1
  have h1 : locF' Zd p F'₂ (Fin.last D.R.rS) ∈ lattice₂ D Zd.M p Λ₂ := hfr.1.1 (Fin.last D.R.rS)
  rwa [locF'_last] at h1

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section

noncomputable section

open scoped Classical
open Module Matrix
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Grp

variable {D : D7} {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T)

theorem symm_mem_of_mem (s : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U : Submodule D.host.E (VS D).V)
    (h : ∀ x ∈ U, s x ∈ U) : ∀ x ∈ U, s.symm x ∈ U := by
  intro x hx
  let f : U →ₗ[D.host.E] U :=
    (s : (VS D).V →ₗ[D.host.E] (VS D).V).restrict (p := U) (q := U) (fun y hy => h y hy)
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply s.injective
    exact congrArg Subtype.val hab
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨x, hx⟩
  have hyx : s y.1 = x := congrArg Subtype.val hy
  rw [← hyx, LinearEquiv.symm_apply_apply]
  exact y.2

theorem Xflag_mono (j : ℕ) : Xflag F j ≤ Xflag F (j + 1) := by
  exact Formalism.L2.SG.Pf.xflag_mono_td F (Nat.le_succ j)

theorem Xflag_le_X (j : ℕ) : Xflag F j ≤ Xsp F := by
  exact PI.DCRelEquiv.UnitaryGroupMassFormula.Xflag_le_X F j

theorem X_eq_Xflag : Xsp F = Xflag F D.R.rS := by
  exact (Formalism.L2.SG.Pf.xflag_r F).symm

theorem flag_pres {s : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hs : ∀ j, ∀ x ∈ Xflag F (j + 1), s x - x ∈ Xflag F j)
    (j : ℕ) : ∀ x ∈ Xflag F j, s x ∈ Xflag F j := by
  intro x hx
  cases j with
  | zero =>
    rw [Formalism.L2.SG.Pf.xflag_zero_td F, Submodule.mem_bot] at hx
    rw [hx, map_zero]
    exact Submodule.zero_mem _
  | succ j =>
    have h1 := Xflag_mono F j (hs j x hx)
    have h2 := Submodule.add_mem _ h1 hx
    rwa [sub_add_cancel] at h2

theorem flag_inv {s : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hs : ∀ j, ∀ x ∈ Xflag F (j + 1), s x - x ∈ Xflag F j) :
    ∀ j, ∀ x ∈ Xflag F (j + 1), s.symm x - x ∈ Xflag F j := by
  intro j x hx
  have hy : s.symm x ∈ Xflag F (j + 1) :=
    symm_mem_of_mem s (Xflag F (j + 1)) (flag_pres F hs (j + 1)) x hx
  have h1 := hs j (s.symm x) hy
  rw [LinearEquiv.apply_symm_apply] at h1
  have h2 := Submodule.neg_mem _ h1
  rwa [neg_sub] at h2

theorem flag_mul {s t : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hs : ∀ j, ∀ x ∈ Xflag F (j + 1), s x - x ∈ Xflag F j) (ht : ∀ j, ∀ x ∈ Xflag F (j + 1), t x - x ∈ Xflag F j) :
    ∀ j, ∀ x ∈ Xflag F (j + 1), (s * t) x - x ∈ Xflag F j := by
  intro j x hx
  have htx : t x ∈ Xflag F (j + 1) := flag_pres F ht (j + 1) x hx
  have h1 := Submodule.add_mem _ (hs j (t x) htx) (ht j x hx)
  show s (t x) - x ∈ Xflag F j
  rwa [sub_add_sub_cancel] at h1

theorem X_pres {s : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hs : ∀ j, ∀ x ∈ Xflag F (j + 1), s x - x ∈ Xflag F j) :
    ∀ x ∈ Xsp F, s x ∈ Xsp F := by
  intro x hx
  rw [X_eq_Xflag F] at hx ⊢
  exact flag_pres F hs _ x hx

theorem SRat_inv {s : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hs : s ∈ SRat F) : s.symm ∈ SRat F := by
  simp only [SRat, Set.mem_setOf_eq] at hs ⊢
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hs.1, flag_inv F hs.2.1, ?_⟩
  have h1 := symm_mem_of_mem s (Xsp F) (X_pres F hs.2.1) _ hs.2.2
  have h2 := Submodule.neg_mem _ h1
  rw [map_sub, LinearEquiv.symm_apply_apply, neg_sub] at h2
  exact h2

theorem SRat_mul {s t : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hs : s ∈ SRat F) (ht : t ∈ SRat F) : s * t ∈ SRat F := by
  simp only [SRat, Set.mem_setOf_eq] at hs ht ⊢
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem hs.1 ht.1, flag_mul F hs.2.1 ht.2.1, ?_⟩
  have hw := ht.2.2
  have hsw := X_pres F hs.2.1 _ hw
  have key : (s * t) F.fl.z - F.fl.z = (s F.fl.z - F.fl.z) +
      (s (t F.fl.z - F.fl.z) - (t F.fl.z - F.fl.z)) + (t F.fl.z - F.fl.z) := by
    show s (t F.fl.z) - F.fl.z = _
    rw [map_sub]; abel
  rw [key]
  exact Submodule.add_mem _ (Submodule.add_mem _ hs.2.2 (Submodule.sub_mem _ hsw hw)) hw

theorem perp_pres {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hi : n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hX : ∀ x ∈ Xsp F, n.symm x ∈ Xsp F) : ∀ y ∈ orth (VS D) (Xsp F), n y ∈ orth (VS D) (Xsp F) := by
  have hi' : ∀ a b, (VS D).hT (n a) (n b) = (VS D).hT a b := hi
  intro y hy
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hy ⊢
  intro x hx
  have h1 := hi' (n.symm x) y
  rw [LinearEquiv.apply_symm_apply] at h1
  rw [h1]
  exact hy _ (hX x hx)

theorem NRat_inv {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NRat F) : n.symm ∈ NRat F := by
  simp only [NRat, Set.mem_setOf_eq] at hn ⊢
  have hX : ∀ x ∈ Xsp F, n.symm x ∈ Xsp F := symm_mem_of_mem n (Xsp F) (X_pres F hn.2.1)
  have hO := perp_pres F hn.1 hX
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hn.1, flag_inv F hn.2.1, ?_⟩
  intro x hx
  have hy := symm_mem_of_mem n (orth (VS D) (Xsp F)) hO x hx
  have h2 := Submodule.neg_mem _ (hn.2.2 _ hy)
  rw [LinearEquiv.apply_symm_apply, neg_sub] at h2
  exact h2

theorem NRat_mul {n m : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NRat F) (hm : m ∈ NRat F) : n * m ∈ NRat F := by
  simp only [NRat, Set.mem_setOf_eq] at hn hm ⊢
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem hn.1 hm.1, flag_mul F hn.2.1 hm.2.1, ?_⟩
  intro x hx
  have hw := hm.2.2 x hx
  have hnw := X_pres F hn.2.1 _ hw
  have key : (n * m) x - x = (n x - x) + (n (m x - x) - (m x - x)) + (m x - x) := by
    show n (m x) - x = _
    rw [map_sub]; abel
  rw [key]
  exact Submodule.add_mem _ (Submodule.add_mem _ (hn.2.2 x hx) (Submodule.sub_mem _ hnw hw)) hw

end Grp

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end
