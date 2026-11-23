module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle060
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle076
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle070
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle080
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle065
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GflagSwap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.Lemmas
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IsometryFixFlagAnisotropicVectorOfFixFrame
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle081
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.P2MemZ2OfMemZ2
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle008
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle079
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle055
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FiberCount
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle075
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefNotInt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountOrb
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle082
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle052
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle035

@[expose] public section

section

noncomputable section

open ValuativeRel

namespace Formalism.MainNotions.S.Loc.HermSp.CohU

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V}

theorem gdet_ne_of_ratio {r : ℕ} {f f₁ f₂ : Fin (r + 1) → V} {T T' : F} (h1G : H.Gdet f f₁ T T' ≠ 0)
    (h2u : IsUnit (H.Dl f f₂ (r + 1)))
    (hrat : H.Dl f f₁ r * H.Dl f f₂ (r + 1) = H.Dl f f₂ r * H.Dl f f₁ (r + 1)) : H.Gdet f f₂ T T' ≠ 0 := by
  intro h0
  apply h1G
  have hr' := congrArg M.L.cj hrat
  simp only [map_mul] at hr'
  have key : H.normE (H.Dl f f₁ (r + 1)) * H.Gdet f f₂ T T' =
      H.normE (H.Dl f f₂ (r + 1)) * H.Gdet f f₁ T T' := by
    unfold HermSp.Gdet HermSp.normE
    linear_combination (algebraMap F E (T * T') * (M.L.cj (H.Dl f f₁ r) * M.L.cj (H.Dl f f₂ (r + 1)))) * hrat +
      (algebraMap F E (T * T') * H.Dl f f₂ r * H.Dl f f₁ (r + 1)) * hr'
  rw [h0, mul_zero] at key
  have hu : IsUnit (H.normE (H.Dl f f₂ (r + 1))) := h2u.mul (h2u.map M.L.cj)
  exact (hu.mul_right_eq_zero).1 key.symm

end Formalism.MainNotions.S.Loc.HermSp.CohU

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open CohCut

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem gdl_full (x y : Fin (D.R.rS + 1) → (VS D).V) :
    Formalism.L2.SG.Pf.ScalarFramePf.GDl x y (D.R.rS + 1) = (Formalism.L2.SG.Pf.ScalarFramePf.GZ x y).det := by
  unfold Formalism.L2.SG.Pf.ScalarFramePf.GDl
  rw [dite_eq_left le_rfl]
  have hc : (Fin.castLE (le_refl (D.R.rS + 1)) : Fin (D.R.rS + 1) → Fin (D.R.rS + 1)) = id :=
    funext fun i => Fin.ext rfl
  rw [hc, Matrix.submatrix_id_id]

theorem local_discriminant_unit_of_det (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D)
    (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (hZ : ZhatL (lf D F0) F'₂ = Z) (hdet : Z.det ≠ 0) :
    IsUnit ((locH Zd p).Dl (tLoc Zd p γ).f (locF' Zd p F'₂) (D.R.rS + 1)) := by
  have e : (locH Zd p).Dl (tLoc Zd p γ).f (locF' Zd p F'₂) (D.R.rS + 1) =
      (∏ i : Fin (D.R.rS + 1), (Zd.M p).L.cj (sgnP D p (Fin.castLE le_rfl i) * frFac Zd.δ p (Fin.castLE le_rfl i))) *
        (∏ i : Fin (D.R.rS + 1), (sgnP' D p (Fin.castLE le_rfl i) * frFac Zd.δ p (Fin.castLE le_rfl i))) *
        (D.s.atP p).ιE (Formalism.L2.SG.Pf.ScalarFramePf.GDl (frame (lf D F0)) (frame F'₂) (D.R.rS + 1)) :=
    Formalism.L2.SG.Pf.ScalarFramePf.dl_loc (Z := Zd) (p := p) (frame (lf D F0)) (frame F'₂)
      (fun a => sgnP D p a * frFac Zd.δ p a) (fun b => sgnP' D p b * frFac Zd.δ p b) (D.R.rS + 1) le_rfl
  rw [e]
  have hGZ : Formalism.L2.SG.Pf.ScalarFramePf.GZ (frame (lf D F0)) (frame F'₂) = Z := by
    rw [← hZ]; ext a b; rfl
  have hne : Formalism.L2.SG.Pf.ScalarFramePf.GDl (frame (lf D F0)) (frame F'₂) (D.R.rS + 1) ≠ 0 := by
    rw [gdl_full, hGZ]; exact hdet
  refine IsUnit.mul (IsUnit.mul ?_ ?_) (Formalism.L2.SG.Pf.BBTie.bt_iota_unit p hne)
  · exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
      (fun i _ => (Formalism.L2.SG.Pf.ScalarFramePf.isUnit_sF Zd p _).map (Zd.M p).L.cj)
  · exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
      (fun i _ => Formalism.L2.SG.Pf.ScalarFramePf.isUnit_sF' Zd p _)

theorem cohDG_holds : CohDG Zd u u' F0 what₂ := by
  intro _ γ Z F'₂ φ' hH
  refine Set.finite_empty.subset fun p hp => ?_
  have hdet : Z.det ≠ 0 := (starMinors_holds u u' F0 what₂ γ Z hH.1).1
  have hu := local_discriminant_unit_of_det Zd p γ Z F'₂ hH.2.1 hdet
  have T1 := hH.2.2.2 p
  exact absurd ⟨hu, Formalism.MainNotions.S.Loc.HermSp.CohU.gdet_ne_of_ratio T1.1.1.2.2.2.2.1 hu T1.2.2.2.1.2.2.2.2.2⟩ hp

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.TupGlobApprox

open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.Pf.ProdEApprox Formalism.L2.SG.Pf.PCount ValuativeRel
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.TupGlob
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem locTarget (Zd : LocDat D) (u u' : D.what₂.Word) (p : PlF D) (w : Point D.host.E (D.R.rS + 1))
    {Z₁ L₁ U₁ A₀ B₀ : PairVal.MatR D} (hL₁ : IsLo L₁) (hU₁ : IsUp U₁)
    (hZ : Z₁ * Sg D.host.E D.R.rS = L₁ * ptMat w * U₁) (hA₀ : IsLo A₀) (hB₀ : IsUp B₀) {l ρ : MatP D p}
    (hl : TieN.IntLow (Zd.M p) l) (hρ : TieN.IntUp (Zd.M p) ρ)
    (h : locL Zd p A₀ B₀ * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * locR Zd p A₀ B₀ =
      l * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * ρ) :
    LocTarget Zd p w L₁ U₁ A₀ B₀ := by
  rcases hM : (Zd.M p).split with _ | g
  · exact target_L Zd u u' p hM w hL₁ hU₁ hZ hA₀ hB₀ hl hρ h
  · exact target_G Zd u u' p hM w hL₁ hU₁ hZ hA₀ hB₀ hl hρ h

theorem cf_int (Zd : LocDat D) (p : PlF D) (hδ1 : Zd.δ p ∈ 𝒪[(D.s.atP p).Fp])
    (hδ2 : (Zd.δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp]) (hu1 : (D.s.atP p).ιE (uP p : D.host.E) ∈ (D.s.atP p).O)
    (hu2 : (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) ∈ (D.s.atP p).O) :
    (∀ a, algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a) ∈ (D.s.atP p).O) ∧
      ∀ a, algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a) ∈ (D.s.atP p).O := by
  have e1 : (D.s.atP p).ιE ((uP p : ℚ) : D.host.E) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF ((uP p : ℚ) : D.host.F)) := by
    rw [← (D.s.atP p).compat, map_ratCast (algebraMap D.host.F D.host.E)]
  have e2 : (D.s.atP p).ιE (((uP p : ℚ) : D.host.E)⁻¹) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (((D.s.atP p).ιF ((uP p : ℚ) : D.host.F))⁻¹) := by
    rw [← map_inv₀ (D.s.atP p).ιF, ← (D.s.atP p).compat, map_inv₀ (algebraMap D.host.F D.host.E),
      map_ratCast (algebraMap D.host.F D.host.E)]
  have hy : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (yP Zd p) ∈ (D.s.atP p).O := by
    unfold yP
    rw [map_mul, ← e1]
    exact (D.s.atP p).O.mul_mem (LocModel.LM.algebraMap_mem_O p hδ1) hu1
  have hyi : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (yP Zd p)⁻¹ ∈ (D.s.atP p).O := by
    unfold yP
    rw [mul_inv, map_mul, ← e2]
    exact (D.s.atP p).O.mul_mem (LocModel.LM.algebraMap_mem_O p hδ2) hu2
  exact ⟨fun a => by unfold cf; rw [map_pow]; exact pow_mem hyi _,
    fun a => by unfold cfi; rw [map_pow]; exact pow_mem hy _⟩

theorem stabApprox (Zd : LocDat D) (u u' : D.what₂.Word) : Formalism.L2.SG.Pf.TupGlob.StabApprox Zd u u' := by
  intro w Z₁ A₀ B₀ hAt hA₀ hB₀ hloc
  obtain ⟨L₁, U₁, hL₁u, hU₁u, e₁⟩ := hAt
  have hL₁ : IsLo L₁ := isLo_of_uni hL₁u
  have hU₁ : IsUp U₁ := isUp_of_uni hU₁u
  rw [zhatOM_eq] at e₁
  choose l ρ hl hρ hlr using hloc
  choose T c hc0 hT using fun p => locTarget Zd u u' p w hL₁ hU₁ e₁ hA₀ hB₀ (hl p) (hρ p) (hlr p)
  have hE : ∀ᶠ p in Filter.cofinite, ∀ (k : Fin 8) (i j : Fin (D.R.rS + 1)),
      (D.s.atP p).ιE ((![A₀, B₀, L₁, L₁⁻¹, U₁, U₁⁻¹, Matrix.of fun i _ => pv w.1 i,
        Matrix.of fun i _ => (pv w.1 i)⁻¹] : Fin 8 → PairVal.MatR D) k i j) ∈ (D.s.atP p).O :=
    Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      LocModel.LM.iotaIntegral_almost_all D _
  have hG := (LocModel.good_cofinite Zd.δ Zd.M Zd.agree ∅).and hE
  have hfin := Filter.eventually_cofinite.1 hG
  choose t ht1 ht2 using fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) =>
    sa_lat D.s.atP hfin.toFinset (fun p => T p ij.1 ij.2) c (fun p _ => hc0 p)
  let X' : PairVal.MatR D := Matrix.of fun i j => if Free (fσ w) i j then t (i, j) else (1 : PairVal.MatR D) i j
  have hX'1 : ∀ i j, ¬ Free (fσ w) i j → X' i j = (1 : PairVal.MatR D) i j := fun i j h => by
    simp only [X', Matrix.of_apply, if_neg h]
  have hX'2 : ∀ i j, Free (fσ w) i j → X' i j = t (i, j) := fun i j h => by
    simp only [X', Matrix.of_apply, if_pos h]
  have hX' : IsLo X' :=
    ⟨fun a => by rw [hX'1 a a (fun h => lt_irrefl a h.1), Matrix.one_apply_eq],
      fun a b hab => by rw [hX'1 a b (fun h => absurd h.1 (not_lt.2 hab.le)), Matrix.one_apply_ne hab.ne]⟩
  have hpat : ∀ i j, fσ w j < fσ w i → X' i j = 0 := fun i j hij => by
    have hf : ¬ Free (fσ w) i j := fun h => absurd h.2 (not_lt.2 hij.le)
    have hne : i ≠ j := fun e => by rw [e] at hij; exact lt_irrefl _ hij
    rw [hX'1 i j hf, Matrix.one_apply_ne hne]
  obtain ⟨hgX, hgY, hst⟩ := glob_stab w hL₁ hU₁ e₁ hX' hpat
  refine ⟨gX L₁ X', gY w U₁ X', hgX, hgY, hst, fun p => ?_⟩
  by_cases hp : p ∈ hfin.toFinset
  · exact hT p X' hX' hpat fun i j hf => by rw [hX'2 i j hf]; exact ht1 (i, j) p hp
  · have hgp : _ ∧ _ := not_not.1 ((Set.Finite.mem_toFinset hfin).not.1 hp)
    obtain ⟨⟨hM, ⟨hδ1, hδ2⟩, ⟨hu1, hu2⟩, -⟩, hEp⟩ := hgp
    obtain ⟨hcf, hcfi⟩ := cf_int Zd p hδ1 hδ2 hu1 hu2
    have hXi : ∀ i j, (D.s.atP p).ιE (X' i j) ∈ (D.s.atP p).O := by
      intro i j
      by_cases hf : Free (fσ w) i j
      · rw [hX'2 i j hf]; exact ht2 (i, j) p hp
      · rw [hX'1 i j hf, Matrix.one_apply]
        split_ifs
        · rw [map_one]; exact Subring.one_mem _
        · rw [map_zero]; exact Subring.zero_mem _
    exact good_at Zd p hM w hL₁ hU₁ hA₀ hB₀ hX' hpat hcf hcfi
      (fun i j => hEp 0 i j) (fun i j => hEp 1 i j) (fun i j => hEp 2 i j) (fun i j => hEp 3 i j)
      (fun i j => hEp 4 i j) (fun i j => hEp 5 i j) (fun a => hEp 6 a a) (fun a => hEp 7 a a) hXi

end Formalism.L2.SG.Pf.TupGlobApprox
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

theorem mem_Xa_mapFlag {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
    (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : FlagG S r T) (j : ℕ) (x : S.V) :
    x ∈ (mapFlag γ hγ F).Xa j ↔ γ.symm x ∈ F.Xa j := by
  have h1 : (mapFlag γ hγ F).Xa j = (F.Xa j).map (γ : S.V →ₗ[E] S.V) := by
    unfold FlagG.Xa
    rw [Submodule.map_span, ← Set.image_comp]
    rfl
  rw [h1]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨γ.symm x, h, by simp⟩

theorem mem_Xflag_mapLF {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
    (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (j : ℕ) (x : S.V) :
    x ∈ Xflag (mapLF γ F) j ↔ γ.symm x ∈ Xflag F j := by
  unfold Xflag mapLF
  rw [dite_eq_left hγ]
  exact mem_Xa_mapFlag γ hγ F.fl j x

variable {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}

theorem NLam_SRat {T : D.host.E} {Λ : Submodule (𝓞 D.host.E) (VS D).V} {F : LFlag (D.sp.Y 0) D.R.rS T}
    {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NLam Λ F) : n ∈ SRat F := by
  obtain ⟨hA, hf, hp⟩ := hn
  refine ⟨hA.1, hf, hp _ ?_⟩
  refine (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth _).2 fun x hx => ?_
  rw [hT_swap F.fl.z x, hT_z_X F.fl hx, star_zero]

theorem NLam_transport (t : TauC Y u u') {Λ : Submodule (𝓞 D.host.E) (VS D).V} {m : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hm : m ∈ NLam Λ t.frame) : t.lin⁻¹ * m * t.lin ∈ SRat (lf D (X.Fu u')) := by
  have hγ : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hS := NLam_SRat hm
  obtain ⟨hmi, hmf, hmz⟩ := hS
  refine ⟨(Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).inv_mem hγ) hmi) hγ,
    fun j x hx => ?_, ?_⟩
  · have hx' : t.lin x ∈ Xflag t.frame (j + 1) :=
      (mem_Xflag_mapLF t.lin hγ (lf D (X.Fu u')) (j + 1) _).2 (by rw [LinearEquiv.symm_apply_apply]; exact hx)
    have h := hmf j _ hx'
    have h' := (mem_Xflag_mapLF t.lin hγ (lf D (X.Fu u')) j _).1 h
    rw [map_sub, LinearEquiv.symm_apply_apply] at h'
    exact h'
  · have h2 : m t.frame.fl.z - t.frame.fl.z ∈ t.frame.fl.X := hmz
    have h3 := (mem_frameX Y t _).1 h2
    rw [map_sub, frame_z_eq_lin_zu, LinearEquiv.symm_apply_apply] at h3
    show t.lin.symm (m (t.lin (X.Fu u').z)) - (X.Fu u').z ∈ _
    exact h3

end Formalism.L2.SG.NGCut.NormalVectorPairings
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


variable (u') (F0) in
def GenXiRev : Prop :=
  ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (p : PlF D),
    IsRowLat D F0 Λ → AdmWit Λ (gS D) (lf D F0) F' 1 → IsLift Λ F' →
    (locH Zd p).IsGeneric ⟨lattice₂ D Zd.M p Λ, (locTerm Zd p Λ (lf D F0) F' (Tu D u) (Tu D u')).f, locF' Zd p F',
      (locTerm Zd p Λ (lf D F0) F' (Tu D u) (Tu D u')).T, (locTerm Zd p Λ (lf D F0) F' (Tu D u) (Tu D u')).T'⟩ →
    (locH Zd p).IsGeneric (locTerm Zd p Λ (lf D F0) F' (Tu D u) (Tu D u'))

theorem rowLat_of_move (hC : CtxP u u' F0 what₂) (γ : TermDef.Term D u u' F0 what₂) {Λ₂ : Submodule (𝓞 D.host.E) (VS D).V}
    {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ unipotentFrameFixers F0)
    (himg : (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) = (γ.lam : Set (VS D).V)) : IsRowLat D F0 Λ₂ := by
  have hrow := hC.2.1.1 γ.lam γ.mem
  have hg : Formalism.HermitianLatticesTheory.gmap n Λ₂ = γ.lam := gmap_eq_of_image himg
  have hni : n⁻¹ ∈ Formalism.L2.SG.Pf.Cnt.StabilizerQuotient.G0 F0 := by
    refine ⟨(Formalism.HermitianLatticesTheory.isom _).inv_mem hn.1, fun a => ?_⟩
    refine Fin.lastCases ?_ (fun i => ?_) a
    · have h := hn.2.2.2.2
      simp only [FlagG.fvec, Fin.snoc_last]
      show n.symm _ = _
      rw [LinearEquiv.symm_apply_eq, h]
    · have h := hn.2.2.2.1 i
      simp only [FlagG.fvec, Fin.snoc_castSucc]
      show n.symm _ = _
      rw [LinearEquiv.symm_apply_eq, h]
  have h2 := Formalism.L2.SG.Pf.Cnt.StabilizerQuotient.rowLat_gmap ⟨n⁻¹, hni⟩ hrow
  have e : Formalism.HermitianLatticesTheory.gmap (n⁻¹ : (VS D).V ≃ₗ[D.host.E] (VS D).V) γ.lam = Λ₂ := by
    rw [← hg, ← Formalism.L2.SG.Pf.gmap_mul_sat, inv_mul_cancel, Formalism.L2.SG.Pf.gmap_one_sat]
  rw [← e]; exact h2

variable {Zd}

theorem btGen_of (hOK : BtOK Zd u u' F0 what₂) (hGX : GenXiRev Zd u' F0) : BtGen Zd u u' F0 what₂ := by
  intro hC γ Z F'₂ φ φ' Λ₂ hs
  have hLift := btLift_holds Zd hC γ Z F'₂ φ φ' Λ₂ hs
  have hAdm := btAdm Zd hC γ Z F'₂ φ φ' Λ₂ hs
  have hG := btG_holds Zd hC γ Z F'₂ φ φ' Λ₂ hs
  have hOKv := hOK hC γ Z F'₂ φ φ' Λ₂ hs
  obtain ⟨_, _, ⟨hlat, hloc⟩, ⟨n, hn, himg⟩⟩ := hs
  have hR := rowLat_of_move hC γ hn himg
  have hPD : PD D Λ₂ (lf D F0) u' (liftF F'₂) := ⟨hLift, ⟨1, hAdm⟩, hOKv⟩
  refine (Formalism.L2.SG.Pf.frameGenLoc_holds D Zd F0 Λ₂ (liftF F'₂) hR hPD
    (Formalism.L2.SG.Pf.m_plus_independent _ _ _ _) hG).2 fun p => ?_
  exact hGX Λ₂ (liftF F'₂) p hR hAdm hLift (hloc p).1

theorem bwdTerm'_of' (hOK : BtOK Zd u u' F0 what₂) (hGX : GenXiRev Zd u' F0) : BwdTerm' Zd u u' F0 what₂ :=
  bwdTerm'_of Zd (btLift_holds Zd) (btAdm Zd) (btG_holds Zd) hOK (btGen_of hOK hGX)

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

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
  {δ : ∀ p : PlF D, (D.s.atP p).Fp} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem nu_not_class_holds : FCount.NuNotCls M δ u u' F0 what₂ :=
  FCount.nuNotCls_of (fun Zd => PCount.inOrbZ_holds Zd u u')

theorem local_class_holds (hA : ∀ p, Agree δ M p) (hT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2])
    (hrows : IsRowReps D F0 what₂) (hN : PairVal.NormRepExists D u u' F0 what₂) : LocClsE M δ u u' F0 what₂ :=
  locClsE_of hA hT hrows hN (fun Zd => PCount.inOrbZ_holds Zd u u')

theorem coefProd_of_steps (hA : ∀ p, Agree δ M p) (hT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2])
    (hrows : IsRowReps D F0 what₂) (hN : PairVal.NormRepExists D u u' F0 what₂)
    (hM : Formalism.L2.SG.Pf.NormRepMove D u u') (hPL : PhaseLoc M δ u u' F0 what₂) (hPP : PsiProdE D)
    (hV : VolProd M δ u u' F0 what₂) : CoefProd M δ u u' F0 what₂ :=
  coefProd_of hA (local_class_holds hA hT hrows hN) (phase_class_holds M δ)
    (phaseProd_of hrows hN (Formalism.L2.SG.Pf.phase_well_defined hM hrows) (phaseAtRep_of hPL hPP)) hV

theorem coefficient_product_of_local (hA : ∀ p, Agree δ M p) (hT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2])
    (hrows : IsRowReps D F0 what₂) (hN : PairVal.NormRepExists D u u' F0 what₂)
    (hM : Formalism.L2.SG.Pf.NormRepMove D u u') (hPL : PhaseLoc M δ u u' F0 what₂) (hPP : PsiProdE D)
    (hVP : VolIdxProd M δ u u' F0 what₂) : CoefProd M δ u u' F0 what₂ :=
  coefProd_of_steps hA hT hrows hN hM hPL hPP (volProd_of hA hT hrows hN (local_class_holds hA hT hrows hN) hVP)

end Formalism.L2.SG.Pf.Coef
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut
  Formalism.L2.SG.Pf.ProdEP2Core

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D)

def sgnU : GLp p :=
  ⟨Formalism.L2.SG.LsDatumB.sgnP p, Formalism.L2.SG.LsDatumB.sgnP p, Formalism.L2.SG.Pf.FibQ.permSign_mul_self₂ p,
    Formalism.L2.SG.Pf.FibQ.permSign_mul_self₂ p⟩

def tau : GG p →* GG p where
  toFun x := (x.1, MulOpposite.op (sgnU p * x.2.unop * sgnU p))
  map_one' := by
    have hs : sgnU p * sgnU p = 1 := Units.ext (Formalism.L2.SG.Pf.FibQ.permSign_mul_self₂ p)
    ext1
    · rfl
    · apply MulOpposite.unop_injective
      show sgnU p * (1 : GLp p) * sgnU p = 1
      rw [mul_one, hs]
  map_mul' x y := by
    have hs : sgnU p * sgnU p = 1 := Units.ext (Formalism.L2.SG.Pf.FibQ.permSign_mul_self₂ p)
    ext1
    · rfl
    · apply MulOpposite.unop_injective
      simp only [Prod.snd_mul, MulOpposite.unop_mul, MulOpposite.unop_op]
      calc sgnU p * (y.2.unop * x.2.unop) * sgnU p
          = sgnU p * y.2.unop * (sgnU p * sgnU p) * x.2.unop * sgnU p := by rw [hs]; group
        _ = _ := by group

theorem tau_tau (x : GG p) : tau p (tau p x) = x := by
  have hs : sgnU p * sgnU p = 1 := Units.ext (Formalism.L2.SG.Pf.FibQ.permSign_mul_self₂ p)
  ext1
  · rfl
  · apply MulOpposite.unop_injective
    show sgnU p * (sgnU p * x.2.unop * sgnU p) * sgnU p = x.2.unop
    calc sgnU p * (sgnU p * x.2.unop * sgnU p) * sgnU p = (sgnU p * sgnU p) * x.2.unop * (sgnU p * sgnU p) := by
          group
      _ = _ := by rw [hs]; group

end Formalism.L2.SG.Pf.CountAt
end
end
