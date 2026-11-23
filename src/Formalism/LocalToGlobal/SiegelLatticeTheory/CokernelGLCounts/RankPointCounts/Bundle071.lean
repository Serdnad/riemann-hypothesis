module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle063
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.Bundle002
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexBCongruence
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
public import Formalism.LocalRingCardinality.ConjSqrtMinusD
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle030
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle031
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle033
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle048
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle045
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle057
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle058
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarNMove
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.Lemmas
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle043
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle022
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WittExistsHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle021
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle014
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle013
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle011
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle015
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle064
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle065
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle060
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle029

@[expose] public section

section

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolFib

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal
  Formalism.L2.SG.Pf.ZsVolAct Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem zv (Z a b : MatR D) (h : a * ZhatOM Z * b = ZhatOM Z) : a * Z * sbs b = Z := by
  rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.zhatOM_eq] at h
  unfold sbs
  calc a * Z * (Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS * b * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS) =
      a * (Z * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS) * b * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS := by simp only [Matrix.mul_assoc]
    _ = Z := by rw [h, Matrix.mul_assoc, Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM_sq, Matrix.mul_one]

theorem uu'_eq (Z a₁ a₂ V₁ V₂ uu' : MatR D) (hZ : IsUnit Z.det) (ha₁ : IsUnit a₁.det)
    (hV₁ : IsUnit V₁.det) (hV₂ : IsUnit V₂.det)
    (h₁ : a₁ * Z * V₁ = Z) (h₂ : a₂ * Z * V₂ = Z) (hc : a₁⁻¹ * a₂ * Z * uu' = Z) : uu' * V₁ = V₂ := by
  have e2 : a₂ * Z = Z * V₂⁻¹ := by
    calc a₂ * Z = a₂ * Z * V₂ * V₂⁻¹ := by rw [Matrix.mul_nonsing_inv_cancel_right _ _ hV₂]
      _ = Z * V₂⁻¹ := by rw [h₂]
  have e3 : a₁⁻¹ * Z = Z * V₁ := by
    calc a₁⁻¹ * Z = a₁⁻¹ * (a₁ * Z * V₁) := by rw [h₁]
      _ = Z * V₁ := by rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ ha₁]
  have e4 : Z * (V₁ * V₂⁻¹ * uu') = Z * 1 := by
    rw [Matrix.mul_one]
    calc Z * (V₁ * V₂⁻¹ * uu') = a₁⁻¹ * Z * V₂⁻¹ * uu' := by rw [e3]; simp only [Matrix.mul_assoc]
      _ = a₁⁻¹ * (a₂ * Z) * uu' := by rw [e2]; simp only [Matrix.mul_assoc]
      _ = a₁⁻¹ * a₂ * Z * uu' := by simp only [Matrix.mul_assoc]
      _ = Z := hc
  have e5 : V₁ * V₂⁻¹ * uu' = 1 := by
    have := congrArg (fun M => Z⁻¹ * M) e4
    simpa only [Matrix.nonsing_inv_mul_cancel_left _ _ hZ] using this
  have e6 : uu' = V₂ * V₁⁻¹ := by
    calc uu' = (V₂ * V₁⁻¹) * (V₁ * V₂⁻¹ * uu') := by
          rw [Matrix.mul_assoc V₂, ← Matrix.mul_assoc V₁⁻¹, ← Matrix.mul_assoc V₁⁻¹,
            Matrix.nonsing_inv_mul _ hV₁, Matrix.one_mul, Matrix.mul_nonsing_inv_cancel_left _ _ hV₂]
      _ = V₂ * V₁⁻¹ := by rw [e5, Matrix.mul_one]
  rw [e6, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hV₁, Matrix.mul_one]

theorem fib_mpr (γ : Term D u u' F0 what₂) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L : MatR D)
    (hL : IsLoUni L) (hT0 : ((Tu D u : ℕ) : D.host.E) ≠ 0) (hZu : IsUnit (Zhat F0 F'.fl).det)
    (a₁ : GLR D) (b₁ : MatR D) (ν₁ m₁ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (F₁ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (a₂ : GLR D) (b₂ : MatR D) (ν₂ m₂ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (F₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (x₁ x₂ : GLR D) (hx₁ : (x₁ : MatR D) = L⁻¹ * (a₁ : MatR D) * L) (hx₂ : (x₂ : MatR D) = L⁻¹ * (a₂ : MatR D) * L)
    (hd₁ : LiftData u u' F0 what₂ γ F' a₁ b₁ ν₁ m₁ F₁) (hd₂ : LiftData u u' F0 what₂ γ F' a₂ b₂ ν₂ m₂ F₂)
    (hh : x₁⁻¹ * x₂ ∈ PairVal.stabAut D u u' F0 what₂ γ F' L) : CntLocal.NilradicalFlagMoved F0 γ.lam F₁ F₂ := by
  obtain ⟨ha₁, hb₁, hZ₁, -, hν₁, -, hν₁f, hm₁f, -, -, hF₁⟩ := hd₁
  obtain ⟨ha₂, hb₂, hZ₂, -, hν₂, -, hν₂f, hm₂f, -, -, hF₂⟩ := hd₂
  obtain ⟨s, ⟨hsF, hsF'⟩, uu, hu, hx⟩ := (mem_stabAut_iff u u' F0 what₂ γ F' L hL hT0 _).1 hh
  have hLd : IsUnit L.det := by rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_det hL]; exact isUnit_one
  have ha₁d : IsUnit (a₁ : MatR D).det := by rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_det ha₁]; exact isUnit_one
  have hU₁ := Formalism.L2.SG.Pf.StabilizerIndexVolumes.up_conjT ha₁
  have hU₂ := Formalism.L2.SG.Pf.StabilizerIndexVolumes.up_conjT ha₂
  have hV₁ : IsUpUni (sbs b₁) := Formalism.L2.SG.Pf.StabilizerIndexVolumes.up_sgn hb₁
  have hV₂ : IsUpUni (sbs b₂) := Formalism.L2.SG.Pf.StabilizerIndexVolumes.up_sgn hb₂
  have hV₁d : IsUnit (sbs b₁).det := by rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.up_det hV₁]; exact isUnit_one
  have hV₂d : IsUnit (sbs b₂).det := by rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.up_det hV₂]; exact isUnit_one
  have hU₁d : IsUnit ((a₁ : MatR D).conjTranspose).det := by rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.up_det hU₁]; exact isUnit_one

  have hsF0 := hsF
  obtain ⟨hAut, hf1, hf2⟩ := hsF
  obtain ⟨-, hg1, hg2⟩ := hsF'
  have hiso : ∀ x y, (VS D).hT (s x) (s y) = (VS D).hT x y := ((Formalism.L2.SG.Pf.isAutLam_iff _ s).1 hAut).1
  obtain ⟨uu0, huu0, hu0⟩ := Formalism.L2.SG.Pf.StabilizerIndexVolumes.tri_exists F0 s hf1 hf2
  have heq : uu = uu0 :=
    Formalism.L2.SG.Pf.StabilizerIndexVolumes.coef_unique (Formalism.L2.SG.Pf.StabilizerIndexVolumes.frame_indep F0 hT0) (fun b => s (F0.fvec b)) uu uu0 hu hu0
  subst heq
  obtain ⟨uu', -, hu'⟩ := Formalism.L2.SG.Pf.StabilizerIndexVolumes.tri_exists F'.fl s hg1 hg2
  have hZc := Formalism.L2.SG.Pf.StabilizerIndexVolumes.zhat_conj F0 F'.fl s hiso uu uu' hu0 hu'

  have himg := img_quot L _ _ hLd ha₁d x₁ x₂ hx₁ hx₂
  rw [hx] at himg
  have hcanc : uu.conjTranspose = ((a₂ : MatR D).conjTranspose * ((a₁ : MatR D).conjTranspose)⁻¹).conjTranspose := by
    have := congrArg (fun M => L * M * L⁻¹) himg
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hLd, Matrix.mul_one] at this
    simpa only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hLd, Matrix.one_mul] using this
  have huu : uu = (a₂ : MatR D).conjTranspose * ((a₁ : MatR D).conjTranspose)⁻¹ := by
    have := congrArg Matrix.conjTranspose hcanc
    simpa only [Matrix.conjTranspose_conjTranspose] using this
  have hcT : uu.conjTranspose = ((a₁ : MatR D))⁻¹ * (a₂ : MatR D) := by
    rw [hcanc, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
  have hc : ((a₁ : MatR D))⁻¹ * (a₂ : MatR D) * Zhat F0 F'.fl * uu' = Zhat F0 F'.fl := by
    rw [← hcT]; exact hZc.symm
  have hmove := uu'_eq _ _ _ _ _ uu' hZu ha₁d hV₁d hV₂d (zv _ _ _ hZ₁) (zv _ _ _ hZ₂) hc

  set n : (VS D).V ≃ₗ[D.host.E] (VS D).V := ν₂⁻¹ * s * ν₁ with hn
  have hnN : n ∈ NLam γ.lam (lf D F0) :=
    Formalism.L2.SG.Pf.nlamPf_mul (Formalism.L2.SG.Pf.nlamPf_mul (Formalism.L2.SG.Pf.nlamPf_inv hν₂) hsF0) hν₁
  have hnf := act_mul _ _ _ _ _ (act_mul _ _ _ _ _ (act_inv' _ ν₂ _ hU₂ hν₂f) hu0) hν₁f
  have hone : ((a₂ : MatR D).conjTranspose)⁻¹ * uu * (a₁ : MatR D).conjTranspose = 1 := by
    rw [huu, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ hU₁d,
      Matrix.nonsing_inv_mul _ (by rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.up_det hU₂]; exact isUnit_one)]
  rw [hone] at hnf
  have hnf' : ∀ b, n (F0.fvec b) = F0.fvec b := fun b => by
    rw [show F0.fvec b = frame (lf D F0) b from rfl, hnf b, ← act_one]
    rfl
  refine ⟨n, ⟨hnN, fun a => ?_, ?_⟩, fun a => ?_, ?_⟩
  · have := hnf' (Fin.castSucc a); simpa [FlagG.fvec, Fin.snoc_castSucc] using this
  · have := hnf' (Fin.last _); simpa [FlagG.fvec, Fin.snoc_last] using this
  all_goals
    have hsm : ∀ c, s (m₁ (frame F' c)) = m₂ (frame F' c) := fun c => by
      have := act_mul (frame F') s m₁ uu' (sbs b₁) hu' hm₁f c
      rw [hmove] at this
      rw [hm₂f c]
      exact this
    have hnF : ∀ c, n (frame F₁ c) = frame F₂ c := fun c => by
      rw [hF₁ c, hF₂ c]
      show ν₂⁻¹ (s (ν₁ (ν₁⁻¹ (m₁ (frame F' c))))) = _
      rw [show ν₁ (ν₁⁻¹ (m₁ (frame F' c))) = (ν₁ * ν₁⁻¹) (m₁ (frame F' c)) from rfl, mul_inv_cancel]
      show ν₂⁻¹ (s (m₁ (frame F' c))) = _
      rw [hsm c]
  · have := hnF (Fin.castSucc a); simpa [frame, FlagG.fvec, Fin.snoc_castSucc] using this
  · have := hnF (Fin.last _); simpa [frame, FlagG.fvec, Fin.snoc_last] using this

end Formalism.L2.SG.Pf.ZsVolFib

end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem bwdN_zorth : F0.z ∈ orth (VS D) (Xsp (lf D F0)) :=
  (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx => by
    rw [BwdNA.hsw (VS D) F0.z x]
    have h := NMoveP.hT_f_X F0 (Fin.last D.R.rS) hx
    rw [NMoveP.fvecL] at h
    rw [h, star_zero]

theorem bwdN_znotX : F0.z ∉ Xsp (lf D F0) := by
  intro h
  have h0 := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 (bwdN_zorth (F0 := F0)) F0.z h
  rw [F0.z_norm, neg_eq_zero] at h0
  have hT := (D.mem u).A.T_prime.ne_zero
  exact hT (Nat.cast_eq_zero.1 h0)

variable (u u' F0 what₂)


theorem bwdN_holds : BwdN Zd u u' F0 what₂ := by
  intro hC γ Z hZ F'₂ φ φ' hS Λ₂ hmem₂
  obtain ⟨hΛ₂, hloc₂⟩ := hmem₂
  obtain ⟨-, hT2, hφ⟩ := hS
  have hrow := hC.2.1.1 γ.lam γ.mem
  have : Submodule.IsFullLattice D.host.E γ.lam := hrow.1.1
  have ht1 := fun p => (hT2 p).1
  have hu : ∀ p a, IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a) := fun p a =>
    BwdNP.unit_of_frame Zd p γ (ht1 p).1.2.1 a
  have hSDl : ∀ p, (locH Zd p).IsSelfDual (lattice₂ D Zd.M p γ.lam) := fun p => (ht1 p).1.1
  have hSDl₂ : ∀ p, (locH Zd p).IsSelfDual (lattice₂ D Zd.M p Λ₂) := fun p => (hloc₂ p).1.1.1
  have hpr : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p γ.lam) (tLoc Zd p γ).f := fun p => (ht1 p).1.2.1.1
  have hpr₂ : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ₂) (tLoc Zd p γ).f := fun p => (hloc₂ p).1.1.2.1.1
  have hLset : ∀ p, (locH Zd p).Lset (lattice₂ D Zd.M p γ.lam) (tLoc Zd p γ).f =
      (locH Zd p).Lset (lattice₂ D Zd.M p Λ₂) (tLoc Zd p γ).f := fun p => by
    have h := (hloc₂ p).2.1
    rw [hφ p] at h
    rw [← h]
    exact (Set.image_id _).symm
  have hSD := BwdNP.sd_of_loc Zd (Λ := γ.lam) inferInstance hSDl
  have hSD₂ := BwdNP.sd_of_loc Zd (Λ := Λ₂) inferInstance hSDl₂
  set X := Xsp (lf D F0) with hXdef
  have hXiso : ∀ x ∈ X, ∀ y ∈ X, (VS D).hT x y = 0 := fun x hx y hy => NMoveP.hT_X_X F0 hx hy
  have hXX : ∀ {w : (VS D).V}, w ∈ orth (VS D) (orth (VS D) X) → w ∈ X := fun {w} hw =>
    BwdNA.mem_of_orth_orth (VS D) X fun v hv => by
      rw [BwdNA.hsw (VS D) v w, (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hw v hv, star_zero]
  have hXo := BwdNA.X_le_orth (VS D) X hXiso
  have hL : ∀ x ∈ Λ₂, x ∈ orth (VS D) X → ∃ y ∈ γ.lam, y - x ∈ X := fun x hx hxo => by
    obtain ⟨w, hw, hxw⟩ := BwdNA.dual_sum (VS D) γ.lam inferInstance hSD (orth (VS D) X) x
      (fun m hmΛ hmU => BwdNP.pair_int Zd γ hSDl (fun p => (hLset p).symm.subset) hx hxo hmΛ hmU)
    refine ⟨w, hw, ?_⟩
    have h2 := X.neg_mem (hXX hxw)
    rwa [neg_sub] at h2
  have hL' : ∀ y ∈ γ.lam, y ∈ orth (VS D) X → ∃ x ∈ Λ₂, x ∈ orth (VS D) X ∧ y - x ∈ X := fun y hy hyo => by
    obtain ⟨w, hw, hyw⟩ := BwdNA.dual_sum (VS D) Λ₂ inferInstance hSD₂ (orth (VS D) X) y
      (fun m hmΛ hmU => BwdNP.pair_int Zd γ hSDl₂ (fun p => (hLset p).subset) hy hyo hmΛ hmU)
    have hX1 := hXX hyw
    refine ⟨w, hw, ?_, hX1⟩
    have e : w = y - (y - w) := by abel
    rw [e]
    exact (orth (VS D) X).sub_mem hyo (hXo hX1)
  have hXm : ∀ x ∈ X, x ∈ Λ₂ ↔ x ∈ γ.lam := fun x hx =>
    ⟨BwdNP.memX Zd γ hpr₂ hpr inferInstance hu hx, BwdNP.memX Zd γ hpr hpr₂ inferInstance hu hx⟩
  have hy := BwdNP.exists_y Zd γ (Λ₂ := Λ₂) inferInstance hSD₂ hpr₂ hu bwdN_znotX
  have htr : ∃ c : D.host.E, IsIntegral ℤ c ∧ c + star c = 1 := by
    obtain ⟨c, hc⟩ := D.host.exists_trace_one
    refine ⟨(c : D.host.E), RingOfIntegers.isIntegral_coe c, ?_⟩
    rw [Formalism.BasicNotions.Examples₂.star_eq_conj (H := D.host)]
    exact hc
  obtain ⟨n, hiso, hnX, hnz, hno, himg⟩ := BwdNA.main (VS D) X hXiso F0.z bwdN_zorth γ.lam Λ₂
    inferInstance inferInstance hSD hSD₂ hXm
    (BwdNP.z_mem Zd γ (Λ := γ.lam) inferInstance hpr) (BwdNP.z_mem Zd γ (Λ := Λ₂) inferInstance hpr₂) hL hL' hy htr
  refine ⟨n, ⟨hiso, fun j x hx => ?_, hno, fun a => hnX _ (Submodule.subset_span ⟨a, rfl⟩), hnz⟩, himg⟩
  have hxX : x ∈ X := Submodule.span_mono (Set.image_subset_range _ _) hx
  rw [hnX x hxX, sub_self]
  exact zero_mem _

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolFin

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal PI.UnitaryGroupMassFormula.CntFormula
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem reps (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (hR : RowsOf u F0 what₂) (Z : MatZ D)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ ∈ what₂) :
    ∃ K : Set ((Fin D.R.rS → (VS D).V) × (VS D).V), K.Finite ∧
      ∀ F' ∈ EZ (Tn u') F0 Λ Z, ∃ n ∈ N0 F0 Λ, ((fun a => n (F'.fl.e a)), n F'.fl.z) ∈ K := by
  by_cases hne : (EZ (Tn u') F0 Λ Z).Nonempty
  · obtain ⟨F₁, hF₁⟩ := hne
    simp only [EZ, Set.mem_ofPred_eq] at hF₁
    have hG := hF₁.1.2.2
    rw [gz_eq, hF₁.2.2.2.2] at hG
    obtain ⟨R, hR1⟩ := rank_gram D _ _ Z hG
    have hfix := fixedOK_of_rows D u F0 what₂ hR hΛ
    obtain ⟨Wf, hWf, hW⟩ := orbit_count_first_stage D (Tn u') F0 Λ hfix Z R hR1
    obtain ⟨Af, hAf, hA⟩ := orbit_count_second_stage D (Tn u') F0 Λ hfix Z R hR1 Wf hWf
    refine ⟨_, finite_level_index D (Tn u') F0 Λ hfix Z R hR1 Wf Af hWf hAf, ?_⟩
    intro F' hF'
    have hx := good_places_integral D (Tn u') F0 Λ Z F' hF'
    obtain ⟨n₁, hn₁, h₁⟩ := hW _ hx
    have hx₁ := good_move D (Tn u') F0 Λ Z hx hn₁
    obtain ⟨n₂, hn₂, h₂, h₃⟩ := hA _ hx₁ h₁
    refine ⟨n₁.trans n₂, (unipotent_integral_isGroup D F0 Λ).2.2 n₁ hn₁ n₂ hn₂, ?_⟩
    refine ⟨good_move D (Tn u') F0 Λ Z hx₁ hn₂, ?_, h₃⟩
    have h₄ : pWf D (act D n₂ (act D n₁ (F'.fl.e, F'.fl.z))) ∈ Wf := h₂ ▸ h₁
    exact h₄
  · exact ⟨∅, Set.finite_empty, fun F' hF' => (hne ⟨F', hF'⟩).elim⟩

theorem fin0 (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (hR : RowsOf u F0 what₂) (Z : MatZ D)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ ∈ what₂) : cntE (Tn u') F0 Λ Z ≠ ⊤ := by
  obtain ⟨K, hK, hKrep⟩ := reps D u u' F0 what₂ hR Z Λ hΛ
  have hgrp := unipotent_integral_isGroup D F0 Λ
  let g : ((Fin D.R.rS → (VS D).V) × (VS D).V) → Set (LFlag (VS D) D.R.rS (Tn u')) :=
    fun k => {F'' | F'' ∈ EZ (Tn u') F0 Λ Z ∧
      ∃ n ∈ N0 F0 Λ, ((fun a => n (F''.fl.e a)), n F''.fl.z) = k}
  have hsub : {O | ∃ F' ∈ EZ (Tn u') F0 Λ Z,
      O = {F'' | F'' ∈ EZ (Tn u') F0 Λ Z ∧ NilradicalFlagMoved F0 Λ F' F''}} ⊆ g '' K := by
    rintro O ⟨F', hF', rfl⟩
    obtain ⟨n, hn, hk⟩ := hKrep F' hF'
    refine ⟨_, hk, ?_⟩
    ext F''
    simp only [g, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hF'', m, hm, hme⟩
      refine ⟨hF'', n.trans m.symm, hgrp.2.2 n hn _ (hgrp.2.1 m hm), fun a => ?_, ?_⟩
      · have h := congrFun (congrArg Prod.fst hme) a
        simp only at h
        simp [← h]
      · have h := congrArg Prod.snd hme
        simp only at h
        simp [← h]
    · rintro ⟨hF'', m, hm, he, hz⟩
      refine ⟨hF'', m.symm.trans n, hgrp.2.2 _ (hgrp.2.1 m hm) n hn, ?_⟩
      ext a <;> simp [← he, ← hz]
  simp only [cntE]
  exact ((hK.image g).subset hsub).encard_lt_top.ne

theorem finR (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (hR : IsRowReps D F0 what₂) (Z : MatZ D)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ ∈ what₂) : cntE (Tn u') F0 Λ Z ≠ ⊤ := by
  obtain ⟨F1, he1, hz1⟩ := Formalism.MainNotions.S.Inh.tie_flagG_nonempty D u
  have hT : Tn u ≠ 0 := by exact_mod_cast (Formalism.MainNotions.BridgeLemma.tie_Tu_pos D u).ne'
  obtain ⟨β, hβ, hβe, hβz⟩ := Formalism.L2.SG.Pf.WittFlags.flag_witt hT rfl F0 F1
  have hrows := Formalism.L2.SG.Pf.WittFlags.RowRepsIso_holds D β hβ F0 what₂ hR
  have hmem : Formalism.HermitianLatticesTheory.gmap β Λ ∈ what₂.image (Formalism.HermitianLatticesTheory.gmap β) := Finset.mem_image_of_mem _ hΛ
  have hRo : RowsOf u (Formalism.L2.SG.Saturated.mapFlag β hβ F0) (what₂.image (Formalism.HermitianLatticesTheory.gmap β)) := by
    refine ⟨?_, ?_, hrows, ⟨_, hmem⟩⟩
    · rw [← he1]
      funext a
      exact hβe a
    · rw [← hz1]
      exact hβz
  have h := fin0 D u u' _ _ hRo Z _ hmem
  rwa [Formalism.L2.SG.Pf.Cnt.counting_iso_inverse D β hβ (Tn u') F0 Λ Z] at h

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem orbitFinite_holds : Formalism.L2.SG.Pf.ZsVolOrb.OrbFinE M δ u u' F0 what₂ := by
  intro γ w F' L U hH
  have hfin := finR D u u' F0 what₂ hH.2.2.1 (ZhatL (lf D F0) F') γ.lam γ.mem
  unfold cntE at hfin
  refine (Set.encard_ne_top_iff.mp hfin).subset ?_
  rintro O ⟨F'', hF'', _, rfl⟩
  exact ⟨F'', hF'', rfl⟩

end Formalism.L2.SG.Pf.ZsVolFin

end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open CohCut

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

def CohLp : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
    CohHyp Zd γ Z F'₂ φ' →
    {p | ⇑(φ' p) '' (locH Zd p).Lset (lattice₂ D Zd.M p γ.lam) (tLoc Zd p γ).f' ≠
      (locH Zd p).Lset (lattice₂ D Zd.M p γ.lam) (locF' Zd p F'₂)}.Finite

def CohIota : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
    CohHyp Zd γ Z F'₂ φ' →
    {p | ¬ ∀ g, (Zd.M p).split = some g →
      Prod.map ⇑(φ' p) ⇑(LinearEquiv.refl (D.s.atP p).Ep ((locH Zd p).Wb (tLoc Zd p γ).f)) ''
          (locH Zd p).iotaGraph g (tLoc Zd p γ) =
        (locH Zd p).iotaGraph g (t2 Zd p γ F'₂ (lattice₂ D Zd.M p γ.lam))}.Finite

variable {u u' F0 what₂}

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqAna

namespace Formalism.L2.SG.Pf.MainEqVanish

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def FormGC : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ ν, Pinned X u u ν → ∀ t ∈ (Y.tO u u).genSet, (Y.tO u u).vec t ≠ 0 →
        (∃ w : Point D.host.E (D.R.rS + 1), toPts w = ptPN t ∧ ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u w g) ∧
        ∀ w : Point D.host.E (D.R.rS + 1), toPts w = ptPN t → (∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u w g) →
          ∃ (c : ℂ) (A : X.Vpi u →L[ℂ] X.Vpi u) (B : X.Vpi u →L[ℂ] X.Vpi u),
            OOt t = c • A.comp ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
              OO (ν (Formalism.L2.SG.RealObj.gamW X u u w)) Set.univ (X.Wu u) (X.Wu u)
                (Formalism.L2.SG.RealObj.gamW X u u w)).comp B)

theorem stepTermVanishG_of_form (h : FormGC) : StepTermVanishG := by
  intro Cg cb Cw cT CT C0
  obtain ⟨a₀, b₀, h2⟩ := h Cg cb Cw cT CT C0
  refine ⟨a₀, b₀, fun C' Cl e1 e2 D large₂ X Y u hc ν hν t ht hJ => ?_⟩
  by_contra hv
  obtain ⟨⟨w, hw, hrep⟩, hform⟩ := h2 C' Cl e1 e2 D large₂ X Y u hc ν hν t ht hv
  have hex : ∃ w' : Point D.host.E (D.R.rS + 1), toPts w' = ptPN t ∧ ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u w' g :=
    ⟨w, hw, hrep⟩
  unfold J2of at hJ
  rw [dite_eq_left hex] at hJ
  have hJw : Jw Y u u ν hex.choose = 0 :=
    Formalism.L2.SG.NGVanish.hsEmb_eq_zero _ (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hJ))
  obtain ⟨c, A, B, hO⟩ := hform hex.choose hex.choose_spec.1 hex.choose_spec.2
  have key : ∀ (k χ c : ℂ) (A : X.Vpi u →L[ℂ] X.Vpi u) (Z : X.Vpi u →L[ℂ] X.Vpi u)
      (B : X.Vpi u →L[ℂ] X.Vpi u), k • Z = 0 → k • (χ • (c • A.comp (Z.comp B))) = 0 := by
    intro k χ c A Z B hZ
    have hy : ∀ y, k • Z y = 0 := fun y => by simpa using congrArg (fun T => T y) hZ
    ext x
    simp only [smul_apply, ContinuousLinearMap.comp_apply, zero_apply]
    rw [smul_comm k χ, smul_comm k c, ← map_smul A k, hy]
    simp
  have hamp : ampN (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) t = 0 := by
    unfold ampN
    rw [hO]
    unfold Jw at hJw
    exact key _ _ _ _ _ _ hJw
  apply hv
  show vec (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) t = 0
  unfold vec
  rw [hamp]
  simp
  rfl

end Formalism.L2.SG.Pf.MainEqVanish
end
end
