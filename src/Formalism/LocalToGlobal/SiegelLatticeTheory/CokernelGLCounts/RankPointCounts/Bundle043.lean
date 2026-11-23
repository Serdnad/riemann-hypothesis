module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexBCongruence
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.SpanPerpZero
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle010
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle040
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SupportLoc
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SmoothBigCellSectionsExist
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
import Formalism.PeriodIntegrals.Bundle030
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.IsLoUniConjTranspose
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle027

@[expose] public section

section

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolKey

open Formalism.L2.SG.Pf.StabilizerIndexVolumes Matrix

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ} {T T' : E}

theorem act_inv (f : Fin (r + 1) → S.V) (s : S.V ≃ₗ[E] S.V) (P : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hP : P * P⁻¹ = 1) (hs : ∀ b, s (f b) = ∑ c, P c b • f c) (b : Fin (r + 1)) :
    s (∑ c, P⁻¹ c b • f c) = f b := by

  simp only [map_sum, map_smul, hs, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have h1 : ∀ d, ∑ c, P⁻¹ c b * P d c = (P * P⁻¹) d b := fun d => by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  simp only [h1, hP, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

theorem up_inv_mul {P : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hP : Formalism.MainNotions.S.IsUpUni P) : P * P⁻¹ = 1 := by
  have htri : P.BlockTriangular id := fun i j hij => (hP i j).1 hij
  have hdet : P.det = 1 := by
    rw [Matrix.det_of_upperTriangular htri]
    exact Finset.prod_eq_one fun i _ => (hP i i).2 rfl
  exact Matrix.mul_nonsing_inv P (by rw [hdet]; exact isUnit_one)

theorem eq_sL (F : Formalism.MainNotions.S.FlagG S r T) (F' : Formalism.MainNotions.S.FlagG S r T') (hG : IsUnit (gramOf (gg F F')).det)
    (s : S.V ≃ₗ[E] S.V) (hs : ∀ x y, S.hT (s x) (s y) = S.hT x y)
    (P Q : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hP : Formalism.MainNotions.S.IsUpUni P) (hQ : Formalism.MainNotions.S.IsUpUni Q)
    (hsf : ∀ b, s (F.fvec b) = ∑ c, P c b • F.fvec c) (hsf' : ∀ b, s (F'.fvec b) = ∑ c, Q c b • F'.fvec c)
    (hsX : ∀ x, (∀ i, S.hT (F.e i) x = 0) → s x - x ∈ Submodule.span E (Set.range F.e)) (x : S.V) :
    s x = sL (gg F F') (UU P Q) x := by
  classical
  have hframe : ∀ m, s (gg F F' m) = sL (gg F F') (UU P Q) (gg F F' m) := by
    intro m
    cases m with
    | inl b =>
      show s (F.fvec b) = sL (gg F F') (UU P Q) (F.fvec b)
      rw [hsf, sL_frame (F := F) (F' := F') hG P Q b]
    | inr b =>
      show s (F'.fvec b) = sL (gg F F') (UU P Q) (F'.fvec b)
      rw [hsf', sL_frame' (F := F) (F' := F') hG P Q b]
  have hy : ∀ l, S.hT (gg F F' l) (x - ∑ m, cOf (gg F F') x m • gg F F' m) = 0 := by
    intro l
    have h1 := congrFun (gram_cOf (gg F F') hG x) l

    rw [map_sub, map_sum, ← h1]
    simp only [map_smul, smul_eq_mul, Matrix.mulVec, dotProduct, gramOf]
    rw [sub_eq_zero]
    exact Finset.sum_congr rfl fun m _ => mul_comm _ _
  have hspan0 : ∀ w ∈ Submodule.span E (Set.range (gg F F')),
      S.hT w (x - ∑ m, cOf (gg F F') x m • gg F F' m) = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨l, rfl⟩ := hv
      exact hy l
    | zero => rw [map_zero, LinearMap.zero_apply]
    | add a b _ _ ha hb => rw [map_add (f := _), LinearMap.add_apply, ha, hb, add_zero]
    | smul a v _ hv => rw [map_smulₛₗ, LinearMap.smul_apply, hv, smul_zero]
  have hpre : ∀ l, ∃ w ∈ Submodule.span E (Set.range (gg F F')), s w = gg F F' l := by
    intro l
    cases l with
    | inl b =>
      refine ⟨∑ c, P⁻¹ c b • F.fvec c, Submodule.sum_mem _ fun c _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl c, rfl⟩), ?_⟩
      exact act_inv F.fvec s P (up_inv_mul hP) hsf b
    | inr b =>
      refine ⟨∑ c, Q⁻¹ c b • F'.fvec c, Submodule.sum_mem _ fun c _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr c, rfl⟩), ?_⟩
      exact act_inv F'.fvec s Q (up_inv_mul hQ) hsf' b
  have hsy : s (x - ∑ m, cOf (gg F F') x m • gg F F' m) = x - ∑ m, cOf (gg F F') x m • gg F F' m := by
    have hy' : ∀ i, S.hT (F.e i) (x - ∑ m, cOf (gg F F') x m • gg F F' m) = 0 := by
      intro i
      have h2 := hy (Sum.inl i.castSucc)
      simpa [gg, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc] using h2
    have hmem := hsX _ hy'
    have hdspan : s (x - ∑ m, cOf (gg F F') x m • gg F F' m) - (x - ∑ m, cOf (gg F F') x m • gg F F' m) ∈
        Submodule.span E (Set.range (gg F F')) := by
      refine Submodule.span_mono ?_ hmem
      rintro _ ⟨i, rfl⟩
      exact ⟨Sum.inl i.castSucc, by simp [gg, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc]⟩
    have hdperp : ∀ l, S.hT (gg F F' l)
        (s (x - ∑ m, cOf (gg F F') x m • gg F F' m) - (x - ∑ m, cOf (gg F F') x m • gg F F' m)) = 0 := by
      intro l
      obtain ⟨w, hw, hwl⟩ := hpre l
      rw [map_sub, hy l, sub_zero, ← hwl, hs, hspan0 w hw]
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hdspan
    have hc0 : cOf (gg F F') (s (x - ∑ m, cOf (gg F F') x m • gg F F' m) -
        (x - ∑ m, cOf (gg F F') x m • gg F F' m)) = 0 := by
      rw [cOf_eq]
      have hz : (fun l => S.hT (gg F F' l) (s (x - ∑ m, cOf (gg F F') x m • gg F F' m) -
          (x - ∑ m, cOf (gg F F') x m • gg F F' m))) = 0 := funext hdperp
      rw [hz, Matrix.mulVec_zero]
    have hca : cOf (gg F F') (∑ m, a m • gg F F' m) = a := by
      have h3 := cOf_comb (gg F F') hG 0 a
      rw [zero_add] at h3
      rw [h3]
      have h4 := cOf_smul (gg F F') 0 0
      rw [zero_smul, zero_smul] at h4
      rw [h4, zero_add]
    rw [ha] at hca
    rw [hc0] at hca
    rw [← sub_eq_zero, ← ha, ← hca]
    simp
  have hx : x = (x - ∑ m, cOf (gg F F') x m • gg F F' m) + ∑ m, cOf (gg F F') x m • gg F F' m := by
    rw [sub_add_cancel]

  rw [hx, map_add (f := _), map_add (f := _), map_sum, map_sum, hsy, sL_perp (F := F) (F' := F') hG _ hy]
  congr 1
  exact Finset.sum_congr rfl fun m _ => by rw [map_smul, map_smul, hframe m]

theorem nlam_of_frames (F : Formalism.MainNotions.S.FlagG S r T) (F' : Formalism.MainNotions.S.FlagG S r T') (hG : IsUnit (gramOf (gg F F')).det)
    (hZu : IsUnit (Formalism.MainNotions.S.Zhat F F').det)
    (s : S.V ≃ₗ[E] S.V) (hs : ∀ x y, S.hT (s x) (s y) = S.hT x y)
    (P Q : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hP : Formalism.MainNotions.S.IsUpUni P) (hQ : Formalism.MainNotions.S.IsUpUni Q)
    (hsf : ∀ b, s (F.fvec b) = ∑ c, P c b • F.fvec c) (hsf' : ∀ b, s (F'.fvec b) = ∑ c, Q c b • F'.fvec c)
    (hsX : ∀ x, (∀ i, S.hT (F.e i) x = 0) → s x - x ∈ Submodule.span E (Set.range F.e)) :
    (∀ j, ∀ x ∈ F'.Xa (j + 1), s x - x ∈ F'.Xa j) ∧
      (∀ x, (∀ i, S.hT (F'.e i) x = 0) → s x - x ∈ Submodule.span E (Set.range F'.e)) := by
  have hQd : Q.det = 1 := by
    have htri : Q.BlockTriangular id := fun i j hij => (hQ i j).1 hij
    rw [Matrix.det_of_upperTriangular htri]
    exact Finset.prod_eq_one fun i _ => (hQ i i).2 rfl
  have hmat : P.conjTranspose * Formalism.MainNotions.S.Zhat F F' * Q = Formalism.MainNotions.S.Zhat F F' := by
    ext a b
    have h := hs (F.fvec a) (F'.fvec b)
    rw [hsf, hsf'] at h

    simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
    Finset.mul_sum] at h
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Formalism.MainNotions.S.Zhat, Formalism.MainNotions.S.brS]
    rw [← h, Finset.sum_comm]
    simp only [Finset.sum_mul, RingHom.id_apply, starRingEnd_apply]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => by ring
  have hZH : IsUnit (Formalism.MainNotions.S.Zhat F F').conjTranspose.det := by
    rw [Matrix.det_conjTranspose]
    exact hZu.star
  have hQH : IsUnit Q.conjTranspose.det := by
    rw [Matrix.det_conjTranspose, hQd, star_one]
    exact isUnit_one
  have h2 : Q.conjTranspose * (Formalism.MainNotions.S.Zhat F F').conjTranspose * P = (Formalism.MainNotions.S.Zhat F F').conjTranspose := by
    have h3 := congrArg Matrix.conjTranspose hmat
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      ← Matrix.mul_assoc] at h3
  have e1 : (Formalism.MainNotions.S.Zhat F F').conjTranspose * P = (Q.conjTranspose)⁻¹ * (Formalism.MainNotions.S.Zhat F F').conjTranspose := by
    conv_rhs => rw [← h2]
    rw [Matrix.mul_assoc Q.conjTranspose, ← Matrix.mul_assoc (Q.conjTranspose)⁻¹, Matrix.nonsing_inv_mul _ hQH,
      Matrix.one_mul]
  have hrel : P = ((Formalism.MainNotions.S.Zhat F F').conjTranspose)⁻¹ * (Q.conjTranspose)⁻¹ * (Formalism.MainNotions.S.Zhat F F').conjTranspose := by
    rw [Matrix.mul_assoc, ← e1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hZH, Matrix.one_mul]
  have hQl : Formalism.MainNotions.S.IsLoUni Q.conjTranspose := fun i j =>
    ⟨fun h => by simp [Matrix.conjTranspose_apply, (hQ j i).1 h],
     fun h => by subst h; simp [Matrix.conjTranspose_apply, (hQ i i).2 rfl]⟩
  refine ⟨fun j x hx => ?_, fun x hx => ?_⟩
  · rw [eq_sL F F' hG s hs P Q hP hQ hsf hsf' hsX x]
    exact sL_Xa' (F := F) (F' := F') hG hQ j x hx
  · rw [eq_sL F F' hG s hs P Q hP hQ hsf hsf' hsX x]
    exact sL_orth' (F := F) (F' := F') hG hQ hZH hrel (loUni_inv hQl) x hx

end Formalism.L2.SG.Pf.ZsVolKey

end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.NGCut.SplitEmbedding

namespace Formalism.L2.SG.NGCut.StabilizerCovolume

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ht {D : D7} {w : Point D.host.E (D.R.rS + 1)} (p : Formalism.L2.SG.RealObj.FreeE w) : ℕ := p.1.2.val - p.1.1.val

def ChartC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (t : TT Y u u'), t.relevant → t.G ≠ 0 →
    ∀ w, t.toTerm.atPt w → ∀ (γw s s' : X.B.I.Ginf),
      Formalism.L2.SG.RealObj.IsPtRep X u u' w γw → s ∈ X.SinfU u → s' ∈ X.SinfU u' → t.pt.1 = s * γw * s'⁻¹ →
      ∃ BX : Formalism.L2.SG.RealObj.FreeE w → (Formalism.L2.SG.RealObj.FreeE w → ℂ) → (Formalism.L2.SG.RealObj.FreeE w → ℂ) → ℂ,
        (∀ p, Measurable (fun z : (Formalism.L2.SG.RealObj.FreeE w → ℂ) × (Formalism.L2.SG.RealObj.FreeE w → ℂ) => BX p z.1 z.2)) ∧
        (∀ p (x x' y y' : Formalism.L2.SG.RealObj.FreeE w → ℂ), (∀ q, ht q < ht p → x q = x' q ∧ y q = y' q) →
          BX p x y = BX p x' y') ∧
        (∀ p (x : Formalism.L2.SG.RealObj.FreeE w → ℂ), BX p x 0 = 0) ∧
        Measurable (Formalism.L2.SG.RealObj.stCoord X u' w γw) ∧
        MeasurableSet (Formalism.L2.SG.RealObj.StInf X u u' γw) ∧
        Set.InjOn (Formalism.L2.SG.RealObj.stCoord X u' w γw) (Formalism.L2.SG.RealObj.StInf X u u' γw) ∧
        (∀ x, ∃ z ∈ Formalism.L2.SG.RealObj.StInf X u u' γw, Formalism.L2.SG.RealObj.stCoord X u' w γw z = x) ∧
        (∀ z₁ ∈ Formalism.L2.SG.RealObj.StInf X u u' γw, ∀ z₂ ∈ Formalism.L2.SG.RealObj.StInf X u u' γw,
          z₁ * z₂ ∈ Formalism.L2.SG.RealObj.StInf X u u' γw ∧
          Formalism.L2.SG.RealObj.stCoord X u' w γw (z₁ * z₂) =
            lawX BX (Formalism.L2.SG.RealObj.stCoord X u' w γw z₁) (Formalism.L2.SG.RealObj.stCoord X u' w γw z₂)) ∧
        (∀ r ∈ Formalism.L2.SG.TermOp.Vanish.Rset t, s⁻¹ * r * s ∈ Formalism.L2.SG.RealObj.StInf X u u' γw)

end Formalism.L2.SG.NGCut.StabilizerCovolume
end
end

section

noncomputable section

open scoped Classical Matrix
open ValuativeRel

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section OneDir

variable {D : D7} (Zd : LocDat D)

theorem typed_split (p : PlF D) {g : Formalism.MainNotions.S.Loc.SplitG (Zd.M p).L} (hs : (Zd.M p).split = some g) :
    ∃ sg, (D.s.atP p).split = some sg ∧ g.e = sg.e ∧ g.q = sg.q := by
  have h := (Zd.agree p).2.2.2.2.2
  rw [hs] at h
  cases hsg : (D.s.atP p).split with
  | none => rw [hsg] at h; exact h.elim
  | some sg => rw [hsg] at h; exact ⟨sg, rfl, h.1, h.2⟩

theorem gS_mem_of_split (p : PlF D) {sg} (hsg : (D.s.atP p).split = some sg) :
    ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal →
      ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := fun P hP =>
  (Formalism.L2.SG.Pf.BBTie.bt_g_mem_iff p P hP).2 (by rw [← D.s_split p, hsg]; rfl)

end OneDir

end Formalism.L2.SG.Pf.FibQ
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.LocOrbSumPf

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups MeasureTheory
open Formalism.L2.SG.LsDatumB
open Classical

section ShiftPf

variable {D : Formalism.BasicNotions.D7}

theorem blkMod_eq (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) :
    ∀ a s t x y, 1 ≤ a → a - 1 ≤ x → a - 1 ≤ y → x + y + 1 = 2 * (a - 1) + s → x ≤ D.R.rS → y ≤ D.R.rS →
      ¬ (x = D.R.rS ∧ y = D.R.rS) →
        blkMod δ T T' p a s t = Formalism.L2.SG.Pf.rho δ p x * Formalism.L2.SG.Pf.rho δ p y * Formalism.L2.SG.Pf.kap p *
          (D.s.atP p).ιE t := by
  intro a s t x y h1 h2 h3 h4 h5 h6 h7
  rw [← Formalism.L2.SG.Pf.blkTop_eq δ T T' p a s t x y h1 h2 h3 h4 h5 h6 h7]
  unfold blkTop
  rw [if_neg]
  rintro ⟨hs, rfl⟩
  omega

theorem modMat_off (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1))
    (x y : Fin (D.R.rS + 1)) (hn : ¬ (x = Fin.last D.R.rS ∧ y = Fin.last D.R.rS)) :
    modMat δ T T' p w x y = Formalism.L2.SG.Pf.rho δ p x * Formalism.L2.SG.Pf.rho δ p y * Formalism.L2.SG.Pf.kap p *
      (D.s.atP p).ιE (ptMat w x y) := by
  have hn' : ¬ ((x : ℕ) = D.R.rS ∧ (y : ℕ) = D.R.rS) := fun h =>
    hn ⟨Fin.ext (by rw [Fin.val_last]; exact h.1), Fin.ext (by rw [Fin.val_last]; exact h.2)⟩
  have e := Formalism.L2.SG.Pf.ptEntry_scale (D.s.atP p).ιE (blkMod δ T T' p) (Formalism.L2.SG.Pf.rho δ p)
    (Formalism.L2.SG.Pf.kap p) D.R.rS (blkMod_eq δ T T' p) w.1 1
    x y le_rfl (by have := x.isLt; omega) (by have := y.isLt; omega) (by simpa using hn')
  simp only [Nat.sub_self, zero_add] at e
  show ptEntry (mapBlocks (blkMod δ T T' p) 1 w.1) x y = _
  rw [e]
  rfl

theorem modMat_last (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1))
    (l0 : List (D.host.E × ℕ)) (t : D.host.E) (hb : w.1 = l0 ++ [(t, 1)]) (hs : (l0.map Prod.snd).sum = D.R.rS) :
    modMat δ T T' p w (Fin.last _) (Fin.last _) = blkMod δ T T' p (D.R.rS + 1) 1 t := by
  show ptEntry (mapBlocks (blkMod δ T T' p) 1 w.1) D.R.rS D.R.rS = _
  have hs' : ((mapBlocks (blkMod δ T T' p) 1 l0).map Prod.snd).sum = D.R.rS := by
    rw [Formalism.L2.SG.Pf.mapBlocks_snd, hs]
  rw [hb, Formalism.L2.SG.Pf.mapBlocks_append, Formalism.L2.SG.Pf.ptEntry_append_ge _ _ _ _ hs'.le, if_pos hs'.le, hs',
    Nat.sub_self, hs, add_comm]
  simp [mapBlocks, ptEntry]

theorem corner_zero {B : Type} [Zero B] (f : ℕ → ℕ → D.host.E → B) (w : Point D.host.E (D.R.rS + 1))
    (l0 : List (D.host.E × ℕ)) (t : D.host.E) (s : ℕ) (hb : w.1 = l0 ++ [(t, s)])
    (hs : (l0.map Prod.snd).sum + s = D.R.rS + 1) (h2 : 2 ≤ s) :
    ptEntry (mapBlocks f 1 w.1) D.R.rS D.R.rS = 0 := by
  have hs' : ((mapBlocks f 1 l0).map Prod.snd).sum = (l0.map Prod.snd).sum := by
    rw [Formalism.L2.SG.Pf.mapBlocks_snd]
  have hle : ((mapBlocks f 1 l0).map Prod.snd).sum ≤ D.R.rS := by rw [hs']; omega
  rw [hb, Formalism.L2.SG.Pf.mapBlocks_append, Formalism.L2.SG.Pf.ptEntry_append_ge _ _ _ _ hle, if_pos hle, hs']
  simp only [mapBlocks, ptEntry]
  split_ifs <;> first | rfl | omega

theorem last_big (w : Point D.host.E (D.R.rS + 1)) (h0 : Dmin w D.R.rS = 0) :
    ∃ l0 t s, w.1 = l0 ++ [(t, s)] ∧ (l0.map Prod.snd).sum + s = D.R.rS + 1 ∧ 2 ≤ s := by
  have hne : w.1 ≠ [] := by
    intro h
    have := w.2.2
    rw [h] at this
    simp at this
  obtain ⟨l0, b, hb⟩ : ∃ l0 b, w.1 = l0 ++ [b] :=
    ⟨w.1.dropLast, w.1.getLast hne, (List.dropLast_append_getLast hne).symm⟩
  obtain ⟨t, s⟩ := b
  have hmem := w.2.1 (t, s) (by rw [hb]; simp)
  have hsum : (l0.map Prod.snd).sum + s = D.R.rS + 1 := by
    have := w.2.2
    rw [hb] at this
    simpa using this
  refine ⟨l0, t, s, hb, hsum, ?_⟩
  by_contra hlt
  have hs1 : s = 1 := by have := hmem.2; omega
  subst hs1
  have := Formalism.L2.SG.Pf.dmin_snoc w l0 t hb (by omega)
  rw [h0, zero_mul] at this
  exact Formalism.MainNotions.BridgeLemma.Dmin_top_ne w this

theorem modShift_holds (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) :
    ModShift δ T T' p w := by
  intro a ha
  ext x y
  rw [Matrix.add_apply]
  by_cases hc : x = Fin.last D.R.rS ∧ y = Fin.last D.R.rS
  · obtain ⟨rfl, rfl⟩ := hc
    have hsh : shM δ T T' p w (Fin.last _) (Fin.last _) = cornerSh δ T T' p w := by simp [shM]
    rw [hsh]
    by_cases h0 : Dmin w D.R.rS = 0
    · have hc0 : cornerSh δ T T' p w = 0 := by unfold cornerSh; rw [if_pos h0]
      rw [hc0, add_zero]
      obtain ⟨l0, t, s, hb, hs, h2⟩ := last_big w h0
      have e1 := corner_zero (blkTop δ T T' p) w l0 t s hb hs h2
      have e2 := corner_zero (blkMod δ T T' p) w l0 t s hb hs h2
      show Loc.ptEntryL a.blocks D.R.rS D.R.rS = ptEntry (mapBlocks (blkMod δ T T' p) 1 w.1) D.R.rS D.R.rS
      rw [Formalism.L2.SG.Pf.ptEntryL_eq, Formalism.L2.SG.Pf.modPt_blocks δ T T' p w a ha, e1, e2]
    · obtain ⟨l0, t, hb, hs⟩ := Formalism.L2.SG.Pf.last_one w h0
      rw [Formalism.L2.SG.Pf.amat_last δ T T' p w a ha l0 t hb hs, modMat_last δ T T' p w l0 t hb hs]
      unfold cornerSh
      rw [if_neg h0, Formalism.L2.SG.Pf.zeta_snoc w h0 l0 t hb hs]
      unfold blkTop
      rw [if_pos ⟨by omega, rfl⟩]
  · rw [Formalism.L2.SG.Pf.amat_eq δ T T' p w a ha x y hc, modMat_off δ T T' p w x y hc]
    have : shM δ T T' p w x y = 0 := by simp only [shM, Matrix.of_apply]; rw [if_neg hc]
    rw [this, add_zero]

end ShiftPf

end Formalism.L2.SG.Pf.LocOrbSumPf
end
end
