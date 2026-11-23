module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle012
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle206
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle107
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle310
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatsDiscStable
public import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle311
public import Formalism.LocalToGlobal.Divisibility.DivisionCompatibleToSub2Indef2
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle312
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle313
public import Formalism.PeriodIntegrals.Bundle004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarDensityConjUnitaryHermitianGroups
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianLattices.HermitianLatticesProofs.UnimodularSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOp
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle026
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle002

@[expose] public section

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.FunIdx

section Gen

variable {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V]
  [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

theorem exists_retraction (M0 L : Submodule (𝓞 E) V) (hL : L.FG) (h : IsPrimitiveSub M0 L) :
    ∃ r : L →ₗ[𝓞 E] M0, ∀ x : M0, r ⟨x, h.1 x.2⟩ = x := by
  exact _root_.GlobalTheory.ProjectiveRetraction.exists_retraction M0 L hL h

theorem exists_extend_fun (L : Submodule (𝓞 E) V) (hL : Submodule.span E (L : Set V) = ⊤)
    (ψ : L →ₗ[𝓞 E] 𝓞 E) : ∃ φ : V →ₗ[E] E, ∀ x : L, φ x = (ψ x : E) := by
  haveI : IsLocalizedModule (nonZeroDivisors (𝓞 E)) L.subtype := by
    refine ⟨?_, ?_, ?_⟩
    · intro a
      rw [Module.End.isUnit_iff]
      have ha0 : ((a : 𝓞 E) : E) ≠ 0 := by
        have := nonZeroDivisors.ne_zero a.2
        exact_mod_cast this
      have e : ⇑(algebraMap (𝓞 E) (Module.End (𝓞 E) V) a) = fun v => ((a : 𝓞 E) : E) • v := by
        funext v
        exact (algebraMap_smul E (a : 𝓞 E) v).symm
      rw [e]
      exact MulAction.bijective (Units.mk0 _ ha0)
    · intro y
      have hy : y ∈ Submodule.span E (L : Set V) := hL ▸ Submodule.mem_top
      obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E _ y hy
      rw [Submodule.span_eq] at ht
      exact ⟨(⟨_, ht⟩, t), rfl⟩
    · intro x y hxy
      exact ⟨1, by rw [Subtype.ext hxy]⟩
  let g : L →ₗ[𝓞 E] E := Algebra.linearMap (𝓞 E) E ∘ₗ ψ
  have hu : ∀ a : nonZeroDivisors (𝓞 E), IsUnit (algebraMap (𝓞 E) (Module.End (𝓞 E) E) a) :=
    fun a => IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 E)) (Algebra.linearMap (𝓞 E) E) a
  refine ⟨(IsLocalizedModule.lift (nonZeroDivisors (𝓞 E)) L.subtype g hu).extendScalarsOfIsLocalization
    (nonZeroDivisors (𝓞 E)) E, fun x => ?_⟩
  exact IsLocalizedModule.lift_apply (nonZeroDivisors (𝓞 E)) L.subtype g hu x

end Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem exists_vec (S : HSpace E) (φ : S.V →ₗ[E] E) : ∃ w, ∀ x, φ x = S.hT w x := by
  let G : S.V →ₗ[E] (Fin S.rank → E) := LinearMap.pi fun i => S.hT (S.frame i)
  have hG : Function.Injective G := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply S.nondeg.2 y
    intro x
    have : S.hT.flip y = 0 := S.frame.ext fun i => congrFun hy i
    exact LinearMap.congr_fun this x
  have hs : Function.Surjective G :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [S.rank_eq])).1 hG
  obtain ⟨w, hw⟩ := hs fun i => star (φ (S.frame i))
  refine ⟨w, fun x => LinearMap.congr_fun (S.frame.ext fun i => ?_ : φ = S.hT w) x⟩
  have h1 : S.hT (S.frame i) w = star (φ (S.frame i)) := congrFun hw i
  have h2 : star (S.hT (S.frame i) w) = S.hT w (S.frame i) := S.herm.eq _ _
  rw [← h2, h1, star_star]

theorem span_eq_top_of_unimodular {S : HSpace E} (L : Submodule (𝓞 E) S.V)
    (hL : Submodule.IsLattice E L)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT L) :
    Submodule.span E (L : Set S.V) = ⊤ := by
  exact Formalism.HermitianLatticesTheory.IsUnimodular.span_eq_top hU S.herm hL.fg


theorem exists_dual_vec (S : HSpace E) (M0 L : Submodule (𝓞 E) S.V) (hL : Submodule.IsFullLattice E L)
    (h : IsPrimitiveSub M0 L) (ψ : M0 →ₗ[𝓞 E] 𝓞 E) :
    ∃ w : dualInH S.hT L, ∀ x : M0, (ψ x : E) = S.hT w x := by
  obtain ⟨r, hr⟩ := exists_retraction M0 L hL.fg h
  obtain ⟨φ, hφ⟩ := exists_extend_fun L (Submodule.IsFullLattice.span_eq_top (self := hL)) (ψ ∘ₗ r)
  obtain ⟨w, hw⟩ := exists_vec S φ
  refine ⟨⟨w, ?_, ?_⟩, fun x => ?_⟩
  · refine (Submodule.mem_iInf _).2 fun y => (Submodule.mem_iInf _).2 fun hy => ?_
    change S.hT y w ∈ (1 : Submodule (𝓞 E) E)
    have h2 : star (S.hT w y) = S.hT y w := S.herm.eq _ _
    have h3 : IsIntegral ℤ (S.hT y w) := by
      rw [← h2, ← hw, hφ ⟨y, hy⟩]
      exact (RingOfIntegers.isIntegral_coe _).map (starRingEnd E).toIntAlgHom
    exact Submodule.mem_one.2 ⟨⟨_, h3⟩, rfl⟩
  · change w ∈ Submodule.span E (L : Set S.V)
    rw [(Submodule.IsFullLattice.span_eq_top (self := hL))]; trivial
  · have := hφ ⟨x, h.1 x.2⟩
    rw [LinearMap.comp_apply, hr] at this
    rw [← this, hw]

theorem exists_reps (S : HSpace E) (M0 L : Submodule (𝓞 E) S.V) (hL : Submodule.IsFullLattice E L)
    (h : IsPrimitiveSub M0 L)
    (hfin : 1 ≤ Nat.card (dualInH S.hT L ⧸ L.comap (dualInH S.hT L).subtype)) :
    ∃ reps : Finset (M0 →ₗ[𝓞 E] 𝓞 E),
      reps.card ≤ Nat.card (dualInH S.hT L ⧸ L.comap (dualInH S.hT L).subtype) ∧
      ∀ ψ : M0 →ₗ[𝓞 E] 𝓞 E, ∃ ψ₀ ∈ reps, ∃ v ∈ L, ∀ x : M0, ((ψ x - ψ₀ x : 𝓞 E) : E) = S.hT v x := by
  choose w hw using exists_dual_vec S M0 L hL h
  haveI : Finite (dualInH S.hT L ⧸ L.comap (dualInH S.hT L).subtype) :=
    Nat.finite_of_card_ne_zero (by omega)
  letI := Fintype.ofFinite (dualInH S.hT L ⧸ L.comap (dualInH S.hT L).subtype)
  let g : (M0 →ₗ[𝓞 E] 𝓞 E) → (dualInH S.hT L ⧸ L.comap (dualInH S.hT L).subtype) :=
    fun ψ => Submodule.Quotient.mk (w ψ)
  refine ⟨Finset.univ.image (Function.invFun g), ?_, fun ψ => ?_⟩
  · rw [Nat.card_eq_fintype_card]; exact Finset.card_image_le
  · refine ⟨Function.invFun g (g ψ), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    have h1 : g ψ = g (Function.invFun g (g ψ)) := (Function.invFun_eq ⟨ψ, rfl⟩).symm
    have h2 := (Submodule.Quotient.eq _).1 h1
    refine ⟨_, h2, fun x => ?_⟩
    rw [Submodule.subtype_apply, Submodule.coe_sub, map_sub, LinearMap.sub_apply, ← hw, ← hw]
    push_cast
    rfl

theorem funIdx : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → ∀ M0 : LatW D, IsPrimitiveSub M0 (L0X D Λ (lf D F0)) → ∃ reps : Finset (M0 →ₗ[𝓞 D.host.E] 𝓞 D.host.E), (reps.card : ℝ) ≤ NT D u ^ 2 ∧ ∀ ψ : M0 →ₗ[𝓞 D.host.E] 𝓞 D.host.E, ∃ ψ₀ ∈ reps, ∃ v ∈ L0X D Λ (lf D F0), ∀ x : M0, ((ψ x - ψ₀ x : 𝓞 D.host.E) : D.host.E) = (D.sp.X 0).hT v x := by
  intro D u u' F0 Λ hStand hB hR M0 hM
  obtain ⟨hWH, -, hpd, hlat, hint, hdet, -⟩ := GlobalTheory.T.standardBaseFlag_complement_integralLattice D u u' F0 Λ hStand hB hR
  have hfull : Submodule.IsFullLattice D.host.E (L0X D Λ (lf D F0)) := by
    refine { toIsLattice := hlat, span_eq_top := ?_ }
    apply eq_top_iff.mpr
    intro w _
    have hΛ : Submodule.span D.host.E (Λ : Set (VS D).V) = ⊤ :=
      span_eq_top_of_unimodular Λ hR.2.1.1 hR.2.1.2.1
    have hw : D.sp.iXY 0 w ∈ orth (hS D) F0.Xplus :=
      hWH.1.le (Submodule.mem_sup_left ⟨w, rfl⟩)
    have hwX : D.sp.iXY 0 w ∈ orth (hS D) F0.X :=
      (Formalism.MainNotions.mem_orth_iff _ _).2 fun x hx =>
        (Formalism.MainNotions.mem_orth_iff _ _).1 hw x (Submodule.mem_sup_left hx)
    have hwz : (hS D).hT F0.z (D.sp.iXY 0 w) = 0 :=
      (Formalism.MainNotions.mem_orth_iff _ _).1 hw _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 D.host.E)) D.host.E Λ (D.sp.iXY 0 w) (hΛ ▸ Submodule.mem_top)
    rw [Submodule.span_eq] at ht
    have ht0 : (algebraMap (𝓞 D.host.E) D.host.E t) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors t.2
    have hmem : (t : 𝓞 D.host.E) • w ∈ L0X D Λ (lf D F0) := by
      change D.sp.iXY 0 ((t : 𝓞 D.host.E) • w) ∈ L0sub Λ (lf D F0)
      rw [← algebraMap_smul D.host.E, map_smul, algebraMap_smul]
      have hort : (t : 𝓞 D.host.E) • D.sp.iXY 0 w ∈ toO (hS D) (orth (hS D) F0.X) := by
        change (t : 𝓞 D.host.E) • D.sp.iXY 0 w ∈ (orth (hS D) F0.X).restrictScalars (𝓞 D.host.E)
        exact Submodule.smul_mem _ _ hwX
      refine ⟨⟨Submodule.mem_sup_left ⟨ht, hort⟩, hort⟩, ?_⟩
      change (hS D).hT F0.z ((t : 𝓞 D.host.E) • D.sp.iXY 0 w) = 0
      rw [← algebraMap_smul D.host.E, map_smul, hwz, smul_zero]
    have hspan : (t : 𝓞 D.host.E) • w ∈ Submodule.span D.host.E ((L0X D Λ (lf D F0)) : Set (D.sp.X 0).V) :=
      Submodule.subset_span hmem
    have hspan' : (algebraMap (𝓞 D.host.E) D.host.E t) • w ∈
        Submodule.span D.host.E ((L0X D Λ (lf D F0)) : Set (D.sp.X 0).V) := by
      rw [algebraMap_smul]
      exact hspan
    have := (Submodule.span D.host.E ((L0X D Λ (lf D F0)) : Set (D.sp.X 0).V)).smul_mem (algebraMap (𝓞 D.host.E) D.host.E t)⁻¹ hspan'
    rw [smul_smul, inv_mul_cancel₀ ht0, one_smul] at this
    exact this
  obtain ⟨h1, h2, -⟩ := GlobalTheory.LoopC.DetCard.main D _ hlat.fg hpd hint
  obtain ⟨reps, hc, hr⟩ := exists_reps (D.sp.X 0) M0 _ hfull hM h1
  refine ⟨reps, ?_, hr⟩
  rw [← hdet, ← h2]
  exact_mod_cast hc

end GlobalTheory.LoopC.FunIdx
end

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.FrameDiff

theorem dd_zpow_le (D : D7) (a : Fin D.R.rS) :
    (ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≤
      ddS D ^ (-(D.R.rS : ℤ)) := by
  have ha := a.2
  by_cases h0 : ddS D = 0
  · rw [h0, _root_.zero_zpow _ (by omega)]
    exact FractionalIdeal.zero_le _
  · have h1 : (-((D.R.rS : ℤ) - (a : ℕ))) = -(D.R.rS : ℤ) + ((a : ℕ) : ℤ) := by ring
    rw [h1, zpow_add₀ h0, zpow_natCast]
    have h2 : ddS D ^ (a : ℕ) ≤ 1 := by
      unfold ddS
      rw [← FractionalIdeal.coeIdeal_pow]
      exact FractionalIdeal.coeIdeal_le_one
    calc _ ≤ ddS D ^ (-(D.R.rS : ℤ)) * 1 := by gcongr
      _ = _ := mul_one _

theorem coords_of_mem_XS (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (y : (VS D).V)
    (hy : y ∈ XS D F0) :
    ∃ c : Fin D.R.rS → D.host.E,
      (∀ a, c a ∈ (ddS D ^ (-(D.R.rS : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ∧
      y = ∑ a, c a • F0.e a := by
  unfold XS at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, x, hx, rfl⟩ := hy
    refine ⟨Pi.single a x, fun a' => ?_, ?_⟩
    · by_cases h : a' = a
      · subst h
        rw [Pi.single_eq_same]
        exact dd_zpow_le D a' hx
      · rw [Pi.single_eq_of_ne h]
        exact FractionalIdeal.zero_mem _
    · rw [Finset.sum_eq_single a]
      · simp
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb]
      · simp
  | zero => exact ⟨0, fun _ => FractionalIdeal.zero_mem _, by simp⟩
  | add y y' _ _ h h' =>
    obtain ⟨c, hc, rfl⟩ := h
    obtain ⟨c', hc', rfl⟩ := h'
    refine ⟨c + c', fun a => ?_, by simp [add_smul, Finset.sum_add_distrib]⟩
    exact Submodule.add_mem (FractionalIdeal.coeToSubmodule _) (hc a) (hc' a)
  | smul o y _ h =>
    obtain ⟨c, hc, rfl⟩ := h
    refine ⟨o • c, fun a => ?_, by simp [Finset.smul_sum, smul_assoc]⟩
    exact Submodule.smul_mem (FractionalIdeal.coeToSubmodule _) o (hc a)

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem star_hT (x y : S.V) : star (S.hT x y) = S.hT y x := S.herm.eq x y

theorem gram_eq (F F' : FlagG S r T) (b b' : Fin (r + 1)) :
    S.hT (F.fvec b) (F.fvec b') = S.hT (F'.fvec b) (F'.fvec b') := by
  have hz : ∀ (G : FlagG S r T) a, S.hT G.z (G.e a) = 0 := fun G a => by
    rw [← star_hT, G.z_orth, star_zero]
  induction b using Fin.lastCases <;> induction b' using Fin.lastCases <;>
    simp [FlagG.fvec, F.e_iso, F'.e_iso, F.z_orth, F'.z_orth, F.z_norm, F'.z_norm, hz]

theorem mem_orth_iff (U : Submodule E S.V) (v : S.V) : v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0 := by
  simp [orth, Submodule.mem_iInf]

theorem hT_X_eq_zero (F : FlagG S r T) (v : S.V) (hv : ∀ a, S.hT (F.e a) v = 0) (x : S.V) (hx : x ∈ F.X) :
    S.hT x v = 0 := by
  unfold FlagG.X at hx
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨a, rfl⟩ := hy; exact hv a
  | zero => simp
  | add y y' _ _ h h' => simp [h, h']
  | smul c y _ h => simp [h]

theorem frame_mem (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (h : IsLift Λ F) (he : ∀ a, F.fl.e a ∈ Λ)
    (b : Fin (r + 1)) : frame F b ∈ Λ := by
  induction b using Fin.lastCases with
  | last => simpa [FlagG.fvec] using h.1
  | cast a => simpa [FlagG.fvec] using he a

end Gen

theorem mem_perpE_iff (D : D7) (P : LatW D) (w : (D.sp.X 0).V) :
    w ∈ perpE D P ↔ ∀ p ∈ P, (D.sp.X 0).hT p w = 0 := by
  simp [perpE, Submodule.mem_iInf]

theorem frame_diff : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → ∀ (P : LatW D) (φ : P →ₗ[𝓞 D.host.E] (hS D).V) (Z : GramM D), (∀ p, φ p ∈ XLam Λ (lf D F0)) → ∀ F₁ ∈ FixSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P φ, ∀ F₂ ∈ FixSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P φ, (∀ b, ∃ w, IsWcomp D P (frame F₁ b) w ∧ IsWcomp D P (frame F₂ b) w) → ∃ x : Matrix (Fin D.R.rS) (Fin (D.R.rS + 1)) D.host.E, (∀ b, frame F₂ b = frame F₁ b + ∑ a, x a b • F0.e a) ∧ (∀ a b, x a b ∈ (ddS D ^ (-(D.R.rS : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ∧ xᴴ * Z.submatrix Fin.castSucc id + (Z.submatrix Fin.castSucc id)ᴴ * x = 0 := by
  intro D u u' F0 Λ hst hb hrow P φ Z hφ F₁ h₁ F₂ h₂ hw
  obtain ⟨hW, -, hpos, -⟩ := GlobalTheory.T.standardBaseFlag_complement_integralLattice D u u' F0 Λ hst hb hrow
  obtain ⟨l₁, e₁, z₁, o₁⟩ := h₁
  obtain ⟨l₂, e₂, z₂, o₂⟩ := h₂
  have hiso : ∀ x y, (hS D).hT (D.sp.iXY 0 x) (D.sp.iXY 0 y) = (D.sp.X 0).hT x y :=
    D.sp.iXY_isom 0 (by have := D.R.two_le_m; omega)
  have hZ₁ : ∀ a b, (hS D).hT (F0.fvec a) (frame F₁ b) = Z a b := fun a b => by rw [← z₁]; rfl
  have hZ₂ : ∀ a b, (hS D).hT (F0.fvec a) (frame F₂ b) = Z a b := fun a b => by rw [← z₂]; rfl
  have hWX : ∀ (w : (D.sp.X 0).V), ∀ x ∈ F0.X, (hS D).hT (D.sp.iXY 0 w) x = 0 := by
    intro w x hx
    rw [← star_hT, hT_X_eq_zero F0 (D.sp.iXY 0 w) (fun a => ?_) x hx, star_zero]
    rw [← star_hT, hb.1, (D.sp.hyp_orthX a w).1, star_zero]
  have hd : ∀ b, frame F₂ b - frame F₁ b ∈ XS D F0 := by
    intro b
    rw [← hrow.2.2]
    refine ⟨Λ.sub_mem (frame_mem Λ F₂ l₂ e₂ b) (frame_mem Λ F₁ l₁ e₁ b), ?_⟩
    set d := frame F₂ b - frame F₁ b with hdd
    have hf : ∀ a, (hS D).hT (F0.fvec a) d = 0 := fun a => by rw [hdd, map_sub, hZ₁, hZ₂, sub_self]
    have hX : ∀ x ∈ F0.X, (hS D).hT x d = 0 :=
      hT_X_eq_zero F0 d (fun a => by simpa [FlagG.fvec] using hf a.castSucc)
    have hz : (hS D).hT F0.z d = 0 := by simpa [FlagG.fvec] using hf (Fin.last _)
    have hmem : d ∈ Wsp D ⊔ Xsp (lf D F0) := by
      rw [hW.1, mem_orth_iff]
      intro y hy
      obtain ⟨x, hx, y', hy', rfl⟩ := Submodule.mem_sup.1 hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy'
      simp [hX x hx, hz]
    obtain ⟨_, ⟨w, rfl⟩, x, hx, hwx⟩ := Submodule.mem_sup.1 hmem
    have hwd : ∀ σ, (hS D).hT (D.sp.iXY 0 σ) d = (D.sp.X 0).hT σ w := fun σ => by
      rw [← hwx, map_add (f := _), hiso, hWX σ x hx, add_zero]
    have hwP : w ∈ perpE D P := by
      rw [mem_perpE_iff]
      intro p hp
      have h1 : (hS D).hT (D.sp.iXY 0 p + φ ⟨p, hp⟩) d = 0 := by
        rw [hdd, map_sub, o₁ ⟨p, hp⟩ b, o₂ ⟨p, hp⟩ b, sub_self]
      rw [map_add (f := _), LinearMap.add_apply, hX _ (hφ ⟨p, hp⟩).2, add_zero, hwd] at h1
      exact h1
    obtain ⟨w', c₁, c₂⟩ := hw b
    have hww : (D.sp.X 0).hT w w = 0 := by
      rw [← hwd, hdd, map_sub, c₁.2 w hwP, c₂.2 w hwP, sub_self]
    have hw0 : w = 0 := by
      by_contra hne
      obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
      have := hpos τ w hne
      rw [hww] at this
      simp at this
    rw [hw0, map_zero, zero_add] at hwx
    rw [← hwx]
    exact hx
  choose c hc hcd using fun b => coords_of_mem_XS D F0 _ (hd b)
  have hfr : ∀ b, frame F₂ b = frame F₁ b + ∑ a, c b a • F0.e a := fun b => by
    rw [← hcd]; abel
  refine ⟨Matrix.of fun a b => c b a, hfr, fun a b => hc b a, ?_⟩
  refine Matrix.ext fun b b' => ?_
  have hg : (hS D).hT (frame F₂ b) (frame F₂ b') = (hS D).hT (frame F₁ b) (frame F₁ b') :=
    gram_eq F₂.fl F₁.fl b b'
  have hY : ∀ a b, (hS D).hT (F0.e a) (frame F₁ b) = Z a.castSucc b := fun a b => by
    simpa [FlagG.fvec] using hZ₁ a.castSucc b
  have hY' : ∀ a b, (hS D).hT (frame F₁ b) (F0.e a) = star (Z a.castSucc b) := fun a b => by
    rw [← hY, star_hT]
  rw [hfr b, hfr b'] at hg

  simp only [map_add (f := _), map_sum, LinearMap.add_apply, LinearMap.sum_apply, map_smul, LinearMap.map_smulₛₗ,
  LinearMap.smul_apply, hY, hY', F0.e_iso, smul_eq_mul, mul_zero, Finset.sum_const_zero, add_zero,
  starRingEnd_apply] at hg
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Matrix.submatrix_apply, id, Matrix.zero_apply]
  have : ∑ a, star (Z a.castSucc b) * c b' a = ∑ a, c b' a * star (Z a.castSucc b) :=
    Finset.sum_congr rfl fun a _ => mul_comm _ _
  rw [this]
  linear_combination hg

end GlobalTheory.LoopC.FrameDiff
end

section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Mass.Transp.discModule_transport : ∀ (K V V' : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h : V →ₗ⋆[K] V →ₗ[K] K) (h' : V' →ₗ⋆[K] V' →ₗ[K] K) (e : V ≃ₗ[K] V'), (∀ x y, h' (e x) (e y) = h x y) → ∀ (L : Submodule (𝓞 K) V) (I : Ideal (𝓞 K)), GlobalTheory.Mass.IsIntLat h' (GlobalTheory.Mass.Transp.img e L) → Nonempty ((↥(Formalism.HermitianLatticesTheory.dual h' (GlobalTheory.Mass.Transp.img e L)) ⧸ (GlobalTheory.Mass.Transp.img e L).comap (Formalism.HermitianLatticesTheory.dual h' (GlobalTheory.Mass.Transp.img e L)).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ I)) → GlobalTheory.Mass.IsIntLat h L ∧ Nonempty ((↥(Formalism.HermitianLatticesTheory.dual h L) ⧸ L.comap (Formalism.HermitianLatticesTheory.dual h L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ I)) := by
  intro K V V' _ _ _ _ _ _ _ _ _ _ _ h h' e he L I hI hQ
  have hL : GlobalTheory.Mass.IsIntLat h L := by
    have := GlobalTheory.Mass.Transp.intLat_img e.symm (GlobalTheory.Mass.Transp.symm_isom e he) _ hI
    rwa [GlobalTheory.Mass.Transp.img_symm_img] at this
  refine ⟨hL, ?_⟩
  obtain ⟨q⟩ := hQ
  set D := Formalism.HermitianLatticesTheory.dual h L with hDdef
  set D' := Formalism.HermitianLatticesTheory.dual h' (GlobalTheory.Mass.Transp.img e L) with hD'def
  have hD : D' = GlobalTheory.Mass.Transp.img e D := GlobalTheory.Mass.Transp.dual_img e he L
  have hmem : ∀ x : V, x ∈ D → e x ∈ D' := by
    intro x hx; rw [hD, GlobalTheory.Mass.Transp.mem_img]; simpa using hx
  have hmem' : ∀ y : V', y ∈ D' → e.symm y ∈ D := by
    intro y hy; rw [hD, GlobalTheory.Mass.Transp.mem_img] at hy; exact hy
  let f : D ≃ₗ[𝓞 K] D' :=
    { toFun := fun x => ⟨e x, hmem x x.2⟩
      invFun := fun y => ⟨e.symm y, hmem' y y.2⟩
      map_add' := fun x y => by ext; simp
      map_smul' := fun r x => by
        ext
        simp only [SetLike.val_smul, RingHom.id_apply]
        exact (e.toLinearMap.restrictScalars (𝓞 K)).map_smul r x
      left_inv := fun x => by ext; simp
      right_inv := fun y => by ext; simp }
  have hf : (L.comap D.subtype).map (f : D →ₗ[𝓞 K] D') = (GlobalTheory.Mass.Transp.img e L).comap D'.subtype := by
    ext ⟨y, hy⟩
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
    rw [GlobalTheory.Mass.Transp.mem_img]
    constructor
    · rintro ⟨⟨x, hx⟩, hxL, hxy⟩
      have : (f ⟨x, hx⟩ : V') = y := congrArg Subtype.val hxy
      simp only [f, LinearEquiv.coe_mk] at this
      rw [← this]; simpa using hxL
    · intro hyL
      refine ⟨⟨e.symm y, hmem' y hy⟩, hyL, ?_⟩
      ext; simp [f]
  exact ⟨(Submodule.Quotient.equiv _ _ f hf).trans q⟩
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.unitary_iwasawa_integration_formula_real_place : IwasawaFormula := by
  first | exact @GlobalTheory.FlagMeas.iwasawaFormula | exact GlobalTheory.FlagMeas.iwasawaFormula | (intros; apply GlobalTheory.FlagMeas.iwasawaFormula <;> assumption)
end

section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Cx NumberField

theorem _root_.GlobalTheory.T.rowMap_surjective_of_primitiveRows : ∀ (D : D7) [_root_.NumberField.IsTotallyComplex D.what₂.LL] (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Ps : Subgroup G) (ψs : Ps →* D.what₂.LLˣ) (Zs : DefSub A3.fam3.amb3) (S0 : IndefData (A3.side3 P0 ψ0 Zs)) (S1 : IndefData (A3.side3 Ps ψs Zs)) (X0 : BaseLevelRowSide D) (Dc : DefCols (A3.side3 Ps ψs Zs)) (Sp : SPer Dc) (C : ColData Dc Sp S1) (NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL)) (I : DivisionCompatibilityDataThreeSided D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 Dc) (Dcf : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 Ps ψs Zs)) (Spf : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (s : ℕ), DivDef3 D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 C NuC I → A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3) → PrimRows3 R (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3) → (R.toCx3 (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3)).zs = Zs → HEq ((R.toCx3 (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3)).data (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3).cr true) S1 → (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  first | exact @GlobalTheory.rowMap_surjective_of_primitiveRows_alt | exact GlobalTheory.rowMap_surjective_of_primitiveRows_alt | (intros; apply GlobalTheory.rowMap_surjective_of_primitiveRows_alt <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.unitaryJ_haar_entryBounded_polynomial_growth : ∀ {n : ℕ} (ε : Fin n → Bool) (S : Subgroup (Formalism.REAL.UJ ε)), IsClosed (S : Set (Formalism.REAL.UJ ε)) → ∀ μ : Measure (Formalism.REAL.UJ ε), Formalism.L2.SG.RealObj.IsHaarLoc (S : Set (Formalism.REAL.UJ ε)) μ → IsFiniteMeasureOnCompacts μ → ∃ (C : ℝ) (D : ℕ), ∀ R : ℝ, 1 ≤ R → μ {g : Formalism.REAL.UJ ε | ∀ i j, ‖Formalism.MainNotions.S.uMat g i j‖ ≤ R} ≤ ENNReal.ofReal (C * R ^ D) := by
  first | exact @GlobalTheory.UJGrowth.growth | exact GlobalTheory.UJGrowth.growth | (intros; apply GlobalTheory.UJGrowth.growth <;> assumption)
end

section


theorem _root_.GlobalTheory.T.unitriangularStabilizer_pointMatrix_blockDiagonal : ∀ {K : Type} [Field K] (sig : K →+* K), (∀ x, sig (sig x) = x) → ∀ (r : ℕ) (w : Formalism.MainNotions.S.Point K (r + 1)) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K), Formalism.MainNotions.S.ZhatOM Z = Formalism.MainNotions.S.ptMat w → (∀ s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) K, Formalism.MainNotions.S.IsUpUni s → Formalism.MainNotions.S.IsUpUni s' → (s.map sig).transpose * Z * s' = Z → ∀ a b : Fin (r + 1), Formalism.L2.SG.RealObj.blkOf w.1 a.1 ≠ Formalism.L2.SG.RealObj.blkOf w.1 b.1 → s' a b = 0) ∧ ∀ s' : Matrix (Fin (r + 1)) (Fin (r + 1)) K, Formalism.MainNotions.S.IsUpUni s' → (∀ a b : Fin (r + 1), Formalism.L2.SG.RealObj.blkOf w.1 a.1 ≠ Formalism.L2.SG.RealObj.blkOf w.1 b.1 → s' a b = 0) → ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) K, Formalism.MainNotions.S.IsUpUni s ∧ (s.map sig).transpose * Z * s' = Z := by
  first | exact @GlobalTheory.PointStab.stab_blockDiag | exact GlobalTheory.PointStab.stab_blockDiag | (intros; apply GlobalTheory.PointStab.stab_blockDiag <;> assumption)
end

section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.haar_density_conj_unitaryHermitianGroups : ∀ (m : ℕ) (H H' P : Matrix (Fin m) (Fin m) ℂ), Hᴴ = H → H * H = 1 → H'ᴴ = H' → H' * H' = 1 → IsUnit P → Pᴴ * H' * P = H → ∀ (μ : Measure (PI.MtM m)) (c : ℝ≥0∞), PI.IsHaarOnM (UH H') μ → HasDens (UH H') μ c → PI.IsHaarOnM (UH H) (μ.map fun x : PI.MtM m => Matrix.of.symm (P⁻¹ * Matrix.of x * P)) ∧ HasDens (UH H) (μ.map fun x : PI.MtM m => Matrix.of.symm (P⁻¹ * Matrix.of x * P)) c := by
  first | exact @GlobalTheory.AdDens.haar_dens_conj | exact GlobalTheory.AdDens.haar_dens_conj | (intros; apply GlobalTheory.AdDens.haar_dens_conj <;> assumption)
end
