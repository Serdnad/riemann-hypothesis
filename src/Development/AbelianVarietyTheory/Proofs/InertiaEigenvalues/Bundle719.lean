module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle257
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle272
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle142
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle025
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle303
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle705
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle558
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle706
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle702
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle703
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle704
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle605
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle534
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section

namespace GlobalTheory.DownLift.TypeLaw

variable {D : D7}

theorem setIntegral_mul_right_of_fd {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant] (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (k : G) (hk : Measure.map (fun g => g * k) μ = μ) (f : G → ℂ) (hf : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) :
    ∫ g in 𝓕, f (g * k) ∂μ = ∫ g in 𝓕, f g ∂μ := by
  have hmp : MeasurePreserving (fun g : G => g * k) μ μ := ⟨measurable_mul_const k, hk⟩
  have hemb : MeasurableEmbedding (fun g : G => g * k) := measurableEmbedding_mulRight k
  have h2 : IsFundamentalDomain Γ ((fun g : G => g * k) ⁻¹' 𝓕) μ := by
    refine h𝓕.preimage_of_equiv hmp.quasiMeasurePreserving (e := id) Function.bijective_id ?_
    intro γ g
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have hinv : ∀ (γ : Γ) (g : G), (fun g : G => f (g * k)) (γ • g) = (fun g : G => f (g * k)) g := by
    intro γ g
    simp only [Subgroup.smul_def, smul_eq_mul, mul_assoc]
    exact hf γ γ.2 _
  rw [h𝓕.setIntegral_eq h2 hinv]
  exact hmp.setIntegral_preimage_emb hemb f 𝓕

theorem flagOneLevel_eq_self_of_trivial {n : ℕ} (L : LevDat D.host.E ℂ n) (hL : L.P = LevelP.triv L.Pg L.r ℂ) : flag1L L = L := by
  cases L
  simp only at hL
  subst hL
  rfl

theorem adForms_right {G Γ W : Type} [Group G] [Group Γ] (ι : Γ →* G) [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (F : G → W)
    (hF : F ∈ Formalism.IndefR.Bridge.AdForms ι ρ J χ) (x : G) (k : J) : F (x * k) = (χ k : ℂ) • F x := by
  have h1 := hF 1 x k
  rw [map_one, one_mul, map_one, Module.End.one_apply] at h1
  exact h1

theorem adForm_type (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (c : CoefA V)
    (F : Formalism.IndefR.Bridge.Gf V → c.W)
    (hF : F ∈ Formalism.IndefR.Bridge.AdForms (Formalism.IndefR.Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ)
    (κ : GA D V) (hκ : κ ∈ levG V β (flag1L L)) (x : Formalism.IndefR.Bridge.Gf V) :
    F (x * (finHom V).rangeRestrict κ) = levChi V β (flag1L L) κ • F x := by
  have hmem : (finHom V).rangeRestrict κ ∈ (levEnv V β L).J := by
    show finE V κ ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (flag1L L)
    exact hκ.2
  have h1 := adForms_right (W := c.W) (Formalism.IndefR.Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ F hF x ⟨_, hmem⟩
  have hχ : (((levEnv V β L).χ ⟨_, hmem⟩ : ℂˣ) : ℂ) = levChi V β (flag1L L) κ := rfl
  rw [hχ] at h1
  exact h1

end GlobalTheory.DownLift.TypeLaw

namespace GlobalTheory.DownLift.TypeLaw

theorem datVt_P {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) :
    (R.datVt i t).P = LevelP.triv (R.datVt i t).Pg (R.datVt i t).r ℂ := by
  simp [LevCh.datVt, datY, LevelP.conj, LevelP.triv]
  rfl

end GlobalTheory.DownLift.TypeLaw

namespace GlobalTheory.DownLift.TypeLaw

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem extV_type (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (κ : GA D (Vc D i))
    (hκ : κ ∈ levG (Vc D i) (R.βV i) (R.datVt i t)) (h : GA D (Vc D i)) :
    R.extV i t y (h * κ) = levChi (Vc D i) (R.βV i) (R.datVt i t) κ • R.extV i t y h := by
  have hL : flag1L (R.datVt i t) = R.datVt i t := flagOneLevel_eq_self_of_trivial _ (datVt_P R i t)
  have hκ1 : κ ∈ levG (Vc D i) (R.βV i) (flag1L (R.datVt i t)) := by rw [hL]; exact hκ
  have hc0 : levChi (Vc D i) (R.βV i) (R.datVt i t) κ ≠ 0 := levChi_ne_zero _ κ
  have hchi : levChi (Vc D i) (R.βV i) (flag1L (R.datVt i t)) κ = levChi (Vc D i) (R.βV i) (R.datVt i t) κ := by rw [hL]
  have hyA : (R.HV i t).e y ∈ Formalism.IndefR.Bridge.AdForms (Formalism.IndefR.Bridge.ratF (Vc D i)) (R.cV i).coef.ρ
      (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J (levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ :=
    (hM.HV i t).2.1.le ⟨y, rfl⟩
  have hty : ∀ x, (R.HV i t).e y x = (levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ •
      (R.HV i t).e y (x * (finHom (Vc D i)).rangeRestrict κ) := by
    intro x
    have h1 := adForm_type (Vc D i) (R.βV i) (R.datVt i t) (R.cV i) ((R.HV i t).e y) hyA κ hκ1 x
    have h2 : (R.HV i t).e y (x * (finHom (Vc D i)).rangeRestrict κ) =
        levChi (Vc D i) (R.βV i) (R.datVt i t) κ • (R.HV i t).e y x :=
      h1.trans (congrArg (· • (R.HV i t).e y x) hchi)
    exact (inv_smul_smul₀ hc0 _).symm.trans (congrArg ((levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ • ·) h2.symm)
  have e1 := GlobalTheory.ThetaProjEquiv.ext_shift (R.cV i) (hM.cV i) κ hκ.1 _ hc0 ((R.HV i t).e y) ((R.HV i t).e y) hty h
  have hx : ∀ z, R.extV i t y z = (R.cV i).ext ((R.HV i t).e y) z := fun z => rfl
  have e2 : (R.cV i).ext (levChi (Vc D i) (R.βV i) (R.datVt i t) κ • (R.HV i t).e y) h =
      levChi (Vc D i) (R.βV i) (R.datVt i t) κ • (R.cV i).ext ((R.HV i t).e y) h := by
    exact congrFun (LinearMap.map_smul (R.cV i).ext _ ((R.HV i t).e y)) h
  exact (hx (h * κ)).trans (e1.symm.trans (e2.trans (congrArg (levChi (Vc D i) (R.βV i) (R.datVt i t) κ • ·) (hx h).symm)))

end GlobalTheory.DownLift.TypeLaw

namespace GlobalTheory.DownLift.TypeLaw

theorem alg_step {a b c d d' : ℂ} (hc : c ≠ 0) (hab : a = b) (hd : d' = c * d) : a * d = c⁻¹ * (b * d') := by
  rw [hab, hd, mul_left_comm b c d, inv_mul_cancel_left₀ hc]

theorem downInt_level : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (f : WO (Vc D i) (Wc D i) → ℂ), IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ κ ∈ levG (Vc D i) (R.βV i) (R.datVt i t), ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (R.ωP i t (κ, 1) f) l g = (levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ * downInt R i t y f l g := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hP i t y f hf κ hκ l g
  have hM := hG.core.models
  have hc0 : levChi (Vc D i) (R.βV i) (R.datVt i t) κ ≠ 0 := levChi_ne_zero _ κ
  have hFn : ∀ h, l (R.extV i t y (h * κ)) = levChi (Vc D i) (R.βV i) (R.datVt i t) κ * l (R.extV i t y h) := by
    intro h
    exact (congrArg l (extV_type R hM i t y κ hκ h)).trans (l.map_smul _ _)

  have hth : ∀ h, thetaKO (R.ωP i t) h g (R.ωP i t (κ, 1) f) = thetaKO (R.ωP i t) (h * κ) g f := by
    intro h
    have hm : ((h, g) : GA D (Vc D i) × GA D (Wc D i)) * (κ, 1) = (h * κ, g) := by
      rw [Prod.mk_mul_mk, mul_one]
    show R.ωP i t (h, g) (R.ωP i t (κ, 1) f) 0 = R.ωP i t (h * κ, g) f 0
    rw [← hm, map_mul, Module.End.mul_apply]

  let Φ : GA D (Vc D i) → ℂ := fun h => thetaKO (R.ωP i t) h g f * l (R.extV i t y h)
  have hΦ : ∀ γ ∈ GQ (Vc D i), ∀ h, Φ (γ * h) = Φ h := by
    intro γ hγ h
    have ht : thetaKO (R.ωP i t) (γ * h) g f = thetaKO (R.ωP i t) h g f := by
      have hm : ((γ, 1) : GA D (Vc D i) × GA D (Wc D i)) * (h, g) = (γ * h, g) := by
        rw [Prod.mk_mul_mk, one_mul]
      show R.ωP i t (γ * h, g) f 0 = R.ωP i t (h, g) f 0
      rw [← hm, map_mul, Module.End.mul_apply]
      exact (hP i t).datum.om_aut γ hγ 1 (GQ (Wc D i)).one_mem _ ((hP i t).datum.om_pres _ _ hf)
    have hl : l (R.extV i t y (γ * h)) = l (R.extV i t y h) :=
      congrArg l (GlobalTheory.ThetaProjEquiv.extV_left R hM.HV i t y γ hγ h)
    exact congrArg₂ (· * ·) ht hl

  obtain ⟨i1, i2, i3, i4⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable (Vc D i)
  have : IsTopologicalGroup (GA D (Vc D i)) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig (Vc D i).gram))
  have hH : (R.νV i t).IsHaarMeasure := (hM.νV i t).1.1
  have hmap := GlobalTheory.haar_map_mul_right_of_mem_compact_subgroup (R.νV i t) _
    (GlobalTheory.ParahoricCompact.isCompact_levG (Vc D i) (R.βV i) (R.datVt i t)) κ hκ
  have hint := setIntegral_mul_right_of_fd (GQ (Vc D i)) (R.νV i t) (R.fdV i t) (hM.νV i t).2 κ hmap Φ hΦ
  have hfun : (fun h => thetaKO (R.ωP i t) h g (R.ωP i t (κ, 1) f) * l (R.extV i t y h)) =
      fun h => (levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ * Φ (h * κ) := by
    funext h
    exact alg_step hc0 (hth h) (hFn h)
  exact (congrArg (fun φ : GA D (Vc D i) → ℂ => ∫ h in R.fdV i t, φ h ∂(R.νV i t)) hfun).trans
    ((integral_const_mul _ _).trans (congrArg ((levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ * ·) hint))

end GlobalTheory.DownLift.TypeLaw
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem coord_of_frac_rel {A N : Type} [CommRing A] [AddCommGroup N] [Module A N] {d : ℕ}
    (b : Module.Basis (Fin d) A N) (b' : Fin d → N) (hb : ∀ i, b i = b' i) (T c : A) (v w : Fin d → A) (n : N) (r s j k : ℕ)
    (h1 : (T * T) ^ r • (T ^ j • ∑ i, v i • b' i - T ^ k • n) = 0)
    (h2 : T ^ s • (c • n - T ^ j • ∑ i, w i • b' i) = 0) :
    T ^ (r + r + s + j) • (c • v - T ^ k • w) = 0 := by
  obtain rfl : ⇑b = b' := funext hb
  apply b.equivFun.symm.injective
  rw [map_zero, map_smul, map_sub, map_smul, map_smul, Module.Basis.equivFun_symm_apply,
    Module.Basis.equivFun_symm_apply]
  generalize ∑ i, v i • b i = V at *
  generalize ∑ i, w i • b i = W at *
  linear_combination (norm := module) (T ^ s * c) • h1 + (T ^ (r + r + k)) • h2

theorem coord_frobenius : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e → ∀ (B : Obj l ↥(OL K)) (V : Eval S B (M.M B)), IsCoord e V → ∀ (t : ↥B.I) (x m : M.M B) (k : ℕ), IsFrac (t : B.A) (M.Φ B t x) m k → ∀ (Q : Obj l ↥(OL K)) (a : Hom B Q) (g : Hom bk.prism Q), ∃ r : ℕ, a.f t ^ r • (BK.hf g bk.E ^ S.a • V.v a g m - a.f t ^ k • (S.A.map (BK.hf g)).mulVec fun i => Q.D.φ (V.v a g x i)) = 0 := by
  intro l _ K bk d S M e hF B V hV t x m k h Q a g
  refine (exists_isFrac (a.f t) (M.Φ Q ⟨a.f t, a.f_I _ t.2⟩ (M.tr a x))).elim fun n hn => hn.elim fun j hn => ?_
  refine (M.Φ_nat a t ⟨a.f t, a.f_I _ t.2⟩ x m k n j h hn).elim fun r hr => ?_
  refine (GlobalTheory.T.prismaticFCrystal_frobenius_pullback_basis l K bk d M e S.a S.A hF.Φ Q g ⟨a.f t, a.f_I _ t.2⟩ (V.v a g x) n j
    ((congrArg (M.Φ Q ⟨a.f t, a.f_I _ t.2⟩) (hV a g x)).symm.trans hn)).elim fun s hs => ?_
  refine (GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis _ _ g.f _ _ (M.tr g) (M.tr_bc g) _ e).elim fun b hb => ?_
  exact ⟨r + r + s + j, coord_of_frac_rel b (fun i => M.tr g (e i)) hb (a.f t) (BK.hf g bk.E ^ S.a)
    (V.v a g m) ((S.A.map (BK.hf g)).mulVec fun i => Q.D.φ (V.v a g x i)) n r s j k
    ((congrArg (fun z => (a.f t * a.f t) ^ r • (a.f t ^ j • z - a.f t ^ k • n)) (hV a g m)).symm.trans hr) hs⟩

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_injective_pushout_of_prismCover : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C : Obj l ↥(OL K)) (h : Hom B C), Cover h → ∀ (Q : Obj l ↥(OL K)) (a : Hom B Q), ∃ (Q' : Obj l ↥(OL K)) (h' : Hom Q Q') (a' : Hom C Q'), a'.comp h = h'.comp a ∧ Function.Injective h'.f := by
  first | exact @GlobalTheory.BSP.cover_po_injective | exact GlobalTheory.BSP.cover_po_injective | (intros; apply GlobalTheory.BSP.cover_po_injective <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.discPeriod_comparison_matrix_mul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s) (B : Obj l ↥(OL K)) (f₀ : Hom bk.prism B), toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf f₀ bk.E) ∈ nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀) → ∀ (f g h : Hom bk.prism B) (ε₁ ε₂ ε₃ : Matrix (Fin d) (Fin d) (Disc l (BK.hf f₀ X) bk.ρ₀)), ht.Rel (BK.hf f₀ X) f g ε₁ → ht.Rel (BK.hf f₀ X) g h ε₂ → ht.Rel (BK.hf f₀ X) f h ε₃ → ε₁ * ε₂ = ε₃ := by
  first | exact @GlobalTheory.BSP.Height.rel_mul | exact GlobalTheory.BSP.Height.rel_mul | (intros; apply GlobalTheory.BSP.Height.rel_mul <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.discPeriod_comparison_relation_map_prismHom : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s) (B B' : Obj l ↥(OL K)) (f₀ f g : Hom bk.prism B) (f₀' : Hom bk.prism B') (k : Hom B B') (ε : Matrix (Fin d) (Fin d) (Disc l (BK.hf f₀ X) bk.ρ₀)), ht.Rel (BK.hf f₀ X) f g ε → (∃ Fk : Disc l (BK.hf f₀ X) bk.ρ₀ →+* Disc l (BK.hf f₀' X) bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) k.f Fk) ∧ ∀ Fk : Disc l (BK.hf f₀ X) bk.ρ₀ →+* Disc l (BK.hf f₀' X) bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) k.f Fk → ht.Rel (BK.hf f₀' X) (k.comp f) (k.comp g) (ε.map Fk) := by
  first | exact @GlobalTheory.BSP.Height.rel_map | exact GlobalTheory.BSP.Height.rel_map | (intros; apply GlobalTheory.BSP.Height.rel_map <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.stratifiedCoordinates_of_prismCover : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C : Obj l ↥(OL K)) (h : Hom B C) (f : Hom bk.prism C), Cover h → ∀ (P : Type) [AddCommGroup P] [Module B.A P] (u : P →ₛₗ[h.f] (Fin d → C.A)), (∀ (Q : Obj l ↥(OL K)) (p q : Hom C Q), p.comp h = q.comp h → ∀ x, (fun i => p.f (u x i)) = (S.ε (p.comp f) (q.comp f)).mulVec fun i => q.f (u x i)) → ∀ (Q : Obj l ↥(OL K)) (a : Hom B Q) (g : Hom bk.prism Q), ∃ v : P →ₛₗ[a.f] (Fin d → Q.A), ∀ (Q' : Obj l ↥(OL K)) (h' : Hom Q Q') (a' : Hom C Q'), a'.comp h = h'.comp a → ∀ x, (fun i => h'.f (v x i)) = (S.ε (h'.comp g) (a'.comp f)).mulVec fun i => a'.f (u x i) := by
  first | exact @GlobalTheory.BSP.SiteCoord.coords_of_cover | exact GlobalTheory.BSP.SiteCoord.coords_of_cover | (intros; apply GlobalTheory.BSP.SiteCoord.coords_of_cover <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal


theorem _root_.GlobalTheory.T.semistablePeriod_cocycle_frobenius_relation_on_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]), (∀ g, IsUnit (ρ g)) → ∀ (s : WSeed bk d ρ τ) (g : ↥(GK K)) (G Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → s.κ g * s.F.map (bk.iS.comp C) = s.F.map (bk.iS.comp C) * (s.κ g).map Φ := by
  first | (exact @GlobalTheory.BKLim.KappaFrob.main) | (exact GlobalTheory.BKLim.KappaFrob.main) | (intros; apply GlobalTheory.BKLim.KappaFrob.main  <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.comparisonMatrix_exists_on_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s) (B : Obj l ↥(OL K)) (u : B.A) (f g : Hom bk.prism B), ∃ ε : Matrix (Fin d) (Fin d) (Disc l u bk.ρ₀), ht.Rel u f g ε := by
  first | exact @GlobalTheory.BSP.Height.rel_exists | exact GlobalTheory.BSP.Height.rel_exists | (intros; apply GlobalTheory.BSP.Height.rel_exists <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.lift_stratifiedSolution_succ_of_cover : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C D : Obj l ↥(OL K)) (h : Hom B C) (f : Hom bk.prism C) (p q : Hom C D), Cover h → IsPO h h p q → ∀ (m : ℕ) (z : Fin d → C.A), (∀ i, p.f (z i) - (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z j)) i ∈ adI D ^ m) → ∃ z' : Fin d → C.A, (∀ i, z' i - z i ∈ adI C ^ m) ∧ ∀ i, p.f (z' i) - (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z' j)) i ∈ adI D ^ (m + 1) := by
  first | exact @GlobalTheory.BSP.lift_solution_succ | exact GlobalTheory.BSP.lift_solution_succ | (intros; apply GlobalTheory.BSP.lift_solution_succ <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain
open ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.RecT GlobalTheory.HeightCounting
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.AVGood

section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem good_of_toral {x : IrrGL (k := k)} (h : Toral x) : Good x := by
  obtain ⟨s, hs, h1⟩ := h
  exact ⟨s, hs, fun y hy => Or.inl (h1 y hy)⟩

theorem fixed_ne_bot_of_mem_support {x : IrrGL (k := k)} (hx : fixed x.rep (KOne k (Fin x.1)) ≠ ⊥)
    {s : Multiset (IrrGL (k := k))} (hs : HasSupport x.rep s) {y : IrrGL (k := k)} (hy : y ∈ s) :
    fixed y.rep (KOne k (Fin y.1)) ≠ ⊥ := by
  obtain ⟨h, z, rfl, -, -, e, he⟩ := hs
  obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hy
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hx
  obtain ⟨w, hw, hw0⟩ := DepthZero.fixed_of_isSubquotient e (fun a => (z a).rep) he ⟨v, hv, hv0⟩ a
  exact (Submodule.ne_bot_iff _).2 ⟨w, hw, hw0⟩

theorem good_of_fixed_KOne (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing)
    (hk : ∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* k), Continuous i) (x : IrrGL (k := k))
    (hx : fixed x.rep (KOne k (Fin x.1)) ≠ ⊥) : Good x := by
  obtain ⟨s, hs⟩ := GlobalTheory.LocGL.SupportRing.exists_hasSupport hZ x
  exact ⟨s, hs, fun y hy => Or.inr ⟨hk, y, 1, isSmoothChar_one, fixed_ne_bot_of_mem_support hx hs hy,
    (IrrGL.tw_one y _).symm⟩⟩

theorem good_of_isSpherical (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (x : IrrGL (k := k)) (hx : IsSpherical x.rep) :
    Good x :=
  (GlobalTheory.SphSupport.toral_and_good_of_isSpherical hBZ k x hx).2

end Local

def TameAtG (D : D7) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) : Prop :=
  ∀ (i : D.nd.Loc) (j : Fin D.R.m) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E)
    (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), s.w = D.naut.plGw k v →
    NG.IsCompAt (tup (D.nd.mu i) j) s ξ → ∀ u : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ,
      Valued.v ((u : s.v.adicCompletion (maximalRealSubfield D.host.E)) - 1) < 1 → ξ u = 1

end GlobalTheory.AVGood
end
end

section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RecT

section Laws

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem lawsT_iff (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a)
    (rc : IrrGL (k := w.adicCompletion E) → WD h) : LawsT a ha rc ↔ UpperTheory.Zero.LLC.LawsT a ha rc :=
  ⟨fun H => ⟨H.1, H.2, H.3, H.4, H.5, H.6, H.7, H.8, H.9, H.10, H.11, H.12⟩,
   fun H => ⟨H.1, H.2, H.3, H.4, H.5, H.6, H.7, H.8, H.9, H.10, H.11, H.12⟩⟩

end Laws

end GlobalTheory.RecT
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

variable {l : ℕ} {R : Type} [CommRing R]

theorem adI_pow_eq_map_of_map_I {B C : Obj l R} (h : Hom B C) (hI : B.I.map h.f = C.I) (m : ℕ) :
    adI C ^ m = (adI B ^ m).map h.f := by
  rw [Ideal.map_pow]
  congr 1
  simp only [adI, Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_natCast, hI]

theorem isLoc_of_locP (hrig : ∀ (B B' : Obj l R) (f : Hom B B'), B.I.map f.f = B'.I)
    {B : Obj l R} {s d : B.A} (L : LocP B s d) : IsLoc s L.inl := by
  have hJ : ∀ m, adI L.Q ^ m = (adI B ^ m).map L.inl.f :=
    adI_pow_eq_map_of_map_I L.inl (hrig _ _ _)
  refine ⟨fun m => ?_, fun Q a ha => ?_⟩
  · letI := (qmap L.inl m).toAlgebra
    have hmap : ∀ b : B.A, algebraMap (B.A ⧸ adI B ^ m) (L.Q.A ⧸ adI L.Q ^ m) (Ideal.Quotient.mk _ b) =
        Ideal.Quotient.mk _ (L.inl.f b) := fun b => rfl
    refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
    · rintro ⟨y, k, rfl⟩
      change IsUnit (algebraMap (B.A ⧸ adI B ^ m) (L.Q.A ⧸ adI L.Q ^ m) (Ideal.Quotient.mk _ s ^ k))
      rw [map_pow, hmap]
      exact (L.unit.map _).pow k
    · intro z
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
      obtain ⟨k, b, hkb⟩ := L.surj c m
      refine ⟨⟨Ideal.Quotient.mk _ b, ⟨Ideal.Quotient.mk _ s ^ k, k, rfl⟩⟩, ?_⟩
      change Ideal.Quotient.mk _ c * algebraMap (B.A ⧸ adI B ^ m) (L.Q.A ⧸ adI L.Q ^ m)
        (Ideal.Quotient.mk _ s ^ k) = algebraMap (B.A ⧸ adI B ^ m) (L.Q.A ⧸ adI L.Q ^ m) (Ideal.Quotient.mk _ b)
      rw [map_pow, hmap, hmap, ← map_pow, ← map_mul, Ideal.Quotient.eq, hJ, mul_comm]
      exact hkb
    · intro x y hxy
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [hmap, hmap, Ideal.Quotient.eq, hJ, ← map_sub] at hxy
      obtain ⟨k, hk⟩ := L.ker (a - b) m hxy
      refine ⟨⟨Ideal.Quotient.mk _ s ^ k, k, rfl⟩, ?_⟩
      change Ideal.Quotient.mk _ s ^ k * Ideal.Quotient.mk _ a = Ideal.Quotient.mk _ s ^ k * Ideal.Quotient.mk _ b
      rw [← map_pow, ← map_mul, ← map_mul, Ideal.Quotient.eq, ← mul_sub]
      exact hk
  · obtain ⟨c, hc, -⟩ := L.univ Q a ha
    exact ⟨c, hc⟩

theorem exists_isLoc : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B : Obj l R) (s d : B.A), GenAway B s d →
    ∃ (C : Obj l R) (h : Hom B C), IsLoc s h ∧ C.I = Ideal.span {h.f d} := by
  intro l _ R _ B s d hg
  obtain ⟨L⟩ := GlobalTheory.T.nonempty_completedLocalizationPrism l R B s d hg
  exact ⟨L.Q, L.inl, isLoc_of_locP (GlobalTheory.T.prism_hom_map_ideal_eq l R) L, L.I_eq⟩

end GlobalTheory.BSP
end
