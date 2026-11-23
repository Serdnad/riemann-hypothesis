module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle521
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle246
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle269
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle534
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle707
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle002
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleBasisOfFCrystal
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConnPhiExtensionGeneratorEqZeta
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle711
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle014
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RestrictMem
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanOfPowMul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle710
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle020
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LFun (IsSplitChart IsInertChart KGL)
open GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.LocKerMod.FrameIdx

variable {K : Type} [Field K] {n : ℕ}

def colHom : (Fin n → K) →+ Matrix (Fin n) (Fin 1) K where
  toFun y := fun i _ => y i
  map_zero' := rfl
  map_add' _ _ := rfl

theorem colHom_injective : Function.Injective (colHom (K := K) (n := n)) :=
  fun x y h => funext fun i => congrFun (congrFun h i) 0

@[simp] theorem colHom_apply (y : Fin n → K) (i : Fin n) (j : Fin 1) : colHom y i j = y i := rfl

theorem colHom_mulVec (P : Matrix (Fin n) (Fin n) K) (y : Fin n → K) :
    colHom (P *ᵥ y) = GlobalTheory.SplitIdx.mulL (n := 1) P (colHom y) := by
  ext i j
  simp only [GlobalTheory.SplitIdx.mulL, AddMonoidHom.mk'_apply, colHom_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem mulL_one : GlobalTheory.SplitIdx.mulL (n := 1) (1 : Matrix (Fin n) (Fin n) K) = AddMonoidHom.id _ := by
  ext y : 1
  simp [GlobalTheory.SplitIdx.mulL]

end GlobalTheory.LocKerMod.FrameIdx


open GlobalTheory.LocKerMod.FrameIdx in
theorem GlobalTheory.LocKerMod.FrameIdx.idxAt_eq_pow : ∀ (D : D7) (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (a : GL (Fin T.rank) (w.adicCompletion D.host.E)), GlobalTheory.LFun.IsFrameAt w (frameLat T) a → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin T.rank → ℤ) (t : GL (Fin T.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w (n := T.rank), ∀ k₂ ∈ KGL w (n := T.rank), ∀ g : GlobalTheory.FinZeta.Gv T v, GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h g = a * (k₁ * t * k₂) * a⁻¹ → GlobalTheory.LocKerMod.idxAt T w h g = qV D.host.E w ^ (∑ i, max (d i) 0).toNat := by
  intro D T v w h a ha ϖ hϖ d t ht k₁ hk₁ k₂ hk₂ g hg
  set k : GL (Fin T.rank) (w.adicCompletion D.host.E) := k₁ * t * k₂ with hk
  set Lw := (GlobalTheory.LFun.latAt w (frameLat T)).toAddSubgroup with hLw
  set M := GlobalTheory.SplitIdx.intMat D.host.E w T.rank 1 with hM
  let Φ : (Fin T.rank → w.adicCompletion D.host.E) →+ Matrix (Fin T.rank) (Fin 1) (w.adicCompletion D.host.E) :=
    colHom.comp (a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1.mulVecLin.toAddMonoidHom
  have hΦ : Function.Injective Φ := by
    intro x y hxy
    have h1 : (a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *ᵥ x =
        (a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *ᵥ y := colHom_injective hxy
    have e := congrArg (fun z => a.1 *ᵥ z) h1
    simp only [Matrix.mulVec_mulVec] at e
    rwa [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec, Matrix.one_mulVec] at e
  have hA : Lw.map Φ = M := by
    ext Y
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩ i j
      have hx' : a.1 *ᵥ ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *ᵥ x) ∈ GlobalTheory.LFun.latAt w (frameLat T) := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]; exact hx
      exact (ha _).2 hx' i
    · intro hY
      refine ⟨a.1 *ᵥ (fun i => Y i 0), (ha _).1 (fun i => hY i 0), ?_⟩
      refine Matrix.ext fun i j => ?_
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      show colHom ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *ᵥ (a.1 *ᵥ fun i => Y i 0)) i 0 = Y i 0
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      rfl
  have hB : (Lw.map (GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h g).1.mulVecLin.toAddMonoidHom).map Φ =
      M.map (GlobalTheory.SplitIdx.mulL (n := 1) k.1) := by
    rw [← hA, AddSubgroup.map_map, AddSubgroup.map_map]
    congr 1
    refine AddMonoidHom.ext fun x => ?_
    show colHom ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *ᵥ
        ((GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h g).1 *ᵥ x)) =
      GlobalTheory.SplitIdx.mulL (n := 1) k.1 (colHom ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *ᵥ x))
    rw [← colHom_mulVec, hg, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    group
  have step1 : GlobalTheory.LocKerMod.idxAt T w h g = (M.map (GlobalTheory.SplitIdx.mulL (n := 1) k.1)).relIndex M := by
    unfold GlobalTheory.LocKerMod.idxAt
    rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hΦ, hB, hA]
  have hinv : (M.map (GlobalTheory.SplitIdx.mulL (n := 1) k.1)).map (GlobalTheory.SplitIdx.mulL (n := 1) (k⁻¹).1) = M := by
    rw [AddSubgroup.map_map, ← GlobalTheory.SplitIdx.LocIndex.mulL_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      mulL_one, AddSubgroup.map_id]
  have hinj : Function.Injective (GlobalTheory.SplitIdx.mulL (n := 1) (k⁻¹).1) := by
    intro x y hxy
    have e := congrArg (GlobalTheory.SplitIdx.mulL (n := 1) k.1) hxy
    simpa [GlobalTheory.SplitIdx.mulL, ← Matrix.mul_assoc, ← Units.val_mul] using e
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    have hv : Valued.v (0 : w.adicCompletion D.host.E) = _ := hϖ
    rw [map_zero] at hv
    exact WithZero.coe_ne_zero hv.symm
  have ht' : (t⁻¹).1 = Matrix.diagonal (fun i => ϖ ^ (-d i)) := by
    have e1 : t.1 * Matrix.diagonal (fun i => ϖ ^ (-d i)) = 1 := by
      rw [ht, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext i
      rw [← zpow_add₀ hϖ0, add_neg_cancel, zpow_zero]
    calc (t⁻¹).1 = (t⁻¹).1 * (t.1 * Matrix.diagonal (fun i => ϖ ^ (-d i))) := by rw [e1, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have hkinv : k⁻¹ = k₂⁻¹ * t⁻¹ * k₁⁻¹ := by rw [hk]; group
  rw [step1, ← AddSubgroup.relIndex_map_map_of_injective _ _ hinj, hinv, hkinv,
    GlobalTheory.SplitIdx.LocIndex.relIndex_intMat w T.rank 1 ϖ hϖ (fun i => -d i) t⁻¹ ht' k₂⁻¹ (inv_mem hk₂)
      k₁⁻¹ (inv_mem hk₁)]
  simp
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section

namespace GlobalTheory.DownLift.GenFinite

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem representation_inv_mul_apply_cancel_left {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W] (ρ : H →* Module.End ℂ W) (γ h : H)
    (v : W) : ρ (γ * h)⁻¹ (ρ γ v) = ρ h⁻¹ v := by
  rw [← Module.End.mul_apply, ← map_mul]; congr 2; group

theorem representation_inv_mul_smul_one_of_trivial_right {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W] (ρ : H →* Module.End ℂ W) (h κ : H)
    (hκ : ρ κ⁻¹ = 1) (c : ℂ) (v : W) : ρ (h * κ)⁻¹ (c • ρ 1 v) = c • ρ h⁻¹ v := by
  rw [map_one, Module.End.one_apply, map_smul, _root_.mul_inv_rev, map_mul, hκ, one_mul]

theorem extV_law (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    (γ : GQ (Vc D i)) (x : Formalism.IndefR.Bridge.Gf (Vc D i)) (k : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J) :
    (R.HV i t).e y (Formalism.IndefR.Bridge.ratF (Vc D i) γ * x * k) =
      ((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ k : ℂ) • (R.cV i).ρ γ ((R.HV i t).e y x) := by
  have h1 : (R.HV i t).e y ∈ LinearMap.range (R.HV i t).e := LinearMap.mem_range_self _ _
  exact (SetLike.ext_iff.mp (hM.HV i t).2.1 ((R.HV i t).e y)).mp h1 γ x k

theorem extV_left (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    (γ : GA D (Vc D i)) (hγ : γ ∈ GQ (Vc D i)) (h : GA D (Vc D i)) :
    R.extV i t y (γ * h) = R.extV i t y h := by
  have hx : (finHom (Vc D i)).rangeRestrict (γ * h) = Formalism.IndefR.Bridge.ratF (Vc D i) ⟨γ, hγ⟩ *
      (finHom (Vc D i)).rangeRestrict h * ((1 : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J) : Formalism.IndefR.Bridge.Gf (Vc D i)) := by
    apply Subtype.ext
    simp [Formalism.IndefR.Bridge.ratF]
  have e : (R.HV i t).e y ((finHom (Vc D i)).rangeRestrict (γ * h)) = (R.cV i).ρ γ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict h)) := by
    calc _ = _ := congrArg _ hx
      _ = _ := extV_law R hM i t y ⟨γ, hγ⟩ ((finHom (Vc D i)).rangeRestrict h) 1
      _ = _ := by simp only [map_one, Units.val_one, one_smul]
  show (R.cV i).ρ (γ * h)⁻¹ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict (γ * h))) =
    (R.cV i).ρ h⁻¹ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict h))
  refine (congrArg _ e).trans ?_
  exact representation_inv_mul_apply_cancel_left _ γ h _

theorem extV_type (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    (κ : GA D (Vc D i)) (hκ : κ ∈ levG (Vc D i) (R.βV i) (flag1L (R.datVt i t))) (h : GA D (Vc D i)) :
    R.extV i t y (h * κ) = levChi (Vc D i) (R.βV i) (flag1L (R.datVt i t)) κ • R.extV i t y h := by
  let k : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J := ⟨(finHom (Vc D i)).rangeRestrict κ, hκ.2⟩
  have hx : (finHom (Vc D i)).rangeRestrict (h * κ) = Formalism.IndefR.Bridge.ratF (Vc D i) 1 *
      (finHom (Vc D i)).rangeRestrict h * (k : Formalism.IndefR.Bridge.Gf (Vc D i)) := by
    apply Subtype.ext
    simp [k]
  have hχ : (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ k : ℂˣ) : ℂ) =
      levChi (Vc D i) (R.βV i) (flag1L (R.datVt i t)) κ := rfl
  have e : (R.HV i t).e y ((finHom (Vc D i)).rangeRestrict (h * κ)) =
      levChi (Vc D i) (R.βV i) (flag1L (R.datVt i t)) κ • (R.cV i).ρ 1 ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict h)) := by
    calc _ = _ := congrArg _ hx
      _ = _ := extV_law R hM i t y 1 ((finHom (Vc D i)).rangeRestrict h) k
      _ = _ := congrArg (· • _) hχ
  show (R.cV i).ρ (h * κ)⁻¹ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict (h * κ))) =
    _ • (R.cV i).ρ h⁻¹ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict h))
  refine (congrArg _ e).trans ?_
  exact representation_inv_mul_smul_one_of_trivial_right _ h κ ((hM.cV i).1 _ ((GfC (Vc D i)).inv_mem hκ.1)) _ _

def compF (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (l : (R.cV i).W →ₗ[ℂ] ℂ) :
    GA D (Vc D i) → ℂ :=
  fun h => l (R.extV i t y h)

theorem compF_type (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    (l : (R.cV i).W →ₗ[ℂ] ℂ) : HasType (Vc D i) (R.βV i) (flag1L (R.datVt i t)) (compF R i t y l) := by
  intro k hk h
  exact (congrArg l (extV_type R hM i t y k hk h)).trans (by rw [map_smul, smul_eq_mul]; rfl)

theorem compF_left (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    (l : (R.cV i).W →ₗ[ℂ] ℂ) (γ : GA D (Vc D i)) (hγ : γ ∈ GQ (Vc D i)) (h : GA D (Vc D i)) :
    compF R i t y l (γ * h) = compF R i t y l h :=
  congrArg l (extV_left R hM i t y γ hγ h)

theorem theta_left (R : RealDat D A Ks) (i : Fin D.R.m) (t : T)
    (hP : R.FullP)
    (φ : WO (Vc D i) (Wc D i) → ℂ) (hφ : IsThetaFunO R.ψ (Vc D i) (Wc D i) φ) (g : GA D (Wc D i))
    (γ : GA D (Vc D i)) (hγ : γ ∈ GQ (Vc D i)) (h : GA D (Vc D i)) :
    thetaKO (R.ωP i t) (γ * h) g φ = thetaKO (R.ωP i t) h g φ := by
  have hm : ((γ * h, g) : GA D (Vc D i) × GA D (Wc D i)) = (γ, 1) * (h, g) := by rw [Prod.mk_mul_mk, one_mul]
  show R.ωP i t (γ * h, g) φ 0 = R.ωP i t (h, g) φ 0
  rw [hm, map_mul, Module.End.mul_apply]
  exact (hP i t).datum.om_aut γ hγ 1 (GQ (Wc D i)).one_mem _ ((hP i t).datum.om_pres _ φ hφ)

theorem theta_transl (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (φ : WO (Vc D i) (Wc D i) → ℂ)
    (g : GA D (Wc D i)) (κ h : GA D (Vc D i)) :
    thetaKO (R.ωP i t) h g (R.ωP i t (κ, 1) φ) = thetaKO (R.ωP i t) (h * κ) g φ := by
  show R.ωP i t (h, g) (R.ωP i t (κ, 1) φ) 0 = R.ωP i t (h * κ, g) φ 0
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem theta_avgW (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (PP : R.Pg) (a : Fin D.R.r → kP PP.1) (tr : Bool)
    (ε : ℤ) (κ : G → GA D (Vc D i)) (f : WO (Vc D i) (Wc D i) → ℂ) (g : GA D (Wc D i)) (h : GA D (Vc D i)) :
    thetaKO (R.ωP i t) h g (avgW R i t PP a tr ε κ f) =
      ∑ j, (mirC R i PP a tr ε j * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ j))⁻¹) *
        thetaKO (R.ωP i t) (h * (κ j)⁻¹) g f := by
  rw [← Finset.sum_congr rfl fun j _ => congrArg (_ * ·) (theta_transl R i t f g (κ j)⁻¹ h)]
  show R.ωP i t (h, g) (avgW R i t PP a tr ε κ f) 0 = _

  simp only [avgW, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rfl

theorem sum_compF_eq_zero (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    (hNC : NoChi R i t y) (PP : R.Pg) (a : Fin D.R.r → kP PP.1) (ha : a ≠ 0) (tr : Bool) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (κ : G → GA D (Vc D i)) (hκ : IsLifts R i t κ) (l : (R.cV i).W →ₗ[ℂ] ℂ) (h : GA D (Vc D i)) :
    ∑ j, (mirC R i PP a tr ε j * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ j))⁻¹) *
      compF R i t y l (h * κ j) = 0 := by
  have h0 := congrFun (hNC PP a ha tr ε hε l) h
  refine Eq.trans ?_ h0
  simp only [gaL, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  show _ = mirC R i PP a tr ε j * actG0 (Vc D i) (R.βV i) (R.datVt i t) (R.eG j) (compF R i t y l) h
  rw [level_action_spec (compF_type R hM i t y l) ⟨κ j, hκ j⟩ (κ j) (hκ j) h]
  ring

def termF (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (l : (R.cV i).W →ₗ[ℂ] ℂ)
    (f : WO (Vc D i) (Wc D i) → ℂ) (g : GA D (Wc D i)) (κ : GA D (Vc D i)) : GA D (Vc D i) → ℂ :=
  fun h => thetaKO (R.ωP i t) (h * κ⁻¹) g f * compF R i t y l h

theorem termF_eq (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (l : (R.cV i).W →ₗ[ℂ] ℂ)
    (f : WO (Vc D i) (Wc D i) → ℂ) (g : GA D (Wc D i)) (κ : GA D (Vc D i)) :
    (fun h => thetaKO (R.ωP i t) h g (R.ωP i t (κ⁻¹, 1) f) * l (R.extV i t y h)) = termF R i t y l f g κ := by
  funext h
  exact congrArg (· * l (R.extV i t y h)) (theta_transl R i t f g κ⁻¹ h)

theorem termF_left (R : RealDat D A Ks) (hM : R.IsModels) (hP : R.FullP) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    (l : (R.cV i).W →ₗ[ℂ] ℂ) (f : WO (Vc D i) (Wc D i) → ℂ) (hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) f)
    (g : GA D (Wc D i)) (κ : GA D (Vc D i)) (γ : GA D (Vc D i)) (hγ : γ ∈ GQ (Vc D i)) (h : GA D (Vc D i)) :
    termF R i t y l f g κ (γ * h) = termF R i t y l f g κ h := by
  show thetaKO (R.ωP i t) (γ * h * κ⁻¹) g f * compF R i t y l (γ * h) =
    thetaKO (R.ωP i t) (h * κ⁻¹) g f * compF R i t y l h
  rw [mul_assoc, theta_left R i t hP f hf g γ hγ, compF_left R hM i t y l γ hγ h]

theorem avgLaw : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H), NoChi R i t y → ∀ (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 → ∀ (tr : Bool) (ε : ℤ), (ε = 1 ∨ ε = -1) → ∀ κ : G → GA D (Vc D i), GlobalTheory.DownLift.GenFinite.IsLifts R i t κ → ∀ f : WO (Vc D i) (Wc D i) → ℂ, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (GlobalTheory.DownLift.GenFinite.avgW R i t PP a tr ε κ f) l g = 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hP i t y hNC PP a ha tr ε hε κ hκ f hf l g
  have hM := hG.core.models
  obtain ⟨hmeas, hfd⟩ := hM.νV i t
  haveI : (R.νV i t).IsHaarMeasure := hmeas.1
  haveI : IsTopologicalGroup (GA D (Vc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D (Vc D i)) := ⟨rfl⟩
  haveI : Countable (GQ (Vc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
  haveI : (R.νV i t).IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds _ _ hmeas.1
  have hu_int : ∀ j, IntegrableOn (termF R i t y l f g (κ j)) (R.fdV i t) (R.νV i t) := by
    intro j
    have h1 := GlobalTheory.T.integrableOn_downwardThetaLift_integrand D G Pl0 T A Ks R F hG hP i t y (R.ωP i t ((κ j)⁻¹, 1) f) l g
      ((hP i t).datum.om_pres _ f hf)
    exact (congrArg (fun φ => IntegrableOn φ (R.fdV i t) (R.νV i t)) (termF_eq R i t y l f g (κ j))).mp h1
  have hv_int : ∀ j, IntegrableOn (fun h => termF R i t y l f g (κ j) (h * κ j)) (R.fdV i t) (R.νV i t) :=
    fun j => GlobalTheory.integrableOn_fundamentalDomain_mul_right hfd (κ j) _
      (fun γ hγ h => termF_left R hM hP i t y l f hf g (κ j) γ hγ h) (hu_int j)
  have hsub : ∀ j, ∫ h in R.fdV i t, termF R i t y l f g (κ j) h ∂(R.νV i t) =
      ∫ h in R.fdV i t, termF R i t y l f g (κ j) (h * κ j) ∂(R.νV i t) :=
    fun j => (GlobalTheory.setIntegral_fundamentalDomain_mul_right hfd (κ j) _
      (fun γ hγ h => termF_left R hM hP i t y l f hf g (κ j) γ hγ h)).symm
  have hpt1 : ∀ h, thetaKO (R.ωP i t) h g (avgW R i t PP a tr ε κ f) * compF R i t y l h =
      ∑ j, (mirC R i PP a tr ε j * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ j))⁻¹) *
        termF R i t y l f g (κ j) h := by
    intro h
    rw [theta_avgW, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _
  have hpt2 : ∀ h, ∑ j, (mirC R i PP a tr ε j * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ j))⁻¹) *
      termF R i t y l f g (κ j) (h * κ j) = 0 := by
    intro h
    have e : ∀ j, termF R i t y l f g (κ j) (h * κ j) = thetaKO (R.ωP i t) h g f * compF R i t y l (h * κ j) := by
      intro j
      show thetaKO (R.ωP i t) (h * κ j * (κ j)⁻¹) g f * _ = _
      rw [mul_inv_cancel_right]
    simp only [e]
    rw [← mul_zero (thetaKO (R.ωP i t) h g f), ← sum_compF_eq_zero R hM i t y hNC PP a ha tr ε hε κ hκ l h,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  show ∫ h in R.fdV i t, thetaKO (R.ωP i t) h g (avgW R i t PP a tr ε κ f) * compF R i t y l h ∂(R.νV i t) = 0
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt1),
    integral_finsetSum _ fun j _ => (hu_int j).const_mul _]
  simp only [integral_const_mul]
  simp only [hsub]
  simp only [← integral_const_mul]
  rw [← integral_finsetSum _ fun j _ => (hv_int j).const_mul _]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt2)]
  exact integral_zero _ _

end GlobalTheory.DownLift.GenFinite

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.prismCrystal_changeOfBasis_constantCoeff_eq_one : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : Lat a O K ϖ) (I : Ident t ϖ P T), letI := zlLat T; ∀ (E : FCrys l ↥(OL (ϖ.field a))) (jA : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T)), Realises (ϖ.field a) E (ainfObj _) (ainfId _) ↥T.L.T (actZ T) jA → (∀ y : TW (OW l O) T, (∃ x : E.M (ϖ.prism a), y = kappa T (jA (E.tr (ϖ.toAinf a) x))) ↔ ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) → ∀ (oE : O → FHom E E), (∀ (c : O) (x : E.M (ainfObj (ϖ.field a))), jA ((oE c).u (ainfObj (ϖ.field a)) x) = (OfCrystal.mulZ T c).lTensor (WCb l) (jA x)) → ∀ (b : ι → E.M (ϖ.prism a)), (∀ j, ∃ hm : (bas j : Vec K a ι) ∈ P.M, kappa T (jA (E.tr (ϖ.toAinf a) (b j))) = I.j (toW t ϖ P ⟨bas j, mem_ME_of_mem_M hm⟩)) → ∀ (PP S₀ : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (δ : GlobalTheory.Prism.Hom PP S₀) (κ : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (κ₀ : ZMod a → S₀.A →+* K⟦X⟧), δ.comp p₀ = δ.comp p₁ → (∀ τ y, κ₀ τ (δ.f y) = PowerSeries.constantCoeff (κ τ y)) → (∀ τ (x : (Wq l a)⟦X⟧), κ τ (p₀.f x) = PowerSeries.C (toAc t K (frobS l a x) τ : K⟦X⟧)) → ∀ (Q : Type) [Fintype Q] (c : ι → ι → Q → O) (y : ι → ι → Q → PP.A), (∀ j, E.tr p₁ (b j) = ∑ i, ∑ q, y i j q • (oE (c i j q)).u PP (E.tr p₀ (b i))) → ∀ τ, (Matrix.of fun i j => ∑ q, c i j q • κ τ (y i j q)).map PowerSeries.constantCoeff = 1 := by
  first | exact @GlobalTheory.CrysDiag.eps_constantCoeff_eq_one | exact GlobalTheory.CrysDiag.eps_constantCoeff_eq_one | (intros; apply GlobalTheory.CrysDiag.eps_constantCoeff_eq_one <;> assumption)
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType ValuativeRel Polynomial

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TameCharLabel

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {p : ℕ} [Fact p.Prime]

theorem red_natCast_val (hp : resCard F = p) (a : ZMod p) : red hp ((a.val : ℕ) : 𝒪[F]) = a := by
  rw [map_natCast, ZMod.natCast_zmod_val]

theorem valuation_natCast_val (hp : resCard F = p) (a : (ZMod p)ˣ) :
    valuation F ((((a : ZMod p).val : ℕ) : F)) = 1 := by
  have hu : IsUnit (((a : ZMod p).val : ℕ) : 𝒪[F]) :=
    isUnit_of_red_ne_zero hp (by rw [red_natCast_val]; exact a.ne_zero)
  have := (Valuation.integer.integers (valuation F)).isUnit_iff_valuation_eq_one.1 hu
  rwa [map_natCast] at this

theorem tame_eq {χ : Fˣ →* ℂˣ} (hχ : IsTame χ) {x y : Fˣ} (hy : valuation F (y : F) = 1)
    (hxy : valuation F ((x : F) - y) < 1) : χ x = χ y := by
  have h1 : valuation F (((x / y : Fˣ) : F) - 1) < 1 := by
    have : ((x / y : Fˣ) : F) - 1 = ((x : F) - y) / y := by
      rw [Units.val_div_eq_div_val, sub_div, div_self y.ne_zero]
    rw [this, map_div₀, hy, div_one]
    exact hxy
  have := hχ _ h1
  rwa [_root_.map_div, div_eq_one] at this

def unitOf (hp : resCard F = p) (a : (ZMod p)ˣ) : Fˣ :=
  Units.mk0 (((a : ZMod p).val : ℕ) : F) fun h => by
    have := valuation_natCast_val hp a
    rw [h, map_zero] at this
    exact zero_ne_one this

theorem eq_unitOf {χ : Fˣ →* ℂˣ} (hχ : IsTame χ) (hp : resCard F = p) (a : (ZMod p)ˣ) (x : Fˣ)
    (hx : valuation F ((x : F) - ((a : ZMod p).val : F)) < 1) : χ x = χ (unitOf hp a) :=
  tame_eq hχ (valuation_natCast_val hp a) hx

theorem exists_charLift (hp : resCard F = p) {χ : Fˣ →* ℂˣ} (hχ : IsTame χ) : ∃ θ : (ZMod p)ˣ →* ℂˣ, CharLift θ χ := by
  refine ⟨{ toFun := fun a => χ (unitOf hp a), map_one' := ?_, map_mul' := fun a b => ?_ }, fun a x hx => ?_⟩
  · have h := eq_unitOf hχ hp 1 1 (by
      have := (red_eq_iff_val hp 1 ((1 : (ZMod p)ˣ) : ZMod p)).1 (by simp)
      simpa using this)
    rw [map_one] at h
    exact h.symm
  · have h := eq_unitOf hχ hp (a * b) (unitOf hp a * unitOf hp b) (by
      have := (red_eq_iff_val hp (((a : ZMod p).val : ℕ) * ((b : ZMod p).val : ℕ) : 𝒪[F]) ((a * b : (ZMod p)ˣ) : ZMod p)).1
        (by rw [map_mul, red_natCast_val, red_natCast_val, Units.val_mul])
      rw [MulMemClass.coe_mul, SubringClass.coe_natCast, SubringClass.coe_natCast] at this
      rw [Units.val_mul]
      exact this)
    rw [map_mul] at h
    exact h.symm
  · exact eq_unitOf hχ hp a x hx

end Local

end GlobalTheory.TameCharLabel

namespace GlobalTheory.TameCharLabel

open NumberField IsDedekindDomain GlobalTheory.SerSys.TameGen GlobalTheory.Published.DepthZeroModel

theorem inflates_det {E : Type} [Field E] [NumberField E] {g : ℕ} [Fact g.Prime] {w : HeightOneSpectrum (𝓞 E)}
    (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) {θ : (ZMod g)ˣ →* ℂˣ} {χ : (w.adicCompletion E)ˣ →* ℂˣ}
    (hχ : IsSmoothChar χ) (hθ : CharLift θ χ) :
    Inflates ((IrrRep.det (Fin 1) χ hχ).ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) (tauOne θ) := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  refine ⟨LinearMap.id, fun e => (one_ne_zero : (1 : ℂ) ≠ 0) (LinearMap.congr_fun e (1 : ℂ)), fun k (v : ℂ) => ?_⟩
  set c := Matrix.GeneralLinearGroup.det k
  have e2 : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g 1 k)) =
      Units.map i.toRingHom.toMonoidHom (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom c) := by
    ext; simp [c, GlobalTheory.GLp.inc, RingHom.map_det]
  have e3 : Matrix.GeneralLinearGroup.det (GlobalTheory.GLp.red g 1 k) =
      Units.map (PadicInt.toZMod (p := g)).toMonoidHom c := by
    ext; simp [c, GlobalTheory.GLp.red, RingHom.map_det]
  set r : ℕ := (PadicInt.toZMod (c : ℤ_[g])).val
  have hk : ‖(((c : ℤ_[g]) - r : ℤ_[g]) : ℚ_[g])‖ < 1 := by
    have : (c : ℤ_[g]) - r ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
      rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
    rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at this
    exact this
  have h6 := he.lt_one_iff_lt_one.2 (GlobalTheory.Published.DepthZeroTypeModel.v_lt_one i hi hk)
  have h7 : χ (Units.map i.toRingHom.toMonoidHom (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom c)) =
      θ (Units.map (PadicInt.toZMod (p := g)).toMonoidHom c) := by
    refine hθ _ _ ?_
    convert h6 using 2
    simp [r]
  change ((θ (Matrix.GeneralLinearGroup.det (GlobalTheory.GLp.red g 1 k)) : ℂˣ) : ℂ) • v =
    ((χ (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g 1 k))) : ℂˣ) : ℂ) • v
  rw [e2, e3, h7]

end GlobalTheory.TameCharLabel

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.teichmuller_eps_pow_sub_one_eq_eisenstein_mul_unit : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ε : OCb l) (c : ℕ), IsEps ε → c ≠ 0 → ∃ u : OD l O, IsUnit u ∧ toOD l O (1 ⊗ₜ WittVector.teichmuller l ε) ^ c - 1 = GlobalTheory.GalStep.ED K t ϖ * u := by
  first | exact @GlobalTheory.GalStep.teich_pow_sub_one_eq_ED_mul | exact GlobalTheory.GalStep.teich_pow_sub_one_eq_ED_mul | (intros; apply GlobalTheory.GalStep.teich_pow_sub_one_eq_ED_mul <;> assumption)
end
