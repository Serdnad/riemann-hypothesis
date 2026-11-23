module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficie
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle062
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle415
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.LocalToGlobal.AlgebraicTheory.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle104
public import Formalism.LocalToGlobal.Columns.ChainInstY
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle065
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle105
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardKerSubspacesAndHeckePolyOfConvolution
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementC
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle108
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalToGlobal.IndefiniteReal.Bridge
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL.IwaFix

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

theorem fixed_iwahori_ne_bot_of_twist {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin n) k) V} {ρ' : Representation ℂ (GL (Fin n) k) W} (s : ℂ)
    (T : (twist ρ (detChar (Fin n) (absPow k s))).Equiv ρ') (h : fixed ρ' (iwahori k (Fin n)) ≠ ⊥) :
    fixed ρ (iwahori k (Fin n)) ≠ ⊥ := by
  obtain ⟨y, hy, h0⟩ := (Submodule.ne_bot_iff _).1 h
  obtain ⟨x, rfl⟩ := T.toLinearEquiv.surjective y
  refine (Submodule.ne_bot_iff _).2 ⟨x, GlobalTheory.Parabolic.mem_fixed.2 fun g hg => ?_, fun hx => h0 (by simp [hx])⟩
  have e := T.toIntertwiningMap.isIntertwining _ _ g x
  have hd : absPow k s (Matrix.GeneralLinearGroup.det g) = 1 := by
    have h1 := GlobalTheory.SmGL.LeviInt.nabs_det_eq_one (iwahori_le_KO k (Fin n) hg)
    ext; simp [absPow, h1]
  rw [twist_apply, detChar_apply, hd, Units.val_one, one_smul] at e
  have hy' := GlobalTheory.Parabolic.mem_fixed.1 hy g hg
  exact T.toLinearEquiv.injective (e.trans hy')

end GlobalTheory.AboveL.IwaFix
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.Pst.ResLetter

open TensorProduct Module

theorem zpow_intertwine {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (T : M →+ N) (a : (Module.End R M)ˣ) (b : (Module.End R N)ˣ) (hab : ∀ x, T ((a : Module.End R M) x) = (b : Module.End R N) (T x)) (n : ℤ) (x : M) :
    T (((a ^ n : (Module.End R M)ˣ) : Module.End R M) x) = ((b ^ n : (Module.End R N)ˣ) : Module.End R N) (T x) := by
  have hinv : ∀ y, T (((a⁻¹ : (Module.End R M)ˣ) : Module.End R M) y) =
      ((b⁻¹ : (Module.End R N)ˣ) : Module.End R N) (T y) := by
    intro y
    have h1 : (b : Module.End R N) (T (((a⁻¹ : (Module.End R M)ˣ) : Module.End R M) y)) = T y := by
      rw [← hab, ← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one, Module.End.one_apply]
    rw [← h1, ← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Module.End.one_apply]
  induction n using Int.induction_on generalizing x with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, zpow_add_one, Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, ih, hab]
  | pred n ih =>
    rw [zpow_sub_one, zpow_sub_one, Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, ih, hinv]

section Gen

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {LL : FinExt l} {V : Type} [AddCommGroup V]
  [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] {K K' : FinExt l}
  (ρ : Representation ↥LL.1 ↥(GK K) V) (hle : K.1 ≤ K'.1)

def toRes : ↥(Dpst P ρ) →+ ↥(Dpst P (GlobalTheory.Pst.resTo ρ hle)) where
  toFun x := ⟨x.1, by rw [GlobalTheory.Pst.Dpst_resTo]; exact x.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

def ofRes : ↥(Dpst P (GlobalTheory.Pst.resTo ρ hle)) →+ ↥(Dpst P ρ) where
  toFun x := ⟨x.1, by rw [← GlobalTheory.Pst.Dpst_resTo P ρ hle]; exact x.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

theorem toRes_ofRes (x : ↥(Dpst P (GlobalTheory.Pst.resTo ρ hle))) : toRes P ρ hle (ofRes P ρ hle x) = x := rfl
theorem ofRes_toRes (x : ↥(Dpst P ρ)) : ofRes P ρ hle (toRes P ρ hle x) = x := rfl

theorem toRes_smul (a : ↥LL.1) (x : ↥(Dpst P ρ)) :
    toRes P ρ hle ((Dpst P ρ).module.toSMul.smul a x) =
      (Dpst P (GlobalTheory.Pst.resTo ρ hle)).module.toSMul.smul (RingHom.id _ a) (toRes P ρ hle x) := rfl
theorem ofRes_smul (a : ↥LL.1) (x : ↥(Dpst P (GlobalTheory.Pst.resTo ρ hle))) :
    ofRes P ρ hle ((Dpst P (GlobalTheory.Pst.resTo ρ hle)).module.toSMul.smul a x) =
      (Dpst P ρ).module.toSMul.smul (RingHom.id _ a) (ofRes P ρ hle x) := rfl

theorem toRes_mulD (c : ↥(MaximalUnramifiedExtension l)) (x : ↥(Dpst P ρ)) :
    toRes P ρ hle (mulD P ρ c x) = mulD P (GlobalTheory.Pst.resTo ρ hle) c (toRes P ρ hle x) := rfl
theorem ofRes_mulD (c : ↥(MaximalUnramifiedExtension l)) (x : ↥(Dpst P (GlobalTheory.Pst.resTo ρ hle))) :
    ofRes P ρ hle (mulD P (GlobalTheory.Pst.resTo ρ hle) c x) = mulD P ρ c (ofRes P ρ hle x) := rfl
theorem toRes_phiD (x : ↥(Dpst P ρ)) :
    toRes P ρ hle (phiD P ρ x) = phiD P (GlobalTheory.Pst.resTo ρ hle) (toRes P ρ hle x) := rfl
theorem toRes_monD (x : ↥(Dpst P ρ)) :
    toRes P ρ hle (monD P ρ x) = monD P (GlobalTheory.Pst.resTo ρ hle) (toRes P ρ hle x) := rfl

theorem toRes_actD (g : ↥(GK K)) (g' : ↥(GK K')) (hg : (g' : GQ l) = (g : GQ l)) (x : ↥(Dpst P ρ)) :
    toRes P ρ hle (actD P ρ g x) = actD P (GlobalTheory.Pst.resTo ρ hle) g' (toRes P ρ hle x) := by
  have e : Subgroup.inclusion (GK_le hle) g' = g := Subtype.ext hg
  subst e
  rfl

theorem toRes_phiU_zpow [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)]
    [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (GlobalTheory.Pst.resTo ρ hle))] (n : ℤ) (x : ↥(Dpst P ρ)) :
    toRes P ρ hle (((phiU P ρ ^ n : (End ↥LL.1 ↥(Dpst P ρ))ˣ) : End ↥LL.1 ↥(Dpst P ρ)) x) =
      ((phiU P (GlobalTheory.Pst.resTo ρ hle) ^ n : (End ↥LL.1 ↥(Dpst P (GlobalTheory.Pst.resTo ρ hle)))ˣ) :
        End ↥LL.1 ↥(Dpst P (GlobalTheory.Pst.resTo ρ hle))) (toRes P ρ hle x) :=
  zpow_intertwine (toRes P ρ hle) (phiU P ρ) (phiU P (GlobalTheory.Pst.resTo ρ hle)) (fun y => toRes_phiD P ρ hle y) n x

end Gen

section Weil

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L Ω : Type} [Field Ω] [Field K] [NumberField K]
  [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)}
  {h : Formalism.ConjugateSelfDual.IsPlaceOver A v} {h' : Formalism.ConjugateSelfDual.IsPlaceOver A v'}
  {O O' : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O']
  [TopologicalSpace O'] {Bw : LocBridge l K Ω (ReciprocityTheory.Gal.Dec (F := K) A) O} {Bw' : LocBridge l L Ω (ReciprocityTheory.Gal.Dec (F := L) A) O'}
  {LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]

theorem alpha_eq (hj : GlobalTheory.Pst.Induces Bw) (hj' : GlobalTheory.Pst.Induces Bw') (σ : Weil h) (σ' : Weil h')
    (hσ : ∀ z : Ω, (σ : Formalism.ConjugateSelfDual.G K Ω) z = (σ' : Formalism.ConjugateSelfDual.G L Ω) z) : alpha l σ' = alpha l σ := by
  have e := GlobalTheory.LocLanglands.normV_zpow_deg_eq σ' σ hσ
  rw [GlobalTheory.Pst.normV_eq_pow (hj'.mem_placesOver h'), GlobalTheory.Pst.normV_eq_pow (hj.mem_placesOver h)] at e
  push_cast at e
  simp only [← zpow_natCast, ← zpow_mul] at e
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  exact zpow_right_injective₀ (zero_lt_one.trans hl) hl.ne' e

variable (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V) (hle : Bw.Kw.1 ≤ Bw'.Kw.1)
  [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (GlobalTheory.Pst.resTo ρ hle))]

theorem toRes_weilD (σ : Weil h) (σ' : Weil h')
    (hg : (weilToGK Bw' h' σ' : GQ l) = (weilToGK Bw h σ : GQ l)) (ha : alpha l σ' = alpha l σ)
    (x : ↥(Dpst P ρ)) :
    toRes P ρ hle (weilD Bw h P ρ σ x) = weilD Bw' h' P (GlobalTheory.Pst.resTo ρ hle) σ' (toRes P ρ hle x) := by
  calc toRes P ρ hle (weilD Bw h P ρ σ x)
      = toRes P ρ hle (actD P ρ (weilToGK Bw h σ)
          (((phiU P ρ ^ (-alpha l σ) : (End ↥LL.1 ↥(Dpst P ρ))ˣ) : End ↥LL.1 ↥(Dpst P ρ)) x)) := rfl
    _ = actD P (GlobalTheory.Pst.resTo ρ hle) (weilToGK Bw' h' σ') (toRes P ρ hle
          (((phiU P ρ ^ (-alpha l σ) : (End ↥LL.1 ↥(Dpst P ρ))ˣ) : End ↥LL.1 ↥(Dpst P ρ)) x)) :=
        toRes_actD P ρ hle _ _ hg _
    _ = actD P (GlobalTheory.Pst.resTo ρ hle) (weilToGK Bw' h' σ')
          (((phiU P (GlobalTheory.Pst.resTo ρ hle) ^ (-alpha l σ) : (End ↥LL.1 ↥(Dpst P (GlobalTheory.Pst.resTo ρ hle)))ˣ) :
            End ↥LL.1 ↥(Dpst P (GlobalTheory.Pst.resTo ρ hle))) (toRes P ρ hle x)) :=
        congrArg _ (toRes_phiU_zpow P ρ hle _ x)
    _ = weilD Bw' h' P (GlobalTheory.Pst.resTo ρ hle) σ' (toRes P ρ hle x) := by rw [← ha]; rfl

variable (ι : Om l ≃+* ℂ)

theorem wdHom_ext {M : Type*} [AddCommGroup M] [Module ℂ M] {f g : WDSpace P ι ρ →ₗ[ℂ] M}
    (hfg : ∀ x, f (wdMk P ι ρ x) = g (wdMk P ι ρ x)) : f = g :=
  LinearMap.ext_on_range (span_wdMk P ι ρ) hfg

def resEquiv : WDSpace P ι ρ ≃ₗ[ℂ] WDSpace P ι (GlobalTheory.Pst.resTo ρ hle) :=
  letI := algC ι LL
  LinearEquiv.ofLinear
    (EnlargeCoeff.chg (mulD P ρ) (mulD P (GlobalTheory.Pst.resTo ρ hle)) ℂ (urC ι) (RingHom.id _) (fun _ => rfl)
      (toRes P ρ hle) (toRes_smul P ρ hle) (toRes_mulD P ρ hle))
    (EnlargeCoeff.chg (mulD P (GlobalTheory.Pst.resTo ρ hle)) (mulD P ρ) ℂ (urC ι) (RingHom.id _) (fun _ => rfl)
      (ofRes P ρ hle) (ofRes_smul P ρ hle) (ofRes_mulD P ρ hle))
    (letter_hom_ext _ _ _ fun x => by
      rw [LinearMap.comp_apply, EnlargeCoeff.chg_mk, EnlargeCoeff.chg_mk, toRes_ofRes, LinearMap.id_apply])
    (letter_hom_ext _ _ _ fun x => by
      rw [LinearMap.comp_apply, EnlargeCoeff.chg_mk, EnlargeCoeff.chg_mk, ofRes_toRes, LinearMap.id_apply])

theorem resEquiv_mk (x : ↥(Dpst P ρ)) :
    resEquiv P ρ hle ι (wdMk P ι ρ x) = wdMk P ι (GlobalTheory.Pst.resTo ρ hle) (toRes P ρ hle x) :=
  letI := algC ι LL
  EnlargeCoeff.chg_mk _ _ _ _ _ _ _ _ (toRes_mulD P ρ hle) x

theorem resEquiv_wdN (y : WDSpace P ι ρ) :
    resEquiv P ρ hle ι (wdN P ι ρ y) = wdN P ι (GlobalTheory.Pst.resTo ρ hle) (resEquiv P ρ hle ι y) := by
  have : (resEquiv P ρ hle ι).toLinearMap ∘ₗ wdN P ι ρ =
      wdN P ι (GlobalTheory.Pst.resTo ρ hle) ∘ₗ (resEquiv P ρ hle ι).toLinearMap :=
    wdHom_ext P ρ ι fun x => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, wdN_mk, resEquiv_mk, toRes_monD]
  exact LinearMap.congr_fun this y

theorem resEquiv_wdRho (hj : GlobalTheory.Pst.Induces Bw) (hj' : GlobalTheory.Pst.Induces Bw') (σ : Weil h) (σ' : Weil h')
    (hg : (weilToGK Bw' h' σ' : GQ l) = (weilToGK Bw h σ : GQ l)) (ha : alpha l σ' = alpha l σ)
    (y : WDSpace P ι ρ) :
    resEquiv P ρ hle ι (wdRho P ι Bw h hj ρ σ y) =
      wdRho P ι Bw' h' hj' (GlobalTheory.Pst.resTo ρ hle) σ' (resEquiv P ρ hle ι y) := by
  have : (resEquiv P ρ hle ι).toLinearMap ∘ₗ wdRho P ι Bw h hj ρ σ =
      wdRho P ι Bw' h' hj' (GlobalTheory.Pst.resTo ρ hle) σ' ∘ₗ (resEquiv P ρ hle ι).toLinearMap :=
    wdHom_ext P ρ ι fun x => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, wdRho_mk, resEquiv_mk, toRes_weilD P ρ hle σ σ' hg ha]
  exact LinearMap.congr_fun this y

end Weil

theorem wdSpace_resTo_equiv : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (ι : Qbar l ≃+* ℂ) (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : Formalism.ConjugateSelfDual.IsPlaceOver A v) (h' : Formalism.ConjugateSelfDual.IsPlaceOver A v') (O O' : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O'] (Bw : LocBridge l K Ω (ReciprocityTheory.Gal.Dec (F := K) A) O) (Bw' : LocBridge l L Ω (ReciprocityTheory.Gal.Dec (F := L) A) O') (hj : GlobalTheory.Pst.Induces Bw) (hj' : GlobalTheory.Pst.Induces Bw') (hle : Bw.Kw.1 ≤ Bw'.Kw.1), (∀ (σ : Weil h) (σ' : Weil h'), (∀ z : Ω, (σ : Formalism.ConjugateSelfDual.G K Ω) z = (σ' : Formalism.ConjugateSelfDual.G L Ω) z) → (weilToGK Bw' h' σ' : GQ l) = (weilToGK Bw h σ : GQ l)) → ∀ (LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (GlobalTheory.Pst.resTo ρ hle))], IsPst P ρ → ∃ e : WDSpace P ι ρ ≃ₗ[ℂ] WDSpace P ι (GlobalTheory.Pst.resTo ρ hle), (∀ (σ : Weil h) (σ' : Weil h'), (∀ z : Ω, (σ : Formalism.ConjugateSelfDual.G K Ω) z = (σ' : Formalism.ConjugateSelfDual.G L Ω) z) → ∀ x, e (wdRho P ι Bw h hj ρ σ x) = wdRho P ι Bw' h' hj' (GlobalTheory.Pst.resTo ρ hle) σ' (e x)) ∧ ∀ x, e (wdN P ι ρ x) = wdN P ι (GlobalTheory.Pst.resTo ρ hle) (e x) := by
  intro l _ P ι K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' O O' _ _ _ _ _ _ Bw Bw' hj hj' hle hW LL V _ _ _ _ _ ρ _ _ _
  exact ⟨resEquiv P ρ hle ι, fun σ σ' hσ x =>
    resEquiv_wdRho P ρ hle ι hj hj' σ σ' (hW σ σ' hσ) (alpha_eq hj hj' σ σ' hσ) x,
    fun x => resEquiv_wdN P ρ hle ι x⟩

end GlobalTheory.Pst.ResLetter
end
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.periodDatum_frobenius_restrict_hostField : ∀ (D : D7) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (c : D.host.E →+* ↥K.1), l ∉ D.host.small → l ≠ D.host.q → l ≠ D.host.d → ∀ (x : D.host.E) (y : ↥(K0 K)), algebraMap ↥(K0 K) ↥K.1 y = c x → algebraMap ↥(K0 K) ↥K.1 ((P.PD K).σ y) = c (D.host.sigmaOf (DV.frobG D l) x) := by
  first | exact @GlobalTheory.FrobPeriod.periodFrob_restrict | exact GlobalTheory.FrobPeriod.periodFrob_restrict | (intros; apply GlobalTheory.FrobPeriod.periodFrob_restrict <;> assumption)
end

section


theorem _root_.GlobalTheory.T.localNormalization_integral_scalar : Formalism.L2.AlgTh.LocNormScale := by
  first | exact @GlobalTheory.locNormScale | exact GlobalTheory.locNormScale | (intros; apply GlobalTheory.locNormScale <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.TwTop

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV
open _root_.Formalism.L2.Col (Fields Primes Chars LocCst rowSG ChPt Sp HomE PhiTopG prXpG inFr frsF frsG
  cOf ftY atNL repY XiTop phiT)

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

def topF {u : Pr.Word} (i : ℕ) (P : rowSG Pr sel mu) (p : ChPt (R := R) sel mu u i) (Y : Set (Sp X.E (R.N i)))
    (p' : ChPt (R := R) sel mu u (i + 1)) (x : HomE X.E (R.N i) (R.N (i + 1))) : X.K :=
  PhiTopG Ch mu cst.sharp i (i + 1) (R.N (i + 1)) P.1 (prXpG X.E (R.N (i + 1)) ∘ₗ inFr (frsF sel mu p P) (frsG sel mu p' P) x ∘ₗ
      LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R i))) *
    ftY sel mu cst P (atNL X.E (R.N (i + 1)) (R.N (i + 1) - 1) ∘ₗ inFr (frsF sel mu p P) (frsG sel mu p' P) x) ((frsF sel mu p P).symm (repY Y))

theorem xiTop_eq_prod {u : Pr.Word} (i : ℕ) (p : ChPt (R := R) sel mu u i) (Y : Set (Sp X.E (R.N i)))
    (p' : ChPt (R := R) sel mu u (i + 1)) (x : HomE X.E (R.N i) (R.N (i + 1))) :
    XiTop Ch sel mu cst i p Y p' x = phiT X.K p.deco.1 p'.deco.1 x * ∏ P, topF Ch sel mu cst i P p Y p' x := rfl

end GlobalTheory.TwTop

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.TopStep

noncomputable section

namespace GlobalTheory.AwayMat

theorem muAt_det_congr_one : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    X.AbelianUnramifiedExtensionConditions → Pr.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → ∀ (i : ℕ) (P : rowSG Pr sel mu) (n : ℕ) (k : Sp X.E n ≃ₗ[X.E] Sp X.E n),
    (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.D P)⁻¹ * (k (Pi.single s (1 : X.E)) l - (Pi.single s (1 : X.E) : Sp X.E n) l))) →
    muAt Ch sel mu cst i P ((LinearEquiv.det k : X.Eˣ) : X.E) = 1 := by
  intro X Pr R Ch sel S mu cst L G m2 _hX _hPr _hsel hL i P n k hk
  have hD : 1 ≤ cst.D P := hL.cst_ok.D_pos P
  have hq : (qOf P.1 : X.E) ≠ 0 := qOf_ne_zero
  set Z : Fin n → Fin n → X.E := fun a b => (qOf P.1 : X.E) ^ (cst.D P - 1) *
    (((qOf P.1 : X.E) ^ cst.D P)⁻¹ * (k (Pi.single b (1 : X.E)) a - (Pi.single b (1 : X.E) : Sp X.E n) a)) with hZ
  set A : Fin n → Fin n → X.E := fun a b => (Pi.single b (1 : X.E) : Sp X.E n) a with hA
  have hZi : ∀ a b, IntAt P.1 (Z a b) := fun a b => (intAt_pow (intAt_nat _) _).mul (hk b a)
  have hAi : ∀ a b, IntAt P.1 (A a b) := fun a b => by
    simp only [hA, Pi.single_apply]
    split_ifs
    · exact intAt_one
    · exact intAt_zero
  have hpow : (qOf P.1 : X.E) * (qOf P.1 : X.E) ^ (cst.D P - 1) = (qOf P.1 : X.E) ^ cst.D P := by
    rw [← pow_succ']
    congr 1
    omega
  have hM : LinearMap.toMatrix (Pi.basisFun X.E (Fin n)) (Pi.basisFun X.E (Fin n)) k.toLinearMap =
      Matrix.of fun a b => A a b + (qOf P.1 : X.E) * Z a b := by
    ext a b
    rw [LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr, Matrix.of_apply, hZ, hA]
    simp only
    rw [← mul_assoc, hpow, mul_inv_cancel_left₀ (pow_ne_zero _ hq)]
    simp
  have hdet : ((LinearEquiv.det k : X.Eˣ) : X.E) = Matrix.det (Matrix.of fun a b => A a b + (qOf P.1 : X.E) * Z a b) := by
    rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix (Pi.basisFun X.E (Fin n)), hM]
  have hA1 : (Matrix.of fun a b => A a b) = 1 := by
    ext a b
    simp [hA, Pi.single_apply, Matrix.one_apply, eq_comm]
  have hred : redP P.1 ((LinearEquiv.det k : X.Eˣ) : X.E) = redP P.1 (1 : X.E) := by
    rw [hdet, LastSteps.redP_det_add_q hAi hZi, hA1, Matrix.det_one]
  have h1 : IsUnit (redP P.1 (1 : X.E)) := by
    rw [reduction_one₂]
    exact isUnit_one
  have hu : IsUnit (redP P.1 ((LinearEquiv.det k : X.Eˣ) : X.E)) := hred ▸ h1
  unfold muAt
  rw [LastSteps.locChar_unit _ _ hu, LastSteps.unitV_congr _ hred]
  unfold LocE.unitV
  rw [dite_eq_left h1, show h1.unit = 1 from Units.ext reduction_one₂, map_one, Units.val_one]

end GlobalTheory.AwayMat
end
end

section

open NumberField IsDedekindDomain Matrix

namespace GlobalTheory.Proof.mem_integralGLAtPrime_of_congruent_one_mod_pow

open _root_.Formalism.L2.Col (GLint qOf stdAt IntAt Sp mem_localization_standardLattice)

variable {E : Type} [Field E] [NumberField E]

theorem intAt_iff_mem (P : HeightOneSpectrum (𝓞 E)) (a : E) :
    IntAt P a ↔ a ∈ (P.valuation E).integer := by
  rw [GlobalTheory.Proof.IntegralPowerExpansion.intAt_iff_val, Valuation.mem_integer_iff]

theorem mem_stdAt {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (x : Sp E n) :
    x ∈ stdAt E n P ↔ ∀ i, IntAt P (x i) := by
  letI : StarRing E := starRingOfComm
  exact mem_localization_standardLattice P x

theorem intAt_mulVec (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (A : Matrix (Fin n) (Fin n) E)
    (hA : ∀ a b, IntAt P (A a b)) (w : Fin n → E) (hw : ∀ i, IntAt P (w i)) (i : Fin n) :
    IntAt P ((A *ᵥ w) i) := by
  rw [intAt_iff_mem]
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ =>
    Subring.mul_mem _ ((intAt_iff_mem P _).1 (hA i j)) ((intAt_iff_mem P _).1 (hw j))

theorem qOf_ne_zero (P : HeightOneSpectrum (𝓞 E)) : (qOf P : E) ≠ 0 := by
  rw [Nat.cast_ne_zero, qOf, Ne, Ideal.absNorm_eq_zero_iff]
  exact P.ne_bot

theorem intAt_of_cong (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (d : ℕ) (M : Matrix (Fin n) (Fin n) E)
    (h : ∀ a b, IntAt P (((qOf P : E) ^ d)⁻¹ * (M a b - (1 : Matrix (Fin n) (Fin n) E) a b))) (a b : Fin n) :
    IntAt P (M a b) := by
  have hq : ((qOf P : E) ^ d) ≠ 0 := pow_ne_zero _ (qOf_ne_zero P)
  have e : M a b = (1 : Matrix (Fin n) (Fin n) E) a b +
      (qOf P : E) ^ d * (((qOf P : E) ^ d)⁻¹ * (M a b - (1 : Matrix (Fin n) (Fin n) E) a b)) := by
    field_simp
    ring
  rw [e, intAt_iff_mem]
  refine Subring.add_mem _ ?_ (Subring.mul_mem _ ?_ ((intAt_iff_mem P _).1 (h a b)))
  · rw [Matrix.one_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  · exact Subring.pow_mem _ (natCast_mem _ _) _

theorem map_stdAt (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (f : Sp E n →ₗ[E] Sp E n)
    (hf : ∀ a b, IntAt P (LinearMap.toMatrix' f a b)) {x : Sp E n} (hx : x ∈ stdAt E n P) :
    f x ∈ stdAt E n P := by
  rw [mem_stdAt] at hx ⊢
  intro i
  rw [← LinearMap.toMatrix'_mulVec]
  exact intAt_mulVec P _ hf x hx i

theorem glint_of_cong {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (d : ℕ) (g : Sp E n ≃ₗ[E] Sp E n)
    (hg : ∀ a b, IntAt P (((qOf P : E) ^ d)⁻¹ *
      (LinearMap.toMatrix' g.toLinearMap a b - (1 : Matrix (Fin n) (Fin n) E) a b)))
    (hg' : ∀ a b, IntAt P (((qOf P : E) ^ d)⁻¹ *
      (LinearMap.toMatrix' g.symm.toLinearMap a b - (1 : Matrix (Fin n) (Fin n) E) a b))) :
    g ∈ GLint E n P ∧ ∀ w ∈ stdAt E n P, ((qOf P : E) ^ d)⁻¹ • (g w - w) ∈ stdAt E n P := by
  refine ⟨fun x => ⟨fun hx => ?_, fun hx => map_stdAt P g.toLinearMap (intAt_of_cong P d _ hg) hx⟩, ?_⟩
  · have := map_stdAt P g.symm.toLinearMap (intAt_of_cong P d _ hg') hx
    simpa using this
  · intro w hw
    set A : Matrix (Fin n) (Fin n) E :=
      ((qOf P : E) ^ d)⁻¹ • (LinearMap.toMatrix' g.toLinearMap - (1 : Matrix (Fin n) (Fin n) E)) with hA
    have hAi : ∀ a b, IntAt P (A a b) := by
      intro a b
      simpa [hA, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] using hg a b
    have e : ((qOf P : E) ^ d)⁻¹ • (g w - w) = A *ᵥ w := by
      have h1 : (g w : Sp E n) = LinearMap.toMatrix' g.toLinearMap *ᵥ w := by
        rw [LinearMap.toMatrix'_mulVec]; rfl
      rw [hA, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ← h1]
    rw [e, mem_stdAt]
    rw [mem_stdAt] at hw
    exact intAt_mulVec P _ hAi w hw

end GlobalTheory.Proof.mem_integralGLAtPrime_of_congruent_one_mod_pow
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

theorem _root_.GlobalTheory.T.blockDetResidueChar_eq_one_of_cong_mod_q : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (kj n N : ℕ) (g : HomE E N N), n ≤ N → (∀ x ∈ stdAt E N P, (qOf P : E)⁻¹ • (g x - x) ∈ stdAt E N P) → LocE.lamQB ξ kj n g = 1 := by
  first | exact @GlobalTheory.LamQBCong.lamQB_eq_one_of_cong | exact GlobalTheory.LamQBCong.lamQB_eq_one_of_cong | (intros; apply GlobalTheory.LamQBCong.lamQB_eq_one_of_cong <;> assumption)
end

section

open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial

theorem _root_.GlobalTheory.T.card_ker_subspaces_and_heckePolyOf_convolution : (∀ (k U U' : Type) [Field k] [Fintype k] [AddCommGroup U] [Module k U] [FiniteDimensional k U] [AddCommGroup U'] [Module k U'] [FiniteDimensional k U'] (n t d : ℕ) (f : U →ₗ[k] U'), Module.finrank k U = n + t → Module.finrank k U' = n → Nat.card {W : Submodule k U // Module.finrank k W + d = n + t ∧ W ≤ LinearMap.ker f} = ∑ j ∈ Finset.range (d + 1), Fintype.card k ^ ((n - j) * (d - j)) * gaussBin (Fintype.card k) t (d - j) * Nat.card {W' : Submodule k U' // Module.finrank k W' = j ∧ LinearMap.range f ≤ W'}) ∧ ∀ (L : Type) [Field L] (q n t : ℕ) (a : ℕ → L) (ν s : L), (∀ j, n < j → a j = 0) → heckePolyOf (n + t) q (fun d => ∑ j ∈ Finset.range (d + 1), (q : L) ^ ((n - j) * (d - j)) * (gaussBin q t (d - j) : L) * ν ^ (d - j) * s ^ j * a j) = (heckePolyOf n q a).comp (C s * X) * blockPoly (ν * (q : L) ^ n) q t := by
  first | exact @GlobalTheory.KerRangeCount.card_ker_and_heckePolyOf_conv | exact GlobalTheory.KerRangeCount.card_ker_and_heckePolyOf_conv | (intros; apply GlobalTheory.KerRangeCount.card_ker_and_heckePolyOf_conv <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

theorem _root_.GlobalTheory.T.localNormalisation_transport_isometry : ∀ (a₀ : ℕ) (b₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (θ : (n → ℂ) → ℂ) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (φ : (n → ℂ) ≃ₗ[ℂ] (n → ℂ)), IsIsom (matH h) (matH h) (φ : (n → ℂ) →ₗ[ℂ] (n → ℂ)) → LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ p ι → LocNorm a₀ b₀ dK ha hdK lam hlam h (Λ.comap φ.toLinearMap.toAddMonoidHom) (fun z => θ (φ z)) p ι := by
  first | exact @GlobalTheory.ThLoc.LocPull.locNorm_pull | exact GlobalTheory.ThLoc.LocPull.locNorm_pull | (intros; apply GlobalTheory.ThLoc.LocPull.locNorm_pull <;> assumption)
end
