module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1134
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle051
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle848
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1067
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle117
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle158
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothVecLowKSub
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.SchurLatticeConjugates
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1123
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankRiemannRochNsmulHyperplane
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1124
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
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
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle783
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle002
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle010
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.CmpbHessAtAddConst
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt.NatGlue

variable (R : Type) [CommRing R] {D : Type} [CommRing D] [Algebra R D]

def locMap (s : D) : D →ₐ[R] Localization.Away s := IsScalarTower.toAlgHom R D _

theorem locMap_apply (s x : D) : locMap R s x = algebraMap D (Localization.Away s) x := rfl

def locR (a b : D) : Localization.Away a →ₐ[R] Localization.Away (a * b) :=
  ⟨IsLocalization.Away.awayToAwayRight a b, fun r ↦ by
    have := IsLocalization.Away.awayToAwayRight_eq (S := Localization.Away a) (P := Localization.Away (a * b))
      a b (algebraMap R D r)
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this
    exact this⟩

def locL (a b : D) : Localization.Away b →ₐ[R] Localization.Away (a * b) :=
  ⟨IsLocalization.Away.awayToAwayLeft b a, fun r ↦ by
    have := IsLocalization.Away.awayToAwayLeft_eq (S := Localization.Away b) (P := Localization.Away (a * b))
      b a (algebraMap R D r)
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this
    exact this⟩

theorem locR_apply (a b : D) (x : Localization.Away a) :
    locR R a b x = IsLocalization.Away.awayToAwayRight a b x := rfl

theorem locL_apply (a b : D) (x : Localization.Away b) :
    locL R a b x = IsLocalization.Away.awayToAwayLeft b a x := rfl

theorem locR_comp (a b : D) : (locR R a b).comp (locMap R a) = locMap R (a * b) := by
  ext x
  rw [AlgHom.comp_apply, locR_apply, locMap_apply, locMap_apply]
  exact IsLocalization.Away.awayToAwayRight_eq a b x

theorem locL_comp (a b : D) : (locL R a b).comp (locMap R b) = locMap R (a * b) := by
  ext x
  rw [AlgHom.comp_apply, locL_apply, locMap_apply, locMap_apply]
  exact IsLocalization.Away.awayToAwayLeft_eq b a x

theorem awayMap_comp {E : Type} [CommRing E] [Algebra R E] (φ : D →ₐ[R] E) (s : D) :
    (IsScalarTower.toAlgHom R E (Localization.Away (φ s))).comp φ = (Localization.awayMapₐ φ s).comp (locMap R s) := by
  ext x
  rw [AlgHom.comp_apply, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, locMap_apply]
  first
    | exact (IsLocalization.Away.map_eq (S := Localization.Away s) (P := Localization.Away (φ s)) s x).symm
    | simp [Localization.awayMapₐ, IsLocalization.Away.mapₐ, IsLocalization.Away.map, IsLocalization.map_eq]
    | (show _ = IsLocalization.map _ (φ : D →+* E) _ _; exact (IsLocalization.map_eq _ _).symm)

theorem existsUnique_of_natural : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens),
    ⨆ i, W i = ⊤ → ∀ (D : Type) [CommRing D] [Algebra R D] (y : Pt X D)
    (τ : ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E),
    (∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : D →ₐ[R] E)
      (θ : E →ₐ[R] E'), Sm W (D := E) (spOver ψ ≫ y) → τ E' (θ.comp ψ) = θ (τ E ψ)) →
    ∃! d : D, ∀ (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E),
      Sm W (D := E) (spOver ψ ≫ y) → τ E ψ = ψ d := by
  apply GlobalTheory.PtExt.natFamily_existsUnique <;> assumption

end GlobalTheory.PtExt.NatGlue
end
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal
open Formalism.L2.Host (HChar)

namespace GlobalTheory.HeckeStrip

theorem completedLBoundedInStrips : GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.CompletedLBoundedInStrips := by
  intro E _ _ _ I _ φ hφ χ n hu hi hn
  obtain ⟨m, X, hm, hX0, hX1, hXm, hXn, hXz, hXP, hXβ⟩ := GlobalTheory.T.exists_idealCharacter_of_unitary_heckeChar E χ hu
  have hβ : ∀ β : 𝓞 E, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = wt φ n (β : E) := by
    intro β h0 h1
    have h0' : (β : E) ≠ 0 := by exact_mod_cast h0
    rw [hXβ β (Units.mk0 _ h0') rfl h1, hi (Units.mk0 _ h0')]
    simp only [wt, Units.val_mk0, zpow_neg, Finset.prod_inv_distrib]
  have hle : ∀ a, ‖X a‖ ≤ 1 := fun a => by
    by_cases ha : a = ⊥
    · simp [ha, hX0]
    by_cases ha' : a ⊔ m = ⊤
    · exact (hXn a ha ha').le
    · simp [hXz a ha']
  obtain ⟨r, c, B, M, F, hB, hM, hper, hinv, hdec⟩ := GlobalTheory.T.heckeLSeries_eq_sum_principalPartialSeries E I φ n m X hm hX0 hXm hXn hXz hβ
  choose Λ hΛd hΛb hΛe using fun k => GlobalTheory.T.completed_heckePartialLSeries_entire_bounded_strips E I φ hφ n hn (M k) (F k) (hM k) (hper k) (hinv k)
  have hB0 : ∀ k, ((B k : ℕ) : ℂ) ≠ 0 := fun k => by exact_mod_cast (hB k).ne'
  refine ⟨fun s => ∑ k, c k * ((B k : ℕ) : ℂ) ^ s * Λ k s, ⟨?_, fun s hs => ?_⟩, ?_⟩
  · intro s
    refine DifferentiableAt.fun_sum fun k _ => ?_
    exact ((differentiableAt_const _).mul ((differentiableAt_id.const_cpow (Or.inl (hB0 k))))).mul ((hΛd k).differentiableAt)
  · refine ⟨∑' a : Ideal (𝓞 E), X a * ((Ideal.absNorm a : ℕ) : ℂ) ^ (-s), ?_, ?_⟩
    · rw [GlobalTheory.tsum_ideal_mul_absNorm_cpow_eq_exp_tsum E X hX0 hX1 hXm hle s hs]
      convert GlobalTheory.HeckeOne.hasProd_exp hu hs using 1
      simp only [hXP, GlobalTheory.HeckeOne.cf]
    · rw [hdec s hs, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hΛe k s hs]
      ring
  · intro a b hab
    choose C hC using fun k => hΛb k a b hab
    refine ⟨∑ k, ‖c k‖ * ((B k : ℝ) ^ b * |C k|), fun s h1 h2 => ?_⟩
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_mul, mul_assoc, Complex.norm_natCast_cpow_of_pos (hB k)]
    have hB1 : (1 : ℝ) ≤ (B k : ℝ) := by exact_mod_cast hB k
    gcongr
    exact (hC k s h1 h2).trans (le_abs_self _)

end GlobalTheory.HeckeStrip
end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseScalar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem Q_base (h : R.toLevCh.Is A.μ0) : R.Q A.μ0 = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro PP hPP
  refine (h.Q_ram A.μ0 PP).2 (Or.inl hPP) ?_
  rw [h.xi_base]
  intro x _
  rfl

theorem exists_factor {X Y Z : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]
    (e : Y →ₗ[ℂ] Z) (f : X →ₗ[ℂ] Z) (V : Submodule ℂ Z) (hinj : Function.Injective e) (hr : LinearMap.range e = V)
    (hm : ∀ x, f x ∈ V) : ∃ th : X →ₗ[ℂ] Y, ∀ x, e (th x) = f x := by
  subst hr
  refine ⟨(LinearEquiv.ofInjective _ hinj).symm.toLinearMap ∘ₗ f.codRestrict _ hm, fun x => ?_⟩
  have := congrArg Subtype.val ((LinearEquiv.ofInjective _ hinj).apply_symm_apply ⟨f x, hm x⟩)
  rwa [LinearEquiv.ofInjective_apply] at this

theorem integrableOn_of_isThetaLift {G' H' S' Sinf TK Tau X : Type} [MeasurableSpace H'] [AddCommGroup Sinf] [Module ℂ Sinf] [AddCommGroup TK]
    [Module ℂ TK] [AddCommGroup Tau] [Module ℂ Tau] [AddCommGroup X] [Module ℂ X] {ν : Measure H'} {𝓕 : Set H'}
    {th : G' → H' → S' → ℂ} {pt : Sinf → S'} {io : TK →ₗ[ℂ] Tau →ₗ[ℂ] Sinf} {φ : X →ₗ[ℂ] (H' → Tau)}
    {thP : LinearMap.range φ →ₗ[ℂ] TK →ₗ[ℂ] G' → ℂ} (h : Lift.IsThetaP ν 𝓕 th pt io (LinearMap.range φ) thP)
    (x : X) (e : TK) (g : G') :
    IntegrableOn (fun a => th g a (pt (io e (φ x a)))) 𝓕 ν ∧
      thP (φ.rangeRestrict x) e g = Lift.thetaPInt ν 𝓕 th pt io (φ x) e g :=
  ⟨h.integ (φ.rangeRestrict x) e g, h.eq (φ.rangeRestrict x) e g⟩

theorem adjLev_triv {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [FiniteDimensional ℂ X] [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (th : X →ₗ[ℂ] Y) :
    GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.adjLev (D := D) R.triv th = LinearMap.adjoint th := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.adjLev
  have : Nat.card (R.triv).H = 1 := Subgroup.card_bot
  rw [this]; simp

end GlobalTheory.BaseScalar

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix

namespace GlobalTheory.LiftLower

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def csumAt {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) (σ : K →+* ℂ) (f g : S.Forms) : ℂ :=
  star (fun a => σ (S.basis.repr f a)) ⬝ᵥ (S.H.map σ) *ᵥ fun a => σ (S.basis.repr g a)

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

abbrev levSW (i : Fin D.R.m) : Set (GA D (Wc D i)) := levS _ (R.βW i) (R.datWp i R.triv)

abbrev chiW (i : Fin D.R.m) : GA D (Wc D i) → ℂ := Lev.levChi _ (R.βW i) (R.datWp i R.triv)

def partH (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) : Submodule ℂ (R.HW i σ).H :=
  (partFull R.θ (R.MW i σ) (levSW R i) (chiW R i) (GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF R) c).comap (R.HW i σ).e

def IsNormSys (i : Fin D.R.m) (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) : Prop :=
  ∀ P d, (¬ ∃ Rp, Hecke₂ (Wc D i) (levSW R i) (chiW R i) (GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF R) P d Rp) → c P d = 0

def projH (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) : (R.HW i σ).H →ₗ[ℂ] (R.HW i σ).H :=
  ∑ g, RealDat.eC (A := A) σ g • R.gW i σ g


variable (D) in
def hookPlus (i : Fin D.R.m) : ℝ :=
  ∑ ρ : D.what₂.Tau, Real.log (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.pW D i ρ) (aPl D i (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.pW D i ρ) ρ) : ℝ)

variable {R}

theorem Q_base (h : R.toLevCh.Is A.μ0) : R.Q A.μ0 = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro PP hPP
  refine (h.Q_ram A.μ0 PP).2 (Or.inl hPP) ?_
  rw [h.xi_base]
  intro x _
  rfl

theorem typePart_base (h : R.toLevCh.Is A.μ0) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) :
    GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.typePart R i σ A.μ0 R.triv c = partH R i σ c := by
  classical
  have e : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.finS R A.μ0 = GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF R := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.finS GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF
    rw [Q_base h]
    congr 1
    ext; simp
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.typePart partH
  rw [e]

theorem e_projH (h : R.models_gW) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (x : (R.HW i σ).H) :
    (R.HW i σ).e (projH R i σ x) = postOn _ (R.eWf i σ) ((R.HW i σ).e x) := by
  unfold projH RealDat.eWf gaL

  rw [LinearMap.sum_apply, map_sum]
  ext v g
  simp only [LinearMap.smul_apply, map_smul, h i σ, postOn_apply, LinearMap.sum_apply, MultilinearMap.sum_apply,
    MultilinearMap.smul_apply]
  rfl

end GlobalTheory.LiftLower

end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GeoActCompare
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.completedLattice_stabilizer_iff_basis_integral : ∀ (D : D7) (V : HSp D) (r : ℕ) (hr : V.rank = r) (β : GL (Fin r) (EAf D)), LatticeBasisLifts.IsLatBasis V hr β → ∀ κ : GA D V, gLat V κ = (latHat V : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)) ↔ LatticeBasisLifts.finR V hr κ ∈ Formalism.L2.DIV.St β := by
  first | exact @GlobalTheory.LatStab.gLat_eq_latHat_iff | exact GlobalTheory.LatStab.gLat_eq_latHat_iff | (intros; apply GlobalTheory.LatStab.gLat_eq_latHat_iff <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.LowTypeRestriction

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult
  Formalism.IndefR.Datum Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def DeterminedByLowTypes : Prop :=
  ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (θ : InfFam D), IsInfFam θ →
    (∀ τ, lowT M τ ≠ ⊥) → ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ T ∈ Mult θ M J χ,
      (∀ v : ∀ ρ, lowT M ρ, T (fun ρ => v ρ) = 0) → T = 0

theorem resInj_of_determined (h : DeterminedByLowTypes) : GlobalTheory.IndefiniteRowSideFullHecke.ResidueInjectivityAt.ResInj :=
  fun D _ _ _ _ _ _ _ _ _ _ R hθ i U hU hv =>
    h D _ _ (R.MW i _) R.θ hθ (lowT_ne_bot _) _ _ U hU hv

end GlobalTheory.LowTypeRestriction

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine

theorem _root_.GlobalTheory.T.abs_logRootDisc_sub_log_hostPrime_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), |GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E - Real.log H.d| ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E := by
  first | exact @GlobalTheory.abs_lrd_sub_log_d_le_lrd | exact GlobalTheory.abs_lrd_sub_log_d_le_lrd | (intros; apply GlobalTheory.abs_lrd_sub_log_d_le_lrd <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix

theorem _root_.GlobalTheory.T.finiteAdelicGL_mem_integral_cofinite_places : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (k : GL (Fin a) (Af E)), {w : HeightOneSpectrum (𝓞 E) | GeneralLinearGroup.map (pLoc E w) k ∉ KGL w (n := a)}.Finite := by
  first | exact @GlobalTheory.GLFinPlaces.gl_mem_int_cofinite | exact GlobalTheory.GLFinPlaces.gl_mem_int_cofinite | (intros; apply GlobalTheory.GLFinPlaces.gl_mem_int_cofinite <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix

theorem _root_.GlobalTheory.T.smoothAutomorphicForm_fixed_of_locally_integral_fixed : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsAutForm φ → ∀ S : Finset (HeightOneSpectrum (𝓞 E)), (∀ w ∉ S, ∀ k ∈ KGL w (n := a), act (.fin (locGL E a w k)) φ = φ) → ∀ k : GL (Fin a) (Af E), (∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) k ∈ KGL w (n := a)) → (∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) k = 1) → act (.fin k) φ = φ := by
  first | exact @GlobalTheory.CuspRep.fixed_of_locFixed | exact GlobalTheory.CuspRep.fixed_of_locFixed | (intros; apply GlobalTheory.CuspRep.fixed_of_locFixed <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.ChernDegree

theorem inter_const_eq_topSelf_of_presents :
    ∀ (Y : Var ℂ) (Δ : Y.Dv) (L : LB Y.X) (r : L.ι → Y.Fnˣ), L.IsLB → Presents Δ L r → Y.inter (fun _ => Δ) = topSelfIntersection ℂ L Y.dim :=
  fun _ _ _ _ hL h => Var.inter_eq_of_toPic_eq (fun _ => hL) fun _ => h.toPic_eq

end GlobalTheory.ChernDegree
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
open ReciprocityTheory.L2DbarEstimates (V cHess)
open GlobalTheory.ChartGlue
open scoped ContDiff

namespace GlobalTheory.ChernIso

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
  {A B : LB X} {φ : Weight p σ B} {D : ℕ}

theorem cInfAt_log_normSq {W : X.Opens} (g : Γ(X, W)) {y : CxPts p σ} (hy : y ∈ ptsIn p σ W)
    (h0 : ev p σ W g y ≠ 0) : CInfAt (fun z => Real.log (‖ev p σ W g z‖ ^ 2)) y := by
  have hs : ContDiff ℝ ∞ fun v : Unit → ℂ => ‖v ()‖ ^ 2 := (contDiff_apply ℝ (fun _ => ℂ) ()).norm_sq ℂ
  refine ⟨W, Unit, inferInstance, fun _ => g, fun v => Real.log (‖v ()‖ ^ 2),
    {v | ‖v ()‖ ^ 2 ≠ 0}, hy, isOpen_ne_fun hs.continuous continuous_const,
    pow_ne_zero _ (norm_ne_zero_iff.2 h0), hs.contDiffOn.log fun _ h => h, EventuallyEq.rfl⟩

theorem ofIso_apply (hA : A.IsLB) (w : LB.Iso B A) (hw : w.IsGen) {a : A.ι} {b : B.ι}
    {y : CxPts p σ} (ha : y ∈ ptsIn p σ (A.U a)) (hb : y ∈ ptsIn p σ (B.U b)) :
    (φ.ofIso hA w hw).φ a y = φ.φ b y + Real.log (‖ev p σ _ (w.s (a, b)).val y‖ ^ 2) := by
  rw [Weight.ofIso, Weight.ofPairs_φ ha hb]

theorem isCInf_ofIso (h : φ.IsCInf) (hA : A.IsLB) (w : LB.Iso B A) (hw : w.IsGen) :
    (φ.ofIso hA w hw).IsCInf := fun a y ha => by
  have hb := mem_pick φ.isLB y
  refine ((h _ y hb).add (cInfAt_log_normSq (w.s (a, pick φ.isLB y)).val
    (mem_ptsIn_inf.2 ⟨ha, hb⟩) (ev_iso_ne_zero w hb ha))).congr ?_
  filter_upwards [(isOpen_ptsIn _).mem_nhds ha, (isOpen_ptsIn _).mem_nhds hb] with z h₁ h₂
  exact ofIso_apply hA w hw h₁ h₂

theorem hess_ofIso (h : φ.IsCInf) (hA : A.IsLB) (w : LB.Iso B A) (hw : w.IsGen)
    (c : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source) {a : A.ι} {b : B.ι}
    (ha : y ∈ ptsIn p σ (A.U a)) (hb : y ∈ ptsIn p σ (B.U b)) :
    c.hess (φ.ofIso hA w hw) a y = c.hess φ b y := by
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (A.U a ⊓ B.U b))
  have hm := mem_over c.e hy (mem_ptsIn_inf.2 ⟨ha, hb⟩)
  have hg := c.holo (A.U a ⊓ B.U b) (w.s (a, b)).val
  have h0 : ∀ v ∈ c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (A.U a ⊓ B.U b),
      (ev p σ (A.U a ⊓ B.U b) (w.s (a, b)).val ∘ c.e.symm) v ≠ 0 := fun v hv =>
    ev_iso_ne_zero w (mem_ptsIn_inf.1 hv.2).2 (mem_ptsIn_inf.1 hv.2).1
  have e := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho
    ((contDiffOn_chart (h b) c).mono fun v hv => ⟨hv.1, (mem_ptsIn_inf.1 hv.2).2⟩)
    (contDiffOn_log_normSq ho hg h0) 1 hm
  have e₀ : cHess D (fun v => ((Real.log (‖(ev p σ (A.U a ⊓ B.U b) (w.s (a, b)).val ∘
      c.e.symm) v‖ ^ 2) : ℝ) : ℂ)) (c.e y) = 0 := by
    ext i j
    exact ReciprocityTheory.L2DbarEstimates.Y.cmpa_hess_log ho hm hg h0 i j
  rw [e₀, smul_zero, add_zero] at e
  refine Eq.trans (ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr ?_) e
  filter_upwards [ho.mem_nhds hm] with v hv
  rw [ofIso_apply hA w hw (mem_ptsIn_inf.1 hv.2).1 (mem_ptsIn_inf.1 hv.2).2, one_mul]
  rfl

theorem chernPart_ofIso (h : φ.IsCInf) (hA : A.IsLB) (w : LB.Iso B A) (hw : w.IsGen) (ε : ℤˣ) :
    (φ.ofIso hA w hw).chernPart D ε = φ.chernPart D ε := by
  refine iSup_congr fun c => Measure.ext fun S hS => ?_
  rw [chartMeas_apply _ _ hS, chartMeas_apply _ _ hS]
  refine setLIntegral_congr_fun (measurableSet_image c.e
    (c.e.open_source.measurableSet.inter hS) inter_subset_left) ?_
  rintro _ ⟨y, hy, rfl⟩
  simp only [c.e.left_inv hy.1]
  rw [AlgChart.chernDens, AlgChart.chernDens,
    hess_ofIso h hA w hw c hy.1 (mem_pick _ y) (mem_pick φ.isLB y)]

theorem chernInt_ofIso (h : φ.IsCInf) (hA : A.IsLB) (w : LB.Iso B A) (hw : w.IsGen)
    (S : Set (CxPts p σ)) (f : CxPts p σ → ℝ) :
    (φ.ofIso hA w hw).chernInt D S f = φ.chernInt D S f := by
  rw [Weight.chernInt, Weight.chernInt, chernPart_ofIso h, chernPart_ofIso h]

theorem chernMass_ofIso : ∀ (Y : Var ℂ) (L A : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L)
    (hA : A.IsLB) (w : L.Iso A) (hw : w.IsGen), φ.IsCInf → (φ.ofIso hA w hw).IsCInf ∧
      Weight.chernInt (φ.ofIso hA w hw) Y.dim Set.univ (fun _ => 1) =
        Weight.chernInt φ Y.dim Set.univ (fun _ => 1) :=
  fun _ _ _ _ hA w hw h => ⟨isCInf_ofIso h hA w hw, chernInt_ofIso h hA w hw _ _⟩

end GlobalTheory.ChernIso
end

section

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal

theorem _root_.GlobalTheory.T.rankGrowthLimsup_of_eventually_polynomial : ∀ (D a : ℕ) (h : ℕ → ℕ) (H : Polynomial ℚ), 1 ≤ a → (∀ᶠ n : ℕ in atTop, (h n : ℚ) = H.eval (n : ℚ)) → (H.degree ≤ D → ∀ δ : ℕ, (δ : ℚ) = (D.factorial : ℚ) * H.coeff D → growth D (fun k => (h (a * k) : ℕ∞)) = (a : ℝ≥0∞) ^ D * δ) ∧ ((D : WithBot ℕ) < H.degree → growth D (fun k => (h (a * k) : ℕ∞)) = ⊤) := by
  first | exact @GlobalTheory.CompHt.growth_of_eventually_eq_eval | exact GlobalTheory.CompHt.growth_of_eventually_eq_eval | (intros; apply GlobalTheory.CompHt.growth_of_eventually_eq_eval <;> assumption)
end
