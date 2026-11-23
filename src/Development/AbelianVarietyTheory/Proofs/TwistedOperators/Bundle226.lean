module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle219
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle220
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle035
import GroundTheory.GlobalFields.TateThesis.Bundle001
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle213
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle125
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle219
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle204
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle143
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec.TensLawOf

section

variable {p q r s : ℕ}

theorem cJoint_swap {σ : Type} (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ))
    (a₂ : Mat r s →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (Λ₁ : Ix p q → ℚ) (Λ₂ : Ix r s → ℚ)
    (Φ : MvPolynomial σ ℂ) (h : CJoint a₁ a₂ Λ₁ Λ₂ Φ) : CJoint a₂ a₁ Λ₂ Λ₁ Φ := by
  obtain ⟨⟨d, h0, h1, h2⟩, h3, h4⟩ := h
  exact ⟨⟨d, h0, h2, h1⟩, h4, h3⟩

theorem tIntw_swap {W : Type} [AddCommGroup W] [Module ℂ W] (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ W)
    (a₂ : Mat r s →ₗ[ℂ] Module.End ℂ W) (M₁ : GKMod p q) (M₂ : GKMod r s) (f : W →ₗ[ℂ] M₁.V ⊗[ℂ] M₂.V)
    (h : TIntw a₁ a₂ M₁ M₂ f) :
    TIntw a₂ a₁ M₂ M₁ ((TensorProduct.comm ℂ M₁.V M₂.V).toLinearMap ∘ₗ f) := by
  constructor
  · intro Y
    rw [LinearMap.comp_assoc, h.2 Y, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc]
    congr 1
    ext x y
    simp
  · intro Y
    rw [LinearMap.comp_assoc, h.1 Y, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc]
    congr 1
    ext x y
    simp

theorem comm_comp_inj {W A B : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] {f g : W →ₗ[ℂ] A ⊗[ℂ] B}
    (h : (TensorProduct.comm ℂ A B).toLinearMap ∘ₗ f = (TensorProduct.comm ℂ A B).toLinearMap ∘ₗ g) : f = g := by
  refine LinearMap.ext fun x => ?_
  exact (TensorProduct.comm ℂ A B).injective (LinearMap.congr_fun h x)

theorem range_swap {W A B C : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C] (f : W →ₗ[ℂ] A ⊗[ℂ] B) (j : C →ₗ[ℂ] B)
    (h : LinearMap.range ((TensorProduct.comm ℂ A B).toLinearMap ∘ₗ f) =
      LinearMap.range (TensorProduct.map j (LinearMap.id : A →ₗ[ℂ] A))) :
    LinearMap.range f = LinearMap.range (TensorProduct.map (LinearMap.id : A →ₗ[ℂ] A) j) := by
  have e : (TensorProduct.comm ℂ A B).toLinearMap ∘ₗ TensorProduct.map (LinearMap.id : A →ₗ[ℂ] A) j =
      TensorProduct.map j (LinearMap.id : A →ₗ[ℂ] A) ∘ₗ (TensorProduct.comm ℂ A C).toLinearMap := by
    ext x y
    simp
  apply Submodule.map_injective_of_injective (f := (TensorProduct.comm ℂ A B).toLinearMap)
    (TensorProduct.comm ℂ A B).injective
  rw [← LinearMap.range_comp, ← LinearMap.range_comp, h, e,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]

end

theorem tensLaw_of : ∀ (X : ProvA) (p q r s : ℕ) (lam : Ix p q → ℚ) (lam' : Ix r s → ℚ), ARi X lam lam' → ARiiiUp X lam lam' → ARiiiDown X lam lam' → ARiiiLine X lam lam' → TensLaw (fockAct1 p q r s) (fockAct2 p q r s) (X.ds p q lam) (X.ds r s lam') (blattner lam) (blattner lam') ∧ TensLaw (fockAct2 p q r s) (fockAct1 p q r s) (X.ds r s lam') (X.ds p q lam) (blattner lam') (blattner lam) := by
  intro X p q r s lam lam' h1 hU hD hL
  obtain ⟨hiff, hnorm, huniq⟩ := GlobalTheory.T.fockModel_jointHarmonics_form_normalisation_uniqueness X p q r s (blattner lam) (blattner lam')
  obtain ⟨Φ₀, hΦ₀⟩ := h1.1
  have hex : CJoint (fockAct1 p q r s) (fockAct2 p q r s) (blattner lam) (blattner lam') Φ₀ :=
    (hiff Φ₀).2 ⟨hΦ₀.1, hΦ₀.2.1, hΦ₀.2.2.1⟩
  refine ⟨⟨⟨Φ₀, hex⟩, huniq, ?_, hL⟩, ⟨⟨Φ₀, cJoint_swap _ _ _ _ _ hex⟩,
    fun Φ Φ' h h' => huniq Φ Φ' (cJoint_swap _ _ _ _ _ h) (cJoint_swap _ _ _ _ _ h'), ?_, ?_⟩⟩
  · intro MM f hf hf0
    obtain ⟨⟨N, -, e, he⟩, hΦ⟩ := hU MM f hf hf0
    refine ⟨⟨N, e, he⟩, fun Φ hJ => ?_⟩
    obtain ⟨c, -, hc⟩ := hnorm Φ hJ
    obtain ⟨g1, g2⟩ := hΦ _ hc
    refine ⟨fun h0 => g1 (by rw [map_smul, h0, smul_zero]), fun f' hf' h => g2 f' hf' ?_⟩
    rw [map_smul, map_smul, h]
  · intro MM f hf hf0
    have hf1 := tIntw_swap _ _ _ _ f hf
    obtain ⟨⟨N, -, e, he, hr⟩, hΦ⟩ := hD MM _ hf1
      (fun h => hf0 (comm_comp_inj (by rw [h, LinearMap.comp_zero])))
    refine ⟨⟨N, e, he, range_swap f _ hr⟩, fun Φ hJ => ?_⟩
    obtain ⟨c, -, hc⟩ := hnorm Φ (cJoint_swap _ _ _ _ _ hJ)
    obtain ⟨g1, g2⟩ := hΦ _ hc
    refine ⟨fun h0 => g1 (by rw [map_smul, LinearMap.comp_apply, h0, map_zero, smul_zero]), fun f' hf' h =>
      comm_comp_inj (g2 _ (tIntw_swap _ _ _ _ f' hf') ?_)⟩
    rw [map_smul, map_smul, LinearMap.comp_apply, LinearMap.comp_apply, h]
  · obtain ⟨f₀, hf₀, hne, hall⟩ := hL
    refine ⟨_, tIntw_swap _ _ _ _ f₀ hf₀,
      fun h => hne (comm_comp_inj (by rw [h, LinearMap.comp_zero])), fun f hf => ?_⟩
    obtain ⟨c, hc⟩ := hall _ (tIntw_swap _ _ _ _ f hf)
    refine ⟨c, comm_comp_inj ?_⟩
    rw [hc]
    refine LinearMap.ext fun x => ?_
    simp

end GlobalTheory.ArchRec.TensLawOf

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

theorem _root_.GlobalTheory.T.exists_kFiniteIsometry_discreteSeriesModel_detCover : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (p q : ℕ) (T : GrpData p q) (R : DSRep T) (lam : Ix p q → ℚ) (c : ℚ) (br cj : Bool) (e : Ix p q ≃ Fin V.rank) (m : ℤ) (U : M.H τ → R.U.H), IsParam lam → IsOrd (M.ε τ) (M.lam τ) lam c (sg br cj) e → (m : ℚ) = 2 * c → Comparison₂ R M τ br cj e m U → (∀ x v, U x = R.ι v → (IsHighestUnit (M.ε τ) (M.lam τ) (M.σ τ) x ↔ UnitHW R (blattner lam) v)) → ∃ u, KTie R M τ lam c br cj e u := by
  first | exact @GlobalTheory.ArchRec.KFiniteTie.exists_kTie | exact GlobalTheory.ArchRec.KFiniteTie.exists_kTie | (intros; apply GlobalTheory.ArchRec.KFiniteTie.exists_kTie <;> assumption)
end

section

open GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap Matrix

namespace GlobalTheory

theorem famChar_hasDerivAt : ∀ (l : Type) [Fintype l] (B : ℝ → (l ⊕ l → ℝ) → (l ⊕ l → ℝ)) (T U : ℝ → Sch l →ₗ[ℂ] Sch l) (Q : Sch l → EuclideanSpace ℝ l → ℂ), (∀ s t f, T (s + t) f = T s (T t f)) → (∀ f, T 0 f = f) → (∀ s t f, U (s + t) f = U s (U t f)) → (∀ f, U 0 f = f) → (∀ s t w, B (s + t) w = B s (B t w)) → (∀ w, B 0 w = w) → (∀ t w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(T t f₁) = rhoFun (B t w) ⇑(T t f)) → (∀ t w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(U t f₁) = rhoFun (B t w) ⇑(U t f)) → (∀ t f, ∫ x, ‖T t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) → (∀ t f, ∫ x, ‖U t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) → (∀ f y, Continuous fun t => T t f y) → (∀ f y, HasDerivAt (fun t => U t f y) (Q f y) 0) → ∃ c : ℂ, ∀ f y, HasDerivAt (fun t => T t f y) (Q f y + c * f y) 0 := by
  intro l _ B T U Q hT hT0 hU hU0 hB hB0 hTρ hUρ hTi hUi hTc hUd
  have hUinv : ∀ t f, U (-t) (U t f) = f := fun t f => by rw [← hU, neg_add_cancel, hU0]
  have hUinv' : ∀ t f, U t (U (-t) f) = f := fun t f => by rw [← hU, add_neg_cancel, hU0]

  have key : ∀ t, ∃ c : ℂ, ∀ f, T t f = c • U t f := by
    intro t
    obtain ⟨c, hc⟩ := GlobalTheory.T.exists_scalar_of_commute_schrodingerOperators l ((T t).comp (U (-t)))
      (fun f => by simp only [LinearMap.comp_apply]; rw [hTi, hUi])
      (fun w f f₁ h => by
        simp only [LinearMap.comp_apply]
        rw [hTρ t (B (-t) w) (U (-t) f) (U (-t) f₁) (hUρ (-t) w f f₁ h), ← hB, add_neg_cancel, hB0])
    refine ⟨c, fun f => ?_⟩
    have := hc (U t f)
    simp only [LinearMap.comp_apply, hUinv] at this
    exact this
  choose lam hlam using key
  set f₀ : Sch l := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l)
  have hf₀ : f₀ 0 ≠ 0 := by simp [f₀]

  have hl0 : lam 0 = 1 := by
    have h := hlam 0 f₀
    rw [hT0, hU0] at h
    have h2 := congrArg (fun g : Sch l => g 0) h
    simp only [SchwartzMap.smul_apply, smul_eq_mul] at h2
    have : (lam 0 - 1) * f₀ 0 = 0 := by linear_combination -h2
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hf₀)
  have hlmul : ∀ s t, lam (s + t) = lam s * lam t := by
    intro s t
    have h1 := hlam (s + t) (U (-(s + t)) f₀)
    rw [hUinv', hT, hlam t, map_smul, hlam s, ← hU, hUinv', smul_smul] at h1
    have h2 := congrArg (fun g : Sch l => g 0) h1
    simp only [SchwartzMap.smul_apply, smul_eq_mul] at h2
    have : (lam s * lam t - lam (s + t)) * f₀ 0 = 0 := by linear_combination h2
    exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hf₀)).symm

  have hd : ContinuousAt (fun t => U t f₀ 0) 0 := (hUd f₀ 0).continuousAt
  have hd0 : U 0 f₀ 0 ≠ 0 := by rw [hU0]; exact hf₀
  have hlc : ContinuousAt lam 0 := by
    have hq : ContinuousAt (fun t => T t f₀ 0 / U t f₀ 0) 0 :=
      ((hTc f₀ 0).continuousAt).div hd hd0
    refine hq.congr ?_
    filter_upwards [hd.eventually_ne hd0] with t ht
    rw [hlam t f₀, SchwartzMap.smul_apply, smul_eq_mul, mul_div_assoc, div_self ht, mul_one]

  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_hasDerivAt_zero_of_continuousAt_of_map_add lam hl0 hlmul hlc
  refine ⟨c, fun f y => ?_⟩
  have hfun : (fun t => T t f y) = fun t => lam t * U t f y := by
    funext t; rw [hlam t f, SchwartzMap.smul_apply, smul_eq_mul]
  rw [hfun]
  have h := hc.mul (hUd f y)
  rw [hl0, hU0, one_mul, add_comm] at h
  exact h

end GlobalTheory
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

theorem _root_.GlobalTheory.T.nonempty_fockModel_of_unitary_pair_covers : ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s), Nonempty (FockData T0 T1 T2) := by
  first | exact @GlobalTheory.nonempty_fockData_of_covers | exact GlobalTheory.nonempty_fockData_of_covers | (intros; apply GlobalTheory.nonempty_fockData_of_covers <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_compact_annihilator_finiteAdeles_stdChar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ O ∈ nhds (0 : Af D.host.F), ∃ K : Set (Af D.host.F), IsCompact K ∧ ∀ x : Af D.host.F, (∀ t ∈ O, ψ (pairA D.host.F 0 (t * x)) = 1) → x ∈ K := by
  first | exact @GlobalTheory.ScalarAnnih.exists_compact_of_annih | exact GlobalTheory.ScalarAnnih.exists_compact_of_annih | (intros; apply GlobalTheory.ScalarAnnih.exists_compact_of_annih <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio

noncomputable section
namespace GlobalTheory.HeckeCharsOfSquare

variable {D : D7}

theorem isHeckeChar_mul {χ ψ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hψ : IsHeckeChar D ψ) :
    IsHeckeChar D (χ * ψ) :=
  ⟨hχ.1.mul hψ.1, fun x => by rw [MonoidHom.mul_apply, hχ.2 x, hψ.2 x, mul_one]⟩

theorem isHeckeChar_inv {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) : IsHeckeChar D χ⁻¹ :=
  ⟨hχ.1.inv, fun x => by rw [MonoidHom.inv_apply, hχ.2 x, inv_one]⟩

theorem isHeckeChar_div {χ ψ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hψ : IsHeckeChar D ψ) :
    IsHeckeChar D (χ / ψ) := by
  rw [div_eq_mul_inv]; exact isHeckeChar_mul hχ (isHeckeChar_inv hψ)

theorem isHeckeChar_pow {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (n : ℕ) : IsHeckeChar D (χ ^ n) :=
  ⟨hχ.1.pow n, fun x => by rw [MonoidHom.pow_apply, hχ.2 x, one_pow]⟩

theorem resEta_of_mod {χ : (AE D)ˣ →* Circle} {a b : ℕ} (h : ResEta D χ a) (hab : a % 2 = b % 2) : ResEta D χ b := by
  refine ⟨h.1, fun η hη x => ?_⟩
  rw [h.2 η hη x, ← Nat.mod_add_div a 2, ← Nat.mod_add_div b 2, pow_add, pow_add, pow_mul, pow_mul,
    GlobalTheory.EtaTildeOddParity.isEta_sq D η hη x, one_pow, one_pow, hab]

theorem resEta_mul {χ ψ : (AE D)ˣ →* Circle} {a b : ℕ} (hχ : ResEta D χ a) (hψ : ResEta D ψ b) :
    ResEta D (χ * ψ) (a + b) :=
  ⟨hχ.1, fun η hη x => by rw [MonoidHom.mul_apply, hχ.2 η hη x, hψ.2 η hη x, pow_add]⟩

theorem resEta_inv {χ : (AE D)ˣ →* Circle} {a : ℕ} (hχ : ResEta D χ a) : ResEta D χ⁻¹ a := by
  refine ⟨hχ.1, fun η hη x => ?_⟩
  rw [MonoidHom.inv_apply, hχ.2 η hη x, ← inv_pow]
  have h2 := GlobalTheory.EtaTildeOddParity.isEta_sq D η hη x
  rw [inv_eq_of_mul_eq_one_right (by rw [← sq, h2] : η x * η x = 1)]

theorem resEta_pow {χ : (AE D)ˣ →* Circle} {a : ℕ} (hχ : ResEta D χ a) (k : ℕ) : ResEta D (χ ^ k) (a * k) :=
  ⟨hχ.1, fun η hη x => by rw [MonoidHom.pow_apply, hχ.2 η hη x, pow_mul]⟩

theorem resEta_div {χ ψ : (AE D)ˣ →* Circle} {a b : ℕ} (hχ : ResEta D χ a) (hψ : ResEta D ψ b) :
    ResEta D (χ / ψ) (a + b) := by
  rw [div_eq_mul_inv]; exact resEta_mul hχ (resEta_inv hψ)

theorem resEta_of_att {μ η : (AE D)ˣ →* Circle} {a b : ℕ} (ha : ResEta D (Lift.attChr μ η a) a)
    (hb : ResEta D (Lift.attChr μ η b) b) (hab : Odd (a + b)) : ResEta D μ 0 ∧ ResEta D η 1 := by
  rcases Nat.even_or_odd a with hae | hao
  · have hbo : Odd b := (Nat.odd_add'.1 hab).2 hae
    have hna : ¬ Odd a := Nat.not_odd_iff_even.2 hae
    simp only [Lift.attChr, hna, if_false] at ha
    simp only [Lift.attChr, hbo, if_true] at hb
    have hμ : ResEta D μ 0 := resEta_of_mod ha (by rw [Nat.even_iff.1 hae])
    refine ⟨hμ, resEta_of_mod (χ := η) (a := a + b) ?_ (by rw [Nat.odd_iff.1 hab])⟩
    have e : η = μ / (μ * η⁻¹) := by rw [div_mul_eq_div_div, div_self', one_div, inv_inv]
    rw [e]; exact resEta_div ha hb
  · have hbe : Even b := by
      rcases Nat.even_or_odd b with h | h
      · exact h
      · exact absurd hab (Nat.not_odd_iff_even.2 (hao.add_odd h))
    have hnb : ¬ Odd b := Nat.not_odd_iff_even.2 hbe
    simp only [Lift.attChr, hao, if_true] at ha
    simp only [Lift.attChr, hnb, if_false] at hb
    have hμ : ResEta D μ 0 := resEta_of_mod hb (by rw [Nat.even_iff.1 hbe])
    refine ⟨hμ, resEta_of_mod (χ := η) (a := b + a) ?_ (by rw [add_comm, Nat.odd_iff.1 hab])⟩
    have e : η = μ / (μ * η⁻¹) := by rw [div_mul_eq_div_div, div_self', one_div, inv_inv]
    rw [e]; exact resEta_div hb ha

end GlobalTheory.HeckeCharsOfSquare

namespace GlobalTheory.HeckeCharsOfSquare

end GlobalTheory.HeckeCharsOfSquare
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseFrameUnimod

theorem isLattice_of_squeeze {E M : Type} [Field E] [NumberField E] [AddCommGroup M] [Module E M] [Module (𝓞 E) M]
    [IsScalarTower (𝓞 E) E M] {L Λ : Submodule (𝓞 E) M} (hL : Submodule.IsLattice E L) {c : E} (hc : c ≠ 0)
    (h1 : ∀ x ∈ L, c • x ∈ Λ) (h2 : ∀ x ∈ Λ, c • x ∈ L) : Submodule.IsLattice E Λ := by
  let f : M →ₗ[𝓞 E] M := ((c⁻¹ • LinearMap.id : M →ₗ[E] M)).restrictScalars (𝓞 E)
  have hfg : (L.map f).FG := hL.fg.map f
  have hle : Λ ≤ L.map f := fun x hx => ⟨c • x, h2 x hx, by simp [f, smul_smul, hc]⟩
  exact Submodule.IsLattice.of_fg E (hfg.of_le hle)

theorem coe_span_dualSet {E : Type} [Field E] [NumberField E] {n : Type} [Fintype n] (σ : E →+* E)
    (J : Matrix n n E) (L : Submodule (𝓞 E) (n → E)) :
    (Submodule.span (𝓞 E) (dualSet σ J L) : Set (n → E)) = dualSet σ J L := by
  refine Set.Subset.antisymm (fun y hy => ?_) Submodule.subset_span
  induction hy using Submodule.span_induction with
  | mem y hy => exact hy
  | zero => intro x _; simpa [Formalism.UG.hform] using (algebraMap (𝓞 E) E).range.zero_mem
  | add y z _ _ hy hz =>
    intro x hx
    have : Formalism.UG.hform σ J x (y + z) = Formalism.UG.hform σ J x y + Formalism.UG.hform σ J x z := by
      simp [Formalism.UG.hform, mul_add, Finset.sum_add_distrib]
    rw [this]
    exact add_mem (hy x hx) (hz x hx)
  | smul a y _ hy =>
    intro x hx
    have : Formalism.UG.hform σ J x (a • y) = algebraMap (𝓞 E) E a * Formalism.UG.hform σ J x y := by
      simp only [Formalism.UG.hform, Finset.mul_sum, Pi.smul_apply, Algebra.smul_def]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this]
    exact mul_mem ⟨a, rfl⟩ (hy x hx)

theorem isDefUnimod_of_isBaseFrame : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), V.SigOK → V.IsPosDef → IsBaseFrame V β Λ N → IsDefUnimod D.sp.cm V.gram Λ := by
  intro D V β Λ N hs hp ⟨_, hdual, hN, h1, h2⟩
  obtain ⟨-, hJ⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm
  have hL : Submodule.IsLattice D.host.E (Formalism.L2.Herm.crdLat V V.L0) :=
    Submodule.IsLattice.of_fg D.host.E (V.standardTuple_isLattice.fg.map _)
  have hmem : ∀ x, x ∈ Formalism.L2.Herm.crdLat V V.L0 ↔ x ∈ L0c D V := by
    intro v
    constructor
    · rintro ⟨x, hx, rfl⟩
      change ∑ i, V.frame.equivFun x i • V.frame i ∈ V.L0
      rwa [V.frame.sum_equivFun]
    · intro hv
      refine ⟨V.frame.equivFun.symm v, ?_, V.frame.equivFun.apply_symm_apply v⟩
      rw [Module.Basis.equivFun_symm_apply]
      exact hv
  refine ⟨Matrix.ext fun i j => (hJ V).1 i j, (hJ V).2.isUnit,
    GlobalTheory.Proof.TotallyDefiniteMass.isTotDef_gram D.sp.cm V hs hp,
    isLattice_of_squeeze hL (Nat.cast_ne_zero.2 hN.ne') (fun x hx => h1 x ((hmem x).1 hx))
      (fun x hx => (hmem _).2 (h2 x hx)), ?_⟩
  rw [← coe_span_dualSet]
  exact congrArg SetLike.coe hdual

end GlobalTheory.BaseFrameUnimod
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.parahoricLevel_liftsExist : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank), ∀ (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsBaseFrame V β Λ N → (∀ PP ∈ L.Pg, ∀ PP', PP' ∈ L.Pg ∨ PP' ∈ L.Q → ¬ Formalism.IndefR.Lev.IsConjPl PP PP') → Disjoint L.Pg L.Q → LiftsExist V β L := by
  first | exact @GlobalTheory.ParahoricLift.liftsExist | exact GlobalTheory.ParahoricLift.liftsExist | (intros; apply GlobalTheory.ParahoricLift.liftsExist <;> assumption)
end
