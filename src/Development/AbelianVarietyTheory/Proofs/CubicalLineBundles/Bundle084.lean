module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle024
public import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementB
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle028
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle082
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle013
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle014
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle129
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.OneLeAbsNormOfLeOne
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle081
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle052
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LamObj
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkNum
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Topology.Separation.CompletelyRegular
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.abelian₂ Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.FD (Data DataX Frame LamBasis fdeg)
open GlobalTheory.SecTransport GlobalTheory.SecTieEx

namespace GlobalTheory.FramedCMPointCompare

section Bundles

variable {X X' Y : Scheme.{0}}

end Bundles

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} {c : Coeff l}

section Letters

variable [StarRing (𝓞 E)] {nΨ n' : ℕ}

variable {o : LamObj c nΨ n'}

end Letters

section Data

variable {Dw : Datum H} {Xo : Moduli Dw l}

end Data

variable {D : D7}

theorem fdeg_host (D : D7) : fdeg D.host.E = D.R.f := by
  unfold fdeg
  rw [hostSize_finrank]
  omega

end GlobalTheory.FramedCMPointCompare
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.KeyVal

theorem exists_unit_of_pow {R K' : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K'] [Algebra R K']
    [IsFractionRing R K'] {z : K'} {m : ℕ} (hm : 0 < m) (w : Rˣ) (h : z ^ m = algebraMap R K' w) :
    ∃ u : Rˣ, z = algebraMap R K' u := by
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := R) (K := K') (x := z) hm
    (by rw [h]; exact isIntegral_algebraMap)
  have h1 : r ^ m = w := IsFractionRing.injective R K' (by rw [map_pow, hr, h])
  have h2 : IsUnit r := (isUnit_pow_iff hm.ne').1 (h1 ▸ w.isUnit)
  exact ⟨h2.unit, by simp [hr]⟩

theorem unit_iff {K : Type} [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K)) {R K' : Type} [CommRing R]
    [Field K'] [Algebra R K'] (hi : Function.Injective (algebraMap R K')) (f : K →+* K')
    (hv : ∀ y : K, f y ∈ Set.range (algebraMap R K') ↔ p.valuation K y ≤ 1) (y : K) :
    (∃ u : Rˣ, f y = algebraMap R K' u) ↔ p.valuation K y = 1 := by
  constructor
  · rintro ⟨u, hu⟩
    have hy : y ≠ 0 := by
      rintro rfl
      exact (u.isUnit.map (algebraMap R K')).ne_zero (by rw [← hu, map_zero])
    refine eq_one_of_one_le_mul_left ((hv y).1 ⟨_, hu.symm⟩)
      ((hv y⁻¹).1 ⟨(u⁻¹ : Rˣ), by rw [map_units_inv, map_inv₀, hu]⟩) ?_
    rw [← map_mul, mul_inv_cancel₀ hy, map_one]
  · intro h
    have hy : y ≠ 0 := by
      rintro rfl
      simp at h
    obtain ⟨r, hr⟩ := (hv y).2 h.le
    obtain ⟨s, hs⟩ := (hv y⁻¹).2 (by rw [map_inv₀, h, inv_one])
    have e : r * s = 1 := hi (by rw [map_mul, hr, hs, ← map_mul, mul_inv_cancel₀ hy, map_one, map_one])
    exact ⟨Units.mkOfMulEqOne r s e, by simp [hr]⟩

theorem valuation_eq_of_isLocGen {K : Type} [Field K] [NumberField K] {p : HeightOneSpectrum (𝓞 K)} {c c' : K}
    {I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K} (h : IsLocGen p c I) (h' : IsLocGen p c' I) :
    p.valuation K c = p.valuation K c' := by
  rw [valuation_eq_exp_count p h.1, valuation_eq_exp_count p h'.1, h.2, h'.2]

theorem exists_pow_rel (K : Type) [Field K] [NumberField K] (x : KeyIn K) :
    ∃ (n : ℕ) (k : K), 1 ≤ n ∧ k ≠ 0 ∧ ∀ (R K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K']
      [Algebra R K'] [IsFractionRing R K'] (f : K →+* K') (x' : KeyIn K') (a d : K'), KeyPB x' x f →
      KeyIntegral R x' a d → ∃ u : Rˣ, a ^ (8 * n) * algebraMap R K' u = d ^ (4 * n) * f k := by
  obtain ⟨N, hN, κ, hH, hF, hU, -⟩ := GlobalTheory.keyFormulaPow_and_keyDegree.1
  refine ⟨N x.P.g, κ K x, hN _, (κ K x).ne_zero, ?_⟩
  intro R K' _ _ _ _ _ _ f x' a d hPB hInt
  haveI : CharZero K' := (RingHom.charZero_iff f.injective).1 inferInstance
  obtain ⟨th', hth', v', hv', M, xR, hth'eq, hv'eq, hMdet, hPBR⟩ := hInt
  have hFx := hF K K' f x x' hPB
  have hHx := hH K' x'.P x'.g_pos x'.rig x'.rig_gen x'.th x'.th_ne x'.v x'.basis th' hth' v' hv' a M hth'eq hv'eq
  obtain ⟨u, hu, -⟩ := hU R K' xR _ hPBR
  have hg : x'.P.g = x.P.g := by obtain ⟨-, -, -, hg, -⟩ := hPB; exact hg
  refine ⟨u, ?_⟩
  rw [← hu, ← hFx, ← hMdet, ← hg]
  exact hHx

theorem integral_section_unit : ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (Tl abelian₂ : MLine K) (p : HeightOneSpectrum (𝓞 K)), KeyLocAt x Tl abelian₂ p → ∀ (R K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K'] [Algebra R K'] [IsFractionRing R K'] (f : K →+* K') (x' : KeyIn K') (a d : K') (ca cd : K) (ud : Rˣ), (∀ y : K, f y ∈ Set.range (algebraMap R K') ↔ p.valuation K y ≤ 1) → KeyPB x' x f → KeyIntegral R x' a d → IsLocGen p cd abelian₂.I → d = f cd * algebraMap R K' ud → IsLocGen p ca Tl.I → ∃ u : Rˣ, a = f ca * algebraMap R K' u := by
  intro K _ _ x Tl abelian₂ p hloc R K' _ _ _ _ _ _ f x' a d ca cd ud hval hPB hInt hcd hd hca
  obtain ⟨n, k, hn, hk, H⟩ := exists_pow_rel K x
  obtain ⟨K₁, _, _, R₁, _, _, _, _, _, f₁, x₁, a₁, d₁, ca₁, cd₁, ua₁, ud₁, hPB₁, hInt₁, hval₁, ha₁, hd₁, hca₁, hcd₁⟩ := hloc
  obtain ⟨u₁, hu₁⟩ := H R₁ K₁ f₁ x₁ a₁ d₁ hPB₁ hInt₁
  obtain ⟨u, hu⟩ := H R K' f x' a d hPB hInt
  have h1 : p.valuation K (cd₁ ^ (4 * n) * k / ca₁ ^ (8 * n)) = 1 := by
    refine (unit_iff p (IsFractionRing.injective R₁ K₁) f₁ hval₁ _).1 ⟨ua₁ ^ (8 * n) * u₁ * ud₁⁻¹ ^ (4 * n), ?_⟩
    have hfa : f₁ ca₁ ≠ 0 := (map_ne_zero f₁).2 hca₁.1
    have hD : algebraMap R₁ K₁ (ud₁ : R₁) ≠ 0 := (ud₁.isUnit.map (algebraMap R₁ K₁)).ne_zero
    rw [ha₁, hd₁, mul_pow, mul_pow] at hu₁
    rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_mul, map_mul,
      map_pow, map_pow, map_units_inv, map_div₀, map_mul, map_pow, map_pow, inv_pow, ← div_eq_mul_inv,
      div_eq_div_iff (pow_ne_zero _ hfa) (pow_ne_zero _ hD)]
    linear_combination -hu₁
  have h2 : p.valuation K (cd ^ (4 * n) * k / ca ^ (8 * n)) = 1 := by
    rw [map_div₀, map_mul, map_pow, map_pow] at h1 ⊢
    rw [valuation_eq_of_isLocGen hca hca₁, valuation_eq_of_isLocGen hcd hcd₁, h1]
  obtain ⟨w, hw⟩ := (unit_iff p (IsFractionRing.injective R K') f hval _).2 h2
  have hfa : f ca ≠ 0 := (map_ne_zero f).2 hca.1
  have hU : algebraMap R K' (u : R) ≠ 0 := (u.isUnit.map (algebraMap R K')).ne_zero
  obtain ⟨t, ht⟩ := exists_unit_of_pow (R := R) (z := a / f ca) (m := 8 * n) (by omega) (w * ud ^ (4 * n) * u⁻¹) (by
    rw [hd, mul_pow] at hu
    rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_mul,
      map_pow, map_units_inv, ← hw, map_div₀, map_mul, map_pow, map_pow, div_pow, ← div_eq_mul_inv,
      eq_div_iff hU, div_mul_eq_mul_div, div_mul_eq_mul_div, hu]
    ring)
  exact ⟨t, by rw [← ht, mul_div_cancel₀ _ hfa]⟩

end GlobalTheory.KeyVal
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT


theorem _root_.GlobalTheory.T.ruleValue_integral_of_supLattice_values_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (F : Rul Xo c), (∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) → ∀ (T : CDVR) (io : c.F →+* T.Fr), T.FinRes → letI := io.toAlgebra; ∀ y : FrPt Xo c T.Fr, Integral T io y → evR Xo c F y ∈ Set.range (algebraMap T.V T.Fr) := by
  first | exact @GlobalTheory.LamT.evR_mem_range_of_valSet_nonneg | exact GlobalTheory.LamT.evR_mem_range_of_valSet_nonneg | (intros; apply GlobalTheory.LamT.evR_mem_range_of_valSet_nonneg <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.KeyUniq

theorem volume_image {g : ℕ} (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (s : Set (Fin g → ℂ)) :
    (volume (F '' s)).toReal = ‖LinearMap.det F‖ ^ 2 * (volume s).toReal := by
  have h := Measure.addHaar_image_linearMap volume (F.restrictScalars ℝ) s
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply, abs_of_nonneg (Complex.normSq_nonneg _),
    Complex.normSq_eq_norm_sq] at h
  rw [show (F '' s) = (F.restrictScalars ℝ) '' s from rfl, h, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

theorem volume_fund {g : ℕ} (Λ Λ' : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ']
    (F : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hF : ∀ z, F z ∈ Λ' ↔ z ∈ Λ) {s s' : Set (Fin g → ℂ)}
    (hs : IsAddFundamentalDomain Λ s volume) (hs' : IsAddFundamentalDomain Λ' s' volume) :
    (volume s').toReal = ‖LinearMap.det F.toLinearMap‖ ^ 2 * (volume s).toReal := by
  let φ : Λ' ≃ Λ :=
    { toFun := fun b => ⟨F.symm b, (hF _).1 (by rw [F.apply_symm_apply]; exact b.2)⟩
      invFun := fun a => ⟨F a, (hF a).2 a.2⟩
      left_inv := fun b => Subtype.ext (F.apply_symm_apply b.1)
      right_inv := fun a => Subtype.ext (F.symm_apply_apply a.1) }
  have hq : Measure.QuasiMeasurePreserving F.toEquiv.symm volume volume :=
    Measure.LinearMap.quasiMeasurePreserving volume (F.symm.restrictScalars ℝ).toLinearMap
      (F.symm.restrictScalars ℝ).isUnit_det'.ne_zero
  have h1 : IsAddFundamentalDomain Λ' (F.toEquiv '' s) volume :=
    hs.image_of_equiv F.toEquiv hq φ fun b z => by
      change F (F.symm b + z) = b + F z
      rw [map_add (f := _), F.apply_symm_apply]
  have : Countable Λ' := countable_of_Lindelof_of_discrete
  have : MeasurableConstVAdd Λ' (Fin g → ℂ) := ⟨fun c => measurable_const_add (c : Fin g → ℂ)⟩
  have : VAddInvariantMeasure Λ' (Fin g → ℂ) volume :=
    ⟨fun c s _ => measure_preimage_add volume (c : Fin g → ℂ) s⟩
  rw [hs'.measure_eq h1]
  exact volume_image F.toLinearMap s

theorem norm_eq_and_hermForm_eq : ∀ (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (Hm : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (χ : u.Λ → ℂ) (θ : (Fin x.P.g → ℂ) → ℂ) (Fd : Set (Fin x.P.g → ℂ)) (u' : HolUnif x.P.A x.P.L x.P.g) (Hm' : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (χ' : u'.Λ → ℂ) (θ' : (Fin x.P.g → ℂ) → ℂ) (Fd' : Set (Fin x.P.g → ℂ)), u.IsAH Hm χ ∧ u.IsRig x.rig ∧ u.IsFn x.th θ ∧ IsAddFundamentalDomain u.Λ Fd volume → u'.IsAH Hm' χ' ∧ u'.IsRig x.rig ∧ u'.IsFn x.th θ' ∧ IsAddFundamentalDomain u'.Λ Fd' volume → (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) / (volume Fd).toReal = (∫ z in Fd', ‖θ' z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm' z z).re)) / (volume Fd').toReal ∧ ∀ (v w : epsR ℂ ⟶ x.P.A) (V W V' W' : Fin x.P.g → ℂ), IsTangent v → IsTangent w → u.IsDiff V v → u.IsDiff W w → u'.IsDiff V' v → u'.IsDiff W' w → hermForm Hm V W = hermForm Hm' V' W' := by
  rintro x u Hm χ θ Fd u' Hm' χ' θ' Fd' ⟨hA, hR, hθ, hD⟩ ⟨hA', hR', hθ', hD'⟩
  obtain ⟨-, t1, -⟩ := unimodular_and_tangent_of_isAH thetaUnifAV_all x.P x.rig x.rig_gen u Hm χ hA
  obtain ⟨-, t1', t2'⟩ := unimodular_and_tangent_of_isAH thetaUnifAV_all x.P x.rig x.rig_gen u' Hm' χ' hA'
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo x.P.A x.P.isAb x.P.L x.P.g x.P.g u' t1' t2' u.ex u.ex_add
    (fun U f => by simpa only [Set.mem_univ, true_and] using u.hol U f)
  let e : (Fin x.P.g → ℂ) ≃ₗ[ℂ] (Fin x.P.g → ℂ) := LinearEquiv.ofInjectiveEndo F (UnifCompare.injective u u' F hF)
  have hd : ∀ w v, u.IsDiff w v ↔ u'.IsDiff (F w) v :=
    UnifCompare.isDiff_iff u u' e.toContinuousLinearEquiv hF
  refine ⟨?_, fun v w V W V' W' hv hw h1 h2 h3 h4 => ?_⟩
  · obtain ⟨N, hN, κ, -, -, -, -, hK⟩ := keyFormulaPow_and_keyDegree.1
    choose W hW using fun i => (t1 _ (x.basis.1 i)).exists
    have k := hK x u Hm (Matrix.of W) χ θ Fd _ _ hA hR hθ hW hD rfl rfl
    have k' := hK x u' Hm' (Matrix.of fun i => F (W i)) χ' θ' Fd' _ _ hA' hR' hθ' (fun i => (hd _ _).1 (hW i)) hD' rfl rfl
    have := u'.discrete
    have hvol : (volume Fd').toReal = ‖LinearMap.det F‖ ^ 2 * (volume Fd).toReal :=
      volume_fund u.Λ u'.Λ e (UnifCompare.mem_iff u u' F hF) hD hD'
    have hdet : (Matrix.of fun i => F (W i)).det = LinearMap.det F * (Matrix.of W).det := by
      have : (Matrix.of fun i => F (W i)) = Matrix.of W * (LinearMap.toMatrix' F).transpose := by
        ext i j
        rw [Matrix.of_apply, ← LinearMap.toMatrix'_mulVec, Matrix.mul_apply, Matrix.mulVec, dotProduct]
        exact Finset.sum_congr rfl fun _ _ => _root_.mul_comm _ _
      rw [this, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix', _root_.mul_comm]
    have h0 : ‖LinearMap.det F‖ ≠ 0 := norm_ne_zero_iff.2 e.isUnit_det'.ne_zero
    have hη : (volume Fd').toReal / (Real.pi ^ x.P.g * ‖(Matrix.of fun i => F (W i)).det‖ ^ 2) =
        (volume Fd).toReal / (Real.pi ^ x.P.g * ‖(Matrix.of W).det‖ ^ 2) := by
      rw [hvol, hdet, norm_mul, mul_pow, mul_left_comm, mul_div_mul_left _ _ (pow_ne_zero 2 h0)]
    rw [hη] at k'
    have hne := k.trans_ne (pow_ne_zero _ Real.two_pi_pos.ne')
    have h1 := mul_left_cancel₀ (left_ne_zero_of_mul (left_ne_zero_of_mul hne))
      (mul_right_cancel₀ (right_ne_zero_of_mul hne) (k.trans k'.symm))
    exact (pow_left_inj₀ (div_nonneg (integral_nonneg fun z => by positivity) ENNReal.toReal_nonneg)
      (div_nonneg (integral_nonneg fun z => by positivity) ENNReal.toReal_nonneg)
      (by have := hN x.P.g; omega)).1 h1
  · rw [(t1' v hv).unique h3 ((hd _ _).1 h1), (t1' w hw).unique h4 ((hd _ _).1 h2)]
    exact (UnifCompare.hermForm_eq x.P.isLB u u' hA hA' F hF V W).symm

end GlobalTheory.KeyUniq
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT


theorem _root_.GlobalTheory.T.thetaSection_norm_and_hermitianForm_indep_uniformisation : ∀ (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (Hm : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (χ : u.Λ → ℂ) (θ : (Fin x.P.g → ℂ) → ℂ) (Fd : Set (Fin x.P.g → ℂ)) (u' : HolUnif x.P.A x.P.L x.P.g) (Hm' : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (χ' : u'.Λ → ℂ) (θ' : (Fin x.P.g → ℂ) → ℂ) (Fd' : Set (Fin x.P.g → ℂ)), u.IsAH Hm χ ∧ u.IsRig x.rig ∧ u.IsFn x.th θ ∧ IsAddFundamentalDomain u.Λ Fd volume → u'.IsAH Hm' χ' ∧ u'.IsRig x.rig ∧ u'.IsFn x.th θ' ∧ IsAddFundamentalDomain u'.Λ Fd' volume → (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) / (volume Fd).toReal = (∫ z in Fd', ‖θ' z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm' z z).re)) / (volume Fd').toReal ∧ ∀ (v w : epsR ℂ ⟶ x.P.A) (V W V' W' : Fin x.P.g → ℂ), IsTangent v → IsTangent w → u.IsDiff V v → u.IsDiff W w → u'.IsDiff V' v → u'.IsDiff W' w → hermForm Hm V W = hermForm Hm' V' W' := by
  first | exact @GlobalTheory.KeyUniq.norm_eq_and_hermForm_eq | exact GlobalTheory.KeyUniq.norm_eq_and_hermForm_eq | (intros; apply GlobalTheory.KeyUniq.norm_eq_and_hermForm_eq <;> assumption)

end
end
