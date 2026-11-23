module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle004
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle001
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle006
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SpherePairLogSineMoment
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle047
public import Mathlib.NumberTheory.NumberField.CMField
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEmbeddingWeight
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle047
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
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
public import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusMatrix
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ATeleSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs

@[expose] public section

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict

theorem relIndex_ne_zero_of_nsmul_mem {W : Type*} [AddCommGroup W] (L G : AddSubgroup W) [AddGroup.FG L] {D : ℕ} (hD : D ≠ 0)
    (hinj : ∀ y : W, D • y = 0 → y = 0) (hG : ∀ y ∈ G, D • y ∈ L) : L.relIndex G ≠ 0 := by
  let f : G →+ L :=
    { toFun := fun y => ⟨D • (y : W), hG y y.2⟩
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp [smul_add] }
  have hf : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun a ha => ?_
    have : D • (a : W) = 0 := congrArg Subtype.val ha
    exact Subtype.ext (hinj _ this)
  haveI : Module.Finite ℤ L := Module.Finite.iff_addGroup_fg.2 inferInstance
  haveI : Module.Finite ℤ G := Module.Finite.of_injective f.toIntLinearMap hf
  haveI : AddGroup.FG G := Module.Finite.iff_addGroup_fg.1 inferInstance
  haveI : Finite (G ⧸ L.addSubgroupOf G) := by
    refine AddCommGroup.finite_of_fg_torsion _ ?_
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H y =>
      refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨D, Nat.pos_of_ne_zero hD, ?_⟩
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
      simpa using hG y y.2
  exact AddSubgroup.index_ne_zero_of_finite

theorem latEmb_relIndex_dual_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Λ : Type) [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (N : ℕ) (e : Λ →+ (Fin N → E)), Function.Injective e → ∀ form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ, Function.Bijective form → ∀ B : LinearMap.BilinForm ℚ (Fin N → E), (∀ x y, B (e x) (e y) = ((form x y : ℤ) : ℚ)) → (∀ u v, B u v = - B v u) → (∀ u, (∀ v, B v u = 0) → u = 0) → (∀ v : Fin N → E, ∃ (k : ℕ) (x : Λ), k ≠ 0 ∧ e x = k • v) → ∀ (h : HermitianForm (maximalRealSubfield E) E (Fin N → E)) (m : ℕ), m ≠ 0 → (∀ (a : E) u v, Algebra.trace ℚ E (a * (((m : E) * (H.rt : E))⁻¹ * h.toSesq v u)) = B (a • u) v) → e.range.relIndex (GroundTheory.Heights₂.Heights.FiniteCovolume.dualLattice h e.range) ≠ 0 := by
  intro E _ _ _ H Λ _ _ _ N e he form hform B hB hskew hnd hspan h m hm htr
  classical
  have hd0 : (H.d : E) ≠ 0 := Nat.cast_ne_zero.2 H.d_prime.ne_zero
  have hm0 : (m : E) ≠ 0 := Nat.cast_ne_zero.2 hm
  have hrtsq : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (fun a : 𝓞 E => (a : E)) H.rt_sq
    simpa using this
  have hrt0 : (H.rt : E) ≠ 0 := by
    intro h0
    rw [h0] at hrtsq
    exact hd0 (by simpa using hrtsq.symm)
  have hinv : ((m * H.d : ℕ) : E) * ((m : E) * (H.rt : E))⁻¹ = -(H.rt : E) := by
    push_cast
    field_simp
    linear_combination hrtsq
  have key : ∀ y ∈ GroundTheory.Heights₂.Heights.FiniteCovolume.dualLattice h e.range, ∀ x, ∃ n : ℤ, (n : ℚ) = ((m * H.d : ℕ) : ℚ) * B (e x) y := by
    intro y hy x
    have hint : IsIntegral ℤ (h.toSesq y (e x)) := hy (e x) ⟨x, rfl⟩
    have ht := htr 1 (e x) y
    rw [one_smul, one_mul] at ht
    have h2 : ((m * H.d : ℕ) : ℚ) * B (e x) y
        = Algebra.trace ℚ E (-(H.rt : E) * h.toSesq y (e x)) := by
      rw [← ht, ← hinv, mul_assoc, ← smul_eq_mul (a := ((m * H.d : ℕ) : ℚ)), ← map_smul]
      congr 1
      rw [Algebra.smul_def]
      simp
    have hrti : IsIntegral ℤ (-(H.rt : E)) := (H.rt.2).neg
    have h3 : IsIntegral ℤ (Algebra.trace ℚ E (-(H.rt : E) * h.toSesq y (e x))) :=
      Algebra.isIntegral_trace (hrti.mul hint)
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 h3
    exact ⟨n, by rw [h2, ← hn]; simp⟩
  have hDy : ∀ y ∈ GroundTheory.Heights₂.Heights.FiniteCovolume.dualLattice h e.range, (m * H.d) • y ∈ e.range := by
    intro y hy
    choose n hn using key y hy
    have hadd : ∀ a b, n (a + b) = n a + n b := by
      intro a b
      have : ((n (a + b) : ℤ) : ℚ) = ((n a + n b : ℤ) : ℚ) := by
        push_cast
        rw [hn, hn, hn, map_add (f := _), map_add (f := _), LinearMap.add_apply, mul_add]
      exact_mod_cast this
    let φ : Λ →ₗ[ℤ] ℤ := (AddMonoidHom.mk' n hadd).toIntLinearMap
    obtain ⟨z, hz⟩ := hform.2 φ
    have hzx : ∀ x, form z x = n x := fun x => by rw [hz]; rfl
    have h0 : ∀ x, B (e x) ((m * H.d) • y + e z) = 0 := by
      intro x
      have h1 : B (e x) (e z) = -((n x : ℤ) : ℚ) := by
        rw [hskew, hB, hzx]
      rw [map_add (f := _), map_nsmul, h1, hn, nsmul_eq_mul]
      ring
    have h1 : ∀ v, B v ((m * H.d) • y + e z) = 0 := by
      intro v
      obtain ⟨k, x, hk, hx⟩ := hspan v
      have h2 := h0 x
      rw [hx, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at h2
      exact (mul_eq_zero.1 h2).resolve_left (Nat.cast_ne_zero.2 hk)
    have h2 := hnd _ h1
    exact ⟨-z, by rw [map_neg]; exact (eq_neg_of_add_eq_zero_left h2).symm⟩
  haveI : AddGroup.FG e.range := by
    haveI : Module.Finite ℤ e.range :=
      Module.Finite.of_surjective e.rangeRestrict.toIntLinearMap e.rangeRestrict_surjective
    exact Module.Finite.iff_addGroup_fg.1 inferInstance
  refine relIndex_ne_zero_of_nsmul_mem _ _ (D := m * H.d) (mul_ne_zero hm H.d_prime.ne_zero) ?_ hDy
  intro y hy
  funext i
  have h1 := congrFun hy i
  simp only [Pi.smul_apply, Pi.zero_apply] at h1
  rw [nsmul_eq_mul] at h1
  exact (mul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 (mul_ne_zero hm H.d_prime.ne_zero))

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

theorem _root_.GlobalTheory.T.sphere_pair_log_sine_moment : ∀ (ℓ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ) (Q : MvPolynomial (Fin 2) ℝ),
    ∫ p : ℂ × ℂ, logSin 1 p.1 p.2 * (wS p.1 * wS p.2 * ℓ (aeval ![lin3 (nS p.1), lin3 (nS p.2)] Q)) =
      Real.pi ^ 2 * ℓ (momentPoly (sphereMeasure.prod sphereMeasure) wwLogWeight
        (aeval ![dotPoly (Prod.fst : S2 × S2 → S2), dotPoly Prod.snd] Q)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibN.StereoTwo.integral_eq_moment | exact GlobalTheory.CompanionTheory.Ar.PB.FibN.StereoTwo.integral_eq_moment | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibN.StereoTwo.integral_eq_moment <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

theorem _root_.GlobalTheory.T.sphere_moment_power : ∀ (ℓ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ) (N : ℕ),
    ∫ a : ℂ, wS a * ℓ (lin3 (nS a) ^ N) =
      Real.pi * ℓ (momentPoly sphereMeasure (fun _ => 1) (dotPoly (id : S2 → S2) ^ N)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibN.stereo_one | exact GlobalTheory.CompanionTheory.Ar.PB.FibN.stereo_one | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibN.stereo_one <;> assumption)
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatticeCoordinates

open scoped TensorProduct nonZeroDivisors

theorem exists_nat_eq_mul {E : Type} [Field E] [NumberField E] {a : 𝓞 E} (ha : a ≠ 0) :
    ∃ (k : ℕ) (b : 𝓞 E), k ≠ 0 ∧ (k : 𝓞 E) = b * a := by
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
  refine ⟨Ideal.absNorm (Ideal.span {a}), b, ?_, hb.symm⟩
  rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
  exact ha

theorem exists_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ], ∃ N : ℕ, Module.finrank ℚ E * N = Module.finrank ℤ Λ ∧ ∃ e : Λ →+ (Fin N → E), Function.Injective e ∧ (∀ (a : 𝓞 E) x, e (a • x) = (a : E) • e x) ∧ ∀ v : Fin N → E, ∃ (k : ℕ) (x : Λ), k ≠ 0 ∧ e x = k • v := by
  intro E _ _ _ Λ _ _ _ _
  let f : Λ →ₗ[𝓞 E] E ⊗[𝓞 E] Λ := TensorProduct.mk (𝓞 E) E Λ 1
  have hb : IsBaseChange E f := TensorProduct.isBaseChange _ _ _
  haveI h1 : IsLocalizedModule (𝓞 E)⁰ f := (isLocalizedModule_iff_isBaseChange (𝓞 E)⁰ E f).2 hb
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) E :=
    IsIntegralClosure.isLocalization ℤ ℚ E (𝓞 E)
  haveI h2 : IsLocalizedModule (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) f :=
    (isLocalizedModule_iff_isBaseChange _ E f).2 hb
  haveI h3 : IsLocalizedModule ℤ⁰ (f.restrictScalars ℤ) := IsLocalizedModule.restrictScalars _ f
  haveI : Module.Finite (𝓞 E) Λ := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) Λ
  have hrank : Module.finrank ℚ E * Module.finrank E (E ⊗[𝓞 E] Λ) = Module.finrank ℤ Λ := by
    rw [← IsLocalizedModule.finrank_eq ℤ⁰ (f.restrictScalars ℤ) le_rfl,
      ← IsLocalization.finrank_eq ℚ ℤ⁰ le_rfl, Module.finrank_mul_finrank]
  have htors : ∀ x : Λ, f x = 0 → x = 0 := by
    intro x hx
    obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_zero_iff (𝓞 E)⁰ f).1 hx
    obtain ⟨k, b, hk, hkb⟩ := exists_nat_eq_mul (nonZeroDivisors.coe_ne_zero c)
    have hkx : (k : ℤ) • x = 0 := by
      rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul (𝓞 E), hkb, mul_smul]
      have : (c : 𝓞 E) • x = 0 := hc
      rw [this, smul_zero]
    exact (smul_eq_zero.1 hkx).resolve_left (by exact_mod_cast hk)
  let g := (Module.finBasis E (E ⊗[𝓞 E] Λ)).equivFun
  refine ⟨Module.finrank E (E ⊗[𝓞 E] Λ), hrank,
    AddMonoidHom.mk' (fun x => g (f x)) (fun x y => by simp only [map_add (f := _)]), ?_, ?_, ?_⟩
  · refine (injective_iff_map_eq_zero _).2 fun x hx => htors x ?_
    exact g.map_eq_zero_iff.1 hx
  · intro a x
    change g (f (a • x)) = (a : E) • g (f x)
    rw [map_smul, ← map_smul g]
    congr 1
  · intro v
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalizedModule.surj (𝓞 E)⁰ f (g.symm v)
    obtain ⟨k, b, hk, hkb⟩ := exists_nat_eq_mul (nonZeroDivisors.coe_ne_zero s)
    refine ⟨k, b • x, hk, ?_⟩
    change g (f (b • x)) = k • v
    have hs' : (s : 𝓞 E) • g.symm v = f x := hs
    rw [map_smul, ← hs', ← mul_smul, ← hkb, Nat.cast_smul_eq_nsmul, map_nsmul, LinearEquiv.apply_symm_apply]

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatticeCoordinates
end
end

section

set_option maxSynthPendingDepth 1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem intersection_locConst_trivial : PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (L : Fin D → HermLine ι) (B : HermLine ι) (Λ : (F →+* ℂ) → ℝ) (II : IntersectionSystem), IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → (∀ j, IsSmoothHerm (L j)) → B.a = 0 → IsSmoothHerm B → (∀ z ∈ mcPts (mCoordIdeal y), ∃! s : F →+* ℂ, LiesOver y s z) → (∀ z ∈ mcPts (mCoordIdeal y), ∀ sg : F →+* ℂ, LiesOver y sg z → B.h =ᶠ[𝓝 z] fun _ => Λ sg) → II K ι (mCoordIdeal y) (D + 1) (Fin.snoc L B) = ∑ sg : F →+* ℂ, Real.log (Λ sg) * ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) := by
  intro hInt K _ ι _ Ω _ F _ _ _ y D L B Λ II hII hP hL hB0 hB hex hloc
  classical
  let S : (F →+* ℂ) → Set ((Σ k, ι k) → ℂ) := fun sg => {z | LiesOver y sg z}
  have hSc : ∀ sg, IsClosed (S sg) := fun sg =>
    GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingWeight.isClosed_liesOver y sg
  have hSs : ∀ sg (t : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, t k ≠ 0) → z ∈ S sg →
      (fun p => t p.1 * z p) ∈ S sg :=
    fun _ t _ _ hz => GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingWeight.liesOver_smul hz t
  have hex' : ∀ z ∈ mcPts (mCoordIdeal y), ∃! sg, z ∈ S sg := hex
  have hR := (hII K ι).2.2 (mCoordIdeal y) D L B 1 0 hP hL hB (fun k => by simp [hB0])
    tele_one_homog (fun h1 => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one _).mpr h1))
  have hnum : II K ι (mCoordIdeal y) (D + 1) (Fin.snoc L B) =
      ptsIntegral (mCoordIdeal y) (pot L) fun z => Real.log (B.h z) := by
    rw [hR]
    unfold recR
    rw [tele_divSupp_one, finsum_mem_empty, zero_sub]
    unfold arInt
    have hl : logNorm B 1 = fun z => - Real.log (B.h z) := by
      funext z
      simp [logNorm, Real.log_inv]
    rw [hl, tele_ptsIntegral_neg, neg_neg]
    rfl
  have hw : ptsIntegral (mCoordIdeal y) (pot L) (fun z => Real.log (B.h z)) =
      ptsIntegral (mCoordIdeal y) (pot L)
        (fun z => ∑ s, Real.log (Λ s) * (S s).indicator (fun _ => (1 : ℝ)) z) := by
    refine GroundTheory.Heights₂.Heights.Inter.DiagRAux.ptsIntegral_congr_mcPts _ (fun _ _ _ => rfl) ?_
    intro z hz
    obtain ⟨sg, hsg, -⟩ := hex z hz
    have hval : B.h z = Λ sg := (hloc z hz sg hsg).self_of_nhds
    rw [Finset.sum_eq_single sg]
    · rw [Set.indicator_of_mem (show z ∈ S sg from hsg), mul_one, hval]
    · intro s _ hs
      have hns : z ∉ S s := fun h => hs ((hex z hz).unique h hsg)
      rw [Set.indicator_of_notMem hns, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ sg) h
  rw [hnum, hw]
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.PiecesAdditive.proof hInt K ι _ D L (F →+* ℂ) S
    (fun s => Real.log (Λ s)) hP hL hSc hSs hex'

end GlobalTheory.CompanionTheory.Ar.Giv
end
