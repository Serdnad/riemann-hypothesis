module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Order.CompletePartialOrder
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Separation.CompletelyRegular
public import ReciprocityTheory.L2DbarEstimates.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle241
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle532
public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle533
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousMeasureEqSmulAddHaarLocalField
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle534
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.L2DbarEstimates.NormFibrations.MvBlowup
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle005
import Mathlib.RingTheory.MvPowerSeries.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.RootUnitGeom

theorem eq_one_of_pow_eq_one_of_isNilpotent {A : Type*} [CommRing A] {v : A} {k : ℕ}
    (hk : IsUnit (k : A)) (hv : v ^ k = 1) (hn : IsNilpotent (v - 1)) : v = 1 := by
  have hw : IsNilpotent (∑ i ∈ Finset.range k, (v ^ i - 1)) := by
    refine isNilpotent_sum fun i _ => ?_
    have : v ^ i - 1 = (∑ j ∈ Finset.range i, v ^ j) * (v - 1) := (geom_sum_mul v i).symm
    rw [this]
    exact mem_nilradical.1 (Ideal.mul_mem_left _ _ (mem_nilradical.2 hn))
  have hs : ∑ i ∈ Finset.range k, v ^ i = (k : A) + ∑ i ∈ Finset.range k, (v ^ i - 1) := by
    simp [Finset.sum_sub_distrib]
  have hu : IsUnit (∑ i ∈ Finset.range k, v ^ i) := by
    rw [hs]
    exact hw.isUnit_add_left_of_commute hk (Commute.all _ _)
  have h0 : (∑ i ∈ Finset.range k, v ^ i) * (v - 1) = 0 := by
    rw [geom_sum_mul, hv, sub_self]
  have : v - 1 = 0 := (hu.mul_right_eq_zero).1 h0
  exact sub_eq_zero.1 this

end GlobalTheory.RootUnitGeom

namespace GlobalTheory.RootUnitGeom

theorem fromSpecResidueField_appTop_comp (S : Scheme.{0}) (x : S) :
    (S.fromSpecResidueField x).appTop ≫ (Scheme.ΓSpecIso _).hom = S.evaluation ⊤ x trivial := by
  rw [Scheme.fromSpecResidueField, Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop]
  simp only [Category.assoc, Scheme.ΓSpecIso_naturality]
  have e : (homOfLE (le_top : (⊤ : (Spec (S.presheaf.stalk x)).Opens) ≤ ⊤)) = 𝟙 _ := rfl
  rw [e, op_id, CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_assoc]
  rfl

theorem evaluation_eq_one (R : Type) [CommRing R] (S : Scheme.{0}) (s : S ⟶ Sp R)
    (u : Γ(S, ⊤)ˣ)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (β : R →+* K), x ≫ s = spMap β →
      Units.map x.appTop.hom.toMonoidHom u = 1) (q : S) :
    S.evaluation ⊤ q trivial (u : Γ(S, ⊤)) = 1 := by
  let K := AlgebraicClosure (S.residueField q)
  let f : S.residueField q ⟶ CommRingCat.of K := CommRingCat.ofHom (algebraMap (S.residueField q) K)
  let x : Sp K ⟶ S := Spec.map f ≫ S.fromSpecResidueField q
  have hx : x ≫ s = spMap (Spec.preimage (x ≫ s)).hom := by
    simp [spMap]
  have h1 := h K x _ hx
  have h2 : x.appTop (u : Γ(S, ⊤)) = 1 := by
    have := congrArg Units.val h1
    simpa using this
  have e : x.appTop ≫ (Scheme.ΓSpecIso _).hom = S.evaluation ⊤ q trivial ≫ f := by
    simp only [x, Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality]
    rw [← Category.assoc, fromSpecResidueField_appTop_comp]
  have h3 := congrArg (fun g => g (u : Γ(S, ⊤))) (congrArg (fun g => (CategoryTheory.ConcreteCategory.hom g : _ → _)) e)
  simp only [CategoryTheory.comp_apply, h2, map_one] at h3
  apply (algebraMap (S.residueField q) K).injective
  rw [map_one]
  exact h3.symm

end GlobalTheory.RootUnitGeom

namespace GlobalTheory.RootUnitGeom

theorem germ_isNilpotent (S : Scheme.{0}) (ε : Γ(S, ⊤)) (hε : S.basicOpen ε = ⊥) (q : S) :
    IsNilpotent (S.presheaf.germ ⊤ q trivial ε) := by
  obtain ⟨U, hU, hqU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 S.isBasis_affineOpens)
    (show q ∈ (⊤ : S.Opens) from trivial)
  have hb : S.basicOpen (S.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ε) = ⊥ := by
    rw [Scheme.basicOpen_res, hε, inf_bot_eq]
  have hn := (Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact
    (IsAffineOpen.isCompact hU) _).2 hb
  have := hn.map (S.presheaf.germ U q hqU).hom
  rwa [TopCat.Presheaf.germ_res_apply] at this

end GlobalTheory.RootUnitGeom


open GlobalTheory.RootUnitGeom in
theorem GlobalTheory.rootOfUnity_eq_one_of_geom : ∀ (R : Type) [CommRing R] (S : Scheme.{0}) (s : S ⟶ Sp R) (k : ℕ)
    (u : Γ(S, ⊤)ˣ), IsUnit (k : R) → u ^ k = 1 →
    (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (β : R →+* K), x ≫ s = spMap β →
      Units.map x.appTop.hom.toMonoidHom u = 1) → u = 1 := by
  intro R _ S s k u hk hu h
  have hε : S.basicOpen ((u : Γ(S, ⊤)) - 1) = ⊥ := by
    rw [Scheme.basicOpen_eq_bot_iff_forall_evaluation_eq_zero]
    intro x
    rw [map_sub, map_one, evaluation_eq_one R S s u h x.1, sub_self]
  ext1
  apply TopCat.Presheaf.section_ext S.sheaf ⊤
  intro q hq
  let φ : R →+* S.presheaf.stalk q :=
    (S.presheaf.germ ⊤ q trivial).hom.comp (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
  have hk' : IsUnit (k : S.presheaf.stalk q) := by
    simpa [map_natCast] using hk.map φ
  have hv : (S.presheaf.germ ⊤ q trivial (u : Γ(S, ⊤))) ^ k = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hu, Units.val_one, map_one]
  have hn : IsNilpotent (S.presheaf.germ ⊤ q trivial (u : Γ(S, ⊤)) - 1) := by
    have := germ_isNilpotent S _ hε q
    rwa [map_sub, map_one] at this
  have := eq_one_of_pow_eq_one_of_isNilpotent hk' hv hn
  change S.presheaf.germ ⊤ q trivial (u : Γ(S, ⊤)) = S.presheaf.germ ⊤ q trivial ((1 : Γ(S, ⊤)ˣ) : Γ(S, ⊤))
  rw [this, Units.val_one, map_one]
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

noncomputable section

theorem l2ball_sq_mul_vol_le {n : ℕ} {x : V n} {s : ℝ} (u : V n → ℂ)
    (hu : DifferentiableOn ℂ u (ball x s)) :
    ENNReal.ofReal (‖u x‖ ^ 2) * volume (ball (0 : V n) s) ≤
      ∫⁻ v in ball x s, ENNReal.ofReal (‖u v‖ ^ 2) := by
  have hu' : DifferentiableOn ℂ (fun y => u (x + y)) (ball 0 s) := by
    intro y hy
    have hxy : x + y ∈ ball x s := by simpa [mem_ball, dist_eq_norm] using hy
    exact ((hu.differentiableAt (isOpen_ball.mem_nhds hxy)).comp y
      ((differentiable_const x).add differentiable_id y)).differentiableWithinAt
  have hρm : Measurable fun t : ℝ => (Set.Iio s).indicator (fun _ => (1 : ℝ≥0∞)) t :=
    measurable_const.indicator measurableSet_Iio
  have h := ReciprocityTheory.L2DbarEstimates.mv n s _ _ hu' hρm
    (fun t ht => Set.indicator_of_notMem (by simpa using ht) _)
  have e1 : ∀ y : V n, (Set.Iio s).indicator (fun _ => (1 : ℝ≥0∞)) ‖y‖ =
      (ball (0 : V n) s).indicator 1 y := by
    intro y
    by_cases hy : ‖y‖ < s
    · rw [Set.indicator_of_mem (by simpa using hy), Set.indicator_of_mem (by simpa using hy)]; rfl
    · rw [Set.indicator_of_notMem (by simpa using hy), Set.indicator_of_notMem (by simpa using hy)]
  simp only [add_zero, e1] at h
  rw [lintegral_indicator_one measurableSet_ball] at h
  refine h.trans (le_of_eq ?_)
  rw [← lintegral_indicator measurableSet_ball,
    ← lintegral_add_left_eq_self (fun v => (ball x s).indicator (fun v => ENNReal.ofReal (‖u v‖ ^ 2)) v) x]
  refine lintegral_congr fun y => ?_
  by_cases hy : y ∈ ball (0 : V n) s
  · have hxy : x + y ∈ ball x s := by simpa [mem_ball, dist_eq_norm] using hy
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hxy]; simp
  · have hxy : x + y ∉ ball x s := by simpa [mem_ball, dist_eq_norm] using hy
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hxy]; simp

theorem norm_fderiv_le_of_ball {n : ℕ} {p : V n} {ρ R M : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (u : V n → ℂ) (hu : DifferentiableOn ℂ u (ball p R)) (hM : ∀ x ∈ ball p R, ‖u x‖ ≤ M) :
    ‖fderiv ℂ u p‖ ≤ M / ρ := by
  first
  | exact @_root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded
  | exact _root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded
  | (apply _root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded <;> assumption)
  | (intros; apply _root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded ..)

theorem l2_value_deriv_ball :
    ∀ (n : ℕ) (r : ℝ), 0 < r → ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : V n) (u : V n → ℂ),
      DifferentiableOn ℂ u (ball p r) →
        ENNReal.ofReal (‖u p‖ ^ 2 + ‖fderiv ℂ u p‖ ^ 2) ≤
          ENNReal.ofReal C * ∫⁻ v in ball p r, ENNReal.ofReal (‖u v‖ ^ 2) := by
  intro n r hr
  set β : ℝ := (volume (ball (0 : V n) (r / 2))).toReal with hβdef
  have hβ : 0 < β := ENNReal.toReal_pos (measure_ball_pos volume _ (by linarith)).ne'
    measure_ball_lt_top.ne
  have hV : volume (ball (0 : V n) (r / 2)) = ENNReal.ofReal β :=
    (ENNReal.ofReal_toReal measure_ball_lt_top.ne).symm
  refine ⟨(1 + 16 / r ^ 2) / β, by positivity, fun p u hu => ?_⟩
  set I := ∫⁻ v in ball p r, ENNReal.ofReal (‖u v‖ ^ 2) with hIdef
  by_cases hI : I = ⊤
  · rw [hI, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne']; exact le_top
  set J := I.toReal with hJ
  have hI' : I = ENNReal.ofReal J := (ENNReal.ofReal_toReal hI).symm
  have hx : ∀ x ∈ ball p (r / 2), ‖u x‖ ^ 2 ≤ J / β := by
    intro x hx
    have hsub : ball x (r / 2) ⊆ ball p r := by
      apply ball_subset_ball'
      rw [mem_ball] at hx; linarith
    have h2 := (l2ball_sq_mul_vol_le u (hu.mono hsub)).trans (lintegral_mono_set hsub)
    rw [hV, ← ENNReal.ofReal_mul (sq_nonneg _), ← hIdef, hI'] at h2
    rw [le_div_iff₀ hβ]
    exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).1 h2
  set M := Real.sqrt (J / β) with hMdef
  have hJβ : 0 ≤ J / β := div_nonneg ENNReal.toReal_nonneg hβ.le
  have hMx : ∀ x ∈ ball p (r / 2), ‖u x‖ ≤ M := by
    intro x hx'
    have := Real.sqrt_le_sqrt (hx x hx')
    rwa [Real.sqrt_sq (norm_nonneg _)] at this
  have hD := norm_fderiv_le_of_ball (ρ := r / 4) (by positivity) (by linarith) u
    (hu.mono (ball_subset_ball (by linarith))) hMx
  have hD2 : ‖fderiv ℂ u p‖ ^ 2 ≤ 16 / r ^ 2 * (J / β) := by
    have := pow_le_pow_left₀ (norm_nonneg _) hD 2
    refine this.trans (le_of_eq ?_)
    rw [div_pow, Real.sq_sqrt hJβ]; field_simp; ring
  have hp := hx p (mem_ball_self (by linarith))
  rw [hI', ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ‖u p‖ ^ 2 + ‖fderiv ℂ u p‖ ^ 2 ≤ J / β + 16 / r ^ 2 * (J / β) := add_le_add hp hD2
    _ = (1 + 16 / r ^ 2) / β * J := by ring

end

end GlobalTheory
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.exists_eq_smul_of_dvd_dualDistrib : ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (N : Type) [AddCommGroup N] [Module O N] [Module.Projective O M] [Module.Projective O N] (a : O) (z : M ⊗[O] N), (∀ (φ : Module.Dual O M) (ψ : Module.Dual O N), a ∣ TensorProduct.dualDistrib O M N (φ ⊗ₜ ψ) z) → ∃ y, z = a • y := by
  first | exact @GlobalTheory.tensor_projective_dvd_of_coord_dvd | exact GlobalTheory.tensor_projective_dvd_of_coord_dvd | (intros; apply GlobalTheory.tensor_projective_dvd_of_coord_dvd <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WedgeDiag

variable {R : Type} [CommRing R] {I : Type} [LinearOrder I]

noncomputable def lowerWedge :
    (I →₀ R) →ₗ[R] (I →₀ R) →ₗ[R] ⋀[R]^2 (I →₀ R) :=
  Finsupp.linearCombination R (fun i => Finsupp.linearCombination R (fun j =>
    if i < j then exteriorPower.ιMulti R 2 ![Finsupp.single i 1, Finsupp.single j 1] else 0))

noncomputable def wedgeBil {M : Type} [AddCommGroup M] [Module R M] :
    M →ₗ[R] M →ₗ[R] ⋀[R]^2 M :=
  LinearMap.mk₂ R (fun x y => exteriorPower.ιMulti R 2 ![x, y])
    (fun x x' y => by
      simpa using (exteriorPower.ιMulti R 2).toMultilinearMap.cons_add ![y] x x')
    (fun c x y => by
      simpa using (exteriorPower.ιMulti R 2).toMultilinearMap.cons_smul ![y] c x)
    (fun x y y' => by
      have h := fun a b : M => (exteriorPower.ιMulti R 2).map_swap ![a, b] (i := 0) (j := 1) (by decide)
      have e : ∀ a b : M, ![a, b] ∘ Equiv.swap 0 1 = ![b, a] := by
        intro a b; ext k; fin_cases k <;> rfl
      simp only [e] at h
      have h1 : exteriorPower.ιMulti R 2 ![y + y', x] = exteriorPower.ιMulti R 2 ![y, x] + exteriorPower.ιMulti R 2 ![y', x] := by
        simpa using (exteriorPower.ιMulti R 2).toMultilinearMap.cons_add ![x] y y'
      rw [h (y + y') x, h y x, h y' x, h1, neg_add])
    (fun c x y => by
      have h := fun a b : M => (exteriorPower.ιMulti R 2).map_swap ![a, b] (i := 0) (j := 1) (by decide)
      have e : ∀ a b : M, ![a, b] ∘ Equiv.swap 0 1 = ![b, a] := by
        intro a b; ext k; fin_cases k <;> rfl
      simp only [e] at h
      have h1 : exteriorPower.ιMulti R 2 ![c • y, x] = c • exteriorPower.ιMulti R 2 ![y, x] := by
        simpa using (exteriorPower.ιMulti R 2).toMultilinearMap.cons_smul ![x] c y
      rw [h (c • y) x, h y x, h1, smul_neg])

theorem wedgeBil_apply {M : Type} [AddCommGroup M] [Module R M] (x y : M) :
    wedgeBil x y = exteriorPower.ιMulti R 2 ![x, y] := rfl

theorem lowerWedge_sub_flip :
    lowerWedge (R := R) (I := I) - lowerWedge.flip = wedgeBil (M := I →₀ R) := by
  ext i j
  simp only [lowerWedge, LinearMap.sub_apply, LinearMap.flip_apply, LinearMap.coe_comp,
    Function.comp_apply, Finsupp.lsingle_apply, Finsupp.linearCombination_single, one_smul,
    LinearMap.smul_apply, wedgeBil_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, h.not_gt]
  · simp only [lt_irrefl, if_false, sub_zero]
    exact congrArg _ ((exteriorPower.ιMulti R 2 (M := I →₀ R)).map_eq_zero_of_eq ![Finsupp.single i 1, Finsupp.single i 1] (i := 0) (j := 1) rfl (by decide)).symm
  · have hs := (exteriorPower.ιMulti R 2).map_swap ![Finsupp.single j (1:R), Finsupp.single i 1] (i := 0) (j := 1) (by decide)
    have e : ![Finsupp.single j (1:R), Finsupp.single i 1] ∘ Equiv.swap 0 1 = ![Finsupp.single i 1, Finsupp.single j 1] := by
      ext k; fin_cases k <;> rfl
    rw [e] at hs
    simp [h, h.not_gt, hs]

end GlobalTheory.WedgeDiag

namespace GlobalTheory.WedgeDiag

variable {R : Type} [CommRing R] {I : Type} [LinearOrder I]

noncomputable def crossWedge :
    ((I →₀ R) × (I →₀ R)) [⋀^Fin 2]→ₗ[R] ⋀[R]^2 (I →₀ R) where
  toFun v := lowerWedge (v 0).1 (v 1).2 - lowerWedge (v 1).1 (v 0).2
  map_update_add' := by
    intro _ v i x y
    fin_cases i <;> simp [Function.update_of_ne, map_add (f := _), LinearMap.add_apply] <;> abel
  map_update_smul' := by
    intro _ v i c x
    fin_cases i <;> simp [Function.update_of_ne, map_smul, LinearMap.smul_apply, smul_sub]
  map_eq_zero_of_eq' := by
    intro v i j h hij
    fin_cases i <;> fin_cases j <;> simp_all

theorem crossWedge_apply (v : Fin 2 → (I →₀ R) × (I →₀ R)) :
    crossWedge v = lowerWedge (v 0).1 (v 1).2 - lowerWedge (v 1).1 (v 0).2 := rfl

noncomputable def crossWedgeLin : ⋀[R]^2 ((I →₀ R) × (I →₀ R)) →ₗ[R] ⋀[R]^2 (I →₀ R) :=
  exteriorPower.alternatingMapLinearEquiv crossWedge

theorem crossWedgeLin_inl :
    crossWedgeLin ∘ₗ exteriorPower.map 2 (LinearMap.inl R (I →₀ R) (I →₀ R)) = 0 := by
  ext v
  simp [crossWedgeLin, crossWedge_apply]

theorem crossWedgeLin_inr :
    crossWedgeLin ∘ₗ exteriorPower.map 2 (LinearMap.inr R (I →₀ R) (I →₀ R)) = 0 := by
  ext v
  simp [crossWedgeLin, crossWedge_apply]

theorem crossWedgeLin_diag :
    crossWedgeLin ∘ₗ exteriorPower.map 2
      (LinearMap.inl R (I →₀ R) (I →₀ R) + LinearMap.inr R (I →₀ R) (I →₀ R)) = LinearMap.id := by
  ext v
  have h := LinearMap.congr_fun₂ (lowerWedge_sub_flip (R := R) (I := I)) (v 0) (v 1)
  simp only [LinearMap.sub_apply, LinearMap.flip_apply, wedgeBil_apply] at h
  have hv : ![v 0, v 1] = v := by ext k; fin_cases k <;> rfl
  rw [hv] at h
  simp [crossWedgeLin, crossWedge_apply, h]

theorem free_case (t : ⋀[R]^2 (I →₀ R))
    (H : exteriorPower.map 2 (LinearMap.inl R (I →₀ R) (I →₀ R) + LinearMap.inr R (I →₀ R) (I →₀ R)) t =
      exteriorPower.map 2 (LinearMap.inl R (I →₀ R) (I →₀ R)) t +
        exteriorPower.map 2 (LinearMap.inr R (I →₀ R) (I →₀ R)) t) : t = 0 := by
  have h := congrArg crossWedgeLin H
  rw [map_add (f := _), ← LinearMap.comp_apply, ← LinearMap.comp_apply crossWedgeLin, ← LinearMap.comp_apply crossWedgeLin,
    crossWedgeLin_diag, crossWedgeLin_inl, crossWedgeLin_inr] at h
  simpa using h

end GlobalTheory.WedgeDiag

namespace GlobalTheory.WedgeDiag

theorem eq_zero_of_diag_additive : ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Module.Projective R M] (t : ⋀[R]^2 M), exteriorPower.map 2 (LinearMap.inl R M M + LinearMap.inr R M M) t = exteriorPower.map 2 (LinearMap.inl R M M) t + exteriorPower.map 2 (LinearMap.inr R M M) t → t = 0 := by
  intro R M _ _ _ _ t H
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective R M)
  letI : LinearOrder M := IsWellOrder.linearOrder WellOrderingRel
  set p : (M →₀ R) →ₗ[R] M := Finsupp.linearCombination R id
  have e0 : (LinearMap.inl R (M →₀ R) (M →₀ R) + LinearMap.inr R (M →₀ R) (M →₀ R)) ∘ₗ s =
      (s.prodMap s) ∘ₗ (LinearMap.inl R M M + LinearMap.inr R M M) := by
    ext x <;> simp
  have e1 : (s.prodMap s) ∘ₗ LinearMap.inl R M M = LinearMap.inl R (M →₀ R) (M →₀ R) ∘ₗ s := by
    ext x <;> simp
  have e2 : (s.prodMap s) ∘ₗ LinearMap.inr R M M = LinearMap.inr R (M →₀ R) (M →₀ R) ∘ₗ s := by
    ext x <;> simp
  have hu : exteriorPower.map 2 s t = 0 := by
    apply free_case
    have h := congrArg (exteriorPower.map 2 (s.prodMap s)) H
    rw [map_add (f := _)] at h
    simp only [← LinearMap.comp_apply, ← exteriorPower.map_comp] at h ⊢
    rw [e0, ← e1, ← e2]
    exact h
  have := congrArg (exteriorPower.map 2 p) hu
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, hs, exteriorPower.map_id, map_zero] at this
  exact this

end GlobalTheory.WedgeDiag
end

section

open Filter Topology

theorem _root_.GlobalTheory.T.exists_linearIndependent_products_function_field : ∀ (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin D → K), IsTranscendenceBasis ℤ x → ∀ (J : Type) [Fintype J] (e : J → K), LinearIndependent ℤ e → ∀ m : ℕ, 0 < m → ∃ v : Fin (Fintype.card J * m ^ D) → K, LinearIndependent ℤ v ∧ ∀ s, ∃ (u : Fin m → J) (a : Fin D → ℕ), (∀ i, a i < m) ∧ v s = (∏ l, e (u l)) * ∏ i, x i ^ a i := by
  first | exact @GlobalTheory.many_independent_products_in_function_field | exact GlobalTheory.many_independent_products_in_function_field | (intros; apply GlobalTheory.many_independent_products_in_function_field <;> assumption)
end

section

open scoped Matrix

theorem _root_.GlobalTheory.T.exists_isotropic_graph_unitary_isUnit_lowerBlock : ∀ (O : Type) [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    (∃ x : O, IsUnit (c x - x)) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
    ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O, IsUnit g.det →
      gᵀ * Matrix.fromBlocks 0 J J 0 * g.map c = Matrix.fromBlocks 0 J J 0 →
      ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ IsUnit (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det := by
  first | exact @GlobalTheory.exists_isotropic_graph_isUnit_lowerRow | exact GlobalTheory.exists_isotropic_graph_isUnit_lowerRow | (intros; apply GlobalTheory.exists_isotropic_graph_isUnit_lowerRow <;> assumption)
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

theorem _root_.GlobalTheory.T.map_linearEquiv_addHaar_localField : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (T : V ≃ₗ[F] V), μ.map T = (distribHaarChar F (LinearEquiv.det T))⁻¹ • μ := by
  first | exact @GlobalTheory.KSp.map_linearEquiv_haar | exact GlobalTheory.KSp.map_linearEquiv_haar | (intros; apply GlobalTheory.KSp.map_linearEquiv_haar <;> assumption)
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

theorem _root_.GlobalTheory.T.homogeneousMeasure_eq_smul_addHaar_localField : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (lam : Measure F) [lam.IsAddHaarMeasure] (n : Measure F) [IsFiniteMeasureOnCompacts n], n {0} = 0 → (∀ u : Fˣ, n.map (fun x => (u : F) * x) = (distribHaarChar F u)⁻¹ • n) → ∃ r : NNReal, n = r • lam := by
  first | exact @GlobalTheory.KSp.Homog.eq_smul_haar_of_homog | exact GlobalTheory.KSp.Homog.eq_smul_haar_of_homog | (intros; apply GlobalTheory.KSp.Homog.eq_smul_haar_of_homog <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.constantCoeff_subst_of_forall_constantCoeff_zero : ∀ (R : Type) [CommRing R] (σ τ : Type) [Finite σ] (a : σ → MvPowerSeries τ R), (∀ i, constantCoeff (a i) = 0) → ∀ g : MvPowerSeries σ R, constantCoeff (subst a g) = constantCoeff g := by
  first | exact @GlobalTheory.constantCoeff_subst_of_constantCoeff_zero | exact GlobalTheory.constantCoeff_subst_of_constantCoeff_zero | (intros; apply GlobalTheory.constantCoeff_subst_of_constantCoeff_zero <;> assumption)
end
