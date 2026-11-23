module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1498
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1499
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1500
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1404
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1413
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1414
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1325
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1428
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1103
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1494
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle005
import ReciprocityTheory.L2DbarEstimates.LeviForms.OfRealNormSqSumMul
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle008
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes

namespace GlobalTheory.LKRes

theorem sigRes_iterate_val (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (n r k : ℕ) (g : GL (Fin n) (KQ p K r)) (i j : Fin n) :
    (((⇑(sigRes p K n r))^[k] g : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) i j =
      (⇑(sigKQ p K r))^[k] ((g : Matrix (Fin n) (Fin n) (KQ p K r)) i j) := by
  induction k generalizing g with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    rfl

theorem sigRes_iterate_eq_self : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r : ℕ), 0 < r → ∀ g : GL (Fin n) (KQ p K r), (⇑(sigRes p K n r))^[r] g = g := by
  intro p _ K n r hr g
  apply Units.ext
  ext i j
  rw [sigRes_iterate_val]
  exact GlobalTheory.T.padicTensorUnramifiedFrobTwist_iterate_degree p K r hr _

end GlobalTheory.LKRes
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.finite_padicTensorUnramifiedIntegers_quot_primePow : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r m : ℕ), Finite (GlobalTheory.LKLoc.intK p K ⧸ Ideal.span {(p : GlobalTheory.LKLoc.intK p K) ^ m}) → Finite (GlobalTheory.LKLoc.intK p (Qr p r) ⧸ Ideal.span {(p : GlobalTheory.LKLoc.intK p (Qr p r)) ^ m}) → Finite (intKQ p K r ⧸ Ideal.span {(p : intKQ p K r) ^ m}) := by
  first | (exact @GlobalTheory.TenFin.finite_intKQ_quot) | (exact GlobalTheory.TenFin.finite_intKQ_quot) | (intros; apply GlobalTheory.TenFin.finite_intKQ_quot  <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem exists_sec_nonvanishing_finite : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ S : Set X, S.Finite → ∃ e : ℕ, 0 < e ∧ ∃ f ∈ P.H e 0, S ⊆ NV P e 0 f := by
  intro k _ X _ p D _ P hA S hS
  obtain ⟨n, hn, s, h₁, -, -⟩ := hA.exists_affine_finite_subset hS (U := ⊤) (Set.subset_univ _)
  obtain ⟨f, hf, e⟩ := (GlobalTheory.T.lineBundlePow_sections_rationalFunctions_loci k X p P n).1 s
  refine ⟨n, hn, f, hf, ?_⟩
  rw [e]
  exact h₁

end GlobalTheory.HSAmp
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ResMap

def stalkEquiv {X : Scheme.{0}} [IsIntegral X] (x : X) : X.presheaf.stalk x ≃+* locRing x :=
  RingEquiv.ofBijective (algebraMap (X.presheaf.stalk x) X.functionField).rangeRestrict
    ⟨fun _ _ e => IsFractionRing.injective _ X.functionField (congrArg Subtype.val e),
      RingHom.rangeRestrict_surjective _⟩

theorem residueMap : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (z : X) (k : ℕ),
  topologicalKrullDim (closure ({z} : Set X)) = k →
  ∃ (κ : Type) (_ : Field κ) (_ : Algebra ℂ κ) (π₀ : locRing z →+* κ),
    Function.Surjective π₀ ∧ (∀ r : locRing z, π₀ r = 0 ↔ ZeroAt z (r : X.functionField)) ∧
    (∀ a (h : Cartier.constFn p a ∈ locRing z), π₀ ⟨Cartier.constFn p a, h⟩ = algebraMap ℂ κ a) ∧
    (∃ w : Fin k → κ, TrBasis (algebraMap ℂ κ) w) ∧
    ∀ (x : X) (h : locRing x ≤ locRing z), IsLocModel (algebraMap ℂ κ) (π₀.comp (Subring.inclusion h)).range ∧
      (∀ f : κ, ∃ a b : locRing x, π₀ (Subring.inclusion h b) ≠ 0 ∧ f * π₀ (Subring.inclusion h b) = π₀ (Subring.inclusion h a)) ∧
      (IsClosed ({x} : Set X) → RatRes (algebraMap ℂ κ) (π₀.comp (Subring.inclusion h)).range) := by
  intro X _ _ p hp z k hk
  have hprop : IsProper p := by
    obtain ⟨N, j, hj, rfl⟩ := hp
    have := isProper_str ℂ N
    infer_instance
  have hsep : X.IsSeparated := ⟨by rw [← Limits.terminal.comp_from p]; infer_instance⟩
  obtain ⟨Z, i, hi, hZ, rfl⟩ := GlobalTheory.exists_isClosedImmersion_genericPoint z
  let q := i ≫ p
  have hrange : Set.range i = closure ({i (genericPoint Z)} : Set X) := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h₁
    exact (isGenericPoint_def.mp h₁).symm
  have hdim : topologicalKrullDim Z = k := by
    rw [← GlobalTheory.topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hrange]
    exact hk
  obtain ⟨-, w, hw⟩ := isLocModel_locRing_and_exists_trBasis Z q k (genericPoint Z) hdim
  letI alg : Algebra ℂ Z.functionField := (Cartier.constFn q).toAlgebra
  let π₀ : locRing (i (genericPoint Z)) →+* Z.functionField :=
    (i.stalkMap (genericPoint Z)).hom.comp (stalkEquiv (i (genericPoint Z))).symm.toRingHom
  refine ⟨Z.functionField, inferInstance, alg, π₀, ?_, ?_, ?_, ⟨w, hw⟩, ?_⟩
  · exact (i.stalkMap_surjective _).comp (stalkEquiv _).symm.surjective
  · intro r
    obtain ⟨a, rfl⟩ := (stalkEquiv _).surjective r
    have e1 : π₀ (stalkEquiv _ a) = (i.stalkMap (genericPoint Z)).hom a := by
      show (i.stalkMap (genericPoint Z)).hom ((stalkEquiv _).symm (stalkEquiv _ a)) = _
      rw [RingEquiv.symm_apply_apply]
    have e2 : ((stalkEquiv _ a : locRing _) : X.functionField) = algebraMap _ _ a := rfl
    rw [e1, e2]
    constructor
    · intro h0
      refine ⟨a, ?_, rfl⟩
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have := hu.map (i.stalkMap (genericPoint Z)).hom
      rw [h0] at this
      exact not_isUnit_zero this
    · rintro ⟨b, hb, e⟩
      obtain rfl := IsFractionRing.injective _ X.functionField e
      by_contra hne
      have hu : IsUnit ((i.stalkMap (genericPoint Z)).hom b) := isUnit_iff_ne_zero.2 hne
      exact (IsLocalRing.mem_maximalIdeal _).1 hb ((isUnit_map_iff _ _).1 hu)
  · intro a ha
    have hg := (algebraMap_germ (X := X) (x := i (genericPoint Z)) (U := ⊤) trivial (algX p ⊤ a)).trans
      (RingHom.congr_fun (fnOf_comp_algX p ⊤ (gen_mem (x := i (genericPoint Z)) trivial)) a)
    have hr : (⟨Cartier.constFn p a, ha⟩ : locRing _) =
        stalkEquiv _ (X.presheaf.germ ⊤ _ trivial (algX p ⊤ a)) := Subtype.ext hg.symm
    rw [hr]
    show (i.stalkMap (genericPoint Z)).hom ((stalkEquiv _).symm (stalkEquiv _ _)) = _
    rw [RingEquiv.symm_apply_apply]
    erw [Scheme.Hom.germ_stalkMap_apply i ⊤ (genericPoint Z) trivial (algX p ⊤ a)]
    have hc : (i.app ⊤).hom (algX p ⊤ a) = algX q (i ⁻¹ᵁ ⊤) a := by
      have e : (i ≫ p).appLE ⊤ (i ⁻¹ᵁ ⊤) (le_top.trans (Scheme.Hom.preimage_top _).ge) =
          p.appLE ⊤ ⊤ (le_top.trans (Scheme.Hom.preimage_top _).ge) ≫ i.appLE ⊤ (i ⁻¹ᵁ ⊤) le_rfl := by
        first
          | rw [Scheme.Hom.appLE_comp_appLE]
          | (simp only [Scheme.Hom.comp_appLE, Scheme.Hom.appLE, Category.assoc,
              Scheme.Hom.naturality_assoc]; rfl)
      simp only [algX, q, RingHom.comp_apply]
      rw [Scheme.Hom.app_eq_appLE, e, CommRingCat.comp_apply]
    rw [hc]
    exact RingHom.congr_fun (fnOf_comp_algX q (i ⁻¹ᵁ ⊤) (gen_mem (x := genericPoint Z) trivial)) a
  · intro x h
    have hs : i (genericPoint Z) ⤳ x := GlobalTheory.T.specializes_of_pointLocalRing_le_separated X x _ h
    obtain ⟨y, rfl⟩ : x ∈ Set.range i := by
      rw [hrange]; exact specializes_iff_mem_closure.mp hs
    have key : ∀ a : X.presheaf.stalk (i y),
        π₀ (Subring.inclusion h ⟨algebraMap _ X.functionField a, a, rfl⟩) =
          algebraMap (Z.presheaf.stalk y) Z.functionField ((i.stalkMap y).hom a) := by
      intro a
      have e : (Subring.inclusion h ⟨algebraMap _ X.functionField a, a, rfl⟩ : locRing _) =
          stalkEquiv _ ((X.presheaf.stalkSpecializes hs).hom a) := by
        apply Subtype.ext
        show algebraMap _ X.functionField a =
          algebraMap _ X.functionField ((X.presheaf.stalkSpecializes hs).hom a)
        simp only [RingHom.algebraMap_toAlgebra]
        rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]
      rw [e]
      show (i.stalkMap (genericPoint Z)).hom ((stalkEquiv _).symm (stalkEquiv _ _)) = _
      rw [RingEquiv.symm_apply_apply]
      exact Scheme.Hom.stalkSpecializes_stalkMap_apply i (genericPoint Z) y
        ((genericPoint_spec Z).specializes trivial) a
    have hR : (π₀.comp (Subring.inclusion h)).range = locRing y := by
      ext f
      constructor
      · rintro ⟨⟨r, a, rfl⟩, rfl⟩
        exact ⟨(i.stalkMap y).hom a, (key a).symm⟩
      · rintro ⟨b, rfl⟩
        obtain ⟨a, rfl⟩ := i.stalkMap_surjective y b
        exact ⟨⟨_, a, rfl⟩, key a⟩
    have hloc : IsLocModel (Cartier.constFn q) (locRing y) := isLocModel_locRing y
    rw [hR]
    refine ⟨hloc, fun f => ?_, fun hx => ?_⟩
    · obtain ⟨a', ha', b', hb', hb0, e⟩ := hloc.frac f
      rw [← hR] at ha' hb'
      obtain ⟨a, rfl⟩ := ha'
      obtain ⟨b, rfl⟩ := hb'
      exact ⟨a, b, hb0, e⟩
    · have hy : IsClosed ({y} : Set Z) := by
        have hpre : (i : Z → X) ⁻¹' {i y} = {y} := by
          ext t
          simp only [Set.mem_preimage, Set.mem_singleton_iff]
          exact i.isClosedEmbedding.injective.eq_iff
        rw [← hpre]
        exact hx.preimage i.continuous
      exact GlobalTheory.T.hasRationalResidueField_pointLocalRing_closedPoint Z q y hy

end GlobalTheory.ResMap
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.topologicalKrullDim_le_zero_fibre_affineOpen : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), GlobalTheory.MixHt.IsAmb p → ∀ (ℓ : ℕ) (U : X.Opens) (C : Set X), ℓ.Prime → IsAffineOpen U → IsIrreducible C → IsClosed C → C ⊆ GlobalTheory.HSAmp.fib X ℓ → C ⊆ (U : Set X) → topologicalKrullDim C ≤ 0 := by
  first | exact @GlobalTheory.MixHt.dim_le_zero_of_fib_of_subset_affine | exact GlobalTheory.MixHt.dim_le_zero_of_fib_of_subset_affine | (intros; apply GlobalTheory.MixHt.dim_le_zero_of_fib_of_subset_affine <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false


namespace GlobalTheory.HSAmp

open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y

theorem semiPos_up_of_isCan : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x →
    ∀ (n : ℕ) (u : SmFn p), 1 ≤ n → IsCan P e n x u → (up P.L u).SemiPos D := by
  intro k _ X _ p D _ P e x hx n u hn hu σ i c y hy ξ
  set j := pick (P.A.φ σ).isLB y
  have hj : y ∈ ptsIn p σ (P.A.B.U j) := mem_pick (P.A.φ σ).isLB y
  set O := ptsIn p σ (P.L.B.U i) ∩ ptsIn p σ (P.A.B.U j) with hOdef
  have hO : IsOpen O := (isOpen_ptsIn _).inter (isOpen_ptsIn _)
  have he : (0 : ℝ) < e := by exact_mod_cast hx.pos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hen : (0 : ℝ) < (e : ℝ) * n := mul_pos he hn'

  have key : ∀ z ∈ O, 0 < ∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) z ^ n) ∧
      (P.L.φ σ).φ i z + u.u σ z =
        ((e : ℝ) * n)⁻¹ * Real.log (∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) z ^ n)) := by
    intro z hz
    have hnu : ∀ l, P.nu e 0 σ z (x l) ^ (2 * n) =
        Complex.normSq (ratVal (P.loc e 0 (x l) i j) z ^ n) * Real.exp (-((e : ℝ) * n) * (P.L.φ σ).φ i z) := by
      intro l
      rw [GlobalTheory.VolBr.nu_eq k X p P e 0 (x l) (hx.mem l) σ z i j hz.1 hz.2, Complex.normSq_eq_norm_sq, norm_pow,
        mul_pow, ← pow_mul, ← Real.exp_nat_mul]
      congr 2
      · ring_nf
      · push_cast; ring
    have hsum : ∑ l, P.nu e 0 σ z (x l) ^ (2 * n) =
        (∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) z ^ n)) * Real.exp (-((e : ℝ) * n) * (P.L.φ σ).φ i z) := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun l _ => hnu l
    have hpos : 0 < ∑ l, P.nu e 0 σ z (x l) ^ (2 * n) := by
      obtain ⟨l, hl⟩ := hx.cover (under z)
      have h1 := ((GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P e 0 (x l) (hx.mem l)).2.2.2.2 (x l) (hx.mem l) σ z hl).2
      exact Finset.sum_pos' (fun l' _ => pow_nonneg (by unfold Pair.nu; positivity) _)
        ⟨l, Finset.mem_univ _, pow_pos h1 _⟩
    have hS : 0 < ∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) z ^ n) := by
      rw [hsum] at hpos
      exact pos_of_mul_pos_left hpos (Real.exp_pos _).le
    refine ⟨hS, ?_⟩
    rw [hu σ z, hsum, Real.log_mul hS.ne' (Real.exp_pos _).ne', Real.log_exp]
    field_simp
    ring
  have hyO : y ∈ O := ⟨hy.2, hj⟩
  have hW : IsOpen (c.e.target ∩ c.e.symm ⁻¹' O) := GlobalTheory.ChartGlue.isOpen_over c.e hO
  have hyW : c.e y ∈ c.e.target ∩ c.e.symm ⁻¹' O := GlobalTheory.ChartGlue.mem_over c.e hy.1 hyO
  have hG : ∀ l, ContDiffAt ℂ 2 (fun v => ratVal (P.loc e 0 (x l) i j) (c.e.symm v) ^ n) (c.e y) := fun l =>
    contDiffAt_two_of_holo hW (((GlobalTheory.T.sectionLocalFunction_continuousOn_holomorphicChart k X p P e 0 σ (x l) (hx.mem l) i j).2 D c).pow n) hyW
  have hS : 0 < ∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) (c.e.symm (c.e y)) ^ n) :=
    (key _ hyW.2).1
  have hf : ContDiffAt ℝ 2 (fun v => Real.log (∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) (c.e.symm v) ^ n)))
      (c.e y) :=
    (ContDiffAt.sum fun l _ => contDiffAt_normSq_comp (hG l)).log hS.ne'
  have heq : (fun v => ((((P.L.φ σ).addFn (u.u σ)).φ i (c.e.symm v) : ℝ) : ℂ)) =ᶠ[𝓝 (c.e y)]
      fun v => ((((e : ℝ) * n)⁻¹ *
        Real.log (∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) (c.e.symm v) ^ n)) + 0 : ℝ) : ℂ) :=
    eventually_of_mem (hW.mem_nhds hyW) fun v hv => by
      dsimp only
      rw [add_zero, ← (key _ hv.2).2]
      rfl
  change 0 ≤ (leviV D (fun v => ((((P.L.φ σ).addFn (u.u σ)).φ i (c.e.symm v) : ℝ) : ℂ)) (c.e y) ξ).re
  rw [leviV_congr heq, leviV_const_mul hf _ 0, Complex.re_ofReal_mul]
  exact mul_nonneg (inv_nonneg.2 hen.le) (leviV_log_sum_nonneg (fun l => contDiffAt_normSq_comp (hG l))
    (fun l => logPshAt_normSq (hG l)) hS ξ)

end GlobalTheory.HSAmp
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem canNorms : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ (n : ℕ) (u : SmFn p), 1 ≤ n → IsCan P e n x u → (∀ l (σ : k →+* ℂ) (y : CxPts p σ), (upperParabolic P u).nu e 0 σ y (x l) ≤ 1) ∧ (∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ l, Real.exp (-(Real.log (D + 1) / (2 * n))) ≤ (upperParabolic P u).nu e 0 σ y (x l)) ∧ Gens (upperParabolic P u) D e x ∧ Gens P D (e * n) (fun l => x l ^ n) ∧ IsCan P (e * n) 1 (fun l => x l ^ n) u := by
  intro k _ X _ p D _ P e x hx n u hn hu
  have he : (0 : ℝ) < e := by exact_mod_cast hx.pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : 2 * n ≠ 0 := by omega
  have hup := GlobalTheory.T.raiseFirstWeight_sections_loci_values_norms k X p P u (e : ℤ) 0
  have hnn : ∀ (Q : Pair p) σ (y : CxPts p σ) f, 0 ≤ Q.nu e 0 σ y f := fun Q σ y f => by
    rw [← norm_val]; exact norm_nonneg _
  have hS : ∀ σ (y : CxPts p σ), 0 < ∑ l, P.nu e 0 σ y (x l) ^ (2 * n) := by
    intro σ y
    obtain ⟨l, hl⟩ := hx.cover (under y)
    have h := ((GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P e 0 (x l) (hx.mem l)).2.2.2.2 (x l) (hx.mem l) σ y hl).2
    exact lt_of_lt_of_le (pow_pos h _) (Finset.single_le_sum (f := fun l => P.nu e 0 σ y (x l) ^ (2 * n))
      (fun i _ => pow_nonneg (hnn P σ y _) _) (Finset.mem_univ l))
  have key : ∀ σ (y : CxPts p σ) f, (upperParabolic P u).nu e 0 σ y f ^ (2 * n) =
      P.nu e 0 σ y f ^ (2 * n) / ∑ l, P.nu e 0 σ y (x l) ^ (2 * n) := by
    intro σ y f
    rw [(hup.2.2 σ y f).2, mul_pow, ← Real.exp_nat_mul, hu σ y]
    have : ((2 * n : ℕ) : ℝ) * (-(((e : ℤ) : ℝ) * (((e : ℝ) * n)⁻¹ * Real.log (∑ l, P.nu e 0 σ y (x l) ^ (2 * n)))) / 2)
        = -Real.log (∑ l, P.nu e 0 σ y (x l) ^ (2 * n)) := by
      push_cast; field_simp
    rw [this, Real.exp_neg, Real.exp_log (hS σ y), div_eq_mul_inv]
  refine ⟨fun l σ y => ?_, fun σ y => ?_, ⟨hx.pos, fun l => hup.1 ▸ hx.mem l, fun z => ?_⟩, ⟨?_, fun l => ?_, fun z => ?_⟩, ?_⟩
  · rw [← pow_le_pow_iff_left₀ (hnn _ σ y _) zero_le_one hn0, one_pow, key, div_le_one (hS σ y)]
    exact Finset.single_le_sum (f := fun l => P.nu e 0 σ y (x l) ^ (2 * n))
      (fun i _ => pow_nonneg (hnn P σ y _) _) (Finset.mem_univ l)
  · obtain ⟨l, -, hl⟩ := Finset.exists_max_image Finset.univ (fun l => P.nu e 0 σ y (x l)) Finset.univ_nonempty
    refine ⟨l, ?_⟩
    rw [← pow_le_pow_iff_left₀ (Real.exp_pos _).le (hnn _ σ y _) hn0, key, ← Real.exp_nat_mul]
    have e1 : ((2 * n : ℕ) : ℝ) * -(Real.log (D + 1) / (2 * n)) = -Real.log (D + 1) := by
      push_cast; field_simp
    have hD : (0 : ℝ) < D + 1 := by positivity
    rw [e1, Real.exp_neg, Real.exp_log hD, inv_eq_one_div, div_le_div_iff₀ hD (hS σ y), one_mul]
    calc ∑ i, P.nu e 0 σ y (x i) ^ (2 * n) ≤ ∑ _i : Fin (D + 1), P.nu e 0 σ y (x l) ^ (2 * n) :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (hnn P σ y _) (hl i (Finset.mem_univ i)) _
      _ = P.nu e 0 σ y (x l) ^ (2 * n) * (D + 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  · obtain ⟨l, hl⟩ := hx.cover z
    exact ⟨l, (hup.2.1 (x l)).symm ▸ hl⟩
  · exact Nat.mul_pos hx.pos hn
  · have h := (GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P e 0 (x l) (hx.mem l) n).1
    convert h using 2 <;> push_cast <;> ring
  · obtain ⟨l, hl⟩ := hx.cover z
    refine ⟨l, ?_⟩
    have h := (GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P e 0 (x l) (hx.mem l)).2.2.1 n hn
    have e2 : ((e * n : ℕ) : ℤ) = (n : ℤ) * (e : ℤ) := by push_cast; ring
    have e3 : (0 : ℤ) = (n : ℤ) * 0 := by ring
    show z ∈ NV P ((e * n : ℕ) : ℤ) 0 (x l ^ n)
    rw [e2, e3, h]; exact hl
  · intro σ y
    have hp : ∀ l, P.nu ((e * n : ℕ) : ℤ) 0 σ y (x l ^ n) = P.nu e 0 σ y (x l) ^ n := fun l => by
      have h := (GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P e 0 (x l) (hx.mem l) n).2 σ y
      convert h using 2 <;> push_cast <;> ring
    rw [hu σ y]
    simp only [hp, ← pow_mul]
    push_cast
    ring_nf

end GlobalTheory.HSAmp
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp

def conjPt {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} (y : CxPts p σ) :
    CxPts p ((starRingEnd ℂ).comp σ) :=
  ⟨spMap (starRingEnd ℂ) ≫ y.1, by
    have e : spMap ((starRingEnd ℂ).comp σ) = spMap (starRingEnd ℂ) ≫ spMap σ := by
      rw [spMap, spMap, spMap, ← Spec.map_comp]
      rfl
    rw [Category.assoc, y.2, e]⟩

theorem ratVal_conj {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp k} {σ σ' : k →+* ℂ}
    {f : X.functionField} {y : CxPts q σ} {y' : CxPts q σ'}
    (h : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) (hf : RegAt (under y) f) :
    ratVal f y' = starRingEnd ℂ (ratVal f y) := by
  obtain ⟨U, hU, a, rfl⟩ := hf.exists_fnOf
  have hy : y ∈ ptsIn q σ U := mem_ptsIn.2 hU
  rw [ratVal_fnOf hy, ratVal_fnOf (CxPts.mem_ptsIn_conj h hy), CxPts.ev_conj h hy]

theorem val_conj : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ), ∃ (σ' : k →+* ℂ) (y' : CxPts p σ') (θ : ℂ), ‖θ‖ = 1 ∧ ∀ f ∈ P.H a b, val P a b σ' y' f = θ * (starRingEnd ℂ) (val P a b σ y f) := by
  intro k _ X _ p P a b σ y
  have h : (conjPt y).1 = spMap (starRingEnd ℂ) ≫ y.1 := rfl
  have hi := mem_pick (P.L.φ σ).isLB y
  have hj := mem_pick (P.A.φ σ).isLB y
  obtain ⟨θ₁, h₁, e₁⟩ := GlobalTheory.T.sectionValueUnitFrame_eq_localFunction_unitScalar k X p P a b σ y _ _ hi hj
  obtain ⟨θ₂, h₂, e₂⟩ := GlobalTheory.T.sectionValueUnitFrame_eq_localFunction_unitScalar k X p P a b _ (conjPt y) _ _
    (CxPts.mem_ptsIn_conj h hi) (CxPts.mem_ptsIn_conj h hj)
  refine ⟨_, conjPt y, θ₂ * θ₁, by rw [norm_mul, h₁, h₂, one_mul], fun f hf => ?_⟩
  have hreg := hf _ _ _ (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)
  rw [e₁ f hf, e₂ f hf, ratVal_conj h hreg, P.L.conj σ _ _ y _ h hi, P.A.conj σ _ _ y _ h hj]
  have hθ : θ₁ * starRingEnd ℂ θ₁ = 1 := by
    rw [Complex.mul_conj', h₁]
    simp
  simp only [map_mul, Complex.conj_ofReal]
  linear_combination (-(θ₂ * starRingEnd ℂ (ratVal (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) y) *
    ((Real.exp (-(a * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + b * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2) : ℝ) : ℂ))) * hθ

end GlobalTheory.HSAmp
end
end

section

open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix

theorem _root_.GlobalTheory.T.bergman_function_total_mass_extremal : ∀ (S : Type) (Y : S → Type) [∀ σ, MeasurableSpace (Y σ)] (ι : Type) [Fintype ι] [DecidableEq ι] (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ), IsFam μ v → (gram μ v).PosDef → (∀ σ, Integrable (bergmanDensity μ v σ) (μ σ)) ∧ ∑ᶠ σ, ∫ y, bergmanDensity μ v σ y ∂μ σ = Fintype.card ι ∧ (∀ σ y, 0 ≤ bergmanDensity μ v σ y) ∧ ∀ σ y (M : ℝ), 0 ≤ M → (∀ c : ι → ℂ, cmb v c σ y ≤ M * l2 μ v c) → bergmanDensity μ v σ y ≤ M := by
  first | exact @GlobalTheory.HSAmp.berg_mass_extremal | exact GlobalTheory.HSAmp.berg_mass_extremal | (intros; apply GlobalTheory.HSAmp.berg_mass_extremal <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.dvrPlace_centre_on_base_of_etaleTowerOverNormalLocal : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (P : Place cL),
  IsEtTower cK R cL T ι ψ τ → P.IsPrimeOf T →
  (∀ g : R, g ≠ 0 → P.ord (ι g : L) = 0) ∨
  ∃ P0 : Place cK, P0.IsPrimeOf R ∧ ∀ g : R, g ≠ 0 → (P0.ord (g : K) = 0 ↔ P.ord (ι g : L) = 0) := by
  first | exact @GlobalTheory.FieldPair.centre_of_isEtTower | exact GlobalTheory.FieldPair.centre_of_isEtTower | (intros; apply GlobalTheory.FieldPair.centre_of_isEtTower <;> assumption)
end
