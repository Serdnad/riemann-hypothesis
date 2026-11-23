module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle002
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Topology.Instances.Matrix
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MulVecEqZeroOfPair
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NilpotentDerivationRank
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle005
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericLuDecompositionUnique
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle008
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle007
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Chart

theorem one_left_spMap {S : Scheme.{0}} (G : Over S) [GrpObj G] {R A : Type} [CommRing R] [CommRing A]
    (x : Sp R ⟶ S) (g : R →+* A) :
    (1 : Over.mk (spMap g ≫ x) ⟶ G).left = spMap g ≫ (1 : Over.mk x ⟶ G).left := by
  let k : Over.mk (spMap g ≫ x) ⟶ Over.mk x := Over.homMk (spMap g) rfl
  have h : (1 : Over.mk (spMap g ≫ x) ⟶ G) = k ≫ (1 : Over.mk x ⟶ G) := by
    rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (k ≫ toUnit _) (toUnit _)]
  rw [h]; rfl

theorem exists_chart_at_point (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R : Type) [CommRing R]
    (x : Sp R ⟶ S) (p : Ideal R) [p.IsPrime] :
    ∃ f : R, f ∉ p ∧ ∃ (U : G.left.Opens) (V : S.Opens) (hU : IsAffineOpen U) (_ : IsAffineOpen V)
      (hUV : U ≤ G.hom ⁻¹ᵁ V),
      RingHom.Smooth (G.hom.appLE V U hUV).hom ∧
      ∃ u : Γ(G.left, U) →+* Localization.Away f,
        (1 : Over.mk (spMap (algebraMap R (Localization.Away f)) ≫ x) ⟶ G).left = spMap u ≫ hU.fromSpec := by
  let t : Sp R ⟶ G.left := (1 : Over.mk x ⟶ G).left
  let q : PrimeSpectrum R := ⟨p, inferInstance⟩
  let q' : Sp R := q
  obtain ⟨V, hV, hqV, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := G.hom (t q')) trivial
  obtain ⟨U, hU, hqU, hUV⟩ := exists_isAffineOpen_mem_and_subset (X := G.left) (U := G.hom ⁻¹ᵁ V) (x := t q') hqV
  have hUV' : U ≤ G.hom ⁻¹ᵁ V := hUV
  have hopen : IsOpen {y : PrimeSpectrum R | t (show Sp R from y) ∈ U} := (t ⁻¹ᵁ U).isOpen
  obtain ⟨_, ⟨f, rfl⟩, hqf, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (show q ∈ _ from hqU) hopen
  refine ⟨f, hqf, U, V, hU, hV, hUV', HasRingHomProperty.appLE @Smooth G.hom inferInstance ⟨V, hV⟩ ⟨U, hU⟩ hUV', ?_⟩
  let a : Sp (Localization.Away f) ⟶ Sp R := spMap (algebraMap R (Localization.Away f))
  have hrange : Set.range (a ≫ t) ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    apply hsub
    have : (PrimeSpectrum.comap (algebraMap R (Localization.Away f))) y ∈
        Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away f))) := ⟨y, rfl⟩
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f] at this
    exact this
  let l := IsOpenImmersion.lift hU.fromSpec (a ≫ t) hrange
  refine ⟨(Spec.preimage l).hom, ?_⟩
  have hl : spMap (Spec.preimage l).hom = l := by
    simp [spMap]
  rw [one_left_spMap, hl]
  exact (IsOpenImmersion.lift_fac _ _ _).symm

end GlobalTheory.CompanionTheory.Ar.Chart
end

section

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.CompanionTheory.Ggeo

theorem germ_vanish_of_generic_dominated : ∀ (X : Scheme.{0}) [IsReduced X] (Ω O : Type) [Field Ω] [CommRing O] (ξ : Spec (CommRingCat.of Ω) ⟶ X), (∀ q : X, ξ (IsLocalRing.closedPoint Ω) ⤳ q) → ∀ (s₀ : X ⟶ Spec (CommRingCat.of O)) (gm : O →+* Ω), ξ ≫ s₀ = Spec.map (CommRingCat.ofHom gm) → ∀ (x : X) (a : O), gm a = 0 → (Spec.preimage (X.fromSpecStalk x ≫ s₀)).hom a = 0 :=
  PositivityTheory.UnitarySelfGeneration.germ_vanishes_of_generic_vanishing

end GlobalTheory.CompanionTheory.Ggeo
end

section

open Filter Topology Matrix

namespace GlobalTheory.CompanionTheory.PeriodLimitSeq

open GlobalTheory.CompanionTheory.PeriodLimit

theorem int_seq_const (a : ℕ → ℤ) (L : ℂ) (h : Tendsto (fun m => (a m : ℂ)) atTop (𝓝 L)) :
    ∃ N : ℤ, L = N ∧ ∀ᶠ m in atTop, a m = N := by
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 h (1 / 2) (by norm_num)
  have key : ∀ m ≥ M, a m = a M := by
    intro m hm
    have h2 : dist (a m : ℂ) (a M : ℂ) < 1 := by
      calc dist (a m : ℂ) (a M : ℂ) ≤ dist (a m : ℂ) L + dist (a M : ℂ) L :=
            dist_triangle_right _ _ _
        _ < 1 / 2 + 1 / 2 := add_lt_add (hM m hm) (hM M le_rfl)
        _ = 1 := by norm_num
    rw [Complex.dist_eq, ← Int.cast_sub, Complex.norm_intCast, ← Int.cast_abs] at h2
    have h3 : |a m - a M| < 1 := by exact_mod_cast h2
    exact sub_eq_zero.1 (Int.abs_lt_one_iff.1 h3)
  have hev : ∀ᶠ m in atTop, a m = a M := eventually_atTop.2 ⟨M, key⟩
  refine ⟨a M, ?_, hev⟩
  exact tendsto_nhds_unique h (tendsto_const_nhds.congr' (hev.mono fun m hm => by simp [hm]))

theorem mulVec_expand {g : ℕ} (Bs : Matrix (Fin g) (Fin g) ℤ) (A : Matrix (Fin g) (Fin g) ℂ)
    (t : ℂ) (v : Fin g → ℤ) (k : Fin g) :
    ((A + t • Bs.map (fun x : ℤ => (x : ℂ))) *ᵥ (fun k => (v k : ℂ))) k
      = (A *ᵥ (fun k => (v k : ℂ))) k + t * (((Bs *ᵥ v) k : ℤ) : ℂ) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
    smul_eq_mul, add_mul, Finset.sum_add_distrib]
  push_cast
  rw [Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

private theorem im_mulVec_lemma {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (v : Fin g → ℤ) (k : Fin g) :
    ((M *ᵥ (fun k => (v k : ℂ))) k).im = ((M.map Complex.im) *ᵥ (fun k => (v k : ℝ))) k := by
  simp [Matrix.mulVec, dotProduct, Complex.im_sum, Complex.mul_im]

theorem freq_ker {g : ℕ} (Bs : Matrix (Fin g) (Fin g) ℤ) (σ : Matrix (Fin g) (Fin g) ℂ)
    (σs τs : ℕ → Matrix (Fin g) (Fin g) ℂ) (t : ℕ → ℂ) (us vs : ℕ → Fin g → ℤ) (y : Fin g → ℂ)
    (hσ : Tendsto σs atTop (𝓝 σ)) (ht : Tendsto (fun m => (t m).im) atTop atTop)
    (hτ : ∀ m, τs m = σs m + t m • Bs.map (fun x : ℤ => (x : ℂ)))
    (hy : Tendsto (fun m => (fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ))) atTop (𝓝 y))
    (v : Fin g → ℤ) (hv : ∃ᶠ m in atTop, vs m = v) :
    Bs *ᵥ v = 0 ∧ ∀ k, (y k).im = ((σ.map Complex.im) *ᵥ (fun k => (v k : ℝ))) k := by
  have hyk : ∀ k, Tendsto (fun m => ((fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ))) k)
      atTop (𝓝 (y k)) := fun k => tendsto_pi_nhds.1 hy k
  have hσk : ∀ k, Tendsto (fun m => (σs m *ᵥ (fun k => (v k : ℂ))) k) atTop
      (𝓝 ((σ *ᵥ (fun k => (v k : ℂ))) k)) := by
    intro k
    have hc : Continuous (fun M : Matrix (Fin g) (Fin g) ℂ => (M *ᵥ (fun k => (v k : ℂ))) k) :=
      (continuous_apply k).comp (continuous_id.matrix_mulVec continuous_const)
    exact (hc.tendsto σ).comp hσ
  have htpos : ∀ᶠ m in atTop, 0 < (t m).im := ht.eventually_gt_atTop 0
  have hid : ∀ m, vs m = v → ∀ k,
      (((fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ))) k).im
        = ((σs m *ᵥ (fun k => (v k : ℂ))) k).im + (t m).im * (((Bs *ᵥ v) k : ℤ) : ℝ) := by
    intro m hm k
    rw [Pi.add_apply, hm, hτ m, mulVec_expand]
    simp [Complex.mul_im]
  have hker : Bs *ᵥ v = 0 := by
    funext k
    have hf : Tendsto (fun m => ((((fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ))) k).im
        - ((σs m *ᵥ (fun k => (v k : ℂ))) k).im) / (t m).im) atTop (𝓝 0) :=
      (((Complex.continuous_im.tendsto _).comp (hyk k)).sub
        ((Complex.continuous_im.tendsto _).comp (hσk k))).div_atTop ht
    have hfreq : ∃ᶠ m in atTop, ((((fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ))) k).im
        - ((σs m *ᵥ (fun k => (v k : ℂ))) k).im) / (t m).im = (((Bs *ᵥ v) k : ℤ) : ℝ) := by
      refine (hv.and_eventually htpos).mono fun m hm => ?_
      rw [hid m hm.1 k, add_sub_cancel_left]
      exact mul_div_cancel_left₀ _ hm.2.ne'
    have h0 := tendsto_nhds_unique_of_frequently_eq hf tendsto_const_nhds hfreq
    show (Bs *ᵥ v) k = 0
    exact_mod_cast h0.symm
  refine ⟨hker, fun k => ?_⟩
  rw [← im_mulVec_lemma σ v k]
  have hfreq2 : ∃ᶠ m in atTop,
      (((fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ))) k).im
        = ((σs m *ᵥ (fun k => (v k : ℂ))) k).im := by
    refine hv.mono fun m hm => ?_
    rw [hid m hm k, hker]
    simp
  exact tendsto_nhds_unique_of_frequently_eq ((Complex.continuous_im.tendsto _).comp (hyk k))
    ((Complex.continuous_im.tendsto _).comp (hσk k)) hfreq2

private theorem cast_mulVec_lemma_2 {g : ℕ} (Bs : Matrix (Fin g) (Fin g) ℤ) (v : Fin g → ℤ) :
    Bs.map (fun x : ℤ => (x : ℝ)) *ᵥ (fun k => (v k : ℝ)) = fun k => (((Bs *ᵥ v) k : ℤ) : ℝ) := by
  funext k
  simp [Matrix.mulVec, dotProduct]

theorem unique_value {g : ℕ} (Bs : Matrix (Fin g) (Fin g) ℤ) (σ : Matrix (Fin g) (Fin g) ℂ)
    (c : ℝ) (hc : 0 < c) (y : Fin g → ℂ)
    (hpos : ∀ v : Fin g → ℝ, Bs.map (fun x : ℤ => (x : ℝ)) *ᵥ v = 0 →
      c * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((σ.map Complex.im) *ᵥ v))
    (v v' : Fin g → ℤ) (hk : Bs *ᵥ v = 0) (hk' : Bs *ᵥ v' = 0)
    (hi : ∀ k, (y k).im = ((σ.map Complex.im) *ᵥ (fun k => (v k : ℝ))) k)
    (hi' : ∀ k, (y k).im = ((σ.map Complex.im) *ᵥ (fun k => (v' k : ℝ))) k) : v = v' := by
  obtain ⟨w, hw⟩ : ∃ w : Fin g → ℝ, w = (fun k => (v k : ℝ)) - (fun k => (v' k : ℝ)) := ⟨_, rfl⟩
  have hBw : Bs.map (fun x : ℤ => (x : ℝ)) *ᵥ w = 0 := by
    rw [hw, Matrix.mulVec_sub, cast_mulVec_lemma_2, cast_mulVec_lemma_2, hk, hk']
    funext k
    simp
  have hSw : (σ.map Complex.im) *ᵥ w = 0 := by
    funext k
    have e1 := hi k
    have e2 := hi' k
    rw [hw, Matrix.mulVec_sub, Pi.sub_apply, Pi.zero_apply, ← e1, ← e2, sub_self]
  have h1 := hpos w hBw
  rw [hSw, dotProduct_zero] at h1
  have h3 : 0 ≤ w ⬝ᵥ w := Finset.sum_nonneg fun i _ => mul_self_nonneg (w i)
  have h5 : w ⬝ᵥ w ≤ 0 := by
    by_contra hne
    have := mul_pos hc (not_le.1 hne)
    linarith
  have h4 : w = 0 := dotProduct_self_eq_zero.1 (le_antisymm h5 h3)
  funext k
  have h6 := congrFun h4 k
  rw [hw] at h6
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at h6
  exact_mod_cast h6

theorem limit_seq : ∀ (g : ℕ) (Bs : Matrix (Fin g) (Fin g) ℤ) (σ : Matrix (Fin g) (Fin g) ℂ) (σs τs : ℕ → Matrix (Fin g) (Fin g) ℂ) (t : ℕ → ℂ) (c : ℝ) (us vs : ℕ → Fin g → ℤ) (y : Fin g → ℂ), 0 < c → Tendsto σs atTop (𝓝 σ) → Tendsto (fun m => (t m).im) atTop atTop → (∀ m, τs m = σs m + t m • Bs.map (fun x : ℤ => (x : ℂ))) → (∀ m, ((τs m).map Complex.im - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef) → (∀ v : Fin g → ℝ, Bs.map (fun x : ℤ => (x : ℝ)) *ᵥ v = 0 → c * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((σ.map Complex.im) *ᵥ v)) → Tendsto (fun m => (fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ))) atTop (𝓝 y) → ∃ u v : Fin g → ℤ, Bs *ᵥ v = 0 ∧ y = (fun k => (u k : ℂ)) + σ *ᵥ (fun k => (v k : ℂ)) ∧ ∀ᶠ m in atTop, us m = u ∧ vs m = v := by
  intro g Bs σ σs τs t c us vs y hc hσ ht hτ hpsd hposσ hy
  have huniq : ∀ w w' : Fin g → ℤ, (∃ᶠ m in atTop, vs m = w) → (∃ᶠ m in atTop, vs m = w') →
      w = w' := by
    intro w w' hw hw'
    obtain ⟨hk, hi⟩ := freq_ker Bs σ σs τs t us vs y hσ ht hτ hy w hw
    obtain ⟨hk', hi'⟩ := freq_ker Bs σ σs τs t us vs y hσ ht hτ hy w' hw'
    exact unique_value Bs σ c hc y hposσ w w' hk hk' hi hi'
  have hS : Tendsto (fun m => ∑ k, ((((fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ)) :
      Fin g → ℂ)) k).im ^ 2) atTop (𝓝 (∑ k, (y k).im ^ 2)) := by
    refine tendsto_finsetSum _ fun k _ => ?_
    exact ((Complex.continuous_im.tendsto _).comp (tendsto_pi_nhds.1 hy k)).pow 2
  have hbd : ∀ᶠ m in atTop,
      vs m ∈ {w : Fin g → ℤ | ∑ k, (w k : ℝ) ^ 2 ≤ (∑ k, (y k).im ^ 2 + 1) / c ^ 2} := by
    filter_upwards [hS.eventually_lt_const (lt_add_one _)] with m hm
    have h1 := sq_mul_sum_sq_le ((τs m).map Complex.im) hc (hpsd m) (fun k => (vs m k : ℝ))
    simp only [im_period (τs m) (us m) (vs m)] at h1
    show ∑ k, (vs m k : ℝ) ^ 2 ≤ (∑ k, (y k).im ^ 2 + 1) / c ^ 2
    rw [le_div_iff₀ (pow_pos hc 2)]
    linarith
  have hfin := finite_sum_sq_le (g := g) ((∑ k, (y k).im ^ 2 + 1) / c ^ 2)
  have hall : ∀ᶠ m in atTop, ∀ w ∈ {w ∈ {w : Fin g → ℤ | ∑ k, (w k : ℝ) ^ 2 ≤
      (∑ k, (y k).im ^ 2 + 1) / c ^ 2} | ¬ ∃ᶠ n in atTop, vs n = w}, vs m ≠ w := by
    rw [Filter.eventually_all_finite (hfin.subset (Set.sep_subset _ _))]
    intro w hw
    exact Filter.not_frequently.1 hw.2
  have hev : ∀ᶠ m in atTop, ∃ᶠ n in atTop, vs n = vs m := by
    filter_upwards [hbd, hall] with m hm1 hm2
    by_contra hne
    exact hm2 (vs m) ⟨hm1, hne⟩ rfl
  obtain ⟨m0, hm0⟩ := hev.exists
  have hv_ev : ∀ᶠ m in atTop, vs m = vs m0 := by
    filter_upwards [hev] with m hm
    exact huniq _ _ hm hm0
  obtain ⟨hker, -⟩ := freq_ker Bs σ σs τs t us vs y hσ ht hτ hy (vs m0) hv_ev.frequently
  have hσk : ∀ k, Tendsto (fun m => (σs m *ᵥ (fun k => (vs m0 k : ℂ))) k) atTop
      (𝓝 ((σ *ᵥ (fun k => (vs m0 k : ℂ))) k)) := by
    intro k
    have hc' : Continuous (fun M : Matrix (Fin g) (Fin g) ℂ => (M *ᵥ (fun k => (vs m0 k : ℂ))) k) :=
      (continuous_apply k).comp (continuous_id.matrix_mulVec continuous_const)
    exact (hc'.tendsto σ).comp hσ
  have hu : ∀ k, Tendsto (fun m => (us m k : ℂ)) atTop
      (𝓝 (y k - (σ *ᵥ (fun k => (vs m0 k : ℂ))) k)) := by
    intro k
    have h1 : Tendsto (fun m => ((fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ))) k
        - (σs m *ᵥ (fun k => (vs m0 k : ℂ))) k) atTop
        (𝓝 (y k - (σ *ᵥ (fun k => (vs m0 k : ℂ))) k)) :=
      (tendsto_pi_nhds.1 hy k).sub (hσk k)
    refine h1.congr' ?_
    filter_upwards [hv_ev] with m hm
    rw [Pi.add_apply, hm, hτ m, mulVec_expand, hker]
    simp
  choose u hu1 hu2 using fun k => int_seq_const (fun m => us m k) _ (hu k)
  refine ⟨u, vs m0, hker, ?_, ?_⟩
  · funext k
    simp only [Pi.add_apply]
    rw [← hu1 k]
    ring
  · have hall2 : ∀ᶠ m in atTop, ∀ k, us m k = u k := Filter.eventually_all.2 hu2
    filter_upwards [hall2, hv_ev] with m h1 h2
    exact ⟨funext h1, h2⟩

end GlobalTheory.CompanionTheory.PeriodLimitSeq
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.nilpotent_derivation_rank : ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (R : Type) [CommRing R] [Algebra k R] [Module.Finite k R] (D : Derivation k R R) (ε : R →ₐ[k] k),
    (∀ a : R, (⇑D)^[p] a = 0) → ∀ t : R, IsUnit ((⇑D)^[p - 1] t) →
      Module.finrank k R = p * Module.finrank k (LinearMap.ker (D : R →ₗ[k] R)) ∧
      ∃ z : R, ε (D z) ≠ 0 ∧ ∀ u : R →ₗ[k] k, (∀ a b : R, u (a * b) = u a * ε b + ε a * u b) →
        (∀ a : R, D a = 0 → u a = 0) → u z = 0 → u = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.DerivFree.finrank_and_vanishing | exact GlobalTheory.CompanionTheory.Ggeo.DerivFree.finrank_and_vanishing | (intros; apply GlobalTheory.CompanionTheory.Ggeo.DerivFree.finrank_and_vanishing <;> assumption)
end

section


theorem _root_.GlobalTheory.T.iota_multi_change_of_basis_det : ∀ (Ω V : Type) [Field Ω] [AddCommGroup V] [Module Ω V] (n : ℕ) (e : Fin n → V) (P : Matrix (Fin n) (Fin n) Ω), exteriorPower.ιMulti Ω n (fun i => ∑ j, P i j • e j) = P.det • exteriorPower.ιMulti Ω n e := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Lat.wedge_matrix_mul_family | exact GlobalTheory.CompanionTheory.Ar.Lat.wedge_matrix_mul_family | (intros; apply GlobalTheory.CompanionTheory.Ar.Lat.wedge_matrix_mul_family <;> assumption)
end

section


theorem _root_.GlobalTheory.T.iota_multi_ne_zero_of_lin_indep : ∀ (Ω V : Type) [Field Ω] [AddCommGroup V] [Module Ω V] (n : ℕ) (e : Fin n → V), LinearIndependent Ω e → exteriorPower.ιMulti Ω n e ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Exterior.ιMulti_ne_zero_of_linearIndependent | exact GlobalTheory.CompanionTheory.Exterior.ιMulti_ne_zero_of_linearIndependent | (intros; apply GlobalTheory.CompanionTheory.Exterior.ιMulti_ne_zero_of_linearIndependent <;> assumption)
end

section


theorem _root_.GlobalTheory.T.mem_span_of_iota_multi_proportional : ∀ (Ω V : Type) [Field Ω] [AddCommGroup V] [Module Ω V] (n : ℕ) (b e : Fin n → V) (t : Ω), LinearIndependent Ω e → t ≠ 0 → exteriorPower.ιMulti Ω n b = t • exteriorPower.ιMulti Ω n e → ∀ i, b i ∈ Submodule.span Ω (Set.range e) := by
  first | exact @GlobalTheory.CompanionTheory.WedgeSpan.span_of_wedge_proportional | exact GlobalTheory.CompanionTheory.WedgeSpan.span_of_wedge_proportional | (intros; apply GlobalTheory.CompanionTheory.WedgeSpan.span_of_wedge_proportional <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_lu_decomposition_mul_generic_unipotent : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (n : ℕ) (A : Matrix (Fin n) (Fin n) K) (u : Matrix (Fin n) (Fin n) L), A.det ≠ 0 → (∀ k, u k k = 1) → (∀ l k, l < k → u l k = 0) → AlgebraicIndependent K (fun q : {lk : Fin n × Fin n // lk.2 < lk.1} => u q.1.1 q.1.2) → ∃ v w : Matrix (Fin n) (Fin n) L, A.map (algebraMap K L) * u = v * w ∧ (∀ k, v k k = 1) ∧ (∀ l k, l < k → v l k = 0) ∧ (∀ l k, k < l → w l k = 0) ∧ ∀ k, w k k ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.GenericLU.generic_lu | exact GlobalTheory.CompanionTheory.GenericLU.generic_lu | (intros; apply GlobalTheory.CompanionTheory.GenericLU.generic_lu <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory

theorem _root_.GlobalTheory.T.local_hom_char_zero_units : ∀ (O F L K : Type) [CommRing O] [Field F] [NumberField F] [CommRing L] [Field K] [CharZero K] (β : O →+* F) (θ : O →+* L) (ρ : L →+* K), IsLocalHom ρ → (∀ a, β a = 0 → θ a = 0) → ∀ b, β b ≠ 0 → IsUnit (θ b) := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.unit_of_local_hom_charZero_nf | exact GlobalTheory.CompanionTheory.Ggeo.unit_of_local_hom_charZero_nf | (intros; apply GlobalTheory.CompanionTheory.Ggeo.unit_of_local_hom_charZero_nf <;> assumption)
end

section


theorem _root_.GlobalTheory.T.number_field_maps_local_ring_unique : ∀ (K : Type) [Field K] [NumberField K] (B : Type) [CommRing B] [IsLocalRing B] (Ω : Type) [Field Ω] (π : B →+* Ω) (s t : K →+* B), π.comp s = π.comp t → s = t := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.TwoMaps.ringHom_eq_of_comp_eq | exact GlobalTheory.CompanionTheory.Ggeo.TwoMaps.ringHom_eq_of_comp_eq | (intros; apply GlobalTheory.CompanionTheory.Ggeo.TwoMaps.ringHom_eq_of_comp_eq <;> assumption)
end

section

open NumberField

theorem _root_.GlobalTheory.T.eigen_projector_field_embedding : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K] (σ : 𝓞 E →+* K), ∃ (n : ℕ) (e : Fin n → 𝓞 E) (c : Fin n → K), ∑ k, c k * σ (e k) = 1 ∧ ∀ (L W : Type) [Field L] [AddCommGroup W] [Module L W] (j : K →+* L) (ρ : 𝓞 E →+* Module.End L W) (a : 𝓞 E) (w : W), ρ a (∑ k, j (c k) • ρ (e k) w) = j (σ a) • ∑ k, j (c k) • ρ (e k) w := by
  first | exact @GlobalTheory.CompanionTheory.TraceProj.exists_eigen_projector | exact GlobalTheory.CompanionTheory.TraceProj.exists_eigen_projector | (intros; apply GlobalTheory.CompanionTheory.TraceProj.exists_eigen_projector <;> assumption)
end

section

open NumberField


theorem _root_.GlobalTheory.T.exists_section_not_in_set : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDedekindDomain R] (M : Type) [AddCommGroup M] [Module R M], (∀ (a : R) (m : M), a ≠ 0 → a • m = 0 → m = 0) → ∀ t : M, t ≠ 0 → ∀ d₀ : R, d₀ ≠ 0 → (∀ (x d : R) (u : M), d ≠ 0 → d • u = x • t → d ∣ d₀ * x) → ∀ (V : Set M) (P : Ideal R), P.IsMaximal → P ≠ ⊥ → (∀ u ∈ V, ∀ c e : R, e ≠ 0 → (∀ π ∈ P, e ∣ c * π) → ∃ u' : M, e • u' = c • u) → ∃ (x : R) (u : M), d₀ • u = x • t ∧ u ∉ V := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.KeydegPrimes.exists_multiple_not_mem | exact GlobalTheory.CompanionTheory.Ggeo.KeydegPrimes.exists_multiple_not_mem | (intros; apply GlobalTheory.CompanionTheory.Ggeo.KeydegPrimes.exists_multiple_not_mem <;> assumption)
end
