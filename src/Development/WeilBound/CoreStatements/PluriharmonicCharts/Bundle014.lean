module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HolDifferentiableAt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle052
public import Development.WeilBound.CoreStatements.VolumeEquality.CoverRootsSch
public import Mathlib.Algebra.MvPolynomial.Cardinal
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle002
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle018
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle065
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle118
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
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
public import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle010
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle002
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle021

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open scoped Matrix ComplexOrder

noncomputable section

namespace PositivityTheory.Xgp.c_bm_exists_period

theorem exists_embedding (K k : Type) [Field K] [Field k] [Countable K] [Countable k] (β : K →+* k) (s : K →+* ℂ) :
    ∃ j : k →+* ℂ, j.comp β = s := by
  letI := β.toAlgebra
  letI := s.toAlgebra
  obtain ⟨I₁, x, hx⟩ := exists_isTranscendenceBasis' K k
  obtain ⟨κ, z, hz⟩ := exists_isTranscendenceBasis' K ℂ
  have hI₁ : Countable I₁ := hx.1.injective.countable
  have hκ : Cardinal.mk ℂ = Cardinal.mk κ := by
    have := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' z hz
      (Cardinal.mk_le_aleph0_iff.2 inferInstance) (by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum)
    exact this
  have hle : Cardinal.mk I₁ ≤ Cardinal.mk κ := by
    rw [← hκ, Cardinal.mk_complex]
    exact (Cardinal.mk_le_aleph0_iff.2 hI₁).trans Cardinal.aleph0_le_continuum
  obtain ⟨e⟩ := hle
  have hz' : AlgebraicIndependent K (z ∘ e) := hz.1.comp e e.injective
  letI : Algebra (MvPolynomial I₁ K) k := (MvPolynomial.aeval x : MvPolynomial I₁ K →ₐ[K] k).toRingHom.toAlgebra
  letI : Algebra (MvPolynomial I₁ K) ℂ := (MvPolynomial.aeval (z ∘ e) : MvPolynomial I₁ K →ₐ[K] ℂ).toRingHom.toAlgebra
  haveI : FaithfulSMul (MvPolynomial I₁ K) k := (faithfulSMul_iff_algebraMap_injective _ _).2 hx.1
  haveI : FaithfulSMul (MvPolynomial I₁ K) ℂ := (faithfulSMul_iff_algebraMap_injective _ _).2 hz'
  haveI : Algebra.IsAlgebraic (MvPolynomial I₁ K) k := by
    haveI := hx.isAlgebraic
    exact Algebra.IsAlgebraic.of_ringHom_of_comp_eq (S := Algebra.adjoin K (Set.range x)) (B := k) hx.1.aevalEquiv
      (RingHom.id k) hx.1.aevalEquiv.surjective Function.injective_id
      (RingHom.ext fun p => hx.1.algebraMap_aevalEquiv p)
  let j : k →ₐ[MvPolynomial I₁ K] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨j.toRingHom, RingHom.ext fun a => ?_⟩
  have h := j.commutes (MvPolynomial.C a)
  have h1 : algebraMap (MvPolynomial I₁ K) k (MvPolynomial.C a) = β a := MvPolynomial.aeval_C x a
  have h2 : algebraMap (MvPolynomial I₁ K) ℂ (MvPolynomial.C a) = s a := MvPolynomial.aeval_C (z ∘ e) a
  rw [h1, h2] at h
  exact h

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

theorem genMap_bij (hξ : IsCptGen ξ) (q : X) (hq : q = genPt ξ) (h : genPt ξ ⤳ q) :
    Function.Bijective (genMap ξ ⟨q, h⟩) := by
  subst hq
  have : X.presheaf.stalkSpecializes h = 𝟙 _ := TopCat.Presheaf.stalkSpecializes_refl _ _
  refine ⟨hξ.inj _, ?_⟩
  unfold genMap
  simp only [this]
  exact hξ.bij.2

theorem countable_of_tie {κ : Type} [Finite κ] {x : κ → Ω} (h : CoordTie ℤ ξ x) : Countable Ω := by
  obtain ⟨c, hc⟩ := h.cover ⟨genPt ξ, specializes_rfl⟩
  haveI : Countable (MvPolynomial κ ℤ) := by
    rw [← Cardinal.mk_le_aleph0_iff]
    exact MvPolynomial.cardinalMk_le_max.trans (max_le (max_le Cardinal.mk_le_aleph0 Cardinal.mk_le_aleph0) le_rfl)
  refine Function.Surjective.countable (f := fun a : MvPolynomial κ ℤ × MvPolynomial κ ℤ =>
    MvPolynomial.aeval (fun j => x j / x c) a.1 / MvPolynomial.aeval (fun j => x j / x c) a.2) fun a => ?_
  obtain ⟨s, hs, hu, hsa⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ κ x h c _ hc a).1 ((genMap_bij h.gen _ rfl _).2 a)
  rw [Algebra.adjoin_range_eq_range_aeval] at hs hsa
  obtain ⟨f, hf⟩ := hs
  obtain ⟨g, hg⟩ := hsa
  refine ⟨(g, f), ?_⟩
  have hf' : MvPolynomial.aeval (fun j => x j / x c) f = s := hf
  have hg' : MvPolynomial.aeval (fun j => x j / x c) g = s * a := hg
  simp only [hf', hg']
  exact mul_div_cancel_left₀ _ hu.1

theorem cancel_gen (hξ : IsCptGen ξ) {R : Type} [CommRing R] {a b : Ω →+* R} (h : spMap a ≫ ξ = spMap b ≫ ξ) :
    a = b := by
  have e := LieTangent.spec_genMap ξ ⟨genPt ξ, specializes_rfl⟩
  have h' : (spMap a ≫ Spec.map (CommRingCat.ofHom (genMap ξ ⟨genPt ξ, specializes_rfl⟩))) ≫ X.fromSpecStalk _ =
      (spMap b ≫ Spec.map (CommRingCat.ofHom (genMap ξ ⟨genPt ξ, specializes_rfl⟩))) ≫ X.fromSpecStalk _ := by
    rw [Category.assoc, Category.assoc, e, h]
  rw [cancel_mono, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp] at h'
  have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h')
  refine RingHom.ext fun t => ?_
  obtain ⟨s, rfl⟩ := (genMap_bij hξ _ rfl specializes_rfl).2 t
  exact DFunLike.congr_fun h2 s

theorem factor_gen (hξ : IsCptGen ξ) {R : Type} [CommRing R] [IsLocalRing R] (V : Sp R ⟶ X)
    (hV : centre V = genPt ξ) : ∃ δ : Ω →+* R, spMap δ ≫ ξ = V := by
  have h : genPt ξ ⤳ centre V := hV ▸ specializes_rfl
  let e := RingEquiv.ofBijective _ (genMap_bij hξ _ hV h)
  refine ⟨(Scheme.stalkClosedPointTo V).hom.comp e.symm.toRingHom, ?_⟩
  have e1 := LieTangent.spec_genMap ξ ⟨centre V, h⟩
  have e2 := LieTangent.spec_centre V
  refine (congrArg (spMap _ ≫ ·) e1.symm).trans (Eq.trans ?_ e2)
  rw [← Category.assoc, spMap, ← Spec.map_comp]
  congr 2
  ext s
  exact congrArg (Scheme.stalkClosedPointTo V).hom (e.symm_apply_apply s)

theorem hom_dual_ext {F₀ F : Type} [Field F₀] [Field F] [CharZero F] (i : F₀ →+* F)
    (hfin : 0 < (letI := i.toAlgebra; Module.finrank F₀ F)) {δ δ' : F →+* DualNumber ℂ} (h : δ.comp i = δ'.comp i)
    (h' : ∀ x, (δ x).fst = (δ' x).fst) : δ = δ' := by
  letI := i.toAlgebra
  letI := (δ.comp i).toAlgebra
  haveI : CharZero F₀ := i.charZero
  haveI : Module.Finite F₀ F := Module.finite_of_finrank_pos hfin
  have hu : Algebra.FormallyUnramified F₀ F := Algebra.FormallyUnramified.of_isSeparable F₀ F
  have h := Algebra.FormallyUnramified.ext' (R := F₀) (A := F) (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom
    ⟨2, by
      rw [Submodule.zero_eq_bot, eq_bot_iff, sq, Ideal.mul_le]
      intro a ha b hb
      have ha' : a.fst = 0 := ha
      have hb' : b.fst = 0 := hb
      rw [Ideal.mem_bot]
      ext <;> simp [ha', hb']⟩
    { δ with commutes' := fun _ => rfl } { δ' with commutes' := fun r => (DFunLike.congr_fun h r).symm } h'
  exact RingHom.ext fun x => DFunLike.congr_fun h x

theorem const_of_finite {Y : Scheme.{0}} {Ω₀ : Type} [Field Ω₀] [CharZero Ω] {ξ₀ : Sp Ω₀ ⟶ Y} (hξ : IsCptGen ξ)
    (hξ₀ : IsCptGen ξ₀) {f : X ⟶ Y} {i : Ω₀ →+* Ω} (hf : ξ ≫ f = spMap i ≫ ξ₀)
    (hfin : 0 < (letI := i.toAlgebra; Module.finrank Ω₀ Ω)) {φ : Ω →+* ℂ} {V : Sp (DualNumber ℂ) ⟶ X}
    (h1 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ V = spMap φ ≫ ξ)
    (h2 : V ≫ f = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ (spMap φ ≫ ξ) ≫ f) :
    V = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap φ ≫ ξ := by
  have hc : centre V = genPt ξ := by
    have a1 : centre (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ V) = centre V := by
      exact congrArg V (Spec_closedPoint (f := CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom))
    rw [← a1, h1]
    exact SheetDecomposition.CovSch.centre_spMap φ ξ
  obtain ⟨δ, rfl⟩ := factor_gen hξ V hc
  have sc : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C),
      spMap (g.comp f) = spMap g ≫ spMap f := fun f g => Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)
  have e1 : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp δ = φ := cancel_gen hξ (by rw [sc, Category.assoc, h1])
  have e2 : δ.comp i = ((algebraMap ℂ (DualNumber ℂ)).comp φ).comp i := cancel_gen hξ₀ (by
    rw [sc, sc _ ((algebraMap ℂ (DualNumber ℂ)).comp φ), sc φ, Category.assoc, Category.assoc, Category.assoc, ← hf]
    simpa only [Category.assoc] using h2)
  rw [hom_dual_ext i hfin e2 fun x => by
    simpa [TrivSqZeroExt.algebraMap_eq_inl] using DFunLike.congr_fun e1 x, sc, Category.assoc]

theorem fderiv_value_zero (hξ : IsCptGen ξ) (hall : ∀ q : X, genPt ξ ⤳ q) {n : ℕ} {B : Set (Fin n → ℂ)}
    {p : (Fin n → ℂ) → (Sp ℂ ⟶ X)} (hp : IsHolTo B p) (h0 : 0 ∈ B) (hc : centre (p 0) = centre ξ) {v : Fin n → ℂ}
    (hv : IsDerivAt0 p v (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ p 0)) {a : Ω} {r : (Fin n → ℂ) → ℂ}
    (hr : ∀ᶠ u in nhds 0, ValAt ξ (p u) a (r u)) : fderiv ℂ r 0 v = 0 := by
  obtain ⟨g, rfl⟩ := hξ.bij.2 a
  obtain ⟨U, hU, s, rfl⟩ := X.presheaf.exists_germ_eq g
  have hU0 : ⊤ ≤ p 0 ⁻¹ᵁ U := (SheetDecomposition.CovSch.top_le_iff _ _).2 (hc ▸ hU)
  have he : r =ᶠ[nhds 0] fun u => valAt' (p u) U s := by
    filter_upwards [hr, GlobalTheory.LocalLift.hol_eventually_mem hp h0 hU0] with u h1 h2
    have h3 := (SheetDecomposition.CovSch.top_le_iff _ _).1 h2.2
    rw [SheetDecomposition.CovSch.valAt'_eq _ _ h3]
    exact SheetDecomposition.CovSch.v_unique hξ h1 (SheetDecomposition.CovSch.valAt_sec (hall _) U h3 hU s)
  have h1 : ⊤ ≤ (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ p 0) ⁻¹ᵁ U := fun q _ => hU0 (Set.mem_univ _)
  rw [he.fderiv_eq, ← hv.2 U h1 s]
  have := GlobalTheory.TangentOrigin.evalPt_spMap_comp (algebraMap ℂ (DualNumber ℂ)) (p 0) U hU0 h1 s
  refine (congrArg TrivSqZeroExt.snd this).trans ?_
  simp [TrivSqZeroExt.algebraMap_eq_inl]

end PositivityTheory.Xgp.c_bm_exists_period
end
end

section

open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB

namespace PositivityTheory.Xgp.sq_limit

open GlobalTheory.CompanionTheory.Ar.Giv GlobalTheory.CompanionTheory.Ar.Giv.SignedConv ReciprocityTheory.AnForm.M.FinHolAtlas

theorem continuousOn_logNormSec {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (L : LocPot X) (v : X → X → ℂ) (hL : IsPotential A L) (hv : IsSection A L v) :
    ContinuousOn (logNormSec L v) (bdry v)ᶜ := by
  intro y hy
  refine ContinuousAt.continuousWithinAt ?_
  have hy' : v y y ≠ 0 := hy
  have h1 : ContinuousAt (v y) y := LeviFormBoundaryTopology.continuousAt_of_holoOn A (hv.1 y) (L.mem_U y)
  have h2 : ContinuousAt (L.φ y) y :=
    LeviFormBoundaryTopology.continuousAt_of_smoothOn A (L.isOpen_U y) (hL.1 y) (L.mem_U y)
  have h3 : ContinuousAt (fun z => Real.log (‖v y z‖ * Real.exp (-L.φ y z))) y := by
    refine ContinuousAt.log (h1.norm.mul (Real.continuous_exp.continuousAt.comp h2.neg)) ?_
    exact mul_ne_zero (norm_ne_zero_iff.2 hy') (Real.exp_pos _).ne'
  refine h3.congr ?_
  filter_upwards [(L.isOpen_U y).mem_nhds (L.mem_U y)] with z hz
  unfold logNormSec
  rw [hv.2 y z z ⟨hz, L.mem_U z⟩]

theorem smoothOn_mono {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {U V : Set X} {f : X → ℝ} (hUV : U ⊆ V) (h : A.SmoothOn V f) : A.SmoothOn U f :=
  fun j => (h j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono hUV))

theorem isPshOn_mono {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {U V : Set X} {P : LocPot X} (hUV : U ⊆ V) (h : IsPshOn A V P) : IsPshOn A U P :=
  fun x j y hy w => h x j y ⟨hy.1, hy.2.1, hUV hy.2.2⟩ w

theorem unifIntSigned (hU : UnifIntStatement) {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) {n : ℕ}
    (m : Fin n → ℕ) (W : Fin n → Set X) (hΘ : IsPotential A Θ) (hΘp : IsPosPot A Θ)
    (hL : IsPotential A L) (hS : IsSection A L s) (hSNC : IsSNC A L s m W)
    (hs : ∀ y, logNormSec L s y ≤ 0) (L' : LocPot X) (v : X → X → ℂ) (Dg : Set X)
    (hL' : IsPotential A L') (hv : IsSection A L' v) (hvS : IsSNC A L' v ![1] ![Dg])
    (hsv : IsSNC A (L + L') (fun x y => s x y * v x y) (Fin.snoc m 1) (Fin.snoc W Dg))
    (hvn : ∀ y, logNormSec L' v y ≤ 0)
    (th : Fin e → LocPot X) (ph : Fin e → X → ℝ) (phT : Fin e → ℝ → X → ℝ) (C₅ C t₀ : ℝ)
    (hSW : ∀ i, IsSingWeight A L s (th i) (ph i) C₅)
    (hRF : ∀ i, IsRegFamily A Θ L s (th i) (ph i) (phT i) C t₀)
    (hC2 : ∀ i, IsRegFamilyC2 A s (ph i) (phT i)) :
    MIntegrable A (fun i => th i + LocPot.ofFun (ph i)) (logNormSec L' v) ∧
      (∀ᶠ t in 𝓝[>] (0 : ℝ), MIntegrable A (fun i => th i + LocPot.ofFun (phT i t)) (logNormSec L' v)) ∧
      Tendsto (fun t => mInt A (fun i => th i + LocPot.ofFun (phT i t)) (logNormSec L' v)) (𝓝[>] 0)
        (𝓝 (mInt A (fun i => th i + LocPot.ofFun (ph i)) (logNormSec L' v))) := by
  letI : MeasurableSpace X := borel X
  haveI : BorelSpace X := ⟨rfl⟩
  set g := logNormSec L' v with hg
  have hΘpsh : IsPsh A Θ := isPsh_of_isPosPot A Θ hΘp
  set U : Set X := (bdry s)ᶜ ∩ (bdry v)ᶜ with hUdef
  have hUo : IsOpen U := (LeviFormBoundaryTopology.isClosed_bdry hS).isOpen_compl.inter
    (LeviFormBoundaryTopology.isClosed_bdry hv).isOpen_compl
  have hUs : U ⊆ (bdry s)ᶜ := Set.inter_subset_left
  have hnull : ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Uᶜ) = 0 := by
    intro j
    rw [hUdef, Set.compl_inter, Set.preimage_union, Set.inter_union_distrib_left]
    exact measure_union_null (chart_null A L s m W hS hSNC j) (chart_null A L' v _ _ hv hvS j)
  have hgc : ContinuousOn g U := (continuousOn_logNormSec A L' v hL' hv).mono Set.inter_subset_right
  have hmem : ∀ T : Finset (Fin e),
      (∀ i, IsSingWeight A L s (if i ∈ T then th i else LocPot.ofFun 0)
        (if i ∈ T then ph i else 0) |C₅|) ∧
      (∀ i, IsRegFamily A Θ L s (if i ∈ T then th i else LocPot.ofFun 0)
        (if i ∈ T then ph i else 0) (fun t => if i ∈ T then phT i t else 0) |C|
        (min t₀ (Real.exp (-Real.exp 1)))) ∧
      (∀ i, IsRegFamilyC2 A s (if i ∈ T then ph i else 0) (fun t => if i ∈ T then phT i t else 0)) := by
    intro T
    have hz : ∀ i : Fin e, IsSingWeight A L s (LocPot.ofFun 0) 0 |C₅| ∧
        IsRegFamily A Θ L s (LocPot.ofFun 0) 0 (fun _ => 0) |C| (min t₀ (Real.exp (-Real.exp 1))) ∧
        IsRegFamilyC2 A s 0 (fun _ => 0) := fun i =>
      zero_member A Θ L s |C₅| |C| _ hΘ hΘp hs (abs_nonneg _) (abs_nonneg _)
        (lt_min (hRF i).1 (Real.exp_pos _)) (min_le_right _ _)
    refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩ <;> by_cases hi : i ∈ T <;>
      simp only [hi, ↓reduceIte]
    · exact isSingWeight_abs A L s _ _ _ hs (hSW i)
    · exact (hz i).1
    · exact isRegFamily_mono A Θ L s (th i) (ph i) (phT i) C t₀ |C| _ hΘ hΘpsh (hSW i).1 hs (hRF i)
        le_rfl (lt_min (hRF i).1 (Real.exp_pos _)) (min_le_left _ _) (min_le_right _ _)
    · exact (hz i).2.1
    · exact hC2 i
    · exact (hz i).2.2
  have hconv : ∀ T : Finset (Fin e),
      Integrable g (maMeasure A (fun i => (if i ∈ T then th i else LocPot.ofFun 0) +
        LocPot.ofFun (if i ∈ T then ph i else 0) + Θ)) ∧
      (∀ᶠ t in 𝓝[>] (0 : ℝ), Integrable g (maMeasure A (fun i => (if i ∈ T then th i else LocPot.ofFun 0) +
        LocPot.ofFun (if i ∈ T then phT i t else 0) + Θ))) ∧
      Tendsto (fun t => ∫ y, g y ∂maMeasure A (fun i => (if i ∈ T then th i else LocPot.ofFun 0) +
        LocPot.ofFun (if i ∈ T then phT i t else 0) + Θ)) (𝓝[>] 0)
        (𝓝 (∫ y, g y ∂maMeasure A (fun i => (if i ∈ T then th i else LocPot.ofFun 0) +
          LocPot.ofFun (if i ∈ T then ph i else 0) + Θ))) := by
    intro T
    obtain ⟨h1, h2, h3⟩ := hU A Θ L s m W hΘ hΘp hL hS hSNC hs L' v Dg hL' hv hvS hsv hvn
      (fun i => if i ∈ T then th i else LocPot.ofFun 0) (fun i => if i ∈ T then ph i else 0)
      (fun i t => if i ∈ T then phT i t else 0) |C₅| |C| _ (hmem T).1 (hmem T).2.1 (hmem T).2.2
    refine ⟨integrable_neg_iff.1 h1, h2.mono fun t ht => integrable_neg_iff.1 ht, ?_⟩
    simp only [integral_neg] at h3
    simpa only [neg_neg] using h3.neg
  have hlimT := fun T : Finset (Fin e) => GlobalTheory.T.mInt_eq_integral_maMeasure A U
    (fun i => if i ∈ T then th i else LocPot.ofFun 0) (fun i => if i ∈ T then ph i else 0) Θ hUo hnull
    (fun i => ((hmem T).1 i).1) hΘ hΘpsh (fun i => smoothOn_mono A hUs ((hmem T).1 i).2.1)
    (fun i => isPshOn_add_psh A _ _ _ Θ hUo ((hmem T).1 i).1 hΘ (smoothOn_mono A hUs ((hmem T).1 i).2.1)
      (isPshOn_mono A hUs ((hmem T).1 i).2.2.1) hΘpsh) g hgc (hconv T).1
  have hexpL := expand_mInt A U th ph Θ g hUo hnull (fun i => (hSW i).1) hΘ
    (fun i => smoothOn_mono A hUs (hSW i).2.1) (fun T => (hlimT T).1)
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ i, A.Smooth (phT i t)) ∧
      ∀ T : Finset (Fin e), (∀ i, A.Smooth (if i ∈ T then phT i t else 0) ∧
        IsPsh A ((if i ∈ T then th i else LocPot.ofFun 0) +
          LocPot.ofFun (if i ∈ T then phT i t else 0) + Θ)) ∧
        Integrable g (maMeasure A (fun i => (if i ∈ T then th i else LocPot.ofFun 0) +
          LocPot.ofFun (if i ∈ T then phT i t else 0) + Θ)) := by
    refine (eventually_all.2 fun i => ?_).and (eventually_all.2 fun T => ?_)
    · exact (eventually_isPsh A Θ L s (th i) (ph i) (phT i) C t₀ hΘ hΘp (hSW i).1 (hRF i)).mono
        fun t ht => ht.1
    · refine (eventually_all.2 fun i => ?_).and (hconv T).2.1
      exact eventually_isPsh A Θ L s _ _ _ _ _ hΘ hΘp ((hmem T).1 i).1 ((hmem T).2.1 i)
  have hreg : ∀ᶠ t in 𝓝[>] (0 : ℝ), MIntegrable A (fun i => th i + LocPot.ofFun (phT i t)) g ∧
      ∑ T : Finset (Fin e), (-1 : ℝ) ^ (e - T.card) *
        ∫ y, g y ∂maMeasure A (fun i => (if i ∈ T then th i else LocPot.ofFun 0) +
          LocPot.ofFun (if i ∈ T then phT i t else 0) + Θ) =
        mInt A (fun i => th i + LocPot.ofFun (phT i t)) g := by
    filter_upwards [hev] with t ht
    have hmt := fun T : Finset (Fin e) => GlobalTheory.T.mInt_eq_integral_maMeasure A U
      (fun i => if i ∈ T then th i else LocPot.ofFun 0) (fun i => if i ∈ T then phT i t else 0) Θ hUo hnull
      (fun i => ((hmem T).1 i).1) hΘ hΘpsh (fun i => smoothOn_of_smooth A _ _ ((ht.2 T).1 i).1)
      (fun i => isPshOn_of_isPsh A _ _ ((ht.2 T).1 i).2) g hgc (ht.2 T).2
    have hx := expand_mInt A U th (fun i => phT i t) Θ g hUo hnull (fun i => (hSW i).1) hΘ
      (fun i => smoothOn_of_smooth A _ _ (ht.1 i)) (fun T => (hmt T).1)
    refine ⟨hx.1, ?_⟩
    rw [hx.2]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [(hmt T).2]
  refine ⟨hexpL.1, hreg.mono fun t ht => ht.1, ?_⟩
  rw [hexpL.2]
  refine Tendsto.congr' (hreg.mono fun t ht => ht.2) ?_
  refine tendsto_finsetSum _ fun T _ => ?_
  rw [(hlimT T).2]
  exact ((hconv T).2.2).const_mul _

theorem singular_part (hI : Inputs) {d : ℕ} {σ : Type} [Fintype σ] {SY : AnSys (d + 1) σ} {a₀ : σ}
    {ε : σ → ℤ} (Q : AnSq SY a₀ ε) (w : Fin (d + 2) → Option σ) :
    MIntegrable Q.SW.A (fun r => Q.SW.potH (w r)) (logNormSec Q.L' Q.v) ∧
      (∀ᶠ t in 𝓝[>] (0 : ℝ), MIntegrable Q.SW.A (fun r => Q.SW.potT (w r) t) (logNormSec Q.L' Q.v)) ∧
      Tendsto (fun t => mInt Q.SW.A (fun r => Q.SW.potT (w r) t) (logNormSec Q.L' Q.v)) (𝓝[>] 0)
        (𝓝 (mInt Q.SW.A (fun r => Q.SW.potH (w r)) (logNormSec Q.L' Q.v))) :=
  unifIntSigned hI.unifInt Q.SW.A Q.SW.Θ Q.SW.L Q.SW.s Q.SW.m Q.SW.W Q.SW.potΘ Q.SW.posΘ Q.SW.potL
    Q.SW.sec Q.SW.snc Q.SW.norm_le Q.L' Q.v Q.Dg Q.potL' Q.secv Q.sncv Q.sncsv Q.normv
    (fun r => Q.SW.th (w r)) (fun r => Q.SW.ph (w r)) (fun r => Q.SW.phT (w r)) Q.SW.C₅ Q.SW.C Q.SW.t₀
    (fun r => Q.SW.sing (w r)) (fun r => Q.SW.reg (w r)) (fun r => Q.SW.c2 (w r))

end PositivityTheory.Xgp.sq_limit
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

theorem PositivityTheory.Xgp.t_c_fm_exists_flags_tie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)) (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω (rk (CMType H) D.p D.q))) ⟶ X'), CoordTie ℤ ξ' (seg (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) → CoordTie ℤ ξ' (flagCoord ((k : K₀) → J₀ k) (seg x₀) φ (cc 𝔐 bW bO)) := by
  intro E _ _ _ H D l Xo c Y S Ω _ K₀ _ J₀ _ x₀ 𝔐 bW bO n φ X' ξ' h
  let e : FlagIx ((k : K₀) → J₀ k) n (rk (CMType H) D.p D.q) ≃
      ((k : K₀ ⊕ StepIx (CMType H) D.p D.q) → idx J₀ n k) :=
    (Equiv.sumPiEquivProdPi (idx J₀ n)).symm
  have h2 := coordTie_comp_equiv h e
  convert h2 using 1
  funext cJ
  obtain ⟨c0, c1⟩ := cJ
  change _ = seg (yv (aOf 𝔐 bW bO φ) x₀) (e (c0, c1))
  simp only [seg, flagCoord, Fintype.prod_sum_type, map_prod]
  congr 1
end
