module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle424
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShellMassIntegrableNearNondegenerateZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CmCurveGoodOutsidePrimePremises
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle004
public import Formalism.PairingDivisors.StatementH
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Mon
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle004
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.HasSumLocallyUniformlyWeierstrassZetaExcept

@[expose] public section

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CatCoh.Desc


open Classical in
theorem twoCocycle_comma_coboundary_of_standardCover : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (n : ℕ) (d : Fin n → F.obj T), Ideal.span (Set.range d) = ⊤ → ∀ (z : ∀ t t' t'', (T ⟶ G.obj t) → (t ⟶ t') → (t' ⟶ t'') → F.obj (G.obj t'')), (∀ t t' t'' t''' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t'') (c : t'' ⟶ t'''), mp F (G.map c) (z t t' t'' u a b) + z t t'' t''' u (a ≫ b) c = z t t' t''' u a (b ≫ c) + z t' t'' t''' (u ≫ G.map a) b c) → (∀ i : Fin n, ∃ y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t'), ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), IsUnit (mp F u (d i)) → mp F (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b) → ∃ y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t'), ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), (∃ i, IsUnit (mp F u (d i))) → mp F (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b := by
  intro R _ C _ C' _ F G _ _ H hcov hfil T n d hd z hz hy
  choose y hy using hy
  have hu : ∀ {t t' : C'} {u : T ⟶ G.obj t} (a : t ⟶ t') {x : F.obj T}, IsUnit (mp F u x) →
      IsUnit (mp F (u ≫ G.map a) x) := fun a _ h ↦ isUnit_comp _ h
  have h1 := fun i j : Fin n ↦ GlobalTheory.T.oneCocycle_invertibleLocus_isCoboundary_alt F G H hcov hfil T (d i * d j)
    (fun t t' u a ↦ y j t t' u a - y i t t' u a) fun t t' t'' u a b h ↦ by
      rw [map_mul, IsUnit.mul_iff] at h
      rw [map_sub]
      linear_combination hy i t t' t'' u a b h.1 - hy j t t' t'' u a b h.2
  choose β hβ' using h1
  have hβ : ∀ i j t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), IsUnit (mp F u (d i)) →
      IsUnit (mp F u (d j)) →
      β i j t' (u ≫ G.map a) - mp F (G.map a) (β i j t u) = y j t t' u a - y i t t' u a :=
    fun i j t t' u a hi hj ↦ hβ' i j t t' u a (by rw [map_mul]; exact hi.mul hj)
  have h2 := fun i j k : Fin n ↦ GlobalTheory.T.sections_invertibleLocus_of_basisFunctor F G H hcov hfil T (d i * d j * d k)
    (fun t u ↦ β j k t u - β i k t u + β i j t u) fun t t' u a h ↦ by
      rw [map_mul, map_mul, IsUnit.mul_iff, IsUnit.mul_iff] at h
      rw [map_add (f := _), map_sub]
      linear_combination hβ j k t t' u a h.1.2 h.2 - hβ i k t t' u a h.1.1 h.2 +
        hβ i j t t' u a h.1.1 h.1.2
  choose x hx' hxs' using h2
  have hx : ∀ i j k, IsSec F (fun S u ↦ (IsUnit (mp F u (d i)) ∧ IsUnit (mp F u (d j))) ∧
      IsUnit (mp F u (d k))) (x i j k) := fun i j k S S' u ψ h ↦
    hx' i j k S S' u ψ (by
      show IsUnit _
      rw [map_mul, map_mul]; exact (h.1.1.mul h.1.2).mul h.2)
  have hxs : ∀ i j k t (u : T ⟶ G.obj t), IsUnit (mp F u (d i)) → IsUnit (mp F u (d j)) →
      IsUnit (mp F u (d k)) → x i j k (G.obj t) u = β j k t u - β i k t u + β i j t u :=
    fun i j k t u hi hj hk ↦ hxs' i j k t u (by rw [map_mul, map_mul]; exact (hi.mul hj).mul hk)
  obtain ⟨e, he, he'⟩ := cech2 H hd x hx (fun l i j k S u hl hi hj hk ↦ by
    obtain ⟨m, b, hb, hb'⟩ := hcov S
    refine sep_std H hb _ fun S' ψ ⟨r, hr⟩ ↦ ?_
    obtain ⟨t, v, w, rfl⟩ := hb' r S' ψ hr
    have hl' := isUnit_comp v hl
    have hi' := isUnit_comp v hi
    have hj' := isUnit_comp v hj
    have hk' := isUnit_comp v hk
    rw [mp_comp, map_sub (mp F v), map_add (mp F v), map_sub (mp F v),
      ← hx i j k S _ u v ⟨⟨hi, hj⟩, hk⟩, ← hx l j k S _ u v ⟨⟨hl, hj⟩, hk⟩,
      ← hx l i k S _ u v ⟨⟨hl, hi⟩, hk⟩, ← hx l i j S _ u v ⟨⟨hl, hi⟩, hj⟩,
      hxs _ _ _ _ _ hi' hj' hk', hxs _ _ _ _ _ hl' hj' hk', hxs _ _ _ _ _ hl' hi' hk',
      hxs _ _ _ _ _ hl' hi' hj']
    ring_nf
    exact map_zero _)
  obtain ⟨γ, hγ⟩ : ∃ γ : Fin n → ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t), ∀ i j t u,
      IsUnit (mp F u (d i)) → IsUnit (mp F u (d j)) →
      γ j t u - γ i t u = β i j t u - e i j (G.obj t) u := by
    refine ⟨fun i t u ↦ if h : ∃ i, IsUnit (mp F u (d i)) then
      β h.choose i t u - e h.choose i _ u else 0, fun i j t u hi hj ↦ ?_⟩
    have h : ∃ i, IsUnit (mp F u (d i)) := ⟨i, hi⟩
    simp only [dif_pos h]
    linear_combination -he' _ i j _ u h.choose_spec hi hj + hxs _ i j t u h.choose_spec hi hj
  obtain ⟨α, hα⟩ : ∃ α : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t'), ∀ i t t' u a,
      IsUnit (mp F u (d i)) →
      α t t' u a = y i t t' u a - (γ i t' (u ≫ G.map a) - mp F (G.map a) (γ i t u)) := by
    refine ⟨fun t t' u a ↦ if h : ∃ i, IsUnit (mp F u (d i)) then
      y h.choose t t' u a - (γ h.choose t' (u ≫ G.map a) - mp F (G.map a) (γ h.choose t u)) else 0,
      fun i t t' u a hi ↦ ?_⟩
    have h : ∃ i, IsUnit (mp F u (d i)) := ⟨i, hi⟩
    simp only [dif_pos h]
    have k1 := congrArg (mp F (G.map a)) (hγ i _ t u hi h.choose_spec)
    have k2 := hγ i _ t' (u ≫ G.map a) (hu a hi) (hu a h.choose_spec)
    have k3 := he i _ _ _ u (G.map a) ⟨hi, h.choose_spec⟩
    have k4 := hβ i _ t t' u a hi h.choose_spec
    simp only [map_sub] at k1
    linear_combination k1 - k2 + k3 - k4
  refine ⟨α, fun t t' t'' u a b ⟨i, hi⟩ ↦ ?_⟩
  rw [hα i _ _ _ _ hi, hα i _ _ _ _ hi, hα i _ _ _ _ (hu a hi)]
  simp only [map_sub, mp_comp, Category.assoc, G.map_comp]
  linear_combination hy i t t' t'' u a b hi

end GlobalTheory.CatCoh.Desc
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

open MeasureTheory Filter Topology Metric in
open scoped ENNReal ContDiff in
private lemma continuous_sqn_of_isSec' {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι La : Type*}
    [AddCommGroup La] (A : _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas n Y ι La) {L : La} {N : ℕ} {s : Fin N → ι → Y → ℂ}
    (hs : ∀ k, A.IsSec L (s k)) : Continuous (A.sqn L s) := by
  have hsum : A.sqn L s = fun y => ∑ k, A.nsq L (s k) y := by
    funext y
    rfl
  rw [hsum]
  refine continuous_finsetSum _ fun k _ => ?_
  have hk : A.IsSecOn L Set.univ (s k) := hs k
  exact continuousOn_univ.mp (_root_.ReciprocityTheory.L2DbarEstimates.Y.api_nsq_contOn A isOpen_univ hk)

open MeasureTheory Filter Topology Metric in
open scoped ENNReal ContDiff in
private lemma mem_zeroSet_of_sqn_eq_zero {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι La : Type*}
    [AddCommGroup La] (A : _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas n Y ι La) {L : La} {N : ℕ} (s : Fin N → ι → Y → ℂ) {y : Y}
    (hy : A.sqn L s y = 0) : y ∈ A.zeroSet s := by
  have hy' : ∑ k, A.nsq L (s k) y = 0 := hy
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun k _ => A.nsq_nonneg L (s k) y)] at hy'
  simp only [_root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.zeroSet, Set.mem_setOf_eq]
  intro k
  have hk : ‖s k (A.pick y) y‖ ^ 2 * Real.exp (-A.ph L (A.pick y) y) = 0 :=
    hy' k (Finset.mem_univ _)
  have h2 := (mul_eq_zero.mp hk).resolve_right (Real.exp_pos _).ne'
  simpa using h2

open MeasureTheory Filter Topology Metric in
open scoped ENNReal ContDiff in
private lemma lintegral_le_sum_of_pairwiseDisjoint_pieces {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    (Z : Finset Y) (V W : Y → Set Y) (hd : (↑Z : Set Y).PairwiseDisjoint V)
    (hV : ∀ P ∈ Z, MeasurableSet (V P)) (hVW : ∀ P ∈ Z, V P ⊆ W P) (F : Y → ℝ≥0∞)
    (G : Y → Y → ℝ≥0∞) (hF0 : ∀ y, y ∉ ⋃ P ∈ Z, V P → F y = 0)
    (hFG : ∀ P ∈ Z, ∀ y ∈ V P, F y = G P y) :
    ∫⁻ y, F y ∂ν ≤ ∑ P ∈ Z, ∫⁻ y in W P, G P y ∂ν := by
  rw [← setLIntegral_eq_of_support_subset (s := ⋃ P ∈ Z, V P), lintegral_biUnion_finset hd hV]
  · refine Finset.sum_le_sum fun P hP => ?_
    rw [setLIntegral_congr_fun (hV P hP) (fun y hy => hFG P hP y hy)]
    exact lintegral_mono_set (hVW P hP)
  · intro y hy
    by_contra hyn
    exact hy (hF0 y hyn)

open MeasureTheory Filter Topology Metric in
open scoped ENNReal ContDiff in
private lemma resSq_nonneg {n : ℕ} {Y : Type*} [TopologicalSpace Y]
    [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι La : Type*}
    [AddCommGroup La] (A : _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas n Y ι La) (E L : La) (s : Fin n → ι → Y → ℂ) (P : Y) (c : ℂ) :
    0 ≤ _root_.GlobalTheory.Published.L2Extension.resSq A E L s P c := by
  unfold _root_.GlobalTheory.Published.L2Extension.resSq
  positivity


open MeasureTheory Filter Topology Metric in
open scoped ENNReal ContDiff in
theorem _root_.GlobalTheory.OTY.exists_local_extension : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas n Y ι La), 1 ≤ n → ∀ (E L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → ∀ hS : (A.zeroSet s).Finite, (∀ P ∈ A.zeroSet s, _root_.GlobalTheory.Published.L2Extension.jacAt A s P ≠ 0) → ∀ (f : Y → ℂ) (δ : ℝ), 0 < δ → ∃ (Ω : Set Y) (h : ι → Y → ℂ) (m : ℝ), (IsOpen Ω ∧ A.IsSecOn (A.kap + E) Ω h ∧ (∀ i y, y ∉ Ω → h i y = 0)) ∧ 0 < m ∧ (∀ y, A.sqn L s y < m → y ∈ Ω) ∧ (∀ P ∈ A.zeroSet s, h (A.pick P) P = f P) ∧ (∀ T : ℝ, 2 ≤ T → ∫⁻ y in {y | -T - 1 ≤ δ * _root_.GlobalTheory.Published.L2Extension.psi A L s y ∧ δ * _root_.GlobalTheory.Published.L2Extension.psi A L s y ≤ -T + 1}, ENNReal.ofReal (A.nsq (A.kap + E) h y * Real.exp (-_root_.GlobalTheory.Published.L2Extension.psi A L s y)) ∂A.mu ≤ ENNReal.ofReal (62 / 30 * (Real.pi ^ n / ((n - 1).factorial : ℝ)) / δ * ∑ P ∈ hS.toFinset, _root_.GlobalTheory.Published.L2Extension.resSq A E L s P (f P))) ∧ ∫⁻ y, ENNReal.ofReal (1 / (1 + (δ * _root_.GlobalTheory.Published.L2Extension.psi A L s y) ^ 2) * A.nsq (A.kap + E) h y * Real.exp (-_root_.GlobalTheory.Published.L2Extension.psi A L s y)) ∂A.mu < ⊤ := by
  intro n Y _ _ _ _ _ _ ι La _ A hn E L s hs hS hjac f δ hδ
  choose! N hNo hPN hNsub hNT hNfin using fun P (hP : P ∈ A.zeroSet s) =>
    _root_.GlobalTheory.OTY.ShellZero.shell_near_zero n Y ι La A hn E L s hs P hP (hjac P hP) (f P) δ hδ
  obtain ⟨U, hU, hUd⟩ := hS.t2_separation
  set Z := hS.toFinset with hZ
  have hmemZ : ∀ {P}, P ∈ Z → P ∈ A.zeroSet s := fun hP => hS.mem_toFinset.mp hP
  have hd : (↑Z : Set Y).PairwiseDisjoint (fun P => N P ∩ U P) := by
    intro P hP Q hQ hPQ
    exact Disjoint.mono Set.inter_subset_right Set.inter_subset_right
      (hUd (hmemZ (Finset.mem_coe.mp hP)) (hmemZ (Finset.mem_coe.mp hQ)) hPQ)
  have hVo : ∀ P ∈ Z, IsOpen (N P ∩ U P) := fun P hP => (hNo P (hmemZ hP)).inter (hU P).2
  obtain ⟨h, hh⟩ : ∃ h : ι → Y → ℂ, h = fun i y =>
      ∑ P ∈ Z, (N P ∩ U P).indicator (fun y => A.g (A.kap + E) i (A.pick P) y * f P) y :=
    ⟨_, rfl⟩
  have hloc : ∀ P ∈ Z, ∀ y ∈ N P ∩ U P, ∀ i, h i y = A.g (A.kap + E) i (A.pick P) y * f P := by
    intro P hP y hy i
    rw [hh]
    dsimp only
    rw [Finset.sum_eq_single P]
    · exact Set.indicator_of_mem hy _
    · intro Q hQ hQP
      refine Set.indicator_of_notMem (fun hyQ => ?_) _
      exact Set.disjoint_left.mp (hd (Finset.mem_coe.mpr hQ) (Finset.mem_coe.mpr hP) hQP) hyQ hy
    · intro hPn
      exact absurd hP hPn
  have hout : ∀ y, y ∉ ⋃ P ∈ Z, N P ∩ U P → ∀ i, h i y = 0 := by
    intro y hy i
    rw [hh]
    exact Finset.sum_eq_zero fun P hP =>
      Set.indicator_of_notMem (fun hyP => hy (Set.mem_iUnion₂.mpr ⟨P, hP, hyP⟩)) _
  have hZΩ : ∀ y ∈ A.zeroSet s, y ∈ ⋃ P ∈ Z, N P ∩ U P := fun y hy =>
    Set.mem_iUnion₂.mpr ⟨y, hS.mem_toFinset.mpr hy, hPN y hy, (hU y).1⟩
  have hΩo : IsOpen (⋃ P ∈ Z, N P ∩ U P) :=
    isOpen_iUnion fun P => isOpen_iUnion fun hP => hVo P hP
  have hnsq : ∀ P ∈ Z, ∀ y ∈ N P ∩ U P, A.nsq (A.kap + E) h y =
      A.nsq (A.kap + E) (fun i y => A.g (A.kap + E) i (A.pick P) y * f P) y := by
    intro P hP y hy
    unfold _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.nsq
    rw [hloc P hP y hy]
  have hnsq0 : ∀ y, y ∉ ⋃ P ∈ Z, N P ∩ U P → A.nsq (A.kap + E) h y = 0 := by
    intro y hy
    unfold _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.nsq
    rw [hout y hy]
    simp
  obtain ⟨m, hm, hmΩ⟩ : ∃ m : ℝ, 0 < m ∧ ∀ y, A.sqn L s y < m → y ∈ ⋃ P ∈ Z, N P ∩ U P := by
    rcases (⋃ P ∈ Z, N P ∩ U P)ᶜ.eq_empty_or_nonempty with he | hne
    · refine ⟨1, one_pos, fun y _ => ?_⟩
      by_contra hy
      have hyc : y ∈ (⋃ P ∈ Z, N P ∩ U P)ᶜ := hy
      rw [he] at hyc
      exact hyc
    · obtain ⟨x0, hx0, hmin⟩ := hΩo.isClosed_compl.isCompact.exists_isMinOn hne
        (continuous_sqn_of_isSec' A hs).continuousOn
      refine ⟨A.sqn L s x0, lt_of_le_of_ne (A.sqn_nonneg L s x0)
        (fun h0 => hx0 (hZΩ x0 (mem_zeroSet_of_sqn_eq_zero A s h0.symm))), fun y hy => ?_⟩
      by_contra hyΩ
      exact (not_le.mpr hy) (isMinOn_iff.mp hmin y hyΩ)
  refine ⟨⋃ P ∈ Z, N P ∩ U P, h, m, ⟨hΩo, ⟨?_, ?_⟩, fun i y hy => hout y hy i⟩, hm, hmΩ, ?_, ?_, ?_⟩
  · intro i x hx
    obtain ⟨P, hP, hxP⟩ := Set.mem_iUnion₂.mp hx.2
    have hWo : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (N P ∩ U P)) :=
      (A.chart i).isOpen_inter_preimage_symm (hVo P hP)
    have hW : (A.chart i).target ∩ (A.chart i).symm ⁻¹' (N P ∩ U P) ∈ 𝓝 x :=
      hWo.mem_nhds ⟨hx.1, hxP⟩
    have hg : DifferentiableAt ℂ (A.g (A.kap + E) i (A.pick P) ∘ (A.chart i).symm) x := by
      refine ((A.holo_g (A.kap + E) i (A.pick P)).mono ?_).differentiableAt hW
      intro z hz
      unfold _root_.ReciprocityTheory.L2DbarEstimates.Y.ovl
      exact ⟨hz.1, hNsub P (hmemZ hP) hz.2.1⟩
    refine ((hg.mul_const (f P)).congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hW] with z hz
    simp only [Function.comp_apply]
    exact hloc P hP _ hz.2 i
  · intro i j y hy hi hj
    obtain ⟨P, hP, hyP⟩ := Set.mem_iUnion₂.mp hy
    rw [hloc P hP y hyP i, hloc P hP y hyP j, ← mul_assoc,
      ← A.g_cocycle _ i j _ y hi hj (hNsub P (hmemZ hP) hyP.1)]
  · intro P hP
    rw [hloc P (hS.mem_toFinset.mpr hP) P ⟨hPN P hP, (hU P).1⟩, A.g_self _ _ (A.mem_pick P),
      one_mul]
  · intro T hT
    refine (lintegral_le_sum_of_pairwiseDisjoint_pieces _ Z (fun P => N P ∩ U P) N hd
      (fun P hP => (hVo P hP).measurableSet) (fun P _ => Set.inter_subset_left) _
      (fun P y => ENNReal.ofReal (A.nsq (A.kap + E)
        (fun i y => A.g (A.kap + E) i (A.pick P) y * f P) y *
          Real.exp (-_root_.GlobalTheory.Published.L2Extension.psi A L s y)))
      (fun y hy => by simp only [hnsq0 y hy, zero_mul, ENNReal.ofReal_zero])
      (fun P hP y hy => by simp only [hnsq P hP y hy])).trans ?_
    calc _ ≤ ∑ P ∈ Z, ENNReal.ofReal (62 / 30 * (Real.pi ^ n / ((n - 1).factorial : ℝ)) / δ *
          _root_.GlobalTheory.Published.L2Extension.resSq A E L s P (f P)) := by
          refine Finset.sum_le_sum fun P hP => ?_
          rw [Measure.restrict_restrict (hNo P (hmemZ hP)).measurableSet]
          exact hNT P (hmemZ hP) T hT
      _ = _ := by
          rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg]
          intro P _
          exact mul_nonneg (by positivity) (resSq_nonneg A E L s P (f P))
  · refine lt_of_le_of_lt (lintegral_le_sum_of_pairwiseDisjoint_pieces A.mu Z (fun P => N P ∩ U P) N hd
      (fun P hP => (hVo P hP).measurableSet) (fun P _ => Set.inter_subset_left) _
      (fun P y => ENNReal.ofReal (1 / (1 + (δ * _root_.GlobalTheory.Published.L2Extension.psi A L s y) ^ 2) *
        A.nsq (A.kap + E) (fun i y => A.g (A.kap + E) i (A.pick P) y * f P) y *
          Real.exp (-_root_.GlobalTheory.Published.L2Extension.psi A L s y)))
      (fun y hy => by simp only [hnsq0 y hy, mul_zero, zero_mul, ENNReal.ofReal_zero])
      (fun P hP y hy => by simp only [hnsq P hP y hy])) ?_
    exact ENNReal.sum_lt_top.2 fun P hP => hNfin P (hmemZ hP)

end GlobalTheory.OTY
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem isMonHom_of_fst_mul_snd {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (g : A ⟶ B)
    (h : (fst A A * snd A A) ≫ g = (fst A A ≫ g) * (snd A A ≫ g)) : IsMonHom g := by
  have hm : ∀ (T : Over S) (x y : T ⟶ A), (x * y) ≫ g = (x ≫ g) * (y ≫ g) := fun T x y => by
    have := congrArg (lift x y ≫ ·) h
    simpa only [← Category.assoc, MonObj.comp_mul, lift_fst, lift_snd] using this
  refine ⟨?_, ?_⟩
  · have h1 := hm (𝟙_ _) 1 1
    rw [_root_.mul_one] at h1
    have h2 : (1 : 𝟙_ (Over S) ⟶ A) ≫ g = 1 := left_eq_mul.1 h1
    simpa [Hom.one_def] using h2
  · have e : (fst A A * snd A A) = μ[A] := by simp [Hom.mul_def]
    rw [e] at h
    rw [h, Hom.mul_def]
    congr 1

theorem mul_comp_of_isGrpPullback {S S' : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]
    {Y Z : Over S'} [GrpObj Y] [GrpObj Z] {t : S' ⟶ S} {a : Y.left ⟶ A.left} {b : Z.left ⟶ B.left}
    (ha : IsGrpPullback Y A t a) (hb : IsGrpPullback Z B t b) (f : Y ⟶ Z) [IsMonHom f] (g : A ⟶ B)
    (hg : a ≫ g.left = f.left ≫ b) (T : Over S') (x y : Over.mk (T.hom ≫ t) ⟶ A) :
    (x * y) ≫ g = (x ≫ g) * (y ≫ g) := by
  let x' : T ⟶ Y := Over.homMk (ha.1.lift x.left T.hom (Over.w x)) (ha.1.lift_snd _ _ _)
  let y' : T ⟶ Y := Over.homMk (ha.1.lift y.left T.hom (Over.w y)) (ha.1.lift_snd _ _ _)
  have hx : x.left = x'.left ≫ a := (ha.1.lift_fst _ _ _).symm
  have hy : y.left = y'.left ≫ a := (ha.1.lift_fst _ _ _).symm
  have h1 := ha.2 T x' y' x y hx hy
  have h2 := hb.2 T (x' ≫ f) (y' ≫ f) (x ≫ g) (y ≫ g)
    (by rw [Over.comp_left, Over.comp_left, hx, Category.assoc, Category.assoc, hg])
    (by rw [Over.comp_left, Over.comp_left, hy, Category.assoc, Category.assoc, hg])
  ext
  rw [h2, Over.comp_left, h1, ← MonObj.mul_comp, Over.comp_left, Category.assoc, Category.assoc, hg]

theorem grpHom_algebraise : GlobalTheory.Published.FormalAlgebraisation.Morphisms → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (A B : Over (Spec (CommRingCat.of R))) [GrpObj A] [GrpObj B], IsProper A.hom → IsProper B.hom → ∀ (Y Z : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) [∀ e, GrpObj (Y e)] [∀ e, GrpObj (Z e)] (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (δ : ∀ e, (Z e).left ⟶ (Z (e + 1)).left) (a : ∀ e, (Y e).left ⟶ A.left) (b : ∀ e, (Z e).left ⟶ B.left), (∀ e, IsGrpPullback (Y e) A (thick R I e) (a e)) → (∀ e, β e ≫ a (e + 1) = a e) → (∀ e, IsGrpPullback (Z e) B (thick R I e) (b e)) → (∀ e, δ e ≫ b (e + 1) = b e) → ∀ f : ∀ e, Y e ⟶ Z e, (∀ e, IsMonHom (f e)) → (∀ e, β e ≫ (f (e + 1)).left = (f e).left ≫ δ e) → ∃ g : A ⟶ B, IsMonHom g ∧ (∀ e, a e ≫ g.left = (f e).left ≫ b e) ∧ ∀ g' : A ⟶ B, (∀ e, a e ≫ g'.left = (f e).left ≫ b e) → g' = g := by
  intro H R _ _ I hI A B _ _ hA hB Y Z _ _ β δ a b ha hβ hb hδ f hf hc
  obtain ⟨g, hg, hu⟩ := H R I hI A B hA inferInstance inferInstance inferInstance Y β a
    (fun e => (ha e).1) hβ (fun e => (f e).left ≫ b e)
    (fun e => by rw [Category.assoc, (hb e).1.w, ← Category.assoc, Over.w])
    (fun e => by rw [← Category.assoc, hc, Category.assoc, hδ])
  refine ⟨g, isMonHom_of_fst_mul_snd g ?_, hg, hu⟩
  haveI : IsProper (A ⊗ A).hom := by
    change IsProper (pullback.fst A.hom A.hom ≫ A.hom)
    infer_instance
  refine H.hom_ext hI fun e => ?_
  haveI := hf e
  let T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :=
    Over.mk (pullback.snd (A ⊗ A).hom (thick R I e))
  let P : Over.mk (T.hom ≫ thick R I e) ⟶ A ⊗ A :=
    Over.homMk (pullback.fst (A ⊗ A).hom (thick R I e)) pullback.condition
  have key := mul_comp_of_isGrpPullback (ha e) (hb e) (f e) g (hg e) T (P ≫ fst A A) (P ≫ snd A A)
  have key' : P ≫ (fst A A * snd A A) ≫ g = P ≫ ((fst A A ≫ g) * (snd A A ≫ g)) := by
    rw [← Category.assoc, MonObj.comp_mul, key, MonObj.comp_mul, Category.assoc, Category.assoc]
  exact congrArg (·.left) key'

end GlobalTheory
end

section

open GlobalTheory.Published Formalism.L2.Th1.F
open scoped IntermediateField

namespace GlobalTheory.CMModel

theorem isIntegral_sqrtNegNat (p : ℕ) : IsIntegral ℤ (sqrtNegNat p) :=
  IsIntegral.of_pow two_pos (by rw [sqrtNegNat_sq]; exact (isIntegral_natCast p).neg)

theorem exists_rat_of_mem_adjoin_sqrtNegNat {p : ℕ} {z : ℂ} (hz : z ∈ ℚ⟮sqrtNegNat p⟯) :
    ∃ a b : ℚ, z = a + b * sqrtNegNat p := by
  have hint : IsIntegral ℚ (sqrtNegNat p) := (isIntegral_sqrtNegNat p).tower_top
  have hz' : z ∈ Algebra.adjoin ℚ {sqrtNegNat p} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hz
  clear hz
  induction hz' using Algebra.adjoin_induction with
  | mem x hx => exact ⟨0, 1, by simpa using hx⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, d, rfl⟩ := hy
    exact ⟨a + c, b + d, by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, d, rfl⟩ := hy
    exact ⟨a * c - p * (b * d), a * d + b * c, by
      push_cast; linear_combination (b * d : ℂ) * sqrtNegNat_sq p⟩

theorem dvd_of_sqrtNegNat_mem {p q : ℕ} (hp : p.Prime) (h : sqrtNegNat q ∈ ℚ⟮sqrtNegNat p⟯) :
    p ∣ q := by
  obtain ⟨a, b, e⟩ := exists_rat_of_mem_adjoin_sqrtNegNat h
  have ha : a = 0 := by
    have := congrArg Complex.re e
    simpa [sqrtNegNat] using this.symm
  have e2 : (q : ℂ) = b ^ 2 * p := by
    have := sqrtNegNat_sq q
    rw [e, ha] at this
    push_cast at this
    linear_combination this - (b : ℂ) ^ 2 * sqrtNegNat_sq p
  have e3 : (q : ℚ) = b ^ 2 * p := by exact_mod_cast e2
  have hs : IsSquare ((q * p : ℕ) : ℚ) := ⟨b * p, by push_cast; rw [e3]; ring⟩
  obtain ⟨n, hn⟩ := Rat.isSquare_natCast_iff.1 hs
  have hpn : p ∣ n := by
    have : p ∣ n * n := hn ▸ dvd_mul_left p q
    exact (hp.dvd_mul.1 this).elim id id
  have : p * p ∣ q * p := hn ▸ mul_dvd_mul hpn hpn
  exact Nat.dvd_of_mul_dvd_mul_right hp.pos this

theorem mem_adjoin_of_invariant {p : ℕ} {L : PeriodPair} (hL : IsIntegersLattice p L) (m : ℂ) (hm0 : m ≠ 0)
    (e2 : (m ^ 4)⁻¹ * L.g₂ = L.g₂) (e3 : (m ^ 6)⁻¹ * L.g₃ = L.g₃) : m ∈ ℚ⟮sqrtNegNat p⟯ := by
  have H₀ := isHomothetic_scalePeriods L m hm0
  have e := lattice_eq_of_g₂_eq_of_g₃_eq (H₀.g₂_eq.trans e2) (H₀.g₃_eq.trans e3)
  have := (H₀ 1).2 ((hL 1).2 ⟨one_mem _, isIntegral_one⟩)
  rw [e, mul_one] at this
  exact ((hL m).1 this).1

theorem integersLattice_invariants_ne_zero :
    ∀ (p : ℕ) (L : PeriodPair), p.Prime → 3 < p → IsIntegersLattice p L →
      L.g₂ ≠ 0 ∧ L.g₃ ≠ 0 ∧ MulStable L (sqrtNegNat p) := by
  intro p L hp h3 hL
  refine ⟨fun h => ?_, fun h => ?_, fun ω hω => ?_⟩
  · have hs := sqrtNegNat_sq 3
    push_cast at hs
    have h6 : ((1 + sqrtNegNat 3) / 2) ^ 3 = -1 := by
      linear_combination (3 / 8 + sqrtNegNat 3 / 8) * hs
    have hm := mem_adjoin_of_invariant hL ((1 + sqrtNegNat 3) / 2)
      (fun e => by rw [e] at h6; norm_num at h6) (by simp [h])
      (by rw [show 6 = 3 * 2 by norm_num, pow_mul, h6]; simp)
    have hm' : sqrtNegNat 3 ∈ ℚ⟮sqrtNegNat p⟯ := by
      have := sub_mem (add_mem hm hm) (one_mem _)
      convert this using 1
      ring
    exact absurd (Nat.le_of_dvd three_pos (dvd_of_sqrtNegNat_mem hp hm')) (not_le.2 h3)
  · have hm := mem_adjoin_of_invariant hL Complex.I Complex.I_ne_zero (by simp) (by simp [h])
    have hm' : sqrtNegNat 1 ∈ ℚ⟮sqrtNegNat p⟯ := by simpa [sqrtNegNat] using hm
    have := Nat.le_of_dvd one_pos (dvd_of_sqrtNegNat_mem hp hm')
    omega
  · exact (hL _).2 ⟨mul_mem (IntermediateField.mem_adjoin_simple_self ℚ _) ((hL ω).1 hω).1,
      (isIntegral_sqrtNegNat p).mul ((hL ω).1 hω).2⟩

end GlobalTheory.CMModel
end

section

namespace GlobalTheory.PrimeMembershipExistence

theorem exists_prime_mem {K : Type} [Field K] [NumberField K] (w : Formalism.PairingDivisionLocalBalance.Pl K) :
    ∃ p : ℕ, Nat.Prime p ∧
      (p : NumberField.RingOfIntegers K) ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal w := by

  have hP := w.isPrime
  have hn0 : Ideal.absNorm w.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact w.ne_bot
  have hmem := Ideal.absNorm_mem w.asIdeal
  rw [← Nat.prod_factorization_pow_eq_self hn0, Finsupp.prod, Nat.cast_prod] at hmem
  obtain ⟨p, hp, hpm⟩ := hP.prod_mem_iff.1 hmem
  rw [Nat.support_factorization] at hp
  rw [Nat.cast_pow] at hpm
  exact ⟨p, Nat.prime_of_mem_primeFactors hp, hP.mem_of_pow_mem _ hpm⟩

end GlobalTheory.PrimeMembershipExistence
end
