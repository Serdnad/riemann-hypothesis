module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle100
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle105
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle096
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle101
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.FDeriv.Star
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Algebra.MvPolynomial
import Std.Tactic.BVDecide.Normalize.Prop
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChartGeo

open Topology

theorem inFrameDomain_eventually {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
    (y : (Σ k, J k) → Ω) (cc : (k : K) → J k) (f : Ω) {z : (Σ k, J k) → ℂ} (hz : InFrameDomain y cc f z) :
    ∀ᶠ w in 𝓝 z, InFrameDomain y cc f w := by
  obtain ⟨hc, v, ⟨d, g, h, hg, hh, hy, hgh, hhz, rfl⟩, hv⟩ := hz
  have hgz : MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) g) ≠ 0 := by
    intro h0
    apply hv
    rw [h0, zero_div]
  have c1 : ∀ᶠ w in 𝓝 z, MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) g) ≠ 0 :=
    (MvPolynomial.continuous_eval _).continuousAt.eventually_ne hgz
  have c2 : ∀ᶠ w in 𝓝 z, MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) h) ≠ 0 :=
    (MvPolynomial.continuous_eval _).continuousAt.eventually_ne hhz
  have c3 : ∀ᶠ w : (Σ k, J k) → ℂ in 𝓝 z, ∀ k, w ⟨k, cc k⟩ ≠ 0 :=
    Filter.eventually_all.2 fun k => (continuous_apply _).continuousAt.eventually_ne (hc k)
  filter_upwards [c1, c2, c3] with w h1 h2 h3
  exact ⟨h3, _, ⟨d, g, h, hg, hh, hy, hgh, h2, rfl⟩, div_ne_zero h1 h2⟩

theorem exists_perm_prefix {n : ℕ} (A : Finset (Fin n)) :
    ∃ π : Equiv.Perm (Fin n), ∀ i, ((π i : Fin n) : ℕ) < A.card ↔ i ∈ A := by
  classical
  have hle : A.card ≤ n := by simpa using A.card_le_univ
  let e : {x // x ∈ A} ≃ {j : Fin n // (j : ℕ) < A.card} :=
    A.equivFin.trans (Fin.castLEOrderIso hle).toEquiv
  refine ⟨e.extendSubtype, fun i => ⟨fun h => ?_, fun h => e.extendSubtype_mem i h⟩⟩
  by_contra hi
  exact e.extendSubtype_not_mem i hi h

theorem recentre_apply {n : ℕ} (t₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) (u : Fin n → ℂ) (i : Fin n) :
    HodgeMetric.recentre t₀ ρ π u i = t₀ i + (ρ : ℂ) * u (π i) := by
  simp [HodgeMetric.recentre]

theorem recentre_mem_ball {n : ℕ} {t₀ u : Fin n → ℂ} {ρ ε : ℝ} (hρ : 0 < ρ) (hε : ρ ≤ ε) (π : Equiv.Perm (Fin n))
    (hu : u ∈ Metric.ball (0 : Fin n → ℂ) 1) : HodgeMetric.recentre t₀ ρ π u ∈ Metric.ball t₀ ε := by
  rw [mem_ball_iff_norm]
  refine lt_of_lt_of_le ?_ hε
  rw [pi_norm_lt_iff hρ]
  intro i
  have h1 : ‖u (π i)‖ < 1 :=
    lt_of_le_of_lt (norm_le_pi_norm u (π i)) (by simpa using hu)
  have h2 : (HodgeMetric.recentre t₀ ρ π u - t₀) i = (ρ : ℂ) * u (π i) := by
    simp [recentre_apply]
  rw [h2, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
  nlinarith

theorem exists_recentre_chart : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] (y : (Σ k, J k) → Ω) (P : Ideal (MRing J)) (n : ℕ) (Bd : Set ((Σ k, J k) → ℂ)) (χ : SncChart P n Bd) (t₀ : Fin n → ℂ) (cc : (k : K) → J k) (f : Ω), t₀ ∈ Metric.ball (0 : Fin n → ℂ) 1 → InFrameDomain y cc f (χ.γ t₀) → ∃ (a₀ : ℕ) (π : Equiv.Perm (Fin n)) (ρ₀ : ℝ), a₀ ≤ n ∧ 0 < ρ₀ ∧ ρ₀ ≤ 1 ∧ (∀ i : Fin n, (i : ℕ) < a₀ → ((π.symm i : Fin n) : ℕ) < χ.a ∧ t₀ (π.symm i) = 0) ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, HodgeMetric.recentre t₀ ρ π u ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ InFrameDomain y cc f (χ.γ (HodgeMetric.recentre t₀ ρ π u)) ∧ (χ.γ (HodgeMetric.recentre t₀ ρ π u) ∉ Bd ↔ u ∈ Flat.punct n a₀ 1) := by
  intro K _ J _ Ω _ y P n Bd χ t₀ cc f ht₀ hF
  classical
  let A : Finset (Fin n) := Finset.univ.filter (fun i => (i : ℕ) < χ.a ∧ t₀ i = 0)
  have hA : ∀ i, i ∈ A ↔ (i : ℕ) < χ.a ∧ t₀ i = 0 := fun i => by simp [A]
  obtain ⟨π, hπ⟩ := exists_perm_prefix A
  have hγ : ContinuousAt χ.γ t₀ := (χ.analytic t₀ ht₀).continuousAt
  have e1 : ∀ᶠ t in 𝓝 t₀, InFrameDomain y cc f (χ.γ t) :=
    hγ.eventually (inFrameDomain_eventually y cc f hF)
  have e2 : ∀ᶠ t : Fin n → ℂ in 𝓝 t₀, ∀ i : Fin n, t₀ i ≠ 0 → t i ≠ 0 := by
    refine Filter.eventually_all.2 fun i => ?_
    by_cases hi : t₀ i = 0
    · exact Filter.Eventually.of_forall fun t h => absurd hi h
    · filter_upwards [(continuous_apply i).continuousAt.eventually_ne hi] with t ht _ using ht
  have e3 : ∀ᶠ t in 𝓝 t₀, t ∈ Metric.ball (0 : Fin n → ℂ) 1 :=
    Metric.isOpen_ball.mem_nhds ht₀
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (e1.and (e2.and e3))
  have hle : A.card ≤ n := by simpa using A.card_le_univ
  refine ⟨A.card, π, min ε 1, hle, lt_min hε one_pos, min_le_right _ _, fun i hi => ?_, fun ρ hρ hρ₀ u hu => ?_⟩
  · have : π.symm i ∈ A := (hπ _).1 (by simpa using hi)
    exact (hA _).1 this
  · obtain ⟨hF', hne, hb⟩ := hball _ (recentre_mem_ball hρ (hρ₀.trans (min_le_left _ _)) π hu)
    refine ⟨hb, hF', ?_⟩
    have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
    rw [χ.boundary _ hb]
    constructor
    · intro h
      refine ⟨by simpa using hu, fun j hj => fun h0 => h ?_⟩
      have hm : π.symm j ∈ A := (hπ _).1 (by simpa using hj)
      obtain ⟨h1, h2⟩ := (hA _).1 hm
      refine ⟨π.symm j, h1, ?_⟩
      rw [recentre_apply, h2]
      simp [h0]
    · rintro ⟨-, hu'⟩ ⟨i, hi, h0⟩
      by_cases hti : t₀ i = 0
      · have hm : i ∈ A := (hA i).2 ⟨hi, hti⟩
        have := hu' (π i) ((hπ i).2 hm)
        rw [recentre_apply, hti, zero_add] at h0
        exact (mul_ne_zero hρc this) h0
      · exact hne i hti h0

end GlobalTheory.CompanionTheory.Ar.ChartGeo
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ConjPeriods

open GroundTheory.Heights₂.Heights.Regular

theorem star_mem_logCover {n a : ℕ} (h : a ≤ n) {w : Fin n → ℂ} (hw : w ∈ logCover h) :
    star w ∈ logCover h := by
  refine ⟨fun i => ?_, fun k hk => ?_⟩
  · simpa using hw.1 i
  · simpa using hw.2 k hk

theorem expCover_star {n : ℕ} (a : ℕ) (w : Fin n → ℂ) : expCover a (star w) = star (expCover a w) := by
  funext k
  simp only [expCover, Pi.star_apply]
  split_ifs
  · exact Complex.exp_conj _
  · rfl

theorem isOpen_logCover {n a : ℕ} (h : a ≤ n) : IsOpen (logCover h) := by
  have : logCover h = (⋂ i : Fin a, {w : Fin n → ℂ | (w (Fin.castLE h i)).re < 0}) ∩
      ⋂ k : Fin n, {w : Fin n → ℂ | a ≤ k.val → ‖w k‖ < 1} := by
    ext w; simp [logCover]
  rw [this]
  refine (isOpen_iInter_of_finite fun i => ?_).inter (isOpen_iInter_of_finite fun k => ?_)
  · exact isOpen_lt (Complex.continuous_re.comp (continuous_apply _)) continuous_const
  · by_cases hk : a ≤ k.val
    · simpa [hk] using isOpen_lt (continuous_norm.comp (continuous_apply k)) continuous_const
    · simp [hk]

theorem star_mem_ball {n : ℕ} {z : Fin n → ℂ} (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) :
    star z ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
  rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos] at hz ⊢
  intro i
  simpa using hz i

theorem differentiableOn_conj {n g : ℕ} {S : Set (Fin n → ℂ)} (hS : IsOpen S) (hst : ∀ w ∈ S, star w ∈ S)
    {f : (Fin n → ℂ) → Fin g → ℂ} (hf : DifferentiableOn ℂ f S) :
    DifferentiableOn ℂ (fun w => star (f (star w))) S := by
  intro w hw
  have h1 : DifferentiableAt ℂ f (star w) := hf.differentiableAt (hS.mem_nhds (hst w hw))
  have h2 := h1.star_star
  rw [star_star] at h2
  exact h2.differentiableWithinAt

theorem dot_map_conj {g : ℕ} (x y : Fin g → ℂ) (M : Matrix (Fin g) (Fin g) ℂ) :
    x ⬝ᵥ M.map (starRingEnd ℂ) *ᵥ y = star (star x ⬝ᵥ M *ᵥ star y) := by
  simp [dotProduct, Matrix.mulVec, star_sum]

theorem isHermitian_map_conj {g : ℕ} {M : Matrix (Fin g) (Fin g) ℂ} (hM : M.IsHermitian) :
    (M.map (starRingEnd ℂ)).IsHermitian := by
  ext i j
  have := hM.apply i j
  simp [Matrix.conjTranspose_apply, ← this]

theorem star_single {n : ℕ} (c : Fin n) :
    star (Pi.single c (2 * Real.pi * Complex.I) : Fin n → ℂ) = -Pi.single c (2 * Real.pi * Complex.I) := by
  funext k
  by_cases hk : k = c
  · subst hk
    simp
  · simp [hk]

theorem sub_single_mem_logCover {n a : ℕ} (h : a ≤ n) {w : Fin n → ℂ} (hw : w ∈ logCover h) (i : Fin a) :
    w - Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I) ∈ logCover h := by
  refine ⟨fun j => ?_, fun k hk => ?_⟩
  · by_cases hj : Fin.castLE h j = Fin.castLE h i
    · simpa [hj, Pi.single_apply] using (by simpa [hj] using hw.1 j)
    · simpa [Pi.single_apply, hj] using hw.1 j
  · have hki : k ≠ Fin.castLE h i := by
      rintro rfl
      simp at hk
      omega
    simpa [Pi.single_apply, hki] using hw.2 k hk

def conj {n a g : ℕ} {Λ : Type} [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ)
    (hT : ∀ i, Function.Bijective (L.T i)) : Flat.LogPeriods n a g Λ where
  a_le := L.a_le
  free := L.free
  fin := L.fin
  rank := L.rank
  E := -L.E
  alt x := by simp [L.alt x]
  unimod := by
    constructor
    · intro x y hxy
      exact L.unimod.1 (neg_injective hxy)
    · intro f
      obtain ⟨x, hx⟩ := L.unimod.2 (-f)
      exact ⟨x, by simp [hx]⟩
  P w := AddMonoidHom.mk' (fun x => star (L.P (star w) x)) (fun x y => by simp)
  hol x := differentiableOn_conj (isOpen_logCover L.a_le) (fun w hw => star_mem_logCover L.a_le hw) (L.hol x)
  H z := (L.H (star z)).map (starRingEnd ℂ)
  herm w hw := by
    rw [← expCover_star]
    exact isHermitian_map_conj (L.herm _ (star_mem_logCover L.a_le hw))
  pos w hw z hz := by
    rw [← expCover_star, dot_map_conj]
    have h := L.pos _ (star_mem_logCover L.a_le hw) (star z) (by simpa using hz)
    simpa using h
  im w hw x y := by
    simp only [AddMonoidHom.mk'_apply]
    rw [← expCover_star, dot_map_conj]
    have h := L.im _ (star_mem_logCover L.a_le hw) x y
    simp [h]
  T i := ((LinearEquiv.ofBijective (L.T i) (hT i)).symm : Λ ≃ₗ[ℤ] Λ).toLinearMap
  mono i w hw x := by
    set e : Fin _ → ℂ := Pi.single (Fin.castLE L.a_le i) (2 * Real.pi * Complex.I) with he
    have hw₁ : star w - e ∈ logCover L.a_le :=
      sub_single_mem_logCover L.a_le (star_mem_logCover L.a_le hw) i
    have hm := L.mono i _ hw₁ ((LinearEquiv.ofBijective (L.T i) (hT i)).symm x)
    have hTT : L.T i ((LinearEquiv.ofBijective (L.T i) (hT i)).symm x) = x :=
      (LinearEquiv.ofBijective (L.T i) (hT i)).apply_symm_apply x
    rw [hTT, ← he, sub_add_cancel] at hm
    have hs : star (w + e) = star w - e := by
      rw [star_add, he, star_single, sub_eq_add_neg]
    simp only [AddMonoidHom.mk'_apply, LinearEquiv.coe_coe]
    rw [hs, hm]
  W := L.W
  coiso x hx := L.coiso x fun y hy => by simpa using hx y hy
  s x z := star (L.s x (star z))
  s_hol x := differentiableOn_conj Metric.isOpen_ball (fun _ hz => star_mem_ball hz) (L.s_hol x)
  s_eq x w hw := by
    simp only [AddMonoidHom.mk'_apply]
    rw [← expCover_star, L.s_eq x _ (star_mem_logCover L.a_le hw)]
  span := by
    rw [eq_top_iff]
    intro v _
    have key : ∀ y ∈ Submodule.span ℂ (Set.range fun x => L.s x 0),
        star y ∈ Submodule.span ℂ (Set.range fun x => star (L.s x (star (0 : Fin _ → ℂ)))) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨x, rfl⟩ := hy
        exact Submodule.subset_span ⟨x, by simp⟩
      | zero => simp
      | add y z _ _ hy hz => simpa using Submodule.add_mem _ hy hz
      | smul c y _ hy =>
        rw [star_smul]
        exact Submodule.smul_mem _ _ hy
    have := key (star v) (by rw [L.span]; trivial)
    simpa using this

theorem exists_conj_periodGram : ∀ (n a g r : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ)
    (U : Fin r → (Fin n → ℂ) → Fin g → ℂ), (∀ i, Function.Bijective (L.T i)) →
    ∃ L' : Flat.LogPeriods n a g Λ, ∀ u ∈ Flat.punct n a 1,
      HodgeMetric.periodGram L' (fun k u' => star (U k (star u'))) u =
        (HodgeMetric.periodGram L U (star u)).map (starRingEnd ℂ) := by
  intro n a g r Λ _ L U hT
  refine ⟨conj L hT, fun u _ => ?_⟩
  ext i j
  simp only [HodgeMetric.periodGram, Matrix.of_apply, Matrix.map_apply]
  change _ * (_ ⬝ᵥ ((L.H (star u)).map (starRingEnd ℂ)) *ᵥ _) = _
  rw [dot_map_conj, map_mul, Complex.conj_ofReal]
  simp

end GlobalTheory.CompanionTheory.Ar.Flat.ConjPeriods
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)


theorem _root_.GlobalTheory.T.root_origin_coord_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (R : Top.RootModel (CMType H) (D.p + D.q)) (S₀ S : Finset ℕ) (o : RootOrigin Y S₀ R Fx) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (bk : R.K → K) (bx : ∀ k, R.ι k ≃ J (bk k)) (𝔐 : HodgeCpt Y S y) (i : R.Ω →+* Ω) (h : 𝔐.X ⟶ o.𝔐.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ o.𝔐.ξ h i) (Fl : 𝔐.Flag) (xdeg : RootIx D → K → ℤ) (e : RootIx D → Ω), (∀ k a, y ⟨bk k, bx k a⟩ = i (R.y ⟨k, a⟩)) → GenPull o.Fl Fl i hd → Fl.RootLines xdeg e → (∀ (p : Cpt 𝔐.ξ) (a : R.Ω), a ∈ regAt o.𝔐.ξ (pushCpt hd p) → unitAt 𝔐.ξ p (i a) → unitAt o.𝔐.ξ (pushCpt hd p) a) → (∀ (p : Cpt 𝔐.ξ) (a : R.Ω), a ∈ regAt o.𝔐.ξ (pushCpt hd p) → i a ∈ regAt 𝔐.ξ p) → (∀ x : 𝔐.X, x ∈ abLocus 𝔐.t.G ↔ h x ∈ abLocus o.𝔐.t.G) → ∀ p : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r p) → ∀ (a : Fin (Fx.m + 1)) (t : Ω), InChart 𝔐.ξ (fun i' => (i.comp o.g) (Fx.yf i')) a p → (Lat.tens Fl.rootLat fun r => -Fx.n r).IsGenAt p t → (i.comp o.g) Fx.sE * (i.comp o.g) (Fx.yf a) ^ Fx.q' / t ∈ regAt 𝔐.ξ p ∧ (p.1 ∉ abLocus 𝔐.t.G → ¬ unitAt 𝔐.ξ p ((i.comp o.g) Fx.sE * (i.comp o.g) (Fx.yf a) ^ Fx.q' / t)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Chg.CoverEff.section_on_cover | exact GlobalTheory.CompanionTheory.Ar.Chg.CoverEff.section_on_cover | (intros; apply GlobalTheory.CompanionTheory.Ar.Chg.CoverEff.section_on_cover <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChgUnit

theorem mem_regAt_of_valAt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {R : Type}
    [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X} {a : Ω} {r : R} (h : ValAt ξ z a r) (p : Cpt ξ)
    (hp : p.1 = centre z) : a ∈ regAt ξ p := by
  obtain ⟨x, hx⟩ := p
  dsimp only at hp
  subst hp
  obtain ⟨_, s, hs, -⟩ := h
  exact ⟨s, hs⟩

theorem inChart_of_coordsAt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {K : Type}
    [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {R : Type} [CommRing R] [IsLocalRing R]
    {z : Spec (CommRingCat.of R) ⟶ X} {w : (Σ k, J k) → R} (hw : CoordsAt ξ y z w) (c : (k : K) → J k)
    (hc : ∀ k, IsUnit (w ⟨k, c k⟩)) (p : Cpt ξ) (hp : p.1 = centre z) :
    InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p := by
  refine ⟨Finset.prod_ne_zero_iff.2 fun k _ => (hw.2 k _ (hc k)).1, fun c' => ?_⟩
  show (∏ k, y ⟨k, c' k⟩) / (∏ k, y ⟨k, c k⟩) ∈ regAt ξ p
  rw [← Finset.prod_div_distrib]
  refine prod_mem fun k _ => ?_
  obtain ⟨r, hr, -⟩ := (hw.2 k _ (hc k)).2 (c' k)
  exact mem_regAt_of_valAt hr p hp

theorem exists_unit_of_span_eq {Ω : Type} [Field Ω] (R : Subring Ω) {a b : Ω} (ha : a ≠ 0)
    (h : Submodule.span R {a} = Submodule.span R {b}) : ∃ u : Ω, u ∈ R ∧ u⁻¹ ∈ R ∧ a = u * b := by
  have h1 : a ∈ Submodule.span R {b} := h ▸ Submodule.mem_span_singleton_self a
  have h2 : b ∈ Submodule.span R {a} := h ▸ Submodule.mem_span_singleton_self b
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 h1
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 h2
  have hr' : (r : Ω) * b = a := hr
  have ht' : (t : Ω) * a = b := ht
  have hrt : (r : Ω) * t = 1 := by
    apply mul_right_cancel₀ ha
    rw [_root_.mul_assoc, ht', hr', _root_.one_mul]
  refine ⟨r, r.2, ?_, hr'.symm⟩
  rw [inv_eq_of_mul_eq_one_right hrt]
  exact t.2

theorem zpow_mem_of_inv_mem {Ω : Type} [Field Ω] (R : Subring Ω) {u : Ω} (h : u ∈ R) (h' : u⁻¹ ∈ R) (n : ℤ) :
    u ^ n ∈ R := by
  cases n with
  | ofNat m => simpa using pow_mem h m
  | negSucc m =>
    rw [zpow_negSucc, ← inv_pow]
    exact pow_mem h' _

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem tens_unit_eq {Λ : Lat ξ Ω} {p : Cpt ξ} {s : Ω} (hs : Λ.IsGenAt p s) (n : ℤ) :
    Lat.tens (fun _ : Unit => Λ) (fun _ => n) p = Submodule.span (regAt ξ p) {s ^ n} := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro t ⟨s', hs', rfl⟩
    have h' := hs' ()
    obtain ⟨u, hu, hu', e⟩ := exists_unit_of_span_eq (regAt ξ p) h'.1 (h'.2.symm.trans hs.2)
    refine Submodule.mem_span_singleton.2 ⟨⟨u ^ n, zpow_mem_of_inv_mem _ hu hu' n⟩, ?_⟩
    show u ^ n * s ^ n = _
    simp [e, mul_zpow]
  · refine Submodule.span_le.2 ?_
    rintro t rfl
    exact Submodule.subset_span ⟨fun _ => s, fun _ => hs, by simp⟩

theorem exists_gen_of_tens {Λ : Lat ξ Ω} {p : Cpt ξ} {g : Ω} {n : ℤ} (hg : g ≠ 0)
    (h : Lat.tens (fun _ : Unit => Λ) (fun _ => n) p = Submodule.span (regAt ξ p) {g}) : ∃ s, Λ.IsGenAt p s := by
  by_contra hn
  have hempty : {t | ∃ s : Unit → Ω, (∀ i, Λ.IsGenAt p (s i)) ∧ t = ∏ i, s i ^ (fun _ => n) i} = ∅ := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨s, hs, -⟩
    exact hn ⟨_, hs ()⟩
  have h0 : Lat.tens (fun _ : Unit => Λ) (fun _ => n) p = ⊥ := by
    show Submodule.span _ _ = ⊥
    rw [hempty, Submodule.span_empty]
  have hm : g ∈ Submodule.span (regAt ξ p) {g} := Submodule.mem_span_singleton_self g
  rw [← h, h0] at hm
  exact hg ((Submodule.mem_bot _).1 hm)

theorem exists_value_of_unit (hξ : IsCptGen ξ) (z : Spec (CommRingCat.of ℂ) ⟶ X) (hz : genPt ξ ⤳ centre z) {f : Ω}
    (hf : f ≠ 0) (h1 : f ∈ regAt ξ ⟨centre z, hz⟩) (h2 : f⁻¹ ∈ regAt ξ ⟨centre z, hz⟩) :
    ∃ u : ℂ, u ≠ 0 ∧ ValAt ξ z f u := by
  obtain ⟨s, hs⟩ := h1
  obtain ⟨t, ht⟩ := h2
  have hst : s * t = 1 := hξ.inj ⟨centre z, hz⟩ (by rw [map_mul, hs, ht, map_one, mul_inv_cancel₀ hf])
  refine ⟨(Scheme.stalkClosedPointTo z).hom s, fun h0 => ?_, hz, s, hs, rfl⟩
  exact ((IsUnit.of_mul_eq_one t hst).map (Scheme.stalkClosedPointTo z).hom).ne_zero h0

theorem comparison_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (a : K → ℤ) (a₀ : K₀ → ℤ) (e : Ω) (e₀ : Ω₀) (r : CMType H × Fin (D.p + D.q)), Function.Injective β → CharZero Ω → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → GenPull Fl₀ Fl i hd → (Fl₀.rootLat r).IsDegOn Set.univ y₀ a₀ e₀ → (Fl.rootLat r).IsDegOn Set.univ y a e → (∀ (p : Cpt 𝔐.ξ) (a : Ω₀), a ∈ regAt 𝔐₀.ξ (pushCpt hd p) → unitAt 𝔐.ξ p (i a) → unitAt 𝔐₀.ξ (pushCpt hd p) a) → (∀ (p : Cpt 𝔐.ξ) (a : Ω₀), a ∈ regAt 𝔐₀.ξ (pushCpt hd p) → i a ∈ regAt 𝔐.ξ p) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w → CoordsAt 𝔐₀.ξ y₀ (z ≫ h) (fun p => w (blkV bk bx p))) → ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w → ∀ (c : (k : K) → J k) (c₀ : (k : K₀) → J₀ k), (∀ k, w ⟨k, c k⟩ ≠ 0) → (∀ k, w (blkV bk bx ⟨k, c₀ k⟩) ≠ 0) → ∃ u : ℂ, u ≠ 0 ∧ ValAt 𝔐.ξ z (i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ a₀ k) * e₀) / ((∏ k, y ⟨k, c k⟩ ^ a k) * e)) u := by
  intro E _ _ _ H D l Xo c O _ β Y S₀ S Ω₀ Ω _ _ K₀ K _ _ J₀ J _ _ y₀ y 𝔐₀ 𝔐 i h hd Fl₀ Fl bk bx a a₀ e e₀ r hβ hΩ
    hy hgen hdeg₀ hdeg hunit hreg hco z w hw cc c₀ hc hc₀
  haveI := hΩ
  have hz : genPt 𝔐.ξ ⤳ centre z := 𝔐.all _
  let q : Cpt 𝔐.ξ := ⟨centre z, hz⟩
  let q₀ : Cpt 𝔐₀.ξ := pushCpt hd q
  have hw₀ := hco z w hw
  have huc : ∀ k, IsUnit (w ⟨k, cc k⟩) := fun k => IsUnit.mk0 _ (hc k)
  have huc₀ : ∀ k, IsUnit ((fun p => w (blkV bk bx p)) (⟨k, c₀ k⟩ : Σ k, J₀ k)) := fun k => IsUnit.mk0 _ (hc₀ k)
  have hq₀c : q₀.1 = centre (z ≫ h) := rfl
  have hq : (Fl.rootLat r) q = Submodule.span (regAt 𝔐.ξ q) {(∏ k, y ⟨k, cc k⟩ ^ a k) * e} :=
    hdeg.2 q trivial cc (inChart_of_coordsAt hw cc huc q rfl)
  have hq₀ : (Fl₀.rootLat r) q₀ = Submodule.span (regAt 𝔐₀.ξ q₀) {(∏ k, y₀ ⟨k, c₀ k⟩ ^ a₀ k) * e₀} :=
    hdeg₀.2 q₀ trivial c₀ (inChart_of_coordsAt hw₀ c₀ huc₀ q₀ hq₀c)
  have hg : (∏ k, y ⟨k, cc k⟩ ^ a k) * e ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hw.2 k _ (huc k)).1) hdeg.1
  have hg₀ : (∏ k, y₀ ⟨k, c₀ k⟩ ^ a₀ k) * e₀ ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hw₀.2 k _ (huc₀ k)).1) hdeg₀.1
  obtain ⟨s₀, hs₀⟩ := exists_gen_of_tens
    (Λ := (𝔐₀.V (HodgeCpt.rootIdx D r).1).gr (Fl₀.b (HodgeCpt.rootIdx D r).1) (HodgeCpt.rootIdx D r).2)
    (n := HodgeCpt.rootSgn D r) hg₀ hq₀
  have e₁ := tens_unit_eq hs₀ (HodgeCpt.rootSgn D r)
  obtain ⟨u₀, hu₀, hu₀', hgu⟩ := exists_unit_of_span_eq (regAt 𝔐₀.ξ q₀) hg₀ (hq₀.symm.trans e₁)
  have hs : ((𝔐.V (HodgeCpt.rootIdx D r).1).gr (Fl.b (HodgeCpt.rootIdx D r).1) (HodgeCpt.rootIdx D r).2).IsGenAt q
      (i s₀) := hgen q (fun p hp => not_inFibre 𝔐.ξ z hz hp) _ _ s₀ hs₀
  have e₂ := tens_unit_eq hs (HodgeCpt.rootSgn D r)
  obtain ⟨v, hv, hv', hgv⟩ := exists_unit_of_span_eq (regAt 𝔐.ξ q) (zpow_ne_zero _ hs.1) (e₂.symm.trans hq)
  have hfe : i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ a₀ k) * e₀) / ((∏ k, y ⟨k, cc k⟩ ^ a k) * e) = i u₀ * v := by
    rw [hgu, map_mul, map_zpow₀, hgv, ← _root_.mul_assoc (i u₀) v]
    exact mul_div_cancel_right₀ _ hg
  have hf : i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ a₀ k) * e₀) / ((∏ k, y ⟨k, cc k⟩ ^ a k) * e) ≠ 0 :=
    div_ne_zero ((map_ne_zero i).2 hg₀) hg
  refine exists_value_of_unit 𝔐.tie.gen z hz hf ?_ ?_
  · rw [hfe]
    exact mul_mem (hreg q _ hu₀) hv
  · rw [hfe, mul_inv, ← map_inv₀]
    exact mul_mem (hreg q _ hu₀') hv'

end GlobalTheory.CompanionTheory.Ar.ChgUnit
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)


theorem _root_.GlobalTheory.T.flat_on_log_resolution_corr : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P Jd : Ideal (MRing J)) (D : ℕ) (R : AnLogRes P Jd D) (Ψ : Type) (N : ℕ) (T : Ψ × Fin N → HermLine J), (∀ r, IsFlatOn R (T r)) → ∀ a, IsFlatOn R (corr T a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Chg.isFlatOn_corr | exact GlobalTheory.CompanionTheory.Ar.Chg.isFlatOn_corr | (intros; apply GlobalTheory.CompanionTheory.Ar.Chg.isFlatOn_corr <;> assumption)
end
