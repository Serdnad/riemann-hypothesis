module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

theorem ialg_one {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] :
    IsMultiHomog (1 : MRing ι) 0 := by
  classical
  intro m hm k
  have : m = 0 := by
    by_contra h
    rw [mem_support_iff, coeff_one, if_neg (Ne.symm h)] at hm
    exact hm rfl
  simp [this]

theorem ialg_mul {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {f g : MRing ι} {a b : K → ℕ}
    (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m₁, h₁, m₂, h₂, rfl⟩ := Finset.mem_add.1 (support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m₁ h₁ k, hg m₂ h₂ k]

theorem ialg_rename {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {κ : K → K'}
    {v : (Σ k, ι k) → Σ k, ι' k} (hv : IsBlockMap κ v) {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) :
    IsMultiHomog (rename v f : MRing ι') (Function.extend κ a 0) := by
  classical
  intro m' hm' k'
  rw [support_rename_of_injective hv.2.1] at hm'
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hm'
  by_cases hk : ∃ k, κ k = k'
  · obtain ⟨k, rfl⟩ := hk
    rw [hv.1.extend_apply, ← hf m hm k]
    have hc : ∀ i : ι k, ∃ j : ι' (κ k), v ⟨k, i⟩ = ⟨κ k, j⟩ := by
      intro i
      have h1 := hv.2.2.1 ⟨k, i⟩
      generalize v ⟨k, i⟩ = q at h1
      obtain ⟨k₁, j⟩ := q
      obtain rfl : k₁ = κ k := h1
      exact ⟨j, rfl⟩
    choose e he using hc
    have hb : Function.Bijective e := by
      constructor
      · intro i i' h
        have : v ⟨k, i⟩ = v ⟨k, i'⟩ := by rw [he, he, h]
        exact sigma_mk_injective (β := ι) (hv.2.1 this)
      · intro j
        obtain ⟨⟨k₀, i⟩, hq⟩ := hv.2.2.2 ⟨κ k, j⟩ ⟨k, rfl⟩
        have hk : κ k₀ = κ k := by
          have := hv.2.2.1 ⟨k₀, i⟩
          rw [hq] at this
          exact this.symm
        obtain rfl := hv.1 hk
        exact ⟨i, sigma_mk_injective (β := ι') ((he i).symm.trans hq)⟩
    refine (Fintype.sum_bijective e hb _ _ fun i => ?_).symm
    rw [← he, Finsupp.mapDomain_apply_of_injective hv.2.1]
  · rw [Function.extend_apply' _ _ _ hk]
    refine Finset.sum_eq_zero fun i _ => Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨p, hp⟩
    refine hk ⟨p.1, ?_⟩
    rw [← hv.2.2.1 p, hp]

theorem i_algebra : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)), IsMultiProjPrime P → (∀ a, IsLineIso P a a 1 1) ∧ (∀ a b f g, IsLineIso P a b f g → IsLineIso P b a g f) ∧ (∀ a b c f g f' g', IsLineIso P a b f g → IsLineIso P b c f' g' → IsLineIso P a c (f * f') (g * g')) ∧ (∀ a b a' b' f g f' g', IsLineIso P a b f g → IsLineIso P a' b' f' g' → IsLineIso P (a + a') (b + b') (f * f') (g * g')) ∧ ∀ (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) (P' : Ideal (MRing ι')), IsBlockMap κ v → imageZ v P' = P → ∀ a b f g, IsLineIso P a b f g → IsLineIso P' (pullDeg κ a) (pullDeg κ b) (rename v f) (rename v g) := by
  intro K _ ι _ P hP
  have hp : P.IsPrime := hP.1
  have tens : ∀ f g f' g' : MRing ι, UnitRatio P f g → UnitRatio P f' g' → UnitRatio P (f * f') (g * g') := by
    rintro f g f' g' ⟨hf, hg, h⟩ ⟨hf', hg', h'⟩
    refine ⟨fun hh => (hp.mem_or_mem hh).elim hf hf', fun hh => (hp.mem_or_mem hh).elim hg hg',
      fun W hW hPW hr => ?_⟩
    obtain ⟨u, v, hu, hv, huv⟩ := h W hW hPW hr
    obtain ⟨u', v', hu', hv', huv'⟩ := h' W hW hPW hr
    refine ⟨u * u', v * v', fun hh => (hW.mem_or_mem hh).elim hu hu', fun hh => (hW.mem_or_mem hh).elim hv hv', ?_⟩
    have := P.add_mem (P.mul_mem_left (u' * f') huv) (P.mul_mem_left (v * g) huv')
    convert this using 1
    ring
  refine ⟨fun a => ⟨⟨0, 0, ialg_one, ialg_one, by simp⟩, ?_⟩, ?_, ?_, ?_, ?_⟩
  · have h1 : (1 : MRing ι) ∉ P := (Ideal.ne_top_iff_one P).1 hp.ne_top
    exact ⟨h1, h1, fun W hW _ _ => ⟨1, 1, (Ideal.ne_top_iff_one W).1 hW.ne_top,
      (Ideal.ne_top_iff_one W).1 hW.ne_top, by simp⟩⟩
  · rintro a b f g ⟨⟨α, γ, h1, h2, h3⟩, hf, hg, h⟩
    refine ⟨⟨γ, α, h2, h1, fun k => by linarith [h3 k]⟩, hg, hf, fun W hW hPW hr => ?_⟩
    obtain ⟨u, v, hu, hv, huv⟩ := h W hW hPW hr
    exact ⟨v, u, hv, hu, by simpa using P.neg_mem huv⟩
  · rintro a b c f g f' g' ⟨⟨α, γ, h1, h2, h3⟩, h⟩ ⟨⟨α', γ', h1', h2', h3'⟩, h'⟩
    refine ⟨⟨α + α', γ + γ', ialg_mul h1 h1', ialg_mul h2 h2', fun k => ?_⟩, tens _ _ _ _ h h'⟩
    simp only [Pi.add_apply, Nat.cast_add]
    linarith [h3 k, h3' k]
  · rintro a b a' b' f g f' g' ⟨⟨α, γ, h1, h2, h3⟩, h⟩ ⟨⟨α', γ', h1', h2', h3'⟩, h'⟩
    refine ⟨⟨α + α', γ + γ', ialg_mul h1 h1', ialg_mul h2 h2', fun k => ?_⟩, tens _ _ _ _ h h'⟩
    simp only [Pi.add_apply, Nat.cast_add]
    linarith [h3 k, h3' k]
  · rintro K' _ ι' _ κ v P' hv rfl a b f g ⟨⟨α, γ, h1, h2, h3⟩, hf, hg, h⟩
    refine ⟨⟨Function.extend κ α 0, Function.extend κ γ 0, ialg_rename hv h1, ialg_rename hv h2, fun k' => ?_⟩,
      hf, hg, fun W hW hPW hr => ?_⟩
    · unfold pullDeg
      by_cases hk : ∃ k, κ k = k'
      · obtain ⟨k, rfl⟩ := hk
        simp only [hv.1.extend_apply]
        exact h3 k
      · simp only [Function.extend_apply' _ _ _ hk]
        simp
    · have hr' : IsRelevant (imageZ v W) := by
        intro k
        obtain ⟨i, hi⟩ := hr (κ k)
        obtain ⟨⟨k₀, j⟩, hq⟩ := hv.2.2.2 ⟨κ k, i⟩ ⟨k, rfl⟩
        have hk : κ k₀ = κ k := by
          have := hv.2.2.1 ⟨k₀, j⟩
          rw [hq] at this
          exact this.symm
        obtain rfl := hv.1 hk
        refine ⟨j, fun hh => hi ?_⟩
        have : rename v (X ⟨k₀, j⟩ : MRing ι) ∈ W := hh
        rwa [rename_X, hq] at this
      obtain ⟨u, w, hu, hw, huw⟩ := h (imageZ v W) (Ideal.comap_isPrime _ W) (Ideal.comap_mono hPW) hr'
      refine ⟨rename v u, rename v w, hu, hw, ?_⟩
      have : rename v (u * f - w * g) ∈ P' := huw
      simpa using this

end PositivityTheory.UnitarySelfGeneration
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

theorem j_pull : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k), IsBlockMap κ v → (∀ A : HermLine ι, ∃! A' : HermLine ι', IsPullHerm κ v A A') ∧ (∀ (A : HermLine ι) (A' : HermLine ι'), IsPullHerm κ v A A' → IsSmoothHerm A → IsSmoothHerm A') ∧ (∀ (P' : Ideal (MRing ι')), ∀ z ∈ mcPts P', (fun p => z (v p)) ∈ mcPts (imageZ v P')) ∧ ∀ (z : (Σ k, ι' k) → ℂ) (f : MRing ι), evC z (rename v f) = evC (fun p => z (v p)) f := by
  intro K _ ι _ K' _ ι' _ κ v hv
  obtain ⟨hκ, hvi, hv1, hv2⟩ := hv
  have hnz : ∀ z : (Σ k, ι' k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∀ k, ∃ i, z (v ⟨k, i⟩) ≠ 0 := by
    intro z hz k
    obtain ⟨i', hi'⟩ := hz (κ k)
    obtain ⟨⟨k', i⟩, hp⟩ := hv2 ⟨κ k, i'⟩ ⟨k, rfl⟩
    have h1 : κ k' = κ k := by
      have := hv1 ⟨k', i⟩
      rw [hp] at this
      exact this.symm
    obtain rfl := hκ h1
    exact ⟨i, by rwa [hp]⟩
  have hev : ∀ (z : (Σ k, ι' k) → ℂ) (f : MRing ι), evC z (rename v f) = evC (fun p => z (v p)) f := by
    intro z f
    unfold evC
    rw [map_rename, eval_rename]
    rfl
  refine ⟨fun A => ⟨⟨pullDeg κ A.a, fun z => A.h fun p => z (v p), fun z hz => A.pos _ (hnz z hz), fun c z hc => ?_⟩,
    ⟨rfl, fun _ => rfl⟩, ?_⟩, fun A A' h hA => ?_, fun P' z hz => ⟨hnz z hz.1, fun f hf => ?_⟩, hev⟩
  · have h1 := A.smul (fun k => c (κ k)) (fun p => z (v p)) fun k => hc _
    simp only [hv1]
    rw [h1]
    congr 1
    refine Finset.prod_of_injOn κ hκ.injOn (fun _ _ => Finset.mem_univ _) (fun k' _ hk' => ?_) fun k _ => ?_
    · unfold pullDeg
      rw [Function.extend_apply' _ _ _ (by simpa using hk')]
      simp
    · unfold pullDeg
      rw [hκ.extend_apply]
  · rintro ⟨a, h, _, _⟩ ⟨h1, h2⟩
    obtain rfl : a = pullDeg κ A.a := h1
    obtain rfl : h = fun z => A.h fun p => z (v p) := funext h2
    rfl
  · unfold IsSmoothHerm
    rw [show A'.h = A.h ∘ fun z p => z (v p) from funext h.2]
    exact ContDiffOn.comp hA (contDiffOn_pi.mpr fun p => (contDiff_apply ℝ (fun _ => ℂ) (v p)).contDiffOn) fun z hz => hnz z hz
  · exact (hev z f).symm.trans (hz.2 _ hf)

end PositivityTheory.UnitarySelfGeneration
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration.Isomove

noncomputable section Move

variable {X X' : Scheme.{0}} {G : Over X} {G' : Over X'} [GrpObj G] [GrpObj G'] {f : X' ⟶ X} {φ : G'.left ⟶ G.left}

theorem mv_one_left {Y : Scheme.{0}} (y : Y ⟶ X) : (1 : Over.mk y ⟶ G).left = y ≫ (η[G]).left := by
  rw [Hom.one_def]
  simp

omit [GrpObj G] [GrpObj G'] in
theorem mv_push (w : φ ≫ G.hom = G'.hom ≫ f) {Y : Scheme.{0}} {y' : Y ⟶ X'} {y : Y ⟶ X} (hy : y' ≫ f = y)
    (a' : Over.mk y' ⟶ G') : ∃ a : Over.mk y ⟶ G, a'.left ≫ φ = a.left := by
  refine ⟨Over.homMk (a'.left ≫ φ) ?_, rfl⟩
  have hw := Over.w a'
  simp only [Over.mk_hom] at hw ⊢
  rw [Category.assoc, w, ← Category.assoc, hw, hy]

theorem mv_mul (h : IsGrpPullback G' G f φ) {Y : Scheme.{0}} {y' : Y ⟶ X'} {y : Y ⟶ X} (hy : y' ≫ f = y)
    {a' b' : Over.mk y' ⟶ G'} {a b : Over.mk y ⟶ G} (ha : a'.left ≫ φ = a.left) (hb : b'.left ≫ φ = b.left) :
    (a' * b').left ≫ φ = (a * b).left := by
  subst hy
  exact (h.2 (Over.mk y') a' b' a b ha.symm hb.symm).symm

private theorem mv_one_lemma (h : IsGrpPullback G' G f φ) {Y : Scheme.{0}} {y' : Y ⟶ X'} {y : Y ⟶ X}
    (hy : y' ≫ f = y) (e : Over.mk y ⟶ G) (he : (1 : Over.mk y' ⟶ G').left ≫ φ = e.left) : e = 1 := by
  have hm := mv_mul h hy he he
  rw [show (1 : Over.mk y' ⟶ G') * 1 = 1 from mul_one _, he] at hm
  have hee : e * e = e := (Over.OverMorphism.ext hm).symm
  simpa using congrArg (· * e⁻¹) hee

theorem mv_one (h : IsGrpPullback G' G f φ) {Y : Scheme.{0}} {y' : Y ⟶ X'} {y : Y ⟶ X} (hy : y' ≫ f = y) :
    (1 : Over.mk y' ⟶ G').left ≫ φ = (1 : Over.mk y ⟶ G).left := by
  obtain ⟨e, he⟩ := mv_push (φ := φ) h.1.w hy (1 : Over.mk y' ⟶ G')
  rw [he, mv_one_lemma h hy e he]

theorem mv_pow (h : IsGrpPullback G' G f φ) {Y : Scheme.{0}} {y' : Y ⟶ X'} {y : Y ⟶ X} (hy : y' ≫ f = y)
    {a' : Over.mk y' ⟶ G'} {a : Over.mk y ⟶ G} (ha : a'.left ≫ φ = a.left) {n : ℕ} (hn : a' ^ n = 1) :
    a ^ n = 1 := by
  have key : ∀ k : ℕ, (a' ^ k).left ≫ φ = (a ^ k).left := by
    intro k
    induction k with
    | zero => simpa only [pow_zero] using mv_one h hy
    | succ k ih =>
      rw [pow_succ, pow_succ]
      exact mv_mul h hy ih ha
  apply Over.OverMorphism.ext
  rw [← key n, hn, mv_one h hy]

theorem mv_eta (h : IsGrpPullback G' G f φ) : (η[G']).left ≫ φ = f ≫ (η[G]).left := by
  have := mv_one h (y' := 𝟙 X') (y := f) (Category.id_comp f)
  simpa [mv_one_left] using this

theorem mv_tan (h : IsGrpPullback G' G f φ) {R : Type} [CommRing R] {x' : Sp R ⟶ X'} {x : Sp R ⟶ X}
    (hx : x' ≫ f = x) {v' : epsAt x' ⟶ G'} {v : epsAt x ⟶ G} (hv : v'.left ≫ φ = v.left) (ht : IsTanAt G' x' v') :
    IsTanAt G x v := by
  unfold IsTanAt at ht ⊢
  rw [← hv, ← Category.assoc, ht]
  exact mv_one h hx

private theorem dualMap_lemma {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') (a : DualNumber R) :
    dualMap σ a = TrivSqZeroExt.inl (σ a.fst) + TrivSqZeroExt.inr (σ a.snd) := rfl

theorem mv_dual_alg {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') :
    spMap (dualMap σ) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap R' (DualNumber R')) ≫ spMap σ := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun r => ?_
  ext <;> simp [dualMap_lemma, TrivSqZeroExt.algebraMap_eq_inl]

theorem mv_dual_fst {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') :
    spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (dualMap σ) =
      spMap σ ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun a => ?_
  simp [dualMap_lemma]

theorem mv_dual_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (σ : R →+* R') (τ : R' →+* R'') :
    spMap (dualMap τ) ≫ spMap (dualMap σ) = spMap (dualMap (τ.comp σ)) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun a => ?_
  ext <;> simp [dualMap_lemma]

theorem mv_bc {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {x : Sp R ⟶ X} {x' : Sp R' ⟶ X}
    (hx : spMap σ ≫ x = x') (v : epsAt x ⟶ G) :
    ∃ v' : epsAt x' ⟶ G, v'.left = spMap (dualMap σ) ≫ v.left ∧ (IsTanAt G x v → IsTanAt G x' v') := by
  refine ⟨Over.homMk (spMap (dualMap σ) ≫ v.left) ?_, rfl, ?_⟩
  · have hw := Over.w v
    simp only [epsAt, Over.mk_hom] at hw ⊢
    rw [Category.assoc, hw, ← Category.assoc, mv_dual_alg, Category.assoc, hx]
  · intro ht
    unfold IsTanAt at ht ⊢
    simp only [Over.homMk_left]
    rw [← Category.assoc, mv_dual_fst, Category.assoc, ht, mv_one_left, mv_one_left, ← Category.assoc, hx]

variable {Ω : Type} [Field Ω]

theorem mv_stalk {ξ' : Sp Ω ⟶ X'} {ξ : Sp Ω ⟶ X} (hξ : ξ' ≫ f = ξ) (q' : Cpt ξ') (q : Cpt ξ) (hq : f q'.1 = q.1) :
    ∃ σ : X.presheaf.stalk q.1 →+* X'.presheaf.stalk q'.1,
      spMap σ ≫ X.fromSpecStalk q.1 = X'.fromSpecStalk q'.1 ≫ f ∧ (genMap ξ' q').comp σ = genMap ξ q ∧
      (IsIso f → Function.Bijective σ) := by
  obtain ⟨q, hqs⟩ := q
  obtain ⟨q', hq's⟩ := q'
  change f q' = q at hq
  subst hq hξ
  change ξ' (IsLocalRing.closedPoint Ω) ⤳ q' at hq's
  change f (ξ' (IsLocalRing.closedPoint Ω)) ⤳ f q' at hqs
  refine ⟨(f.stalkMap q').hom, ?_, ?_, ?_⟩
  · simp [spMap]
  · change (X'.presheaf.stalkSpecializes hq's ≫ Scheme.stalkClosedPointTo ξ').hom.comp (f.stalkMap q').hom =
      (X.presheaf.stalkSpecializes hqs ≫ Scheme.stalkClosedPointTo (ξ' ≫ f)).hom
    rw [← CommRingCat.hom_comp]
    apply congrArg CommRingCat.Hom.hom
    rw [Scheme.stalkClosedPointTo_comp]
    calc _ = (f.stalkMap q' ≫ X'.presheaf.stalkSpecializes hq's) ≫ Scheme.stalkClosedPointTo ξ' :=
          (Category.assoc _ _ _).symm
      _ = (X.presheaf.stalkSpecializes hqs ≫ f.stalkMap _) ≫ Scheme.stalkClosedPointTo ξ' := by
          congr 1
          exact (Scheme.Hom.stalkSpecializes_stalkMap f _ q' hq's).symm
      _ = _ := Category.assoc _ _ _
  · intro hf
    exact ConcreteCategory.bijective_of_isIso (f.stalkMap q')

theorem mv_regAt_le {ξ' : Sp Ω ⟶ X'} {ξ : Sp Ω ⟶ X} (hξ : ξ' ≫ f = ξ) (q' : Cpt ξ') (q : Cpt ξ)
    (hq : f q'.1 = q.1) : regAt ξ q ≤ regAt ξ' q' := by
  obtain ⟨σ, -, hσ, -⟩ := mv_stalk hξ q' q hq
  unfold regAt
  rw [← hσ]
  rintro _ ⟨r, rfl⟩
  exact ⟨σ r, rfl⟩

theorem mv_secVal_comp {B : Type} [CommRing B] {Z Z' : Scheme.{0}} (x : Sp B ⟶ Z) (ψ : Z ⟶ Z') (y : Sp B ⟶ Z')
    (hy : x ≫ ψ = y) (W : Z'.Opens) (s : Γ(Z', W)) (h : ⊤ ≤ x ⁻¹ᵁ ψ ⁻¹ᵁ W) (h' : ⊤ ≤ y ⁻¹ᵁ W) :
    secVal x (ψ ⁻¹ᵁ W) h ((ψ.app W).hom s) = secVal y W h' s := by
  subst hy
  unfold secVal
  congr 1

theorem mv_secVal_bc {B B' : Type} [CommRing B] [CommRing B'] (σ : B →+* B') {Z : Scheme.{0}} (x : Sp B ⟶ Z)
    (y : Sp B' ⟶ Z) (hy : spMap σ ≫ x = y) (W : Z.Opens) (s : Γ(Z, W)) (h : ⊤ ≤ x ⁻¹ᵁ W) (h' : ⊤ ≤ y ⁻¹ᵁ W) :
    secVal y W h' s = σ (secVal x W h s) := by
  subst hy
  have key : Scheme.Hom.appLE (spMap σ ≫ x) W ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of B')).hom =
      Scheme.Hom.appLE x W ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom ≫ CommRingCat.ofHom σ := by
    rw [← Scheme.ΓSpecIso_naturality, ← Category.assoc]
    congr 1
  have := congrArg (fun g => g.hom s) key
  simpa [secVal] using this

end Move

end PositivityTheory.UnitarySelfGeneration.Isomove
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem tw_sub : ∀ (O : Type) [CommRing O] (s : O ≃+* O) (L : Type) [AddCommGroup L] [Module O L] (f : L →ₗ[O] TwMod s L) (I : Ideal O), I.map (s : O →+* O) ≤ I → ∀ x ∈ I • (⊤ : Submodule O L), (show L from f x) ∈ I • (⊤ : Submodule O L) := by
  intro O _ s L _ _ f I hI x hx
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha y _
    have hsa : s a ∈ I := hI (Ideal.mem_map_of_mem (s : O →+* O) ha)
    have key : (show L from f (a • y)) = s a • (show L from f y) := f.map_smul a y
    rw [key]
    exact Submodule.smul_mem_smul hsa Submodule.mem_top
  · intro y z hy hz
    have key : (show L from f (y + z)) = (show L from f y) + (show L from f z) := f.map_add y z
    rw [key]
    exact Submodule.add_mem _ hy hz

end PositivityTheory.UnitarySelfGeneration
end
