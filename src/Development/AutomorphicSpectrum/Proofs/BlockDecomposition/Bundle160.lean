module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle005
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.CechDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedCoverVanishingInduction
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DpZeroRight
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace GlobalTheory.CompanionTheory.GeoVanish

open HomogeneousLocalization MvPolynomial

variable {K : Type} [Field K] {N : ℕ}

theorem away_mk_zero {x : MvPolynomial (Fin (N + 1)) K} (hx : x ∈ grK K N 1) (n : ℕ)
    (h0 : (0 : MvPolynomial (Fin (N + 1)) K) ∈ grK K N (n • 1)) :
    Away.mk (grK K N) hx n 0 h0 = 0 := by
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, HomogeneousLocalization.val_zero, Localization.mk_zero]

theorem away_mk_add {x : MvPolynomial (Fin (N + 1)) K} (hx : x ∈ grK K N 1) (n : ℕ)
    {a b : MvPolynomial (Fin (N + 1)) K} (ha : a ∈ grK K N (n • 1)) (hb : b ∈ grK K N (n • 1))
    (hab : a + b ∈ grK K N (n • 1)) :
    Away.mk (grK K N) hx n (a + b) hab = Away.mk (grK K N) hx n a ha + Away.mk (grK K N) hx n b hb := by
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, HomogeneousLocalization.val_add, Localization.add_mk_self]

theorem away_mk_mul {x : MvPolynomial (Fin (N + 1)) K} (hx : x ∈ grK K N 1) {k m n : ℕ} (hn : k + m = n)
    {a b : MvPolynomial (Fin (N + 1)) K} (ha : a ∈ grK K N (k • 1)) (hb : b ∈ grK K N (m • 1))
    (hab : a * b ∈ grK K N (n • 1)) :
    Away.mk (grK K N) hx n (a * b) hab = Away.mk (grK K N) hx k a ha * Away.mk (grK K N) hx m b hb := by
  subst hn
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, HomogeneousLocalization.val_mul, Localization.mk_mul]
  congr 1
  exact Subtype.ext (pow_add x k m)

theorem chart_zero {R : Type} [CommRing R] {x : MvPolynomial (Fin (N + 1)) K} (hx : x ∈ grK K N 1)
    (φ : Away (grK K N) x →+* R) (S : Set (MvPolynomial (Fin (N + 1)) K))
    (hS : ∀ f ∈ S, ∃ (d : ℕ) (hf : f ∈ grK K N (d • 1)), φ (Away.mk (grK K N) hx d f hf) = 0)
    {p : MvPolynomial (Fin (N + 1)) K} (hp : p ∈ Ideal.span S) :
    ∀ (n : ℕ) (f : MvPolynomial (Fin (N + 1)) K) (hf : f ∈ grK K N (n • 1)),
      f = (DirectSum.decompose (grK K N) p n : MvPolynomial (Fin (N + 1)) K) →
        φ (Away.mk (grK K N) hx n f hf) = 0 := by
  have hmem : ∀ (q : MvPolynomial (Fin (N + 1)) K) (n : ℕ),
      (DirectSum.decompose (grK K N) q n : MvPolynomial (Fin (N + 1)) K) ∈ grK K N (n • 1) := by
    intro q n
    simpa using (DirectSum.decompose (grK K N) q n).2
  have hzero : ∀ (n : ℕ) (f : MvPolynomial (Fin (N + 1)) K) (hf : f ∈ grK K N (n • 1)),
      f = (DirectSum.decompose (grK K N) (0 : MvPolynomial (Fin (N + 1)) K) n : MvPolynomial (Fin (N + 1)) K) →
        φ (Away.mk (grK K N) hx n f hf) = 0 := by
    intro n f hf h
    have h0 : f = 0 := by simpa using h
    subst h0
    rw [away_mk_zero, map_zero]
  have hadd : ∀ (p q : MvPolynomial (Fin (N + 1)) K),
      (∀ (n : ℕ) (f : MvPolynomial (Fin (N + 1)) K) (hf : f ∈ grK K N (n • 1)),
        f = (DirectSum.decompose (grK K N) p n : MvPolynomial (Fin (N + 1)) K) →
          φ (Away.mk (grK K N) hx n f hf) = 0) →
      (∀ (n : ℕ) (f : MvPolynomial (Fin (N + 1)) K) (hf : f ∈ grK K N (n • 1)),
        f = (DirectSum.decompose (grK K N) q n : MvPolynomial (Fin (N + 1)) K) →
          φ (Away.mk (grK K N) hx n f hf) = 0) →
      ∀ (n : ℕ) (f : MvPolynomial (Fin (N + 1)) K) (hf : f ∈ grK K N (n • 1)),
        f = (DirectSum.decompose (grK K N) (p + q) n : MvPolynomial (Fin (N + 1)) K) →
          φ (Away.mk (grK K N) hx n f hf) = 0 := by
    intro p q ihp ihq n f hf h
    have h' : f = (DirectSum.decompose (grK K N) p n : MvPolynomial (Fin (N + 1)) K) +
        (DirectSum.decompose (grK K N) q n : MvPolynomial (Fin (N + 1)) K) := by
      rw [h, DirectSum.decompose_add, DirectSum.add_apply, AddMemClass.coe_add]
    subst h'
    rw [away_mk_add hx n (hmem p n) (hmem q n), map_add (f := _), ihp n _ _ rfl, ihq n _ _ rfl, add_zero]
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨d, hd, h0⟩ := hS p hp
    intro n f hf h
    have hd' : p ∈ grK K N d := by simpa using hd
    by_cases hnd : n = d
    · subst hnd
      have : f = p := h.trans (DirectSum.decompose_of_mem_same _ hd')
      subst this
      exact h0
    · have h1 : f = 0 := h.trans (DirectSum.decompose_of_mem_ne _ hd' (Ne.symm hnd))
      subst h1
      rw [away_mk_zero, map_zero]
  | zero => exact hzero
  | add p q _ _ ihp ihq => exact hadd p q ihp ihq
  | smul a p _ ih =>
    induction a using DirectSum.Decomposition.inductionOn (grK K N) with
    | zero => simpa using hzero
    | @homogeneous k m =>
      intro n f hf h
      rw [smul_eq_mul] at h
      by_cases hk : k ≤ n
      · rw [DirectSum.coe_decompose_mul_of_left_mem_of_le _ m.2 hk] at h
        subst h
        have hm1 : (m : MvPolynomial (Fin (N + 1)) K) ∈ grK K N (k • 1) := by simpa using m.2
        rw [away_mk_mul hx (by omega : k + (n - k) = n) hm1 (hmem p (n - k)), map_mul,
          ih (n - k) _ _ rfl, mul_zero]
      · rw [DirectSum.coe_decompose_mul_of_left_mem_of_not_le _ m.2 hk] at h
        subst h
        rw [away_mk_zero, map_zero]
    | add a b iha ihb =>
      rw [add_smul]
      exact hadd _ _ iha ihb

theorem evV_res {X : Scheme.{0}} (i : X ⟶ PSpace K N) (g : MvPolynomial (Fin (N + 1)) K) {V W : X.Opens}
    (hV : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) g) (h : W ≤ V) (y : Away (grK K N) g) :
    resO h (evV i g V hV y) = evV i g W (h.trans hV) y := by
  have := Scheme.Hom.appLE_map i hV (homOfLE h).op
  simp only [evV]
  exact congr($(this).hom ((Proj.awayToSection (grK K N) g).hom y))

theorem evV_awayMap {X : Scheme.{0}} (i : X ⟶ PSpace K N) {a b c : MvPolynomial (Fin (N + 1)) K} {m : ℕ}
    (hb : b ∈ grK K N m) (hc : c = a * b) {W : X.Opens} (hW : W ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) c)
    (hW' : W ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) a) (y : Away (grK K N) a) :
    evV i c W hW (awayMap (grK K N) hb hc y) = evV i a W hW' y := by
  have h1 := Proj.awayMap_awayToSection (grK K N) hb hc
  have h2 := Scheme.Hom.map_appLE i hW (homOfLE (Proj.basicOpen_mono (grK K N) a c ⟨_, hc⟩)).op
  have h3 : (Proj.awayToSection (grK K N) c).hom (awayMap (grK K N) hb hc y) =
      ((PSpace K N).presheaf.map (homOfLE (Proj.basicOpen_mono (grK K N) a c ⟨_, hc⟩)).op).hom
        ((Proj.awayToSection (grK K N) a).hom y) := congr($(h1).hom y)
  simp only [evV, RingHom.comp_apply]
  rw [h3]
  exact congr($(h2).hom ((Proj.awayToSection (grK K N) a).hom y))

theorem exists_chart (p : PSpace K N) : ∃ j, p ∈ Proj.basicOpen (grK K N) (X j : MvPolynomial (Fin (N + 1)) K) := by
  have h : ⨆ j, Proj.basicOpen (grK K N) (X j : MvPolynomial (Fin (N + 1)) K) = ⊤ := by
    refine Proj.iSup_basicOpen_eq_top _ _ ((HomogeneousIdeal.toIdeal_irrelevant_le _).2 fun n hn f hf => ?_)
    change f ∈ Ideal.span _
    rw [← Set.image_univ, mem_ideal_span_X_image]
    intro m hm
    by_contra! H
    obtain rfl : m = 0 := Finsupp.ext fun i => H i (Set.mem_univ i)
    have hf' : f ∈ grK K N n := hf
    have := ((mem_homogeneousSubmodule _ _).1 hf') (mem_support_iff.1 hm)
    simp only [map_zero] at this
    omega
  exact TopologicalSpace.Opens.mem_iSup.1 (h.ge (Set.mem_univ p))

theorem ratio_eq {g x f : MvPolynomial (Fin (N + 1)) K} {e s : ℕ} (hg : g ∈ grK K N e) (hx : x ∈ grK K N 1)
    (hf : f ∈ grK K N (s • e)) (hf1 : f ∈ grK K N ((s • e) • 1)) (hxs : x ^ (s • e) ∈ grK K N (s • e)) :
    awayMap (grK K N) hx (rfl : g * x = g * x) (Away.mk (grK K N) hg s f hf) =
      awayMap (grK K N) hx (rfl : g * x = g * x) (Away.mk (grK K N) hg s (x ^ (s • e)) hxs) *
        awayMap (grK K N) hg (mul_comm g x) (Away.mk (grK K N) hx (s • e) f hf1) := by
  apply HomogeneousLocalization.val_injective
  simp only [awayMap_mk, Away.val_mk, HomogeneousLocalization.val_mul, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul, smul_eq_mul]
  ring

end GlobalTheory.CompanionTheory.GeoVanish


open GlobalTheory.CompanionTheory.GeoVanish in
theorem GlobalTheory.CompanionTheory.GeoVanish.homIdeal_vanish : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N), ∀ {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ} (he : 0 < e) (hg : g ∈ grK K N e) {s : ℕ} {f : MvPolynomial (Fin (N + 1)) K} (hf : f ∈ grK K N (s • e)), f ∈ homIdeal i → ∀ (V : X.Opens) (hV : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) g), evV i g V hV (HomogeneousLocalization.Away.mk (grK K N) hg s f hf) = 0 := by
  intro K _ X N i g e he hg s f hf hfI V hV
  have hf1 : f ∈ grK K N ((s • e) • 1) := by simpa using hf
  have key : ∀ j : Fin (N + 1), evV i (MvPolynomial.X j) (i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j)) le_rfl
      (HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) (s • e) f hf1) = 0 := by
    intro j
    refine chart_zero (xv_mem K N j) (evV i (MvPolynomial.X j) _ le_rfl) _ ?_ hfI (s • e) f hf1
      (DirectSum.decompose_of_mem_same _ hf).symm
    rintro p ⟨d, hp, h⟩
    exact ⟨d, hp, h j⟩
  refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf
    (fun j : Fin (N + 1) => V ⊓ i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j)) V
    (fun j => homOfLE inf_le_left) ?_ _ _ ?_
  · intro p hp
    obtain ⟨j, hj⟩ := exists_chart (i p)
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨j, ?_⟩
    exact And.intro hp hj
  · intro j
    set x : MvPolynomial (Fin (N + 1)) K := MvPolynomial.X j with hxdef
    have hx : x ∈ grK K N 1 := xv_mem K N j
    set W := V ⊓ i ⁻¹ᵁ Proj.basicOpen (grK K N) x with hWdef
    have hWg : W ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) g := inf_le_left.trans hV
    have hWx : W ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) x := inf_le_right
    have hWgx : W ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (g * x) := by
      rw [Proj.basicOpen_mul]
      exact fun p hp => And.intro (hWg hp) (hWx hp)
    have hxs : x ^ (s • e) ∈ grK K N (s • e) := by
      simpa using SetLike.pow_mem_graded (s • e) hx
    have h0 : evV i x W hWx (HomogeneousLocalization.Away.mk (grK K N) hx (s • e) f hf1) = 0 := by
      rw [← evV_res i x le_rfl hWx, key j, map_zero]
    have h1 : evV i g W hWg (HomogeneousLocalization.Away.mk (grK K N) hg s f hf) = 0 := by
      rw [← evV_awayMap i hx rfl hWgx hWg, ratio_eq hg hx hf hf1 hxs, map_mul,
        evV_awayMap i hg (mul_comm g x) hWgx hWx, h0, mul_zero]
    change resO (inf_le_left : W ≤ V) (evV i g V hV _) = resO (inf_le_left : W ≤ V) 0
    rw [map_zero, evV_res i g hV inf_le_left]
    exact h1
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace GlobalTheory.CompanionTheory.GeoTpow

open HomogeneousLocalization

variable {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ}

theorem evV_awayMap (i : X ⟶ PSpace K N) {f g x : MvPolynomial (Fin (N + 1)) K} {n : ℕ}
    (hg : g ∈ grK K N n) (hx : x = f * g) (V : X.Opens)
    (hf : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) f) (hxV : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) x)
    (a : Away (grK K N) f) :
    evV i x V hxV (awayMap (grK K N) hg hx a) = evV i f V hf a := by
  have h := congrArg (fun φ => φ.hom a) (Proj.awayMap_awayToSection (grK K N) hg hx)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  change (i.appLE _ V hxV).hom ((Proj.awayToSection (grK K N) x).hom (awayMap (grK K N) hg hx a)) = _
  rw [h]
  change ((_ ≫ i.appLE _ V hxV).hom) _ = _
  rw [Scheme.Hom.map_appLE]
  rfl

theorem prod_pow_mem {n e p : ℕ} (y : Fin n → MvPolynomial (Fin (N + 1)) K)
    (hy : ∀ k, (y k).IsHomogeneous e) (α : Fin n → ℕ) (hp : (∑ j, α j) * e = p) :
    ∏ j, y j ^ α j ∈ grK K N p := by
  have h := MvPolynomial.IsHomogeneous.prod Finset.univ (fun j => y j ^ α j) (fun j => e * α j)
    (fun j _ => (hy j).pow (α j))
  rw [MvPolynomial.mem_homogeneousSubmodule, ← hp, mul_comm, Finset.mul_sum]
  exact h

theorem prod_mk_pow {n e c : ℕ} {g : MvPolynomial (Fin (N + 1)) K} (hg : g ∈ grK K N e)
    (y : Fin n → MvPolynomial (Fin (N + 1)) K) (h1 : ∀ j, y j ∈ grK K N (1 • e)) (α : Fin n → ℕ)
    (hc : ∑ j, α j = c) (hm : ∏ j, y j ^ α j ∈ grK K N (c • e)) :
    ∏ j, Away.mk (grK K N) hg 1 (y j) (h1 j) ^ α j = Away.mk (grK K N) hg c (∏ j, y j ^ α j) hm := by
  have hpow : ∀ k : ℕ, g ^ k ∈ Submonoid.powers g := fun k => ⟨k, rfl⟩
  let v : Localization (Submonoid.powers g) := Localization.mk 1 ⟨g, 1, pow_one g⟩
  have hv : ∀ k : ℕ, v ^ k = Localization.mk 1 ⟨g ^ k, hpow k⟩ := by
    intro k
    induction k with
    | zero => simpa using Localization.mk_one.symm
    | succ k ih =>
      rw [pow_succ, ih, Localization.mk_mul]
      simp [pow_succ]
  have key : ∀ (k : ℕ) (x) (hx : x ∈ grK K N (k • e)),
      (Away.mk (grK K N) hg k x hx).val = algebraMap _ _ x * v ^ k := by
    intro k x hx
    rw [Away.val_mk, hv, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul]
    simp
  apply HomogeneousLocalization.val_injective
  rw [← HomogeneousLocalization.algebraMap_apply, map_prod]
  simp_rw [map_pow, HomogeneousLocalization.algebraMap_apply, key, pow_one, mul_pow,
    Finset.prod_mul_distrib, map_prod, map_pow, Finset.prod_pow_eq_pow_sum, hc]

theorem exists_shift {n : ℕ} (S : Finset (Fin n)) (v : Fin n → ℤ) (h : ∀ j, j ∉ S → 0 ≤ v j) :
    ∃ (r : ℕ) (α : Fin n → ℕ), ∀ j, (α j : ℤ) = v j + if j ∈ S then (r : ℤ) else 0 := by
  refine ⟨∑ j, (v j).natAbs, fun j => (v j + if j ∈ S then ((∑ j, (v j).natAbs : ℕ) : ℤ) else 0).toNat, fun j => ?_⟩
  refine Int.toNat_of_nonneg ?_
  by_cases hj : j ∈ S
  · have h1 : (v j).natAbs ≤ ∑ j, (v j).natAbs :=
      Finset.single_le_sum (f := fun j => (v j).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    simp only [hj, if_true]
    omega
  · simpa [hj] using h j hj

theorem cross_mul {c r e₁ e₂ : ℕ} {f g a : MvPolynomial (Fin (N + 1)) K}
    (hf : f ∈ grK K N e₁) (hg : g ∈ grK K N e₂) (ha : a ∈ grK K N (r • e₁)) (ha' : a ∈ grK K N (c • e₂))
    (hF : f ^ r ∈ grK K N (c • e₂)) :
    awayMap (grK K N) hg (mul_comm g f) (Away.mk (grK K N) hf r a ha) *
      awayMap (grK K N) hf (rfl : g * f = g * f) (Away.mk (grK K N) hg c (f ^ r) hF) =
    awayMap (grK K N) hf (rfl : g * f = g * f) (Away.mk (grK K N) hg c a ha') := by
  simp only [awayMap_mk]
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul]
  simp only [Away.val_mk]
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul, OneMemClass.coe_one, one_mul]
  ring

theorem core {d e : ℕ} (i : X ⟶ PSpace K N) (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K)
    (hy : ∀ k, (y k).IsHomogeneous e) (V : X.Opens) (h0 : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (y 0))
    (S : Finset (Fin (d + 1))) (hS : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (yS y S))
    (hy0 : y 0 ∈ grK K N e) (h1 : ∀ j, y j ∈ grK K N (1 • e)) (r : ℕ) (α : Fin (d + 1) → ℕ)
    (hα : ∑ j, α j = r * S.card)
    (ha : ∏ j, y j ^ α j ∈ grK K N (r • (S.card * e))) :
    evV i (yS y S) V hS (Away.mk (grK K N) (yS_mem y hy S) r _ ha) *
        ∏ j, evV i (y 0) V h0 (Away.mk (grK K N) hy0 1 (y j) (h1 j)) ^ (if j ∈ S then r else 0) =
      ∏ j, evV i (y 0) V h0 (Away.mk (grK K N) hy0 1 (y j) (h1 j)) ^ α j := by
  have hP : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (y 0 * yS y S) := by
    rw [Proj.basicOpen_mul]
    exact le_inf h0 hS
  have hβ : ∑ j, (if j ∈ S then r else 0) = r * S.card := by
    simp [Finset.sum_ite_mem, mul_comm]
  have ha' : ∏ j, y j ^ α j ∈ grK K N ((r * S.card) • e) :=
    prod_pow_mem y hy α (by rw [hα, smul_eq_mul])
  have hF' : ∏ j, y j ^ (if j ∈ S then r else 0) ∈ grK K N ((r * S.card) • e) :=
    prod_pow_mem y hy _ (by rw [hβ, smul_eq_mul])
  have hFeq : ∏ j, y j ^ (if j ∈ S then r else 0) = yS y S ^ r := by
    simp [yS, pow_ite, Finset.prod_ite_mem, Finset.prod_pow]
  have hF : yS y S ^ r ∈ grK K N ((r * S.card) • e) := hFeq ▸ hF'
  simp_rw [← map_pow, ← map_prod]
  rw [prod_mk_pow hy0 y h1 α hα ha', prod_mk_pow hy0 y h1 _ hβ hF']
  simp only [hFeq]
  rw [← evV_awayMap i hy0 (mul_comm (y 0) (yS y S)) V hS hP,
    ← evV_awayMap i (yS_mem y hy S) rfl V h0 hP, ← evV_awayMap i (yS_mem y hy S) rfl V h0 hP, ← map_mul,
    cross_mul (yS_mem y hy S) hy0 ha ha' hF]

theorem tpow_mem_range {K : Type} [Field K] {X : Scheme.{0}} {N d e : ℕ} (i : X ⟶ PSpace K N)
    (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) {V : X.Opens}
    (hV : V ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)) : 0 < e →
    ∀ (S : Finset (Fin (d + 1))) (hS : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (yS y S))
      (ht : ∀ k, IsUnit (tV i y hy V hV k)), ∀ m ∈ expS S,
      tpow (fun k => (ht k).unit) m ∈ Set.range (evV i (yS y S) V hS) := by
  intro _ S hS ht m hm
  have h0 : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (y 0) :=
    hV.trans (iInf_le (fun k => i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)) 0)
  have hy0 : y 0 ∈ grK K N e := (MvPolynomial.mem_homogeneousSubmodule e (y 0)).2 (hy 0)
  have h1 : ∀ j, y j ∈ grK K N (1 • e) := fun j => by
    simpa using (MvPolynomial.mem_homogeneousSubmodule e (y j)).2 (hy j)
  let n : Fin (d + 1) → ℤ := Fin.cons (-∑ k, m k) m
  have hn0 : n 0 = -∑ k, m k := rfl
  have hns : ∀ k : Fin d, n k.succ = m k := fun _ => rfl
  have hn : ∀ j, j ∉ S → 0 ≤ n j := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · intro hj
      have := hm.2 hj
      rw [hn0]
      omega
    · intro hj
      rw [hns]
      exact hm.1 k hj
  obtain ⟨r, α, hα⟩ := exists_shift S n hn
  have hsum : ∑ j, n j = 0 := by
    rw [Fin.sum_univ_succ, hn0]
    simp only [hns]
    ring
  have hαs : ∑ j, α j = r * S.card := by
    have : ((∑ j, α j : ℕ) : ℤ) = ((r * S.card : ℕ) : ℤ) := by
      push_cast
      simp_rw [hα]
      rw [Finset.sum_add_distrib, hsum]
      simp [Finset.sum_ite_mem, mul_comm]
    exact_mod_cast this
  have ha : ∏ j, y j ^ α j ∈ grK K N (r • (S.card * e)) :=
    prod_pow_mem y hy α (by rw [hαs, smul_eq_mul, mul_assoc])
  refine ⟨Away.mk (grK K N) (yS_mem y hy S) r _ ha, ?_⟩
  have hc := core i y hy V h0 S hS hy0 h1 r α hαs ha
  let T : Fin (d + 1) → (Γ(X, V))ˣ := Fin.cons 1 (fun k => (ht k).unit)
  have hT0 : T 0 = 1 := rfl
  have hTs : ∀ k : Fin d, T k.succ = (ht k).unit := fun _ => rfl
  have hT : ∀ j, evV i (y 0) V h0 (Away.mk (grK K N) hy0 1 (y j) (h1 j)) = (T j : Γ(X, V)) := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · have : Away.mk (grK K N) hy0 1 (y 0) (h1 0) = 1 := by
        apply HomogeneousLocalization.val_injective
        rw [Away.val_mk, HomogeneousLocalization.val_one]
        simpa using Localization.mk_self (⟨y 0, 1, pow_one _⟩ : Submonoid.powers (y 0))
      rw [this, map_one, hT0, Units.val_one]
    · rw [hTs, IsUnit.unit_spec]
      rfl
  simp only [hT] at hc
  have hU : ∏ k, (ht k).unit ^ m k = ∏ j, T j ^ n j := by
    rw [Fin.prod_univ_succ, hT0, one_zpow, one_mul]
    simp only [hTs, hns]
  have hA : ∏ j, T j ^ α j = (∏ j, T j ^ n j) * ∏ j, T j ^ (if j ∈ S then r else 0) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add, hα]
    split_ifs <;> simp
  have hc' : evV i (yS y S) V hS (Away.mk (grK K N) (yS_mem y hy S) r _ ha) *
      ((∏ j, T j ^ (if j ∈ S then r else 0) : (Γ(X, V))ˣ) : Γ(X, V)) =
      ((∏ j, T j ^ n j : (Γ(X, V))ˣ) : Γ(X, V)) * ((∏ j, T j ^ (if j ∈ S then r else 0) : (Γ(X, V))ˣ) : Γ(X, V)) := by
    rw [← Units.val_mul, ← hA]
    simpa [Units.coe_prod] using hc
  have := (Units.mul_left_inj _).1 hc'
  rw [this, tpow, hU]

end GlobalTheory.CompanionTheory.GeoTpow
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.graded_cover_vanishing_induction : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (Φ : PDF R C) (Fil : ℤ → IdF Φ.A),
    IsFil Φ Fil → ∀ (s n : ℕ) (W : Fin (n + 2) → ObjectProperty C), (∀ T, (∃ α, W α T) → (Fil s).S T = ⊥) →
    (∀ α ⦃T T' : C⦄, (T ⟶ T') → W α T → (∃ β, W β T') → W α T') →
    (∀ S : Finset (Fin (n + 2)), S.Nonempty → ∀ (r : ℤ) (j : ℕ), (j : ℤ) ≠ r → Subsingleton (HU (gr Fil r) (capS W S) j)) →
    (∀ S : Finset (Fin (n + 2)), S.Nonempty → ∀ (r : ℤ) (j : ℕ), (n : ℤ) + 1 < r → Subsingleton (HU (gr Fil r) (capS W S) j)) →
    ∀ (z : CH.Cn (CH.modF ((ObjectProperty.ι fun T : C => ∃ α, W α T) ⋙ Φ.A)) 2), CH.d _ 2 z = 0 → (∀ σ, z σ ∈ (Fil 1).S _) →
    ∀ (b : ∀ i, CH.Cn (CH.modF ((W i).ι ⋙ Φ.A)) 1), (∀ i σ, b i σ ∈ (Fil 1).S _) →
    (∀ i, resB Φ.A (fun T h => ⟨i, h⟩ : W i ≤ fun T : C => ∃ α, W α T) z = CH.d _ 1 (b i)) →
    (∀ h, (CH.cx _).cls (cupPowC ((ObjectProperty.ι fun T : C => ∃ α, W α T) ⋙ Φ.A) z (n + 1)) h = 0) →
    ∀ c : HU (gr Fil ((n : ℤ) + 1)) (capS W Finset.univ) (n + 1),
      Rep ((Fil ((n : ℤ) + 1)).res (capS W Finset.univ).ι) ((Fil ((n : ℤ) + 1 + 1)).res (capS W Finset.univ).ι)
        (cupListC ((capS W Finset.univ).ι ⋙ Φ.A) fun k : Fin (n + 1) =>
          resB Φ.A (capS_le_univ W k.castSucc) (b k.castSucc) - resB Φ.A (capS_le_univ W k.succ) (b k.succ)) c →
      ∃ (ω : ∀ i, HU (gr Fil ((n : ℤ) + 1)) (capS W (Finset.univ.erase i)) (n + 1))
        (f : CH.Cn (CH.modF ((capS W Finset.univ).ι ⋙ Φ.A)) n),
        (∀ σ, f σ ∈ (Fil n).S _) ∧ (∀ σ, CH.d _ n f σ ∈ (Fil ((n : ℤ) + 1)).S _) ∧
        Rep ((Fil ((n : ℤ) + 1)).res (capS W Finset.univ).ι) ((Fil ((n : ℤ) + 1 + 1)).res (capS W Finset.univ).ι)
          (CH.d _ n f) (c - ∑ i, ((resU (gr Fil ((n : ℤ) + 1)) (capS_univ_le W (Finset.univ.erase i))).pull (n + 1)) (ω i)) := by
  first | exact @GlobalTheory.CompanionTheory.ConeZig.cech_top_cup_power | exact GlobalTheory.CompanionTheory.ConeZig.cech_top_cup_power | (intros; apply GlobalTheory.CompanionTheory.ConeZig.cech_top_cup_power <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.cohomology_vanishing_of_trivial_frame : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} (E : Frame (Φ := Φ) 0) (F : C ⥤ ModuleCat.{0} R),
    Subsingleton (F.obj E.D) → ∀ n, Subsingleton (CH.H F n) := by
  intro R _ C _ Φ E F hD n
  have hInitial : Limits.IsInitial E.D := by
    refine Limits.IsInitial.ofUniqueHom (fun T => Classical.choice (E.ne T)) ?_
    intro T f
    obtain ⟨g, -, hg⟩ := E.bij f (fun _ => 0) (fun i => i.elim0)
    exact (hg _ (fun i => i.elim0)).trans (hg _ (fun i => i.elim0)).symm
  obtain ⟨-, -, hex0, hex⟩ := CrystallineSemistableComparison.P.initial F E.D hInitial
  have key : ∀ x : CH.H F n, x = 0 := by
    intro x
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx F) n).1 x
    refine ((CrystallineSemistableComparison.P.cls_surj (CH.cx F) n).2.1 a ha).2 ?_
    cases n with
    | zero =>
      obtain ⟨m, hm⟩ := hex0 a ha
      rw [one_smul] at hm
      have hm0 : m = 0 := Subsingleton.elim _ _
      rw [hm0, map_zero] at hm
      exact hm.symm
    | succ n =>
      obtain ⟨y, hy⟩ := hex n a ha
      rw [one_smul] at hy
      exact ⟨y, hy⟩
  exact ⟨fun x y => by rw [key x, key y]⟩
end
