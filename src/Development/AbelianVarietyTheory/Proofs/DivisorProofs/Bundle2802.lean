module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle120
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle121
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
namespace GlobalTheory.Mum.AdicSum


open Classical in
theorem sum_sub_sum_mem {R : Type} [CommRing R] (J : Ideal R) {X : Type} (v : X → R)
    (S T : Finset X) (hS : ∀ α ∉ S, v α ∈ J) (hT : ∀ α ∉ T, v α ∈ J) :
    ∑ α ∈ S, v α - ∑ α ∈ T, v α ∈ J := by
  rw [← Finset.sum_sdiff_sub_sum_sdiff (s₁ := T) (s₂ := S)]
  exact J.sub_mem (J.sum_mem fun α hα => hT α (Finset.mem_sdiff.1 hα).2)
    (J.sum_mem fun α hα => hS α (Finset.mem_sdiff.1 hα).2)

theorem exists_adic_sum : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (X : Type) (v : X → R), (∀ e : ℕ, {α | v α ∉ maximalIdeal R ^ (e + 1)}.Finite) →
    ∃ s : R, ∀ (e : ℕ) (S : Finset X), (∀ α ∉ S, v α ∈ maximalIdeal R ^ (e + 1)) →
      s - ∑ α ∈ S, v α ∈ maximalIdeal R ^ (e + 1) := by
  intro R _ _ _ hR X v hfin
  have hC : IsAdicComplete (maximalIdeal R) R := hR.1.2.2.2
  have hfin' : ∀ n : ℕ, {α | v α ∉ maximalIdeal R ^ n}.Finite := fun n =>
    (hfin n).subset fun α (hα : v α ∉ maximalIdeal R ^ n) (h : v α ∈ maximalIdeal R ^ (n + 1)) =>
      hα (Ideal.pow_le_pow_right (Nat.le_succ n) h)
  let F : ℕ → Finset X := fun n => (hfin' n).toFinset
  have hF : ∀ n, ∀ α ∉ F n, v α ∈ maximalIdeal R ^ n := by
    intro n α hα
    by_contra h
    exact hα ((hfin' n).mem_toFinset.2 h)
  let f : ℕ → R := fun n => ∑ α ∈ F n, v α
  have hsm : ∀ n : ℕ, maximalIdeal R ^ n • (⊤ : Submodule R R) = maximalIdeal R ^ n := fun n => by
    rw [smul_eq_mul, Ideal.mul_top]
  obtain ⟨L, hL⟩ := (hC.toIsPrecomplete).prec (f := f) (by
    intro m n hmn
    rw [SModEq.sub_mem, hsm]
    exact sum_sub_sum_mem (maximalIdeal R ^ m) v (F m) (F n) (hF m)
      fun α hα => Ideal.pow_le_pow_right hmn (hF n α hα))
  refine ⟨L, fun e S hS => ?_⟩
  have h1 : f (e + 1) - L ∈ maximalIdeal R ^ (e + 1) := by
    have := hL (e + 1)
    rwa [SModEq.sub_mem, hsm] at this
  have h2 := sum_sub_sum_mem (maximalIdeal R ^ (e + 1)) v (F (e + 1)) S (hF (e + 1)) hS
  have : L - ∑ α ∈ S, v α = (f (e + 1) - ∑ α ∈ S, v α) - (f (e + 1) - L) := by ring
  rw [this]
  exact Ideal.sub_mem _ h2 h1

end GlobalTheory.Mum.AdicSum
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem Modif.factor_gp (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (L : Type) [Field L] (ρ : R →+* L)
    (y : Sp L ⟶ M.S) (hρ : Function.Injective ρ) (hy : y ≫ M.π = spMap ρ) :
    ∃ ga : FractionRing R →+* L, (∀ r, ga (algebraMap R _ r) = ρ r) ∧ y = spMap ga ≫ M.gp := by
  have hI := M.integral
  have hdom := M.dominant
  have hsub : ∀ (K : Type) [Field K] (a b : Sp K), a = b := fun K _ a b =>
    PrimeSpectrum.ext (by haveI := a.isPrime; haveI := b.isPrime; rw [Ideal.eq_bot_of_prime a.asIdeal, Ideal.eq_bot_of_prime b.asIdeal])
  let p : Sp L := IsLocalRing.closedPoint L
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := y p) (U := ⊤) trivial
  have hyV : Set.range y ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]; rintro _ ⟨z, rfl⟩; rw [hsub L z p]; exact hxV
  obtain ⟨q, hq⟩ := M.gp.denseRange.exists_mem_open V.isOpen ⟨y p, hxV⟩
  have hgV : Set.range M.gp ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]; rintro _ ⟨z, rfl⟩; rw [hsub (FractionRing R) z q]; exact hq
  haveI : Nonempty V := ⟨⟨y p, hxV⟩⟩
  haveI : IsDomain Γ(M.S, V) := IsIntegral.component_integral V
  set yV := IsOpenImmersion.lift hV.fromSpec y hyV with hyVdef
  set gV := IsOpenImmersion.lift hV.fromSpec M.gp hgV with hgVdef
  have hyf : yV ≫ hV.fromSpec = y := IsOpenImmersion.lift_fac _ _ _
  have hgf : gV ≫ hV.fromSpec = M.gp := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨by', hby⟩ := Spec.map_surjective yV
  obtain ⟨bg, hbg⟩ := Spec.map_surjective gV
  obtain ⟨c, hc⟩ := Spec.map_surjective (hV.fromSpec ≫ M.π)
  have hcy : by'.hom.comp c.hom = ρ := by
    have e : Spec.map (c ≫ by') = Spec.map (CommRingCat.ofHom ρ) := by
      rw [Spec.map_comp, hby, hc, ← Category.assoc, hyf, hy]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  have hcg : bg.hom.comp c.hom = algebraMap R (FractionRing R) := by
    have e : Spec.map (c ≫ bg) = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) := by
      rw [Spec.map_comp, hbg, hc, ← Category.assoc, hgf, M.gp_π]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  have hdV : IsDominant gV := by
    haveI : IsDominant (gV ≫ hV.fromSpec) := by rw [hgf]; exact hdom
    exact IsDominant.of_comp_of_isOpenImmersion gV hV.fromSpec
  have hinj : Function.Injective bg.hom := by
    rw [← hbg] at hdV
    have h := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical bg.hom).1 hdV.denseRange
    rw [nilradical_eq_zero] at h
    exact (RingHom.injective_iff_ker_eq_bot _).2 (le_bot_iff.1 h)
  let ga : FractionRing R →+* L := IsFractionRing.lift hρ
  have hga : ∀ r, ga (algebraMap R _ r) = ρ r := IsFractionRing.lift_algebraMap hρ
  have key : ∀ b, by'.hom b = ga (bg.hom b) := by
    intro b
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) (bg.hom b)
    have hs0 : ρ s ≠ 0 := (map_ne_zero_iff ρ hρ).2 (nonZeroDivisors.ne_zero s.2)
    have hcs : bg.hom (c.hom s) = algebraMap R (FractionRing R) s := RingHom.congr_fun hcg s
    have hcr : bg.hom (c.hom r) = algebraMap R (FractionRing R) r := RingHom.congr_fun hcg r
    have h1 : c.hom s * b = c.hom r := hinj (by
      rw [map_mul, hcs, hcr, ← hrs]; exact IsLocalization.mk'_spec' (FractionRing R) r s)
    have h2 := congrArg by'.hom h1
    have hys : by'.hom (c.hom s) = ρ s := RingHom.congr_fun hcy s
    have hyr : by'.hom (c.hom r) = ρ r := RingHom.congr_fun hcy r
    rw [map_mul, hys, hyr] at h2
    rw [← hrs, IsFractionRing.lift_mk', eq_div_iff hs0, mul_comm]
    exact h2
  refine ⟨ga, hga, ?_⟩
  have e : by' = bg ≫ CommRingCat.ofHom ga := by ext b; exact key b
  rw [← hyf, ← hby, e, Spec.map_comp, Category.assoc, hbg, hgf]

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_finite_affine_chart_cover : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S), QuasiCompact G.hom → ∀ (L : LB G.left), L.IsLB → ∃ (n : ℕ) (j : Fin n → L.ι) (W : Fin n → G.left.Opens) (U : Fin n → M.S.Opens), (⨆ b, W b = ⊤) ∧ (∀ b, W b ≤ L.U (j b)) ∧ (∀ b, W b ≤ G.hom ⁻¹ᵁ U b) ∧ (∀ b, IsAffineOpen (W b)) ∧ (∀ b, IsAffineOpen (U b)) := by
  intro R _ _ M G hG L hL
  haveI := M.proper
  haveI : CompactSpace M.S := QuasiCompact.compactSpace_of_compactSpace M.π
  haveI : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have hx : ∀ x : G.left, ∃ (j : L.ι) (W : G.left.Opens) (U : M.S.Opens),
      x ∈ W ∧ W ≤ L.U j ∧ W ≤ G.hom ⁻¹ᵁ U ∧ IsAffineOpen W ∧ IsAffineOpen U := by
    intro x
    have hxt : x ∈ (⊤ : G.left.Opens) := trivial
    rw [← hL.cover] at hxt
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hxt
    obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 M.S.isBasis_affineOpens)
      (show G.hom x ∈ (⊤ : M.S.Opens) from trivial)
    obtain ⟨W, hW, hxW, hWle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 G.left.isBasis_affineOpens)
      (show x ∈ L.U j ⊓ G.hom ⁻¹ᵁ U from ⟨hj, hxU⟩)
    exact ⟨j, W, U, hxW, hWle.trans inf_le_left, hWle.trans inf_le_right, hW, hU⟩
  choose j W U hxW hWj hWU hWa hUa using hx
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (W x : Set G.left)) (fun x => (W x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxW x⟩)
  let e := t.equivFin
  refine ⟨t.card, fun b => j (e.symm b), fun b => W (e.symm b), fun b => U (e.symm b), ?_,
    fun b => hWj _, fun b => hWU _, fun b => hWa _, fun b => hUa _⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨e ⟨y, hy⟩, by simpa using hxy⟩

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_fractionRing_map_comp_eq {R W B : Type} [CommRing R] [IsDomain R] [CommRing W] [IsDomain W] [CommRing B]
    (φ : R →+* W) (hφ : Function.Injective φ) (c : R →+* B) (a : B →+* FractionRing R) (b : B →+* FractionRing W)
    (ha : Function.Injective a) (hac : a.comp c = algebraMap R (FractionRing R))
    (hbc : b.comp c = (algebraMap W (FractionRing W)).comp φ) :
    ∃ ψ : FractionRing R →+* FractionRing W,
      ψ.comp (algebraMap R (FractionRing R)) = (algebraMap W (FractionRing W)).comp φ ∧ ψ.comp a = b := by
  have hinj : Function.Injective ((algebraMap W (FractionRing W)).comp φ) :=
    (IsFractionRing.injective W (FractionRing W)).comp hφ
  refine ⟨IsFractionRing.lift hinj, ?_, ?_⟩
  · ext r
    simp only [RingHom.comp_apply, IsFractionRing.lift_algebraMap]
  · ext x
    obtain ⟨r, r', hr', h⟩ := IsFractionRing.div_surjective (A := R) (a x)
    have h0 : algebraMap R (FractionRing R) r' ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hr'
    have hac' : ∀ y, a (c y) = algebraMap R (FractionRing R) y := fun y => RingHom.congr_fun hac y
    have hbc' : ∀ y, b (c y) = ((algebraMap W (FractionRing W)).comp φ) y := fun y => RingHom.congr_fun hbc y
    have h1 : x * c r' = c r := by
      apply ha
      rw [map_mul, hac', hac', ← h, div_mul_cancel₀ _ h0]
    have h2 : ((algebraMap W (FractionRing W)).comp φ) r' ≠ 0 := by
      intro h3
      exact nonZeroDivisors.ne_zero hr' (hinj (h3.trans (map_zero _).symm))
    rw [RingHom.comp_apply, ← h, map_div₀, IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap,
      div_eq_iff h2, ← hbc', ← hbc', ← map_mul, h1]

theorem Modif.exists_generic_factor : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (W : Type) [CommRing W] [IsDomain W] (φ : R →+* W), Function.Injective φ → ∀ ξ : Sp W ⟶ M.S, ξ ≫ M.π = spMap φ → ∃ ψ : FractionRing R →+* FractionRing W, ψ.comp (algebraMap R (FractionRing R)) = (algebraMap W (FractionRing W)).comp φ ∧ spMap ψ ≫ M.gp = jK W ≫ ξ := by
  intro R _ _ M W _ _ φ hφ ξ hξ
  haveI := M.integral
  haveI := M.dominant
  let s : M.S := (jK W ≫ ξ) (IsLocalRing.closedPoint (FractionRing W))
  obtain ⟨B, f, hf, hs, -⟩ := M.S.exists_affine_mem_range_and_range_subset (x := s) (U := ⊤) trivial
  have hb : Set.range (jK W ≫ ξ) ⊆ Set.range f := by
    rintro _ ⟨y, rfl⟩
    have : y = IsLocalRing.closedPoint (FractionRing W) := Subsingleton.elim (α := PrimeSpectrum (FractionRing W)) _ _
    rw [this]; exact hs
  have ha : Set.range M.gp ⊆ Set.range f := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := M.gp.denseRange.exists_mem_open f.isOpenEmbedding.isOpen_range ⟨s, hs⟩
    have : y = z := Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _
    rw [this]; exact hz
  obtain ⟨a, ha'⟩ := Spec.map_surjective (IsOpenImmersion.lift f M.gp ha)
  obtain ⟨b, hb'⟩ := Spec.map_surjective (IsOpenImmersion.lift f (jK W ≫ ξ) hb)
  obtain ⟨c, hc'⟩ := Spec.map_surjective (f ≫ M.π)
  have e1 : Spec.map a ≫ f = M.gp := by rw [ha', IsOpenImmersion.lift_fac]
  have e2 : Spec.map b ≫ f = jK W ≫ ξ := by rw [hb', IsOpenImmersion.lift_fac]
  have hac : c ≫ a = CommRingCat.ofHom (algebraMap R (FractionRing R)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hc', ← Category.assoc, e1, M.gp_π]
  have hbc : c ≫ b = CommRingCat.ofHom φ ≫ CommRingCat.ofHom (algebraMap W (FractionRing W)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hc', ← Category.assoc, e2, Category.assoc, hξ, Spec.map_comp]
  have hred : IsReduced (Spec B) := isReduced_of_isOpenImmersion f
  have hred' : _root_.IsReduced B := (affine_isReduced_iff B).1 hred
  have hdom : IsDominant (Spec.map a) := by
    haveI : IsDominant (Spec.map a ≫ f) := e1 ▸ M.dominant
    exact IsDominant.of_comp_of_isOpenImmersion _ f
  have hainj : Function.Injective a.hom := by
    have := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical a.hom).1 hdom.1
    rw [nilradical_eq_zero] at this
    exact (RingHom.injective_iff_ker_eq_bot _).2 (le_bot_iff.1 this)
  obtain ⟨ψ, h1, h2⟩ := exists_fractionRing_map_comp_eq φ hφ c.hom a.hom b.hom hainj
    (congrArg CommRingCat.Hom.hom hac) (congrArg CommRingCat.Hom.hom hbc)
  refine ⟨ψ, h1, ?_⟩
  have h3 : a ≫ CommRingCat.ofHom ψ = b := by
    ext1; exact h2
  rw [← e1, ← e2, ← h3, Spec.map_comp, Category.assoc]

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem exists_odd_prime_isUnit_of_base :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∃ n : ℕ, n.Prime ∧ Odd n ∧ IsUnit (n : R) := by
  intro R _ _ _ _
  by_cases h3 : IsUnit ((3 : ℕ) : R)
  · exact ⟨3, Nat.prime_three, ⟨1, rfl⟩, h3⟩
  by_cases h5 : IsUnit ((5 : ℕ) : R)
  · exact ⟨5, by norm_num, ⟨2, rfl⟩, h5⟩
  exfalso
  have m3 : ((3 : ℕ) : R) ∈ maximalIdeal R := (mem_maximalIdeal _).2 h3
  have m5 : ((5 : ℕ) : R) ∈ maximalIdeal R := (mem_maximalIdeal _).2 h5
  have m2 : ((5 : ℕ) : R) - ((3 : ℕ) : R) ∈ maximalIdeal R := Ideal.sub_mem _ m5 m3
  have m1 : ((3 : ℕ) : R) - (((5 : ℕ) : R) - ((3 : ℕ) : R)) ∈ maximalIdeal R := Ideal.sub_mem _ m3 m2
  have e : ((3 : ℕ) : R) - (((5 : ℕ) : R) - ((3 : ℕ) : R)) = 1 := by push_cast; ring
  rw [e] at m1
  exact (mem_maximalIdeal _).1 m1 isUnit_one

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem Modif.flat_gp (R : Type) [CommRing R] [IsDomain R] (M : Modif R) : Flat M.gp := by
  haveI := M.integral
  haveI := M.dominant
  refine Flat.of_stalkMap _ fun x => ?_
  have hx : M.gp.base x = genericPoint M.S := by
    have hd : DenseRange M.gp.base := M.gp.denseRange
    have hr : Set.range M.gp.base = {M.gp.base x} := by
      ext y; constructor
      · rintro ⟨z, rfl⟩; rw [Subsingleton.elim z x]; rfl
      · rintro rfl; exact ⟨x, rfl⟩
    have hg : IsGenericPoint (M.gp.base x) ⊤ := by
      rw [IsGenericPoint, ← hr]
      simpa [Set.top_eq_univ] using hd.closure_range
    exact hg.eq (genericPoint_spec M.S)
  have hF : IsField (M.S.presheaf.stalk (M.gp.base x)) := by
    rw [hx]; exact Field.toIsField _
  letI : Field (M.S.presheaf.stalk (M.gp.base x)) := hF.toField
  unfold RingHom.Flat
  exact inferInstance

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem isAffineOpen_preimage_genericBaseChange : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S) (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ W : G.left.Opens, IsAffineOpen W → IsAffineOpen (α ⁻¹ᵁ W) := by
  intro R _ _ M G Y α t h W hW
  haveI := M.proper
  haveI : M.S.IsSeparated := by
    constructor
    rw [← terminal.comp_from M.π]
    infer_instance
  haveI : IsAffineHom M.gp := by
    haveI : IsAffineHom (M.gp ≫ terminal.from M.S) := inferInstance
    exact IsAffineHom.of_comp M.gp (terminal.from M.S)
  haveI : IsAffineHom α := MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance
  exact hW.preimage α

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem cDvr_of_finExt : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R']
    [IsLocalRing R'] (ρ : R →+* R'), GlobalTheory.LN.CDvr R → FinExt ρ → GlobalTheory.LN.CDvr R' := by
  intro R R' _ _ _ _ _ _ ρ hR hE
  obtain ⟨hdvr, -, hc0⟩ := hR
  obtain ⟨⟨hnoeth, -, hic, hcomp⟩, hinj, hfin⟩ := hE
  letI : Algebra R R' := ρ.toAlgebra
  haveI : Module.Finite R R' := hfin
  haveI : Algebra.IsIntegral R R' := inferInstance
  haveI := hnoeth
  haveI := hic
  have hinj' : Function.Injective (algebraMap R R') := hinj
  haveI : Ring.DimensionLEOne R' := Ring.DimensionLEOne.of_isIntegral R R'
  haveI : IsDedekindDomain R' := { }
  have hnf : ¬ IsField R' := fun h =>
    IsDiscreteValuationRing.not_isField R (isField_of_isIntegral_of_isField hinj' h)
  have hdvr' : IsDiscreteValuationRing R' := ((IsDiscreteValuationRing.TFAE R' hnf).out 1 3).2 (inferInstance : IsDedekindDomain R')
  exact ⟨hdvr', hcomp, charZero_of_injective_algebraMap hinj'⟩

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem isLocallyNoetherian_of_smooth_over_modif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (M : Modif R) (G : Over M.S), Smooth G.hom → IsLocallyNoetherian G.left := by
  intro R _ _ _ M G hG
  haveI : IsLocallyNoetherian (Sp R) := inferInstance
  haveI := M.proper
  haveI : IsLocallyNoetherian M.S := LocallyOfFiniteType.isLocallyNoetherian M.π
  haveI := hG
  exact LocallyOfFiniteType.isLocallyNoetherian G.hom

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


attribute [local instance] GlobalTheory.TorusExt.gtGroup in
theorem GlobalTheory.Mum.lab_level_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A),
    OneTrait D.toPre A lab → ∀ k d : ℕ, 1 ≤ k → 1 ≤ d →
    ∀ (p : QkPt D.toPre (Kb R) k) (q : QkPt D.toPre (Kb R) (k * d)), q.y = d • p.y → q.g = p.g →
      lab (k * d) q = lab k p := by
  intro R _ _ _ _ D A lab hO k d hk hd p q hy hg
  obtain ⟨W, _, _, _, φ, G', _, _, D', A', U', hD, a, _, em, hW, -, -, hG', ⟨ga, hga, hcart, -⟩, hc, hind⟩ := hO
  have := hW.1
  haveI : CharZero W := hW.2.2
  have hW' : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hB := D.tau_bimult
  have hB' := D'.tau_bimult
  have hG := GlobalTheory.globalFns_holds
  have hL := GlobalTheory.firstFiveLaws
  have hN1 : 1 ≤ k * d := Nat.mul_pos hk hd
  have hem : em.toRingHom.comp (algebraMap (FractionRing R) (Kb R)) = algebraMap (FractionRing R) (Kb W) :=
    RingHom.ext em.commutes
  have hsq : spMap em.toRingHom ≫ jFK (R := R) (Kb R) = (TFK (R := W) (Kb W)).hom ≫ spMap ga := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hem]
    refine congrArg (fun f => Spec.map (CommRingCat.ofHom f))
      (IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => ?_))
    simp only [RingHom.comp_apply]
    rw [hga r]
    exact hc r
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv hcart (TFK (R := W) (Kb W)) _ hsq
  let s : Over.mk (spMap em.toRingHom ≫ jFK (R := R) (Kb R)) ⟶ TFK (R := R) (Kb R) :=
    Over.homMk (spMap em.toRingHom) rfl
  have hcomp : ∀ {m : ℕ} (r : QkPt D.toPre (Kb R) m), 1 ≤ m →
      QkToAkU U'.toUnifPre (Kb W) m (GlobalTheory.ArcPull.pullQk hD hG hc hB hB' (GlobalTheory.TorusExt.qkExt hB em.toRingHom hem r))
        (e.symm (s ≫ lab m r)) := by
    intro m r hm
    refine hind m hm r _ _ _ ((GlobalTheory.TorusExt.qkExt_iff hB _ hem _ _).2 rfl) rfl
      ((GlobalTheory.ArcPull.eq_pullQk_iff hD hG hc hB hB' _ _).1 rfl).2 ?_
    rw [← he, e.apply_symm_apply]
    rfl
  have h₁ := hcomp p hk
  have h₂ := ((GlobalTheory.LevelCompat.qkToAkU_level hL W (maximalIdeal W) hW' D' A' G' hG' U' (Kb W) k d (k * d) hk hd rfl
    (GlobalTheory.ArcPull.pullQk hD hG hc hB hB' (GlobalTheory.TorusExt.qkExt hB em.toRingHom hem p))
    (GlobalTheory.ArcPull.pullQk hD hG hc hB hB' (GlobalTheory.TorusExt.qkExt hB em.toRingHom hem q)) (e.symm (s ≫ lab (k * d) q))).1
    (by show hD.xe.symm q.y = d • hD.xe.symm p.y; rw [hy, map_nsmul])
    (by
      show GlobalTheory.ArcPull.pullGt hD hG hc (GlobalTheory.TorusExt.gtExt D.toPre em.toRingHom hem q.g) =
        GlobalTheory.ArcPull.pullGt hD hG hc (GlobalTheory.TorusExt.gtExt D.toPre em.toRingHom hem p.g)
      rw [hg])).2 (hcomp q hN1)
  obtain ⟨f, hf, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL W (maximalIdeal W) hW' D' A' G' hG' U' (Kb W) k hk
  have hx := ((hf _ _).1 h₂).trans ((hf _ _).1 h₁).symm
  have hs : s ≫ lab (k * d) q = s ≫ lab k p := e.symm.injective hx
  have : Epi (spMap em.toRingHom) := Flat.epi_of_flat_of_surjective _
  exact Over.OverMorphism.ext ((cancel_epi (spMap em.toRingHom)).1 (congrArg (fun z => z.left) hs))
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_adicSum_null_family_complete_local : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (X : Type) (v : X → R), (∀ e : ℕ, {α | v α ∉ maximalIdeal R ^ (e + 1)}.Finite) → ∃ s : R, ∀ (e : ℕ) (S : Finset X), (∀ α ∉ S, v α ∈ maximalIdeal R ^ (e + 1)) → s - ∑ α ∈ S, v α ∈ maximalIdeal R ^ (e + 1) := by
  first | exact @GlobalTheory.Mum.AdicSum.exists_adic_sum | exact GlobalTheory.Mum.AdicSum.exists_adic_sum | (intros; apply GlobalTheory.Mum.AdicSum.exists_adic_sum <;> assumption)

end
end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_factor_field_point_through_generic_point : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (L : Type) [Field L] (ρ : R →+* L) (y : Sp L ⟶ M.S), Function.Injective ρ → y ≫ M.π = spMap ρ → ∃ ga : FractionRing R →+* L, (∀ r, ga (algebraMap R _ r) = ρ r) ∧ y = spMap ga ≫ M.gp := by
  first | exact @GlobalTheory.Mum.Modif.factor_gp | exact GlobalTheory.Mum.Modif.factor_gp | (intros; apply GlobalTheory.Mum.Modif.factor_gp <;> assumption)

end
end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_finite_affine_chart_cover_over_modification : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S), QuasiCompact G.hom → ∀ (L : LB G.left), L.IsLB → ∃ (n : ℕ) (j : Fin n → L.ι) (W : Fin n → G.left.Opens) (U : Fin n → M.S.Opens), (⨆ b, W b = ⊤) ∧ (∀ b, W b ≤ L.U (j b)) ∧ (∀ b, W b ≤ G.hom ⁻¹ᵁ U b) ∧ (∀ b, IsAffineOpen (W b)) ∧ (∀ b, IsAffineOpen (U b)) := by
  first | exact @GlobalTheory.Mum.exists_finite_affine_chart_cover | exact GlobalTheory.Mum.exists_finite_affine_chart_cover | (intros; apply GlobalTheory.Mum.exists_finite_affine_chart_cover <;> assumption)

end
end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_genericPoint_factor_of_injective_base_map : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (W : Type) [CommRing W] [IsDomain W] (φ : R →+* W), Function.Injective φ → ∀ ξ : Sp W ⟶ M.S, ξ ≫ M.π = spMap φ → ∃ ψ : FractionRing R →+* FractionRing W, ψ.comp (algebraMap R (FractionRing R)) = (algebraMap W (FractionRing W)).comp φ ∧ spMap ψ ≫ M.gp = jK W ≫ ξ := by
  first | exact @GlobalTheory.Mum.Modif.exists_generic_factor | exact GlobalTheory.Mum.Modif.exists_generic_factor | (intros; apply GlobalTheory.Mum.Modif.exists_generic_factor <;> assumption)

end
end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_odd_prime_isUnit_of_completeNormalCharZeroBase : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∃ n : ℕ, n.Prime ∧ Odd n ∧ IsUnit (n : R) := by
  first | exact @GlobalTheory.exists_odd_prime_isUnit_of_base | exact GlobalTheory.exists_odd_prime_isUnit_of_base | (intros; apply GlobalTheory.exists_odd_prime_isUnit_of_base <;> assumption)

end
end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.genericPoint_flat_of_modification_of_domain : ∀ (R : Type) [CommRing R] [IsDomain R] (M : GlobalTheory.Mum.Modif R), Flat M.gp := by
  first | exact @GlobalTheory.Mum.Modif.flat_gp | exact GlobalTheory.Mum.Modif.flat_gp | (intros; apply GlobalTheory.Mum.Modif.flat_gp <;> assumption)

end
end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.isAffineOpen_preimage_genericBaseChange_modification : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S) (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ W : G.left.Opens, IsAffineOpen W → IsAffineOpen (α ⁻¹ᵁ W) := by
  first | exact @GlobalTheory.Mum.isAffineOpen_preimage_genericBaseChange | exact GlobalTheory.Mum.isAffineOpen_preimage_genericBaseChange | (intros; apply GlobalTheory.Mum.isAffineOpen_preimage_genericBaseChange <;> assumption)

end
end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.isCompleteDVRCharZero_of_finiteInjectiveExtension : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), GlobalTheory.LN.CDvr R → FinExt ρ → GlobalTheory.LN.CDvr R' := by
  first | exact @GlobalTheory.Mum.cDvr_of_finExt | exact GlobalTheory.Mum.cDvr_of_finExt | (intros; apply GlobalTheory.Mum.cDvr_of_finExt <;> assumption)

end
end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.isLocallyNoetherian_of_smooth_over_modification : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (M : Modif R) (G : Over M.S), Smooth G.hom → IsLocallyNoetherian G.left := by
  first | exact @GlobalTheory.Mum.isLocallyNoetherian_of_smooth_over_modif | exact GlobalTheory.Mum.isLocallyNoetherian_of_smooth_over_modif | (intros; apply GlobalTheory.Mum.isLocallyNoetherian_of_smooth_over_modif <;> assumption)

end
end
