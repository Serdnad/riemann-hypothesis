module

public import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowup
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.PullbackCarrier
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
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.ResolutionOfSingularities.Foundations.Blowup.ReesGrading
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ConsCompSuccAboveZero
import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

section

open FunctorialResolution.Blowup

namespace UpperTheory.ChartGen

variable {R : Type} [CommRing R]

private theorem val_rho (I : Ideal R) (c : ↥I) (r : R) :
    HomogeneousLocalization.val (chartRingHom I c r) =
      Localization.mk ((reesDegreeZeroEquiv I r : ↥(reesAlgebra I)))
        (1 : ↥(Submonoid.powers (reesGenerator I c))) := rfl

private theorem cancel_rho (I : Ideal R) (c : ↥I) (n : ℕ)
    {x y : HomogeneousLocalization.Away (reesGrading I) (reesGenerator I c)}
    (h : x * chartRingHom I c (c : R) ^ n = y * chartRingHom I c (c : R) ^ n) : x = y := by
  have hn := pow_mem (chartRingHom_mem_nonZeroDivisors I c) n
  have h0 : (x - y) * chartRingHom I c (c : R) ^ n = 0 := by rw [sub_mul, h, sub_self]
  exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hn).2 _ h0)

private theorem exists_mul_pow_eq (I : Ideal R) (c : ↥I)
    (z : HomogeneousLocalization.Away (reesGrading I) (reesGenerator I c)) :
    ∃ (n : ℕ) (r : R), r ∈ I ^ n ∧
      z * chartRingHom I c (c : R) ^ n = chartRingHom I c r := by
  obtain ⟨n, x, hx, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (reesGrading I)
    (reesGenerator_mem_reesGrading I c) z
  have hx' : x ∈ reesGrading I n := by simpa using hx
  obtain ⟨r, hr, hxr⟩ := (mem_reesGrading_iff_monomial I n x).1 hx'
  refine ⟨n, r, hr, ?_⟩
  rw [← map_pow, HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mul,
    val_rho, val_rho, HomogeneousLocalization.Away.val_mk, Localization.mk_mul,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  apply Subtype.ext
  have hpow : ((reesGenerator I c ^ n : ↥(reesAlgebra I)) : Polynomial R) =
      Polynomial.monomial n ((c : R) ^ n) := by
    rw [SubmonoidClass.coe_pow, reesGenerator_coe, Polynomial.monomial_pow, one_mul]
  push_cast [reesDegreeZeroEquiv_coe_coe, hxr, hpow]
  simp [Polynomial.C_mul_monomial, Polynomial.monomial_mul_C, mul_comm]
  rw [← Polynomial.C_pow, Polynomial.monomial_mul_C]

end UpperTheory.ChartGen

open UpperTheory.ChartGen in
theorem UpperTheory.surjective_eval_blowupChart_of_span_eq :
    ∀ {R : Type} [CommRing R] (I : Ideal R) {M : ℕ} (a : Fin (M + 1) → ↥I), Ideal.span (Set.range fun l => (a l : R)) = I → ∀ m : Fin (M + 1), Function.Surjective (MvPolynomial.eval₂Hom (chartRingHom I (a m)) (fun l => chartFraction I (a m) (a l))) := by
  intro R _ I M a hspan m
  set c := a m with hc
  set φ := MvPolynomial.eval₂Hom (chartRingHom I c) (fun l => chartFraction I c (a l)) with hφ
  have hC : ∀ r : R, chartRingHom I c r ∈ φ.range := fun r =>
    ⟨MvPolynomial.C r, by simp [hφ]⟩
  have hX : ∀ l, chartFraction I c (a l) ∈ φ.range := fun l =>
    ⟨MvPolynomial.X l, by simp [hφ]⟩
  have hfrac : ∀ b : ↥I, chartFraction I c b ∈ φ.range := by
    intro b
    have hb : (b : R) ∈ Ideal.span (Set.range fun l => (a l : R)) := by rw [hspan]; exact b.2
    obtain ⟨s, hs⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hb
    have hw : ∑ l, chartRingHom I c (s l) * chartFraction I c (a l) ∈ φ.range :=
      sum_mem fun l _ => mul_mem (hC _) (hX l)
    have heq : chartFraction I c b = ∑ l, chartRingHom I c (s l) * chartFraction I c (a l) := by
      apply cancel_rho I c 1

      rw [pow_one, ← chartRingHom_coe_eq_chartFraction_mul, ← hs, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_mul, chartRingHom_coe_eq_chartFraction_mul I c (a l), mul_assoc]
    rw [heq]
    exact hw
  have hpow : ∀ (n : ℕ), ∀ r ∈ I ^ n, ∃ w ∈ φ.range,
      chartRingHom I c r = w * chartRingHom I c (c : R) ^ n := by
    intro n
    induction n with
    | zero => exact fun r _ => ⟨_, hC r, by simp⟩
    | succ n ih =>
      intro r hr
      rw [pow_succ] at hr
      refine Submodule.mul_induction_on hr ?_ ?_
      · intro s hs b hb
        obtain ⟨w, hw, hwe⟩ := ih s hs
        refine ⟨w * chartFraction I c ⟨b, hb⟩, mul_mem hw (hfrac _), ?_⟩
        have hbe := chartRingHom_coe_eq_chartFraction_mul I c ⟨b, hb⟩
        rw [map_mul, hwe]
        simp only at hbe
        rw [hbe]
        ring
      · rintro x y ⟨wx, hwx, hx⟩ ⟨wy, hwy, hy⟩
        exact ⟨wx + wy, add_mem hwx hwy, by rw [map_add (f := _), hx, hy, add_mul]⟩
  intro z
  obtain ⟨n, r, hr, hz⟩ := exists_mul_pow_eq I c z
  obtain ⟨w, hw, hwe⟩ := hpow n r hr
  have hzw : z = w := cancel_rho I c n (hz.trans hwe)
  rw [hzw]
  exact hw
end

section

open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor FunctorialResolution.Blowup
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

theorem UpperTheory.restrict_mem_nonZeroDivisors_of_isAffineOpen :
    ∀ {W : Scheme.{0}} {V O : W.Opens}, IsAffineOpen V → ∀ (h : O ≤ V) (t : Γ(W, V)), t ∈ nonZeroDivisors Γ(W, V) →
        W.presheaf.map (homOfLE h).op t ∈ nonZeroDivisors Γ(W, O) := by
  intro W V O hV h t ht
  rw [mem_nonZeroDivisors_iff_right] at ht ⊢
  intro s hs
  refine TopCat.Presheaf.section_ext W.sheaf O s 0 (fun x hx => ?_)
  rw [map_zero]
  have hxV : x ∈ V := h hx
  algebraize [(W.presheaf.germ V x hxV).hom]
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  have hloc := IsLocalization.nonZeroDivisors_le_comap (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
    (W.presheaf.stalk x) (mem_nonZeroDivisors_iff_right.mpr ht)
  rw [Submonoid.mem_comap, RingHom.algebraMap_toAlgebra, mem_nonZeroDivisors_iff_right] at hloc
  apply hloc
  have e := congrArg (W.presheaf.germ O x hx).hom hs
  rw [map_mul, map_zero, TopCat.Presheaf.germ_res_apply] at e
  exact e
end

section

open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor FunctorialResolution.Blowup
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

theorem UpperTheory.sections_generated_over_affine_product_cover :
    ∀ {S Z P W : Scheme.{0}} [IsAffine S] (p : Z ⟶ S) (q : P ⟶ S) (π : W ⟶ Z) (f : W ⟶ P)
        (h : π ≫ p = f ≫ q) {α β : Type} (U : α → Z.Opens) (D : β → P.Opens),
        (∀ a, IsAffineOpen (U a)) → (∀ b, IsAffineOpen (D b)) → iSup U = ⊤ → iSup D = ⊤ →
        ∀ (V : α → β → W.Opens), (∀ a b, IsAffineOpen (V a b)) →
        ∀ (eV : ∀ a b, V a b = π ⁻¹ᵁ U a ⊓ f ⁻¹ᵁ D b),
        (∀ a b (s : Γ(W, V a b)), s ∈ Subring.closure
          (Set.range (π.appLE (U a) (V a b) ((eV a b).le.trans inf_le_left)).hom ∪
           Set.range (f.appLE (D b) (V a b) ((eV a b).le.trans inf_le_right)).hom)) →
        IsClosedImmersion (pullback.lift π f h : W ⟶ pullback p q) := by
  intro S Z P W _ p q π f h α β U D hU hD hUc hDc V hV eV hgen
  set L : W ⟶ pullback p q := pullback.lift π f h with hL
  let Wt : α × β → (pullback p q).Opens := fun i =>
    pullback.fst p q ⁻¹ᵁ U i.1 ⊓ pullback.snd p q ⁻¹ᵁ D i.2
  have hcov : iSup Wt = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    have hx1 : pullback.fst p q x ∈ iSup U := by rw [hUc]; trivial
    have hx2 : pullback.snd p q x ∈ iSup D := by rw [hDc]; trivial
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hx1
    obtain ⟨b, hb⟩ := TopologicalSpace.Opens.mem_iSup.mp hx2
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨(a, b), ⟨ha, hb⟩⟩
  have hWt : ∀ i, IsAffineOpen (Wt i) := by
    intro i
    haveI : IsAffine (U i.1) := hU i.1
    haveI : IsAffine (D i.2) := hD i.2
    let m := pullback.map ((U i.1).ι ≫ p) ((D i.2).ι ≫ q) p q (U i.1).ι (D i.2).ι (𝟙 S)
      (by simp) (by simp)
    have hm : m.opensRange = Wt i := by
      ext1
      rw [Scheme.Hom.coe_opensRange, Scheme.Pullback.range_map, Scheme.Opens.range_ι,
        Scheme.Opens.range_ι]
      rfl
    rw [← hm]
    exact isAffineOpen_opensRange m
  have hpre : ∀ i, L ⁻¹ᵁ Wt i = V i.1 i.2 := by
    intro i
    rw [eV, Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hL,
      pullback.lift_fst, pullback.lift_snd]
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion) Wt hcov]
  rintro ⟨a, b⟩
  have aux : ∀ (Vo : W.Opens) (h1 : Vo ≤ π ⁻¹ᵁ U a) (h2 : Vo ≤ f ⁻¹ᵁ D b), Vo = V a b →
      ∀ s : Γ(W, Vo), s ∈ Subring.closure (Set.range (π.appLE (U a) Vo h1).hom ∪
        Set.range (f.appLE (D b) Vo h2).hom) := by
    rintro Vo h1 h2 rfl s
    exact hgen a b s
  have e1 : L ⁻¹ᵁ Wt (a, b) ≤ π ⁻¹ᵁ U a := by
    rw [hpre (a, b)]; exact (eV a b).le.trans inf_le_left
  have e2 : L ⁻¹ᵁ Wt (a, b) ≤ f ⁻¹ᵁ D b := by
    rw [hpre (a, b)]; exact (eV a b).le.trans inf_le_right
  have hsurj : Function.Surjective (L.app (Wt (a, b))) := by
    intro y
    have hy := aux _ e1 e2 (hpre (a, b)) y
    have hle : Set.range (π.appLE (U a) _ e1).hom ∪ Set.range (f.appLE (D b) _ e2).hom ⊆
        ((L.app (Wt (a, b))).hom.range : Set _) := by
      rintro _ (⟨x, rfl⟩ | ⟨x, rfl⟩)
      · refine ⟨(pullback.fst p q).appLE (U a) (Wt (a, b)) inf_le_left x, ?_⟩
        rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
        simp only [hL, pullback.lift_fst]
      · refine ⟨(pullback.snd p q).appLE (D b) (Wt (a, b)) inf_le_right x, ?_⟩
        rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
        simp only [hL, pullback.lift_snd]
    exact (Subring.closure_le.mpr hle) hy
  haveI : IsAffine (Wt (a, b)) := hWt (a, b)
  have hA : IsAffineOpen (L ⁻¹ᵁ Wt (a, b)) := by rw [hpre (a, b)]; exact hV a b
  haveI : IsAffine (L ⁻¹ᵁ Wt (a, b)) := hA
  apply IsClosedImmersion.of_surjective_of_isAffine
  rw [morphismRestrict_appTop]
  have hs2 : Function.Surjective (L.app ((Wt (a, b)).ι ''ᵁ ⊤)) := by
    rw [Scheme.Opens.ι_image_top]
    exact hsurj
  have comp_surj : ∀ {A B C : CommRingCat} (u : A ⟶ B) (v : B ⟶ C) [IsIso v],
      Function.Surjective u → Function.Surjective (u ≫ v) := by
    intro A B C u v _ hu y
    obtain ⟨z, rfl⟩ := (ConcreteCategory.bijective_of_isIso v).2 y
    obtain ⟨w, rfl⟩ := hu z
    exact ⟨w, by simp⟩
  have isoE : ∀ {A B : W.Opens} (e : A = B), IsIso (W.presheaf.map (eqToHom e).op) := by
    intro A B e
    subst e
    rw [eqToHom_refl, op_id, W.presheaf.map_id]
    infer_instance
  refine @comp_surj _ _ _ _ _ (isoE _) hs2
end
