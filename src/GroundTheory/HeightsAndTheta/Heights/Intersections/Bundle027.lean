module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle013
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle021
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle002
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace BlockGenFinite

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem eval_smul_of_isMultiHomog {s : MRing ι} {a : K → ℕ} (hs : IsMultiHomog s a) (c : K → ℂ)
    (u : (Σ k, ι k) → ℂ) :
    eval (fun p ↦ c p.1 * u p) (map (Int.castRingHom ℂ) s) =
      (∏ k, c k ^ a k) * eval u (map (Int.castRingHom ℂ) s) := by
  rw [eval_map, eval_map, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hprod : ∏ p, (c p.1 * u p) ^ d p = (∏ k, c k ^ a k) * ∏ p, u p ^ d p := by
    simp only [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    show ∏ i, c k ^ d ⟨k, i⟩ = c k ^ a k
    rw [Finset.prod_pow_eq_pow_sum, hs d hd k]
  rw [hprod]
  ring


omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem eval_map_rename (v : (Σ k, ι k) → (Σ k', ι' k')) (s : MRing ι) (z' : (Σ k', ι' k') → ℂ) :
    eval z' (map (Int.castRingHom ℂ) (rename v s)) = eval (fun p ↦ z' (v p)) (map (Int.castRingHom ℂ) s) := by
  rw [map_rename, eval_rename]
  rfl

end BlockGenFinite


open BlockGenFinite in
theorem BlockGenFinite.proof (hR : BlockRatioAlg.Statement) : BlockGenFinite.Statement := by
  classical
  intro K _ ι _ K' _ ι' _ κ v P' n hv hP' hP
  have hrel := hP'.2.1.2.2
  have hpr := hP'.2.1.1
  have hrel' : ∀ k : FibreBlock κ, ∃ i : ι' k.1, (X (⟨k.1, i⟩ : Σ k', ι' k') : MRing ι') ∉ P' := fun k ↦ hrel k.1
  choose c hc using hrel'
  have hA := fun q : (Σ k : FibreBlock κ, ι' k.1) ↦
    hR K ι K' ι' κ v P' n hv hP' hP ⟨q.1.1, q.2⟩ ⟨q.1.1, c q.1⟩ rfl (hc q.1)
  choose m A a hAh hAl hAP using hA
  refine ⟨(∏ q, rename v (A q (Fin.last (m q)))) * ∏ k : FibreBlock κ, X ⟨k.1, c k⟩,
    (∑ q, Function.extend κ (a q) 0) + ∑ k : FibreBlock κ, Pi.single k.1 1, ?_, ?_, ?_⟩
  · exact AvoidRing.isMultiHomog_mul
      (AvoidRing.isMultiHomog_prod _ _ _ fun q _ ↦ ArithmeticIntersectionHorizontal.isMultiHomog_rename hv (hAh q _))
      (AvoidRing.isMultiHomog_prod _ _ _ fun k _ ↦ AvoidRing.isMultiHomog_X _ _)
  · intro h
    rcases hpr.mul_mem_iff_mem_or_mem.mp h with h | h
    · obtain ⟨q, -, hq⟩ := hpr.prod_mem_iff.mp h
      exact hAl q hq
    · obtain ⟨k, -, hk⟩ := hpr.prod_mem_iff.mp h
      exact hc k hk
  intro u

  obtain ⟨pol, hpol⟩ : ∃ pol : (Σ k : FibreBlock κ, ι' k.1) → Polynomial ℂ, ∀ q, pol q =
      ∑ j : Fin (m q + 1), Polynomial.C (eval u (map (Int.castRingHom ℂ) (A q j))) * Polynomial.X ^ (j : ℕ) :=
    ⟨_, fun _ ↦ rfl⟩

  obtain ⟨build, hbuild⟩ : ∃ build : ((Σ k : FibreBlock κ, ι' k.1) → ℂ) → (Σ k', ι' k') → ℂ, ∀ ρ p',
      build ρ p' = if h : p'.1 ∈ Set.range κ then u (hv.2.2.2 p' h).choose else ρ ⟨⟨p'.1, h⟩, p'.2⟩ :=
    ⟨_, fun _ _ ↦ rfl⟩
  refine ⟨(Fintype.piFinset fun q ↦ (pol q).roots.toFinset).image build, ?_⟩
  rintro z' hz' hf0 ⟨d, hd, hzd⟩
  have hzd' : ∀ p, z' (v p) = d p.1 * u p := fun p ↦ congrFun hzd p
  simp only [map_mul, map_prod, map_X, eval_X] at hf0
  have hcz : ∀ k : FibreBlock κ, z' ⟨k.1, c k⟩ ≠ 0 := fun k ↦
    Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hf0) k (Finset.mem_univ _)
  have hlead : ∀ q, eval u (map (Int.castRingHom ℂ) (A q (Fin.last (m q)))) ≠ 0 := by
    intro q h
    have := Finset.prod_ne_zero_iff.mp (left_ne_zero_of_mul hf0) q (Finset.mem_univ _)
    rw [eval_map_rename, show (fun p ↦ z' (v p)) = fun p ↦ d p.1 * u p from hzd,
      eval_smul_of_isMultiHomog (hAh q _), h, mul_zero] at this
    exact this rfl

  have hroot : ∀ q, z' ⟨q.1.1, q.2⟩ / z' ⟨q.1.1, c q.1⟩ ∈ (pol q).roots.toFinset := by
    intro q
    have hne : pol q ≠ 0 := by
      intro h0
      have h1 := congrArg (fun f ↦ _root_.AddMonoidAlgebra.coeff (M := ℕ) f (m q)) h0
      simp only [hpol, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
        Polynomial.coeff_zero] at h1
      rw [Finset.sum_eq_single (Fin.last (m q))] at h1
      · simp only [Fin.val_last, if_true] at h1
        exact hlead q h1
      · intro j _ hj
        rw [if_neg]
        intro e
        exact hj (Fin.ext (by simp [e]))
      · simp
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot.def]
    have hrel0 := hz'.2 _ (hAP q)

    simp only [map_sum, map_mul, map_pow, map_X, eval_X, eval_map_rename,
    show (fun p ↦ z' (v p)) = fun p ↦ d p.1 * u p from hzd, eval_smul_of_isMultiHomog (hAh q _)] at hrel0
    have hD : (∏ k, d k ^ a q k) * z' ⟨q.1.1, c q.1⟩ ^ m q ≠ 0 :=
      mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hd k)) (pow_ne_zero _ (hcz q.1))
    refine (mul_eq_zero.mp ?_).resolve_left hD
    rw [hpol, Polynomial.eval_finsetSum, Finset.mul_sum, ← hrel0]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hj : (j : ℕ) ≤ m q := Nat.lt_succ_iff.mp j.2
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← pow_sub_mul_pow (z' ⟨q.1.1, c q.1⟩) hj, div_pow]
    field_simp [pow_ne_zero _ (hcz q.1)]

  refine ⟨build fun q ↦ z' ⟨q.1.1, q.2⟩ / z' ⟨q.1.1, c q.1⟩,
    Finset.mem_image_of_mem _ (Fintype.mem_piFinset.mpr hroot), ?_⟩
  refine ⟨fun k' ↦ if h : k' ∈ Set.range κ then d h.choose else z' ⟨k', c ⟨k', h⟩⟩,
    fun k' ↦ ?_, funext fun p' ↦ ?_⟩
  · dsimp only
    split_ifs with h
    · exact hd _
    · exact hcz ⟨k', h⟩
  · rw [hbuild]
    by_cases h : p'.1 ∈ Set.range κ
    · rw [dite_eq_left h]
      dsimp only
      rw [dite_eq_left h]
      obtain ⟨p, rfl⟩ := hv.2.2.2 p' h
      rw [show h.choose = p.1 from hv.1 (h.choose_spec.trans (hv.2.2.1 p)),
        show (hv.2.2.2 (v p) h).choose = p from hv.2.1 (hv.2.2.2 (v p) h).choose_spec]
      exact hzd' p
    · rw [dite_eq_right h]
      dsimp only
      rw [dite_eq_right h]
      have hc' := hcz ⟨p'.1, h⟩
      dsimp only at hc'
      field_simp [hc']

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace ArithmeticIntersectionCycle

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]


omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem comap_C_imageZ (v : (Σ k, ι k) → (Σ k', ι' k')) (W' : Ideal (MRing ι')) :
    (imageZ v W').comap (C : ℤ →+* MRing ι) = W'.comap (C : ℤ →+* MRing ι') := by
  ext c
  simp [imageZ, Ideal.mem_comap]

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem isHorizontal_imageZ_iff (v : (Σ k, ι k) → (Σ k', ι' k')) (W' : Ideal (MRing ι')) :
    IsHorizontal (imageZ v W') ↔ IsHorizontal W' := by
  rw [IsHorizontal, IsHorizontal, comap_C_imageZ]

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem charOf_imageZ (v : (Σ k, ι k) → (Σ k', ι' k')) (W' : Ideal (MRing ι')) :
    charOf (imageZ v W') = charOf W' := by
  simp only [charOf, comap_C_imageZ]

end ArithmeticIntersectionCycle

theorem ArithmeticIntersectionCycle.proof (hHor : ArithmeticIntersectionHorizontal.Statement) (hVert : ArithmeticIntersectionVertical.Statement) (hPush : ArithmeticIntersectionDivisorPushforward.Statement)
    (hGP : GenericPointExists.Statement)
    (hEU : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι) :
    ArithmeticIntersectionCycle.Statement := by
  intro I hI n hn K _ ι _ K' _ ι' _ κ v P' G J L L' s α hv hP' hP hJ hL hLL' hs hsP
  classical

  have hex : ∀ W' : Ideal (MRing ι'), W'.IsPrime →
      ∃ (G' : GenFibre v W') (J' : IFamily G'.Φ (fibreIdx ι' κ)), IsFieldIntersection J' := by
    intro W' hW'
    obtain ⟨G'⟩ := hGP K ι K' ι' v W' hW'
    obtain ⟨J', hJ', -⟩ := hEU G'.Φ (FibreBlock κ) (fibreIdx ι' κ)
    exact ⟨G', J', hJ'⟩
  let E : Ideal (MRing ι') → ℤ := fun W' =>
    if h : ∃ (G' : GenFibre v W') (J' : IFamily G'.Φ (fibreIdx ι' κ)), IsFieldIntersection J' then
      h.choose_spec.choose (fibreIdeal κ h.choose) 0 Fin.elim0 else 0
  have hE : ∀ W' : Ideal (MRing ι'), W'.IsPrime →
      ∃ (G' : GenFibre v W') (J' : IFamily G'.Φ (fibreIdx ι' κ)),
        IsFieldIntersection J' ∧ E W' = J' (fibreIdeal κ G') 0 Fin.elim0 := by
    intro W' hW'
    have h := hex W' hW'
    exact ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec, by simp only [E, dif_pos h]⟩

  let T : Ideal (MRing ι) → ℝ := fun W =>
    if IsHorizontal W then I K ι W n L else (geoNum n W (fun j => (L j).a) : ℝ) * Real.log (charOf W)
  let T' : Ideal (MRing ι') → ℝ := fun W' =>
    if IsHorizontal W' then I K' ι' W' n L' else (geoNum n W' (fun j => (L' j).a) : ℝ) * Real.log (charOf W')
  have hterm : ∀ W' ∈ divSupp P' (rename v s), T' W' = if imageZ v W' ∈ divSupp (imageZ v P') s then (E W' : ℝ) * T (imageZ v W') else 0 := by
    intro W' hW'
    obtain ⟨G', J', hJ', hEW⟩ := hE W' hW'.1.isPrime
    by_cases hh : IsHorizontal W'
    · have hh' : IsHorizontal (imageZ v W') := (ArithmeticIntersectionCycle.isHorizontal_imageZ_iff v W').2 hh
      rcases hHor I hI n hn K ι K' ι' κ v P' L L' s α W' hv hP' hP hL hLL' hs hsP hW' hh with
        ⟨hm, he⟩ | ⟨hm, h0⟩
      · simp only [T', T, if_pos hh, if_pos hm, if_pos hh', he G' J' hJ', hEW]
      · simp only [T', if_pos hh, if_neg hm, h0]
    · have hh' : ¬ IsHorizontal (imageZ v W') := fun h => hh ((ArithmeticIntersectionCycle.isHorizontal_imageZ_iff v W').1 h)
      have ha : (fun j => (L' j).a) = fun j => pullDeg κ (L j).a := funext fun j => (hLL' j).1
      rcases hVert K ι K' ι' κ v P' n (fun j => (L j).a) s α W' hv hP' hP hs hsP hW' hh with
        ⟨hm, he⟩ | ⟨hm, h0⟩
      · simp only [T', T, if_neg hh, if_pos hm, if_neg hh', ArithmeticIntersectionCycle.charOf_imageZ]
        rw [ha, he G' J' hJ', hEW]
        push_cast
        ring
      · simp only [T', if_neg hh, if_neg hm]
        rw [ha, h0]
        simp

  have hfin' : (divSupp P' (rename v s)).Finite := divSupp_finite _ _
  have hfin : (divSupp (imageZ v P') s).Finite := divSupp_finite _ _
  have key : ∀ W ∈ hfin.toFinset,
      ∑ W' ∈ hfin'.toFinset.filter (fun W' => imageZ v W' = W),
        (multAt (P' ⊔ Ideal.span {rename v s}) W' : ℤ) * E W' =
        J (fibreIdeal κ G) 0 Fin.elim0 * multAt (imageZ v P' ⊔ Ideal.span {s}) W := by
    intro W hW
    have h := hPush K ι K' ι' κ v P' n G J s α W E hv hP' hP hJ hs hsP (hfin.mem_toFinset.1 hW)
      (fun W' hW' _ => hE W' hW'.1.isPrime)
    have hfiber : {W' | W' ∈ divSupp P' (rename v s) ∧ imageZ v W' = W}.Finite :=
      hfin'.subset (fun _ hx => hx.1)
    rw [finsum_mem_eq_finite_toFinset_sum _ hfiber] at h
    rw [← h]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext W'
    simp [Set.Finite.mem_toFinset]

  show (∑ᶠ W' ∈ divSupp P' (rename v s), (multAt (P' ⊔ Ideal.span {rename v s}) W' : ℝ) * T' W') =
    (J (fibreIdeal κ G) 0 Fin.elim0 : ℝ) * ∑ᶠ W ∈ divSupp (imageZ v P') s, (multAt (imageZ v P' ⊔ Ideal.span {s}) W : ℝ) * T W
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin', finsum_mem_eq_finite_toFinset_sum _ hfin]
  calc ∑ W' ∈ hfin'.toFinset, (multAt (P' ⊔ Ideal.span {rename v s}) W' : ℝ) * T' W'
      = ∑ W' ∈ hfin'.toFinset, if imageZ v W' ∈ hfin.toFinset then
          (multAt (P' ⊔ Ideal.span {rename v s}) W' : ℝ) * E W' * T (imageZ v W') else 0 := by
        refine Finset.sum_congr rfl fun W' hW' => ?_
        rw [hterm W' (hfin'.mem_toFinset.1 hW')]
        simp only [Set.Finite.mem_toFinset]
        split_ifs <;> ring
    _ = ∑ W' ∈ hfin'.toFinset with imageZ v W' ∈ hfin.toFinset,
          (multAt (P' ⊔ Ideal.span {rename v s}) W' : ℝ) * E W' * T (imageZ v W') := by
        rw [Finset.sum_filter]
    _ = ∑ W ∈ hfin.toFinset, ∑ W' ∈ hfin'.toFinset with imageZ v W' = W,
          (multAt (P' ⊔ Ideal.span {rename v s}) W' : ℝ) * E W' * T (imageZ v W') := by
        rw [Finset.sum_fiberwise_eq_sum_filter]
    _ = ∑ W ∈ hfin.toFinset, ((∑ W' ∈ hfin'.toFinset with imageZ v W' = W,
          (multAt (P' ⊔ Ideal.span {rename v s}) W' : ℤ) * E W' : ℤ) : ℝ) * T W := by
        refine Finset.sum_congr rfl fun W _ => ?_
        push_cast
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun W' hW' => ?_
        rw [(Finset.mem_filter.1 hW').2]
    _ = (J (fibreIdeal κ G) 0 Fin.elim0 : ℝ) *
          ∑ W ∈ hfin.toFinset, (multAt (imageZ v P' ⊔ Ideal.span {s}) W : ℝ) * T W := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun W hW => ?_
        rw [key W hW]
        push_cast
        ring

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityLocalPrime.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (p : ℤ) (y : funField P),
    IsArithVar P 1 → Prime p →
    (∀ W, IsClosedPt W → P ≤ W → C p ∈ W → (y : FractionRing (MRing ι ⧸ P)) ∈ locRing P W) →
    ∃ n : ℤ, ¬ p ∣ n ∧ (n : funField P) * y ∈ regRing P

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityLocal.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (b : regRing P),
    IsArithVar P 1 → b ≠ 0 →
    {W | IsClosedPt W ∧ P ≤ W ∧
        Nat.card (locRing P W ⧸ locIdeal P W ((b : funField P) : FractionRing (MRing ι ⧸ P))) ≠ 1}.Finite ∧
      ∑ᶠ W ∈ {W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W},
          Real.log (Nat.card (locRing P W ⧸ locIdeal P W ((b : funField P) : FractionRing (MRing ι ⧸ P)))) =
        Real.log (Nat.card (regRing P ⧸ Ideal.span {b}))

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityMaximalSurjective.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsArithVar P 1 → ∀ m : Ideal (regRing P), m.IsMaximal →
    ∃ W : Ideal (MRing ι), IsClosedPt W ∧ P ≤ W ∧ ∀ x ∈ m, ∀ z ∈ locRing P W,
      ((x : funField P) : FractionRing (MRing ι ⧸ P)) * z ≠ 1

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityMaximalSpectrum.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsArithVar P 1 → ∃ e : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W} ≃ MaximalSpectrum (regRing P),
      ∀ (W : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W}) (y : FractionRing (MRing ι ⧸ P)),
        y ∈ locRing P W.1 ↔ ∃ x s : regRing P, s ∉ (e W).asIdeal ∧
          y * ((s : funField P) : FractionRing (MRing ι ⧸ P)) = ((x : funField P) : FractionRing (MRing ι ⧸ P))

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityLocalize.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι))
    (y : FractionRing (MRing ι ⧸ P)),
    IsArithVar P 1 → IsClosedPt W → P ≤ W → y ∈ locRing P W →
    ∃ s x : regRing P, (∃ z ∈ locRing P W, ((s : funField P) : FractionRing (MRing ι ⧸ P)) * z = 1) ∧
      y * ((s : funField P) : FractionRing (MRing ι ⧸ P)) = ((x : funField P) : FractionRing (MRing ι ⧸ P))

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityIntegral.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsArithVar P 1 → ∀ x : regRing P, IsIntegral ℤ ((x : funField P) : FractionRing (MRing ι ⧸ P))

end

end GroundTheory.Heights₂.Heights.Inter
end
