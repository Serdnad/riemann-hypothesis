module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle013
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.Intersections.NormSegreSameOrbit
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle025
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle005
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CycDim
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle013

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GenericPointsInAffineChart

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]


open Classical in
theorem exists_normalise {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {P' : Ideal (MRing ι')} (hP' : IsMultiHomogIdeal P') {j : ∀ k : FibreBlock κ, ι' k.1}
    {z : (Σ k, ι k) → ℂ} {c : K → ℂ} (hc : ∀ k, c k ≠ 0) {z' : (Σ k', ι' k') → ℂ} (hz' : z' ∈ mcPts P')
    (hzz : SameOrbit (fun p => z' (v p)) z) (hj : ∀ k : FibreBlock κ, z' ⟨k.1, j k⟩ ≠ 0) :
    ∃ d : K' → ℂ, (∀ k, d k ≠ 0) ∧ (fun q => d q.1 * z' q) ∈ mcPts P' ∧
      (∀ p, d (v p).1 * z' (v p) = c p.1 * z p) ∧ ∀ k : FibreBlock κ, d k.1 * z' ⟨k.1, j k⟩ = 1 := by
  obtain ⟨s, hs, hzs⟩ := hzz
  let d : K' → ℂ := fun k' =>
    if h : k' ∈ Set.range κ then c h.choose / s h.choose else (z' ⟨k', j ⟨k', h⟩⟩)⁻¹
  have hdk : ∀ k, d (κ k) = c k / s k := by
    intro k
    have h : κ k ∈ Set.range κ := ⟨k, rfl⟩
    have hk : h.choose = k := hv.1 h.choose_spec
    simp only [d, dif_pos h, hk]
  have hd : ∀ k, d k ≠ 0 := by
    intro k'
    by_cases h : k' ∈ Set.range κ
    · obtain ⟨k, rfl⟩ := h
      rw [hdk]
      exact div_ne_zero (hc k) (hs k)
    · simp only [d, dif_neg h]
      exact inv_ne_zero (hj ⟨k', h⟩)
  refine ⟨d, hd, mcPts_smul hP' d hd hz', fun p => ?_, fun k => ?_⟩
  · have h1 : z' (v p) = s p.1 * z p := congrFun hzs p
    rw [hv.2.2.1 p, hdk, h1]
    field_simp [hs p.1]
  · have h : k.1 ∉ Set.range κ := k.2
    simp only [d, dif_neg h]
    exact inv_mul_cancel₀ (hj k)


omit [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem eq_of_normalised {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {j : ∀ k : FibreBlock κ, ι' k.1} {w : (Σ k, ι k) → ℂ} (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0)
    {z₁ z₂ : (Σ k', ι' k') → ℂ} (h₁v : ∀ p, z₁ (v p) = w p) (h₁j : ∀ k : FibreBlock κ, z₁ ⟨k.1, j k⟩ = 1)
    (h₂v : ∀ p, z₂ (v p) = w p) (h₂j : ∀ k : FibreBlock κ, z₂ ⟨k.1, j k⟩ = 1) (h : SameOrbit z₁ z₂) :
    z₁ = z₂ := by
  obtain ⟨t, -, ht⟩ := h
  have ht1 : ∀ k', t k' = 1 := by
    intro k'
    by_cases hk : k' ∈ Set.range κ
    · obtain ⟨k, rfl⟩ := hk
      obtain ⟨i, hi⟩ := hw k
      have e := congrFun ht (v ⟨k, i⟩)
      simp only [h₁v, h₂v, hv.2.2.1] at e
      have e' : (t (κ k) - 1) * w ⟨k, i⟩ = 0 := by rw [sub_mul, ← e]; ring
      exact sub_eq_zero.mp ((mul_eq_zero.mp e').resolve_right hi)
    · have e := congrFun ht ⟨k', j ⟨k', hk⟩⟩
      have e1 : z₁ ⟨k', j ⟨k', hk⟩⟩ = 1 := h₁j ⟨k', hk⟩
      have e2 : z₂ ⟨k', j ⟨k', hk⟩⟩ = 1 := h₂j ⟨k', hk⟩
      simp only [e1, e2, mul_one] at e
      exact e.symm
  rw [ht]
  funext q
  simp [ht1]

end GenericPointsInAffineChart


open GenericPointsInAffineChart PullbackDegreeCount in
theorem GenericPointsInAffineChart.proof (hFin : ArithmeticIntersectionChartFinite.Statement) (hNorm : ChartNormCount.Statement)
    (hOrb : OrbitCompNonvanish.Statement) : GenericPointsInAffineChart.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n G j hv hP' hP hj
  obtain ⟨E, hE, hEw⟩ := hNorm K ι K' ι' κ v P' n G j hv hP' hP hj (hFin K ι K' ι' κ v P' n G j hv hP' hP hj)
  have hPh : IsMultiHomogIdeal (imageZ v P') := hP.2.1.2.1
  have hP'h : IsMultiHomogIdeal P' := hP'.2.1.2.1
  obtain ⟨D, a, hD, hDP, hDz⟩ := hOrb K ι (imageZ v P') E hPh hE
  refine ⟨D, a, hD, hDP, fun z hz hDz0 => ?_⟩
  obtain ⟨c, hc, hEc⟩ := hDz z hDz0
  have hw : (fun p => c p.1 * z p) ∈ mcPts (imageZ v P') := mcPts_smul hPh c hc hz
  obtain ⟨hfin, hcard, hnz⟩ := hEw _ hw hEc
  set N := {z' | z' ∈ mcPts P' ∧ (∀ p, z' (v p) = c p.1 * z p) ∧ ∀ k : FibreBlock κ, z' ⟨k.1, j k⟩ = 1} with hN
  let orb : ((Σ k', ι' k') → ℂ) → Set ((Σ k', ι' k') → ℂ) := fun z' => {z'' | SameOrbit z'' z'}
  have himg : ptsOverChart P' κ v j z = orb '' N := by
    ext O
    constructor
    · rintro ⟨z', hz', rfl, hzz, hjz⟩
      obtain ⟨d, hd, hm, hdv, hdj⟩ := exists_normalise hv hP'h hc hz' hzz hjz
      have hs : SameOrbit (fun q => d q.1 * z' q) z' := ⟨d, hd, rfl⟩
      refine ⟨_, ⟨hm, hdv, hdj⟩, ?_⟩
      ext y
      exact ⟨fun h => sameOrbit_comp h hs, fun h => sameOrbit_comp h (sameOrbit_flip hs)⟩
    · rintro ⟨z', ⟨hz', hzv, hzj⟩, rfl⟩
      refine ⟨z', hz', rfl, ⟨c, hc, funext hzv⟩, fun k => ?_⟩
      rw [hzj k]
      exact one_ne_zero
  have hinj : Set.InjOn orb N := by
    intro z₁ h₁ z₂ h₂ h12
    have hmem : z₁ ∈ orb z₁ := sameOrbit_self z₁
    rw [h12] at hmem
    exact eq_of_normalised hv hw.1 h₁.2.1 h₁.2.2 h₂.2.1 h₂.2.2 hmem
  refine ⟨himg ▸ hfin.image orb, ?_, fun z' hz' hzz hjz q hq => ?_⟩
  · rw [himg, hinj.ncard_image, hcard]
  · obtain ⟨d, hd, hm, hdv, hdj⟩ := exists_normalise hv hP'h hc hz' hzz hjz
    have h := hnz _ hm hdv hdj q hq
    exact right_ne_zero_of_mul h

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

section Homog

variable {R : Type*} [CommRing R] {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem weight_blockSingle (d : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ)) d = fun k => ∑ i, d ⟨k, i⟩ := by
  funext k
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]
  simp [Pi.single_apply]

theorem isMultiHomog_iff_weighted (f : MRingOver R ι) (a : K → ℕ) :
    IsMultiHomog f a ↔ IsWeightedHomogeneous (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ)) f a := by
  constructor
  · intro h d hd
    rw [weight_blockSingle]
    funext k
    exact h d (mem_support_iff.mpr hd) k
  · intro h m hm k
    have := h (mem_support_iff.mp hm)
    rw [weight_blockSingle] at this
    exact congrFun this k

end Homog

section Subst

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}


omit [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem aeval_baseSubst (hv : IsBlockMap κ v) (G : GenFibre v P') (f : MRing ι') :
    aeval (fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩) (baseSubst κ G f) = aeval G.x' f := by
  have h : ((aeval (fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩) :
      MRingOver G.Φ (fibreIdx ι' κ) →ₐ[G.Φ] G.Φ').toRingHom.comp (baseSubst κ G)) =
      (aeval G.x' : MRing ι' →ₐ[ℤ] G.Φ').toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [show (C r : MRing ι') = (r : MRing ι') from eq_intCast C r, map_intCast]
    · intro q
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
      unfold baseSubst
      rw [eval₂Hom_X']
      split_ifs with h h'
      · rw [aeval_C, ← G.compat, h'.choose_spec]
      · exact absurd (hv.2.2.2 q h) h'
      · rw [aeval_X]
  exact DFunLike.congr_fun h f

theorem baseSubst_isMultiHomog (G : GenFibre v P') {s : MRing ι'} {a : K' → ℕ} (hs : IsMultiHomog s a) :
    IsMultiHomog (baseSubst κ G s) (fun k : FibreBlock κ => a k.1) := by
  classical
  rw [isMultiHomog_iff_weighted] at hs ⊢
  have hg : ∀ q : Σ k', ι' k', IsWeightedHomogeneous
      (fun q : Σ k : FibreBlock κ, ι' k.1 => (Pi.single q.1 1 : FibreBlock κ → ℕ))
      (if h : q.1 ∈ Set.range κ then (if h' : q ∈ Set.range v then C (G.x h'.choose) else 0)
        else X ⟨⟨q.1, h⟩, q.2⟩ : MRingOver G.Φ (fibreIdx ι' κ))
      (fun k : FibreBlock κ => (Pi.single q.1 1 : K' → ℕ) k.1) := by
    intro q
    by_cases h : q.1 ∈ Set.range κ
    · have h0 : (fun k : FibreBlock κ => (Pi.single q.1 1 : K' → ℕ) k.1) = 0 := by
        funext k
        have : k.1 ≠ q.1 := fun e => k.2 (e ▸ h)
        simp [this]
      rw [dite_eq_left h, h0]
      split_ifs
      · exact isWeightedHomogeneous_C _ _
      · exact isWeightedHomogeneous_zero _ _ _
    · rw [dite_eq_right h]
      have e : (fun k : FibreBlock κ => (Pi.single q.1 1 : K' → ℕ) k.1) =
          (Pi.single (⟨q.1, h⟩ : FibreBlock κ) 1 : FibreBlock κ → ℕ) := by
        funext k
        simp [Pi.single_apply, Subtype.ext_iff]
      rw [e]
      exact isWeightedHomogeneous_X G.Φ _ (⟨⟨q.1, h⟩, q.2⟩ : Σ k : FibreBlock κ, ι' k.1)
  induction hs using IsWeightedHomogeneous.induction_on with
  | zero => rw [map_zero]; exact isWeightedHomogeneous_zero _ _ _
  | add p q hp hq ihp ihq => rw [map_add (f := _)]; exact ihp.add ihq
  | monomial d r hr =>
    unfold baseSubst
    rw [coe_eval₂Hom, eval₂_monomial, MvPolynomial.algebraMap_apply, Finsupp.prod]
    convert ((IsWeightedHomogeneous.prod d.support _ _ fun q _ => (hg q).pow (d q)).C_mul _) using 1
    funext k
    rw [← hr]
    simp [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]

end Subst

theorem PFFibreSum.proof (hFD : FibreDimStatement) (hBij : PFFibreBij.Statement) (hMult : PFFibreMult.Statement) :
    PFFibreSum.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' d r G J N s a hv hP' hP hJ hNa hs hsP
  classical
  have hV : IsProjVarF (fibreIdeal κ G) (r + 1) := hFD K ι K' ι' κ v P' d (r + 1) G hv hP' hP
  have hmem : ∀ g : MRing ι', baseSubst κ G g ∈ fibreIdeal κ G ↔ g ∈ P' := by
    intro g
    rw [fibreIdeal, RingHom.mem_ker, aeval_baseSubst hv, ← RingHom.mem_ker, G.genericFibre_ker_target]
  have hsec : IsRatSection (fibreIdeal κ G) (fibreDeg κ (N (Fin.last r)).a) (baseSubst κ G s) 1 := by
    refine ⟨fun k => a k.1, 0, baseSubst_isMultiHomog G hs,
      (isMultiHomog_iff_weighted _ _).mpr (isWeightedHomogeneous_one _ _), fun h => hsP ((hmem s).mp h),
      fun h1 => hV.1.1.ne_top ((Ideal.eq_top_iff_one _).mpr h1), fun k => ?_⟩
    simp [fibreDeg, hNa]
  have hb' : J (fibreIdeal κ G) (r + 1) (fun j => fibreDeg κ (N j).a) =
      cycEval (fun W => J W r (fun j => fibreDeg κ (N (Fin.castSucc j)).a))
        (ratDiv (fibreIdeal κ G) (baseSubst κ G s) 1) := by
    rw [← hJ.2 _ r _ _ _ _ hV hsec]
    exact congrArg _ (Fin.snoc_init_self (α := fun _ => FibreBlock κ → ℤ) (fun j => fibreDeg κ (N j).a)).symm
  have hdiv1 : divCycle (fibreIdeal κ G) 1 = 0 := by
    ext W
    simp only [divCycle, Finsupp.ofSupportFinite_coe, Finsupp.coe_zero, Pi.zero_apply]
    rw [if_neg]
    simp [divSupp, Ideal.span_singleton_one, Ideal.minimalPrimes_top]
  set L := fun j : Fin r => fibreDeg κ (N (Fin.castSucc j)).a
  set V := fibreIdeal κ G
  set f := baseSubst κ G s
  have hD : ∀ Q, (divCycle V f Q : ℝ) = if Q ∈ divSupp V f then (multAt (V ⊔ Ideal.span {f}) Q : ℝ) else 0 := by
    intro Q
    simp only [divCycle, Finsupp.ofSupportFinite_coe]
    split_ifs <;> simp

  have hR : ((cycEval (fun W => J W r L) (ratDiv V f 1) : ℤ) : ℝ) =
      ∑ᶠ Q ∈ divSupp V f, (multAt (V ⊔ Ideal.span {f}) Q : ℝ) * (J Q r L : ℝ) := by
    rw [ratDiv, hdiv1, Finsupp.mapRange_zero, sub_zero, cycEval,
      Finsupp.sum_mapRange_index (fun _ => zero_mul _), Finsupp.sum, Int.cast_sum,
      finsum_mem_def]
    simp only [Int.cast_mul, Int.cast_natCast]
    have hsupp : Function.support (fun Q => (divCycle V f Q : ℝ) * (J Q r L : ℝ)) ⊆ ↑(divCycle V f).support := by
      intro Q hQ
      rw [Function.mem_support] at hQ
      rw [Finset.mem_coe, Finsupp.mem_support_iff]
      intro h0
      exact hQ (by rw [h0]; simp)
    rw [← finsum_eq_sum_of_support_subset _ hsupp]
    congr 1
    funext Q
    rw [hD]
    by_cases hQ : Q ∈ divSupp V f <;> simp [hQ, Set.indicator]

  have hL : ∑ᶠ W ∈ divSupp P' s, (multAt (P' ⊔ Ideal.span {s}) W : ℝ) *
        (if IsHorizontal W ∧ imageZ v W = imageZ v P' then (J (fibreOf κ G W) r L : ℝ) else 0) =
      ∑ᶠ W ∈ {W | W ∈ divSupp P' s ∧ IsHorizontal W ∧ imageZ v W = imageZ v P'},
        (multAt (P' ⊔ Ideal.span {s}) W : ℝ) * (J (fibreOf κ G W) r L : ℝ) := by
    rw [finsum_mem_def, finsum_mem_def]
    congr 1
    funext W
    by_cases hW : W ∈ divSupp P' s <;> by_cases hH : IsHorizontal W ∧ imageZ v W = imageZ v P' <;>
      simp [Set.indicator, hW, hH]
  rw [hb', hR, hL]
  refine finsum_mem_eq_of_bijOn (fibreOf κ G) (hBij K ι K' ι' κ v P' d (d + r + 1) G s hv hP' hP) ?_
  rintro W ⟨hW, hH, hI⟩
  rw [hMult K ι K' ι' κ v P' d (d + r + 1) G s W hv hP' hP hW hH hI]

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem divSupp_disjoint_of_not_mem {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {u a : MRing ι} (h : ∀ W ∈ divSupp P u, a ∉ W) :
    ∀ W, W ∈ divSupp P u → W ∉ divSupp P a :=
  fun W hW hW' => h W hW (hW'.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))

theorem isMultiProjPrime_of_mem_divSupp {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} (hP : IsMultiProjPrime P) {u : MRing ι} {b : K → ℕ} (hu : IsMultiHomog u b)
    {W : Ideal (MRing ι)} (hW : W ∈ divSupp P u) : IsMultiProjPrime W :=
  ⟨hW.1.isPrime, ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isMultiHomogIdeal_of_mem_minimalPrimes hP.2.1 hu hW.1, hW.2⟩

theorem WellDefined.proof (h₁ : Swap.Statement) (h₂ : RPositionAdd.Statement) :
    WellDefined.Statement := by
  intro K _ ι _ I P n L B s t hR hA hP hL hB hs ht
  classical
  obtain ⟨bs, hbs, hsH, hsP⟩ := hs
  obtain ⟨bt, hbt, htH, htP⟩ := ht
  have hPm : IsMultiProjPrime P := hP.2.1
  set S : Set (Ideal (MRing ι)) := divSupp P s ∪ divSupp P t ∪ {P} with hSdef
  have hSf : S.Finite :=
    ((divSupp_finite P s).union (divSupp_finite P t)).union (Set.finite_singleton P)
  have hS' : ∀ W ∈ S, IsMultiProjPrime W := by
    rintro W ((hW | hW) | hW)
    · exact isMultiProjPrime_of_mem_divSupp hPm hsH hW
    · exact isMultiProjPrime_of_mem_divSupp hPm htH hW
    · rw [Set.mem_singleton_iff.mp hW]
      exact hPm
  obtain ⟨d₀, hd₀⟩ := AvoidRing.exists_form_avoid S hSf hS'
  set M := L (Fin.last n) with hM
  set k : ℕ := ∑ l, (d₀ l + (M.a l).natAbs) with hkdef
  have hk1 : ∀ l, d₀ l + (M.a l).natAbs ≤ k := fun l =>
    Finset.single_le_sum (f := fun l => d₀ l + (M.a l).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ l)
  set b : K → ℕ := fun l => (M.a l + k).toNat with hbdef
  have hb : ∀ l, (b l : ℤ) = M.a l + k := fun l =>
    Int.toNat_of_nonneg (by have := hk1 l; omega)
  have hbd : d₀ ≤ b := fun l => by
    have h1 := hk1 l
    have h2 := hb l
    show d₀ l ≤ b l
    omega
  have hkd : d₀ ≤ fun _ => k := fun l => by
    have := hk1 l
    show d₀ l ≤ k
    omega
  obtain ⟨a1, ha1H, ha1S⟩ := hd₀ b hbd
  obtain ⟨a2, ha2H, ha2S⟩ := hd₀ _ hkd
  set H : HermLine ι := HermLine.sqMetric (fun _ => k) with hH
  have hHs : IsSmoothHerm H := isSmoothHerm_sqMetric _
  have hMs : IsSmoothHerm M := hL _
  have hA1s : IsSmoothHerm (M.tensor H) := isSmoothHerm_tensor hMs hHs
  have hL' : ∀ j, IsSmoothHerm (Fin.init L j) := fun j => hL _
  have hPS : P ∈ S := Or.inr rfl
  have hsec1 : IsSectionOn P (M.tensor H) a1 :=
    ⟨b, fun l => by rw [hb l]; rfl, ha1H, ha1S P hPS⟩
  have hsec2 : IsSectionOn P H a2 := ⟨fun _ => k, fun l => rfl, ha2H, ha2S P hPS⟩
  have hsecs : IsSectionOn P B s := ⟨bs, hbs, hsH, hsP⟩
  have hsect : IsSectionOn P B t := ⟨bt, hbt, htH, htP⟩
  have d1s := divSupp_disjoint_of_not_mem fun W hW => ha1S W (Or.inl (Or.inl hW))
  have d1t := divSupp_disjoint_of_not_mem fun W hW => ha1S W (Or.inl (Or.inr hW))
  have d2s := divSupp_disjoint_of_not_mem fun W hW => ha2S W (Or.inl (Or.inl hW))
  have d2t := divSupp_disjoint_of_not_mem fun W hW => ha2S W (Or.inl (Or.inr hW))
  have e1s := h₁ K ι I P n (Fin.init L) B (M.tensor H) s a1 hR hP hL' hB hA1s hsecs hsec1 d1s
  have e1t := h₁ K ι I P n (Fin.init L) B (M.tensor H) t a1 hR hP hL' hB hA1s hsect hsec1 d1t
  have e2s := h₁ K ι I P n (Fin.init L) B H s a2 hR hP hL' hB hHs hsecs hsec2 d2s
  have e2t := h₁ K ι I P n (Fin.init L) B H t a2 hR hP hL' hB hHs hsect hsec2 d2t
  have fs := h₂ K ι I P n (Fin.init L) M H B s hA hP hL' hMs hHs hB hsecs
  have ft := h₂ K ι I P n (Fin.init L) M H B t hA hP hL' hMs hHs hB hsect
  have hLeq : L = Fin.snoc (Fin.init L) M := (Fin.snoc_init_self L).symm
  rw [hLeq]
  linarith

end

end GroundTheory.Heights₂.Heights.Inter
end
