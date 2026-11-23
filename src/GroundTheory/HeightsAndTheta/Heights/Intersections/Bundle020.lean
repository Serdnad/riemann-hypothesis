module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle013
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle016
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle014
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
import Mathlib.RingTheory.Henselian
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [∀ k, Fintype (ι k)] in
theorem hermLine_eq_of {A B : HermLine ι} (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  cases A
  cases B
  cases ha
  cases hh
  rfl

theorem isSmoothHerm_tensor {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) :
    IsSmoothHerm (A.tensor B) :=
  hA.mul hB

theorem isSmoothHerm_hermZpow {A : HermLine ι} (hA : IsSmoothHerm A) (m : ℤ) :
    IsSmoothHerm (hermZpow A m) := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · have h : (hermZpow A (n : ℤ)).h = fun z => A.h z ^ n := funext fun z => zpow_natCast (A.h z) n
    unfold IsSmoothHerm
    rw [h]
    exact hA.pow n
  · have h : (hermZpow A (-(n : ℤ))).h = fun z => (A.h z ^ n)⁻¹ :=
      funext fun z => by rw [← zpow_natCast, ← zpow_neg]; rfl
    unfold IsSmoothHerm
    rw [h]
    exact (hA.pow n).inv fun z hz => (pow_pos (A.pos z hz) n).ne'

def famExt (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι)) (n : ℕ)
    (e : Fin 2 → HermLine ι) : MultilinearMap (RingHom.id ℝ) (fun _ : Fin n => Fin 2 → ℝ) ℝ :=
  ∑ s : Fin n → Fin 2,
    I P n (e ∘ s) • (MultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compLinearMap fun j => LinearMap.proj (s j)

section Family

variable {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} {P : Ideal (MRing ι)} {n : ℕ}


omit [∀ k, Fintype (ι k)] in
theorem famExt_apply (e : Fin 2 → HermLine ι) (v : Fin n → Fin 2 → ℝ) :
    famExt I P n e v = ∑ s : Fin n → Fin 2, I P n (e ∘ s) * ∏ j, v j (s j) := by
  simp [famExt, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]


omit [∀ k, Fintype (ι k)] in
theorem famExt_basis (e : Fin 2 → HermLine ι) (t : Fin n → Fin 2) :
    famExt I P n e (fun j => Pi.single (t j) 1) = I P n (e ∘ t) := by
  rw [famExt_apply, Finset.sum_eq_single t]
  · simp
  · intro s _ hs
    obtain ⟨j, hj⟩ : ∃ j, s j ≠ t j := by
      by_contra h
      push Not at h
      exact hs (funext h)
    rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj]), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ t) h

theorem famExt_symm (hI : IsIntersectionFamily I) (hP : IsArithVar P n) (e : Fin 2 → HermLine ι)
    (he : ∀ i, IsSmoothHerm (e i)) : IsSymmForm (famExt I P n e) := by
  intro σ v
  rw [famExt_apply, famExt_apply]
  refine Fintype.sum_equiv (Equiv.arrowCongr σ (Equiv.refl (Fin 2))) _ _ fun s => ?_
  have h1 : e ∘ (Equiv.arrowCongr σ (Equiv.refl (Fin 2)) s) = (e ∘ s) ∘ σ.symm := rfl
  have h2 : ∏ j, v j ((Equiv.arrowCongr σ (Equiv.refl (Fin 2)) s) j) = ∏ j, (v ∘ σ) j (s j) := by
    refine (Equiv.prod_comp σ fun j => v j (s (σ.symm j))).symm.trans ?_
    simp
  rw [h1, h2, hI.1 P n (e ∘ s) σ.symm hP fun j => he _]

theorem fam_snoc_zpow_zero (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1))
    (L : Fin n → HermLine ι) (hL : ∀ j, IsSmoothHerm (L j)) {X : HermLine ι} (hX : IsSmoothHerm X) :
    I P (n + 1) (Fin.snoc L (hermZpow X 0)) = 0 := by
  have e : (hermZpow X 0).tensor (hermZpow X 0) = hermZpow X 0 :=
    hermLine_eq_of (by simp [HermLine.tensor, hermZpow]) (by funext z; simp [HermLine.tensor, hermZpow])
  have h := hI.2.1 P n L _ _ hP hL (isSmoothHerm_hermZpow hX 0) (isSmoothHerm_hermZpow hX 0)
  rw [e] at h
  linarith

theorem fam_snoc_zpow_nat (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1))
    (L : Fin n → HermLine ι) (hL : ∀ j, IsSmoothHerm (L j)) {X : HermLine ι} (hX : IsSmoothHerm X) (k : ℕ) :
    I P (n + 1) (Fin.snoc L (hermZpow X k)) = k * I P (n + 1) (Fin.snoc L X) := by
  induction k with
  | zero =>
    simp only [Nat.cast_zero, zero_mul]
    exact fam_snoc_zpow_zero hI hP L hL hX
  | succ k ih =>
    have e : hermZpow X ((k + 1 : ℕ) : ℤ) = (hermZpow X k).tensor X :=
      hermLine_eq_of (by simp [HermLine.tensor, hermZpow, add_smul])
        (funext fun z => by
          show X.h z ^ ((k + 1 : ℕ) : ℤ) = X.h z ^ (k : ℤ) * X.h z
          rw [zpow_natCast, zpow_natCast, pow_succ])
    rw [e, hI.2.1 P n L _ _ hP hL (isSmoothHerm_hermZpow hX k) hX, ih]
    push_cast
    ring

theorem fam_snoc_zpow (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1))
    (L : Fin n → HermLine ι) (hL : ∀ j, IsSmoothHerm (L j)) {X : HermLine ι} (hX : IsSmoothHerm X) (m : ℤ) :
    I P (n + 1) (Fin.snoc L (hermZpow X m)) = m * I P (n + 1) (Fin.snoc L X) := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · rw [fam_snoc_zpow_nat hI hP L hL hX k, Int.cast_natCast]
  · have hs : ∀ m : ℤ, IsSmoothHerm (hermZpow X m) := isSmoothHerm_hermZpow hX
    have hsum := hI.2.1 P n L _ _ hP hL (hs (-k)) (hs k)
    have h1 : (1 : MRing ι) ∉ P := (Ideal.ne_top_iff_one P).mp hP.2.1.1.ne_top
    have hh : IsMultiHomog (1 : MRing ι) (0 : K → ℕ) := by
      intro d hd k'
      rw [MvPolynomial.support_one, Finset.mem_singleton] at hd
      subst hd
      simp
    have hT : I P (n + 1) (Fin.snoc L ((hermZpow X (-k)).tensor (hermZpow X k))) =
        I P (n + 1) (Fin.snoc L (hermZpow X 0)) := by
      rw [hI.2.2 P n L _ 1 0 hP hL (isSmoothHerm_tensor (hs _) (hs _))
          (fun k' => by simp [HermLine.tensor, hermZpow]) hh h1,
        hI.2.2 P n L _ 1 0 hP hL (hs 0) (fun k' => by simp [hermZpow]) hh h1, recR_eq, recR_eq]
      congr 1
      unfold arInt
      congr 1
      funext z
      unfold logNorm
      simp only [map_one, norm_one]
      show Real.log (1 / (X.h z ^ (-(k : ℤ)) * X.h z ^ (k : ℤ))) = Real.log (1 / X.h z ^ (0 : ℤ))
      rcases eq_or_ne (X.h z) 0 with hx | hx
      · rw [hx]
        rcases eq_or_ne k 0 with rfl | hk
        · simp
        · rw [zero_zpow (k : ℤ) (by exact_mod_cast hk), mul_zero]
          simp
      · rw [zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ hx)]
        simp
    rw [hT, fam_snoc_zpow_zero hI hP L hL hX, fam_snoc_zpow_nat hI hP L hL hX k] at hsum
    push_cast
    linarith

theorem fam_update_eq_snoc (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1))
    (L : Fin (n + 1) → HermLine ι) (hL : ∀ j, IsSmoothHerm (L j)) (a : Fin (n + 1)) {B : HermLine ι}
    (hB : IsSmoothHerm B) :
    I P (n + 1) (Function.update L a B) =
      I P (n + 1) (Fin.snoc (fun i : Fin n => L (Equiv.swap a (Fin.last n) i.castSucc)) B) := by
  have hs : ∀ j, IsSmoothHerm (Function.update L a B j) := by
    intro j
    rcases eq_or_ne j a with rfl | h
    · rwa [Function.update_self]
    · rw [Function.update_of_ne h]
      exact hL j
  rw [← hI.1 P (n + 1) _ (Equiv.swap a (Fin.last n)) hP hs]
  congr 1
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp
  · rw [Function.comp_apply, Fin.snoc_castSucc, Function.update_of_ne]
    intro h
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at h
    exact Fin.castSucc_ne_last i h

end Family

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem ChartNormPts.proof : ChartNormPts.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' G j hv hP' hj z' hw hz1
  classical
  have hcast : ∀ p : MRing ι', eval z' (map (Int.castRingHom ℂ) p) = aeval z' p := fun p => by
    rw [eval_map, aeval_def, algebraMap_int_eq]
  have hcoef : (eval₂Hom (Int.castRingHom ℂ) fun p => z' (v p)) =
      (aeval (z' ∘ v) : MRing ι →ₐ[ℤ] ℂ).toRingHom := by
    ext c
    · simp
    · simp
  have hφ : (algebraMap G.Φ G.Φ').comp (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom =
      (aeval (G.x' ∘ v) : MRing ι →ₐ[ℤ] G.Φ').toRingHom := by
    ext c
    · simp
    · simp [G.compat]
  rw [hφ, hcoef]
  constructor
  · intro hz F hF
    have hH : ChartNormPts.homogenise v (fun q : Σ k : FibreBlock κ, ι' k.1 => (⟨q.1.1, q.2⟩ : Σ k', ι' k'))
        (fun q => ⟨q.1.1, j q.1⟩) F ∈ P' := by
      rw [← G.genericFibre_ker_target, RingHom.mem_ker]
      show aeval G.x' _ = 0
      rw [ChartNormPts.aeval_homogenise_div v _ _ F G.x' fun q => hj q.1, hF, mul_zero]
    have h0 := hz.2 _ hH
    rwa [hcast, ChartNormPts.aeval_homogenise_one v _ _ F z' fun q => hz1 q.1] at h0
  · intro hF
    refine ⟨fun k' => ?_, fun f hf => ?_⟩
    · by_cases h : k' ∈ Set.range κ
      · obtain ⟨k, rfl⟩ := h
        obtain ⟨i, hi⟩ := hw.1 k
        replace hi : z' (v ⟨k, i⟩) ≠ 0 := hi
        revert hi
        generalize hq : v ⟨k, i⟩ = q
        obtain ⟨k₀, i₀⟩ := q
        intro hi
        have e : k₀ = κ k := by rw [← hv.2.2.1 ⟨k, i⟩, hq]
        subst e
        exact ⟨i₀, hi⟩
      · exact ⟨j ⟨k', h⟩, by rw [hz1 ⟨k', h⟩]; exact one_ne_zero⟩
    obtain ⟨S, hS, rfl⟩ := hP'
    suffices hle : Ideal.span S ≤ RingHom.ker (aeval z' : MRing ι' →ₐ[ℤ] ℂ) by
      rw [hcast]; exact hle hf
    rw [Ideal.span_le]
    intro g hg
    obtain ⟨a, ha⟩ := hS g hg
    let σ : (Σ k', ι' k') → MvPolynomial (Σ k : FibreBlock κ, ι' k.1) (MRing ι) := fun q' =>
      if h : q'.1 ∈ Set.range κ then C (X (hv.2.2.2 q' h).choose) else X ⟨⟨q'.1, h⟩, q'.2⟩
    have hcomp : ∀ {R : Type} [CommRing R] (ψ : MvPolynomial (Σ k : FibreBlock κ, ι' k.1) (MRing ι) →+* R),
        ψ (aeval σ g) = aeval (fun q' => ψ (σ q')) g := fun ψ =>
      comp_aeval_apply (f := σ) ψ.toIntAlgHom g
    have h1 := hF (aeval σ g)
    rw [← coe_eval₂Hom, ← coe_eval₂Hom, hcomp, hcomp] at h1
    let c : K' → G.Φ' := fun k' => if h : k' ∈ Set.range κ then 1 else (G.x' ⟨k', j ⟨k', h⟩⟩)⁻¹
    have hx : (fun q' => eval₂Hom (aeval (G.x' ∘ v) : MRing ι →ₐ[ℤ] G.Φ').toRingHom
        (fun q => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩) (σ q')) = fun q' => c q'.1 * G.x' q' := by
      funext q'
      by_cases h : q'.1 ∈ Set.range κ
      · simp only [σ, c, dif_pos h, coe_eval₂Hom, eval₂_C, one_mul]
        simp [(hv.2.2.2 q' h).choose_spec]
      · simp only [σ, c, dif_neg h, coe_eval₂Hom, eval₂_X]
        rw [div_eq_inv_mul]
    have hz : (fun q' => eval₂Hom (aeval (z' ∘ v) : MRing ι →ₐ[ℤ] ℂ).toRingHom
        (fun q => z' ⟨q.1.1, q.2⟩) (σ q')) = z' := by
      funext q'
      by_cases h : q'.1 ∈ Set.range κ
      · simp only [σ, dif_pos h, coe_eval₂Hom, eval₂_C]
        simp [(hv.2.2.2 q' h).choose_spec]
      · simp only [σ, dif_neg h, coe_eval₂Hom, eval₂_X]
    rw [hx, hz, ChartNormPts.aeval_smul_homog g a ha] at h1
    have hg0 : aeval G.x' g = 0 := by
      have : g ∈ RingHom.ker (aeval G.x' : MRing ι' →ₐ[ℤ] G.Φ') := by
        rw [G.genericFibre_ker_target]; exact Ideal.subset_span hg
      exact this
    exact h1 (by rw [hg0, mul_zero])

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem FibreDimensionZero.proof (h₁ : ArithmeticIntersectionFibreMultiHomogeneous.Statement) (h₂ : EvalKerKrullDim.Statement)
    (h₃ : FibreTranscendenceDegreeAlt.Statement) : FibreDimensionZero.Statement := by
  intro K _ ι _ K' _ ι' _ κ v p _ W' n hv hp hW hV G'
  refine ⟨⟨RingHom.ker_isPrime _, h₁ K ι K' ι' κ v p W' hv hp hW.1.2.1 G', fun k => ?_⟩, ?_⟩
  · obtain ⟨i, hi⟩ := hW.1.2.2 k.1
    refine ⟨i, fun h => hi ?_⟩
    rw [fibreIdeal, RingHom.mem_ker, aeval_X] at h
    have hX : (X ⟨k.1, i⟩ : MRing ι') ∈ W' := by
      rw [← G'.genericFibre_ker_target, RingHom.mem_ker, aeval_X]
      exact h
    simpa using Ideal.mem_map_of_mem (MvPolynomial.map (Int.castRingHom (ZMod p))) hX
  · rw [fibreIdeal, h₂ (FibreBlock κ) (fibreIdx ι' κ) G'.Φ G'.Φ', h₃ K ι K' ι' κ v p W' n hv hp hW hV G']
    simp

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GenericPointsAvoidBadLocus

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]


omit [Fintype K] in
theorem isMultiHomog_prod_int {β : Type*} (s : Finset β) (f : β → MRing ι) (a : β → K → ℕ)
    (h : ∀ b ∈ s, IsMultiHomog (f b) (a b)) : IsMultiHomog (∏ b ∈ s, f b) (∑ b ∈ s, a b) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro m hm k
    rw [Finset.prod_empty, MvPolynomial.support_one, Finset.mem_singleton] at hm
    subst hm
    simp
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, Finset.sum_insert hb]
    intro m hm k
    obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm)
    have h1 := h b (Finset.mem_insert_self b s) m1 hm1 k
    have h2 := ih (fun b' hb' => h b' (Finset.mem_insert_of_mem hb')) m2 hm2 k
    simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, h1, h2]


omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem adjoin_chart_le {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}
    (G : GenFibre v P') (i j : ∀ k : FibreBlock κ, ι' k.1) (hi : ∀ k : FibreBlock κ, G.x' ⟨k.1, i k⟩ ≠ 0) :
    IntermediateField.adjoin G.Φ
        (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩) ≤
      IntermediateField.adjoin G.Φ
        (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩) := by
  rw [IntermediateField.adjoin_le_iff]
  rintro _ ⟨q, rfl⟩
  have hq : G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩ =
      (G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩) / (G.x' ⟨q.1.1, j q.1⟩ / G.x' ⟨q.1.1, i q.1⟩) :=
    (div_div_div_cancel_right₀ (hi q.1) _ _).symm
  show G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩ ∈ _
  rw [hq]
  exact div_mem (IntermediateField.subset_adjoin _ _ ⟨q, rfl⟩)
    (IntermediateField.subset_adjoin _ _ ⟨⟨q.1, j q.1⟩, rfl⟩)

end GenericPointsAvoidBadLocus


open GenericPointsAvoidBadLocus in
theorem GenericPointsAvoidBadLocus.proof (hChart : GenericPointsInAffineChart.Statement) : GenericPointsAvoidBadLocus.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n G i hv hP' hZ hi
  classical
  let C := {j : ∀ k : FibreBlock κ, ι' k.1 // ∀ k : FibreBlock κ, G.x' ⟨k.1, j k⟩ ≠ 0}
  choose D a hD hDZ hpts using fun j : C => hChart K ι K' ι' κ v P' n G j.1 hv hP' hZ j.2
  have hprime : (imageZ v P').IsPrime := hZ.2.1.1
  refine ⟨∏ j, D j, ∑ j, a j, isMultiHomog_prod_int _ _ _ fun j _ => hD j, fun hmem => ?_, ?_⟩
  · obtain ⟨j, -, hj⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hDZ j hj
  intro z hz hDz
  have hDj : ∀ j : C, eval z (map (Int.castRingHom ℂ) (D j)) ≠ 0 := by
    intro j h0
    apply hDz
    rw [map_prod, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ j) h0
  let i0 : C := ⟨i, hi⟩
  have hEq : ∀ j : C, ptsOverChart P' κ v i z = ptsOverChart P' κ v j.1 z := by
    intro j
    have hci : (ptsOverChart P' κ v i z).ncard = Module.finrank G.Φ (IntermediateField.adjoin G.Φ
        (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩)) :=
      (hpts i0 z hz (hDj i0)).2.1
    obtain ⟨hfin, hcj, -⟩ := hpts j z hz (hDj j)
    have hsub : ptsOverChart P' κ v i z ⊆ ptsOverChart P' κ v j.1 z := by
      rintro O ⟨z', hz', rfl, hw, hc⟩
      exact ⟨z', hz', rfl, hw, fun k => (hpts i0 z hz (hDj i0)).2.2 z' hz' hw hc ⟨k, j.1 k⟩ (j.2 k)⟩
    refine Set.eq_of_subset_of_ncard_le hsub (le_of_eq ?_) hfin
    rw [hcj, hci, le_antisymm (adjoin_chart_le G i j.1 hi) (adjoin_chart_le G j.1 i j.2)]
  have hall : ptsOverPt P' v z = ptsOverChart P' κ v i z := by
    ext O
    constructor
    · rintro ⟨z', hz', rfl, hw⟩
      choose ℓ hℓ using fun k : FibreBlock κ => hz'.1 k.1
      have hgen : ∀ k : FibreBlock κ, G.x' ⟨k.1, ℓ k⟩ ≠ 0 := by
        intro k h0
        apply hℓ k
        have hmem : (X ⟨k.1, ℓ k⟩ : MRing ι') ∈ P' := by
          rw [← G.genericFibre_ker_target, RingHom.mem_ker]
          simpa using h0
        simpa using hz'.2 _ hmem
      rw [hEq ⟨ℓ, hgen⟩]
      exact ⟨z', hz', rfl, hw, hℓ⟩
    · rintro ⟨z', hz', rfl, hw, -⟩
      exact ⟨z', hz', rfl, hw⟩
  rw [hall]
  exact (hpts i0 z hz (hDj i0)).2.1

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M

open ReciprocityTheory.ChartRestriction.G in
def pullbackDensity_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' J' : Ideal (MRing ι')) (n : ℕ)
    (R : AnLogRes P' J' n) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (L : Fin n → Geo.HermLine ι) (L' : Fin n → Geo.HermLine ι')
    (A : Geo.HermLine ι) (A' : Geo.HermLine ι') (s : MRing ι),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) → IsGoodProj (imageZ v P') Ψ →
    (∀ j, Geo.IsSmoothHerm (L j)) → (∀ j, AI.I4.IsPullHerm κ v (L j) (L' j)) →
    Geo.IsSmoothHerm A → AI.I4.IsPullHerm κ v A A' → Geo.IsSectionOn (imageZ v P') A s →
    ∀ᵐ y : Fin n → ℂ, ∀ x ∈ pullQ R v Ψ ⁻¹' {y} \ pullBad R v Ψ,
      Geo.logNorm A' (rename v s) (R.lift x x) * pushDens R.A (fun j => Geo.potOf R (L' j)) (pullQ R v Ψ) x =
        sheetDensity (imageZ v P') Ψ (Geo.pot L) (Geo.logNorm A s) y (pullW R v Ψ x)

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end
