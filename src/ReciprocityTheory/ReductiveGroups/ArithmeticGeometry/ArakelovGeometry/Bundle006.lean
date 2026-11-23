module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle002
public import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsSmoothPts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
public import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle005
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.KrullDimension.PID

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module

variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J]

theorem aeval_map_int (x : J → Ω) (f : MvPolynomial J ℤ) :
    aeval x (map (Int.castRingHom ℚ) f) = aeval x f := by
  rw [aeval_def, eval₂_map, aeval_def]
  congr 1 <;> exact RingHom.ext_int _ _

theorem eval_smul_of_homog {R : Type*} [CommRing R] {φ : MvPolynomial J R} {d : ℕ}
    (hφ : φ.IsHomogeneous d) (c : R) (z : J → R) : eval (c • z) φ = c ^ d * eval z φ := by
  conv_lhs => rw [φ.as_sum]
  conv_rhs => rw [φ.as_sum]

  simp only [map_sum, Finset.mul_sum, eval_monomial]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hd : ∑ i ∈ s.support, s i = d := by
    have := hφ (mem_support_iff.mp hs)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [Finsupp.prod, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hd]
  ring

theorem secFun_smul {b : MvPolynomial J ℚ} {n : ℕ}
    (hb : ∃ f : MvPolynomial J ℤ, f.IsHomogeneous n ∧ b = map (Int.castRingHom ℚ) f)
    (c : ℂ) (z : J → ℂ) : secFun b (c • z) = c ^ n * secFun b z := by
  obtain ⟨f, hf, rfl⟩ := hb
  have hmap : map (algebraMap ℚ ℂ) (map (Int.castRingHom ℚ) f) = map (Int.castRingHom ℂ) f := by
    rw [map_map]
    congr 1 <;> exact RingHom.ext_int _ _
  simp only [secFun, hmap]
  exact eval_smul_of_homog (hf.map _) c z

theorem continuous_secFun (b : MvPolynomial J ℚ) : Continuous (secFun b) := by
  unfold secFun
  exact MvPolynomial.continuous_eval _

theorem secFun_map_int (f : MvPolynomial J ℤ) (z : J → ℂ) :
    secFun (map (Int.castRingHom ℚ) f) z = eval z (map (Int.castRingHom ℂ) f) := by
  unfold secFun
  rw [map_map]
  congr 2 <;> exact RingHom.ext_int _ _

theorem secFun_eq_zero_of_pts {x : J → Ω} {n : ℕ} {d : MvPolynomial J ℤ} (hd : d.IsHomogeneous n)
    (h0 : aeval x d = 0) {z : J → ℂ} (hz : z ∈ pts (coordIdeal ℤ x)) :
    secFun (map (Int.castRingHom ℚ) d) z = 0 := by
  have hmem : d ∈ coordIdeal ℤ x := by
    unfold coordIdeal coneMap
    rw [RingHom.mem_ker, aeval_def, ← eval_map]
    have hpt : (fun i => Polynomial.C (x i) * Polynomial.X) =
        (Polynomial.X : Polynomial Ω) • fun i => Polynomial.C (x i) := by
      funext i
      exact mul_comm _ _
    have hC : eval (fun i => Polynomial.C (x i)) (map (algebraMap ℤ (Polynomial Ω)) d) =
        Polynomial.C (aeval x d) := by
      rw [eval_map, aeval_def, hom_eval₂]
      congr 1 <;> exact RingHom.ext_int _ _
    rw [hpt, eval_smul_of_homog (hd.map _), hC, h0, map_zero, mul_zero]
  rw [secFun_map_int]
  exact hz.2 d hmem

theorem secFun_conjPt (b : MvPolynomial J ℚ) (z : J → ℂ) :
    secFun b (conjPt z) = starRingEnd ℂ (secFun b z) := by
  simp only [secFun, eval_map, hom_eval₂]
  rw [RingHom.ext_rat ((starRingEnd ℂ).comp (algebraMap ℚ ℂ)) (algebraMap ℚ ℂ)]
  rfl

theorem continuous_conjPt : Continuous (conjPt : (J → ℂ) → J → ℂ) := by
  exact continuous_pi fun i => Complex.continuous_conj.comp (continuous_apply i)

def conjEquiv (J : Type) [Fintype J] : (J → ℂ) ≃ᵐ (J → ℂ) where
  toFun := conjPt
  invFun := conjPt
  left_inv z := by funext i; simp [conjPt]
  right_inv z := by funext i; simp [conjPt]
  measurable_toFun := continuous_conjPt.measurable
  measurable_invFun := continuous_conjPt.measurable

theorem wgt_conjPt {m : ConeMetric (C := ℂ) (ι := J)} (hm : IsConjInvariant m) (n : ℕ) (z : J → ℂ) :
    wgt m n (conjPt z) = wgt m n z := by
  unfold wgt conjPt
  rw [hm z]

theorem conj_bGram {m : ConeMetric (C := ℂ) (ι := J)} {μ : Measure (J → ℂ)} (hm : IsConjInvariant m)
    (hμ : μ.map conjPt = μ) (n : ℕ) {r : ℕ} (b : Fin r → MvPolynomial J ℚ) (i j : Fin r) :
    starRingEnd ℂ (bGram μ (fun k => secFun (b k)) (wgt m n) i j) =
      bGram μ (fun k => secFun (b k)) (wgt m n) i j := by
  have hμ' : μ.map (conjEquiv J) = μ := hμ
  have he : ∀ x, conjEquiv J x = conjPt x := fun x => rfl
  simp only [bGram, Matrix.of_apply]
  rw [← integral_conj]
  conv_rhs => rw [← hμ']
  rw [integral_map_equiv (conjEquiv J)]
  congr 1
  funext x
  simp [he, secFun_conjPt, wgt_conjPt hm]
  try ring

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

theorem ringKrullDim_le_of_isIntegral' {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] : ringKrullDim S ≤ ringKrullDim R := by
  unfold ringKrullDim
  refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) ?_
  intro P Q hPQ
  exact Ideal.IsIntegral.comap_lt_comap (I := P.asIdeal) (J := Q.asIdeal) hPQ

section Arith

variable {Ω : Type*} [Field Ω] [CharZero Ω]

theorem X_mem_coordIdeal_iff {J : Type} (v : J → Ω) (i : J) :
    (X i : MvPolynomial J ℤ) ∈ coordIdeal ℤ v ↔ v i = 0 := by
  rw [coordIdeal, RingHom.mem_ker, coneMap, aeval_X, mul_eq_zero, Polynomial.C_eq_zero]
  simp [Polynomial.X_ne_zero]

theorem isHorizontal_coordIdeal {κ : Type} (v : Ix κ → Ω) :
    IsHorizontal (ι := GlobalTheory κ) (coordIdeal ℤ v) := by
  rw [IsHorizontal, eq_bot_iff]
  intro n hn
  rw [Ideal.mem_comap, coordIdeal, RingHom.mem_ker, coneMap, aeval_C] at hn
  rw [Submodule.mem_bot]
  simpa using hn

theorem isMultiHomogIdeal_coordIdeal {κ : Type} [Fintype κ] (v : Ix κ → Ω) :
    IsMultiHomogIdeal (ι := GlobalTheory κ) (coordIdeal ℤ v) := by
  refine ⟨{f | f ∈ coordIdeal ℤ v ∧ ∃ n, f.IsHomogeneous n}, ?_, ?_⟩
  · rintro f ⟨_, n, hn⟩
    refine ⟨fun _ => n, fun m hm k => ?_⟩
    have h1 : Finsupp.degree m = n := by
      rw [Finsupp.degree_eq_weight_one]
      exact hn (mem_support_iff.mp hm)
    rw [Finsupp.degree_eq_sum, Fintype.sum_sigma] at h1
    cases k
    simpa using h1
  · apply le_antisymm
    · intro f hf
      rw [← sum_homogeneousComponent f]
      exact Ideal.sum_mem _ fun d _ => Ideal.subset_span
        ⟨coordIdeal_isHomogIdeal ℤ v f hf d, d, homogeneousComponent_isHomogeneous d f⟩
    · exact Ideal.span_le.mpr fun f hf => hf.1

theorem coneMap_rename {J J' : Type} (v : J → Ω) (e : J' → J) (p : MvPolynomial J' ℤ) :
    coneMap ℤ v (rename e p) = coneMap ℤ (v ∘ e) p := by
  rw [coneMap, coneMap, aeval_rename]
  rfl

end Arith

section Dim

variable {Ω : Type*} [Field Ω] [CharZero Ω] {J : Type} [Fintype J] {D : ℕ}

theorem isIntegralElem_of_comp {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (val : S →+* T) (hval : Function.Injective val) {s : S}
    (h : (val.comp f).IsIntegralElem (val s)) : f.IsIntegralElem s := by
  obtain ⟨p, hp, he⟩ := h
  refine ⟨p, hp, hval ?_⟩
  rw [map_zero, ← he, Polynomial.hom_eval₂]

theorem isIntegralElem_coneMap (v : J → Ω) (e : Fin (D + 1) → J) (hf : IsProjFrame v e)
    (q : MvPolynomial J ℤ) :
    (coneMap ℤ (v ∘ e) : MvPolynomial (Fin (D + 1)) ℤ →+* Polynomial Ω).IsIntegralElem
      (coneMap ℤ v q) := by
  have hinj : Function.Injective (coneMap ℤ (v ∘ e)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro p hp
    have : p ∈ coordIdeal ℤ (v ∘ e) := by simpa [coordIdeal, RingHom.mem_ker] using hp
    rw [hf.free] at this
    exact (Ideal.mem_bot).mp this
  set φ := AlgEquiv.ofInjective (coneMap ℤ (v ∘ e)) hinj
  have hgen : ∀ i, (coneMap ℤ (v ∘ e) : MvPolynomial (Fin (D + 1)) ℤ →+* Polynomial Ω).IsIntegralElem
      (Polynomial.C (v i) * Polynomial.X) := by
    intro i
    have hi : IsIntegral (coneMap ℤ (v ∘ e)).range (Polynomial.C (v i) * Polynomial.X : Polynomial Ω) :=
      hf.integral i
    obtain ⟨p, hp, hps⟩ := hi
    refine ⟨p.map φ.symm.toRingEquiv.toRingHom,
      hp.map _, ?_⟩
    have hcomp : ((coneMap ℤ (v ∘ e) : MvPolynomial (Fin (D + 1)) ℤ →+* Polynomial Ω).comp
        φ.symm.toRingEquiv.toRingHom) = algebraMap (coneMap ℤ (v ∘ e)).range (Polynomial Ω) := by
      refine RingHom.ext fun r => ?_
      have h1 : ((φ (φ.symm r) : (coneMap ℤ (v ∘ e)).range) : Polynomial Ω) =
          coneMap ℤ (v ∘ e) (φ.symm r) := rfl
      rw [AlgEquiv.apply_symm_apply] at h1
      exact h1.symm
    rw [Polynomial.eval₂_map, hcomp]
    exact hps
  induction q using MvPolynomial.induction_on with
  | C a =>
    have : coneMap ℤ v (C a) = coneMap ℤ (v ∘ e) (C a) := by simp
    rw [this]
    exact RingHom.isIntegralElem_map _
  | add p q hp hq =>
    rw [map_add (f := _)]
    exact RingHom.IsIntegralElem.add _ hp hq
  | mul_X p i hp =>
    rw [map_mul]
    refine RingHom.IsIntegralElem.mul _ hp ?_
    simpa [coneMap] using hgen i

theorem coneMap_injective_of_frame (v : J → Ω) (e : Fin (D + 1) → J) (hf : IsProjFrame v e) :
    Function.Injective (coneMap ℤ (v ∘ e)) := by
  exact (injective_iff_map_eq_zero _).2 fun p hp => by
    have h : p ∈ coordIdeal ℤ (v ∘ e) := (RingHom.mem_ker).2 hp
    rwa [hf.free, Ideal.mem_bot] at h

theorem ringKrullDim_mvPoly_fin_int :
    ringKrullDim (MvPolynomial (Fin (D + 1)) ℤ) = ((D + 2 : ℕ) : WithBot ℕ∞) := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField,
    Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [show ((D + 2 : ℕ) : WithBot ℕ∞) = 1 + ((D + 1 : ℕ) : WithBot ℕ∞) by norm_cast; omega]

theorem ringKrullDim_quot_of_frame (v : J → Ω) (e : Fin (D + 1) → J) (hf : IsProjFrame v e) :
    ringKrullDim (MvPolynomial J ℤ ⧸ coordIdeal ℤ v) = ((D + 2 : ℕ) : WithBot ℕ∞) := by
  have hq : ringKrullDim (MvPolynomial J ℤ ⧸ coordIdeal ℤ v) =
      ringKrullDim (coneMap ℤ v).range :=
    ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerEquivRange (coneMap ℤ v)).toRingEquiv
  let f : MvPolynomial (Fin (D + 1)) ℤ →+* (coneMap ℤ v).range :=
    ((coneMap ℤ v).rangeRestrict.comp (rename e)).toRingHom
  have hvalf : ((coneMap ℤ v).range.val : (coneMap ℤ v).range →+* Polynomial Ω).comp f =
      (coneMap ℤ (v ∘ e) : MvPolynomial (Fin (D + 1)) ℤ →+* Polynomial Ω) := by
    refine RingHom.ext fun p => ?_
    simp [f, coneMap_rename]
  have hinj : Function.Injective f := by
    intro a b hab
    apply coneMap_injective_of_frame v e hf
    have := congrArg ((coneMap ℤ v).range.val : (coneMap ℤ v).range →+* Polynomial Ω) hab
    rw [← RingHom.comp_apply, ← RingHom.comp_apply, hvalf] at this
    exact this
  have hint : f.IsIntegral := fun s => by
    obtain ⟨q, hq⟩ := s.2
    apply isIntegralElem_of_comp f ((coneMap ℤ v).range.val : (coneMap ℤ v).range →+* Polynomial Ω)
      Subtype.val_injective
    rw [hvalf]
    change RingHom.IsIntegralElem _ (s : Polynomial Ω)
    rw [← hq]
    exact isIntegralElem_coneMap v e hf q
  rw [hq]
  apply le_antisymm
  · let _ := f.toAlgebra
    have : Algebra.IsIntegral (MvPolynomial (Fin (D + 1)) ℤ) (coneMap ℤ v).range := ⟨hint⟩
    rw [← ringKrullDim_mvPoly_fin_int]
    exact ringKrullDim_le_of_isIntegral'
  · exact le_ringKrullDim_of_isIntegral f hint hinj _ ringKrullDim_mvPoly_fin_int.ge

end Dim

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end
