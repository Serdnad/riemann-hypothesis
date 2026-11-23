module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.IsTop
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.RtrPoly
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free

@[expose] public section

section

open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.topPol :
    ∀ (n : ℕ) (ν : Fin n → ℕ), Antitone ν → ∀ H : ℕ, (∀ k, ν k ≤ H) → ∃ f : Pol n, f ≠ 0 ∧ f.totalDegree ≤ n * H ∧
      ∀ b : Matrix (Fin n) (Fin n) ℂ, (∀ i j, j < i → b i j = 0) → rtr b f = (∏ k, b k k ^ ν k) • f := by
  intro n ν hν H hH
  classical
  have hmem : ∀ (h : ℕ) (hs : (Finset.univ.filter (fun i : Fin n => h < ν i)).Nonempty) (i : Fin n),
      i ∈ Finset.univ.filter (fun i : Fin n => h < ν i) ↔ i ≤ (Finset.univ.filter (fun i : Fin n => h < ν i)).max' hs := by
    intro h hs i
    constructor
    · intro hi
      exact Finset.le_max' _ _ hi
    · intro hi
      have hm := Finset.max'_mem _ hs
      rw [Finset.mem_filter] at hm ⊢
      exact ⟨Finset.mem_univ _, lt_of_lt_of_le hm.2 (hν hi)⟩
  obtain ⟨g, hg1, hg2, hg3⟩ : ∃ g : ℕ → Pol n, (∀ h, g h ≠ 0) ∧ (∀ h, (g h).totalDegree ≤ n) ∧
      ∀ b : Matrix (Fin n) (Fin n) ℂ, (∀ i j, j < i → b i j = 0) → ∀ h,
        rtr b (g h) = (∏ i ∈ Finset.univ.filter (fun i : Fin n => h < ν i), b i i) • g h := by
    refine ⟨fun h => if hs : (Finset.univ.filter (fun i : Fin n => h < ν i)).Nonempty then
      minor ((Finset.univ.filter (fun i : Fin n => h < ν i)).max' hs) else 1, ?_, ?_, ?_⟩
    · intro h
      by_cases hs : (Finset.univ.filter (fun i : Fin n => h < ν i)).Nonempty
      · simp only [dite_eq_left hs]
        exact (minorDeg n _).1
      · simp only [dite_eq_right hs]
        exact one_ne_zero
    · intro h
      by_cases hs : (Finset.univ.filter (fun i : Fin n => h < ν i)).Nonempty
      · simp only [dite_eq_left hs]
        have h1 := (minorDeg n ((Finset.univ.filter (fun i : Fin n => h < ν i)).max' hs)).2
        have h2 := ((Finset.univ.filter (fun i : Fin n => h < ν i)).max' hs).isLt
        omega
      · simp only [dite_eq_right hs, MvPolynomial.totalDegree_one]
        exact Nat.zero_le _
    · intro b hb h
      by_cases hs : (Finset.univ.filter (fun i : Fin n => h < ν i)).Nonempty
      · simp only [dite_eq_left hs]
        rw [minorRtr n _ b hb]
        congr 1
        apply Finset.prod_congr _ (fun _ _ => rfl)
        ext i
        rw [hmem h hs i, Finset.mem_filter]
        simp
      · simp only [dite_eq_right hs]
        rw [Finset.not_nonempty_iff_eq_empty.mp hs]
        simp
  refine ⟨∏ h ∈ Finset.range H, g h, ?_, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr (fun h _ => hg1 h)
  · calc (∏ h ∈ Finset.range H, g h).totalDegree ≤ ∑ h ∈ Finset.range H, (g h).totalDegree :=
          MvPolynomial.totalDegree_finsetProd _ _
      _ ≤ ∑ h ∈ Finset.range H, n := Finset.sum_le_sum (fun h _ => hg2 h)
      _ = n * H := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]
  · intro b hb
    have key : ∏ h ∈ Finset.range H, ∏ i ∈ Finset.univ.filter (fun i : Fin n => h < ν i), b i i =
        ∏ k, b k k ^ ν k := by
      calc ∏ h ∈ Finset.range H, ∏ i ∈ Finset.univ.filter (fun i : Fin n => h < ν i), b i i
          = ∏ h ∈ Finset.range H, ∏ i, (if h < ν i then b i i else 1) := by
            refine Finset.prod_congr rfl (fun h _ => ?_)
            rw [Finset.prod_filter]
        _ = ∏ i, ∏ h ∈ Finset.range H, (if h < ν i then b i i else 1) := Finset.prod_comm
        _ = ∏ k, b k k ^ ν k := by
            refine Finset.prod_congr rfl (fun i _ => ?_)
            rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
            congr 1
            have hf : (Finset.range H).filter (fun h => h < ν i) = Finset.range (ν i) := by
              ext h
              simp only [Finset.mem_filter, Finset.mem_range]
              have := hH i
              omega
            rw [hf, Finset.card_range]
    rw [map_prod, Finset.prod_congr rfl (fun h _ => hg3 b hb h), ← key]
    simp only [Algebra.smul_def, map_prod, Finset.prod_mul_distrib]
end

section

open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.curve :
    ∀ (n : ℕ) (Ξ : Pre n) (c : ℂ → Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ), c 0 = 1 →
      (∀ a b, HasDerivAt (fun t => c t a b) (X a b) 0) → ∀ i j, HasDerivAt (fun t => Ξ.mat (c t) i j) (Ξ.D X i j) 0 := by
  intro n Ξ c X h0 hd i j
  have hγ : HasDerivAt (fun t => (of.symm (c t) : Fin n → Fin n → ℂ)) (of.symm X) 0 := by
    rw [hasDerivAt_pi]
    intro a
    rw [hasDerivAt_pi]
    intro b
    exact hd a b
  have hγ0 : (of.symm (c 0) : Fin n → Fin n → ℂ) = oneM n := by
    rw [h0]
  have hf : HasFDerivAt (Ξ.coef i j) (fderiv ℂ (Ξ.coef i j) (oneM n))
      ((fun t => (of.symm (c t) : Fin n → Fin n → ℂ)) 0) := by
    show HasFDerivAt (Ξ.coef i j) (fderiv ℂ (Ξ.coef i j) (oneM n)) (of.symm (c 0))
    rw [hγ0]
    exact ((coefDiff n Ξ i j) (oneM n)).hasFDerivAt
  exact hf.comp_hasDerivAt (0 : ℂ) hγ
end

section

open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.polPre :
    ∀ (n N : ℕ), ∃ (Ξ : Pre n) (e : MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ N ≃ₗ[ℂ] (Fin Ξ.d → ℂ)),
      ∀ (g : Matrix (Fin n) (Fin n) ℂ) (f f' : MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ N),
        (f' : Pol n) = rtr g f → Ξ.mat g *ᵥ e f = e f' := by
  intro n N
  let V := MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ N
  have mem : ∀ (g : Matrix (Fin n) (Fin n) ℂ) (f : V), rtr g (f : Pol n) ∈ V := by
    intro g f
    rw [MvPolynomial.mem_restrictTotalDegree]
    exact (rtrDeg n g f).trans ((MvPolynomial.mem_restrictTotalDegree _ _ _).1 f.2)
  let R : Matrix (Fin n) (Fin n) ℂ → V →ₗ[ℂ] V := fun g =>
    LinearMap.codRestrict V ((rtr g).toLinearMap.comp V.subtype) (mem g)
  have hR : ∀ g (f : V), ((R g f : V) : Pol n) = rtr g (f : Pol n) := fun g f => rfl
  let b := Module.finBasis ℂ V
  let M : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ :=
    fun g => LinearMap.toMatrix b b (R g)
  have hR1 : R 1 = LinearMap.id := by
    ext f
    rw [hR, (rtrMul n).1]
    rfl
  have hRm : ∀ g h, R (g * h) = R g ∘ₗ R h := by
    intro g h
    ext f
    rw [hR, (rtrMul n).2]
    rfl
  let mat : Matrix (Fin n) (Fin n) ℂ →* Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ :=
    { toFun := M
      map_one' := by
        show LinearMap.toMatrix b b (R 1) = 1
        rw [hR1, LinearMap.toMatrix_id]
      map_mul' := by
        intro g h
        show LinearMap.toMatrix b b (R (g * h)) = LinearMap.toMatrix b b (R g) * LinearMap.toMatrix b b (R h)
        rw [hRm]
        exact LinearMap.toMatrix_comp b b b (R g) (R h) }
  have poly : ∀ i j : Fin (Module.finrank ℂ V), ∃ p : Pol n, ∀ g : Matrix (Fin n) (Fin n) ℂ,
      mat g i j = MvPolynomial.eval (fun ab => g ab.1 ab.2) p := by
    intro i j
    obtain ⟨φ, hφ⟩ := LinearMap.exists_extend (b.coord i)
    obtain ⟨p, hp⟩ := rtrPoly n ((b j : V) : Pol n) φ
    refine ⟨p, fun g => ?_⟩
    rw [← hp]
    show LinearMap.toMatrix b b (R g) i j = _
    rw [LinearMap.toMatrix_apply, ← hR, ← b.coord_apply, ← hφ]
    rfl
  refine ⟨⟨Module.finrank ℂ V, mat, poly⟩, b.equivFun, ?_⟩
  intro g f f' hf
  show LinearMap.toMatrix b b (R g) *ᵥ b.repr f = b.repr f'
  rw [LinearMap.toMatrix_mulVec_repr]
  congr 2
  apply Subtype.ext
  rw [hR, hf]
end
