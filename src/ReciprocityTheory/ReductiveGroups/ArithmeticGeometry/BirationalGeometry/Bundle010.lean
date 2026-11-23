module

public import Mathlib.FieldTheory.Relrank
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle009

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

def IsMultilinFam (II : AllFam) : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (j : Fin n) (A B : HermLine ι),
    IsArithVar P n → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B →
    II K ι P n (Function.update L j (A.tensor B)) =
      II K ι P n (Function.update L j A) + II K ι P n (Function.update L j B)

def HasPFCoord (II : AllFam) : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k', ι' k') → Ω) (d : ℕ) (L : Fin d → HermLine ι) (L' : Fin d → HermLine ι'),
    IsBlockMap κ v → IsArithVar (mCoordIdeal y) d → IsArithVar (imageZ v (mCoordIdeal y)) d →
    (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) →
    II K' ι' (mCoordIdeal y) d L' =
      (IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) : ℝ) *
        II K ι (imageZ v (mCoordIdeal y)) d L

def HasContractMixed (II : AllFam) : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d₀ d r : ℕ)
    (L : Fin d → HermLine ι) (L' : Fin d → HermLine ι') (N : Fin r → HermLine ι'),
    IsBlockMap κ v → IsArithVar P' (d + r) → IsArithVar (imageZ v P') d₀ → d₀ < d →
    (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) → (∀ j, IsSmoothHerm (N j)) →
    II K' ι' P' (d + r) (Fin.append L' N) = 0

def IsFullIntersectionSystem (II : IntersectionSystem) : Prop :=
  IsIntersectionSystem II ∧ IsMultilinFam II ∧ HasPFCoord II ∧ HasContractMixed II

def ArithIntersectionSystemStatement : Prop :=
  ∃ II : IntersectionSystem, IsFullIntersectionSystem II

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}



theorem exists_monic_rel (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (P : Ideal (MRing ι)) (hPh : IsMultiHomogIdeal P) (hΨ : IsGoodProj P Ψ)
    (F : MvPolynomial ((k : K) → ι k) ℂ) :
    ∃ (n : ℕ) (c : ℕ → MvPolynomial (Fin (e + 1)) ℂ), c n = 1 ∧
      ∀ z ∈ mcPts P, ∑ i ∈ Finset.range (n + 1),
        eval (Ψ (segre z)) (c i) * eval (segre z) F ^ i = 0 := by
  classical
  have hrel := fun i => segre_rel hPh Ψ hΨ i
  choose r hr G hG hrelz using hrel
  let R := MvPolynomial (Fin (e + 1)) ℂ
  let Z := ↥(mcPts P)
  let φw : MvPolynomial ((k : K) → ι k) ℂ →+* (Z → ℂ) :=
    Pi.ringHom fun z : Z => MvPolynomial.eval (segre z.1)
  let φy : R →+* (Z → ℂ) := Pi.ringHom fun z : Z => MvPolynomial.eval (Ψ (segre z.1))
  letI : Algebra R (Z → ℂ) := φy.toAlgebra
  have hsmul : ∀ (c : R) (x : Z → ℂ), c • x = φy c * x := fun c x => Algebra.smul_def c x
  let T : Finset (((k : K) → ι k) →₀ ℕ) :=
    (Fintype.piFinset fun i => Finset.range (r i)).image Finsupp.equivFunOnFinite.symm
  have memT : ∀ s : ((k : K) → ι k) →₀ ℕ, (∀ i, s i < r i) → s ∈ T := fun s hs =>
    Finset.mem_image.2 ⟨⇑s, Fintype.mem_piFinset.2 fun i => Finset.mem_range.2 (hs i),
      Finsupp.equivFunOnFinite_symm_coe s⟩
  let N : Submodule R (Z → ℂ) :=
    Submodule.span R (↑(T.image fun s => φw (monomial s 1)) : Set (Z → ℂ))
  have hC : ∀ (a : ℂ) (x : Z → ℂ), x ∈ N → φw (C a) * x ∈ N := by
    intro a x hx
    have e1 : φw (C a) = φy (C a) := by
      funext z
      show MvPolynomial.eval (segre z.1) (C a) = MvPolynomial.eval (Ψ (segre z.1)) (C a)
      rw [eval_C, eval_C]
    rw [e1, ← hsmul]
    exact N.smul_mem _ hx
  have hY : ∀ (j : Fin (e + 1)) (x : Z → ℂ), x ∈ N → φy (X j) * x ∈ N := by
    intro j x hx
    rw [← hsmul]
    exact N.smul_mem _ hx
  have key : ∀ d, ∀ f : MvPolynomial ((k : K) → ι k) ℂ, f.totalDegree ≤ d → φw f ∈ N := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro f hf

      rw [f.as_sum, map_sum]
      refine N.sum_mem fun s hs => ?_
      rw [show monomial s (AddMonoidAlgebra.coeff f s) = C (AddMonoidAlgebra.coeff f s) * monomial s 1 by
        rw [C_mul_monomial, mul_one], map_mul]
      apply hC
      have hsdeg : (s.sum fun _ e => e) ≤ d := (le_totalDegree hs).trans hf
      by_cases hall : ∀ i, s i < r i
      · exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (memT s hall)))
      · push_neg at hall
        obtain ⟨i, hi⟩ := hall
        obtain ⟨s', hsplit⟩ : ∃ s', s = s' + Finsupp.single i (r i) :=
          ⟨s - Finsupp.single i (r i), (tsub_add_cancel_of_le (Finsupp.single_le_iff.2 hi)).symm⟩
        have hdeg : (s.sum fun _ e => e) = (s'.sum fun _ e => e) + r i := by
          rw [hsplit, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
            Finsupp.sum_single_index rfl]
        have hXr : φw (X i ^ r i) = ∑ j, φy (X j) * φw (G i j) := by
          funext z
          rw [Finset.sum_apply]
          show MvPolynomial.eval (segre z.1) (X i ^ r i) =
            ∑ j, MvPolynomial.eval (Ψ (segre z.1)) (X j) * MvPolynomial.eval (segre z.1) (G i j)
          simp only [map_pow, eval_X]
          exact hrelz i z.1 z.2
        have hri := hr i
        rw [hsplit, monomial_add_single, map_mul, hXr, Finset.mul_sum]
        refine N.sum_mem fun j _ => ?_
        rw [mul_left_comm, ← map_mul φw]
        apply hY
        apply ih ((s.sum fun _ e => e) - 1) (by omega)
        calc (monomial s' 1 * G i j).totalDegree
            ≤ (monomial s' (1 : ℂ)).totalDegree + (G i j).totalDegree := totalDegree_mul _ _
          _ ≤ (s'.sum fun _ e => e) + (r i - 1) := by
            rw [totalDegree_monomial _ one_ne_zero]
            exact Nat.add_le_add_left (hG i j) _
          _ ≤ (s.sum fun _ e => e) - 1 := by omega
  have hFG : (Subalgebra.toSubmodule (Algebra.adjoin R (Set.range φw))).FG := by
    have e2 : Subalgebra.toSubmodule (Algebra.adjoin R (Set.range φw)) = N := by
      apply le_antisymm
      · rw [Algebra.adjoin_eq_span, Submodule.span_le]
        intro x hx
        let Mw : Submonoid (Z → ℂ) :=
          { carrier := Set.range φw
            mul_mem' := by
              rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
              exact ⟨a * b, map_mul _ _ _⟩
            one_mem' := ⟨1, map_one _⟩ }
        have hx' : x ∈ Mw := (Submonoid.closure_le.2 (fun y hy => hy)) hx
        obtain ⟨f, rfl⟩ := hx'
        exact key _ f le_rfl
      · rw [Submodule.span_le]
        intro x hx
        obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
        exact Algebra.subset_adjoin ⟨_, rfl⟩
    rw [e2]
    exact ⟨_, rfl⟩
  have hint : IsIntegral R (φw F) :=
    IsIntegral.of_mem_of_fg (Algebra.adjoin R (Set.range φw)) hFG (φw F)
      (Algebra.subset_adjoin ⟨F, rfl⟩)
  obtain ⟨p, hpm, hp⟩ := hint
  refine ⟨p.natDegree, p.coeff, hpm.coeff_natDegree, fun z hz => ?_⟩
  have h := congrFun hp ⟨z, hz⟩
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_apply] at h
  exact h

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial ReciprocityTheory.AnForm.M

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem eval_smul_of_isMultiHomog {s : MRing ι} {a : K → ℕ} (hs : IsMultiHomog s a)
    (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    eval (fun p => c p.1 * z p) (map (Int.castRingHom ℂ) s) =
      (∏ k, c k ^ a k) * eval z (map (Int.castRingHom ℂ) s) := by
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hms : m ∈ s.support := by
    rw [MvPolynomial.mem_support_iff] at hm ⊢
    intro h0
    exact hm (by rw [MvPolynomial.coeff_map, h0, map_zero])
  have hsub : ∀ f : (Σ k, ι k) → ℂ, ∏ i ∈ m.support, f i ^ m i = ∏ i, f i ^ m i := fun f =>
    Finset.prod_subset (Finset.subset_univ _) fun i _ hi => by
      rw [Finsupp.notMem_support_iff.mp hi, pow_zero]
  rw [hsub, hsub, mul_left_comm]
  congr 1
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [← Finset.univ_sigma_univ, Finset.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [show (∏ s, c (⟨k, s⟩ : Σ k, ι k).fst ^ m ⟨k, s⟩) = ∏ s, c k ^ m ⟨k, s⟩ from rfl,
    Finset.prod_pow_eq_pow_sum, hs m hms k]

theorem analyticAt_eval_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : E → (Σ k, ι k) → ℂ} {y : E} (hF : ∀ p, AnalyticAt ℂ (fun y => F y p) y) (f : MRing ι) :
    AnalyticAt ℂ (fun y => eval (F y) (map (Int.castRingHom ℂ) f)) y := by
  induction (map (Int.castRingHom ℂ) f) using MvPolynomial.induction_on with
  | C a => simpa using analyticAt_const
  | add p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, eval_X]
    exact hp.mul (hF i)

variable {P J : Ideal (MRing ι)} {e : ℕ}

theorem holoOn_eval_lift (R : AnLogRes P J e) (x : R.X) (f : MRing ι) :
    R.A.HoloOn (R.U x) (fun y => eval (R.lift x y) (map (Int.castRingHom ℂ) f)) := by
  intro j w hw
  exact analyticAt_eval_comp (F := fun w => R.lift x ((R.A.chart j).symm w))
    (fun p => R.holo x p j w hw) f

theorem isSection_lift (R : AnLogRes P J e) {A : HermLine ι} {s : MRing ι}
    (hs : IsSectionOn P A s) :
    IsSection R.A (potOf R A) (fun x y => eval (R.lift x y) (map (Int.castRingHom ℂ) s)) := by
  obtain ⟨a, ha, hsa, -⟩ := hs
  refine ⟨fun x => holoOn_eval_lift R x s, fun x x' y hy => ?_⟩
  obtain ⟨c, hc, hxy⟩ := R.compat x x' y hy
  have h1 := A.pos _ (R.mem x y hy.1).1
  have h2 := A.pos _ (R.mem x' y hy.2).1
  have hsm := A.smul c (R.lift x' y) hc
  rw [← hxy] at hsm
  have he : eval (R.lift x y) (map (Int.castRingHom ℂ) s) =
      (∏ k, c k ^ a k) * eval (R.lift x' y) (map (Int.castRingHom ℂ) s) := by
    rw [hxy]
    exact eval_smul_of_isMultiHomog hsa c _
  simp only [potOf]
  rw [Real.exp_neg, Real.exp_neg, Real.exp_log h1, Real.exp_log h2, he, hsm]
  simp only [ha, zpow_natCast, norm_mul, norm_prod, norm_pow]
  have hP : 0 < ∏ k, ‖c k‖ ^ a k :=
    Finset.prod_pos fun k _ => pow_pos (norm_pos_iff.mpr (hc k)) _
  field_simp

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M

def projCoord {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
    {e n : ℕ} (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (x : R.X) :
    Fin n → ℂ :=
  fun i => Ψ (segre (R.lift x x)) i.succ / Ψ (segre (R.lift x x)) 0

end ReciprocityTheory.ChartRestriction.G.Geo
end
end
