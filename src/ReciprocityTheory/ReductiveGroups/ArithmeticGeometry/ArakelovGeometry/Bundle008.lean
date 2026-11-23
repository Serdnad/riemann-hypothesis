module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsSmoothPts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle006
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle005

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem exists_isSecBasis (x : Ix κ → Ω) (n : ℕ) :
    ∃ b : Fin (finrank ℤ (sec ℤ x n)) → MvPolynomial (Ix κ) ℚ, IsSecBasis x n b := by
  classical
  haveI : Module.Finite ℤ (sec ℤ x n) := by
    rw [Module.finite_def, Submodule.fg_top]
    exact (homogeneousSubmodule_fg (Ix κ) ℤ n).map _
  haveI : Module.Free ℤ (sec ℤ x n) := Module.free_of_finite_type_torsion_free'
  let bas := Module.finBasis ℤ (sec ℤ x n)
  have hmem : ∀ k, ∃ f : MvPolynomial (Ix κ) ℤ, f.IsHomogeneous n ∧ aeval x f = ((bas k : sec ℤ x n) : Ω) := by
    intro k
    obtain ⟨f, hf, hfx⟩ := Submodule.mem_map.1 (bas k).2
    exact ⟨f, (mem_homogeneousSubmodule n f).1 hf, hfx⟩
  choose f hfh hfx using hmem
  have hcast : ∀ g : MvPolynomial (Ix κ) ℤ, aeval x (map (Int.castRingHom ℚ) g) = aeval x g := by
    intro g
    rw [← algebraMap_int_eq, aeval_map_algebraMap]
  have hval : (fun k => aeval x (map (Int.castRingHom ℚ) (f k))) = (sec ℤ x n).subtype ∘ bas := by
    funext k
    rw [hcast, hfx]
    rfl
  refine ⟨fun k => map (Int.castRingHom ℚ) (f k), fun k => ⟨f k, hfh k, rfl⟩, ?_, ?_⟩
  · rw [hval]
    exact bas.linearIndependent.map' (sec ℤ x n).subtype (Submodule.ker_subtype _)
  · rw [hval, Set.range_comp, Submodule.span_image, bas.span_eq, Submodule.map_subtype_top]

theorem IsSecBasis.card_eq {x : Ix κ → Ω} {n r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ}
    (hb : IsSecBasis x n b) : r = finrank ℤ (sec ℤ x n) := by
  rw [← hb.2.2, finrank_span_eq_card hb.2.1, Fintype.card_fin]

theorem continuousOn_rho {J : Type} [Fintype J] {m : ConeMetric (C := ℂ) (ι := J)} (hm : IsSmoothMetric m) :
    ContinuousOn m.ρ {0}ᶜ := hm.continuousOn.mono fun _ hz => hz

theorem sum_secFun_smul {n r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ}
    (hb : ∀ k, ∃ f : MvPolynomial (Ix κ) ℤ, f.IsHomogeneous n ∧ b k = map (Int.castRingHom ℚ) f)
    (c : Fin r → ℂ) (a : ℂ) (w : Ix κ → ℂ) :
    ∑ i, c i * secFun (b i) (a • w) = a ^ n * ∑ i, c i * secFun (b i) w := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [secFun_smul (hb i)]
  ring

theorem isDegZero_normSq {m : ConeMetric (C := ℂ) (ι := Ix κ)} {n r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ}
    (hb : ∀ k, ∃ f : MvPolynomial (Ix κ) ℤ, f.IsHomogeneous n ∧ b k = map (Int.castRingHom ℚ) f)
    (c : Fin r → ℂ) : IsDegZero fun z => ‖∑ i, c i * secFun (b i) z‖ ^ 2 * wgt m n z := by
  intro a z ha
  have hn : ‖a‖ ≠ 0 := norm_ne_zero_iff.2 ha
  have hpow : ‖a‖ ^ (2 * n) ≠ 0 := pow_ne_zero _ hn
  simp only [wgt]
  rw [sum_secFun_smul hb, m.smul, norm_mul, norm_pow, mul_pow, mul_pow (‖a‖), mul_inv, ← pow_mul]
  field_simp
  ring

theorem continuousOn_normSq {m : ConeMetric (C := ℂ) (ι := Ix κ)} (hm : IsSmoothMetric m) {n r : ℕ}
    (b : Fin r → MvPolynomial (Ix κ) ℚ) (c : Fin r → ℂ) :
    ContinuousOn (fun z => ‖∑ i, c i * secFun (b i) z‖ ^ 2 * wgt m n z) {0}ᶜ := by
  have hρ : ContinuousOn m.ρ {0}ᶜ := hm.continuousOn.mono fun _ hz => hz
  refine ContinuousOn.mul ?_ ?_
  · exact ((continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_secFun (b i))).norm.pow 2).continuousOn
  · exact ContinuousOn.inv₀ (hρ.pow _) fun z hz => pow_ne_zero _ (m.pos z hz).ne'

theorem linIndep_rat_of_isSecBasis {x : Ix κ → Ω} {n r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ}
    (hb : IsSecBasis x n b) : LinearIndependent ℚ fun k => aeval x (b k) :=
  (LinearIndependent.iff_fractionRing ℤ ℚ).1 hb.2.1

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem le_of_mem_support_mHom {a : K → ℕ} {f : MRing ι} (hf : f ∈ mHom ι a) {m : (Σ k, ι k) →₀ ℕ}
    (hm : m ∈ f.support) (p : Σ k, ι k) : m p ≤ a p.1 := by
  classical
  revert m
  induction hf using Submodule.span_induction with
  | mem s hs =>
    intro m hm
    rw [← hs m hm p.1]
    exact Finset.single_le_sum (f := fun i => m ⟨p.1, i⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ p.2)
  | zero =>
    intro m hm
    simp at hm
  | add x y _ _ hx hy =>
    intro m hm
    rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
    · exact hx h
    · exact hy h
  | smul c x _ hx =>
    intro m hm
    exact hx (MvPolynomial.support_smul hm)

theorem finite_monoBox (a : K → ℕ) :
    {m : (Σ k, ι k) →₀ ℕ | ∀ p, m p ≤ a p.1}.Finite := by
  have hfin : (Set.pi Set.univ fun p : (Σ k, ι k) => Set.Iic (a p.1)).Finite :=
    Set.Finite.pi fun p => Set.finite_Iic _
  refine (hfin.preimage (Finsupp.equivFunOnFinite.injective.injOn)).subset ?_
  intro m hm p _
  exact hm p

def monoBox (a : K → ℕ) : Finset ((Σ k, ι k) →₀ ℕ) := (finite_monoBox (ι := ι) a).toFinset

theorem support_subset_monoBox {a : K → ℕ} {f : MRing ι} (hf : f ∈ mHom ι a) :
    f.support ⊆ monoBox a := by
  intro m hm
  simp only [monoBox, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  exact fun p => le_of_mem_support_mHom hf hm p

theorem finite_mPiece (J : Ideal (MRing ι)) (a : K → ℕ) {p : ℕ} (hp : 0 < p)
    (hpJ : (p : MRing ι) ∈ J) : Finite (mPiece J a) := by
  classical
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  let g : (monoBox (ι := ι) a → Fin (q + 1)) → MRing ι ⧸ J := fun c =>
    Ideal.Quotient.mk J (∑ m : monoBox (ι := ι) a,
      MvPolynomial.monomial (m : (Σ k, ι k) →₀ ℕ) (((c m : ℕ) : ℤ)))
  have hsub : (mPiece J a : Set (MRing ι ⧸ J)) ⊆ Set.range g := by
    intro x hx
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hx
    have hq : (0 : ℤ) < ((q + 1 : ℕ) : ℤ) := by omega
    refine ⟨fun m => ⟨((AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ)) % ((q + 1 : ℕ) : ℤ)).toNat, ?_⟩, ?_⟩
    · have h0 := Int.emod_nonneg (AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ)) hq.ne'
      have h1 := Int.emod_lt_of_pos (AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ)) hq
      omega
    · show Ideal.Quotient.mk J (∑ m : monoBox (ι := ι) a, MvPolynomial.monomial (m : (Σ k, ι k) →₀ ℕ)
          ((((AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ)) % ((q + 1 : ℕ) : ℤ)).toNat : ℕ) : ℤ)) =
        Ideal.Quotient.mk J f
      rw [Ideal.Quotient.eq]
      have hf' : f = ∑ m : monoBox (ι := ι) a,
          MvPolynomial.monomial (m : (Σ k, ι k) →₀ ℕ) (AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ)) := by
        rw [Finset.sum_coe_sort (monoBox a) (fun m => MvPolynomial.monomial m (AddMonoidAlgebra.coeff f m))]
        conv_lhs => rw [MvPolynomial.as_sum f]
        refine Finset.sum_subset (support_subset_monoBox hf) (fun m _ hm => ?_)
        simp only [MvPolynomial.mem_support_iff, ne_eq, not_not] at hm
        simp [hm]
      have hP : ((q + 1 : ℕ) : MRing ι) ∈ J := hpJ
      have hdiff : ∀ m : monoBox (ι := ι) a, MvPolynomial.monomial (m : (Σ k, ι k) →₀ ℕ)
          ((((AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ)) % ((q + 1 : ℕ) : ℤ)).toNat : ℕ) : ℤ) -
          MvPolynomial.monomial (m : (Σ k, ι k) →₀ ℕ) (AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ)) ∈ J := by
        intro m
        have h0 := Int.emod_nonneg (AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ)) hq.ne'
        rw [Int.toNat_of_nonneg h0, ← map_sub, Int.emod_def]
        have e : AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ) - ((q + 1 : ℕ) : ℤ) *
            (AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ) / ((q + 1 : ℕ) : ℤ)) -
            AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ) =
            ((q + 1 : ℕ) : ℤ) * (-(AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ) / ((q + 1 : ℕ) : ℤ))) := by
          ring
        rw [e, ← MvPolynomial.C_mul_monomial, map_natCast]
        exact J.mul_mem_right _ hP
      have e2 : (∑ m : monoBox (ι := ι) a, MvPolynomial.monomial (m : (Σ k, ι k) →₀ ℕ)
          ((((AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ)) % ((q + 1 : ℕ) : ℤ)).toNat : ℕ) : ℤ)) - f =
          ∑ m : monoBox (ι := ι) a, (MvPolynomial.monomial (m : (Σ k, ι k) →₀ ℕ)
          ((((AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ)) % ((q + 1 : ℕ) : ℤ)).toNat : ℕ) : ℤ) -
          MvPolynomial.monomial (m : (Σ k, ι k) →₀ ℕ) (AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ))) := by
        rw [Finset.sum_sub_distrib, ← hf']
      rw [e2]
      exact Ideal.sum_mem _ fun m _ => hdiff m
  exact ((Set.finite_range g).subset hsub).to_subtype

theorem card_mPiece_pos (J : Ideal (MRing ι)) (a : K → ℕ) {p : ℕ} (hp : 0 < p)
    (hpJ : (p : MRing ι) ∈ J) : 0 < Nat.card (mPiece J a) := by
  haveI := finite_mPiece J a hp hpJ
  exact Nat.card_pos

theorem card_mPiece_irrel {q : Ideal (MRing ι)} {k : K} (hk : ∀ i, (X ⟨k, i⟩ : MRing ι) ∈ q)
    {a : K → ℕ} (ha : 0 < a k) : Nat.card (mPiece q a) = 1 := by
  classical
  have hmem : ∀ f ∈ mHom ι a, f ∈ q := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem s hs =>
      rw [MvPolynomial.as_sum s]
      refine Ideal.sum_mem _ fun m hm => ?_
      have hsum := hs m hm k
      obtain ⟨i, hi⟩ : ∃ i, 0 < m ⟨k, i⟩ := by
        by_contra hc
        push_neg at hc
        have h0 : ∑ i, m ⟨k, i⟩ = 0 := Finset.sum_eq_zero fun i _ => by have := hc i; omega
        omega
      have e : MvPolynomial.monomial m (AddMonoidAlgebra.coeff s m) =
          MvPolynomial.X ⟨k, i⟩ * MvPolynomial.monomial (m - Finsupp.single ⟨k, i⟩ 1) (AddMonoidAlgebra.coeff s m) := by
        rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul,
          add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr hi)]
      rw [e]
      exact q.mul_mem_right _ (hk i)
    | zero => exact q.zero_mem
    | add x y _ _ hx hy => exact q.add_mem hx hy
    | smul c x _ hx => exact Submodule.smul_of_tower_mem q c hx
  have hzero : ∀ x : mPiece q a, x = 0 := by
    rintro ⟨x, hx⟩
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hx
    apply Subtype.ext
    show Ideal.Quotient.mk q f = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hmem f hf)
  haveI : Unique (mPiece q a) := ⟨⟨0⟩, hzero⟩
  exact Nat.card_unique

theorem card_mPiece_mono {J J' : Ideal (MRing ι)} (h : J ≤ J') (a : K → ℕ) [Finite (mPiece J a)] :
    Nat.card (mPiece J' a) ≤ Nat.card (mPiece J a) := by
  have hmap : ∀ x ∈ mPiece J a, Ideal.Quotient.factor h x ∈ mPiece J' a := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hx
    refine Submodule.mem_map.mpr ⟨g, hg, ?_⟩
    show Ideal.Quotient.mk J' g = Ideal.Quotient.factor h (Ideal.Quotient.mk J g)
    rw [Ideal.Quotient.factor_mk]
  refine Nat.card_le_card_of_surjective (fun x => ⟨Ideal.Quotient.factor h x, hmap x x.2⟩) ?_
  rintro ⟨y, hy⟩
  obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hy
  refine ⟨⟨Ideal.Quotient.mk J g, Submodule.mem_map.mpr ⟨g, hg, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  show Ideal.Quotient.factor h (Ideal.Quotient.mk J g) = Ideal.Quotient.mk J' g
  rw [Ideal.Quotient.factor_mk]

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

section Lin

variable {J : Type} [Fintype J] [DecidableEq J]

theorem isInvMat_mul {A : Matrix J J ℚ} (hA : IsInvMat A) :
    ∃ B : Matrix J J ℚ, A * B = 1 ∧ B * A = 1 := by
  obtain ⟨B, hB⟩ := hA
  refine ⟨B, ?_, ?_⟩
  · refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, Matrix.one_mulVec]
    exact (hB v).1
  · refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, Matrix.one_mulVec]
    exact (hB v).2

variable {Ω : Type*} [Field Ω] [CharZero Ω]

theorem matAct_eq_mulVec (A : Matrix J J ℚ) (v : J → Ω) :
    matAct A v = (A.map (Rat.castHom Ω)).mulVec v := by
  funext i
  simp [matAct, Matrix.mulVec, dotProduct]

theorem matAct_matAct {A B : Matrix J J ℚ} (h : B * A = 1) (v : J → Ω) :
    matAct B (matAct A v) = v := by
  rw [matAct_eq_mulVec, matAct_eq_mulVec, Matrix.mulVec_mulVec, ← Matrix.map_mul, h,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]

theorem matActC_eq (A : Matrix J J ℚ) (z : J → ℂ) : matActC A z = matAct A z := rfl

theorem matAct_smul (A : Matrix J J ℚ) (c : Ω) (v : J → Ω) :
    matAct A (c • v) = c • matAct A v := by
  funext i
  simp only [matAct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem matAct_zero (A : Matrix J J ℚ) : matAct A (0 : J → Ω) = 0 := by
  funext i
  simp [matAct]

theorem matAct_eq_zero_iff {A B : Matrix J J ℚ} (h : B * A = 1) (v : J → Ω) :
    matAct A v = 0 ↔ v = 0 := by
  constructor
  · intro hv
    rw [← matAct_matAct h v, hv, matAct_zero]
  · rintro rfl
    exact matAct_zero A

def linSub (A : Matrix J J ℚ) : MvPolynomial J ℚ →ₐ[ℚ] MvPolynomial J ℚ :=
  bind₁ fun i => ∑ j, C (A i j) * X j

theorem aeval_linSub (A : Matrix J J ℚ) (v : J → Ω) (g : MvPolynomial J ℚ) :
    aeval v (linSub A g) = aeval (matAct A v) g := by
  simp only [linSub, aeval_bind₁]
  congr 2
  funext i
  simp [matAct, eq_ratCast]

theorem isHomogeneous_linSub (A : Matrix J J ℚ) {g : MvPolynomial J ℚ} {n : ℕ}
    (hg : g.IsHomogeneous n) : (linSub A g).IsHomogeneous n := by
  have h := hg.eval₂ (algebraMap ℚ (MvPolynomial J ℚ)) (fun i => ∑ j, C (A i j) * X j)
    (fun r => by rw [MvPolynomial.algebraMap_eq]; exact isHomogeneous_C _ _)
    (fun i => IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X _ _)
  rw [one_mul] at h
  exact h

end Lin

section Pts

variable {J : Type} [Fintype J] {Ω : Type*} [Field Ω] [CharZero Ω]

theorem aeval_int_eq (z : J → ℂ) (f : MvPolynomial J ℤ) :
    eval z (map (Int.castRingHom ℂ) f) = aeval z f := by
  rw [eval_map, aeval_def, algebraMap_int_eq]

theorem aeval_qmap {S : Type*} [CommRing S] [Algebra ℚ S] (z : J → S) (f : MvPolynomial J ℤ) :
    aeval z (qmap f) = aeval z f := by
  show aeval z (map (Int.castRingHom ℚ) f) = _
  rw [aeval_def, aeval_def, eval₂_map]
  congr 1
  exact RingHom.ext_int _ _

theorem mem_pts_iff (v : J → Ω) (z : J → ℂ) :
    z ∈ pts (coordIdeal ℤ v) ↔ z ≠ 0 ∧ ∀ (n : ℕ) (g : MvPolynomial J ℚ), g.IsHomogeneous n →
      aeval v g = 0 → aeval z g = 0 := by
  classical
  simp only [pts, conePts, Set.mem_setOf_eq, coordIdeal, RingHom.mem_ker, aeval_int_eq]
  refine and_congr_right fun _ => ⟨fun H n g hg hv => ?_, fun H f hf => ?_⟩
  · obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors ℤ)
      (g.support.image fun m => g.coeff m)
    have hr' : ∀ m, ∃ r : ℤ, (r : ℚ) = ((b : ℤ) : ℚ) * g.coeff m := by
      intro m
      by_cases hm : m ∈ g.support
      · obtain ⟨r, hr⟩ := hb _ (Finset.mem_image_of_mem _ hm)
        exact ⟨r, by simpa [Algebra.smul_def] using hr⟩
      · rw [mem_support_iff, not_not] at hm
        exact ⟨0, by simp [hm]⟩
    choose r hr using hr'
    obtain ⟨f, hfdef⟩ : ∃ f : MvPolynomial J ℤ, f = ∑ m ∈ g.support, monomial m (r m) := ⟨_, rfl⟩
    have hfg : qmap f = C ((b : ℤ) : ℚ) * g := by
      ext m
      rw [coeff_C_mul, ← hr m]
      simp only [qmap, coeff_map, hfdef, coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq', Finset.sum_ite_eq]
      split_ifs with hm
      · simp
      · rw [mem_support_iff, not_not] at hm
        rw [map_zero, hr m, hm, mul_zero]
    have hfh : f.IsHomogeneous n := by
      intro d hd
      apply hg
      intro h0
      apply hd
      have h1 := congrArg (AddMonoidAlgebra.coeff · d) hfg
      rw [coeff_C_mul, h0, mul_zero] at h1
      simp only [qmap, coeff_map] at h1
      simpa using h1
    have hvf : aeval v f = 0 := by
      rw [← aeval_qmap, hfg, map_mul, hv, mul_zero]
    have hz := H f (by rw [coneMap_of_isHomogeneous (x := v) (hf := hfh), hvf, map_zero, zero_mul])
    rw [← aeval_qmap, hfg, map_mul, aeval_C] at hz
    have hb0 : (b : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero b
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd (by simpa using h) hb0
    · exact h
  · have hk : ∀ k, aeval z (homogeneousComponent k f) = 0 := by
      intro k
      have h1 : aeval v (homogeneousComponent k f) = 0 := by
        rw [← coeff_coneMap, hf, Polynomial.coeff_zero]
      have h2 := H k (qmap (homogeneousComponent k f)) ((homogeneousComponent_isHomogeneous k f).map _)
        (by rw [aeval_qmap, h1])
      rwa [aeval_qmap] at h2

    rw [← sum_homogeneousComponent (φ := f), map_sum]
    exact Finset.sum_eq_zero fun k _ => hk k

theorem pts_matAct_gen (x : J → Ω) (A : Matrix J J ℚ) (hA : IsInvMat A) (z : J → ℂ) :
    matActC A z ∈ pts (coordIdeal ℤ (matAct A x)) ↔ z ∈ pts (coordIdeal ℤ x) := by
  classical
  obtain ⟨B, -, hBA⟩ := isInvMat_mul hA
  have hne : matAct A z ≠ 0 ↔ z ≠ 0 := not_congr (matAct_eq_zero_iff hBA z)
  rw [mem_pts_iff, mem_pts_iff, matActC_eq, hne]
  refine and_congr_right fun _ => ⟨fun H n g hg hx => ?_, fun H n g hg hx => ?_⟩
  · have h1 := H n (linSub B g) (isHomogeneous_linSub B hg)
      (by rw [aeval_linSub, matAct_matAct hBA, hx])
    rwa [aeval_linSub, matAct_matAct hBA] at h1
  · rw [← aeval_linSub] at hx ⊢
    exact H n _ (isHomogeneous_linSub A hg) hx

end Pts

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end
