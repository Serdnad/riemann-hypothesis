module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.Algebra.Algebra.Hom.Rat

@[expose] public section

section

open scoped TensorProduct

namespace GlobalTheory

open MvPolynomial

theorem truncMono_deriv_aeval {k A : Type} [Field k] [CommRing A] [Algebra k A] {d : ℕ}
    (x : Fin d → A) (E : Fin d → Derivation k A A)
    (hE : ∀ i j, E i (x j) = if i = j then 1 else 0) (B : Subalgebra k A)
    (hB : ∀ i, ∀ b ∈ B, E i b = 0) (i : Fin d) (F : MvPolynomial (Fin d) B) :
    E i (aeval x F) = aeval x (pderiv i F) := by
  induction F using MvPolynomial.induction_on with
  | C b =>
    rw [aeval_C, pderiv_C, map_zero]
    exact hB i _ b.2
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _), map_add (f := _)]
  | mul_X p j hp =>
    have h1 : E i (aeval x p * x j) = aeval x p * E i (x j) + x j * E i (aeval x p) := by
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    rw [map_mul, aeval_X, h1, hp, pderiv_mul, pderiv_X, map_add (f := _), map_mul, map_mul, aeval_X, hE]
    by_cases h : i = j
    · subst h; simp; ring
    · simp [h, Pi.single_apply, Ne.symm h]; ring

theorem truncMono_eq_zero {p : ℕ} [Fact p.Prime] {k A : Type} [Field k] [CommRing A]
    [Algebra k A] [CharP k p] {d : ℕ}
    (x : Fin d → A) (E : Fin d → Derivation k A A)
    (hE : ∀ i j, E i (x j) = if i = j then 1 else 0) (B : Subalgebra k A)
    (hB : ∀ i, ∀ b ∈ B, E i b = 0) :
    ∀ n : ℕ, ∀ F : MvPolynomial (Fin d) B,
      (∀ m ∈ F.support, (∀ i, m i < p) ∧ ∑ i, m i ≤ n) → aeval x F = 0 → F = 0 := by
  have hconst : ∀ F : MvPolynomial (Fin d) B, (∀ m, m ≠ 0 → AddMonoidAlgebra.coeff F m = 0) →
      aeval x F = 0 → F = 0 := by
    intro F hc hF
    have hFC : F = C (AddMonoidAlgebra.coeff F 0) := by
      refine MvPolynomial.ext _ _ (fun m => ?_)
      rw [coeff_C]
      by_cases hm : m = 0
      · subst hm; simp
      · rw [if_neg (Ne.symm hm)]; exact hc m hm
    rw [hFC, aeval_C] at hF
    have h0 : AddMonoidAlgebra.coeff F 0 = 0 := Subtype.ext (by simpa using hF)
    rw [hFC, h0, C_0]
  intro n
  induction n with
  | zero =>
    intro F hs hF
    apply hconst F _ hF
    intro m hm
    by_contra hc
    have := (hs m (mem_support_iff.mpr hc)).2
    apply hm
    ext i
    have := (Finset.sum_eq_zero_iff.mp (Nat.le_zero.mp this)) i (Finset.mem_univ _)
    simpa using this
  | succ n ih =>
    intro F hs hF
    have hpd : ∀ i, pderiv i F = 0 := by
      intro i
      apply ih
      · intro m hm
        rw [mem_support_iff, coeff_pderiv] at hm
        have hm' := hs _ (mem_support_iff.mpr (left_ne_zero_of_mul hm))
        refine ⟨fun j => lt_of_le_of_lt ?_ (hm'.1 j), ?_⟩
        · simp
        · have h2 := hm'.2
          simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib] at h2
          have h3 : ∑ j, (Finsupp.single i 1 : Fin d →₀ ℕ) j = 1 := by
            simp [Finsupp.single_apply]
          omega
      · rw [← truncMono_deriv_aeval x E hE B hB, hF, map_zero]
    apply hconst F _ hF
    intro m hm
    obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hm (Finsupp.ext h)
    by_contra hc
    have hlt := (hs m (mem_support_iff.mpr hc)).1 i
    have hcoef := coeff_pderiv (i := i) F (m - Finsupp.single i 1)
    rw [Finsupp.sub_add_single_one_cancel hi, hpd i] at hcoef
    simp at hcoef
    have hmi : (m - Finsupp.single i 1 : Fin d →₀ ℕ) i + 1 = m i := by
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]; omega
    have hunit : IsUnit (((m - Finsupp.single i 1 : Fin d →₀ ℕ) i : B) + 1) := by
      have e : (((m - Finsupp.single i 1 : Fin d →₀ ℕ) i : B) + 1) = algebraMap k B ((m i : ℕ) : k) := by
        rw [map_natCast, ← hmi]; push_cast; rfl
      rw [e]
      apply IsUnit.map
      apply Ne.isUnit
      rw [Ne, CharP.cast_eq_zero_iff k p]
      intro hdvd
      exact hi (Nat.eq_zero_of_dvd_of_lt hdvd hlt)
    have hcoef' : F.coeff m * (((m - Finsupp.single i 1 : Fin d →₀ ℕ) i : B) + 1) = 0 := by
      have hmi' : m i - 1 = (m - Finsupp.single i 1 : Fin d →₀ ℕ) i := by
        omega
      simpa only [← hmi'] using hcoef.symm
    exact hc ((hunit.mul_left_eq_zero).mp hcoef')

end GlobalTheory

namespace GlobalTheory
open MvPolynomial

theorem truncMono_linearIndependent : ∀ (p : ℕ) [Fact p.Prime] (k A : Type) [Field k] [CommRing A] [Algebra k A] [CharP k p] (d : ℕ) (x : Fin d → A) (E : Fin d → Derivation k A A), (∀ i j, E i (x j) = if i = j then 1 else 0) → ∀ B : Subalgebra k A, (∀ i, ∀ b ∈ B, E i b = 0) → LinearIndependent B (fun a : Fin d → Fin p => ∏ i, x i ^ (a i : ℕ)) := by
  intro p _ k A _ _ _ _ d x E hE B hB
  rw [Fintype.linearIndependent_iff]
  intro g hg
  let toF : (Fin d → Fin p) → (Fin d →₀ ℕ) := fun a => Finsupp.equivFunOnFinite.symm (fun i => (a i : ℕ))
  have hinj : Function.Injective toF := by
    intro a b hab
    funext i
    apply Fin.ext
    have := congrArg (fun f : Fin d →₀ ℕ => f i) hab
    simpa [toF] using this
  let F : MvPolynomial (Fin d) B := ∑ a, monomial (toF a) (g a)
  have hcoeff : ∀ m, AddMonoidAlgebra.coeff F m = ∑ a, if toF a = m then g a else 0 := by
    intro m
    simp only [F, coeff_sum, coeff_monomial]
  have hF : aeval x F = 0 := by
    rw [← hg]

    simp only [F, map_sum, aeval_monomial]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Subalgebra.smul_def]
    rfl
  have hF0 : F = 0 := by
    refine truncMono_eq_zero x E hE B hB (∑ _i : Fin d, p) F ?_ hF
    intro m hm
    rw [mem_support_iff, hcoeff] at hm
    obtain ⟨a, _, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
    have hm' : toF a = m := by
      by_contra h
      exact ha (if_neg h)
    subst hm'
    refine ⟨fun i => by simp [toF], ?_⟩
    apply Finset.sum_le_sum
    intro i _
    simp [toF, (a i).isLt.le]
  intro a
  have := hcoeff (toF a)
  rw [hF0] at this
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at this
  simp_rw [hinj.eq_iff] at this
  have hsum : (∑ b : Fin d → Fin p, if b = a then g b else 0) = g a := by
    simp
  rw [hsum] at this
  simpa using this.symm

end GlobalTheory
end

section

open scoped TensorProduct

namespace GlobalTheory.CotangentSquare

open MvPolynomial

variable {O B σ : Type} [CommRing O] [CommRing B]

def firstOrderKer (η : MvPolynomial σ B →+* O) : Ideal (MvPolynomial σ B) where
  carrier := {F | η F = 0 ∧ ∀ l, η (pderiv l F) = 0}
  add_mem' := by
    rintro F G ⟨hF, hF'⟩ ⟨hG, hG'⟩
    exact ⟨by simp [hF, hG], fun l => by simp [hF' l, hG' l]⟩
  zero_mem' := ⟨by simp, fun l => by simp⟩
  smul_mem' := by
    rintro G F ⟨hF, hF'⟩
    exact ⟨by simp [hF], fun l => by simp [pderiv_mul, hF, hF' l]⟩

theorem pderiv_comb [Fintype σ] (η : MvPolynomial σ B →+* O) (f g : σ → MvPolynomial σ B)
    (hf : ∀ i, η (f i) = 0) (k : MvPolynomial σ B) (hk : k ∈ firstOrderKer η) (l : σ) :
    η (pderiv l (∑ i, g i * f i + k)) = ∑ i, η (g i) * η (pderiv l (f i)) := by
  have := hk.2 l

  simp [map_sum, pderiv_mul, hf, this]

theorem det_ne_zero_of_mul_eq [Fintype σ] [DecidableEq σ] [IsDomain O] {N J : Matrix σ σ O}
    {c : O} (hc : c ≠ 0) (h : N * J = c • (1 : Matrix σ σ O)) : J.det ≠ 0 := by
  intro hJ
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, hJ, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one] at this
  exact pow_ne_zero _ hc this.symm

theorem cotangent_map_injective_of_square_presentation : ∀ (O B A σ : Type) [CommRing O] [IsDomain O] [CommRing B] [CommRing A] [Algebra O B] [Algebra O A] [Algebra B A] [IsScalarTower O B A] [Fintype σ] (ε : A →ₐ[O] O) (x : σ → A) (f : σ → MvPolynomial σ B) (c : O), c ≠ 0 → Function.Surjective (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) → (∀ i, MvPolynomial.aeval x (f i) = 0) → RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) ≤ Ideal.span (Set.range f) ⊔ (RingHom.ker ε).comap (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) * RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) → (∀ a ∈ RingHom.ker ε, c • a ∈ RingHom.ker ε ^ 2 ⊔ ((RingHom.ker ε).comap (algebraMap B A)).map (algebraMap B A)) → ∀ b : B, algebraMap B A b ∈ RingHom.ker ε ^ 2 → b ∈ ((RingHom.ker ε).comap (algebraMap B A)) ^ 2 := by
  intro O B A σ _ _ _ _ _ _ _ _ _ ε x f c hc hsurj hf hker hc2 b hb
  classical
  set Ψ := (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) with hΨ
  let η : MvPolynomial σ B →+* O := (ε : A →+* O).comp (Ψ : MvPolynomial σ B →+* A)
  have hη : ∀ F, η F = ε (Ψ F) := fun F => rfl
  set q := (RingHom.ker ε).comap Ψ with hq
  have hqmem : ∀ F, F ∈ q ↔ η F = 0 := fun F => by
    rw [hq, Ideal.mem_comap, RingHom.mem_ker, hη]
  have hkerq : RingHom.ker Ψ ≤ q := fun F hF => by
    rw [hqmem, hη, (RingHom.mem_ker).1 hF, map_zero]
  have hηf : ∀ i, η (f i) = 0 := fun i => by rw [hη, hf i, map_zero]
  set K := firstOrderKer η with hK
  have hq2 : q ^ 2 ≤ K := by
    rw [pow_two]
    refine Ideal.mul_le.2 fun a ha b' hb' => ?_
    rw [hqmem] at ha hb'
    exact ⟨by simp [ha, hb'], fun l => by simp [pderiv_mul, ha, hb']⟩
  have hkerL : RingHom.ker Ψ ≤ Ideal.span (Set.range f) ⊔ q ^ 2 := by
    refine hker.trans (sup_le_sup_left ?_ _)
    rw [pow_two]; exact Ideal.mul_mono_right hkerq
  have hkerK : RingHom.ker Ψ ≤ Ideal.span (Set.range f) ⊔ K := hkerL.trans (sup_le_sup_left hq2 _)
  have hsq : RingHom.ker ε ^ 2 = (q ^ 2).map Ψ := by
    rw [Ideal.map_pow, hq, Ideal.map_comap_of_surjective Ψ hsurj]
  have lift : ∀ (L : Ideal (MvPolynomial σ B)), RingHom.ker Ψ ≤ Ideal.span (Set.range f) ⊔ L →
      ∀ F, Ψ F ∈ L.map Ψ → F ∈ Ideal.span (Set.range f) ⊔ L := by
    intro L hL F hF
    obtain ⟨G, hG, hGF⟩ := (Ideal.mem_map_iff_of_surjective Ψ hsurj).1 hF
    have h1 : F - G ∈ RingHom.ker Ψ := by rw [RingHom.mem_ker, map_sub, hGF, sub_self]
    have h2 : F = (F - G) + G := by ring
    rw [h2]; exact Ideal.add_mem _ (hL h1) (Ideal.mem_sup_right hG)
  have hIB : ((RingHom.ker ε).comap (algebraMap B A)).map (algebraMap B A) ≤ K.map Ψ := by
    rw [Ideal.map_le_iff_le_comap]
    intro i hi
    rw [Ideal.mem_comap, RingHom.mem_ker] at hi
    rw [Ideal.mem_comap]
    have : algebraMap B A i = Ψ (C i) := by simp [hΨ]
    rw [this]
    refine Ideal.mem_map_of_mem _ ⟨?_, fun l => by simp⟩
    rw [hη]; simpa [hΨ] using hi
  let Jac : Matrix σ σ O := fun i l => η (pderiv l (f i))
  have hrow : ∀ j, ∃ g : σ → MvPolynomial σ B, ∀ l,
      (if j = l then c else 0) = ∑ i, η (g i) * Jac i l := by
    intro j
    set F := C (algebraMap O B c) * (X j - C (algebraMap O B (ε (x j)))) with hF
    have ha : x j - algebraMap O A (ε (x j)) ∈ RingHom.ker ε := by
      rw [RingHom.mem_ker]; simp
    have hΨF : Ψ F = c • (x j - algebraMap O A (ε (x j))) := by
      simp [hF, hΨ, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
    have hmem : Ψ F ∈ K.map Ψ := by
      rw [hΨF]
      refine (sup_le ?_ hIB) (hc2 _ ha)
      rw [hsq]; exact Ideal.map_mono hq2
    have hF2 := lift K hkerK F hmem
    rw [Submodule.mem_sup] at hF2
    obtain ⟨s, hs, k, hk, hsk⟩ := hF2
    obtain ⟨g, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hs
    refine ⟨g, fun l => ?_⟩
    have e1 := pderiv_comb η f g hηf k hk l
    rw [hsk] at e1
    rw [← e1, hF]
    by_cases hjl : j = l
    · subst hjl
      simp [pderiv_X_self, hη, hΨ, ← IsScalarTower.algebraMap_apply]
    · simp [hjl, pderiv_X_of_ne (Ne.symm hjl)]
  choose g hg using hrow
  let N : Matrix σ σ O := fun j i => η (g j i)
  have hNJ : N * Jac = c • (1 : Matrix σ σ O) := by
    ext j l
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, ← hg j l]
    split_ifs <;> simp
  have hdet : Jac.det ≠ 0 := det_ne_zero_of_mul_eq hc hNJ
  have hCb : C b ∈ Ideal.span (Set.range f) ⊔ q ^ 2 := by
    refine lift _ hkerL (C b) ?_
    rw [← hsq]; simpa [hΨ] using hb
  rw [Submodule.mem_sup] at hCb
  obtain ⟨s, hs, k, hk, hsk⟩ := hCb
  obtain ⟨g', rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hs
  have hv : Matrix.vecMul (fun i => η (g' i)) Jac = 0 := by
    funext l
    have e1 := pderiv_comb η f g' hηf k (hq2 hk) l
    rw [hsk] at e1
    simp only [pderiv_C, map_zero] at e1
    change ∑ i, η (g' i) * Jac i l = 0
    exact e1.symm
  have hv0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hv
  have hCq : C b ∈ q ^ 2 := by
    rw [← hsk]
    refine Ideal.add_mem _ (Ideal.sum_mem _ fun i _ => ?_) hk
    rw [pow_two]
    refine Ideal.mul_mem_mul ?_ (hkerq ?_)
    · rw [hqmem]; exact congrFun hv0 i
    · rw [RingHom.mem_ker]; exact hf i
  let ev : MvPolynomial σ B →ₐ[B] B := aeval (fun j => algebraMap O B (ε (x j)))
  have hev : ((ε : A →+* O).comp (algebraMap B A)).comp (ev : MvPolynomial σ B →+* B) = η := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [ev, η, hΨ]
    · intro i; simp [ev, η, hΨ, ← IsScalarTower.algebraMap_apply]
  have hqev : q.map ev ≤ (RingHom.ker ε).comap (algebraMap B A) := by
    rw [Ideal.map_le_iff_le_comap]
    intro F hF
    rw [hqmem] at hF
    rw [Ideal.mem_comap, Ideal.mem_comap, RingHom.mem_ker, ← hF, ← hev]
    rfl
  have : b = ev (C b) := by simp [ev]
  rw [this]
  exact Ideal.pow_right_mono hqev 2 (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hCq)

end GlobalTheory.CotangentSquare
end

section

open Matrix Polynomial

namespace GlobalTheory

theorem csr_transpose_aeval {K : Type} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (p : K[X]) :
    (aeval A p)ᵀ = aeval Aᵀ p := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, transpose_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [transpose_smul, transpose_pow]

theorem csr_map_aeval {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (p : K[X]) :
    (aeval A p).map σ = aeval (A.map σ) (p.map σ) := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range' (n := p.natDegree + 1)]
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [← RingHom.mapMatrix_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hpow : (A ^ i).map σ = (A.map σ) ^ i := by
      rw [← RingHom.mapMatrix_apply, map_pow]; rfl
    rw [coeff_map, RingHom.mapMatrix_apply, ← hpow]
    ext a b
    simp [Matrix.smul_apply]
  · exact Nat.lt_succ_of_le (natDegree_map_le)

theorem csr_pow_mul_pow {K : Type} [Field K] {n : ℕ} (γ B : Matrix (Fin n) (Fin n) K)
    (h : γ * B = 1) (d i : ℕ) (hi : i ≤ d) : γ ^ d * B ^ i = γ ^ (d - i) := by
  have key : ∀ j, γ ^ j * B ^ j = 1 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, pow_succ', mul_assoc, ← mul_assoc γ, h, one_mul, ih]
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [add_comm i e, pow_add, mul_assoc, key, mul_one, Nat.add_sub_cancel]

theorem csr_reverse {K : Type} [Field K] {n : ℕ} (γ B : Matrix (Fin n) (Fin n) K)
    (h : γ * B = 1) (P : K[X]) :
    γ ^ P.natDegree * aeval B P = aeval γ P.reverse := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range' (n := P.natDegree + 1), Finset.mul_sum]
  · rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have e1 : P.natDegree + 1 - 1 - i = P.natDegree - i := by omega
    rw [e1, mul_smul_comm, csr_pow_mul_pow γ B h _ _ (Nat.sub_le _ _), coeff_reverse,
      revAt_le hi']
    have e2 : P.natDegree - (P.natDegree - i) = i := by omega
    rw [e2]
  · exact Nat.lt_succ_of_le (reverse_natDegree_le P)

end GlobalTheory

namespace GlobalTheory

theorem csr_ker_orth_range {K : Type} [Field K] (σ : K →+* K) {n : ℕ}
    (γ : Matrix (Fin n) (Fin n) K) (hγ : (γ.map σ)ᵀ * γ = 1) (Q : K[X])
    (hQ : C (σ (Q.coeff 0)) * Q = (Q.map σ).reverse) (x z : Fin n → K)
    (hx : aeval γ Q *ᵥ x = 0) : ∑ k, σ ((aeval γ Q *ᵥ z) k) * x k = 0 := by
  have hγB : γ * (γ.map σ)ᵀ = 1 := mul_eq_one_comm.mp hγ
  have hMt : ((aeval γ Q).map σ)ᵀ = aeval (γ.map σ)ᵀ (Q.map σ) := by
    rw [csr_map_aeval, csr_transpose_aeval]
  have hrev : aeval γ (Q.map σ).reverse = σ (Q.coeff 0) • aeval γ Q := by
    rw [← hQ, aeval_mul, aeval_C, Algebra.smul_def]
  have hBd : (γ.map σ)ᵀ ^ (Q.map σ).natDegree * γ ^ (Q.map σ).natDegree = 1 := by
    rw [csr_pow_mul_pow _ _ hγ _ _ le_rfl, Nat.sub_self, pow_zero]
  have hBP : aeval (γ.map σ)ᵀ (Q.map σ)
      = (γ.map σ)ᵀ ^ (Q.map σ).natDegree * (σ (Q.coeff 0) • aeval γ Q) := by
    rw [← hrev, ← csr_reverse γ _ hγB, ← mul_assoc, hBd, one_mul]
  have hBx : aeval (γ.map σ)ᵀ (Q.map σ) *ᵥ x = 0 := by
    rw [hBP, ← mulVec_mulVec, smul_mulVec, hx, smul_zero, mulVec_zero]
  have expand : ∑ k, σ ((aeval γ Q *ᵥ z) k) * x k
      = ∑ l, σ (z l) * ((((aeval γ Q).map σ)ᵀ) *ᵥ x) l := by

    simp only [mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum,
    transpose_apply, map_apply]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [expand, hMt, hBx]
  simp

end GlobalTheory
end

section

open Matrix

namespace GlobalTheory

noncomputable def endRealMatrixRingHom {g n : ℕ} (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)) :
    Module.End ℂ (Fin g → ℂ) →+* Matrix (Fin n) (Fin n) ℝ where
  toFun f := LinearMap.toMatrix e e (f.restrictScalars ℝ)
  map_one' := by
    have : ((1 : Module.End ℂ (Fin g → ℂ)).restrictScalars ℝ) = 1 := rfl
    rw [this]; exact LinearMap.toMatrix_one e
  map_mul' f h := by
    have : ((f * h).restrictScalars ℝ) = f.restrictScalars ℝ * h.restrictScalars ℝ := rfl
    rw [this]; exact LinearMap.toMatrix_mul e _ _
  map_zero' := by
    have : ((0 : Module.End ℂ (Fin g → ℂ)).restrictScalars ℝ) = 0 := rfl
    rw [this]; exact map_zero _
  map_add' f h := by
    have : ((f + h).restrictScalars ℝ) = f.restrictScalars ℝ + h.restrictScalars ℝ := rfl
    rw [this]; exact map_add _ _ _

theorem endRealMatrixRingHom_injective {g n : ℕ} (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)) :
    Function.Injective (endRealMatrixRingHom e) := by
  intro f h hfh
  have h1 : f.restrictScalars ℝ = h.restrictScalars ℝ := (LinearMap.toMatrix e e).injective hfh
  exact LinearMap.restrictScalars_injective ℝ h1

theorem matrix_identity_transfer (g n : ℕ) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ))
    (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Tq : Matrix (Fin n) (Fin n) ℚ)
    (hT : Tq.map (Rat.cast : ℚ → ℝ) = LinearMap.toMatrix e e (γ.restrictScalars ℝ))
    (c₀ : ℚ) (r : ℕ) (c : Fin r → ℚ) (p : Fin r → Polynomial ℚ)
    (hid : (1 : Matrix (Fin n) (Fin n) ℚ) = c₀ • Tq + ∑ i, c i • ((Polynomial.aeval Tq (p i)) ^ 2 * Tq)) :
    (1 : Module.End ℂ (Fin g → ℂ)) = c₀ • γ + ∑ i, c i • ((Polynomial.aeval γ (p i)) ^ 2 * γ) := by
  let F := (endRealMatrixRingHom e).toRatAlgHom
  let ψ : Matrix (Fin n) (Fin n) ℚ →ₐ[ℚ] Matrix (Fin n) (Fin n) ℝ := (Algebra.ofId ℚ ℝ).mapMatrix
  have hψ : ∀ M, ψ M = M.map (Rat.cast : ℚ → ℝ) := by
    intro M; ext i j; simp [ψ]
  have hFγ : F γ = ψ Tq := by rw [hψ, hT]; rfl
  apply endRealMatrixRingHom_injective e
  change F 1 = F _
  have key := congrArg ψ hid
  rw [map_one] at key
  rw [map_one, key]

  simp only [map_add (f := _), map_sum, map_smul, map_mul, map_pow, ← Polynomial.aeval_algHom_apply, hFγ]

end GlobalTheory
end
