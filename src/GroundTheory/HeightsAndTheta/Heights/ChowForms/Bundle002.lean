module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle001
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
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
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.MvPolynomial.Localization

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def firstGroup {F : Type*} [Field F] {n e : ℕ} (f : MvPolynomial (Fin (e + 1) × Fin n) F) :
    MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F) :=
  aeval (fun ij : Fin (e + 1) × Fin n =>
    Fin.cases (motive := fun _ => MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F))
      (X ij.2) (fun i => C (X (i, ij.2))) ij.1) f

def ChartFirstGroupPrime.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime],
    IsProjPrime I → IsChowForm I (e + 1) f →
      Prime (map (algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p)) (firstGroup f))

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def DehomogOrd.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (I W : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F),
    IsHomogIdeal I → IsHomogIdeal W → I ≤ W → linForm t ∉ W →
    ∀ [(W.map (Ideal.Quotient.mk I)).IsPrime]
      [(W.map (Ideal.Quotient.mk (I ⊔ Ideal.span {linForm t - 1}))).IsPrime]
      (g : MvPolynomial (Fin n) F) (d : ℕ), g.IsHomogeneous d →
      Ring.ord (Localization.AtPrime (W.map (Ideal.Quotient.mk I)))
          (algebraMap _ _ (Ideal.Quotient.mk I g)) =
        Ring.ord (Localization.AtPrime (W.map (Ideal.Quotient.mk (I ⊔ Ideal.span {linForm t - 1}))))
          (algebraMap _ _ (Ideal.Quotient.mk (I ⊔ Ideal.span {linForm t - 1}) g))

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

def LocalMultOrd.Statement : Prop :=
  ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (I W : Ideal A) (x : A)
    [(W.map (Ideal.Quotient.mk I)).IsPrime], W ∈ (I ⊔ Ideal.span {x}).minimalPrimes →
      ((localMult (I ⊔ Ideal.span {x}) W : ℕ) : ℕ∞) =
        Ring.ord (Localization.AtPrime (W.map (Ideal.Quotient.mk I)))
          (algebraMap _ _ (Ideal.Quotient.mk I x))

section Inhabitants

open MvPolynomial

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem NormFormEmbeddings.proof (h : NormFormEval.Statement) : NormFormEmbeddings.Statement := by
  intro K L Ω _ _ _ _ _ _ _ _ _ n η
  have hs : ∀ _ : Fin n, (Set.range (algebraMap K Ω)).Infinite :=
    fun _ => Set.infinite_range_of_injective (algebraMap K Ω).injective
  refine MvPolynomial.funext_set (fun _ => Set.range (algebraMap K Ω)) hs ?_
  intro x hx
  choose u hu using fun m => hx m (Set.mem_univ m)
  obtain rfl : x = algebraMap K Ω ∘ u := funext fun m => (hu m).symm
  have hl : eval (algebraMap K Ω ∘ u) (map (algebraMap K Ω) (normForm K L η)) =
      algebraMap K Ω (eval u (normForm K L η)) := by
    rw [eval_map]
    change _ = algebraMap K Ω (eval₂ (RingHom.id K) u (normForm K L η))
    rw [eval₂_comp_left]
    rfl
  rw [hl, h K L n η u, Algebra.norm_eq_prod_embeddings]

  simp only [map_prod, map_sum, map_mul, eval_X, eval_C, Function.comp_apply]
  refine Finset.prod_congr rfl fun σ _ => Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, Algebra.smul_def]

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem NormFormDvd.proof (h₁ : NormFormEmbeddings.Statement) (h₂ : LinearFormPrime.Statement)
    (h₃ : MapDvdDescent.Statement) : NormFormDvd.Statement := by
  intro K L _ _ _ _ _ _ n η t P hgen ht hdvd
  classical
  apply h₃ K (AlgebraicClosure K) (Fin n)
  rw [h₁ K L (AlgebraicClosure K) n η]
  set θ : (L →ₐ[K] AlgebraicClosure K) → MvPolynomial (Fin n) (AlgebraicClosure K) :=
    fun σ => ∑ m, X m * C (σ (η m)) with hθ

  have hev : ∀ σ, eval (fun m => algebraMap K (AlgebraicClosure K) (t m)) (θ σ) = 1 := by
    intro σ
    have h := congrArg σ ht

    simp only [map_sum, map_one, Algebra.smul_def, map_mul, AlgHom.commutes] at h

    simpa [hθ, map_sum, mul_comm] using h

  have hcoord : ∀ σ m, eval (Pi.single m 1) (θ σ) = σ (η m) := by
    intro σ m
    simp [hθ, Pi.single_apply]
  have hprime : ∀ σ, Prime (θ σ) := by
    intro σ
    refine h₂ (AlgebraicClosure K) n (fun m => σ (η m)) ?_
    intro h0
    have h := hev σ
    have hz : θ σ = 0 := by simp only [hθ]; simp [funext_iff] at h0; simp [h0]
    rw [hz, map_zero] at h
    exact zero_ne_one h
  have hdiv : ∀ σ, θ σ ∣ map (algebraMap K (AlgebraicClosure K)) P := by
    intro σ
    obtain ⟨Q, hQ⟩ := hdvd
    refine ⟨map (σ : L →+* AlgebraicClosure K) Q, ?_⟩
    have h := congrArg (map (σ : L →+* AlgebraicClosure K)) hQ
    rw [map_map, AlgHom.comp_algebraMap, map_mul] at h
    rw [h]
    congr 1

    simp [hθ, map_sum]
  have hinj : ∀ a b, θ a ∣ θ b → a = b := by
    intro a b hab
    obtain ⟨u, hu⟩ := (hprime a).associated_of_dvd (hprime b) hab
    obtain ⟨c, -, hc⟩ := isUnit_iff_eq_C_of_isReduced.1 u.isUnit
    rw [hc] at hu
    have h1 := congrArg (eval (fun m => algebraMap K (AlgebraicClosure K) (t m))) hu
    rw [eval_mul, hev, hev, eval_C, one_mul] at h1
    rw [h1, C_1, mul_one] at hu
    refine AlgHom.ext_of_adjoin_eq_top hgen ?_
    rintro _ ⟨m, rfl⟩
    rw [← hcoord a m, ← hcoord b m, hu]
  have key : ∀ s : Finset (L →ₐ[K] AlgebraicClosure K),
      ∏ σ ∈ s, θ σ ∣ map (algebraMap K (AlgebraicClosure K)) P := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      obtain ⟨R, hR⟩ := ih
      have h := hdiv a
      rw [hR] at h
      rcases (hprime a).dvd_or_dvd h with h' | h'
      · exfalso
        obtain ⟨b, hb, hab⟩ := ((hprime a).dvd_finsetProd_iff _).1 h'
        exact ha (by rw [hinj a b hab]; exact hb)
      · obtain ⟨S, hS⟩ := h'
        exact ⟨S, by rw [hR, hS]; ring⟩
  exact key Finset.univ

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem MapDvdDescent.proof : MapDvdDescent.Statement := by
  classical
  intro K Ω _ _ _ σ f g ⟨G, hG⟩
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K Ω)
    (LinearMap.ker_eq_bot.mpr (algebraMap K Ω).injective)
  have hπa : ∀ a : K, π (algebraMap K Ω a) = a := fun a => by
    simpa using LinearMap.congr_fun hπ a
  have hπm : ∀ (a : K) (y : Ω), π (algebraMap K Ω a * y) = a * π y := fun a y => by
    rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

  let Φ : MvPolynomial σ K := ∑ s ∈ G.support, monomial s (π (AddMonoidAlgebra.coeff G s))
  have hΦ : ∀ s, AddMonoidAlgebra.coeff Φ s = π (AddMonoidAlgebra.coeff G s) := fun s => by
    simp only [Φ, coeff_sum, coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [notMem_support_iff.mp h, map_zero]
  refine ⟨Φ, ?_⟩
  ext s
  have h1 := congrArg (fun P => π (AddMonoidAlgebra.coeff P s)) hG

  simp only [coeff_map, hπa, coeff_mul, map_sum, hπm] at h1
  rw [h1, coeff_mul]
  exact Finset.sum_congr rfl fun x _ => by rw [hΦ]

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem linearForm_coeff_single {F : Type} [Field F] {n : ℕ} (a : Fin n → F) (i : Fin n) :
    (∑ m, X m * C (a m) : MvPolynomial (Fin n) F).coeff (Finsupp.single i 1) = a i := by
  classical
  rw [coeff_sum, Finset.sum_eq_single i]
  · rw [mul_comm, coeff_C_mul, coeff_X]
    simp
  · intro j _ hji
    rw [mul_comm, coeff_C_mul, coeff_X, if_neg, mul_zero]
    intro h
    exact hji ((Finsupp.single_left_inj one_ne_zero).mp h)
  · simp

theorem LinearFormPrime.proof : LinearFormPrime.Statement := by
  intro F _ n a ha
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h
    push Not at h
    exact ha (funext h)
  refine Irreducible.prime (irreducible_of_totalDegree_eq_one ?_ ?_)
  · apply le_antisymm
    · refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun m _ => ?_)
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_X, totalDegree_C]
    · have hs : Finsupp.single i 1 ∈ (∑ m, X m * C (a m) : MvPolynomial (Fin n) F).support := by
        rw [mem_support_iff, linearForm_coeff_single]
        exact hi
      simpa using le_totalDegree hs
  · intro x hx
    have h := hx (Finsupp.single i 1)
    rw [linearForm_coeff_single] at h
    refine isUnit_iff_ne_zero.mpr ?_
    rintro rfl
    exact hi (zero_dvd_iff.mp h)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem NormFormEval.proof : NormFormEval.Statement := by
  intro R S _ _ _ _ _ n η u
  classical
  rw [Algebra.norm_eq_matrix_det (Module.Free.chooseBasis R S)]
  unfold normForm
  rw [RingHom.map_det]
  congr 1
  ext i j

  simp [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem PrimeMapFractionRing.proof : PrimeMapFractionRing.Statement := by
  intro O K _ _ _ _ _ n P hP hnc
  classical
  set M : Submonoid (MvPolynomial (Fin n) O) := (nonZeroDivisors O).map (C (σ := Fin n))
  have : IsLocalization M (MvPolynomial (Fin n) K) :=
    MvPolynomial.isLocalization (σ := Fin n) (nonZeroDivisors O) K

  have hprime : (Ideal.span {P}).IsPrime := (Ideal.span_singleton_prime hP.ne_zero).mpr hP
  have hdisj : Disjoint (M : Set (MvPolynomial (Fin n) O)) ↑(Ideal.span {P}) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ hmem
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
    have hCa : (C a : MvPolynomial (Fin n) O) ≠ 0 := by simpa using ha0
    have hdvd : P ∣ C a := Ideal.mem_span_singleton.mp hmem
    have hdeg : P.totalDegree = 0 := by
      have := totalDegree_le_of_dvd_of_isDomain hdvd hCa
      rw [totalDegree_C] at this
      omega
    exact hnc _ (totalDegree_eq_zero_iff_eq_C.mp hdeg)
  have hmap := IsLocalization.isPrime_of_isPrime_disjoint M (MvPolynomial (Fin n) K) _ hprime hdisj
  rw [Ideal.map_span, Set.image_singleton, MvPolynomial.algebraMap_def] at hmap

  have hinj : Function.Injective (map (σ := Fin n) (algebraMap O K)) :=
    map_injective _ (IsFractionRing.injective O K)
  have hne : map (algebraMap O K) P ≠ 0 := by
    intro h
    exact hP.ne_zero (hinj (by rw [h, map_zero]))
  exact (Ideal.span_singleton_prime hne).mp hmap

end GroundTheory.Heights₂.Heights
end
