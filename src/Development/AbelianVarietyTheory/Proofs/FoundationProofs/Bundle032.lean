module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle041
public import Formalism.JacquetSubsetSums.JacquetSubsetSum
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
public import Mathlib.RingTheory.AdicCompletion.Completeness
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003

@[expose] public section

section

noncomputable section
open Polynomial
namespace GlobalTheory.K5.OnFree

section General

variable {R : Type*} [CommRing R] (f : R[X]) (m : ℕ) (c : R)

abbrev relIdeal : Ideal R[X][X] := Ideal.span {C f, X ^ m - C (C c)}

abbrev topPoly : (AdjoinRoot f)[X] := X ^ m - C (algebraMap R (AdjoinRoot f) c)

def toAdj : (R[X][X] ⧸ relIdeal f m c) →ₐ[R] AdjoinRoot (topPoly f m c) :=
  Ideal.Quotient.liftₐ (relIdeal f m c)
    (Polynomial.eval₂AlgHom
      (Polynomial.aeval (AdjoinRoot.of (topPoly f m c) (AdjoinRoot.root f)))
      (AdjoinRoot.root (topPoly f m c)) (fun _ => Commute.all _ _)) (by
      have h : relIdeal f m c ≤ RingHom.ker (Polynomial.eval₂AlgHom
          (Polynomial.aeval (R := R) (AdjoinRoot.of (topPoly f m c) (AdjoinRoot.root f)))
          (AdjoinRoot.root (topPoly f m c)) (fun _ => Commute.all _ _)) := by
        rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
        constructor
        · have h1 : aeval (AdjoinRoot.of (topPoly f m c) (AdjoinRoot.root f)) f = 0 := by
            rw [← AdjoinRoot.algebraMap_eq, aeval_algebraMap_apply, AdjoinRoot.aeval_eq,
              AdjoinRoot.mk_self, map_zero]
          simpa [RingHom.mem_ker] using h1
        · have h2 := AdjoinRoot.eval₂_root (topPoly f m c)
          simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h2
          simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_pow]
          change eval₂ _ _ X ^ m - eval₂ _ _ (C (C c)) = 0
          rw [eval₂_X, eval₂_C, RingHom.coe_coe, aeval_C,
            IsScalarTower.algebraMap_apply R (AdjoinRoot f)]
          exact h2
      exact fun a ha => h ha)

def baseToQuot : AdjoinRoot f →ₐ[R] (R[X][X] ⧸ relIdeal f m c) :=
  AdjoinRoot.liftAlgHom f (Algebra.ofId R _) (Ideal.Quotient.mk (relIdeal f m c) (C X)) (by
    have h : (Ideal.Quotient.mkₐ R (relIdeal f m c)) (C f) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (by simp))
    have h2 : aeval ((Ideal.Quotient.mkₐ R (relIdeal f m c)) (CAlgHom (R := R) (X : R[X]))) f = 0 := by
      rw [aeval_algHom_apply, aeval_algHom_apply, aeval_X_left_apply]
      exact h
    exact h2)

def toQuot : AdjoinRoot (topPoly f m c) →ₐ[R] (R[X][X] ⧸ relIdeal f m c) :=
  AdjoinRoot.liftAlgHom (topPoly f m c) (baseToQuot f m c)
    (Ideal.Quotient.mk (relIdeal f m c) X) (by
    have h : (Ideal.Quotient.mk (relIdeal f m c)) (X ^ m - C (C c)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (by simp))
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C, RingHom.coe_coe, AlgHom.commutes]
    rw [map_sub, map_pow] at h
    exact h)

theorem toQuot_root : toQuot f m c (AdjoinRoot.root _) = Ideal.Quotient.mk (relIdeal f m c) X := by
  simp [toQuot]

theorem toQuot_of_root : toQuot f m c (AdjoinRoot.of _ (AdjoinRoot.root f)) =
    Ideal.Quotient.mk (relIdeal f m c) (C X) := by
  have h : baseToQuot f m c (AdjoinRoot.root f) = Ideal.Quotient.mk (relIdeal f m c) (C X) :=
    AdjoinRoot.liftAlgHom_root _ _ _ _
  rw [← h]
  simp [toQuot]

theorem toAdj_X : toAdj f m c (Ideal.Quotient.mk (relIdeal f m c) X) = AdjoinRoot.root _ := by
  change eval₂ _ _ X = _
  rw [eval₂_X]

theorem toAdj_C_X : toAdj f m c (Ideal.Quotient.mk (relIdeal f m c) (C X)) =
    AdjoinRoot.of _ (AdjoinRoot.root f) := by
  change eval₂ _ _ (C X) = _
  rw [eval₂_C, RingHom.coe_coe, aeval_X]

def adjEquiv : AdjoinRoot (topPoly f m c) ≃ₐ[R] (R[X][X] ⧸ relIdeal f m c) :=
  AlgEquiv.ofAlgHom (toQuot f m c) (toAdj f m c)
    (by
      refine Ideal.Quotient.algHom_ext R ?_
      refine Polynomial.algHom_ext' ?_ ?_
      · refine Polynomial.algHom_ext ?_
        have := toQuot_of_root f m c
        rw [← toAdj_C_X] at this
        exact this
      · have := toQuot_root f m c
        rw [← toAdj_X] at this
        exact this)
    (by
      refine AdjoinRoot.algHom_ext' ?_ ?_
      · refine AdjoinRoot.algHom_ext ?_
        have := toAdj_C_X f m c
        rw [← toQuot_of_root] at this
        exact this
      · have := toAdj_X f m c
        rw [← toQuot_root] at this
        exact this)

theorem exists_basis [Nontrivial R] (hf : f.Monic) (d : ℕ) (hd : f.natDegree = d) (hd0 : 0 < d)
    (hm : m ≠ 0) :
    ∃ b : Module.Basis (Fin d × Fin m) R (R[X][X] ⧸ relIdeal f m c),
      ∀ i j, b (i, j) = (Ideal.Quotient.mk (relIdeal f m c) (C X)) ^ (i : ℕ) *
        (Ideal.Quotient.mk (relIdeal f m c) X) ^ (j : ℕ) := by
  let b₁ : Module.Basis (Fin d) R (AdjoinRoot f) :=
    (AdjoinRoot.powerBasis' hf).basis.reindex (finCongr hd)
  have hb₁ : ∀ i, b₁ i = AdjoinRoot.root f ^ (i : ℕ) := by
    intro i
    simp only [b₁, Module.Basis.reindex_apply, PowerBasis.coe_basis]
    rfl
  haveI : Nontrivial (AdjoinRoot f) := nontrivial_of_ne _ _ (b₁.ne_zero ⟨0, hd0⟩)
  have hg : (topPoly f m c).Monic := monic_X_pow_sub_C _ hm
  have hgd : (topPoly f m c).natDegree = m := natDegree_X_pow_sub_C _
  let b₂ : Module.Basis (Fin m) (AdjoinRoot f) (AdjoinRoot (topPoly f m c)) :=
    (AdjoinRoot.powerBasis' hg).basis.reindex (finCongr hgd)
  have hb₂ : ∀ j, b₂ j = AdjoinRoot.root (topPoly f m c) ^ (j : ℕ) := by
    intro j
    simp only [b₂, Module.Basis.reindex_apply, PowerBasis.coe_basis]
    rfl
  refine ⟨(b₁.smulTower b₂).map (adjEquiv f m c).toLinearEquiv, fun i j => ?_⟩
  rw [Module.Basis.map_apply, Module.Basis.smulTower_apply, hb₁, hb₂, Algebra.smul_def,
    AdjoinRoot.algebraMap_eq, ← toQuot_of_root, ← toQuot_root, ← map_pow (toQuot f m c),
    ← map_pow (toQuot f m c), ← map_mul, map_pow]
  rfl

end General

theorem on_free (p : ℕ) [hp : Fact p.Prime] (n : ℕ) :
    ∃ b : Module.Basis (Fin (Nat.totient (p ^ n)) × Fin (p ^ n)) (O0 p) (On p n),
      ∀ i j, b (i, j) = xn p n ^ (i : ℕ) * yn p n ^ (j : ℕ) := by
  rcases subsingleton_or_nontrivial (O0 p) with h | h
  · haveI : Subsingleton (On p n) := Module.subsingleton (O0 p) _
    exact ⟨Module.Basis.ofRepr (LinearEquiv.ofSubsingleton _ _), fun _ _ => Subsingleton.elim _ _⟩
  · have hpos : 0 < p ^ n := pow_pos hp.out.pos n
    exact exists_basis (cyclotomic (p ^ n) (O0 p)) (p ^ n) (qO p) (cyclotomic.monic _ _) _
      (natDegree_cyclotomic _ _) (Nat.totient_pos.2 hpos) hpos.ne'

end GlobalTheory.K5.OnFree
end
end

section

open GlobalTheory.K5

namespace GlobalTheory.K5.ReprInd

theorem aux {R Ω : Type*} [CommRing R] [IsDomain R] [AddCommGroup Ω] [Module R Ω] (P : Ω → Prop) :
    ∀ (m : ℕ) (a : Fin m → Ω) (f : Fin m → R), (∀ i, P (a i)) →
      ∃ (n : ℕ) (a' : Fin n → Ω) (f' : Fin n → R) (g : R), (∀ i, P (a' i)) ∧
        LinearIndependent R a' ∧ g ≠ 0 ∧ g • (∑ i, f i • a i) = ∑ i, f' i • a' i := by
  intro m
  induction m with
  | zero =>
    intro a f _
    refine ⟨0, a, f, 1, by simp, linearIndependent_empty_type, one_ne_zero, by simp⟩
  | succ m ih =>
    intro a f hP
    by_cases hli : LinearIndependent R a
    · exact ⟨m + 1, a, f, 1, hP, hli, one_ne_zero, one_smul _ _⟩
    · obtain ⟨c, hc, k, hk⟩ := Fintype.not_linearIndependent_iff.mp hli
      obtain ⟨n, a', f', g, hP', hli', hg, heq⟩ := ih (fun j => a (k.succAbove j))
        (fun j => c k * f (k.succAbove j) - f k * c (k.succAbove j)) (fun j => hP _)
      refine ⟨n, a', f', g * c k, hP', hli', mul_ne_zero hg hk, ?_⟩
      have key : c k • (∑ i, f i • a i) =
          ∑ j : Fin m, (c k * f (k.succAbove j) - f k * c (k.succAbove j)) • a (k.succAbove j) := by
        have h1 : c k • (∑ i, f i • a i) = c k • (∑ i, f i • a i) - f k • (∑ i, c i • a i) := by
          rw [hc, smul_zero, sub_zero]
        rw [h1, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib,
          Fin.sum_univ_succAbove _ k]
        simp only [smul_smul, ← sub_smul]
        rw [mul_comm (f k) (c k), sub_self, zero_smul, zero_add]
      rw [mul_smul, key, heq]

theorem main {R Ω : Type*} [CommRing R] [IsDomain R] [Field Ω] [Algebra R Ω] (P : Ω → Prop) :
    ∀ y ∈ Submodule.span R {x : Ω | P x},
    ∃ (n : ℕ) (a : Fin n → Ω) (f : Fin n → R) (g : R), (∀ i, P (a i)) ∧
      LinearIndependent R a ∧ g ≠ 0 ∧
      algebraMap R Ω g * y = ∑ i, algebraMap R Ω (f i) * a i := by
  intro y hy
  obtain ⟨m, f, a, rfl⟩ := Submodule.mem_span_set'.mp hy
  obtain ⟨n, a', f', g, hP', hli', hg, heq⟩ := aux P m (fun i => (a i : Ω)) f (fun i => (a i).2)
  refine ⟨n, a', f', g, hP', hli', hg, ?_⟩
  simpa only [Algebra.smul_def] using heq

end GlobalTheory.K5.ReprInd

theorem GlobalTheory.K5.algSpan_reprInd : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ y ∈ Submodule.span (O0 p) {x : Ω | IsAlgZp (p := p) x},
    ∃ (n : ℕ) (a : Fin n → Ω) (f : Fin n → O0 p) (g : O0 p), (∀ i, IsAlgZp (p := p) (a i)) ∧
      LinearIndependent (O0 p) a ∧ g ≠ 0 ∧
      algebraMap (O0 p) Ω g * y = ∑ i, algebraMap (O0 p) Ω (f i) * a i := by
  intro p _ Ω _ _ _
  exact GlobalTheory.K5.ReprInd.main (fun x => IsAlgZp (p := p) x)
end

section

open GlobalTheory.K5

namespace GlobalTheory.K5.Basic

theorem exists_not_prime_pow_dvd_completedLaurent (p : ℕ) [Fact p.Prime] (x : O0 p) (hx : x ≠ 0) :
    ∃ a : ℕ, ¬ (p : O0 p) ^ a ∣ x := by
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective (pI p) (Lau p) x
  obtain ⟨a, ha⟩ := exists_not_dvd p s hx
  refine ⟨a, ?_⟩
  rintro ⟨z, hz⟩
  apply ha a le_rfl
  have h1 := congrArg (AdicCompletion.evalₐ (pI p) a) hz
  rw [AdicCompletion.evalₐ_mk, map_mul, map_pow, map_natCast,
    ← map_natCast (Ideal.Quotient.mk (pI p ^ a)), ← map_pow] at h1
  have h2 : Ideal.Quotient.mk (pI p ^ a) ((p : Lau p) ^ a) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, mem_pI_pow]
  rw [h2, zero_mul, Ideal.Quotient.eq_zero_iff_mem, mem_pI_pow] at h1
  exact h1

theorem exists_eq_prime_pow_mul_not_dvd_completedLaurent : ∀ (p : ℕ) [Fact p.Prime], ∀ x : O0 p, x ≠ 0 →
    ∃ (k : ℕ) (y : O0 p), x = (p : O0 p) ^ k * y ∧ ¬ (p : O0 p) ∣ y := by
  intro p _ x hx
  obtain ⟨a, ha⟩ := exists_not_prime_pow_dvd_completedLaurent p x hx
  have hfin : FiniteMultiplicity (p : O0 p) x :=
    ⟨a, fun h => ha ((pow_dvd_pow _ (Nat.le_succ a)).trans h)⟩
  obtain ⟨y, hy, hnd⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  exact ⟨_, y, hy, hnd⟩

end GlobalTheory.K5.Basic
end

section

open GlobalTheory.K5 Polynomial

namespace GlobalTheory.K5

def dlogSub (p : ℕ) [Fact p.Prime] (n : ℕ) : Subalgebra (O0 p) (On p n) where
  carrier := {w | KaehlerDifferential.D (O0 p) (On p n) w ∈
    Submodule.span (On p n) ({KaehlerDifferential.D (O0 p) (On p n) (xn p n),
      KaehlerDifferential.D (O0 p) (On p n) (yn p n)} : Set _)}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Derivation.leibniz] at *
    exact add_mem (Submodule.smul_mem _ _ hb) (Submodule.smul_mem _ _ ha)
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add (f := _)] at *
    exact add_mem ha hb
  algebraMap_mem' := by
    intro r
    simp only [Set.mem_setOf_eq, Derivation.map_algebraMap]
    exact zero_mem _

theorem mem_dlogSub (p : ℕ) [Fact p.Prime] (n : ℕ) (w : On p n) : w ∈ dlogSub p n := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective w
  have hx : xn p n ∈ dlogSub p n :=
    Submodule.subset_span (Set.mem_insert _ _)
  have hy : yn p n ∈ dlogSub p n :=
    Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hC : ∀ a : Polynomial (O0 p), Ideal.Quotient.mk (towerIdeal p n) (C a) ∈ dlogSub p n := by
    intro a
    induction a using Polynomial.induction_on with
    | C r =>
      have : Ideal.Quotient.mk (towerIdeal p n) (C (C r)) = algebraMap (O0 p) (On p n) r := rfl
      rw [this]; exact Subalgebra.algebraMap_mem _ r
    | add a b ha hb => rw [Polynomial.C_add, RingHom.map_add (Ideal.Quotient.mk (towerIdeal p n))]; exact add_mem ha hb
    | monomial k r _ =>
      rw [Polynomial.C_mul, Polynomial.C_pow, map_mul, map_pow]
      refine mul_mem ?_ (pow_mem hx _)
      have : Ideal.Quotient.mk (towerIdeal p n) (C (C r)) = algebraMap (O0 p) (On p n) r := rfl
      rw [this]; exact Subalgebra.algebraMap_mem _ r
  induction f using Polynomial.induction_on with
  | C a => exact hC a
  | add a b ha hb => rw [RingHom.map_add (Ideal.Quotient.mk (towerIdeal p n))]; exact add_mem ha hb
  | monomial k a _ =>
    rw [map_mul, map_pow]
    exact mul_mem (hC a) (pow_mem hy _)

theorem exists_isDlog : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (w : (On p n)ˣ), ∃ α β : On p n, IsDlog p n (w : On p n) α β := by
  intro p _ n w
  have h : KaehlerDifferential.D (O0 p) (On p n) (w : On p n) ∈
      Submodule.span (On p n) ({KaehlerDifferential.D (O0 p) (On p n) (xn p n),
        KaehlerDifferential.D (O0 p) (On p n) (yn p n)} : Set _) := mem_dlogSub p n (w : On p n)
  obtain ⟨P, Q, hPQ⟩ := Submodule.mem_span_pair.mp h
  refine ⟨yn p n * Q * ((w⁻¹ : (On p n)ˣ) : On p n), xn p n * P * ((w⁻¹ : (On p n)ˣ) : On p n), ?_⟩
  unfold IsDlog
  rw [← hPQ, smul_add, smul_smul, smul_smul, add_comm]
  congr 1
  · congr 1
    have := w.mul_inv
    linear_combination (xn p n * yn p n * Q) * (-this)
  · congr 1
    have := w.mul_inv
    linear_combination (xn p n * yn p n * P) * (-this)

end GlobalTheory.K5
end

section

open GlobalTheory.K5

namespace GlobalTheory.K5

noncomputable def lauRed (p : ℕ) [Fact p.Prime] : Lau p →+* LaurentSeries (ZMod p) where
  toFun x := HahnSeries.map x (PadicInt.toZMod (p := p))
  map_one' := HahnSeries.map_one (PadicInt.toZMod (p := p)).toMonoidWithZeroHom
  map_mul' x y := HahnSeries.map_mul (PadicInt.toZMod (p := p)).toNonUnitalRingHom
  map_zero' := by ext n; simp
  map_add' x y := by ext n; simp

theorem lauRed_coeff (p : ℕ) [Fact p.Prime] (x : Lau p) (n : ℤ) :
    (lauRed p x).coeff n = PadicInt.toZMod (x.coeff n) := rfl

theorem lauRed_surjective (p : ℕ) [Fact p.Prime] : Function.Surjective (lauRed p) := by
  intro y
  refine ⟨HahnSeries.map y (⟨fun a => ((ZMod.val a : ℕ) : ℤ_[p]), by simp⟩ : ZeroHom (ZMod p) ℤ_[p]), ?_⟩
  ext n
  rw [lauRed_coeff]
  show PadicInt.toZMod ((ZMod.val (y.coeff n) : ℕ) : ℤ_[p]) = _
  simp

theorem ker_lauRed (p : ℕ) [Fact p.Prime] : RingHom.ker (lauRed p) = pI p := by
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    have h : ∀ n, ∃ c : ℤ_[p], x.coeff n = (p : ℤ_[p]) * c := by
      intro n
      have h1 : x.coeff n ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
        rw [RingHom.mem_ker, ← lauRed_coeff, hx]; rfl
      rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h1
      exact h1
    choose c hc using h
    have hp : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    refine Ideal.mem_span_singleton.2 ⟨⟨c, x.isPWO_support.mono ?_⟩, ?_⟩
    · intro n hn
      rw [HahnSeries.mem_support, hc n]
      exact mul_ne_zero hp hn
    · ext n
      rw [← nsmul_eq_mul, HahnSeries.coeff_nsmul, hc n]
      simp
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    show lauRed p _ = 0
    rw [map_natCast]
    ext n
    rw [← Nat.smul_one_eq_cast, HahnSeries.coeff_nsmul]
    simp

theorem exists_completedLaurent_quot_prime_equiv_laurentFp (p : ℕ) [Fact p.Prime] : ∃ e : (O0 p ⧸ Ideal.span {(p : O0 p)}) ≃+* LaurentSeries (ZMod p),
    e (Ideal.Quotient.mk _ (qO p)) = HahnSeries.single (1 : ℤ) (1 : ZMod p) := by
  have fg : (pI p).FG := Submodule.fg_span_singleton _
  have hker := AdicCompletion.ker_evalOneₐ_eq_map (pI p) fg
  have hsurj : Function.Surjective (AdicCompletion.evalOneₐ (pI p)) := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨algebraMap _ _ a, (AdicCompletion.evalOneₐ (pI p)).commutes a⟩
  have hmap : (pI p).map (algebraMap (Lau p) (O0 p)) = Ideal.span {(p : O0 p)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have h1 : Ideal.span {(p : O0 p)} = RingHom.ker (AdicCompletion.evalOneₐ (pI p)).toRingHom := by
    rw [← hmap]; exact hker.symm
  refine ⟨(Ideal.quotEquivOfEq h1).trans
    ((RingHom.quotientKerEquivOfSurjective (f := (AdicCompletion.evalOneₐ (pI p)).toRingHom) hsurj).trans
      ((Ideal.quotEquivOfEq (ker_lauRed p).symm).trans
        (RingHom.quotientKerEquivOfSurjective (lauRed_surjective p)))), ?_⟩
  simp only [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]
  have hq : (AdicCompletion.evalOneₐ (pI p)).toRingHom (qO p) =
      Ideal.Quotient.mk (pI p) (HahnSeries.single (1 : ℤ) (1 : ℤ_[p])) :=
    (AdicCompletion.evalOneₐ (pI p)).commutes _
  rw [hq, Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]
  ext n
  rw [lauRed_coeff]
  by_cases hn : n = 1
  · subst hn; simp
  · simp [HahnSeries.coeff_single_of_ne hn]

end GlobalTheory.K5
end

section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5

theorem o0_isAdicComplete_span_p : ∀ (p : ℕ) [Fact p.Prime], IsAdicComplete (Ideal.span {(p : O0 p)}) (O0 p) := by
  intro p _
  have hfg : (pI p).FG := ⟨{(p : Lau p)}, by simp⟩
  have h : IsAdicComplete (pI p) (O0 p) := AdicCompletion.isAdicComplete hfg
  have hmap : (pI p).map (algebraMap (Lau p) (O0 p)) = Ideal.span {(p : O0 p)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  rw [← hmap]
  exact { toIsHausdorff := IsHausdorff.map_algebraMap_iff.2 h.toIsHausdorff
          toIsPrecomplete := IsPrecomplete.map_algebraMap_iff.2 h.toIsPrecomplete }

end GlobalTheory.K5
end

section

noncomputable section

namespace GlobalTheory.K5

variable (p : ℕ) [Fact p.Prime]

theorem natCast_dvd_iff_evalₐ_one (x : O0 p) :
    (p : O0 p) ∣ x ↔ AdicCompletion.evalₐ (pI p) 1 x = 0 := by
  rw [GlobalTheory.ValCompletion.evalₐ_eq_zero_iff rfl, pow_one, map_natCast]

theorem prime_natCast_completedLaurentRing : Prime (p : O0 p) := by
  haveI : (pI p ^ 1).IsPrime := by
    rw [pow_one]; exact (Ideal.span_singleton_prime (Basic.prime_lau p).ne_zero).2 (Basic.prime_lau p)
  refine ⟨?_, Basic.not_isUnit_p p, ?_⟩
  · exact_mod_cast (Nat.Prime.ne_zero Fact.out : p ≠ 0)
  · intro a b h
    rw [natCast_dvd_iff_evalₐ_one, map_mul] at h
    rw [natCast_dvd_iff_evalₐ_one, natCast_dvd_iff_evalₐ_one]
    exact mul_eq_zero.1 h

theorem prime_natCast_completedLaurentRing_of_prime : ∀ (p : ℕ) [Fact p.Prime], Prime (p : O0 p) := fun p _ => prime_natCast_completedLaurentRing p

end GlobalTheory.K5
end
end

section

namespace GlobalTheory

theorem signEven : Formalism.PacketSums.SignEven := by
  intro p q h
  apply Even.neg_one_pow
  rw [Nat.even_mul]
  rcases Nat.even_or_odd p with hp | hp
  · exact Or.inl hp
  · right
    rcases Nat.even_or_odd q with hq | hq
    · exact hq
    · exact absurd (hp.add_odd hq) (Nat.not_even_iff_odd.mpr h)

end GlobalTheory
end
