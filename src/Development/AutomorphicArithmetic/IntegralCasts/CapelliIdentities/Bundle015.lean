module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Tactic.Continuity
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Algebra.Polynomial.AlgebraMap
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
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Algebra.ConstMulAction

@[expose] public section

section

noncomputable def UpperTheory.Reformulated.B.Qi29.polyDeriv :
    {n : ℕ} → MvPolynomial (Fin n) ℂ → EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ :=
    fun {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) ↦
      ∑ l : Fin n,
        (MvPolynomial.eval fun (i : Fin n) ↦ x.ofLp i : MvPolynomial (Fin n) ℂ → ℂ)
            ((MvPolynomial.pderiv l : MvPolynomial (Fin n) ℂ → MvPolynomial (Fin n) ℂ) p) •
          EuclideanSpace.proj l

theorem UpperTheory.Reformulated.B.Qi29.hasStrictFDerivAt_eval :
    ∀ {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)),
      HasStrictFDerivAt
        (fun (y : EuclideanSpace ℂ (Fin n)) ↦ (MvPolynomial.eval fun (i : Fin n) ↦ y.ofLp i : MvPolynomial (Fin n) ℂ → ℂ) p)
        (UpperTheory.Reformulated.B.Qi29.polyDeriv p x) x := by
  intro n p x
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h : UpperTheory.Reformulated.B.Qi29.polyDeriv (MvPolynomial.C a : MvPolynomial (Fin n) ℂ) x = 0 := by
      simp [UpperTheory.Reformulated.B.Qi29.polyDeriv]
    rw [h]
    simp only [MvPolynomial.eval_C]
    exact hasStrictFDerivAt_const a x
  | add p q hp hq =>
    have h : UpperTheory.Reformulated.B.Qi29.polyDeriv (p + q) x
        = UpperTheory.Reformulated.B.Qi29.polyDeriv p x + UpperTheory.Reformulated.B.Qi29.polyDeriv q x := by
      simp only [UpperTheory.Reformulated.B.Qi29.polyDeriv, map_add (f := _), add_smul, Finset.sum_add_distrib]
    rw [h]
    simp only [map_add (f := _)]
    exact hp.add hq
  | mul_X p i hp =>
    have hi : HasStrictFDerivAt (fun y : EuclideanSpace ℂ (Fin n) ↦ y.ofLp i)
        (EuclideanSpace.proj i : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ) x :=
      (EuclideanSpace.proj i : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).hasStrictFDerivAt
    have h : UpperTheory.Reformulated.B.Qi29.polyDeriv (p * MvPolynomial.X i) x
        = (MvPolynomial.eval (fun j : Fin n ↦ x.ofLp j) p) •
            (EuclideanSpace.proj i : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ)
          + (x.ofLp i) • UpperTheory.Reformulated.B.Qi29.polyDeriv p x := by
      simp only [UpperTheory.Reformulated.B.Qi29.polyDeriv, Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul,
        MvPolynomial.eval_X, add_smul, Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
      congr 1
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb
        simp [MvPolynomial.pderiv_X_of_ne hb.symm]
      · simp
    rw [h]
    simp only [map_mul, MvPolynomial.eval_X]
    exact hp.mul hi
end

section

noncomputable def UpperTheory.Reformulated.B.Qf34.genericGradient :
    {n : ℕ} →
      (J : Ideal (MvPolynomial (Fin n) ℂ)) → MvPolynomial (Fin n) ℂ → Fin n → FractionRing (MvPolynomial (Fin n) ℂ ⧸ J) :=
    fun {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (f : MvPolynomial (Fin n) ℂ) (l : Fin n) ↦
      (Algebra.algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) (FractionRing (MvPolynomial (Fin n) ℂ ⧸ J)) :
          MvPolynomial (Fin n) ℂ ⧸ J → FractionRing (MvPolynomial (Fin n) ℂ ⧸ J))
        ((Ideal.Quotient.mk J : MvPolynomial (Fin n) ℂ → MvPolynomial (Fin n) ℂ ⧸ J)
          ((MvPolynomial.pderiv l : MvPolynomial (Fin n) ℂ → MvPolynomial (Fin n) ℂ) f))

noncomputable def UpperTheory.Reformulated.B.Qf34.Statement :
    Prop :=
    ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime] (ι : Type) [Fintype ι] (f : ι → MvPolynomial (Fin n) ℂ),
      (∀ (i : ι), f i ∈ J) →
        Submodule.span (FractionRing (MvPolynomial (Fin n) ℂ ⧸ J)) (Set.range (UpperTheory.Reformulated.B.Qf34.genericGradient J ∘ f)) =
            Submodule.span (FractionRing (MvPolynomial (Fin n) ℂ ⧸ J))
              (UpperTheory.Reformulated.B.Qf34.genericGradient J '' (↑J : Set (MvPolynomial (Fin n) ℂ))) →
          ∃ s ∉ J, ∀ p ∈ J, s * p ∈ Ideal.span (Set.range f)

open MvPolynomial in
private theorem UpperTheory.Reformulated.B.Qf34.taylor {k B : Type*} [CommRing k] [CommRing B] [Algebra k B]
    {n : ℕ} (φ ψ : MvPolynomial (Fin n) k →ₐ[k] B)
    (h : ∀ p q, (φ p - ψ p) * (φ q - ψ q) = 0) (p : MvPolynomial (Fin n) k) :
    φ p - ψ p = ∑ l, φ (pderiv l p) * (φ (X l) - ψ (X l)) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.algHom_C]
  | add p q hp hq =>
    simp only [map_add (f := _), add_mul, Finset.sum_add_distrib, ← hp, ← hq]
    ring
  | mul_X p i hp =>
    have e : ∀ l, φ (pderiv l (p * X i)) * (φ (X l) - ψ (X l)) =
        φ (X i) * (φ (pderiv l p) * (φ (X l) - ψ (X l))) +
          (if l = i then φ p * (φ (X i) - ψ (X i)) else 0) := by
      intro l
      rw [pderiv_mul, map_add (f := _), map_mul, map_mul]
      split_ifs with hl
      · subst hl
        rw [pderiv_X_self, map_one]
        ring
      · rw [pderiv_X_of_ne (Ne.symm hl), map_zero]
        ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, ← hp, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, map_mul]
    linear_combination - h p (X i)

open MvPolynomial in
private theorem UpperTheory.Reformulated.B.Qf34.sq_zero_case {k B K ι : Type*} [CommRing k] [CommRing B]
    [Algebra k B] [CommRing K] [Algebra k K] [Fintype ι] {n : ℕ}
    (π : B →ₐ[k] K) (σ : K →ₐ[k] B) (hσ : ∀ x, π (σ x) = x)
    (hsq : ∀ a b, π a = 0 → π b = 0 → a * b = 0)
    (φ : MvPolynomial (Fin n) k →ₐ[k] B) (p : MvPolynomial (Fin n) k)
    (f : ι → MvPolynomial (Fin n) k) (c : ι → K) (hp : π (φ p) = 0) (hf : ∀ i, π (φ (f i)) = 0)
    (hc : ∀ l, π (φ (pderiv l p)) = ∑ i, c i * π (φ (pderiv l (f i)))) :
    φ p = ∑ i, σ (c i) * φ (f i) := by
  have hd : ∀ q, π (φ q - (σ.comp (π.comp φ)) q) = 0 := by
    intro q
    simp [hσ]
  have ht := UpperTheory.Reformulated.B.Qf34.taylor φ (σ.comp (π.comp φ)) fun p q => hsq _ _ (hd p) (hd q)
  have ht' : ∀ q, π (φ q) = 0 →
      φ q = ∑ l, φ (pderiv l q) * (φ (X l) - (σ.comp (π.comp φ)) (X l)) := by
    intro q hq
    rw [← ht q]
    simp [hq]
  rw [ht' p hp, Finset.sum_congr rfl fun i _ => congrArg (σ (c i) * ·) (ht' _ (hf i))]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [← mul_assoc]
  rw [← Finset.sum_mul, ← sub_eq_zero, ← sub_mul]
  refine hsq _ _ ?_ (hd _)
  simp [hσ, hc]

open MvPolynomial in
private theorem UpperTheory.Reformulated.B.Qf34.mem_sup_sq {k A K ι : Type*} [CommRing k] [CommRing A]
    [Algebra k A] [CommRing K] [Algebra k K] [Algebra.FormallySmooth k K] [Fintype ι] {n : ℕ}
    (π : A →ₐ[k] K) (hπ : Function.Surjective π)
    (φ : MvPolynomial (Fin n) k →ₐ[k] A) (p : MvPolynomial (Fin n) k)
    (f : ι → MvPolynomial (Fin n) k) (c : ι → K) (hp : π (φ p) = 0) (hf : ∀ i, π (φ (f i)) = 0)
    (hc : ∀ l, π (φ (pderiv l p)) = ∑ i, c i * π (φ (pderiv l (f i)))) :
    φ p ∈ Ideal.span (Set.range fun i => φ (f i)) ⊔ RingHom.ker π * RingHom.ker π := by
  set m : Ideal A := RingHom.ker π with hm
  let π' : (A ⧸ m * m) →ₐ[k] K := Ideal.Quotient.liftₐ (m * m) π fun a ha => Ideal.mul_le_left ha
  have hπ' : ∀ a, π' (Ideal.Quotient.mk _ a) = π a := fun a => rfl
  have hs : Function.Surjective π' := fun x => by
    obtain ⟨a, rfl⟩ := hπ x
    exact ⟨_, hπ' a⟩
  have hsq : ∀ a b, π' a = 0 → π' b = 0 → a * b = 0 := by
    intro a b ha hb
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_mul ha hb
  have hn : IsNilpotent (RingHom.ker (π' : (A ⧸ m * m) →+* K)) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro a ha b hb
    exact hsq a b ha hb
  let σ := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id k K) π' hs hn
  have hσ : ∀ x, π' (σ x) = x :=
    Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id k K) π' hs hn
  have key := UpperTheory.Reformulated.B.Qf34.sq_zero_case π' σ hσ hsq ((Ideal.Quotient.mkₐ k (m * m)).comp φ)
    p f c hp hf hc
  choose a ha using fun i => Ideal.Quotient.mk_surjective (I := m * m) (σ (c i))
  have h2 : φ p - ∑ i, a i * φ (f i) ∈ m * m := by

    rw [← Ideal.Quotient.eq, map_sum]
    simpa [← ha] using key
  rw [← add_sub_cancel (∑ i, a i * φ (f i)) (φ p)]
  refine Submodule.add_mem_sup (Ideal.sum_mem _ fun i _ => ?_) h2
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem UpperTheory.Reformulated.B.Qf34.proof :
    UpperTheory.Reformulated.B.Qf34.Statement := by
  intro n J _ ι _ f hf hspan
  let R := MvPolynomial (Fin n) ℂ
  let K := FractionRing (R ⧸ J)
  let A := Localization.AtPrime J
  let g : R →ₐ[ℂ] K := (IsScalarTower.toAlgHom ℂ (R ⧸ J) K).comp (Ideal.Quotient.mkₐ ℂ J)
  have hg : ∀ r, g r = algebraMap (R ⧸ J) K (Ideal.Quotient.mk J r) := fun r => rfl
  have hg0 : ∀ r, g r = 0 ↔ r ∈ J := fun r => by
    rw [hg, map_eq_zero_iff _ (IsFractionRing.injective (R ⧸ J) K), Ideal.Quotient.eq_zero_iff_mem]
  have hu : ∀ y : J.primeCompl, IsUnit (g y) := fun y =>
    isUnit_iff_ne_zero.mpr fun h => y.2 ((hg0 _).mp h)
  let π : A →ₐ[ℂ] K := IsLocalization.liftAlgHom (M := J.primeCompl) hu
  let φ : R →ₐ[ℂ] A := IsScalarTower.toAlgHom ℂ R A
  have hπφ : ∀ r, π (φ r) = g r := fun r => IsLocalization.lift_eq hu r
  have hπ : Function.Surjective π := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (R ⧸ J) x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hb' : b ∈ J.primeCompl := fun h =>
      nonZeroDivisors.ne_zero hb (Ideal.Quotient.eq_zero_iff_mem.mpr h)
    refine ⟨IsLocalization.mk' A a ⟨b, hb'⟩, ?_⟩
    rw [← hg, ← hg, eq_div_iff (hu ⟨b, hb'⟩).ne_zero, ← hπφ, ← hπφ, ← map_mul]
    exact congrArg π (IsLocalization.mk'_spec A a ⟨b, hb'⟩)
  haveI : Algebra.EssFiniteType (R ⧸ J) K :=
    Algebra.EssFiniteType.of_isLocalization K (nonZeroDivisors (R ⧸ J))
  haveI : Algebra.EssFiniteType ℂ K := Algebra.EssFiniteType.comp ℂ (R ⧸ J) K
  haveI : Algebra.FormallySmooth ℂ K := Algebra.FormallySmooth.of_perfectField
  have hker : RingHom.ker π = IsLocalRing.maximalIdeal A :=
    IsLocalRing.ker_eq_maximalIdeal (π : A →+* K) hπ
  have hN : IsLocalRing.maximalIdeal A ≤ (Ideal.span (Set.range f)).map (algebraMap R A) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal A)
      (IsNoetherian.noetherian _) (IsLocalRing.maximalIdeal_le_jacobson _) ?_
    conv_lhs => rw [← Localization.AtPrime.map_eq_maximalIdeal]
    rw [Ideal.map_le_iff_le_comap]
    intro p hp
    have hmem : UpperTheory.Reformulated.B.Qf34.genericGradient J p ∈
        Submodule.span K (Set.range (UpperTheory.Reformulated.B.Qf34.genericGradient J ∘ f)) := by
      rw [hspan]
      exact Submodule.subset_span ⟨p, hp, rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hmem
    have := UpperTheory.Reformulated.B.Qf34.mem_sup_sq π hπ φ p f c (by rw [hπφ, hg0]; exact hp)
      (fun i => by rw [hπφ, hg0]; exact hf i) (fun l => by
        have h := congrFun hc l
        rw [Finset.sum_apply] at h
        simp only [hπφ]
        exact h.symm)
    rw [hker] at this
    rw [Ideal.mem_comap, Ideal.map_span, ← Set.range_comp, smul_eq_mul]
    exact this
  obtain ⟨t, ht⟩ : J.FG := IsNoetherian.noetherian J
  have hs : ∀ p ∈ J, ∃ s ∈ J.primeCompl, s * p ∈ Ideal.span (Set.range f) := by
    intro p hp
    rw [← IsLocalization.algebraMap_mem_map_algebraMap_iff J.primeCompl A]
    apply hN
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ hp
  choose! s hs hs' using hs
  have htJ : ∀ p ∈ t, p ∈ J := fun p hp => ht ▸ Ideal.subset_span hp
  refine ⟨∏ p ∈ t, s p, Submonoid.prod_mem J.primeCompl fun p hp => hs p (htJ p hp), ?_⟩
  intro p hp
  rw [← ht] at hp
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu⟩ := Finset.dvd_prod_of_mem s hx
    rw [hu, mul_comm (s x), mul_assoc]
    exact Ideal.mul_mem_left _ _ (hs' x (htJ x hx))
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Ideal.add_mem _ hx hy
  | smul a x _ hx => rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ _ hx
end

section

namespace UpperTheory.Reformulated.B.Qn18

@[reducible] noncomputable def Mat : Type → ℕ → Type :=
  fun C N ↦ Matrix (Fin N) (Fin N) C

@[reducible] noncomputable def MP : (C : Type) → [Field C] → ℕ → Type :=
  fun C [Field C] N ↦ MvPolynomial (Fin N × Fin N) C

noncomputable def ev : {C : Type} → [inst : Field C] → {N : ℕ} → Mat C N → MP C N → C :=
  fun {C} [Field C] {N} x f ↦ MvPolynomial.eval (fun p ↦ x p.1 p.2) f

noncomputable def dAt :
    {C : Type} → [inst : Field C] → {N : ℕ} → MP C N → Mat C N → Mat C N → C :=
  fun {C} [Field C] {N} f x Y ↦
    ∑ p : Fin N × Fin N, ev x (MvPolynomial.pderiv p f) * Y p.1 p.2

noncomputable def Chain : Prop :=
  ∀ (C : Type) [inst : Field C] (N M : ℕ) (φ : Mat C N →ₗ[C] Mat C M) (f : MP C M),
    ∃ (f' : MP C N),
      (∀ (x : Mat C N), ev x f' = ev (φ x) f) ∧
      ∀ (x Y : Mat C N), dAt f' x Y = dAt f (φ x) (φ Y)

noncomputable def OpenCoset : Prop :=
  ∀ (Γ C : Type) [inst : Group Γ] [inst_1 : TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [inst_4 : Field C] (n : ℕ) (r : Γ →* GL (Fin n) C)
    (f : MP C n) (O : Set Γ), IsOpen O → O.Nonempty →
    (∀ g ∈ O, ev ↑(r g) f = 0) →
    ∃ (U : Subgroup Γ),
      U.Normal ∧ U.FiniteIndex ∧ ∃ (g : Γ), ∀ u ∈ U, ev ↑(r (g * u)) f = 0

open scoped Pointwise in
private theorem coset_of_cover {G : Type} [Group G] [TopologicalSpace G]
    [TopologicalSpace.NoetherianSpace G] (hc : ∀ h : G, Continuous fun x : G => h * x)
    (Z : Set G) (hZ : IsClosed Z) (s : Finset G) (hs : ∀ x : G, ∃ a ∈ s, a * x ∈ Z) :
    ∃ U : Subgroup G, U.Normal ∧ U.FiniteIndex ∧ ∃ g : G, ∀ u ∈ U, g * u ∈ Z := by
  classical
  haveI : ContinuousConstSMul G G := ⟨hc⟩
  set X : Set G := irreducibleComponent (1 : G) with hX
  have hXc : X ∈ irreducibleComponents G := irreducibleComponent_mem_irreducibleComponents _
  have horb : MulAction.orbit G X ⊆ irreducibleComponents G := by
    rintro _ ⟨h, rfl⟩
    refine ⟨?_, ?_⟩
    · exact hXc.1.image _ (hc h).continuousOn
    · intro Y hY hle
      have h1 : IsIrreducible (h⁻¹ • Y) := IsIrreducible.image hY _ (hc h⁻¹).continuousOn
      have h2 : X ⊆ h⁻¹ • Y := by
        have : h • X ⊆ Y := hle
        exact Set.smul_set_subset_iff_subset_inv_smul_set.mp this
      have h3 : h⁻¹ • Y ⊆ X := hXc.2 h1 h2
      have h4 : Y ⊆ h • X := by
        have := Set.smul_set_subset_iff_subset_inv_smul_set.mp h3
        simpa using this
      exact h4
  have hfin : (MulAction.orbit G X).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset horb
  haveI : (MulAction.stabilizer G X).FiniteIndex := by
    refine ⟨?_⟩
    rw [MulAction.index_stabilizer]
    exact ((Set.ncard_pos hfin).mpr ⟨X, MulAction.mem_orbit_self X⟩).ne'
  obtain ⟨W, hW, hXW⟩ := isIrreducible_iff_sUnion_isClosed.mp hXc.1
    (s.image fun a => (fun x : G => a * x) ⁻¹' Z)
    (by
      intro z hz
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hz
      exact hZ.preimage (hc a))
    (by
      intro x _
      obtain ⟨a, ha, hx⟩ := hs x
      exact ⟨_, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ ha), hx⟩)
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hW
  refine ⟨(MulAction.stabilizer G X).normalCore, inferInstance, inferInstance, a, ?_⟩
  intro u hu
  have hu' : u • X = X := Subgroup.normalCore_le _ hu
  have : u ∈ X := by
    rw [← hu']
    exact ⟨1, mem_irreducibleComponent, by simp⟩
  exact hXW this

private theorem finite_cover {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] (O : Set G) (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ s : Finset G, ∀ x : G, ∃ a ∈ s, a * x ∈ O := by
  obtain ⟨o, ho⟩ := hne
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun a : G => (fun x : G => a * x) ⁻¹' O)
    (fun a => hO.preimage (continuous_const_mul a))
    (fun x _ => Set.mem_iUnion.mpr ⟨o * x⁻¹, by simpa using ho⟩)
  refine ⟨s, fun x => ?_⟩
  simpa using hs (Set.mem_univ x)

theorem main :
    Chain → OpenCoset := by
  intro hch Γ C _ _ _ _ _ n r f O hO hne hf
  obtain ⟨s, hs⟩ := finite_cover O hO hne
  let p : Γ → PrimeSpectrum (MvPolynomial (Fin n × Fin n) C) := fun g =>
    ⟨RingHom.ker (MvPolynomial.eval fun q : Fin n × Fin n =>
      (↑(r g) : Matrix (Fin n) (Fin n) C) q.1 q.2), RingHom.ker_isPrime _⟩
  have hp : ∀ (g : Γ) (S : Set (MvPolynomial (Fin n × Fin n) C)),
      p g ∈ PrimeSpectrum.zeroLocus S ↔
        ∀ k ∈ S, ev ↑(r g) k = 0 := by
    intro g S
    rw [PrimeSpectrum.mem_zeroLocus]
    exact Iff.rfl
  letI : TopologicalSpace Γ := TopologicalSpace.induced p inferInstance
  have hcl (k : MP C n) : IsClosed {g | ev ↑(r g) k = 0} := by
    refine (isClosed_induced_iff (f := p)).mpr ⟨_, PrimeSpectrum.isClosed_zeroLocus {k}, ?_⟩
    ext g
    simp [hp]
  haveI : TopologicalSpace.NoetherianSpace Γ :=
    (show Topology.IsInducing p from ⟨rfl⟩).noetherianSpace
  have hc (h : Γ) : Continuous fun x => h * x := by
    refine continuous_iff_isClosed.mpr ?_
    intro T hT
    obtain ⟨T', hT', rfl⟩ := (isClosed_induced_iff (f := p)).mp hT
    obtain ⟨S, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus _).mp hT'
    choose F hF using fun k => hch C n n
      (LinearMap.mulLeft C (↑(r h) : Matrix (Fin n) (Fin n) C)) k
    have : (fun x => h * x) ⁻¹' (p ⁻¹' PrimeSpectrum.zeroLocus S) =
        ⋂ k ∈ S, {g | ev ↑(r g) (F k) = 0} := by
      ext g
      simp only [Set.mem_preimage, hp, Set.mem_iInter, Set.mem_setOf_eq, (hF _).1,
        LinearMap.mulLeft_apply, map_mul, Units.val_mul]
    rw [this]
    exact isClosed_biInter fun k _ => hcl (F k)
  exact coset_of_cover hc _ (hcl f) s fun x => by
    obtain ⟨a, ha, hx⟩ := hs x
    exact ⟨a, ha, hf _ hx⟩

end UpperTheory.Reformulated.B.Qn18
end

section

theorem UpperTheory.Reformulated.B.Qi58.aeval_inter :
    ∀ {L M N : Type} [inst : Field L]
    [inst_1 : AddCommGroup M] [inst_2 : _root_.Module L M] [inst_3 : AddCommGroup N] [inst_4 : _root_.Module L N]
    (c : M →ₗ[L] N) (f : Module.End L M) (g : Module.End L N),
    (∀ (x : M), (c : M → N) ((f : M → M) x) = (g : N → N) ((c : M → N) x)) →
      ∀ (Q : Polynomial L) (x : M),
        (c : M → N) (((Polynomial.aeval f : Polynomial L → Module.End L M) Q : M → M) x) =
          ((Polynomial.aeval g : Polynomial L → Module.End L N) Q : N → N) ((c : M → N) x) := by
  intro L M N _ _ _ _ _ c f g h Q x
  have hp : ∀ (n : ℕ) (y : M), c ((f ^ n) y) = (g ^ n) (c y) := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]
  induction Q using Polynomial.induction_on' with
  | add p q hp' hq' => simp only [map_add (f := _), LinearMap.add_apply, hp', hq']
  | monomial n a =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      map_smul, hp]
end

section

theorem UpperTheory.Reformulated.B.AevalIntertwining.aeval_intertwine :
    ∀ {K : Type} [inst : Field K] {M N : Type} [inst_1 : AddCommGroup M]
    [inst_2 : _root_.Module K M] [inst_3 : AddCommGroup N] [inst_4 : _root_.Module K N] (φ : M →ₗ[K] N)
    (f : Module.End K M) (f' : Module.End K N),
    (∀ (x : M), (φ : M → N) ((f : M → M) x) = (f' : N → N) ((φ : M → N) x)) →
      ∀ (p : Polynomial K) (x : M),
        (φ : M → N) (((Polynomial.aeval f : Polynomial K → Module.End K M) p : M → M) x) =
          ((Polynomial.aeval f' : Polynomial K → Module.End K N) p : N → N) ((φ : M → N) x) := by
  intro K _ M N _ _ _ _ φ f f' h p
  have hpow : ∀ (n : ℕ) (x : M), φ ((f ^ n) x) = (f' ^ n) (φ x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro x
    simp only [map_add (f := _), LinearMap.add_apply, hp, hq]
  | monomial n a =>
    intro x
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      map_smul, hpow]
end
