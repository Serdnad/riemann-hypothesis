module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle004
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
public import Mathlib.RingTheory.Nullstellensatz
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial TensorProduct

theorem isReduced_tensor_finite (Ω E : Type*) [Field Ω] [CharZero Ω] [Field E] [Algebra ℚ E]
    [FiniteDimensional ℚ E] : IsReduced (E ⊗[ℚ] Ω) := by
  haveI : Algebra.FormallyUnramified ℚ E := Algebra.FormallyUnramified.of_isSeparable ℚ E
  haveI : IsReduced (Ω ⊗[ℚ] E) := Algebra.FormallyUnramified.isReduced_of_field Ω (Ω ⊗[ℚ] E)
  exact isReduced_of_injective (Algebra.TensorProduct.comm ℚ E Ω).toRingHom
    (Algebra.TensorProduct.comm ℚ E Ω).injective

theorem eq_zero_of_sum_tmul {Ω E : Type*} [Field Ω] [CharZero Ω] [Field E] [Algebra ℚ E] {r : ℕ}
    {s : Fin r → Ω} (hs : LinearIndependent ℚ s) {e : Fin r → E}
    (h : ∑ k, e k ⊗ₜ[ℚ] s k = 0) : e = 0 := by
  classical
  let W := Submodule.span ℚ (Set.range s)
  let 𝒞 : Module.Basis (Fin r) ℚ W := Module.Basis.span hs
  have hinj : Function.Injective (LinearMap.lTensor E W.subtype) :=
    Module.Flat.lTensor_preserves_injective_linearMap W.subtype Subtype.val_injective
  have h0 : (∑ k, e k ⊗ₜ[ℚ] 𝒞 k : E ⊗[ℚ] W) = 0 := by
    apply hinj

    rw [map_sum, map_zero]
    have hc : ∀ k, ((𝒞 k : W) : Ω) = s k := fun k => by
      show ((Module.Basis.span hs k : W) : Ω) = s k
      rw [Module.Basis.span_apply]
    simp only [LinearMap.lTensor_tmul, Submodule.subtype_apply, hc]
    exact h
  have hb := TensorProduct.sum_tmul_basis_right_eq_zero 𝒞 (Finsupp.equivFunOnFinite.symm e) (by
    rw [Finsupp.sum_fintype _ _ (by intros; simp)]
    simpa using h0)
  funext k
  have hk := congrArg (fun b => b k) hb
  simpa using hk

theorem nilp_coeff_eq_zero {Ω : Type} [Field Ω] [CharZero Ω] {r : ℕ} {s : Fin r → Ω}
    (hs : LinearIndependent ℚ s) {c : Fin r → ℂ}
    (h : IsNilpotent (∑ k, c k ⊗ₜ[ℚ] s k : ℂ ⊗[ℚ] Ω)) : c = 0 := by
  classical
  let A : Subalgebra ℚ ℂ := Algebra.adjoin ℚ ((Finset.univ.image c : Finset ℂ) : Set ℂ)
  haveI : Algebra.FiniteType ℚ A := (Subalgebra.fg_iff_finiteType A).1 (Subalgebra.fg_adjoin_finset _)
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := ℚ) (B := A)
  have hcA : ∀ k, c k ∈ A := fun k => Algebra.subset_adjoin (by simp)
  let cA : Fin r → A := fun k => ⟨c k, hcA k⟩
  let tA : A ⊗[ℚ] Ω := ∑ k, cA k ⊗ₜ[ℚ] s k
  let ι : A ⊗[ℚ] Ω →ₐ[ℚ] ℂ ⊗[ℚ] Ω := Algebra.TensorProduct.map A.val (AlgHom.id ℚ Ω)
  have hι : Function.Injective ι := by
    have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := Ω) (A.val.toLinearMap)
      Subtype.val_injective
    have heq : ∀ x, ι x = LinearMap.rTensor Ω A.val.toLinearMap x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [ι, Algebra.TensorProduct.map_tmul]
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    intro x y hxy
    apply hinj
    rw [← heq, ← heq, hxy]
  have hιt : ι tA = ∑ k, c k ⊗ₜ[ℚ] s k := by

    simp [tA, ι, map_sum, Algebra.TensorProduct.map_tmul, cA]
  have hnA : IsNilpotent tA := by
    obtain ⟨m, hm⟩ := h
    refine ⟨m, hι ?_⟩
    rw [map_pow, hιt, hm, map_zero]
  have key : ∀ (E : Type) [Field E] [Algebra ℚ E] [FiniteDimensional ℚ E] (φ : A →ₐ[ℚ] E),
      ∀ k, φ (cA k) = 0 := by
    intro E _ _ _ φ
    let π : A ⊗[ℚ] Ω →ₐ[ℚ] E ⊗[ℚ] Ω := Algebra.TensorProduct.map φ (AlgHom.id ℚ Ω)
    haveI : IsReduced (E ⊗[ℚ] Ω) := isReduced_tensor_finite Ω E
    have h0 : π tA = 0 := (hnA.map π).eq_zero
    have h1 : ∑ k, φ (cA k) ⊗ₜ[ℚ] s k = 0 := by
      rw [← h0]

      simp [tA, π, map_sum, Algebra.TensorProduct.map_tmul]
    exact congrFun (eq_zero_of_sum_tmul hs h1)
  have hmax : ∀ M : Ideal A, M.IsMaximal → ∀ k, cA k ∈ M := by
    intro M hM k
    letI hF : Field (A ⧸ M) := Ideal.Quotient.field M
    haveI : Algebra.FiniteType ℚ (A ⧸ M) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℚ M) Ideal.Quotient.mk_surjective
    haveI : Module.Finite ℚ (A ⧸ M) := finite_of_finite_type_of_isJacobsonRing ℚ (A ⧸ M)
    exact Ideal.Quotient.eq_zero_iff_mem.1 (key (A ⧸ M) (Ideal.Quotient.mkₐ ℚ M) k)
  have hjac : (⊥ : Ideal A).jacobson = ⊥ := IsJacobsonRing.out inferInstance Ideal.isPrime_bot.isRadical
  funext k
  have hk : cA k ∈ (⊥ : Ideal A).jacobson := Ideal.mem_sInf.2 (fun J hJ => hmax J hJ.2 k)
  rw [hjac] at hk
  have h0 : cA k = 0 := (Submodule.mem_bot _).1 hk
  exact congrArg Subtype.val h0

section Poly

variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J]

theorem aeval_eq_zero_of_mem_coordIdeal {x : J → Ω} {f : MvPolynomial J ℤ}
    (hf : f ∈ coordIdeal ℤ x) : aeval x f = 0 := by
  have h0 : (aeval fun i => Polynomial.C (x i) * Polynomial.X : MvPolynomial J ℤ →ₐ[ℤ] Polynomial Ω) f = 0 :=
    RingHom.mem_ker.1 hf
  have h1 := MvPolynomial.comp_aeval_apply (fun i => Polynomial.C (x i) * Polynomial.X)
    ((Polynomial.aeval (1 : Ω)).restrictScalars ℤ) f
  rw [h0, map_zero] at h1
  simpa using h1.symm

def evalT (x : J → Ω) : MvPolynomial J ℂ →ₐ[ℂ] ℂ ⊗[ℚ] Ω :=
  aeval fun j => (1 : ℂ) ⊗ₜ[ℚ] x j

theorem evalT_map_rat (x : J → Ω) (b : MvPolynomial J ℚ) :
    evalT x (map (algebraMap ℚ ℂ) b) = (1 : ℂ) ⊗ₜ[ℚ] aeval x b := by
  unfold evalT
  rw [MvPolynomial.aeval_map_algebraMap]
  have h := MvPolynomial.comp_aeval_apply x (Algebra.TensorProduct.includeRight : Ω →ₐ[ℚ] ℂ ⊗[ℚ] Ω) b
  simpa [Algebra.TensorProduct.includeRight_apply] using h.symm

theorem evalT_map_int (x : J → Ω) (f : MvPolynomial J ℤ) :
    evalT x (map (Int.castRingHom ℂ) f) = (1 : ℂ) ⊗ₜ[ℚ] aeval x f := by
  unfold evalT
  rw [← algebraMap_int_eq, MvPolynomial.aeval_map_algebraMap]
  have h := MvPolynomial.comp_aeval_apply x
    ((Algebra.TensorProduct.includeRight : Ω →ₐ[ℚ] ℂ ⊗[ℚ] Ω).restrictScalars ℤ) f
  simpa [Algebra.TensorProduct.includeRight_apply] using h.symm

theorem coeff_eq_zero_of_vanish {x : J → Ω} {r : ℕ} {b : Fin r → MvPolynomial J ℚ}
    (hs : LinearIndependent ℚ fun k => aeval x (b k)) {c : Fin r → ℂ}
    (h : ∀ z : J → ℂ, (∀ f ∈ coordIdeal ℤ x, eval z (map (Int.castRingHom ℂ) f) = 0) →
      ∑ k, c k * secFun (b k) z = 0) : c = 0 := by
  classical
  set I : Ideal (MvPolynomial J ℂ) := Ideal.map (MvPolynomial.map (Int.castRingHom ℂ)) (coordIdeal ℤ x) with hI
  set P : MvPolynomial J ℂ := ∑ k, MvPolynomial.C (c k) * MvPolynomial.map (algebraMap ℚ ℂ) (b k) with hP
  have hPmem : P ∈ MvPolynomial.vanishingIdeal ℂ (MvPolynomial.zeroLocus ℂ I) := by
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro z hz
    rw [MvPolynomial.mem_zeroLocus_iff] at hz
    have hz' : ∀ f ∈ coordIdeal ℤ x, eval z (map (Int.castRingHom ℂ) f) = 0 := by
      intro f hf
      have hf' := hz _ (Ideal.mem_map_of_mem _ hf)
      exact hf'
    have hsum := h z hz'
    change eval z P = 0

    rw [hP, map_sum]
    simpa [secFun] using hsum
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at hPmem
  obtain ⟨n, hn⟩ := hPmem
  have hker : I ≤ RingHom.ker (evalT x : MvPolynomial J ℂ →+* ℂ ⊗[ℚ] Ω) := by
    rw [hI, Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change evalT x (map (Int.castRingHom ℂ) f) = 0
    rw [evalT_map_int, aeval_eq_zero_of_mem_coordIdeal hf, TensorProduct.tmul_zero]
  have hnil : IsNilpotent (evalT x P) := ⟨n, by
    rw [← map_pow]
    exact hker hn⟩
  have hev : evalT x P = ∑ k, c k ⊗ₜ[ℚ] aeval x (b k) := by

    rw [hP, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, evalT_map_rat, ← MvPolynomial.algebraMap_eq, AlgHom.commutes,
      Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    simp
  rw [hev] at hnil
  exact nilp_coeff_eq_zero hs hnil

end Poly

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

def xpow (i : ∀ k, ι k) (e : K → ℕ) : MRing ι := ∏ k, (X ⟨k, i k⟩ : MRing ι) ^ (e k)

private theorem isMultiHomog_mul_lemma {f g : MRing ι} {c c' : K → ℕ} (hf : IsMultiHomog f c)
    (hg : IsMultiHomog g c') : IsMultiHomog (f * g) (c + c') := by
  classical
  intro m hm k
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, hf a ha k, hg b hb k, Pi.add_apply]

private theorem isMultiHomog_one_arakelov_geometry : IsMultiHomog (1 : MRing ι) 0 := by
  classical
  intro m hm k
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hm
  split_ifs at hm with h
  · subst h
    simp
  · exact absurd rfl hm

theorem isMultiHomog_pow {f : MRing ι} {c : K → ℕ} (hf : IsMultiHomog f c) (n : ℕ) :
    IsMultiHomog (f ^ n) (n • c) := by
  induction n with
  | zero =>
    simp only [pow_zero, zero_smul]
    exact isMultiHomog_one_arakelov_geometry
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact isMultiHomog_mul_lemma ih hf

theorem isMultiHomog_prod (s : Finset K) (g : K → MRing ι) (c : K → K → ℕ)
    (h : ∀ k, IsMultiHomog (g k) (c k)) : IsMultiHomog (∏ k ∈ s, g k) (∑ k ∈ s, c k) := by
  induction s using Finset.induction_on with
  | empty => simpa using isMultiHomog_one_arakelov_geometry
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact isMultiHomog_mul_lemma (h a) ih

theorem isMultiHomog_xpow (i : ∀ k, ι k) (e : K → ℕ) : IsMultiHomog (xpow i e) e := by
  classical
  have hX : ∀ k, IsMultiHomog (X ⟨k, i k⟩ : MRing ι) (Pi.single k 1) := by
    intro k m hm k'
    rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
    subst hm
    by_cases hk : k' = k
    · subst hk
      rw [Finset.sum_eq_single (i k')]
      · simp
      · intro j _ hj
        simp [Finsupp.single_apply, Sigma.mk.inj_iff, Ne.symm hj]
      · simp
    · simp [Finsupp.single_apply, Sigma.mk.inj_iff, hk, Ne.symm hk]
  have h := isMultiHomog_prod Finset.univ (fun k => (X ⟨k, i k⟩ : MRing ι) ^ e k)
    (fun k => e k • Pi.single k 1) (fun k => isMultiHomog_pow (hX k) (e k))
  have he : (∑ k, e k • Pi.single k 1 : K → ℕ) = e := by
    ext k'
    simp [Finset.sum_apply, Pi.single_apply]
  rw [he] at h
  exact h

def dehomI (W : Ideal (MRing ι)) (i : ∀ k, ι k) : Ideal (MRing ι) :=
  W ⊔ Ideal.span (Set.range fun k => (X ⟨k, i k⟩ : MRing ι) - 1)

theorem mk_xpow (W : Ideal (MRing ι)) (i : ∀ k, ι k) (e : K → ℕ) :
    Ideal.Quotient.mk (dehomI W i) (xpow i e) = 1 := by
  unfold xpow
  rw [map_prod]
  apply Finset.prod_eq_one
  intro k _
  have hk : Ideal.Quotient.mk (dehomI W i) (X ⟨k, i k⟩) = 1 := by
    rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk (dehomI W i)), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)
  rw [map_pow, hk, one_pow]

theorem mem_of_mem_dehomI {W : Ideal (MRing ι)} (hWp : W.IsPrime) (hWm : IsMultiHomogIdeal W)
    {i : ∀ k, ι k} (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι) ∉ W) {a : K → ℕ} {s : MRing ι}
    (hs : IsMultiHomog s a) (hsI : s ∈ dehomI W i) : s ∈ W := by
  classical
  haveI : W.IsPrime := hWp
  obtain ⟨F, _, q, hq⟩ : ∃ (F : Type) (_ : Field F) (q : MRing ι →+* F), ∀ f, q f = 0 ↔ f ∈ W :=
    ⟨FractionRing (MRing ι ⧸ W), inferInstance, (algebraMap (MRing ι ⧸ W) _).comp (Ideal.Quotient.mk W),
      fun f => by
        rw [RingHom.comp_apply, show (0 : FractionRing (MRing ι ⧸ W)) = algebraMap (MRing ι ⧸ W) _ 0 from
          (map_zero _).symm, (IsFractionRing.injective (MRing ι ⧸ W) _).eq_iff,
          Ideal.Quotient.eq_zero_iff_mem]⟩
  have hc : ∀ k, q (X ⟨k, i k⟩) ≠ 0 := fun k h => hi k ((hq _).1 h)
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : MRing ι →+* F,
      Θ = MvPolynomial.eval₂Hom (Int.castRingHom F) (fun p => q (X p) / q (X ⟨p.1, i p.1⟩)) := ⟨_, rfl⟩

  have hqm : ∀ (m : ((k : K) × ι k) →₀ ℕ) (c : ℤ),
      q (monomial m c) = (c : F) * ∏ p ∈ m.support, q (X p) ^ m p := by
    intro m c
    rw [MvPolynomial.monomial_eq, map_mul]
    simp only [Finsupp.prod, map_prod, map_pow]
    congr 1
    exact eq_intCast (q.comp MvPolynomial.C) c
  have hΘm : ∀ (m : ((k : K) × ι k) →₀ ℕ) (c : ℤ),
      Θ (monomial m c) = (c : F) * ∏ p ∈ m.support, (q (X p) / q (X ⟨p.1, i p.1⟩)) ^ m p := by
    intro m c
    rw [hΘ, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial, eq_intCast]
    rfl

  have key : ∀ (f : MRing ι) (d : K → ℕ), IsMultiHomog f d →
      Θ f * ∏ k, q (X ⟨k, i k⟩) ^ d k = q f := by
    intro f d hf
    have hC : ∏ k, q (X ⟨k, i k⟩) ^ d k ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
    conv_lhs => rw [f.as_sum]
    conv_rhs => rw [f.as_sum]

    rw [map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hcm : ∏ p ∈ m.support, q (X ⟨p.1, i p.1⟩) ^ m p = ∏ k, q (X ⟨k, i k⟩) ^ d k := by
      rw [Finset.prod_subset (Finset.subset_univ m.support) (fun p _ hp => by
        rw [Finsupp.mem_support_iff, not_not] at hp
        rw [hp, pow_zero]), Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ => ?_
      dsimp only
      rw [Finset.prod_pow_eq_pow_sum, hf m hm k]
    rw [hΘm, hqm]
    simp only [div_pow]
    rw [Finset.prod_div_distrib, hcm, mul_assoc, div_mul_cancel₀ _ hC]
  have hW : W ≤ RingHom.ker Θ := by
    obtain ⟨S, hS, hWS⟩ := hWm
    intro w hw
    have hw' : w ∈ Ideal.span S := hWS ▸ hw
    refine (Ideal.span_le.mpr ?_) hw'
    intro f hf
    rw [SetLike.mem_coe, RingHom.mem_ker]
    obtain ⟨d, hd⟩ := hS f hf
    have h1 := key f d hd
    have h2 : q f = 0 := (hq f).2 (by rw [hWS]; exact Ideal.subset_span hf)
    rw [h2] at h1
    exact (mul_eq_zero.mp h1).resolve_right
      (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k))
  have hJ : ∀ k, Θ ((X ⟨k, i k⟩ : MRing ι) - 1) = 0 := by
    intro k
    rw [map_sub, map_one, hΘ, MvPolynomial.eval₂Hom_X', div_self (hc k), sub_self]
  have hle : W ⊔ Ideal.span (Set.range fun k => (X ⟨k, i k⟩ : MRing ι) - 1) ≤ RingHom.ker Θ :=
    sup_le hW (Ideal.span_le.mpr (by
      rintro _ ⟨k, rfl⟩
      exact RingHom.mem_ker.mpr (hJ k)))
  have hΘs : Θ s = 0 := RingHom.mem_ker.mp (hle hsI)
  have h := key s a hs
  rw [hΘs, zero_mul] at h
  exact (hq s).1 h.symm

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end
