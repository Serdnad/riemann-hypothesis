module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
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
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.IsCharOneOfSubsingleton
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

section

open PowerSeries IsLocalRing UpperTheory.V.abelian₂
open IsDiscreteValuationRing (addVal)
open scoped Pointwise TensorProduct Topology

private theorem UpperTheory.V.abelian₂.isIntegral_iff_norm_le_one_bis {l : ℕ} [Fact l.Prime] {K : Type} [Field K]
    [Algebra ℚ_[l] K] [Algebra ℤ_[l] K] [IsScalarTower ℤ_[l] ℚ_[l] K] [FiniteDimensional ℚ_[l] K]
    (φ : K →ₐ[ℚ_[l]] PadicAlgCl l) (x : K) : IsIntegral ℤ_[l] x ↔ ‖φ x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖φ x‖ = spectralValue (minpoly ℚ_[l] (φ x)) := rfl
  rw [h0, minpoly.algHom_eq φ φ.injective, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by
      rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

theorem UpperTheory.V.abelian₂.dvr_intClosure :
    ∀ (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [Algebra ℚ_[l] K] [Algebra ℤ_[l] K] [IsScalarTower ℤ_[l] ℚ_[l] K]
      [FiniteDimensional ℚ_[l] K],
      IsDiscreteValuationRing (integralClosure ℤ_[l] K) ∧ Module.Finite ℤ_[l] (integralClosure ℤ_[l] K) ∧
        IsFractionRing (integralClosure ℤ_[l] K) K := by
  intro l hl K _ _ _ _ _
  let φ : K →ₐ[ℚ_[l]] PadicAlgCl l := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hint := UpperTheory.V.abelian₂.isIntegral_iff_norm_le_one_bis φ
  have hunit : ∀ a : integralClosure ℤ_[l] K, ‖φ a‖ = 1 → IsUnit a := by
    intro a ha
    have h0 : (a : K) ≠ 0 := by
      intro h
      rw [h] at ha
      simp at ha
    have hi : IsIntegral ℤ_[l] (a : K)⁻¹ := by
      rw [hint, map_inv₀, norm_inv, ha, inv_one]
    exact IsUnit.of_mul_eq_one (⟨_, hi⟩ : integralClosure ℤ_[l] K) (Subtype.ext (mul_inv_cancel₀ h0))
  have hloc : IsLocalRing (integralClosure ℤ_[l] K) := by
    refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
    have ha : ‖φ a‖ ≤ 1 := (hint _).1 a.2
    rcases ha.eq_or_lt with h | h
    · exact Or.inl (hunit a h)
    · refine Or.inr (hunit _ (le_antisymm ((hint _).1 (1 - a).2) ?_))
      by_contra hlt
      push Not at hlt
      have h1 : φ ((1 - a : integralClosure ℤ_[l] K) : K) + φ a = 1 := by simp
      have h2 := (PadicAlgCl.isNonarchimedean l _ _).trans_lt (max_lt hlt h)
      simp only [h1] at h2
      simp at h2
  have hded : IsDedekindDomain (integralClosure ℤ_[l] K) :=
    IsIntegralClosure.isDedekindDomain ℤ_[l] ℚ_[l] K (integralClosure ℤ_[l] K)
  have hinj : Function.Injective (algebraMap ℤ_[l] (integralClosure ℤ_[l] K)) := by
    intro a b hab
    have h := congrArg (fun x : integralClosure ℤ_[l] K => (x : K)) hab
    simp only [Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] K] at h
    exact IsFractionRing.injective ℤ_[l] ℚ_[l] ((algebraMap ℚ_[l] K).injective h)
  have hnf : ¬ IsField (integralClosure ℤ_[l] K) := fun hf =>
    IsDiscreteValuationRing.not_isField ℤ_[l] ((Algebra.IsIntegral.isField_iff_isField hinj).2 hf)
  exact ⟨((IsDiscreteValuationRing.TFAE _ hnf).out 1 3).mpr hded,
    IsIntegralClosure.finite ℤ_[l] ℚ_[l] K (integralClosure ℤ_[l] K),
    integralClosure.isFractionRing_of_finite_extension ℚ_[l] K⟩
end

section

open PowerSeries IsLocalRing UpperTheory.V.abelian₂
open IsDiscreteValuationRing (addVal)
open scoped Pointwise TensorProduct Topology

private theorem mem_smul_top_iff_repr {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] (b : Module.Basis ι R M) (I : Ideal R) (x : M) :
    x ∈ I • (⊤ : Submodule R M) ↔ ∀ i, b.repr x i ∈ I := by
  constructor
  · intro hx i
    refine Submodule.smul_induction_on hx (fun r hr m _ => ?_) (fun a c ha hc => ?_)
    · rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact I.mul_mem_right _ hr
    · rw [map_add (f := _), Finsupp.add_apply]
      exact I.add_mem ha hc
  · intro h
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) trivial

private theorem prec_free {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] (I : Ideal R) [IsPrecomplete I R] :
    IsPrecomplete I M := ⟨fun f hf => by
  let b := Module.Free.chooseBasis R M
  have key : ∀ i, ∃ L : R, ∀ k, b.repr (f k) i - L ∈ I ^ k := fun i => by
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) (fun k => b.repr (f k) i)
      (fun {m n} hmn => by
        have h := hf hmn
        rw [SModEq.sub_mem, mem_smul_top_iff_repr b] at h
        rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
        simpa using h i)
    refine ⟨L, fun k => ?_⟩
    have := hL k
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
  choose L hL using key
  refine ⟨b.equivFun.symm L, fun n => ?_⟩
  rw [SModEq.sub_mem, mem_smul_top_iff_repr b]
  intro i
  have : b.repr (b.equivFun.symm L) i = L i := by
    rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [map_sub, Finsupp.sub_apply, this]
  exact hL i n⟩

private theorem prec_cofinal {R : Type*} [CommRing R] {I J : Ideal R} (hJI : J ≤ I) {e : ℕ}
    (he : I ^ e ≤ J) (hJ : IsPrecomplete J R) : IsPrecomplete I R := ⟨fun f hf => by
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hf ⊢
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := J) (fun k => f ((e + 1) * k))
    (fun {m n} hmn => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      have h := hf (Nat.mul_le_mul_left (e + 1) hmn)
      rw [pow_mul] at h
      exact Ideal.pow_right_mono ((Ideal.pow_le_pow_right (Nat.le_succ e)).trans he) m h)
  refine ⟨L, fun n => ?_⟩
  have h1 := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  have h2 := hf (m := n) (n := (e + 1) * n) (Nat.le_mul_of_pos_left n (Nat.succ_pos e))
  simpa using (I ^ n).add_mem h2 (Ideal.pow_right_mono hJI n h1)⟩

theorem UpperTheory.V.abelian₂.dvr_finite :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
      [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O],
      IsAdicComplete (maximalIdeal O) O ∧ Finite (ResidueField O) ∧ (l : O) ∈ maximalIdeal O ∧
        Function.Injective (algebraMap ℤ_[l] O) ∧ Module.Free ℤ_[l] O ∧ IsLocalHom (algebraMap ℤ_[l] O) := by
  intro l hl O _ _ _ _ _ _
  have hl0 : (l : O) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  have hinj : Function.Injective (algebraMap ℤ_[l] O) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hx
    exact mul_ne_zero ((PadicInt.unitCoeff h0).isUnit.map _).ne_zero (pow_ne_zero _ hl0) hx
  have : FaithfulSMul ℤ_[l] O := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have hfree : Module.Free ℤ_[l] O := Module.free_of_finite_type_torsion_free'
  have hloc : IsLocalHom (algebraMap ℤ_[l] O) := inferInstance
  have hlm : (l : O) ∈ maximalIdeal O := by
    have h : (l : ℤ_[l]) ∈ maximalIdeal ℤ_[l] := by
      rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
    have := map_nonunit (algebraMap ℤ_[l] O) _ h
    rwa [map_natCast] at this
  have hres : Finite (ResidueField O) := by
    have : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
    exact Module.finite_of_finite (ResidueField ℤ_[l])
  refine ⟨?_, hres, hlm, hinj, hfree, hloc⟩
  have hP : IsPrecomplete (maximalIdeal O) O := by
    have h1 : IsPrecomplete ((maximalIdeal ℤ_[l]).map (algebraMap ℤ_[l] O)) O :=
      IsPrecomplete.map_algebraMap_iff.2 (prec_free _)
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast] at h1
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨e, he⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
      (s := Ideal.span {(l : O)}) (by simpa using hl0) hϖ
    refine prec_cofinal ((Ideal.span_singleton_le_iff_mem _).2 hlm) (e := e) ?_ h1
    rw [he, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  exact { toIsHausdorff := inferInstance, toIsPrecomplete := hP }
end

section

open PowerSeries IsLocalRing UpperTheory.V.abelian₂
open IsDiscreteValuationRing (addVal)
open scoped Pointwise TensorProduct Topology

private theorem mem_smul_top_pi {R : Type} [CommRing R] (J : Ideal R) {r : ℕ} (x : Fin r → R) :
    x ∈ J • (⊤ : Submodule R (Fin r → R)) ↔ ∀ i, x i ∈ J := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx (fun a ha y _ i => ?_) (fun a b ha hb i => ?_)
    · exact J.mul_mem_right _ ha
    · exact J.add_mem (ha i) (hb i)
  · intro hx
    rw [pi_eq_sum_univ x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top

private theorem isPrecomplete_pi {R : Type} [CommRing R] (I : Ideal R) [IsPrecomplete I R] (r : ℕ) :
    IsPrecomplete I (Fin r → R) := by
  refine ⟨fun {f} hf => ?_⟩
  have hc : ∀ i : Fin r, ∃ L : R, ∀ n, f n i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    intro i
    refine IsPrecomplete.prec' (f := fun n => f n i) ?_
    intro m n hmn
    have h := hf hmn
    rw [SModEq.sub_mem] at h ⊢
    rw [mem_smul_top_pi] at h
    have := h i
    simpa [Ideal.smul_top_eq_map, smul_eq_mul, Ideal.mul_top] using this
  choose L hL using hc
  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem, mem_smul_top_pi]
  intro i
  have := hL i n
  rw [SModEq.sub_mem] at this
  simpa [smul_eq_mul, Ideal.mul_top] using this

theorem UpperTheory.V.abelian₂.nakayama :
    ∀ (R : Type) [CommRing R] (I : Ideal R) [IsPrecomplete I R] (M : Type) [AddCommGroup M] [Module R M] [IsHausdorff I M],
      (∀ (r : ℕ) (s : Fin r → M), Submodule.span R (Set.range s) ⊔ I • (⊤ : Submodule R M) = ⊤ →
        Submodule.span R (Set.range s) = ⊤) ∧
      (Module.Finite R (M ⧸ I • (⊤ : Submodule R M)) → Module.Finite R M) := by
  intro R _ I _ M _ _ _
  have part1 : ∀ (r : ℕ) (s : Fin r → M), Submodule.span R (Set.range s) ⊔ I • (⊤ : Submodule R M) = ⊤ →
      Submodule.span R (Set.range s) = ⊤ := by
    intro r s hs
    have hsurj : Function.Surjective (Fintype.linearCombination R s) := by
      haveI := isPrecomplete_pi I r
      apply surjective_of_mkQ_comp_surjective (I := I)
      intro q
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      have hm : m ∈ Submodule.span R (Set.range s) ⊔ I • (⊤ : Submodule R M) := by
        rw [hs]; exact Submodule.mem_top
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hm
      rw [← Fintype.range_linearCombination, LinearMap.mem_range] at ha
      obtain ⟨c, rfl⟩ := ha
      refine ⟨c, ?_⟩
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
      rw [Submodule.Quotient.eq]
      simpa using Submodule.neg_mem _ hb
    rw [← Fintype.range_linearCombination, LinearMap.range_eq_top]
    exact hsurj
  refine ⟨part1, ?_⟩
  intro hfin
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M ⧸ I • (⊤ : Submodule R M))
  choose t ht using fun i => Submodule.Quotient.mk_surjective (I • (⊤ : Submodule R M)) (s i)
  have hsup : Submodule.span R (Set.range t) ⊔ I • (⊤ : Submodule R M) = ⊤ := by
    rw [sup_comm, ← Submodule.comap_map_mkQ, Submodule.map_span, ← Set.range_comp]
    have hcomp : (I • (⊤ : Submodule R M)).mkQ ∘ t = s := funext fun i => ht i
    rw [hcomp, hs, Submodule.comap_top]
  have htop := part1 r t hsup
  exact ⟨Submodule.fg_def.2 ⟨Set.range t, Set.finite_range t, htop⟩⟩
end
