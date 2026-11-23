module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.RingTheory.Invariant.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.FieldTheory.Separable
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
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.CosetCover
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Invariant.Galois
public import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.PowerBasis
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly

@[expose] public section

section

open Polynomial

namespace GlobalTheory.InvariantSpecialisation

theorem exists_extension {A B Ω : Type} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] (hinj : Function.Injective (algebraMap A B))
    [Field Ω] [IsAlgClosed Ω] (e : A →+* Ω) :
    ∃ φ : B →+* Ω, φ.comp (algebraMap A B) = e := by
  haveI hP : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B) (RingHom.ker e) ⊥
    (by
      intro a ha
      have : a = 0 := hinj (by simpa using ha)
      simp [this])
  haveI : Q.LiesOver (RingHom.ker e) := ⟨hQP.symm⟩
  letI : Algebra (A ⧸ RingHom.ker e) Ω := (RingHom.kerLift e).toAlgebra
  haveI : FaithfulSMul (A ⧸ RingHom.ker e) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective e)
  haveI : Algebra.IsIntegral (A ⧸ RingHom.ker e) (B ⧸ Q) := inferInstance
  haveI : IsDomain (A ⧸ RingHom.ker e) := Ideal.Quotient.isDomain _
  haveI : IsDomain (B ⧸ Q) := Ideal.Quotient.isDomain _
  haveI : FaithfulSMul (A ⧸ RingHom.ker e) (B ⧸ Q) := inferInstance
  haveI : Module.IsTorsionFree (A ⧸ RingHom.ker e) (B ⧸ Q) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (FaithfulSMul.algebraMap_injective _ _)
  haveI : Module.IsTorsionFree (A ⧸ RingHom.ker e) Ω :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (RingHom.kerLift_injective e)
  haveI : Algebra.IsAlgebraic (A ⧸ RingHom.ker e) (B ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let l : (B ⧸ Q) →ₐ[A ⧸ RingHom.ker e] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨(l : (B ⧸ Q) →+* Ω).comp (Ideal.Quotient.mk Q), ?_⟩
  ext a
  have h := l.commutes (Ideal.Quotient.mk _ a)
  exact h

theorem exists_smul_of_comp_eq {A B Ω : Type} [CommRing A] [CommRing B] [Algebra A B]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G B] [Algebra.IsInvariant A B G]
    [Field Ω] [CharZero Ω] (φ ψ : B →+* Ω)
    (h : ψ.comp (algebraMap A B) = φ.comp (algebraMap A B)) :
    ∃ g : G, ∀ b, ψ b = φ (g • b) := by
  classical
  letI := Fintype.ofFinite G
  have h1 : ∀ b, ∃ g : G, ψ b = φ (g • b) := by
    intro b
    obtain ⟨p, hp⟩ := Algebra.IsInvariant.charpoly_mem_lifts A B G b
    have hp' : p.map (algebraMap A B) = MulSemiringAction.charpoly G b := hp
    have e1 : (MulSemiringAction.charpoly G b).map ψ = (MulSemiringAction.charpoly G b).map φ := by
      rw [← hp', Polynomial.map_map, Polynomial.map_map, h]
    have e2 : ((MulSemiringAction.charpoly G b).map ψ).eval (ψ b) = 0 := by
      rw [Polynomial.eval_map, Polynomial.eval₂_hom, MulSemiringAction.eval_charpoly, map_zero]
    rw [e1, MulSemiringAction.charpoly_eq, Polynomial.map_prod, Polynomial.eval_prod,
      Finset.prod_eq_zero_iff] at e2
    obtain ⟨g, -, hg⟩ := e2
    refine ⟨g, ?_⟩
    simpa [sub_eq_zero] using hg
  let H : G → AddSubgroup B := fun g =>
    { carrier := {b | ψ b = φ (g • b)}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_add (f := _), smul_add, map_add (f := _), ha, hb]
      neg_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [map_neg, smul_neg, map_neg, ha] }
  obtain ⟨g, -, hg⟩ := AddSubgroup.exists_finiteIndex_of_leftCoset_cover
    (H := H) (g := fun _ => 0) (s := Finset.univ) (by
      rw [Set.eq_univ_iff_forall]
      intro b
      obtain ⟨g, hg⟩ := h1 b
      simp only [Set.mem_iUnion]
      exact ⟨g, Finset.mem_univ _, b, hg, zero_add b⟩)
  refine ⟨g, fun b => ?_⟩
  have h2 : ψ ((H g).index • b) = φ (g • ((H g).index • b)) := (H g).nsmul_index_mem b
  rw [smul_comm g, map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul] at h2
  exact mul_left_cancel₀ (Nat.cast_ne_zero.2 hg.index_ne_zero) h2

theorem exists_finite_extension_finrank_dvd :
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (G : Type) [Group G] [Finite G]
      [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G],
      Function.Injective (algebraMap A B) → ∀ (k : Type) [Field k] [CharZero k] (ev : A →+* k),
      ∃ (K' : Type) (_ : Field K') (_ : Algebra k K') (β : B →+* K'), FiniteDimensional k K' ∧
        Module.finrank k K' ∣ Nat.card G ∧
        β.comp (algebraMap A B) = (algebraMap k K').comp ev := by
  intro A B _ _ _ G _ _ _ _ _ hinj k _ _ ev
  haveI := Algebra.IsInvariant.isIntegral A B G
  let Ω := AlgebraicClosure k
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  obtain ⟨φ, hφ⟩ := exists_extension hinj ((algebraMap k Ω).comp ev)
  let K : IntermediateField k Ω := IntermediateField.adjoin k (Set.range φ)
  let P : Subgroup ((Ω ≃ₐ[k] Ω) × G) :=
    { carrier := {x | ∀ b, x.1 (φ b) = φ (x.2 • b)}
      one_mem' := by intro b; simp
      mul_mem' := by
        intro x y hx hy b
        simp only [Prod.fst_mul, Prod.snd_mul, AlgEquiv.mul_apply]
        rw [hy, hx, mul_smul]
      inv_mem' := by
        intro x hx b
        apply x.1.injective
        rw [hx]
        simp }
  let p₁ : P →* (Ω ≃ₐ[k] Ω) := (MonoidHom.fst _ _).comp P.subtype
  let p₂ : P →* G := (MonoidHom.snd _ _).comp P.subtype
  have hsurj : Function.Surjective p₁ := by
    intro σ
    obtain ⟨g, hg⟩ := exists_smul_of_comp_eq (A := A) G φ ((σ : Ω →+* Ω).comp φ) (by
      rw [RingHom.comp_assoc, hφ]
      ext a
      simp)
    exact ⟨⟨(σ, g), hg⟩, rfl⟩
  have hle : p₂.ker ≤ K.fixingSubgroup.comap p₁ := by
    rintro ⟨⟨σ, g⟩, hx⟩ hg
    have hg1 : g = 1 := hg
    subst hg1
    change σ ∈ K.fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hxK
    induction hxK using IntermediateField.adjoin_induction with
    | mem x hx' =>
      obtain ⟨b, rfl⟩ := hx'
      simpa using hx b
    | algebraMap c => exact σ.commutes c
    | add x y _ _ h1 h2 => rw [map_add (f := _), h1, h2]
    | inv x _ h1 => rw [map_inv₀, h1]
    | mul x y _ _ h1 h2 => rw [map_mul, h1, h2]
  have hdvd : Module.finrank k K ∣ Nat.card G := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index,
      ← Subgroup.index_comap_of_surjective _ hsurj]
    refine (Subgroup.index_dvd_of_le hle).trans ?_
    rw [Subgroup.index_ker]
    exact Subgroup.card_subgroup_dvd_card _
  refine ⟨K, inferInstance, inferInstance,
    φ.codRestrict K (fun b => IntermediateField.subset_adjoin _ _ ⟨b, rfl⟩), ?_, hdvd, ?_⟩
  · exact Module.finite_of_finrank_pos (Nat.pos_of_dvd_of_pos hdvd Nat.card_pos)
  · ext a
    exact RingHom.congr_fun hφ a

end GlobalTheory.InvariantSpecialisation
end

section

namespace GlobalTheory.SepPoint

noncomputable def adjoinEquiv (k F : Type) [Field k] [Field F] [Algebra k F] (s : Finset F)
    (hs : AlgebraicIndependent k ((↑) : s → F)) :
    MvPolynomial s k ≃ₐ[k] Algebra.adjoin k (s : Set F) :=
  hs.aevalEquiv.trans (Subalgebra.equivOfEq _ _ (by rw [Subtype.range_coe]))

theorem isIntegrallyClosed_adjoin (k F : Type) [Field k] [Field F] [Algebra k F] (s : Finset F)
    (hs : AlgebraicIndependent k ((↑) : s → F)) :
    IsIntegrallyClosed (Algebra.adjoin k (s : Set F)) := by
  haveI : UniqueFactorizationMonoid (Algebra.adjoin k (s : Set F)) :=
    (adjoinEquiv k F s hs).toMulEquiv.uniqueFactorizationMonoid inferInstance
  infer_instance

theorem infinite_of_isSepClosed (Ω : Type) [Field Ω] [IsSepClosed Ω] : Infinite Ω := by
  by_contra h
  rw [not_infinite_iff_finite] at h
  haveI : IsAlgClosed Ω := IsSepClosed.isAlgClosed_of_perfectField Ω
  exact h.false.elim

theorem exists_ev (k F : Type) [Field k] [Field F] [Algebra k F] (s : Finset F)
    (hs : AlgebraicIndependent k ((↑) : s → F)) (H : Algebra.adjoin k (s : Set F)) (hH : H ≠ 0) :
    ∃ ev : Algebra.adjoin k (s : Set F) →ₐ[k] SeparableClosure k, ev H ≠ 0 := by
  haveI := infinite_of_isSepClosed (SeparableClosure k)
  let e := adjoinEquiv k F s hs
  have hP : e.symm H ≠ 0 := by simpa using hH
  obtain ⟨a, ha⟩ : ∃ a : s → SeparableClosure k,
      MvPolynomial.eval a ((e.symm H).map (algebraMap k (SeparableClosure k))) ≠ 0 := by
    by_contra! h
    apply hP
    have := MvPolynomial.funext (p := (e.symm H).map (algebraMap k (SeparableClosure k)))
      (q := 0) (fun x => by simp [h x])
    exact MvPolynomial.map_injective _ (algebraMap k (SeparableClosure k)).injective
      (by simpa using this)
  refine ⟨(MvPolynomial.aeval a).comp e.symm.toAlgHom, ?_⟩
  simpa [MvPolynomial.aeval_eq_eval₂Hom, MvPolynomial.eval_map] using ha

end GlobalTheory.SepPoint
end

section

namespace GlobalTheory

theorem residueField_localization_atPrime_isSepClosed_of_finiteType :
    ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
      (P : Ideal B) [P.IsMaximal],
      IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime P)) := by
  intro k B _ _ _ _ _ P _
  letI : Field (B ⧸ P) := Ideal.Quotient.field P
  haveI : Module.Finite k (B ⧸ P) := finite_of_finite_type_of_isJacobsonRing k (B ⧸ P)
  haveI : Algebra.IsIntegral k (B ⧸ P) := inferInstance
  let f : k ≃+* (B ⧸ P) := RingEquiv.ofBijective (algebraMap k (B ⧸ P))
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  haveI : IsAlgClosed (B ⧸ P) := IsAlgClosed.of_ringEquiv k (B ⧸ P) f
  let e : (B ⧸ P) ≃+* IsLocalRing.ResidueField (Localization.AtPrime P) :=
    (IsLocalization.AtPrime.equivQuotMaximalIdeal P (Localization.AtPrime P)).toRingEquiv
  haveI : IsAlgClosed (IsLocalRing.ResidueField (Localization.AtPrime P)) :=
    IsAlgClosed.of_ringEquiv _ _ e
  infer_instance

end GlobalTheory
end

section

universe u_1 u_2 u_3 u_4

namespace GlobalTheory.ContinuityFromFixedPoints

open Topology

theorem continuous_of_forall_exists_fix {k : Type u_1} {F : Type u_2} {k' : Type u_3}
    {F' : Type u_4} [Field k] [Field F] [Algebra k F] [Field k'] [Field F'] [Algebra k' F']
    [Algebra.IsIntegral k F] (φ : Gal(F/k) →* Gal(F'/k'))
    (h : ∀ y : F', ∃ x : F, ∀ σ : Gal(F/k), σ x = x → φ σ y = y) :
    Continuous φ := by
  classical
  choose x hx using h
  refine continuous_of_continuousAt_one φ ?_
  rw [ContinuousAt, map_one]
  intro s hs
  obtain ⟨E', hE', hs'⟩ := (krullTopology_mem_nhds_one_iff k' F' s).1 hs
  let b := Module.finBasis k' E'
  let S : Set F := Set.range fun i => x (b i : F')
  have hS : S.Finite := Set.finite_range _
  haveI : Finite S := hS.to_subtype
  have hfin : FiniteDimensional k (IntermediateField.adjoin k S) :=
    IntermediateField.finiteDimensional_adjoin fun z _ => Algebra.IsIntegral.isIntegral z
  rw [Filter.mem_map]
  refine (krullTopology_mem_nhds_one_iff k F _).2 ⟨IntermediateField.adjoin k S, hfin, ?_⟩
  intro σ hσ
  apply hs'
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
  have hb : ∀ i, φ σ (b i : F') = b i := fun i =>
    hx _ σ (hσ _ (IntermediateField.subset_adjoin k S ⟨i, rfl⟩))
  intro y hy
  have hlin : ((φ σ).toLinearMap ∘ₗ E'.val.toLinearMap) = E'.val.toLinearMap :=
    b.ext fun i => by simpa using hb i
  simpa using LinearMap.congr_fun hlin ⟨y, hy⟩

end GlobalTheory.ContinuityFromFixedPoints
end

section

open scoped TensorProduct Classical
open Polynomial

namespace GlobalTheory.DescCoeff

theorem natDegree_minpoly_le_one_tmul {F A : Type} [Field F] [Ring A] [Algebra F A] (K : Type)
    [Field K] [Algebra F K] (g : A) (hK : IsIntegral K ((1 : K) ⊗ₜ[F] g)) :
    (minpoly F g).natDegree ≤ (minpoly K ((1 : K) ⊗ₜ[F] g)).natDegree := by
  set x : K ⊗[F] A := (1 : K) ⊗ₜ[F] g with hx
  have hli : LinearIndependent K (fun j : Fin (minpoly F g).natDegree => x ^ (j : ℕ)) := by
    have h := Module.Flat.linearIndependent_one_tmul (S := K) (linearIndependent_pow (K := F) g)
    convert h using 1
    funext j
    simp [hx, Algebra.TensorProduct.tmul_pow]
  by_contra hlt
  push_neg at hlt
  have hsum := aeval_eq_sum_range' hlt x
  rw [minpoly.aeval, ← Fin.sum_univ_eq_sum_range (fun i => (minpoly K x).coeff i • x ^ i)] at hsum
  have hc := Fintype.linearIndependent_iff.mp hli (fun i => (minpoly K x).coeff i) hsum.symm
  apply minpoly.ne_zero hK
  ext i
  rw [coeff_zero]
  by_cases hi : i < (minpoly F g).natDegree
  · exact hc ⟨i, hi⟩
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem minpoly_one_tmul_eq {F B : Type} [Field F] [Ring B] [Algebra F B] [FiniteDimensional F B]
    (K : Type) [Field K] [Algebra F K] (y : B) :
    minpoly K ((1 : K) ⊗ₜ[F] y) = (minpoly F y).map (algebraMap F K) := by
  set z : K ⊗[F] B := (1 : K) ⊗ₜ[F] y with hz
  have hzi : IsIntegral K z := IsIntegral.of_finite K z
  have hyi : IsIntegral F y := IsIntegral.of_finite F y
  have hzr : z = Algebra.TensorProduct.includeRight y := rfl
  have hdvd : minpoly K z ∣ (minpoly F y).map (algebraMap F K) := by
    apply minpoly.dvd
    rw [aeval_map_algebraMap, hzr, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hge := natDegree_minpoly_le_one_tmul K y hzi
  have := eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (minpoly.monic hzi) hdvd
    (by rw [natDegree_map]; exact hge)
  rw [this, ((minpoly.monic hyi).map _).leadingCoeff, C_1, one_mul]

end GlobalTheory.DescCoeff
end

section

namespace GlobalTheory

open Polynomial

theorem extend_alg_hom_adjoin_integral_root :
    ∀ (k F Ω : Type) [Field k] [Field F] [Algebra k F] [Field Ω] [Algebra k Ω]
    (R : Subalgebra k F) [IsIntegrallyClosed R] (θ : F), IsIntegral R θ →
    ∀ (ev : R →ₐ[k] Ω) (r : Ω), Polynomial.eval₂ (ev : R →+* Ω) r (minpoly R θ) = 0 →
    ∃ ψ : Algebra.adjoin k (insert θ (R : Set F)) →ₐ[k] Ω,
      ∀ (x : F) (hx : x ∈ R) (hx' : x ∈ Algebra.adjoin k (insert θ (R : Set F))),
        ψ ⟨x, hx'⟩ = ev ⟨x, hx⟩ := by
  intro k F Ω _ _ _ _ _ R _ θ hθ ev r hr
  let S : Subalgebra R F := Algebra.adjoin R {θ}
  let e : AdjoinRoot (minpoly R θ) ≃ₐ[R] S := minpoly.equivAdjoin hθ
  let φ : S →+* Ω := (AdjoinRoot.lift (ev : R →+* Ω) r hr).comp (e.symm : S →+* AdjoinRoot (minpoly R θ))
  have hφ : ∀ (x : F) (hx : x ∈ R) (hxS : x ∈ S), φ ⟨x, hxS⟩ = ev ⟨x, hx⟩ := by
    intro x hx hxS
    have h1 : (⟨x, hxS⟩ : S) = algebraMap R S ⟨x, hx⟩ := rfl
    simp only [φ, RingHom.comp_apply, h1]
    rw [show (e.symm : S →+* AdjoinRoot (minpoly R θ)) (algebraMap R S ⟨x, hx⟩)
        = AdjoinRoot.of (minpoly R θ) ⟨x, hx⟩ from e.symm.commutes _]
    exact AdjoinRoot.lift_of hr
  have hle : Algebra.adjoin k (insert θ (R : Set F)) ≤ S.restrictScalars k := by
    rw [Algebra.adjoin_le_iff, Set.insert_subset_iff]
    refine ⟨?_, ?_⟩
    · show θ ∈ S
      exact Algebra.subset_adjoin (Set.mem_singleton _)
    · intro y hy
      show y ∈ S
      exact S.algebraMap_mem (⟨y, hy⟩ : R)
  have hmem : ∀ z : Algebra.adjoin k (insert θ (R : Set F)), (z : F) ∈ S := fun z => hle z.2
  let ψ₀ : Algebra.adjoin k (insert θ (R : Set F)) →+* Ω :=
    { toFun := fun z => φ ⟨z.1, hmem z⟩
      map_one' := φ.map_one
      map_mul' := fun a b => φ.map_mul ⟨a.1, hmem a⟩ ⟨b.1, hmem b⟩
      map_zero' := φ.map_zero
      map_add' := fun a b => φ.map_add ⟨a.1, hmem a⟩ ⟨b.1, hmem b⟩ }
  refine ⟨{ ψ₀ with commutes' := fun c => ?_ }, fun x hx hx' => hφ x hx (hle hx')⟩
  exact (hφ (algebraMap k F c) (R.algebraMap_mem c) _).trans (ev.commutes c)

end GlobalTheory
end

section

namespace GlobalTheory

attribute [local instance] Subgroup.finiteIndex_of_finite_quotient

attribute [local instance] Ideal.Quotient.field in
theorem Ideal.Quotient.normal_of_profinite
    {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    (G : Type) [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G] [IsTopologicalGroup G]
    [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul G B] [Algebra.IsInvariant A B G]
    (P : Ideal A) (Q : Ideal B) [Q.LiesOver P] [P.IsMaximal] [Q.IsMaximal] :
    Normal (A ⧸ P) (B ⧸ Q) := by
  have hint : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral_of_profinite (G := G)
  have hint' : Algebra.IsIntegral (A ⧸ P) (B ⧸ Q) := Ideal.Quotient.algebra_isIntegral_of_liesOver Q P
  refine normal_iff.2 fun ξ => ⟨Algebra.IsIntegral.isIntegral ξ, ?_⟩
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective ξ
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (stabilizer_isOpen G b) (one_mem _)
  let B' := FixedPoints.subalgebra A B N.1.1
  let b' : B' := ⟨b, fun g => hN g.2⟩
  let Q' : Ideal B' := Q.under B'
  have hintB : Algebra.IsIntegral B' B := Algebra.IsIntegral.tower_top A
  have hQ' : Q'.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal Q
  have : Q'.LiesOver P := ⟨by
    rw [Ideal.under_under (A := A) (B := B') (C := B)]
    exact Ideal.LiesOver.over⟩
  have hn : Normal (A ⧸ P) (B' ⧸ Q') := Ideal.Quotient.normal (G ⧸ N.1.1) P Q'
  let f : (B' ⧸ Q') →ₐ[A ⧸ P] B ⧸ Q :=
    { toRingHom := Ideal.quotientMap _ B'.val le_rfl,
      commutes' := Quotient.ind fun _ ↦ rfl }
  have hf : Function.Injective f := f.toRingHom.injective
  have hfb : f (Ideal.Quotient.mk Q' b') = Ideal.Quotient.mk Q b := rfl
  rw [← hfb, minpoly.algHom_eq f hf]
  have hs := hn.splits (Ideal.Quotient.mk Q' b')
  have := hs.map f.toRingHom
  rw [Polynomial.map_map] at this
  have hc : (f : (B' ⧸ Q') →+* B ⧸ Q).comp (algebraMap (A ⧸ P) (B' ⧸ Q')) = algebraMap (A ⧸ P) (B ⧸ Q) := f.comp_algebraMap
  simpa only [AlgHom.toRingHom_eq_coe, hc] using this

end GlobalTheory
end

section

open Matrix Polynomial

namespace GlobalTheory

theorem adjoin_matrix_reduced_of_charpoly_separable :
    ∀ (K : Type) [Field K] (n : ℕ) (N : Matrix (Fin n) (Fin n) K), N.charpoly.Separable →
      ∀ g ∈ Algebra.adjoin K {N}, ∀ m : ℕ, g ^ m = 0 → g = 0 := by
  intro K _ n N hsep g hg m hm
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · rw [pow_zero] at hm
    calc g = g * 1 := (mul_one g).symm
      _ = 0 := by rw [hm, mul_zero]
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hg
  obtain ⟨P, rfl⟩ := hg
  have h1 : minpoly K N ∣ P ^ m := minpoly.dvd K N (by rw [map_pow]; exact hm)
  have hs : (minpoly K N).Separable := hsep.of_dvd (Matrix.minpoly_dvd_charpoly N)
  have h2 : minpoly K N ∣ P := (hs.squarefree.dvd_pow_iff_dvd hmpos.ne').mp h1
  obtain ⟨q, hq⟩ := h2
  show aeval N P = 0
  rw [hq, map_mul, minpoly.aeval, zero_mul]

end GlobalTheory
end
