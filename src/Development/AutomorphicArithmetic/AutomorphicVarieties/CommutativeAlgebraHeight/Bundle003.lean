module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle004
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle001
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle015
public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain
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
public import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle002
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Ideal.GoingDown

@[expose] public section

section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem u_gen_approx {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (m : Ideal R)
    (A : Subalgebra O R) (T : Set R) (h0 : ∀ x : R, ∃ a : O, x - algebraMap O R a ∈ m)
    (hT : ∀ t ∈ T, t ∈ A ∧ t ∈ m) (hm : m ≤ Ideal.span T ⊔ m ^ 2) (N : ℕ) (x : R) :
    ∃ a ∈ A, x - a ∈ m ^ N :=
  _root_.UpperTheory.Reformulated.B.LayerApproximation.co_ext_approx m A T h0 hT hm N x

private theorem u_gen_dual (O : Type) [CommRing O] [IsLocalRing O] (M : Type) [AddCommGroup M] [Module O M]
    (h : Module.IsTorsionBySet O M (maximalIdeal O)) (x : M) (hx : x ≠ 0) :
    ∃ D : M →ₗ[O] ResidueField O, D x ≠ 0 := by
  letI : Module (ResidueField O) M := h.module
  haveI : IsScalarTower O (ResidueField O) M := h.isScalarTower
  have := (Module.forall_dual_apply_eq_zero_iff (ResidueField O) x).not.2 hx
  push Not at this
  obtain ⟨φ, hφ⟩ := this
  exact ⟨φ.restrictScalars O, hφ⟩

private theorem u_gen_span (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R]
    [IsCO O R] (S : Set R) (hS : S ⊆ maximalIdeal R)
    (hO' : ∀ a ∈ maximalIdeal O, algebraMap O R a ∈ S)
    (H : ∀ f f' : R →ₐ[O] DualNumber (ResidueField O), (∀ s ∈ S, f s = f' s) → f = f') :
    maximalIdeal R ≤ Ideal.span S ⊔ maximalIdeal R ^ 2 := by
  intro x hx
  set I : Ideal R := Ideal.span S ⊔ maximalIdeal R ^ 2 with hI
  by_contra hxI
  have hIm : I ≤ maximalIdeal R :=
    sup_le (Ideal.span_le.2 hS) (Ideal.pow_le_self two_ne_zero)
  have hO : ∀ a ∈ maximalIdeal O, algebraMap O R a ∈ I := fun a ha =>
    Ideal.mem_sup_left (Ideal.subset_span (hO' a ha))
  let N : Submodule O R := I.restrictScalars O ⊔ Submodule.span O {1}
  have hIN : ∀ y ∈ I, y ∈ N := fun y hy => Submodule.mem_sup_left hy
  have hON : ∀ a : O, algebraMap O R a ∈ N := fun a =>
    Submodule.mem_sup_right (Submodule.mem_span_singleton.2 ⟨a, (Algebra.algebraMap_eq_smul_one a).symm⟩)
  have hxN : N.mkQ x ≠ 0 := by
    intro h
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 ((Submodule.Quotient.mk_eq_zero N).1 h)
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
    rw [← Algebra.algebraMap_eq_smul_one] at hyz
    have h1 : algebraMap O R a ∈ maximalIdeal R := by
      have := Ideal.sub_mem _ hx (hIm hy)
      rwa [← hyz, add_sub_cancel_left] at this
    have h2 : a ∈ maximalIdeal O := fun h => h1 (h.map _)
    exact hxI (hyz ▸ I.add_mem hy (hO a h2))
  have htor : Module.IsTorsionBySet O (R ⧸ N) (maximalIdeal O) := by
    rintro y ⟨a, ha⟩
    obtain ⟨y, rfl⟩ := N.mkQ_surjective y
    show a • N.mkQ y = 0
    rw [← map_smul]
    refine (Submodule.Quotient.mk_eq_zero N).2 (hIN _ ?_)
    rw [Algebra.smul_def]
    exact I.mul_mem_right _ (hO a ha)
  obtain ⟨φ, hφ⟩ := u_gen_dual O _ htor _ hxN
  let D : R →ₗ[O] ResidueField O := φ ∘ₗ N.mkQ
  have hD : ∀ y ∈ N, D y = 0 := fun y hy => by
    show φ (N.mkQ y) = 0
    rw [show N.mkQ y = 0 from (Submodule.Quotient.mk_eq_zero N).2 hy, map_zero]
  have hres : ∀ (y : R) (a : O), y - algebraMap O R a ∈ maximalIdeal R → res O R y = algebraMap O _ a :=
    fun y a ha => by
      have := (res_eq_zero_iff O R _).2 ha
      rwa [map_sub, AlgHom.commutes, sub_eq_zero] at this
  have hmul : ∀ y z, D (y * z) = res O R y * D z + D y * res O R z := fun y z => by
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) y
    obtain ⟨b, hb⟩ := IsCO.res_surj (O := O) z
    have h1 : D ((y - algebraMap O R a) * (z - algebraMap O R b)) = 0 :=
      hD _ (hIN _ (Ideal.mem_sup_right (by rw [pow_two]; exact Ideal.mul_mem_mul ha hb)))
    have h2 : y * z = (y - algebraMap O R a) * (z - algebraMap O R b) + a • z + b • y
        - algebraMap O R (a * b) := by
      simp only [Algebra.smul_def, map_mul]; ring
    rw [h2, map_sub, map_add (f := _), map_add (f := _), h1, hD _ (hON _), map_smul, map_smul, hres y a ha, hres z b hb]
    simp only [Algebra.smul_def]; ring
  let f : R →ₐ[O] DualNumber (ResidueField O) :=
    { toFun := fun y => (res O R y, D y)
      map_one' := by
        ext
        · exact map_one (res O R)
        · exact hD _ (by simpa using hON 1)
      map_mul' := fun y z => by
        ext
        · exact map_mul (res O R) y z
        · exact hmul y z
      map_zero' := by
        ext
        · exact map_zero (res O R)
        · exact map_zero D
      map_add' := fun y z => by
        ext
        · exact map_add (res O R) y z
        · exact map_add D y z
      commutes' := fun a => by
        ext
        · exact (res O R).commutes a
        · exact hD _ (hON a) }
  let f' : R →ₐ[O] DualNumber (ResidueField O) :=
    (TrivSqZeroExt.inlAlgHom O (ResidueField O) (ResidueField O)).comp (res O R)
  have key : ∀ y, D y = 0 → f y = f' y := fun y hy => by
    ext
    · rfl
    · exact hy
  have hff : f = f' :=
    H f f' fun s hs => key _ (hD _ (hIN _ (Ideal.mem_sup_left (Ideal.subset_span hs))))
  exact hφ (congrArg (fun g : R →ₐ[O] DualNumber (ResidueField O) => (g x).snd) hff)

theorem UpperTheory.V.CA.u_gen :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (T : Set R), (∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f f' : R →ₐ[O] R'), (∀ t ∈ T, f t = f' t) → f = f') → ∀ (N : ℕ) (x : R), ∃ y ∈ Algebra.adjoin O T, x - y ∈ maximalIdeal R ^ N := by
  intro O _ _ R _ _ _ T H N x
  refine u_gen_approx (maximalIdeal R) (Algebra.adjoin O T)
    {y | y ∈ Algebra.adjoin O T ∧ y ∈ maximalIdeal R} (IsCO.res_surj (O := O)) (fun _ h => h) ?_ N x
  refine u_gen_span O R _ (fun _ h => h.2)
    (fun a ha => ⟨Subalgebra.algebraMap_mem _ a, fun h => ha (IsLocalHom.map_nonunit a h)⟩) ?_
  intro f f' h
  haveI := (co_res O).2
  refine H _ f f' fun t ht => ?_
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) t
  have := h _ ⟨sub_mem (Algebra.subset_adjoin ht) (Subalgebra.algebraMap_mem _ a), ha⟩
  rwa [map_sub, map_sub, AlgHom.commutes, AlgHom.commutes, sub_left_inj] at this
end

section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem idempotent_sandwich_list_prod_eq_of_kernel {k E : Type} [Field k] [Ring E] [Algebra k E] {n : ℕ}
    (π : E →ₐ[k] (Fin n → k)) (e g g' : E) (hg : g = e + g')
    (hJ : ∀ z, π z = 0 → e * z * e = 0) (t : List E) :
    ∀ a, π a = 0 → e * a * (g * (t.map (· * g)).prod) = e * a * (g' * (t.map (· * g')).prod) := by
  induction t with
  | nil =>
    intro a ha
    simp only [List.map_nil, List.prod_nil, mul_one]
    rw [hg, mul_add, hJ a ha, zero_add]
  | cons z s ih =>
    intro a ha
    simp only [List.map_cons, List.prod_cons]
    have hmem : π (a * g' * z) = 0 := by simp [map_mul, ha]
    calc e * a * (g * (z * g * (s.map (· * g)).prod))
        = (e * a * g) * (z * (g * (s.map (· * g)).prod)) := by simp only [mul_assoc]
      _ = (e * a * e + e * a * g') * (z * (g * (s.map (· * g)).prod)) := by rw [← mul_add, ← hg]
      _ = e * (a * g' * z) * (g * (s.map (· * g)).prod) := by
          rw [hJ a ha, zero_add]; simp only [mul_assoc]
      _ = e * (a * g' * z) * (g' * (s.map (· * g')).prod) := ih _ hmem
      _ = e * a * (g' * (z * g' * (s.map (· * g')).prod)) := by simp only [mul_assoc]

theorem UpperTheory.V.CA.f_nil :
    ∀ {n : ℕ} {k E : Type} [Field k] [Ring E] [Algebra k E] (e : Fin n → E) (π : E →ₐ[k] (Fin n → k)), CompleteOrthogonalIdempotents e → (∀ i, π (e i) = Pi.single i 1) → (∀ i x, ∃ a : k, e i * x * e i = a • e i) → (∀ x, π x = 0 ↔ ∀ i, e i * x * e i = 0) ∧ ∀ x : Fin n → E, (∀ s, π (x s) = 0) → (List.ofFn x).prod = 0 := by
  intro n k E _ _ _ e π he hπ hsc
  have hJ : ∀ z, π z = 0 → ∀ i, e i * z * e i = 0 := by
    intro z hz i
    obtain ⟨a, ha⟩ := hsc i z
    have ha0 : a = 0 := by
      simpa [map_mul, hz, hπ] using (congrFun (congrArg π ha) i).symm
    rw [ha, ha0, zero_smul]
  refine ⟨fun x => ⟨fun hz i => hJ x hz i, fun h => ?_⟩, fun x hx => ?_⟩
  · funext i
    have h2 := congrFun (congrArg π (h i)) i
    simpa [map_mul, hπ] using h2
  · obtain ⟨F, hF⟩ : ∃ F : Finset (Fin n) → E, ∀ T, F T = ∑ i ∈ T, e i := ⟨_, fun _ => rfl⟩
    have D : ∀ (m : ℕ) (T : Finset (Fin n)), T.card = m → ∀ t : List E, (∀ y ∈ t, π y = 0) →
        m ≤ t.length → F T * (t.map (· * F T)).prod = 0 := by
      intro m
      induction m with
      | zero =>
        intro T hT t _ _
        rw [Finset.card_eq_zero] at hT
        subst hT
        simp [hF]
      | succ m ih =>
        intro T hT t ht hlen
        cases t with
        | nil => simp at hlen
        | cons y s =>
          rw [show F T * ((y :: s).map (· * F T)).prod =
              ∑ i ∈ T, e i * ((y :: s).map (· * F T)).prod by rw [hF T, Finset.sum_mul]]
          apply Finset.sum_eq_zero
          intro i hi
          simp only [List.map_cons, List.prod_cons]
          rw [show e i * (y * F T * (s.map (· * F T)).prod) =
              e i * y * (F T * (s.map (· * F T)).prod) by simp only [mul_assoc]]
          have hsplit : F T = e i + F (T.erase i) := by
            rw [hF, hF, Finset.add_sum_erase T e hi]
          rw [idempotent_sandwich_list_prod_eq_of_kernel π (e i) (F T) (F (T.erase i)) hsplit (fun z hz => hJ z hz i) s y
            (ht y (by simp))]
          rw [ih (T.erase i) (by rw [Finset.card_erase_of_mem hi, hT]; rfl) s
            (fun z hz => ht z (by simp [hz])) (by simp at hlen; omega), mul_zero]
    have key := D n Finset.univ (by simp) (List.ofFn x)
      (by
        intro y hy
        rw [List.mem_ofFn] at hy
        obtain ⟨s, rfl⟩ := hy
        exact hx s)
      (by simp)
    have h1 : F Finset.univ = 1 := by rw [hF]; exact he.complete
    rw [h1, one_mul, show (fun y : E => y * 1) = id from funext mul_one, List.map_id] at key
    exact key
end

section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem dli_left_inv {E : Type} [Ring E] {j : E} (hj : j ∈ Ring.jacobson E) :
    ∃ z : E, z * (1 - j) = 1 := by
  rw [← Ideal.jacobson_bot, Ideal.mem_jacobson_iff] at hj
  obtain ⟨z, hz⟩ := hj (-1)
  rw [Ideal.mem_bot] at hz
  refine ⟨z, ?_⟩
  rw [← sub_eq_zero, ← hz]
  noncomm_ring

private theorem dli_idem_zero {E : Type} [Ring E] {u : E} (hu : IsIdempotentElem u)
    (hj : u ∈ Ring.jacobson E) : u = 0 := by
  obtain ⟨z, hz⟩ := dli_left_inv hj
  calc u = z * (1 - u) * u := by rw [hz, one_mul]
    _ = 0 := by rw [mul_assoc, sub_mul, one_mul, hu.eq, sub_self, mul_zero]

private theorem dli_mem_max {A B E : Type} [CommRing A] [CommRing B] [Ring E] [Algebra A B] [Algebra A E]
    [Algebra.IsIntegral A E] (ι : B →ₐ[A] E) (hι : Function.Injective ι) {y : B}
    (hy : ι y ∈ Ring.jacobson E) (M : Ideal B) (hM : M.IsMaximal) : y ∈ M := by
  by_contra hyM
  obtain ⟨b, m, hm, hbm⟩ := hM.exists_inv hyM
  have h1 : ι (b * y) ∈ Ring.jacobson E := by
    rw [map_mul]; exact Ideal.mul_mem_left _ _ hy
  obtain ⟨z, hz⟩ := dli_left_inv h1
  have hm' : 1 - ι (b * y) = ι m := by
    rw [← map_one ι, ← map_sub, ← hbm]; simp
  rw [hm'] at hz
  obtain ⟨p, hp, hp0⟩ := Algebra.IsIntegral.isIntegral (R := A) z
  have hpow : ∀ i : ℕ, z ^ i * ι m ^ i = 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ z, pow_succ' (ι m), mul_assoc, ← mul_assoc z, hz, one_mul, ih]
  rw [← aeval_def, aeval_eq_sum_range] at hp0
  have h2 : ι (∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • m ^ (p.natDegree - i)) = ι 0 := by

    rw [map_zero, ← zero_mul (ι m ^ p.natDegree), ← hp0, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ p.natDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [map_smul, map_pow, smul_mul_assoc]
    congr 1
    conv_rhs => rw [← Nat.add_sub_cancel' hi', pow_add, ← mul_assoc, hpow, one_mul]
  have h3 := hι h2
  rw [Finset.sum_range_succ, hp.coeff_natDegree, Nat.sub_self, pow_zero, one_smul] at h3
  apply hM.ne_top
  rw [Ideal.eq_top_iff_one, eq_neg_of_add_eq_zero_right h3]
  refine M.neg_mem (M.sum_mem fun i hi => ?_)
  rw [Algebra.smul_def]
  exact M.mul_mem_left _ (M.pow_mem_of_mem hm _ (Nat.sub_pos_of_lt (Finset.mem_range.1 hi)))

private theorem dli_comm {A B F : Type} [CommRing A] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A]
    [IsNoetherianRing A] [CommRing B] [Algebra A B] [Module.Finite A B] [Ring F] (φ : B →+* F) (x : B)
    (hx : IsIdempotentElem (φ x)) (hy : ∀ M : Ideal B, M.IsMaximal → x - x ^ 2 ∈ M) :
    ∃ e : B, IsIdempotentElem e ∧ φ e = φ x := by
  set K : Ideal B := (maximalIdeal A).map (algebraMap A B) with hK
  haveI : IsAdicComplete K B := GlobalTheory.isAdicComplete_map_of_finite _ B
  have hrad : x - x ^ 2 ∈ K.radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨hKP, hP⟩
    refine hy P (Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := A) P ?_)
    have : maximalIdeal A = P.under A :=
      (maximalIdeal.isMaximal A).eq_of_le (Ideal.comap_ne_top _ hP.ne_top) (Ideal.map_le_iff_le_comap.1 hKP)
    rw [← this]; exact maximalIdeal.isMaximal A
  obtain ⟨n, hn⟩ := hrad
  have hn' : (x - x ^ 2) ^ (n + 1) ∈ K := by rw [pow_succ]; exact K.mul_mem_right _ hn
  set a : B := 1 - (1 - x ^ (n + 1)) ^ (n + 1) with ha
  have hφa : φ a = φ x := by
    simp only [ha, map_sub, map_one, map_pow, hx.pow_succ_eq, hx.one_sub.pow_succ_eq, sub_sub_cancel]
  have h0 : a ^ 2 - a ∈ K := by
    have := isIdempotentElem_one_sub_one_sub_pow_pow (Ideal.Quotient.mk K x) (n + 1) (by
      rw [← map_pow, ← map_sub, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hn')
    rw [← Ideal.Quotient.eq, sq, map_mul]
    simpa [ha] using this.eq
  obtain ⟨e, he, he'⟩ := HenselianRing.is_henselian (I := K) (Polynomial.X ^ 2 - Polynomial.X : B[X])
    (by nontriviality B; monicity!) a (by simpa using h0) (by
      refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk K (2 * a - 1)) ?_
      rw [← map_mul, ← map_one (Ideal.Quotient.mk K), Ideal.Quotient.eq]
      convert K.mul_mem_left 4 h0 using 1
      simp only [derivative_sub, derivative_X_pow, derivative_X, eval_sub, eval_mul, eval_C, eval_pow, eval_X, eval_one]
      push_cast
      ring)
  have he2 : e * e - e = 0 := by simpa [sq] using he
  refine ⟨e, sub_eq_zero.1 he2, ?_⟩
  have hu : IsUnit ((e - a) * (-(e - a)) + 1) := Ring.mem_jacobson_iff.1 (HenselianRing.jac he') _
  have hk : a ^ 2 - a ∈ RingHom.ker φ := by
    rw [RingHom.mem_ker, map_sub, map_pow, hφa, sq, hx.eq, sub_self]
  have hd : (e - a) * ((e - a) * (-(e - a)) + 1) ∈ RingHom.ker φ := by
    have : (e - a) * ((e - a) * (-(e - a)) + 1) = -(3 * e - a - 1) * (a ^ 2 - a) := by
      linear_combination (-(e + 1 - 3 * a)) * he2
    rw [this]; exact Ideal.mul_mem_left _ _ hk
  rw [Ideal.mul_unit_mem_iff_mem _ hu, RingHom.mem_ker, map_sub, sub_eq_zero] at hd
  rw [hd, hφa]

section

variable {A E F : Type} [CommRing A] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A] [IsNoetherianRing A]
  [Ring E] [Algebra A E] [Algebra.IsIntegral A E] [Ring F] [Algebra A F] (π : E →ₐ[A] F)

private theorem dli_one (hk : ∀ x, π x = 0 → x ∈ Ring.jacobson E) (x : E) (hx : IsIdempotentElem (π x)) :
    ∃ e ∈ Algebra.adjoin A {x}, IsIdempotentElem e ∧ π e = π x := by
  haveI : Module.Finite A (Algebra.adjoin A {x}) :=
    Module.Finite.iff_fg.2 (Algebra.IsIntegral.isIntegral (R := A) x).fg_adjoin_singleton
  obtain ⟨e, he, he'⟩ := dli_comm (A := A) (B := Algebra.adjoin A {x})
    (π.comp (Algebra.adjoin A {x}).val).toRingHom ⟨x, Algebra.self_mem_adjoin_singleton A x⟩ hx
    (dli_mem_max (Algebra.adjoin A {x}).val Subtype.val_injective (hk _ (by
      simp [sq, hx.eq])))
  exact ⟨e, e.2, congrArg Subtype.val he.eq, he'⟩

private theorem dli_orth (hs : Function.Surjective π) (hk : ∀ x, π x = 0 → x ∈ Ring.jacobson E)
    (e₁ : F) (he₁ : IsIdempotentElem e₁) (e₂ : E) (he₂ : IsIdempotentElem e₂)
    (h₁ : e₁ * π e₂ = 0) (h₂ : π e₂ * e₁ = 0) :
    ∃ e' : E, IsIdempotentElem e' ∧ π e' = e₁ ∧ e' * e₂ = 0 ∧ e₂ * e' = 0 := by
  obtain ⟨y, rfl⟩ := hs e₁
  have hx : π ((1 - e₂) * y * (1 - e₂)) = π y := by
    simp only [map_mul, map_sub, map_one, sub_mul, mul_sub, one_mul, mul_one, h₁, h₂, zero_mul, sub_zero]
  obtain ⟨e, hm, he, he'⟩ := dli_one π hk ((1 - e₂) * y * (1 - e₂)) (hx ▸ he₁)
  rw [hx] at he'
  have hc0 : Commute e₂ ((1 - e₂) * y * (1 - e₂)) := by
    rw [Commute, SemiconjBy, ← mul_assoc, ← mul_assoc, he₂.mul_one_sub_self, mul_assoc _ (1 - e₂),
      he₂.one_sub_mul_self]
    simp
  have hc : Commute e₂ e := Algebra.commute_of_mem_adjoin_singleton_of_commute hm hc0
  have h0 : e₂ * e = 0 := dli_idem_zero (he₂.mul_of_commute hc he) (hk _ (by rw [map_mul, he', h₂]))
  exact ⟨e, he, he', by rw [← hc.eq, h0], h0⟩

private theorem dli_fin (hs : Function.Surjective π) (hk : ∀ x, π x = 0 → x ∈ Ring.jacobson E)
    {n : ℕ} {e : Fin n → F} (he : OrthogonalIdempotents e) :
    ∃ e' : Fin n → E, OrthogonalIdempotents e' ∧ π ∘ e' = e := by
  induction n with
  | zero => exact ⟨0, ⟨finZeroElim, finZeroElim⟩, funext finZeroElim⟩
  | succ n IH =>
    obtain ⟨e', h₁, h₂⟩ := IH (he.embedding (Fin.succEmb n))
    have h₂' (i) : π (e' i) = e i.succ := congr_fun h₂ i
    obtain ⟨e₀, h₃, h₄, h₅, h₆⟩ := dli_orth π hs hk _ (he.idem 0) _ h₁.isIdempotentElem_sum
      (by simp [Finset.mul_sum, h₂', he.mul_eq, eq_comm])
      (by simp [Finset.sum_mul, h₂', he.mul_eq])
    refine ⟨_, (h₁.option _ h₃ h₅ h₆).embedding (finSuccEquiv n).toEmbedding, funext fun i ↦ ?_⟩
    obtain ⟨_ | i, rfl⟩ := (finSuccEquiv n).symm.surjective i <;> simp [*]

end

theorem UpperTheory.V.CA.d_lift_idem :
    ∀ {A E F ι : Type} [CommRing A] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A] [IsNoetherianRing A] [Ring E] [Algebra A E] [Algebra.IsIntegral A E] [Ring F] [Algebra A F] [Fintype ι] [DecidableEq ι] (π : E →ₐ[A] F), Function.Surjective π → (∀ x, π x = 0 → x ∈ Ring.jacobson E) → ∀ f : ι → F, CompleteOrthogonalIdempotents f → ∃ e : ι → E, CompleteOrthogonalIdempotents e ∧ ∀ i, π (e i) = f i := by
  intro A E F ι _ _ _ _ _ _ _ _ _ _ _ π hs hk f hf
  obtain ⟨e', h₁, h₂⟩ := dli_fin π hs hk
    (hf.toOrthogonalIdempotents.embedding (Fintype.equivFin ι).symm.toEmbedding)
  have ho := h₁.embedding (Fintype.equivFin ι).toEmbedding
  have hv : ∀ i, π ((e' ∘ (Fintype.equivFin ι).toEmbedding) i) = f i := fun i => by
    simpa using congr_fun h₂ (Fintype.equivFin ι i)
  refine ⟨_, ⟨ho, ?_⟩, hv⟩
  have := dli_idem_zero ho.isIdempotentElem_sum.one_sub (hk _ (by

    rw [map_sub, map_one, map_sum, Finset.sum_congr rfl fun i _ => hv i, hf.complete, sub_self]))
  exact (sub_eq_zero.1 this).symm
end

section

open IsLocalRing

theorem UpperTheory.V.CA.g_ratliff :
    ∀ (P Q : Type) [CommRing P] [CommRing Q] [IsNoetherianRing P] [IsNoetherianRing Q] [Algebra P Q] [Module.Flat P Q] (n : ℕ),
      ReciprocityTheory.CA.DimFormula P → ReciprocityTheory.CA.DimFormula Q → ringKrullDim P = n → ringKrullDim Q = n →
        ∀ (q : Ideal P) [q.IsPrime], ∀ Q' ∈ (q.map (algebraMap P Q)).minimalPrimes,
          Q'.comap (algebraMap P Q) = q ∧ ringKrullDim (Q ⧸ Q') = ringKrullDim (P ⧸ q) := by
  intro P Q _ _ _ _ _ _ n hP hQ dP dQ q _ Q' hQ'
  have hprime : Q'.IsPrime := hQ'.1.1
  have hle : q.map (algebraMap P Q) ≤ Q' := hQ'.1.2
  have hle' : q ≤ Q'.under P := Ideal.map_le_iff_le_comap.mp hle
  obtain ⟨P₁, h1, h2, h3⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := q) (q := Q'.under P) Q' hle'
  have h4 : q.map (algebraMap P Q) ≤ P₁ := Ideal.map_le_iff_le_comap.mpr h3.over.le
  have h5 : P₁ = Q' := le_antisymm h1 (hQ'.2 ⟨h2, h4⟩ h1)
  subst h5
  refine ⟨h3.over.symm, ?_⟩
  have hh := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown q P₁
  have hpm : (P₁.map (Ideal.Quotient.mk (q.map (algebraMap P Q)))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using h4)
  have h0 : (P₁.map (Ideal.Quotient.mk (q.map (algebraMap P Q)))).height = 0 := by
    rw [Ideal.height_eq_zero_iff]
    have := Ideal.minimalPrimes_map_of_surjective
      (f := Ideal.Quotient.mk (q.map (algebraMap P Q))) Ideal.Quotient.mk_surjective ⊥
    rw [Ideal.map_bot, bot_sup_eq, Ideal.mk_ker] at this
    change _ ∈ (⊥ : Ideal _).minimalPrimes
    rw [this]
    exact ⟨P₁, hQ', rfl⟩
  rw [h0, add_zero] at hh
  have e1 := hP q
  have e2 := hQ P₁
  rw [dP] at e1
  rw [dQ, hh, ← e1] at e2
  have hne : q.height ≠ ⊤ := Ideal.height_ne_top (Ideal.IsPrime.ne_top inferInstance)
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hne
  rw [← hk] at e2
  generalize ringKrullDim (Q ⧸ P₁) = a at e2
  generalize ringKrullDim (P ⧸ q) = b at e2
  induction a using WithBot.recBotCoe with
  | bot =>
    induction b using WithBot.recBotCoe with
    | bot => rfl
    | coe b =>
      rw [WithBot.add_bot, ← WithBot.coe_add] at e2
      exact absurd e2 WithBot.bot_ne_coe
  | coe a =>
    induction b using WithBot.recBotCoe with
    | bot =>
      rw [WithBot.add_bot, ← WithBot.coe_add] at e2
      exact absurd e2 WithBot.coe_ne_bot
    | coe b =>
      rw [← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_inj] at e2
      rw [WithTop.add_left_cancel (ENat.coe_ne_top k) e2]
end
