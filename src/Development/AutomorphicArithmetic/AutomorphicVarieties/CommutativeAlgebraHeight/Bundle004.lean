module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle002
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
public import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.RingTheory.Ideal.GoingUp
import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim

@[expose] public section

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private theorem maximalIdeal_map_eq_of_surjective {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    (f : R →+* R') (hf : Function.Surjective f) : (maximalIdeal R).map f = maximalIdeal R' := by
  have hk : RingHom.ker f ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top f)
  rcases Ideal.map_eq_top_or_isMaximal_of_surjective (f := f) hf (I := maximalIdeal R)
      (maximalIdeal.isMaximal R) with h | h
  · exfalso
    have h1 : (1 : R') ∈ (maximalIdeal R).map f := h ▸ Submodule.mem_top
    obtain ⟨y, hy, hy1⟩ := (Ideal.mem_map_iff_of_surjective f hf).1 h1
    have hker : 1 - y ∈ RingHom.ker f := by simp [RingHom.mem_ker, hy1]
    have h2 := Ideal.add_mem _ (hk hker) hy
    rw [sub_add_cancel] at h2
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 h2)
  · exact IsLocalRing.eq_maximalIdeal h

private theorem isLocalHom_of_surjective {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    (f : R →+* R') (hf : Function.Surjective f) : IsLocalHom f := by
  refine ⟨fun x hx => ?_⟩
  by_contra h
  have hx' : x ∈ maximalIdeal R := h
  have : f x ∈ maximalIdeal R' := by
    rw [← maximalIdeal_map_eq_of_surjective f hf]
    exact Ideal.mem_map_of_mem f hx'
  exact this hx

private theorem smodEq_ideal_pow_smul_univ_iff_sub_mem {A : Type} [CommRing A] (I : Ideal A) (n : ℕ) (a b : A) :
    a ≡ b [SMOD (I ^ n • ⊤ : Submodule A A)] ↔ a - b ∈ I ^ n := by
  simp [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

theorem UpperTheory.V.CA.cl_quot :
    ∀ (O : Type) [CommRing O] (R : Type) [CommRing R] [Algebra O R] [IsLocalRing R] (R' : Type) [CommRing R'] [Algebra O R'] [IsLocalRing R'] (p : R →ₐ[O] R'), Function.Surjective p → IsCL O R → IsCL O R' := by
  intro O _ R _ _ _ R' _ _ _ p hp hR
  have hpr : Function.Surjective (p : R →+* R') := hp
  haveI : IsLocalHom (p : R →+* R') := isLocalHom_of_surjective _ hpr
  haveI := hR.noeth
  haveI : IsNoetherianRing R' := isNoetherianRing_of_surjective R R' (p : R →+* R') hpr
  haveI := hR.complete
  have hm : maximalIdeal R' = (maximalIdeal R).map (p : R →+* R') := (maximalIdeal_map_eq_of_surjective _ hpr).symm
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · haveI : IsHausdorff (maximalIdeal R') R' := inferInstance
    refine { toIsHausdorff := inferInstance, toIsPrecomplete := ⟨fun f hf => ?_⟩ }
    have hd : ∀ n, ∃ d ∈ maximalIdeal R ^ n, p d = f (n + 1) - f n := by
      intro n
      have h0 := (smodEq_ideal_pow_smul_univ_iff_sub_mem _ _ _ _).1 (hf (Nat.le_succ n))
      rw [hm, ← Ideal.map_pow] at h0
      obtain ⟨d, hd, hd'⟩ := (Ideal.mem_map_iff_of_surjective _ hpr).1 (neg_mem h0)
      refine ⟨d, hd, ?_⟩
      rw [neg_sub] at hd'
      exact hd'
    choose d hdm hdp using hd
    obtain ⟨y0, hy0⟩ := hp (f 0)
    have hy : ∀ n, p (y0 + ∑ k ∈ Finset.range n, d k) = f n := by
      intro n
      induction n with
      | zero => simp [hy0]
      | succ n ih =>
        rw [Finset.sum_range_succ, ← add_assoc, map_add (f := _), ih, hdp]
        ring
    have hcauchy : ∀ {m n : ℕ}, m ≤ n →
        (y0 + ∑ k ∈ Finset.range m, d k) ≡ (y0 + ∑ k ∈ Finset.range n, d k)
          [SMOD (maximalIdeal R ^ m • ⊤ : Submodule R R)] := by
      intro m n hmn
      rw [smodEq_ideal_pow_smul_univ_iff_sub_mem]
      induction n, hmn using Nat.le_induction with
      | base => simp
      | succ n hmn ih =>
        have e : (y0 + ∑ k ∈ Finset.range m, d k) - (y0 + ∑ k ∈ Finset.range (n + 1), d k) =
            ((y0 + ∑ k ∈ Finset.range m, d k) - (y0 + ∑ k ∈ Finset.range n, d k)) - d n := by
          rw [Finset.sum_range_succ]
          ring
        rw [e]
        exact Ideal.sub_mem _ ih (Ideal.pow_le_pow_right hmn (hdm n))
    obtain ⟨L, hL⟩ := (inferInstance : IsPrecomplete (maximalIdeal R) R).prec'
      (fun n => y0 + ∑ k ∈ Finset.range n, d k) hcauchy
    refine ⟨p L, fun n => ?_⟩
    rw [smodEq_ideal_pow_smul_univ_iff_sub_mem, hm, ← Ideal.map_pow, ← hy n, ← map_sub]
    exact Ideal.mem_map_of_mem (p : R →+* R') ((smodEq_ideal_pow_smul_univ_iff_sub_mem _ _ _ _).1 (hL n))
  · refine ⟨fun x hx => ?_⟩
    have e : algebraMap O R' x = (p : R →+* R') (algebraMap O R x) := (p.commutes x).symm
    rw [e] at hx
    exact hR.isLocalHom.map_nonunit _ (IsLocalHom.map_nonunit _ hx)
  · let L : ResidueField R →ₗ[O] ResidueField R' :=
      { toFun := IsLocalRing.ResidueField.map (p : R →+* R')
        map_add' := map_add _
        map_smul' := by
          intro o x
          obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
          simp only [Algebra.smul_def, map_mul, RingHom.id_apply]
          congr 1
          rw [IsScalarTower.algebraMap_apply O R (ResidueField R),
            IsScalarTower.algebraMap_apply O R' (ResidueField R')]
          change IsLocalRing.ResidueField.map _ (residue R _) = residue R' _
          rw [IsLocalRing.ResidueField.map_residue]
          simp }
    have hL : Function.Surjective L := by
      intro z
      obtain ⟨y', rfl⟩ := IsLocalRing.residue_surjective z
      obtain ⟨y, rfl⟩ := hpr y'
      exact ⟨IsLocalRing.residue R y, IsLocalRing.ResidueField.map_residue _ _⟩
    haveI := hR.res_fin
    exact Module.Finite.of_surjective L hL
end

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

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
  refine ⟨fun f hf => ?_⟩
  have key : ∀ i, ∃ L : R, ∀ n, f n i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := fun i =>
    IsPrecomplete.prec' (I := I) (fun n => f n i) fun {m n} hmn => by
      have h := hf hmn
      rw [SModEq.sub_mem, mem_smul_top_pi] at h
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      exact h i
  choose L hL using key
  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem, mem_smul_top_pi]
  intro i
  have h := hL i n
  rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h

private theorem isPrecomplete_finite {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) [IsPrecomplete I R] : IsPrecomplete I M := by
  obtain ⟨r, π, hπ⟩ := Module.Finite.exists_fin' R M
  haveI := isPrecomplete_pi I r
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨z, rfl⟩ := AdicCompletion.map_surjective I hπ y
  obtain ⟨w, rfl⟩ := AdicCompletion.of_surjective I (Fin r → R) z
  exact ⟨π w, (AdicCompletion.map_of I π w).symm⟩

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

theorem UpperTheory.V.CA.cl_fin :
    ∀ (O : Type) [CommRing O] (R : Type) [CommRing R] [Algebra O R] [IsLocalRing R] (R' : Type) [CommRing R'] [Algebra O R'] [IsLocalRing R'] [Algebra R R'] [IsScalarTower O R R'] [Module.Finite R R'], IsCL O R → IsCL O R' := by
  intro O _ R _ _ _ R' _ _ _ _ _ _ h
  haveI := h.noeth
  haveI := h.complete
  haveI := h.isLocalHom
  haveI := h.res_fin
  haveI hN : IsNoetherianRing R' := IsNoetherianRing.of_finite R R'
  have hIntegral : (algebraMap R R').IsIntegral :=
    RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)
  have hcomap : (maximalIdeal R').comap (algebraMap R R') = maximalIdeal R :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
      (algebraMap R R') hIntegral (maximalIdeal R'))
  have hle : (maximalIdeal R).map (algebraMap R R') ≤ maximalIdeal R' :=
    Ideal.map_le_iff_le_comap.2 hcomap.ge
  have hrad : maximalIdeal R' ≤ ((maximalIdeal R).map (algebraMap R R')).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun P hP => ?_
    obtain ⟨h1, h2⟩ := hP
    have h3 : P.comap (algebraMap R R') = maximalIdeal R :=
      ((maximalIdeal.isMaximal R).eq_of_le (Ideal.comap_ne_top _ h2.ne_top)
        (Ideal.map_le_iff_le_comap.1 h1)).symm
    have h4 : P.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap R R') hIntegral P
        (h3 ▸ maximalIdeal.isMaximal R)
    exact (eq_maximalIdeal h4).ge
  obtain ⟨e, he⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  have hP : IsPrecomplete (maximalIdeal R') R' :=
    prec_cofinal hle he (IsPrecomplete.map_algebraMap_iff.2 (isPrecomplete_finite _))
  haveI hloc : IsLocalHom (algebraMap R R') := ⟨fun a ha => by
    by_contra hn
    have h1 : a ∈ maximalIdeal R := hn
    rw [← hcomap, Ideal.mem_comap] at h1
    exact h1 ha⟩
  haveI hT : IsScalarTower O (ResidueField R) (ResidueField R') :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [IsScalarTower.algebraMap_apply O R (ResidueField R),
        ← IsScalarTower.algebraMap_apply R (ResidueField R) (ResidueField R'),
        IsScalarTower.algebraMap_apply O R' (ResidueField R'),
        IsScalarTower.algebraMap_apply R R' (ResidueField R'),
        IsScalarTower.algebraMap_apply O R R']
  exact
    { noeth := hN
      complete := { toIsHausdorff := inferInstance, toIsPrecomplete := hP }
      isLocalHom := by
        rw [IsScalarTower.algebraMap_eq O R R']
        infer_instance
      res_fin := Module.Finite.trans (ResidueField R) (ResidueField R') }
end

section

open IsLocalRing

private theorem UpperTheory.V.CA.detps_height {A : Type} [CommRing A] [IsNoetherianRing A] (n : ℕ)
    (M : Fin (n + 1) → Fin (n + 1) → A) (v : Fin (n + 1) → A) (I : Ideal A)
    (hI : I = Ideal.span (Set.range (fun a => ∑ b, M a b * v b) ∪ {Matrix.det (Matrix.of M)}))
    (hp : I.radical.IsPrime) (hv : v 0 ∉ I.radical) : I.radical.height ≤ (n + 1 : ℕ) := by
  classical
  have hJI : Ideal.span (Set.range (fun a => ∑ b, M a b * v b)) ≤ I := by
    rw [hI]
    exact Ideal.span_mono Set.subset_union_left
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le (hJI.trans I.le_radical)
  have hQprime : Q.IsPrime := hQ.1.1
  have key : Matrix.mulVec (Matrix.adjugate (Matrix.of M)) (Matrix.mulVec (Matrix.of M) v) 0
      = Matrix.det (Matrix.of M) * v 0 := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    simp
  have hdv : Matrix.det (Matrix.of M) * v 0 ∈ Q := by
    rw [← key]
    apply hQ.1.2
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    refine Ideal.sum_mem _ fun b _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨b, rfl⟩)
  have hdet : Matrix.det (Matrix.of M) ∈ Q := by
    rcases hQprime.mem_or_mem hdv with h | h
    · exact h
    · exact absurd (hQP h) hv
  have hIQ : I ≤ Q := by
    rw [hI, Ideal.span_le]
    rintro x (⟨a, rfl⟩ | hx)
    · exact hQ.1.2 (Ideal.subset_span ⟨a, rfl⟩)
    · rw [Set.mem_singleton_iff.mp hx]
      exact hdet
  have hPQ : I.radical = Q :=
    le_antisymm (by rw [← hQprime.radical]; exact Ideal.radical_mono hIQ) hQP
  rw [hPQ]
  have hQ' : Q ∈ (Ideal.span ((Finset.univ.image fun a => ∑ b, M a b * v b : Finset A) :
      Set A)).minimalPrimes := by
    simpa using hQ
  refine (Ideal.height_le_card_of_mem_minimalPrimes_span_finset hQ').trans ?_
  exact_mod_cast Finset.card_image_le.trans (by simp)

theorem UpperTheory.V.CA.g_detps :
    (∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (n : ℕ),
      let A := MvPowerSeries ((Fin (n + 1) × Fin (n + 1)) ⊕ Fin (n + 1)) R
      let I : Ideal A := Ideal.span (Set.range (fun a : Fin (n + 1) => ∑ b : Fin (n + 1), (MvPowerSeries.X (Sum.inl (a, b)) * MvPowerSeries.X (Sum.inr b) : A)) ∪ {Matrix.det (Matrix.of fun a b : Fin (n + 1) => (MvPowerSeries.X (Sum.inl (a, b)) : A))})
      I.radical.IsPrime ∧ I.radical.height ≤ (n + 1 : ℕ)) := by
  intro R _ _ _ n A I
  classical
  have hd := UpperTheory.V.CA.g_detrad R n
  simp only at hd
  obtain ⟨hP, hX0, -, hhom⟩ := hd
  set Ip : Ideal (MvPolynomial ((Fin (n + 1) × Fin (n + 1)) ⊕ Fin (n + 1)) R) :=
    Ideal.span (Set.range (fun a : Fin (n + 1) => ∑ b : Fin (n + 1),
      MvPolynomial.X (Sum.inl (a, b)) * MvPolynomial.X (Sum.inr b)) ∪
      {Matrix.det (Matrix.of fun a b : Fin (n + 1) => MvPolynomial.X (Sum.inl (a, b)))}) with hIp
  set φ := (MvPolynomial.coeToMvPowerSeries.ringHom :
    MvPolynomial ((Fin (n + 1) × Fin (n + 1)) ⊕ Fin (n + 1)) R →+* A) with hφ
  have hmap : Ideal.map φ Ip = I := by
    rw [hIp, Ideal.map_span, Set.image_union, Set.image_singleton, ← Set.range_comp]
    congr 3
    · funext a

      simp [φ, map_sum]
    · rw [RingHom.map_det]
      congr 1
      ext a b
      simp [φ]
  obtain ⟨hmp, hcomap⟩ := UpperTheory.V.CA.g_homprime R _ Ip.radical hP hhom
  have hrad : I.radical = Ideal.map φ Ip.radical := by
    apply le_antisymm
    · rw [← hmp.radical]
      apply Ideal.radical_mono
      rw [← hmap]
      exact Ideal.map_mono Ip.le_radical
    · rw [← hmap]
      exact Ideal.map_radical_le φ
  have hIprime : I.radical.IsPrime := by
    rw [hrad]
    exact hmp
  refine ⟨hIprime, ?_⟩
  refine UpperTheory.V.CA.detps_height n (fun a b => (MvPowerSeries.X (Sum.inl (a, b)) : A))
    (fun b => (MvPowerSeries.X (Sum.inr b) : A)) I rfl hIprime ?_
  rw [hrad]
  intro h
  apply hX0
  rw [← hcomap, Ideal.mem_comap]
  simpa [φ] using h
end
