module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle002
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.CmOfRegular
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle005
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
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Flat.Localization
import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim

@[expose] public section

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private theorem dim_eq_of_flat {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra A B] [Module.Flat A B]
    (hm : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    ringKrullDim B = ringKrullDim A := by
  have hl : (maximalIdeal B).LiesOver (maximalIdeal A) :=
    ⟨Ideal.IsMaximal.eq_of_le inferInstance (Ideal.comap_ne_top _ (Ideal.IsMaximal.ne_top inferInstance))
      (by rw [← hm]; exact Ideal.le_comap_map)⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal A) (maximalIdeal B)
  rw [hm, Ideal.map_quotient_self] at h
  simp at h
  rw [← maximalIdeal_height_eq_ringKrullDim, ← maximalIdeal_height_eq_ringKrullDim, h]

private theorem dim_quot_eq_of_flat {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B] [Algebra A B] [Module.Flat A B]
    (hm : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) (J : Ideal A) :
    ringKrullDim (B ⧸ J.map (algebraMap A B)) = ringKrullDim (A ⧸ J) := by
  by_cases hJ : J = ⊤
  · subst hJ
    rw [Ideal.map_top]
    rw [ringKrullDim_eq_bot_of_subsingleton, ringKrullDim_eq_bot_of_subsingleton]
  have hJm : J ≤ maximalIdeal A := IsLocalRing.le_maximalIdeal hJ
  have hIm : J.map (algebraMap A B) ≤ maximalIdeal B := hm ▸ Ideal.map_mono hJm
  have hI : J.map (algebraMap A B) ≠ ⊤ :=
    ne_top_of_le_ne_top (Ideal.IsMaximal.ne_top inferInstance) hIm
  haveI : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  haveI : Nontrivial (B ⧸ J.map (algebraMap A B)) := Ideal.Quotient.nontrivial_iff.mpr hI
  haveI : IsLocalRing (A ⧸ J) := .of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  haveI : IsLocalRing (B ⧸ J.map (algebraMap A B)) :=
    .of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  haveI : Module.Flat (A ⧸ J) (B ⧸ J.map (algebraMap A B)) := by
    have e : (B ⧸ J.map (algebraMap A B)) ≃ₗ[A] TensorProduct A (A ⧸ J) B :=
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot B J).toLinearEquiv.restrictScalars A).trans
        (TensorProduct.comm A B (A ⧸ J))
    haveI := Module.Flat.baseChange A (A ⧸ J) B
    exact Module.Flat.of_linearEquiv (LinearEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective e)
  apply dim_eq_of_flat
  have hmA : maximalIdeal (A ⧸ J) = (maximalIdeal A).map (Ideal.Quotient.mk J) :=
    (IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hJm))).symm
  have hmB : maximalIdeal (B ⧸ J.map (algebraMap A B)) =
      (maximalIdeal B).map (Ideal.Quotient.mk (J.map (algebraMap A B))) :=
    (IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hIm))).symm
  rw [hmA, hmB, Ideal.map_map, ← hm, Ideal.map_map]
  congr 1

theorem UpperTheory.V.CA.c3c :
    ∀ {C R : Type} [CommRing C] [IsNoetherianRing C] [CommRing R] [Algebra C R] [IsLocalRing R] (x : Ideal C) [x.IsMaximal], IsCplAt x R → (∀ I : Ideal C, ringKrullDim (R ⧸ I.map (algebraMap C R)) = dimAt x I) ∧ ∀ (I : Ideal C) (q : Ideal R), I ≤ q.comap (algebraMap C R) → ringKrullDim (R ⧸ q) ≤ dimAt x I := by
  intro C R _ _ _ _ _ x _ hR
  obtain ⟨_, ⟨e⟩, hmap⟩ := cpl_uniq x hR
  haveI := hR.noeth
  haveI : IsNoetherianRing (Cpl x) := isNoetherianRing_of_ringEquiv R e.toRingEquiv
  have hmapI : ∀ I : Ideal C,
      I.map (algebraMap C (Cpl x)) = (I.map (algebraMap C R)).map (e.toRingEquiv : R →+* Cpl x) := by
    intro I
    rw [Ideal.map_map]
    congr 1
    ext c
    simp
  have h1 : x.map (algebraMap C (Cpl x)) =
      (maximalIdeal (Localization.AtPrime x)).map (algebraMap (Localization.AtPrime x) (Cpl x)) := by
    rw [IsScalarTower.algebraMap_eq C (Localization.AtPrime x) (Cpl x), ← Ideal.map_map,
      Localization.AtPrime.map_eq_maximalIdeal]
  have hm : (maximalIdeal (Localization.AtPrime x)).map
      (algebraMap (Localization.AtPrime x) (Cpl x)) = maximalIdeal (Cpl x) := by
    rw [← h1, hmapI, hmap]
    exact IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv e.toRingEquiv)
  have key : ∀ I : Ideal C, ringKrullDim (R ⧸ I.map (algebraMap C R)) = dimAt x I := by
    intro I
    unfold dimAt
    rw [← dim_quot_eq_of_flat hm (I.map (algebraMap C (Localization.AtPrime x))), Ideal.map_map,
      ← IsScalarTower.algebraMap_eq]
    exact ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ e.toRingEquiv (hmapI I))
  refine ⟨key, fun I q hq => ?_⟩
  rw [← key I]
  have hle : I.map (algebraMap C R) ≤ q := Ideal.map_le_iff_le_comap.mpr hq
  exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)
end

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private theorem sop_mod (S : Type) [CommRing S] [IsLocalRing S] [IsNoetherianRing S] (J : Ideal S)
    (hle : J ≤ maximalIdeal S) :
    ∃ (n : ℕ) (x : Fin n → S), (∀ i, x i ∈ maximalIdeal S) ∧ ringKrullDim (S ⧸ J) = n ∧
      maximalIdeal S ≤ (Ideal.span (Set.range x) ⊔ J).radical := by
  have hne : J ≠ ⊤ := fun h =>
    (maximalIdeal.isMaximal S).ne_top (top_le_iff.mp (h ▸ hle))
  haveI : Nontrivial (S ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hne
  haveI : IsLocalRing (S ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  set π := Ideal.Quotient.mk J with hπ
  have hsurj : Function.Surjective π := Ideal.Quotient.mk_surjective
  haveI : IsLocalHom π := IsLocalHom.of_surjective π hsurj
  obtain ⟨s, hs, hcard⟩ :=
    Ideal.exists_finset_card_eq_height_of_isNoetherianRing (maximalIdeal (S ⧸ J))
  choose g hg using hsurj
  have hrad : maximalIdeal (S ⧸ J) ≤ (Ideal.span (s : Set (S ⧸ J))).radical := by
    rw [Ideal.radical_eq_sInf, le_sInf_iff]
    rintro J ⟨hJ, hJ'⟩
    exact hs.2 ⟨hJ', hJ⟩ (le_maximalIdeal hJ'.ne_top)
  refine ⟨s.card, fun i => g (s.equivFin.symm i), fun i => ?_, ?_, ?_⟩
  · have h1 : π (g (s.equivFin.symm i)) ∈ maximalIdeal (S ⧸ J) := by
      rw [hg]
      exact hs.1.2 (Ideal.subset_span (s.equivFin.symm i).2)
    rw [mem_maximalIdeal, mem_nonunits_iff] at h1 ⊢
    exact fun h => h1 (h.map π)
  · rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← hcard]
    rfl
  · intro y hy
    obtain ⟨N, hN⟩ := hrad (map_nonunit π y hy)
    have h2 : Ideal.span (s : Set (S ⧸ J)) ≤
        (Ideal.span (Set.range fun i => g (s.equivFin.symm i))).map π := by
      rw [Ideal.span_le]
      intro y hy
      rw [← hg y]
      refine Ideal.mem_map_of_mem π (Ideal.subset_span ⟨s.equivFin ⟨y, hy⟩, ?_⟩)
      simp
    refine ⟨N, ?_⟩
    have h3 : y ^ N ∈ ((Ideal.span (Set.range fun i => g (s.equivFin.symm i))).map π).comap π := by
      rw [Ideal.mem_comap, map_pow]
      exact h2 hN
    rwa [Ideal.comap_map_of_surjective π Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, hπ, Ideal.mk_ker] at h3

private theorem inj_of_finite {A B : Type} [CommRing A] [Nontrivial A] [NoZeroDivisors A] [CommRing B] (φ : A →+* B)
    (h : φ.Finite) (d : ℕ) (hA : ringKrullDim A = d) (hB : ringKrullDim B = d) :
    Function.Injective φ := by
  haveI : IsDomain A := NoZeroDivisors.to_isDomain A
  letI := φ.toAlgebra
  haveI : Module.Finite A B := h
  exact inj_dim A B d hA hB

private theorem nn_field (k : Type) [Field k] (R : Type) [CommRing R] [Algebra k R] [IsLocalRing R]
    (h : IsCL k R) : ∃ (d : ℕ) (φ : MvPowerSeries (Fin d) k →ₐ[k] R),
      Function.Injective φ ∧ φ.toRingHom.Finite ∧ IsLocalHom φ ∧ ringKrullDim R = d := by
  haveI := h.noeth
  obtain ⟨d, x, hx, hd, hrad⟩ := sop_mod R ⊥ bot_le
  haveI : IsAdicComplete (maximalIdeal k) k := by
    rw [maximalIdeal_eq_bot]; infer_instance
  obtain ⟨φ, -, hfin, hloc⟩ := cl_mvps k R h (Fin d) x hx
    (hrad.trans (Ideal.radical_mono (sup_le_sup_left bot_le _)))
  have hR : ringKrullDim R = d := by
    rw [← hd]; exact (ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot R)).symm
  exact ⟨d, φ, inj_of_finite φ.toRingHom hfin d (cl_cm.2 k d).2 hR, hfin, hloc, hR⟩

private theorem isCL_field (O k R : Type) [CommRing O] [Field k] [CommRing R] [IsLocalRing R]
    [Algebra O k] [Algebra O R] [Algebra k R] [IsScalarTower O k R] (h : IsCL O R) : IsCL k R := by
  have := h.res_fin
  exact ⟨h.noeth, h.complete, inferInstance,
    Module.Finite.of_restrictScalars_finite O k (ResidueField R)⟩

theorem UpperTheory.V.CA.cl_nn :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (R : Type) [CommRing R] [Algebra O R] [IsLocalRing R] [IsDomain R], IsCL O R → (Function.Injective (algebraMap O R) → ∃ (d : ℕ) (φ : MvPowerSeries (Fin d) O →ₐ[O] R), Function.Injective φ ∧ φ.toRingHom.Finite ∧ IsLocalHom φ ∧ ringKrullDim R = (d + 1 : ℕ)) ∧ (¬ Function.Injective (algebraMap O R) → ∃ (d : ℕ) (φ : MvPowerSeries (Fin d) (ResidueField O) →ₐ[O] R), Function.Injective φ ∧ φ.toRingHom.Finite ∧ IsLocalHom φ ∧ ringKrullDim R = d) := by
  intro O _ _ _ _ R _ _ _ _ h
  haveI := h.noeth
  haveI := h.isLocalHom
  refine ⟨fun hinj => ?_, fun hninj => ?_⟩
  · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    have hm : maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
    have ha : algebraMap O R ϖ ∈ maximalIdeal R := map_nonunit _ _ hϖ.not_isUnit
    have ha0 : algebraMap O R ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
    obtain ⟨d, x, hx, hd, hrad⟩ := sop_mod R (Ideal.span {algebraMap O R ϖ})
      ((Ideal.span_singleton_le_iff_mem _).2 ha)
    obtain ⟨φ, -, hfin, hloc⟩ := cl_mvps O R h (Fin d) x hx
      (by rwa [hm, Ideal.map_span, Set.image_singleton])
    have hR : ringKrullDim R = (d + 1 : ℕ) := by
      rw [← ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero ha0) ha, hd]
      rfl
    exact ⟨d, φ, inj_of_finite φ.toRingHom hfin (d + 1) (cl_cm.1 O d).2 hR, hfin, hloc, hR⟩
  · have hk0 : RingHom.ker (algebraMap O R) ≠ ⊥ := fun e =>
      hninj ((RingHom.injective_iff_ker_eq_bot _).2 e)
    have hk : RingHom.ker (algebraMap O R) = maximalIdeal O :=
      eq_maximalIdeal (Ideal.IsPrime.isMaximal (RingHom.ker_isPrime _) hk0)
    let ψ : ResidueField O →+* R := Ideal.Quotient.lift (maximalIdeal O) (algebraMap O R)
      (fun a ha => by rwa [← hk] at ha)
    letI : Algebra (ResidueField O) R := ψ.toAlgebra
    haveI : IsScalarTower O (ResidueField O) R := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have h' : IsCL (ResidueField O) R := isCL_field O (ResidueField O) R h
    obtain ⟨d, φ, h1, h2, h3, h4⟩ := nn_field (ResidueField O) R h'
    exact ⟨d, φ.restrictScalars O, h1, h2, ⟨fun a ha => h3.1 a ha⟩, h4⟩
end

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

theorem UpperTheory.V.CA.c3a :
    ∀ {C R : Type} [CommRing C] [IsNoetherianRing C] [CommRing R] [Algebra C R] [IsLocalRing R] (x : Ideal C) [x.IsMaximal], IsCplAt x R → Module.Flat C R ∧ (∀ p : Ideal C, p.IsPrime → p ≤ x → ∃ q : Ideal R, q.IsPrime ∧ q.comap (algebraMap C R) = p) ∧ (∀ q : Ideal R, q.IsPrime → q.comap (algebraMap C R) ≤ x) ∧ (∀ q ∈ minimalPrimes R, q.comap (algebraMap C R) ∈ minimalPrimes C) ∧ ∀ (I : Ideal C), ∀ q ∈ (I.map (algebraMap C R)).minimalPrimes, q.comap (algebraMap C R) ∈ I.minimalPrimes := by
  intro C R _ _ _ _ _ x _ h
  obtain ⟨-, ⟨e⟩, -⟩ := UpperTheory.V.CA.cpl_uniq x h
  have hflat : Module.Flat C R := by
    have h1 : Module.Flat (Localization.AtPrime x) (Cpl x) := inferInstance
    have h2 : Module.Flat C (Localization.AtPrime x) := IsLocalization.flat _ x.primeCompl
    have h3 : Module.Flat C (Cpl x) := Module.Flat.trans C (Localization.AtPrime x) (Cpl x)
    exact Module.Flat.of_linearEquiv e.toLinearEquiv
  have hx : (maximalIdeal R).comap (algebraMap C R) = x := by simpa using h.comap_pow 1
  have gd : ∀ (p : Ideal C) (q : Ideal R), p.IsPrime → q.IsPrime → p ≤ q.comap (algebraMap C R) →
      ∃ Q : Ideal R, Q ≤ q ∧ Q.IsPrime ∧ Q.comap (algebraMap C R) = p := by
    intro p q hp hq hle
    haveI : q.LiesOver (q.comap (algebraMap C R)) := ⟨rfl⟩
    obtain ⟨Q, hQ, hQp, hQo⟩ := Ideal.exists_ideal_le_liesOver_of_le q hle
    exact ⟨Q, hQ, hQp, hQo.over.symm⟩
  have hmin : ∀ (I : Ideal C), ∀ q ∈ (I.map (algebraMap C R)).minimalPrimes,
      q.comap (algebraMap C R) ∈ I.minimalPrimes := by
    intro I q hq
    haveI : q.IsPrime := hq.1.1
    refine ⟨⟨Ideal.comap_isPrime _ _, Ideal.map_le_iff_le_comap.1 hq.1.2⟩, ?_⟩
    rintro p ⟨hp, hIp⟩ hle
    obtain ⟨Q, hQ, hQp, hQo⟩ := gd p q hp this hle
    have : q ≤ Q := hq.2 ⟨hQp, Ideal.map_le_iff_le_comap.2 (hQo ▸ hIp)⟩ hQ
    rw [← hQo]
    exact Ideal.comap_mono this
  refine ⟨hflat, ?_, ?_, ?_, hmin⟩
  · intro p hp hle
    obtain ⟨Q, -, hQp, hQo⟩ := gd p (maximalIdeal R) hp inferInstance (hx.symm ▸ hle)
    exact ⟨Q, hQp, hQo⟩
  · intro q hq
    rw [← hx]
    exact Ideal.comap_mono (le_maximalIdeal hq.ne_top)
  · intro q hq
    apply hmin ⊥ q
    rw [Ideal.map_bot]
    exact hq
end
