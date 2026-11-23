module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Mathlib.RingTheory.Valuation.LocalSubring
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.LocalRing.LocalSubring
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

namespace UpperTheory.Gal.crystallineComparison

private theorem val_map_sum {α P : Type} (s : Finset α) (f : α → P) :
    s.val.map f = ∑ x ∈ s, ({f x} : Multiset P) := by
  rw [Finset.sum_eq_multiset_sum]
  have h := Multiset.sum_map_singleton (s.val.map f)
  rw [Multiset.map_map] at h
  exact h.symm

open Classical in
private theorem partIn (hIn : CountIn) {k H P : Type} [Field k] [AddCommGroup H] [Module k H]
    [Module.Finite k H] (C : Submodule k H) (hC : Module.finrank k C = 1)
    [Fintype (Submodule k H)] [Fintype (Submodule k (H ⧸ C))]
    (g : Submodule k (H ⧸ C) → Multiset P) (j : ℕ) :
    ∑ D ∈ (Finset.univ.filter fun D : Submodule k H => Module.finrank k D = j + 1).filter
        (fun D => C ≤ D), g (D.map C.mkQ)
      = ∑ E ∈ Finset.univ.filter (fun E : Submodule k (H ⧸ C) => Module.finrank k E = j), g E := by
  obtain ⟨hbij, hrk, -⟩ := hIn k H C hC
  refine Finset.sum_bij (fun D _ => D.map C.mkQ) ?_ ?_ ?_ ?_
  · intro D hD
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hD ⊢
    have := hrk D hD.2
    omega
  · intro D₁ h₁ D₂ h₂ he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
    exact Subtype.ext_iff.mp (@hbij.1 ⟨D₁, h₁.2⟩ ⟨D₂, h₂.2⟩ he)
  · intro E hE
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hE
    obtain ⟨⟨D, hD⟩, hDE⟩ := hbij.2 E
    refine ⟨D, ?_, hDE⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, hD⟩
    have := hrk D hD
    simp only at hDE
    rw [hDE] at this
    omega
  · intro D hD
    rfl

open Classical in
private theorem partZero (hIn : CountIn) {k H : Type} [Field k] [AddCommGroup H] [Module k H]
    [Module.Finite k H] (C : Submodule k H) (hC : Module.finrank k C = 1)
    [Fintype (Submodule k H)] :
    (Finset.univ.filter fun D : Submodule k H => Module.finrank k D = 0).filter
        (fun D => C ≤ D) = ∅ := by
  ext D
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_and]
  intro hD hCD
  have := Submodule.finrank_mono hCD
  omega

open Classical in
private theorem partOut (hIn : CountIn) (hOut : CountOut) {k H P : Type} [Field k] [Finite k]
    [AddCommGroup H] [Module k H] [Module.Finite k H] (C : Submodule k H)
    (hC : Module.finrank k C = 1)
    [Fintype (Submodule k H)] [Fintype (Submodule k (H ⧸ C))]
    (g : Submodule k (H ⧸ C) → Multiset P) (j : ℕ) :
    ∑ D ∈ (Finset.univ.filter fun D : Submodule k H => Module.finrank k D = j).filter
        (fun D => ¬ C ≤ D), g (D.map C.mkQ)
      = Nat.card k ^ j •
        ∑ E ∈ Finset.univ.filter (fun E : Submodule k (H ⧸ C) => Module.finrank k E = j), g E := by
  obtain ⟨-, -, hrk⟩ := hIn k H C hC
  have hmaps : ∀ D ∈ (Finset.univ.filter fun D : Submodule k H => Module.finrank k D = j).filter
      (fun D => ¬ C ≤ D), D.map C.mkQ ∈
        Finset.univ.filter (fun E : Submodule k (H ⧸ C) => Module.finrank k E = j) := by
    intro D hD
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hD ⊢
    rw [← hrk D hD.2]
    exact hD.1
  rw [Finset.smul_sum, ← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl ?_
  intro E hE
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hE
  rw [Finset.sum_congr rfl (g := fun _ => g E) (fun D hD => by rw [(Finset.mem_filter.mp hD).2])]
  rw [Finset.sum_const]
  congr 1
  have hc : Nat.card k ^ j = Nat.card { D // ¬C ≤ D ∧ Submodule.map C.mkQ D = E } := by
    rw [hOut k H C hC E, hE]
  rw [hc, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext D
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨-, h2⟩, h3⟩
    exact ⟨h2, h3⟩
  · rintro ⟨h2, h3⟩
    refine ⟨⟨?_, h2⟩, h3⟩
    rw [hrk D h2, h3, hE]

end UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.ordDecomp_of :
    CountIn → CountOut → OrdDecomp := by
  intro hIn hOut q n P F I _ v hv
  obtain ⟨k, H, _, _, _, _, _, C, A', e, hq, hn, hC, hve⟩ := hv
  classical
  haveI : Finite H := Module.finite_of_finite k
  haveI : Finite (Submodule k H) :=
    Finite.of_injective (fun S : Submodule k H => (S : Set H)) SetLike.coe_injective
  haveI : Finite (H ⧸ C) := Module.finite_of_finite k
  haveI : Finite (Submodule k (H ⧸ C)) :=
    Finite.of_injective (fun S : Submodule k (H ⧸ C) => (S : Set (H ⧸ C))) SetLike.coe_injective
  letI : Fintype (Submodule k H) := Fintype.ofFinite _
  letI : Fintype (Submodule k (H ⧸ C)) := Fintype.ofFinite _
  letI hG : ∀ m : ℕ, Fintype (Gr k H m) := fun m =>
    (inferInstance : Fintype {D : Submodule k H // Module.finrank k D = m})
  have key : ∀ j : Fin (n + 1), Multiset.map (v j) Finset.univ.val =
      ∑ D ∈ (Finset.univ.filter fun D : Submodule k H => Module.finrank k D = (j : ℕ)).filter
        (fun D => C ≤ D), ({F (A' (D.map C.mkQ))} : Multiset P) +
      ∑ D ∈ (Finset.univ.filter fun D : Submodule k H => Module.finrank k D = (j : ℕ)).filter
        (fun D => ¬ C ≤ D), ({A' (D.map C.mkQ)} : Multiset P) := by
    intro j
    rw [← Finset.sum_ite]
    rw [val_map_sum, ← Equiv.sum_comp (e j).symm]
    rw [Finset.sum_subtype (F := hG j)
      (Finset.univ.filter fun D : Submodule k H => Module.finrank k D = (j : ℕ))
      (p := fun D : Submodule k H => Module.finrank k D = (j : ℕ)) (by simp)]
    refine Finset.sum_congr rfl ?_
    intro D _
    have h := hve j ((e j).symm D)
    rw [Equiv.apply_symm_apply] at h
    by_cases hCD : C ≤ D.1
    · rw [h.1 hCD]
      simp [hCD]
    · rw [h.2 hCD]
      simp [hCD]
  refine ⟨fun j => ∑ E ∈ Finset.univ.filter (fun E : Submodule k (H ⧸ C) => Module.finrank k E = j),
    ({A' E} : Multiset P), ?_, ?_, ?_⟩
  · apply Finset.sum_eq_zero
    intro E hE
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hE
    exfalso
    have h1 := Submodule.finrank_le E
    have h2 := Submodule.finrank_quotient_add_finrank C
    omega
  · rw [key 0]
    simp only [Fin.val_zero]
    have h0 := partZero hIn C hC
    have h1 := partOut hIn hOut C hC (fun E => ({A' E} : Multiset P)) 0
    simp only [pow_zero, one_smul] at h1
    convert congrArg₂ (· + ·) (congrArg (fun s => ∑ D ∈ s, ({F (A' (D.map C.mkQ))} : Multiset P)) h0) h1
    all_goals first
      | rfl
      | simp
      | (ext x; simp)
  · intro j
    rw [key j.succ]
    simp only [Fin.val_succ]
    have h2 := partIn hIn C hC (fun E => ({F (A' E)} : Multiset P)) j
    have h3 := partOut hIn hOut C hC (fun E => ({A' E} : Multiset P)) (j + 1)
    rw [hq] at h3
    have h4 : ∑ E ∈ Finset.univ.filter (fun E : Submodule k (H ⧸ C) => Module.finrank k E = j),
        ({F (A' E)} : Multiset P) = Multiset.map F
          (∑ E ∈ Finset.univ.filter (fun E : Submodule k (H ⧸ C) => Module.finrank k E = j),
            ({A' E} : Multiset P)) := by
      rw [← val_map_sum, ← val_map_sum, Multiset.map_map]
      rfl
    rw [← h4]
    convert congrArg₂ (· + ·) h2 h3
    all_goals first
      | rfl
      | simp
      | (ext x; simp)
end

section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.countIn_of :
    CountIn := by
  intro k H _ _ _ _ C hC
  have key : ∀ D : Submodule k H, Module.finrank k D
      = Module.finrank k (Submodule.map C.mkQ D) + Module.finrank k ↥(D ⊓ C) := by
    intro D
    have h := (C.mkQ.domRestrict D).finrank_range_add_finrank_ker
    rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ] at h
    rw [← h, ← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rintro ⟨D₁, h₁⟩ ⟨D₂, h₂⟩ h
    simp only at h
    have e₁ := Submodule.comap_map_mkQ C D₁
    have e₂ := Submodule.comap_map_mkQ C D₂
    rw [h, e₂, sup_eq_right.mpr h₂] at e₁
    rw [sup_eq_right.mpr h₁] at e₁
    exact Subtype.ext e₁.symm
  · intro E
    refine ⟨⟨Submodule.comap C.mkQ E, ?_⟩, ?_⟩
    · intro x hx
      simp [Submodule.mem_comap, (Submodule.Quotient.mk_eq_zero C).mpr hx]
    · exact Submodule.map_comap_eq_self (by simp [Submodule.range_mkQ])
  · intro D hD
    rw [key D, inf_eq_right.mpr hD, hC]
  · intro D hD
    have hle : Module.finrank k ↥(D ⊓ C) ≤ 1 := hC ▸ Submodule.finrank_mono inf_le_right
    have hne : Module.finrank k ↥(D ⊓ C) ≠ 1 := by
      intro h1
      apply hD
      have := Submodule.eq_of_le_of_finrank_eq (inf_le_right : D ⊓ C ≤ C) (h1.trans hC.symm)
      exact this ▸ inf_le_left
    rw [key D]
    omega
end

section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.gaussLin_of :
    GaussLin := by
  intro A ι _ c s hs hc
  by_contra hc0
  have hmem : ∀ a : A, a ∈ (Submodule.span A {c}).annihilator ↔ a * c = 0 := by
    intro a
    rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul]
  have hIt : (Submodule.span A {c}).annihilator ≠ ⊤ := by
    intro h
    have h1 : (1:A) ∈ (Submodule.span A {c}).annihilator := by
      rw [h]; exact Submodule.mem_top
    rw [hmem, one_mul] at h1
    exact hc0 h1
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal _ hIt
  haveI := hM
  letI := Ideal.Quotient.field M
  have hprod : MvPolynomial.map (Ideal.Quotient.mk M) s.prod = 0 := by
    ext m
    change (MvPolynomial.map (Ideal.Quotient.mk M) s.prod).coeff m = 0
    rw [MvPolynomial.coeff_map, Ideal.Quotient.eq_zero_iff_mem]
    apply hIM
    rw [hmem, mul_comm, ← MvPolynomial.coeff_C_mul, hc]
    rfl
  rw [map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hprod
  obtain ⟨p, hp, hp0⟩ := hprod
  obtain ⟨m, hm⟩ := hs p hp
  have h2 := congrArg (AddMonoidAlgebra.coeff · m) hp0
  rw [MvPolynomial.coeff_map, hm, map_one, MvPolynomial.coeff_zero] at h2
  exact one_ne_zero h2
end

section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

private def baseChangePts {R A S K : Type} [CommRing R] [CommRing A] [CommRing S] [CommRing K]
    [Algebra R A] [Algebra R S] [Algebra A K] [Algebra R K] [IsScalarTower R A K] :
    (A ⊗[R] S →ₐ[A] K) ≃ (S →ₐ[R] K) where
  toFun f := (f.restrictScalars R).comp Algebra.TensorProduct.includeRight
  invFun g := Algebra.TensorProduct.lift (Algebra.ofId A K) g fun _ _ => Commute.all _ _
  left_inv f := by
    apply Algebra.TensorProduct.ext
    · ext
    · ext s
      simp [Algebra.ofId_apply]
  right_inv g := by
    ext s
    simp [Algebra.ofId_apply]

theorem UpperTheory.Gal.crystallineComparison.injSplit_of :
    RankOfDeg → SplitsOfEquiv → InjSplit := by
  intro hRank hSplitEq l d R S _ _ _ hE
  haveI := hE.fin
  haveI := hE.et
  have hdeg : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (Localization.Away (l : R)) K],
      Nat.card (Localization.Away (l : R) ⊗[R] S →ₐ[Localization.Away (l : R)] K) = d := by
    intro K _ _ _
    letI : Algebra R K := ((algebraMap (Localization.Away (l : R)) K).comp
      (algebraMap R (Localization.Away (l : R)))).toAlgebra
    haveI : IsScalarTower R (Localization.Away (l : R)) K := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hl : (l : K) ≠ 0 := by
      have hu : IsUnit (algebraMap R (Localization.Away (l : R)) (l : R)) :=
        IsLocalization.Away.algebraMap_isUnit (l : R)
      have hu' := hu.map (algebraMap (Localization.Away (l : R)) K)
      simpa using hu'.ne_zero
    rw [Nat.card_congr baseChangePts]
    exact hE.deg K hl
  have hn := hRank (Localization.Away (l : R)) (Localization.Away (l : R) ⊗[R] S) d hdeg
  obtain ⟨T, _, _, _, _, _, hT⟩ := Algebra.IsFiniteSplit.exists_tensorProduct_of_etale hn
  obtain ⟨n, ⟨e⟩⟩ := hT.nonempty_algEquiv_fun
  obtain ⟨z, hz⟩ := hSplitEq (Localization.Away (l : R)) (Localization.Away (l : R) ⊗[R] S) T (Fin n) e
  exact ⟨T, inferInstance, inferInstance, n, z,
    FaithfulSMul.algebraMap_injective (Localization.Away (l : R)) T, hz⟩
end

section

noncomputable section

namespace UpperTheory.Gal.crystallineComparison

theorem valLift_of : ValLift := by
  intro R _ l hl 𝔭 _
  classical
  obtain ⟨q, hq, hq𝔭⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) (J := 𝔭) bot_le
  have hlq : l ∉ q := fun h =>
    Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hq) h hl
  haveI : q.IsPrime := hq.1.1
  let K := AlgebraicClosure (FractionRing (R ⧸ q))
  let ι : R →+* K := (algebraMap (FractionRing (R ⧸ q)) K).comp
    ((algebraMap (R ⧸ q) (FractionRing (R ⧸ q))).comp (Ideal.Quotient.mk q))
  have hι : ∀ r, ι r = 0 ↔ r ∈ q := by
    intro r
    constructor
    · intro h
      have h1 : algebraMap (R ⧸ q) (FractionRing (R ⧸ q)) (Ideal.Quotient.mk q r) = 0 :=
        (map_eq_zero (algebraMap (FractionRing (R ⧸ q)) K)).mp h
      exact Ideal.Quotient.eq_zero_iff_mem.mp (IsFractionRing.to_map_eq_zero_iff.mp h1)
    · intro h
      simp [ι, Ideal.Quotient.eq_zero_iff_mem.mpr h]
  have hunit : ∀ s : 𝔭.primeCompl, IsUnit (ι s) := fun s =>
    isUnit_iff_ne_zero.mpr (fun h => s.2 (hq𝔭 ((hι s).mp h)))
  let φ : Localization.AtPrime 𝔭 →+* K := IsLocalization.lift (M := 𝔭.primeCompl) hunit
  have hφ : ∀ r, φ (algebraMap R _ r) = ι r := fun r => IsLocalization.lift_eq hunit r
  obtain ⟨B, hsub, hloc⟩ := (LocalSubring.range φ).exists_le_valuationSubring
  have hmemL : ∀ x, φ x ∈ (LocalSubring.range φ).toSubring := fun x => by
    rw [LocalSubring.range_toSubring]; exact ⟨x, rfl⟩
  let ψ' : Localization.AtPrime 𝔭 →+* B := φ.codRestrict B (fun x => hsub (hmemL x))
  let ψ : R →+* B := ψ'.comp (algebraMap R (Localization.AtPrime 𝔭))
  have hψ : ∀ r, (ψ r : K) = ι r := fun r => hφ r
  haveI : IsAlgClosed (FractionRing B) :=
    IsAlgClosed.of_ringEquiv K _ (FractionRing.algEquiv B K).symm.toRingEquiv
  refine ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, ψ.toAlgebra, ?_, ?_⟩
  · intro h
    change ψ l = 0 at h
    apply hlq
    rw [← hι, ← hψ, h, ZeroMemClass.coe_zero]
  · ext r
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    change ¬ IsUnit (ψ r) ↔ r ∈ 𝔭
    constructor
    · intro h
      by_contra hr
      exact h ((IsLocalization.map_units (Localization.AtPrime 𝔭) (⟨r, hr⟩ : 𝔭.primeCompl)).map ψ')
    · intro hr hu
      have hxm : algebraMap R (Localization.AtPrime 𝔭) r ∈ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) :=
        (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔭) 𝔭 r).mpr hr
      let y : (LocalSubring.range φ).toSubring :=
        ⟨φ (algebraMap R (Localization.AtPrime 𝔭) r), hmemL _⟩
      have hy : IsUnit y := hloc.map_nonunit y hu
      obtain ⟨z, hz⟩ := isUnit_iff_exists_inv.mp hy
      obtain ⟨w, hw⟩ : ∃ w, φ w = z := (LocalSubring.range_toSubring φ).le z.2
      have h1 : φ (algebraMap R (Localization.AtPrime 𝔭) r) * (z : K) = 1 := congrArg Subtype.val hz
      have hker : algebraMap R (Localization.AtPrime 𝔭) r * w - 1 ∈ RingHom.ker φ := by
        rw [RingHom.mem_ker, RingHom.map_sub, map_mul, map_one, hw, h1, sub_self]
      have hkerle : RingHom.ker φ ≤ IsLocalRing.maximalIdeal _ :=
        IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top φ)
      have h1m : (1 : Localization.AtPrime 𝔭) ∈ IsLocalRing.maximalIdeal _ := by
        have hs := Ideal.sub_mem _ (Ideal.mul_mem_right w _ hxm) (hkerle hker)
        simpa using hs
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).mpr h1m)

end UpperTheory.Gal.crystallineComparison
end
end

section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.matRep_of :
    MatRep := by
  intro R S _ _ _ _ _
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R S
  set e : Fin n → S := fun k => f (Pi.single k 1) with he
  have hsum : ∀ s : S, ∑ k, g s k • e k = s := by
    intro s
    have h1 : f (g s) = s := LinearMap.congr_fun hfg s
    conv_rhs => rw [← h1, pi_eq_sum_univ (g s)]

    simp only [map_sum, map_smul, e]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 2
    ext j
    simp [Pi.single_apply, eq_comm]
  refine ⟨n, fun s => Matrix.of fun j k => g (s * e k) j, ?_⟩
  intro B _ _ I _ _ z hz
  let φ := AlgEquiv.ofBijective (splitMap z) hz
  let G : Fin n → (B ⊗[R] S →ₗ[B] B) := fun j =>
    (TensorProduct.AlgebraTensorModule.rid R B B).toLinearMap ∘ₗ ((LinearMap.proj j ∘ₗ g).baseChange B)
  have hG : ∀ j b s, G j (b ⊗ₜ s) = algebraMap R B (g s j) * b := by
    intro j b s
    simp [G, LinearMap.baseChange_tmul, Algebra.smul_def]
  have hK : ∀ x i, ∑ k, z i (e k) * G k x = splitMap z x i := by
    intro x i
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b s =>
      rw [splitMap_tmul]
      simp only [hG]
      conv_rhs => rw [← hsum s]

      rw [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, Algebra.smul_def]
      ring
    | add x y hx hy =>
      simp only [map_add (f := _), mul_add, Finset.sum_add_distrib, hx, hy, Pi.add_apply]
  have hL : ∀ t : S, ∑ i, z i t • φ.symm (Pi.single i 1) = (1 : B) ⊗ₜ t := by
    intro t
    apply φ.injective

    rw [map_sum]
    simp only [map_smul, AlgEquiv.apply_symm_apply]
    funext i'
    simp [φ, splitMap_tmul, Finset.sum_apply, Pi.single_apply]
    show (z i') t = splitMap z (1 ⊗ₜ t) i'
    rw [splitMap_tmul, one_mul]
  refine ⟨Matrix.of fun i k => z i (e k), Matrix.of fun j i => G j (φ.symm (Pi.single i 1)), ?_, ?_⟩
  · ext i i'
    simp only [Matrix.mul_apply, Matrix.of_apply]
    rw [hK]
    have h2 : splitMap z (φ.symm (Pi.single i' 1)) = Pi.single i' 1 := φ.apply_symm_apply _
    rw [h2, Matrix.one_apply, Pi.single_apply]
  · intro s
    ext j k
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.of_apply, Matrix.map_apply]
    have h3 : (algebraMap R B) (g (s * e k) j) = G j ((1 : B) ⊗ₜ (s * e k)) := by
      rw [hG, mul_one]

    rw [h3, ← hL, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, map_mul]
    ring
end
