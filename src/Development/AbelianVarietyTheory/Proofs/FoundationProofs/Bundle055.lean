module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsValuationSubringGaussModularFunction
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesCoeffRingHomMapCoeff
public import Mathlib.LinearAlgebra.Matrix.Integer
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle021
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle025
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle024
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle028
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
import Mathlib.Data.Finset.Functor
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle023
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.FieldTheory.PrimitiveElement
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
import Mathlib.Geometry.Manifold.StructureGroupoid
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.SlashActions
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001

@[expose] public section

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES.NF
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem exp_inj (X : Tower Ω ε) : Function.Injective X.exp :=
  (X.exp : X.K →+* HahnSeries ℚ Ω).injective

theorem gal_alg (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (c : Ω) :
    X.gal s (algebraMap Ω X.K c) = algebraMap Ω X.K (s c) := by
  apply exp_inj X
  ext r
  rw [X.gal_exp, AlgHom.commutes, AlgHom.commutes, HahnSeries.algebraMap_apply', HahnSeries.algebraMap_apply']
  by_cases h : r = 0 <;> simp [h, HahnSeries.coeff_single]

theorem gal_j (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) : X.gal s X.jK = X.jK := by
  apply exp_inj X
  ext r
  rw [X.gal_exp]
  obtain ⟨n, hn⟩ := X.j_exp.2.2 r
  rw [hn, map_intCast]

theorem gal_aeval (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (p : Polynomial Ω) (h : ∀ c ∈ p.coeffs, s c = c) :
    X.gal s (Polynomial.aeval X.jK p) = Polynomial.aeval X.jK p := by

  rw [Polynomial.aeval_eq_sum_range, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, map_mul, map_pow, gal_j, gal_alg]
  by_cases h0 : p.coeff i = 0
  · simp [h0]
  · rw [h _ (Polynomial.coeff_mem_coeffs h0)]

theorem exists_poly (X : Tower Ω ε) (f : X.K) : ∃ (C : Set Ω) (P : Polynomial X.K), C.Finite ∧ P ≠ 0 ∧
    ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ c ∈ C, s c = c) → P.IsRoot (X.gal s f) := by
  obtain ⟨p, hp, hf⟩ := X.alg_j f
  have key : ∀ i : ℕ, ∃ u v : Polynomial Ω, (p.coeff i : X.K) = Polynomial.aeval X.jK u / Polynomial.aeval X.jK v :=
    fun i => (IntermediateField.mem_adjoin_simple_iff Ω _).1 (p.coeff i).2
  choose u v huv using key
  refine ⟨⋃ i ∈ p.support, ((u i).coeffs ∪ (v i).coeffs : Set Ω), p.map (algebraMap _ X.K), ?_, ?_, ?_⟩
  · exact Set.Finite.biUnion (Finset.finite_toSet _) fun i _ => (Finset.finite_toSet _).union (Finset.finite_toSet _)
  · exact Polynomial.map_ne_zero hp
  · intro s hs
    have hP : (p.map (algebraMap _ X.K)).map (X.gal s : X.K →+* X.K) = p.map (algebraMap _ X.K) := by
      ext i
      rw [Polynomial.coeff_map, Polynomial.coeff_map]
      by_cases h0 : p.coeff i = 0
      · simp [h0]
      · have hi : i ∈ p.support := Polynomial.mem_support_iff.2 h0
        show X.gal s (p.coeff i : X.K) = (p.coeff i : X.K)
        rw [huv, map_div₀, gal_aeval X s _ fun c hc => hs c (Set.mem_biUnion hi (Or.inl hc)),
          gal_aeval X s _ fun c hc => hs c (Set.mem_biUnion hi (Or.inr hc))]
    have h1 : (p.map (algebraMap _ X.K)).IsRoot f := by
      rw [Polynomial.IsRoot, Polynomial.eval_map_algebraMap, hf]
    rw [← hP]
    exact Polynomial.IsRoot.map (f := (X.gal s : X.K →+* X.K)) h1

theorem coeff_numberField {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (f : X.K) :
    ∃ F : IntermediateField ℚ Ω, FiniteDimensional ℚ F ∧ ∀ r : ℚ, (X.exp f).coeff r ∈ F := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨C, P, hC, hP, hroot⟩ := exists_poly X f
  haveI := hC.to_subtype
  let F₀ : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ C
  haveI : FiniteDimensional ℚ F₀ :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  haveI : @IsScalarTower ℚ F₀ Ω Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : Normal F₀ Ω := IntermediateField.normal ℚ Ω F₀
  let L : Finset ℚ → IntermediateField F₀ Ω := fun T =>
    IntermediateField.adjoin F₀ ((T.image fun r => (X.exp f).coeff r : Finset Ω) : Set Ω)
  have hfin : ∀ T, FiniteDimensional F₀ (L T) := fun T =>
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hb : ∀ T, Module.finrank F₀ (L T) ≤ P.natDegree := by
    intro T
    haveI := hfin T
    haveI : Algebra.IsSeparable F₀ (L T) := by
      haveI : CharZero F₀ := algebraRat.charZero F₀
      infer_instance
    rw [← AlgHom.card F₀ (L T) Ω]
    let e : (L T →ₐ[F₀] Ω) → (Ω ≃ₐ[ℚ] Ω) := fun σ =>
      (AlgEquiv.ofBijective (σ.liftNormal Ω) (Algebra.IsAlgebraic.algHom_bijective _)).restrictScalars ℚ
    have he : ∀ σ (x : L T), e σ x = σ x := fun σ x => σ.liftNormal_commutes Ω x
    have hm : ∀ σ, X.gal (e σ) f ∈ P.roots.toFinset := by
      intro σ
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
      exact hroot _ fun c hc => (σ.liftNormal Ω).commutes (⟨c, IntermediateField.subset_adjoin ℚ C hc⟩ : F₀)
    calc Fintype.card (L T →ₐ[F₀] Ω) ≤ P.roots.toFinset.card := by
          rw [← Finset.card_univ]
          refine Finset.card_le_card_of_injOn (fun σ => X.gal (e σ) f) (fun σ _ => hm σ) ?_
          intro σ _ τ _ h
          apply IntermediateField.adjoin_algHom_ext
          intro x hx
          rw [← he, ← he]
          obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 hx
          show e σ ((X.exp f).coeff r) = e τ ((X.exp f).coeff r)
          rw [← X.gal_exp, ← X.gal_exp]
          exact congrArg (fun g => (X.exp g).coeff r) h
      _ ≤ _ := (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' P)
  have hB : BddAbove (Set.range fun T => Module.finrank F₀ (L T)) := ⟨P.natDegree, by rintro _ ⟨T, rfl⟩; exact hb T⟩
  obtain ⟨T, hT⟩ := Nat.sSup_mem (Set.range_nonempty fun T => Module.finrank F₀ (L T)) hB
  haveI := hfin T
  refine ⟨(L T).restrictScalars ℚ, FiniteDimensional.trans ℚ F₀ (L T), fun r => ?_⟩
  haveI := hfin (insert r T)
  have h : L T = L (insert r T) := by
    refine IntermediateField.eq_of_le_of_finrank_le (IntermediateField.adjoin.mono _ _ _ ?_) ?_
    · exact Finset.coe_subset.2 (Finset.image_subset_image (Finset.subset_insert _ _))
    · exact (le_csSup hB ⟨_, rfl⟩).trans hT.ge
  rw [IntermediateField.mem_restrictScalars, h]
  exact IntermediateField.subset_adjoin _ _ (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_insert_self _ _)))

end GlobalTheory.KZ.ES.NF
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.exists_valuationSubring_gauss_modularFunction : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (q : ℕ), q.Prime → ∀ V : ValuationSubring Ω, ((q : ℕ) : Ω) ∈ V.nonunits → ∃ W : ValuationSubring X.K, (∀ a : Ω, algebraMap Ω X.K a ∈ W ↔ a ∈ V) ∧ (∀ P : Polynomial Ω, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ∈ V ∧ P.coeff i ≠ 0 ∧ (P.coeff i)⁻¹ ∈ V) → W.valuation (Polynomial.aeval X.jK P) = 1) ∧ ∀ f : X.K, (∀ r, (X.exp f).coeff r ∈ V) → (∀ r, r ≠ 0 → (X.exp f).coeff r ∈ V.nonunits) → W.valuation (f - algebraMap Ω X.K ((X.exp f).coeff 0)) < 1 := by
  first | exact @GlobalTheory.KZ.exists_valuationSubring_gauss | exact GlobalTheory.KZ.exists_valuationSubring_gauss | (intros; apply GlobalTheory.KZ.exists_valuationSubring_gauss <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KronRatio

open GlobalTheory.KroneckerCongruence

variable {Ω : Type} [Field Ω]

theorem mem_of_isIntegral_int (V : ValuationSubring Ω) {x : Ω} (hx : IsIntegral ℤ x) : x ∈ V := by
  have h : IsIntegral V x := hx.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := Ω)).1 h
  rw [← hy]; exact y.2

theorem valuation_natCast_eq_one (V : ValuationSubring Ω) {q D : ℕ} (hq : q.Prime)
    (hqV : ((q : ℕ) : Ω) ∈ V.nonunits) (hD : ¬ q ∣ D) : V.valuation (D : Ω) = 1 := by
  have hcop : IsCoprime (q : ℤ) (D : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact (Nat.Prime.coprime_iff_not_dvd hq).2 hD
  obtain ⟨a, b, hab⟩ := hcop
  have hle : ∀ n : ℤ, V.valuation (n : Ω) ≤ 1 := fun n => (V.valuation_le_one_iff _).2 (intCast_mem V n)
  have hq1 : V.valuation (q : Ω) < 1 := V.mem_nonunits_iff.1 hqV
  by_contra hne
  have hD1 : V.valuation (D : Ω) < 1 := lt_of_le_of_ne ((V.valuation_le_one_iff _).2 (natCast_mem V D)) hne
  have h1 : (1 : Ω) = (a : Ω) * (q : Ω) + (b : Ω) * (D : Ω) := by
    have := congrArg (fun z : ℤ => (z : Ω)) hab
    push_cast at this
    exact this.symm
  have h2 : V.valuation (1 : Ω) < 1 := by
    rw [h1]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle a)) hq1
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle b)) hD1
  simp at h2

theorem mem_of_bdd (V : ValuationSubring Ω) {q D : ℕ} (hq : q.Prime) (hqV : ((q : ℕ) : Ω) ∈ V.nonunits)
    (hD : ¬ q ∣ D) {a : Ω} (h : ∃ k : ℕ, IsIntegral ℤ ((D : Ω) ^ k * a)) : a ∈ V := by
  obtain ⟨k, hk⟩ := h
  have h1 := mem_of_isIntegral_int V hk
  have hv := valuation_natCast_eq_one V hq hqV hD
  rw [← V.valuation_le_one_iff] at h1 ⊢
  rwa [map_mul, map_pow, hv, one_pow, one_mul] at h1

theorem coeff_mul_mem (V : ValuationSubring Ω) (x y : HahnSeries ℚ Ω) (hx : ∀ r, x.coeff r ∈ V)
    (hy : ∀ r, y.coeff r ∈ V) (r : ℚ) : (x * y).coeff r ∈ V := by
  have he : x * y = hahnSeriesCoeffRingHomMap V.subtype (liftV V x hx * liftV V y hy) := by
    rw [map_mul, map_liftV, map_liftV]
  rw [he, hahnSeriesCoeffRingHomMap_coeff]; exact (_ : V).2

theorem coeff_pow_mem (V : ValuationSubring Ω) (x : HahnSeries ℚ Ω) (hx : ∀ r, x.coeff r ∈ V) (n : ℕ)
    (r : ℚ) : (x ^ n).coeff r ∈ V := by
  have he : x ^ n = hahnSeriesCoeffRingHomMap V.subtype (liftV V x hx ^ n) := by
    rw [map_pow, map_liftV]
  rw [he, hahnSeriesCoeffRingHomMap_coeff]; exact (_ : V).2

theorem coeff_mul_mem_nonunits (V : ValuationSubring Ω) (x y : HahnSeries ℚ Ω)
    (hx : ∀ r, x.coeff r ∈ V.nonunits) (hy : ∀ r, y.coeff r ∈ V) (r : ℚ) : (x * y).coeff r ∈ V.nonunits := by
  have hx' : ∀ r, x.coeff r ∈ V := fun r =>
    (V.valuation_le_one_iff _).1 (le_of_lt (V.mem_nonunits_iff.1 (hx r)))
  set ρ := IsLocalRing.residue V with hρ_def
  have hρ0 : ∀ z : V, ρ z = 0 ↔ V.valuation (z : Ω) < 1 := fun z => by
    rw [hρ_def, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  have hX : hahnSeriesCoeffRingHomMap ρ (liftV V x hx') = 0 := by
    ext t
    rw [hahnSeriesCoeffRingHomMap_coeff]
    exact (hρ0 _).2 (V.mem_nonunits_iff.1 (hx t))
  have he : x * y = hahnSeriesCoeffRingHomMap V.subtype (liftV V x hx' * liftV V y hy) := by
    rw [map_mul, map_liftV, map_liftV]
  rw [he, hahnSeriesCoeffRingHomMap_coeff, ValuationSubring.mem_nonunits_iff]
  refine (hρ0 ((liftV V x hx' * liftV V y hy).coeff r)).1 ?_
  rw [← hahnSeriesCoeffRingHomMap_coeff, map_mul, hX, zero_mul]
  rfl

end GlobalTheory.KronRatio

namespace GlobalTheory.KZ


open GlobalTheory.KroneckerCongruence GlobalTheory.KronRatio in
theorem kronecker_ratio_reduces_to_const : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (M : ℕ) (f : X.Kˣ), 0 < M → (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (f : X.K) = f) → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), ((q : ℕ) : Ω) ∈ V.nonunits → (∀ x ∈ V, s x ∈ V ∧ s.symm x ∈ V ∧ V.valuation (s x - x ^ q) < 1) → ∀ σ : SL(2, ℤ), ((en σ 0 1 : ZMod M) = 0 ∧ (en σ 1 0 : ZMod M) = 0 ∧ (en σ 1 1 : ZMod M) = q) → ∀ W : ValuationSubring X.K, (∀ a : Ω, algebraMap Ω X.K a ∈ W ↔ a ∈ V) → (∀ g : X.K, (∀ r, (X.exp g).coeff r ∈ V) → (∀ r, r ≠ 0 → (X.exp g).coeff r ∈ V.nonunits) → W.valuation (g - algebraMap Ω X.K ((X.exp g).coeff 0)) < 1) → ∃ κ : Ω, κ ≠ 0 ∧ W.valuation (algebraMap Ω X.K κ * ((∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) (f : X.K)) * X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) (f : X.K)) / (X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL σ) (f : X.K))) ^ q) - 1) < 1 := by
  intro Ω _ _ _ ε X hε hj M f hM hf
  classical
  haveI : NeZero M := ⟨hM.ne'⟩
  let red : SL(2, ℤ) →* SL(2, ZMod M) := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))
  let F : SL(2, ZMod M) → X.K := fun τ =>
    if h : ∃ σ, red σ = τ then X.sl (ofSL h.choose) (f : X.K) else (f : X.K)
  have hF : ∀ σ : SL(2, ℤ), X.sl (ofSL σ) (f : X.K) = F (red σ) := by
    intro σ
    have h : ∃ σ', red σ' = red σ := ⟨σ, rfl⟩
    have e : F (red σ) = X.sl (ofSL h.choose) (f : X.K) := dif_pos h
    have hσ' : red h.choose = red σ := h.choose_spec
    have hγ : σ * h.choose⁻¹ ∈ CongruenceSubgroup.Gamma M := by
      have : σ * h.choose⁻¹ ∈ red.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hσ', mul_inv_cancel]
      exact this
    rw [e]
    calc X.sl (ofSL σ) (f : X.K) = X.sl (ofSL (σ * h.choose⁻¹ * h.choose)) (f : X.K) := by
          rw [inv_mul_cancel_right]
      _ = X.sl (ofSL h.choose) (X.sl (ofSL (σ * h.choose⁻¹)) (f : X.K)) := by rw [map_mul, X.sl_mul]
      _ = _ := by rw [hf _ hγ]
  choose D hD0 hD using X.bdd
  let P : X.K → Finset ℕ := fun g => (D g).primeFactors ∪ (D g⁻¹).primeFactors
  refine ⟨M.primeFactors ∪ P f ∪ Finset.univ.biUnion (fun τ => P (F τ)), ?_⟩
  intro q hq hqS V s hqV hs σ hσ W hW hdom
  have hn : ∀ h : X.K, q ∉ (D h).primeFactors → ∀ r, (X.exp h).coeff r ∈ V := fun h hh r =>
    mem_of_bdd V hq hqV (fun hd => hh (Nat.mem_primeFactors.2 ⟨hq, hd, (hD0 h).ne'⟩)) (hD h r)
  have hint : ∀ g : X.K, q ∉ P g → (∀ r, (X.exp g).coeff r ∈ V) ∧ (∀ r, (X.exp g⁻¹).coeff r ∈ V) := fun g hg =>
    ⟨hn g fun h => hg (Finset.mem_union_left _ h), hn _ fun h => hg (Finset.mem_union_right _ h)⟩
  have hqM : q ∉ M.primeFactors := fun h => hqS (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hqf : q ∉ P f := fun h => hqS (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hqF : q ∉ P (F (red σ)) := fun h =>
    hqS (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨_, Finset.mem_univ _, h⟩))
  obtain ⟨hf1, hf2⟩ := hint _ hqf
  rw [← hF σ] at hqF
  obtain ⟨hs1, hs2⟩ := hint _ hqF
  have hcop : Nat.Coprime q M :=
    (Nat.Prime.coprime_iff_not_dvd hq).2 fun hd => hqM (Nat.mem_primeFactors.2 ⟨hq, hd, hM.ne'⟩)
  have hK := kronecker_congruence_tower ε X hε hj M q (f : X.K) hM hq hcop hf σ ⟨hσ.2.1, hσ.2.2⟩ V s hqV hs hf1 hs1
  refine ⟨1, one_ne_zero, ?_⟩
  generalize (∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) (f : X.K)) *
    X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) (f : X.K) = A at hK ⊢
  have hB0 : X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL σ) (f : X.K))) ^ q ≠ 0 :=
    mul_ne_zero ((map_ne_zero _).2 f.ne_zero)
      (pow_ne_zero _ ((map_ne_zero _).2 ((map_ne_zero _).2 f.ne_zero)))
  have hBinv : ∀ r, (X.exp (X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL σ) (f : X.K))) ^ q)⁻¹).coeff r ∈ V := by
    intro r
    rw [mul_inv, ← inv_pow, ← map_inv₀, ← map_inv₀ (X.gal s.symm), map_mul, map_pow]
    refine coeff_mul_mem V _ _ (fun t => ?_) (coeff_pow_mem V _ (fun t => ?_) q) r
    · rw [X.gal_exp]; exact (hs _ (hf2 t)).1
    · rw [X.gal_exp]; exact (hs _ (hs2 t)).2.1
  generalize X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL σ) (f : X.K))) ^ q = B at hK hB0 hBinv ⊢
  have hge : algebraMap Ω X.K 1 * A / B - 1 = (A - B) * B⁻¹ := by
    rw [map_one, one_mul]; field_simp
  rw [hge]
  have hgc : ∀ r, (X.exp ((A - B) * B⁻¹)).coeff r ∈ V.nonunits := by
    intro r; rw [map_mul]; exact coeff_mul_mem_nonunits V _ _ hK hBinv r
  generalize (A - B) * B⁻¹ = g at hgc ⊢
  have hgV : ∀ r, (X.exp g).coeff r ∈ V := fun r =>
    (V.valuation_le_one_iff _).1 (le_of_lt (V.mem_nonunits_iff.1 (hgc r)))
  have h1 := hdom g hgV fun r _ => hgc r
  have hcV := V.mem_nonunits_iff.1 (hgc 0)
  have hcm := hgV 0
  generalize (X.exp g).coeff 0 = c at h1 hcV hcm
  have h2 : W.valuation (algebraMap Ω X.K c) < 1 := by
    by_cases hc0 : c = 0
    · rw [hc0, map_zero, map_zero]; exact zero_lt_one
    refine lt_of_le_of_ne ((W.valuation_le_one_iff _).2 ((hW c).2 hcm)) fun heq => ?_
    have hinv : algebraMap Ω X.K c⁻¹ ∈ W := by
      rw [← W.valuation_le_one_iff, map_inv₀, map_inv₀, heq, inv_one]
    have h3 : V.valuation c⁻¹ ≤ 1 := (V.valuation_le_one_iff _).2 ((hW _).1 hinv)
    have h4 : V.valuation (c⁻¹ * c) < 1 := by
      rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' h3) hcV
    rw [inv_mul_cancel₀ hc0, map_one] at h4
    exact lt_irrefl _ h4
  have h5 := lt_of_le_of_lt (W.valuation.map_add _ _) (max_lt h1 h2)
  rwa [sub_add_cancel] at h5

end GlobalTheory.KZ
end
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FN

open Matrix CongruenceSubgroup


set_option backward.isDefEq.respectTransparency false in
theorem conj_Gamma_den_mul (g : GL (Fin 2) ℚ) (M : ℕ) (y : SL(2, ℤ))
    (hy' : y ∈ Gamma ((g.1.den * (g⁻¹).1.den) * M)) :
    ∃ z ∈ Gamma M, ((z : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ)) =
      g.1 * ((y : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ)) * (g⁻¹).1 := by
  obtain ⟨y, hy⟩ := y
  let A₁ := g.1
  let A₂ := (g⁻¹).1
  have hA₁₂ : A₁ * A₂ = 1 := by simp only [← Matrix.GeneralLinearGroup.coe_mul,
    mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one, A₁, A₂]
  let a₁ := A₁.den
  let a₂ := A₂.den
  obtain ⟨k, hk⟩ : ∃ k, y = 1 + (a₁ * a₂ * M) • k := by
    replace hy' : y.map (Int.cast : ℤ → ZMod (a₁ * a₂ * M)) = 1 := by
      rw [CongruenceSubgroup.Gamma_mem', Subtype.ext_iff] at hy'
      simpa using! hy'
    use Matrix.of fun i j ↦ (y - 1) i j / (a₁ * a₂ * M)
    rw [← sub_eq_iff_eq_add']
    ext i j
    simp_rw [Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul, Nat.cast_mul]
    refine (Int.mul_ediv_cancel_of_dvd ?_).symm
    rw [← Matrix.map_one Int.cast (by simp) (by simp), ← sub_eq_zero,
      ← Matrix.map_sub _ (by simp)] at hy'
    simpa only [Matrix.zero_apply, Matrix.map_apply, ZMod.intCast_zmod_eq_zero_iff_dvd,
      Nat.cast_mul] using! congr_fun₂ hy' i j
  let z := 1 + M • (A₁.num * k * A₂.num)
  have hz_coe : z.map Int.cast = A₁ * (y.map Int.cast) * A₂ := by
    simp only [Matrix.map_add _ Int.cast_add, Matrix.map_one _ Int.cast_zero Int.cast_one, hk,
      mul_add, mul_one, add_mul, hA₁₂, add_right_inj, z]
    conv_rhs => rw [← A₁.inv_denom_smul_num, ← A₂.inv_denom_smul_num, Matrix.map_smul _ _ (by simp)]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.map_smul (Int.cast : ℤ → ℚ) M (by simp),
      Matrix.map_mul_intCast]
    rw [← Nat.cast_smul_eq_nsmul ℚ (_ * M), ← mul_smul, ← mul_smul,
      mul_comm a₁ a₂, Nat.cast_mul, Nat.cast_mul, mul_assoc _ _ (M : ℚ), mul_comm _ (M : ℚ),
      inv_mul_cancel_left₀ (mod_cast A₂.den_ne_zero),
      mul_inv_cancel_right₀ (mod_cast A₁.den_ne_zero), Nat.cast_smul_eq_nsmul]
  have hz_det : z.det = 1 := by
    have := congr_arg Matrix.det hz_coe
    simp_rw [Matrix.det_mul, ← Int.cast_det] at this
    rwa [mul_right_comm, ← Matrix.det_mul, hA₁₂, Matrix.det_one, one_mul, hy, Int.cast_inj] at this
  refine ⟨⟨z, hz_det⟩, ?_, hz_coe⟩
  rw [CongruenceSubgroup.Gamma_mem', Subtype.ext_iff]
  change z.map (Int.cast : ℤ → ZMod M) = 1
  ext i j
  change (↑((1 : Matrix (Fin 2) (Fin 2) ℤ) i j +
    M • (A₁.num * k * A₂.num) i j) : ZMod M) = (1 : Matrix (Fin 2) (Fin 2) (ZMod M)) i j
  simp [nsmul_eq_mul, Matrix.one_apply]

theorem exists_conj_principal_congruence :
    ∀ g : GQ, ∃ n : ℕ, 0 < n ∧ ∀ N : ℕ, ∀ δ ∈ CongruenceSubgroup.Gamma (N * n),
      ∃ δ' ∈ CongruenceSubgroup.Gamma N, g * ofSL δ = ofSL δ' * g := by
  intro g
  let G : GL (Fin 2) ℚ := g
  refine ⟨G.1.den * (G⁻¹).1.den, Nat.mul_pos (Nat.pos_of_ne_zero (Matrix.den_ne_zero _)) (Nat.pos_of_ne_zero (Matrix.den_ne_zero _)), fun N δ hδ => ?_⟩
  rw [mul_comm] at hδ
  obtain ⟨z, hz, hzc⟩ := conj_Gamma_den_mul G N δ hδ
  refine ⟨z, hz, ?_⟩
  apply Subtype.ext
  apply Units.ext
  have h21 : (G⁻¹).1 * G.1 = 1 := by
    simp only [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.GeneralLinearGroup.coe_one]
  show G.1 * ((δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ)) =
    ((z : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ)) * G.1
  have e1 : ((z : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ)) =
      ((z : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ)) := rfl
  have e2 : ((δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ)) =
      ((δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ)) := rfl
  rw [e1, e2, hzc, Matrix.mul_assoc, h21, Matrix.mul_one]

end GlobalTheory.FN
end
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm
open GlobalTheory.HeckeFamilyMatrices

theorem _root_.GlobalTheory.T.upper_mul_eq_mul_diamond_diag_gamma1InterGamma0 : ∀ (N l q j : ℕ) (σ γ : SL(2, ℤ)), q.Prime → ¬ q ∣ N * l → GlobalTheory.Hk.IsDia N l q σ → j < q → γ ∈ GlobalTheory.Hk.lev N l → (q : ℤ) ∣ mat γ 0 0 + j * mat γ 1 0 → ∃ γ' ∈ GlobalTheory.Hk.lev N l, !![(1 : ℤ), (j : ℤ); 0, (q : ℤ)] * mat γ = mat γ' * (mat σ * dg q 1) := by
  first | exact @GlobalTheory.Hk.upper_mul_eq_mul_diamond_diag | exact GlobalTheory.Hk.upper_mul_eq_mul_diamond_diag | (intros; apply GlobalTheory.Hk.upper_mul_eq_mul_diamond_diag <;> assumption)
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm

theorem _root_.GlobalTheory.T.heckeOperatorsOnHalfPlaneFunctions_agree_explicit : (∀ (k : ℤ) (l : ℕ) (f : ℍ → ℂ), 0 < l → UlF k l f = GlobalTheory.Hk.uOp l f) ∧
  (∀ (k : ℤ) (σ : SL(2, ℤ)) (f : ℍ → ℂ), DdF k σ f = GlobalTheory.Hk.dia k σ f) ∧
  (∀ (k : ℤ) (q : ℕ) (σ : SL(2, ℤ)) (f : ℍ → ℂ), 0 < q → TqF k q σ f = GlobalTheory.Hk.heckeT k q σ f) ∧
  (∀ (N l : ℕ) (d : ℤ) (σ : SL(2, ℤ)), IsDiam N l (d : ZMod N) σ ↔ GlobalTheory.Hk.IsDia N l d σ) ∧
  ∀ N l : ℕ, Lev N l = GlobalTheory.Hk.lev N l := by
  first | exact @GlobalTheory.SlashUpperTriangularMatrices.bridge | exact GlobalTheory.SlashUpperTriangularMatrices.bridge | (intros; apply GlobalTheory.SlashUpperTriangularMatrices.bridge <;> assumption)
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem _root_.GlobalTheory.T.eichlerShimura_conj_cocycles_coboundaries_period_smul : ∀ (Γ : Subgroup SL(2, ℤ)) (w : ℕ), (∀ z ∈ Z1 Γ w, cj z ∈ Z1 Γ w) ∧ (∀ z ∈ B1 Γ w, cj z ∈ B1 Γ w) ∧ ∀ (f : ℍ → ℂ) (c : ℂ), per Γ w (c • f) = c • per Γ w f := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.cj_mem_Z1_cj_mem_B1_per_smul | exact GlobalTheory.HeckeFamilyMatrices.cj_mem_Z1_cj_mem_B1_per_smul | (intros; apply GlobalTheory.HeckeFamilyMatrices.cj_mem_Z1_cj_mem_B1_per_smul <;> assumption)
end

section


theorem _root_.GlobalTheory.T.smoothedEisensteinFxCoefficientSeq_one_mem_subring : ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (c M : ℕ) (ζ : K) (a b : ℤ), 0 < M → Nat.Coprime c M → ¬ (M : ℤ) ∣ a → ζ ^ b ∈ R → ζ ^ (-b) ∈ R → ∀ n : ℕ, GlobalTheory.KummerEisensteinGalois.smF (c : ℤ) 1 M ζ a b n ∈ R := by
  first | exact @GlobalTheory.KummerEisensteinGalois.smF_one_mem_subring | exact GlobalTheory.KummerEisensteinGalois.smF_one_mem_subring | (intros; apply GlobalTheory.KummerEisensteinGalois.smF_one_mem_subring; all_goals assumption)
end
