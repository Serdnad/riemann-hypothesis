module

public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Span.Defs
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
public import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Algebra.Group.Commute.Hom
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.LinearAlgebra.Span.Basic

@[expose] public section

section

namespace GlobalTheory

namespace FirstOrderPoints

open TrivSqZeroExt

variable {R₀ B K : Type} [CommRing R₀] [CommRing B] [Field K] [Algebra R₀ B]
  [Algebra B K] [Algebra R₀ K] [IsScalarTower R₀ B K]

def derOf (h : B →+* DualNumber K) (hfst : ∀ b, (h b).fst = algebraMap B K b)
    (hc : ∀ a : R₀, (h (algebraMap R₀ B a)).snd = 0) : Derivation R₀ B K :=
  Derivation.mk'
    { toFun := fun b => (h b).snd
      map_add' := fun x y => by simp
      map_smul' := fun a b => by
        simp only [RingHom.id_apply]
        rw [Algebra.smul_def, map_mul, snd_mul, hc, hfst, smul_zero, add_zero, smul_eq_mul,
          ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def] }
    (fun a b => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, map_mul, snd_mul, hfst, Algebra.smul_def,
        MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, smul_eq_mul, Algebra.algebraMap_self,
        RingHom.id_apply]
      ring)

lemma derOf_injective (h h' : B →+* DualNumber K) (hfst : ∀ b, (h b).fst = algebraMap B K b)
    (hc : ∀ a : R₀, (h (algebraMap R₀ B a)).snd = 0)
    (hfst' : ∀ b, (h' b).fst = algebraMap B K b)
    (hc' : ∀ a : R₀, (h' (algebraMap R₀ B a)).snd = 0)
    (e : derOf h hfst hc = derOf h' hfst' hc') : h = h' := by
  ext b
  · rw [hfst, hfst']
  · have := congrArg (fun D : Derivation R₀ B K => D b) e
    simpa [derOf] using this

lemma derivation_eq_of_basis {ι : Type} (e : Module.Basis ι B Ω[B⁄R₀]) (D D' : Derivation R₀ B K)
    (h : ∀ j, D.liftKaehlerDifferential (e j) = D'.liftKaehlerDifferential (e j)) : D = D' := by
  have : D.liftKaehlerDifferential = D'.liftKaehlerDifferential := e.ext h
  rw [← Derivation.liftKaehlerDifferential_comp D, ← Derivation.liftKaehlerDifferential_comp D', this]

lemma liftKaehler_eq_sum {ι : Type} [Fintype ι] (D : Derivation R₀ B K) (Ds : ι → Derivation R₀ B K)
    (c : ι → K) (h : ∀ x, D x = ∑ i, c i * Ds i x) (ω : Ω[B⁄R₀]) :
    D.liftKaehlerDifferential ω = ∑ i, c i * (Ds i).liftKaehlerDifferential ω := by
  let φ : Ω[B⁄R₀] →ₗ[B] K :=
    { toFun := fun ω => ∑ i, c i * (Ds i).liftKaehlerDifferential ω
      map_add' := fun x y => by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun b x => by
        simp only [map_smul, RingHom.id_apply, smul_eq_mul, Algebra.smul_def, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring }
  have : D.liftKaehlerDifferential = φ := by
    apply Derivation.liftKaehlerDifferential_unique
    ext x
    simp [φ, Derivation.liftKaehlerDifferential_comp_D, h]
  rw [this]; rfl

end FirstOrderPoints

end GlobalTheory

namespace GlobalTheory

namespace FirstOrderPoints

open TrivSqZeroExt

theorem exists_linearCombination_eq :
    ∀ (R₀ B K : Type) [CommRing R₀] [CommRing B] [Algebra R₀ B] [Field K] (n : ℕ),
    Algebra.IsStandardSmoothOfRelativeDimension n R₀ B → ∀ (ι : Type) [Fintype ι], Fintype.card ι = n →
    ∀ R : B →+* TrivSqZeroExt K (ι → K), (∀ a : R₀, R (algebraMap R₀ B a) = TrivSqZeroExt.inl (R (algebraMap R₀ B a)).fst) →
    (∀ M M' : ι → K, (TrivSqZeroExt.map (Fintype.linearCombination K M)).toRingHom.comp R =
      (TrivSqZeroExt.map (Fintype.linearCombination K M')).toRingHom.comp R → M = M') →
    ∀ g : B →+* DualNumber K, (∀ b, (g b).fst = (R b).fst) →
    (∀ a : R₀, g (algebraMap R₀ B a) = TrivSqZeroExt.inl (g (algebraMap R₀ B a)).fst) →
    ∃ M : ι → K, g = (TrivSqZeroExt.map (Fintype.linearCombination K M)).toRingHom.comp R := by
  intro R₀ B K _ _ _ _ n hsm ι _ hcard R hR hinj g hgfst hg
  classical
  haveI : Algebra.IsStandardSmooth R₀ B := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  let ρ : B →+* K := (TrivSqZeroExt.fstHom K K (ι → K)).toRingHom.comp R
  letI : Algebra B K := ρ.toAlgebra
  letI : Algebra R₀ K := (ρ.comp (algebraMap R₀ B)).toAlgebra
  haveI : IsScalarTower R₀ B K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Nontrivial B := ρ.domain_nontrivial
  have hfin : Module.finrank B Ω[B⁄R₀] = n := by
    have := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := R₀) (S := B) n
    rw [← Module.finrank_eq_rank] at this
    exact_mod_cast this
  let e := Module.finBasisOfFinrankEq B Ω[B⁄R₀] hfin
  let hM : (ι → K) → B →+* DualNumber K := fun M =>
    (TrivSqZeroExt.map (Fintype.linearCombination K M)).toRingHom.comp R
  have hMfst : ∀ M b, (hM M b).fst = algebraMap B K b := fun M b => by
    simp [hM, ρ, RingHom.algebraMap_toAlgebra]
  have hR0 : ∀ a : R₀, (R (algebraMap R₀ B a)).snd = 0 := fun a => by
    have := congrArg TrivSqZeroExt.snd (hR a)
    simpa using this
  have hMc : ∀ M (a : R₀), (hM M (algebraMap R₀ B a)).snd = 0 := fun M a => by
    simp [hM, hR0 a]
  let D : (ι → K) → Derivation R₀ B K := fun M => derOf (hM M) (hMfst M) (hMc M)
  have hD : ∀ M x, D M x = ∑ i, M i * D (Pi.single i 1) x := by
    intro M x
    simp [D, derOf, hM, Fintype.linearCombination_apply, Pi.single_apply, mul_comm]
  let w : ι → (Fin n → K) := fun i j => (D (Pi.single i 1)).liftKaehlerDifferential (e j)
  let L := Fintype.linearCombination K w
  have hL : ∀ M, L M = fun j => (D M).liftKaehlerDifferential (e j) := by
    intro M
    funext j
    rw [liftKaehler_eq_sum (D M) (fun i => D (Pi.single i 1)) M (hD M)]
    simp [L, w, Fintype.linearCombination_apply, Finset.sum_apply]
  have Linj : Function.Injective L := by
    intro M M' hMM
    apply hinj
    apply derOf_injective (hM M) (hM M') (hMfst M) (hMc M) (hMfst M') (hMc M')
    apply derivation_eq_of_basis e
    intro j
    rw [hL, hL] at hMM
    exact congrFun hMM j
  have Lsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hcard])).mp Linj
  have hgfst' : ∀ b, (g b).fst = algebraMap B K b := fun b => hgfst b
  have hgc : ∀ a : R₀, (g (algebraMap R₀ B a)).snd = 0 := fun a => by
    have := congrArg TrivSqZeroExt.snd (hg a)
    simpa using this
  obtain ⟨M, hMeq⟩ := Lsurj (fun j => (derOf g hgfst' hgc).liftKaehlerDifferential (e j))
  refine ⟨M, ?_⟩
  refine derOf_injective g (hM M) hgfst' hgc (hMfst M) (hMc M) ?_
  apply derivation_eq_of_basis e
  intro j
  rw [hL] at hMeq
  exact (congrFun hMeq j).symm

end FirstOrderPoints

end GlobalTheory
end

section

open scoped TensorProduct

namespace GlobalTheory

theorem exists_common_field_extension :
    ∀ (Ω Ω₁ Ω₂ : Type) [Field Ω] [Field Ω₁] [Field Ω₂] (i₁ : Ω →+* Ω₁) (i₂ : Ω →+* Ω₂),
      ∃ (Ω₃ : Type) (_ : Field Ω₃) (j₁ : Ω₁ →+* Ω₃) (j₂ : Ω₂ →+* Ω₃), j₁.comp i₁ = j₂.comp i₂ := by
  intro Ω Ω₁ Ω₂ _ _ _ i₁ i₂
  letI : Algebra Ω Ω₁ := i₁.toAlgebra
  letI : Algebra Ω Ω₂ := i₂.toAlgebra
  haveI : Nontrivial (Ω₁ ⊗[Ω] Ω₂) := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (Ω₁ ⊗[Ω] Ω₂)
  refine ⟨(Ω₁ ⊗[Ω] Ω₂) ⧸ m, Ideal.Quotient.field m,
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeLeftRingHom),
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight (R := Ω) (A := Ω₁) (B := Ω₂)).toRingHom, ?_⟩
  ext x
  have h : (algebraMap Ω Ω₁ x) ⊗ₜ[Ω] (1 : Ω₂) = (1 : Ω₁) ⊗ₜ[Ω] (algebraMap Ω Ω₂ x) := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  exact congrArg (Ideal.Quotient.mk m) h

end GlobalTheory
end

section

namespace GlobalTheory

theorem exists_mul_invol_eq_of_fixed (k : Type) [Field k] [Finite k] (τ : k →+* k)
    (hτ : Function.Involutive τ) (hne : ∃ b : k, τ b ≠ b) (c : k) (hc : τ c = c) :
    ∃ a : k, a * τ a = c := by
  classical
  obtain ⟨b, hb⟩ := hne
  let F : Subfield k := τ.eqLocusField (RingHom.id k)
  have hd : b - τ b ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)

  let f : F × F → k := fun p => (p.1 : k) + (p.2 : k) * b
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨α, β⟩ ⟨α', β'⟩ h
      have ea : τ (α : k) = α := α.2
      have eb : τ (β : k) = β := β.2
      have ea' : τ (α' : k) = α' := α'.2
      have eb' : τ (β' : k) = β' := β'.2
      have h0 : (α : k) + β * b = α' + β' * b := h
      have h1 : τ ((α : k) + β * b) = τ ((α' : k) + β' * b) := by rw [h0]
      rw [map_add (f := _), map_mul, map_add (f := _), map_mul, ea, eb, ea', eb'] at h1
      have hβ : (β : k) = β' := by
        have h2 : ((β : k) - β') * (b - τ b) = 0 := by linear_combination h0 - h1
        rcases mul_eq_zero.mp h2 with h3 | h3
        · exact sub_eq_zero.mp h3
        · exact absurd h3 hd
      have hα : (α : k) = α' := by
        rw [hβ] at h0
        linear_combination h0
      exact Prod.ext (Subtype.ext hα) (Subtype.ext hβ)
    · intro x
      have hβ : τ ((x - τ x) / (b - τ b)) = (x - τ x) / (b - τ b) := by
        rw [map_div₀, map_sub, map_sub, hτ x, hτ b, ← neg_sub x (τ x), ← neg_sub b (τ b),
          neg_div_neg_eq]
      have hm : (x - τ x) / (b - τ b) * (b - τ b) = x - τ x := div_mul_cancel₀ _ hd
      have hα : τ (x - (x - τ x) / (b - τ b) * b) = x - (x - τ x) / (b - τ b) * b := by
        rw [map_sub, map_mul, hβ]
        linear_combination hm
      refine ⟨(⟨x - (x - τ x) / (b - τ b) * b, hα⟩, ⟨(x - τ x) / (b - τ b), hβ⟩), ?_⟩
      show x - (x - τ x) / (b - τ b) * b + (x - τ x) / (b - τ b) * b = x
      ring
  have hcard : Nat.card k = Nat.card F ^ 2 := by
    rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, sq]
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hrank : Module.finrank F k = 2 := by
    have h := Module.natCard_eq_pow_finrank (K := F) (V := k)
    rw [hcard] at h
    exact (Nat.pow_right_injective hq h).symm

  let τ' : k ≃ₐ[F] k := AlgEquiv.ofBijective { τ with commutes' := fun r => r.2 } hτ.bijective
  have hτ' : ∀ x, τ' x = τ x := fun _ => rfl
  have hne1 : (1 : k ≃ₐ[F] k) ≠ τ' := by
    intro h
    apply hb
    rw [← hτ' b, ← h]
    rfl
  have hcardG : Fintype.card (k ≃ₐ[F] k) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hrank]
  have huniv : (Finset.univ : Finset (k ≃ₐ[F] k)) = {1, τ'} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, hcardG, Finset.card_pair hne1]

  obtain ⟨a, ha⟩ := FiniteField.norm_surjective F k ⟨c, hc⟩
  have h := Algebra.norm_eq_prod_automorphisms F a
  rw [ha, huniv, Finset.prod_pair hne1] at h
  refine ⟨a, ?_⟩
  calc a * τ a = (1 : k ≃ₐ[F] k) a * τ' a := rfl
    _ = c := h.symm

end GlobalTheory
end

section

namespace GlobalTheory

theorem div_mem_of_mul_pow_div_mem_of_regularPair (K : Type) [Field K] (O : Subring K) (s t : K)
    (ht : t ∈ O) (h : ∀ g ∈ O, g * t / s ∈ O → g / s ∈ O) (N : ℕ) :
    ∀ g ∈ O, g * t ^ N / s ∈ O → g / s ∈ O := by
  induction N with
  | zero => intro g _ hg; simpa using hg
  | succ N ih =>
    intro g hg hgN
    apply ih g hg
    apply h _ (O.mul_mem hg (O.pow_mem ht N))
    rwa [mul_assoc, ← pow_succ]

theorem regularPair_pow : ∀ (K : Type) [Field K] (O : Subring K) (s t : K), s ∈ O → t ∈ O → s ≠ 0 → (∀ g ∈ O, g * t / s ∈ O → g / s ∈ O) → ∀ (m N : ℕ), ∀ g ∈ O, g * t ^ N / s ^ m ∈ O → g / s ^ m ∈ O := by
  intro K _ O s t hs ht hs0 h m N
  induction m with
  | zero => intro g hg _; simpa using hg
  | succ m ih =>
    intro g hg hgN
    have h1 : g * t ^ N / s ∈ O := by
      have h2 := O.mul_mem hgN (O.pow_mem hs m)
      have e : g * t ^ N / s ^ (m + 1) * s ^ m = g * t ^ N / s := by
        field_simp
        ring
      rwa [e] at h2
    have h3 := div_mem_of_mul_pow_div_mem_of_regularPair K O s t ht h N g hg h1
    have e1 : g / s * t ^ N / s ^ m = g * t ^ N / s ^ (m + 1) := by
      field_simp
      ring
    have e2 : g / s / s ^ m = g / s ^ (m + 1) := by
      field_simp
      ring
    rw [← e2]
    exact ih _ h3 (by rwa [e1])

end GlobalTheory
end

section

universe u_1 u_2

namespace GlobalTheory.BandMonotonicity

theorem band_mono :
    (let d1 : {k : Type u_1} → [Field k] → {ι : Type u_2} → (ι → ℕ) → ℕ → Matrix ι ι k → Prop :=
      @(fun {k : Type u_1} [Field k] {ι : Type u_2} (ℓ : ι → ℕ) (j : ℕ) (X : Matrix ι ι k) ↦
        ∀ (r s : ι), ℓ s < ℓ r + j → X r s = (0 : k));
    ∀ {k : Type u_1} [inst : Field k] {ι : Type u_2} [Fintype ι] [DecidableEq ι] {ℓ : ι → ℕ}
      {i j : ℕ} {X : Matrix ι ι k}, d1 ℓ j X → i ≤ j → d1 ℓ i X) := by
  intro d1 k _ ι _ _ ℓ i j X h hij r s hrs
  exact h r s (by omega)

end GlobalTheory.BandMonotonicity
end

section

namespace GlobalTheory.StrictUpperNilpotent

theorem pow_apply_eq_zero_of_strictUpper {L : Type} [inst : Field L] {n : ℕ}
    {y : Matrix (Fin n) (Fin n) L} (hy : ∀ (i j : Fin n), j ≤ i → y i j = (0 : L)) :
    ∀ (k : ℕ) (i j : Fin n), (↑j : ℕ) < (↑i : ℕ) + k → (y ^ k) i j = (0 : L) := by
  intro k
  induction k with
  | zero =>
    intro i j h
    have hne : i ≠ j := by
      rintro rfl
      simp at h
    rw [pow_zero, Matrix.one_apply_ne hne]
  | succ k ih =>
    intro i j h
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : (l : ℕ) < (i : ℕ) + k
    · rw [ih i l hl, zero_mul]
    · have hjl : j ≤ l := by
        rw [Fin.le_def]
        omega
      rw [hy l j hjl, mul_zero]

end GlobalTheory.StrictUpperNilpotent
end

section

universe u_1 u_2

namespace GlobalTheory.BandLemmaThird

theorem main : (let d1 : {k : Type u_1} → [Field k] → {ι : Type u_2} → (ι → ℕ) → ℕ → Matrix ι ι k → Prop := @(fun {k : Type u_1} [Field k] {ι : Type u_2} (ℓ : ι → ℕ) (j : ℕ) (X : Matrix ι ι k) ↦ ∀ (r s : ι), ℓ s < ℓ r + j → X r s = (0 : k)); ∀ {k : Type u_1} [inst : Field k] {ι : Type u_2} [inst_1 : Fintype ι] [DecidableEq ι] {ℓ : ι → ℕ} {i j : ℕ} {X Y : Matrix ι ι k}, d1 ℓ i X → d1 ℓ j Y → d1 ℓ (i + j) (X * Y)) := by
  intro d1 k _ ι _ _ ℓ i j X Y hX hY r s hrs
  show (X * Y) r s = 0
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun t _ => ?_
  by_cases h : ℓ t < ℓ r + i
  · rw [hX r t h, zero_mul]
  · rw [hY t s (by omega), mul_zero]

end GlobalTheory.BandLemmaThird
end

section

open Matrix

namespace GlobalTheory

theorem finite_joint_eigensystems : ∀ (K : Type) [Field K] (n : ℕ) (ι : Type) (A : ι → Matrix (Fin n) (Fin n) K), (∀ i j, Commute (A i) (A j)) → Set.Finite {χ : ι → K | ∃ c : Fin n → K, c ≠ 0 ∧ ∀ i, A i *ᵥ c = χ i • c} := by
  intro K _ n ι A hc
  let f : ι → Module.End K (Fin n → K) := fun i => Matrix.toLin' (A i)
  have hcf : ∀ i j, Commute (f i) (f j) := by
    intro i j
    exact (hc i j).map Matrix.toLinAlgEquiv'
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcf j i) φ)
  refine (WellFoundedGT.finite_ne_bot_of_iSupIndep hind).subset ?_
  rintro χ ⟨c, hc0, hχ⟩
  show (⨅ i, (f i).maxGenEigenspace (χ i)) ≠ ⊥
  intro hbot
  apply hc0
  have hmem : c ∈ ⨅ i, (f i).maxGenEigenspace (χ i) := by
    rw [Submodule.mem_iInf]
    intro i
    apply Module.End.eigenspace_le_maxGenEigenspace
    rw [Module.End.mem_eigenspace_iff]
    simpa [f] using hχ i
  rw [hbot] at hmem
  exact (Submodule.mem_bot K).mp hmem

end GlobalTheory
end

section

open scoped BigOperators Matrix
open Polynomial

namespace GlobalTheory


open scoped BigOperators Matrix in
open Polynomial in
theorem _root_.GlobalTheory.eigenvector_mem_span_twistedTrace_image :
    ∀ (H K V : Type) [Group H] [Fintype H] [Field K] [CharZero K] [AddCommGroup V] [Module K V] (st : H → V →ₗ[K] V), (∀ h h' x, st (h * h') x = st h' (st h x)) → ∀ (χ : H →* Kˣ) (s : Set V), Submodule.span K s = ⊤ → ∀ x : V, (∀ h, st h x = ((χ h : Kˣ) : K) • x) → x ∈ Submodule.span K ((fun y => ∑ h, (((χ h)⁻¹ : Kˣ) : K) • st h y) '' s) := by
  intro H K V _ _ _ _ _ _ st _ χ s hs x hx
  let P : V →ₗ[K] V := ∑ h, (((χ h)⁻¹ : Kˣ) : K) • st h
  have hP : (fun y => ∑ h, (((χ h)⁻¹ : Kˣ) : K) • st h y) = ⇑P := by
    funext y
    simp [P, LinearMap.sum_apply]
  have hPx : P x = (Fintype.card H : K) • x := by
    rw [← hP]
    simp only [hx, smul_smul, Units.inv_mul, one_smul, Finset.sum_const, Finset.card_univ]
    rw [Nat.cast_smul_eq_nsmul]
  have hcard : (Fintype.card H : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hxP : x = P ((Fintype.card H : K)⁻¹ • x) := by
    rw [map_smul, hPx, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  rw [hP, Submodule.span_image, hs, hxP]
  exact Submodule.mem_map_of_mem Submodule.mem_top

end GlobalTheory
end
