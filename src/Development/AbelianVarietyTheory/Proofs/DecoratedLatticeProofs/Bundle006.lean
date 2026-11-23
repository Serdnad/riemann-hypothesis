module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Algebra.Valued.ValuativeRel
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
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
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

@[expose] public section

section

namespace GlobalTheory

theorem finiteDimensional_span_multilinear_values :
    ∀ {ι : Type} [Fintype ι] (E : ι → Type) [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
      (F : Type) [AddCommGroup F] [Module ℂ F] (T : (∀ i, E i) →ₘₗ[ℂ] F)
      (W : ∀ i, Submodule ℂ (E i)), (∀ i, FiniteDimensional ℂ (W i)) →
      FiniteDimensional ℂ (Submodule.span ℂ {f | ∃ v : ∀ i, E i, (∀ i, v i ∈ W i) ∧ f = T v}) := by
  intro ι _ E _ _ F _ _ T W hW
  have := hW
  let T' : (∀ i, W i) →ₘₗ[ℂ] F := T.compLinearMap (fun i => (W i).subtype)
  have hset : {f | ∃ v : ∀ i, E i, (∀ i, v i ∈ W i) ∧ f = T v} = Set.range T' := by
    ext f
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨fun i => ⟨v i, hv i⟩, rfl⟩
    · rintro ⟨w, rfl⟩
      exact ⟨fun i => (w i : E i), fun i => (w i).2, rfl⟩
  have hle : Submodule.span ℂ (Set.range T') ≤ LinearMap.range (PiTensorProduct.lift T') := by
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    exact ⟨PiTensorProduct.tprod ℂ w, by simp⟩
  rw [hset]
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory
end

section

namespace GlobalTheory.PositiveIffLtCard

theorem pos_iff_lt_card {N : ℕ} {e : Fin N → ℤ} (he : Antitone e) (i : Fin N) :
    (0 : ℤ) < e i ↔ (i : ℕ) < Finset.card {j : Fin N | (0 : ℤ) < e j} := by
  constructor
  · intro h
    have hsub : Finset.Iic i ⊆ ({j : Fin N | (0 : ℤ) < e j} : Finset (Fin N)) := by
      intro j hj
      rw [Finset.mem_Iic] at hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact lt_of_lt_of_le h (he hj)
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hc
    omega
  · intro h
    by_contra hn
    have hsub : ({j : Fin N | (0 : ℤ) < e j} : Finset (Fin N)) ⊆ Finset.Iio i := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      rw [Finset.mem_Iio]
      by_contra hji
      exact hn (lt_of_lt_of_le hj (he (not_lt.mp hji)))
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hc
    omega

end GlobalTheory.PositiveIffLtCard
end

section

namespace GlobalTheory.ShiftVariables

noncomputable def shiftVars (ι k : Type) [CommRing k] :
    MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k :=
  AlgEquiv.ofAlgHom
    (MvPolynomial.aeval fun i => MvPolynomial.X i + 1)
    (MvPolynomial.aeval fun i => MvPolynomial.X i - 1)
    (by ext1 i; simp) (by ext1 i; simp)

theorem shiftVars_X (ι k : Type) [CommRing k] (i : ι) :
    shiftVars ι k (MvPolynomial.X i) = MvPolynomial.X i + 1 := by
  change MvPolynomial.aeval (fun i => MvPolynomial.X i + 1) (MvPolynomial.X i) = _
  simp

theorem exists_ringEquiv_add_one {Ω : Type} [Field Ω] [IsAlgClosed Ω] (k : Subfield Ω) (c : Ω)
    (hc : Transcendental (↥k) c) :
    ∃ (σ : Ω ≃+* Ω), (∀ a ∈ k, (σ : Ω → Ω) a = a) ∧ (σ : Ω → Ω) c = c + (1 : Ω) := by
  classical
  have hs : AlgebraicIndepOn (↥k) id ({c} : Set Ω) :=
    algebraicIndependent_unique_type_iff.mpr (by simpa using hc)
  obtain ⟨t, hct, ht⟩ := exists_isTranscendenceBasis_superset hs
  have hind : AlgebraicIndependent (↥k) ((↑) : t → Ω) := ht.1
  set K := IntermediateField.adjoin (↥k) (Set.range ((↑) : t → Ω)) with hK
  let e := hind.aevalEquivField
  let φ : FractionRing (MvPolynomial t ↥k) ≃ₐ[↥k] FractionRing (MvPolynomial t ↥k) :=
    IsFractionRing.algEquivOfAlgEquiv (K := FractionRing (MvPolynomial t ↥k))
      (L := FractionRing (MvPolynomial t ↥k)) (shiftVars t ↥k)
  let τ : K ≃ₐ[↥k] K := e.symm.trans (φ.trans e)
  have hmem : ∀ i : t, (i : Ω) ∈ K := fun i =>
    IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
  have he : ∀ i : t, e (algebraMap (MvPolynomial t ↥k) _ (MvPolynomial.X i)) = ⟨i, hmem i⟩ := by
    intro i
    apply Subtype.ext
    rw [hind.aevalEquivField_algebraMap_apply_coe]
    simp
  have he1 : ∀ i : t, e (algebraMap (MvPolynomial t ↥k) _ (MvPolynomial.X i + 1)) =
      ⟨i, hmem i⟩ + 1 := by
    intro i
    apply Subtype.ext
    rw [hind.aevalEquivField_algebraMap_apply_coe]
    simp
  have hτ : ∀ i : t, τ ⟨i, hmem i⟩ = ⟨i, hmem i⟩ + 1 := by
    intro i
    have h0 : e.symm ⟨i, hmem i⟩ = algebraMap (MvPolynomial t ↥k) _ (MvPolynomial.X i) := by
      rw [AlgEquiv.symm_apply_eq, he]
    change e (φ (e.symm ⟨i, hmem i⟩)) = _
    rw [h0, IsFractionRing.algEquivOfAlgEquiv_algebraMap, shiftVars_X, he1]
  have : Algebra.IsAlgebraic K Ω := ht.isAlgebraic_field
  have : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  let σ : Ω ≃+* Ω := IsAlgClosure.equivOfEquiv Ω Ω τ.toRingEquiv
  have hσ : ∀ y : K, σ (y : Ω) = (τ y : Ω) := fun y =>
    IsAlgClosure.equivOfEquiv_algebraMap Ω Ω τ.toRingEquiv y
  refine ⟨σ, fun a ha => ?_, ?_⟩
  · have hak : a ∈ K := IntermediateField.algebraMap_mem K (⟨a, ha⟩ : ↥k)
    have h1 := hσ ⟨a, hak⟩
    have h2 : τ ⟨a, hak⟩ = ⟨a, hak⟩ := τ.commutes (⟨a, ha⟩ : ↥k)
    rw [h2] at h1
    exact h1
  · have hc' : c ∈ t := hct rfl
    have h1 := hσ ⟨c, hmem ⟨c, hc'⟩⟩
    rw [hτ ⟨c, hc'⟩] at h1
    simpa using h1

end GlobalTheory.ShiftVariables
end

section

namespace GlobalTheory.IndexComapCosets

theorem index_comap_eq_of_cosets_hit {A B : Type} [Group A] [Group B] (f : A →* B)
    (H : Subgroup B) (h : ∀ b : B, ∃ a : A, (f a)⁻¹ * b ∈ H) :
    (H.comap f).index = H.index := by
  rw [Subgroup.index_eq_card, Subgroup.index_eq_card]
  let φ : A ⧸ H.comap f → B ⧸ H :=
    Quotient.map' f (fun a a' hr => by
      rw [QuotientGroup.leftRel_apply] at hr ⊢
      simpa using hr)
  have hφ : ∀ a : A, φ (a : A ⧸ H.comap f) = (f a : B ⧸ H) := fun a => rfl
  have hinj : Function.Injective φ := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective y
    rw [hφ, hφ, QuotientGroup.eq] at hxy
    rw [QuotientGroup.eq, Subgroup.mem_comap, map_mul, map_inv]
    exact hxy
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨a, ha⟩ := h b
    exact ⟨a, by rw [hφ, QuotientGroup.eq]; exact ha⟩
  exact Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩)

end GlobalTheory.IndexComapCosets
end

section

open Matrix

namespace GlobalTheory

theorem matrix_stableRange_one (κ : Type) [Field κ] (n : ℕ) (c d p q : Matrix (Fin n) (Fin n) κ)
    (h : c * p + d * q = 1) : ∃ y : Matrix (Fin n) (Fin n) κ, (c * y + d).det ≠ 0 := by
  classical
  set C := Matrix.toLin' c with hC
  set D := Matrix.toLin' d with hD
  obtain ⟨Wc, hW⟩ := Submodule.exists_isCompl (LinearMap.range D)
  let π := Submodule.linearProjOfIsCompl Wc (LinearMap.range D) hW.symm
  have hdec : ∀ w : Fin n → κ, C (p *ᵥ w) + D (q *ᵥ w) = w := by
    intro w
    simp only [hC, hD, Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, h,
      Matrix.one_mulVec]
  have hπD : ∀ v, π (D v) = 0 := by
    intro v
    exact Submodule.linearProjOfIsCompl_apply_right hW.symm ⟨D v, LinearMap.mem_range_self _ _⟩
  have hsurj : Function.Surjective (π ∘ₗ C) := by
    intro w
    refine ⟨p *ᵥ (w : Fin n → κ), ?_⟩
    have h2 : π (w : Fin n → κ) = w := Submodule.linearProjOfIsCompl_apply_left _ w
    have := congrArg π (hdec w)
    rw [map_add (f := _), hπD, add_zero, h2] at this
    simpa using this
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective (π ∘ₗ C)
    (LinearMap.range_eq_top.mpr hsurj)
  have hdim : Module.finrank κ (LinearMap.ker D) = Module.finrank κ Wc := by
    have h1 := LinearMap.finrank_range_add_finrank_ker D
    have h2 := Submodule.finrank_add_eq_of_isCompl hW
    simp only [Module.finrank_fin_fun] at h1 h2
    omega
  let e := LinearEquiv.ofFinrankEq _ _ hdim
  obtain ⟨K', hK⟩ := Submodule.exists_isCompl (LinearMap.ker D)
  let projK := Submodule.linearProjOfIsCompl (LinearMap.ker D) K' hK
  let Y : (Fin n → κ) →ₗ[κ] (Fin n → κ) := g ∘ₗ (e : LinearMap.ker D →ₗ[κ] Wc) ∘ₗ projK
  refine ⟨LinearMap.toMatrix' Y, ?_⟩
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hM : (c * LinearMap.toMatrix' Y + d) *ᵥ v = C (Y v) + D v := by
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]
    rfl
  rw [hM] at hv
  have hp : π (C (Y v)) = e (projK v) := by
    have := LinearMap.congr_fun hg (e (projK v))
    simpa [Y] using this
  have h3 : e (projK v) = 0 := by
    have := congrArg π hv
    rwa [map_add, hπD, add_zero, hp, map_zero] at this
  have hk : projK v = 0 := (LinearEquiv.map_eq_zero_iff e).mp h3
  have hY : Y v = 0 := by
    change g (e.toLinearMap (projK v)) = 0
    rw [hk, map_zero]
    exact map_zero g
  have hDv : D v = 0 := by rw [hY, map_zero, zero_add] at hv; exact hv
  have hvK : v ∈ LinearMap.ker D := hDv
  have h4 := Submodule.linearProjOfIsCompl_apply_left hK ⟨v, hvK⟩
  have : (⟨v, hvK⟩ : LinearMap.ker D) = 0 := by rw [← h4]; exact hk
  exact hv0 (congrArg Subtype.val this)

theorem matrix_stableRange_one' : ∀ (κ : Type) [Field κ] (n : ℕ) (c d p q : Matrix (Fin n) (Fin n) κ),
    c * p + d * q = 1 → ∃ y : Matrix (Fin n) (Fin n) κ, (c * y + d).det ≠ 0 :=
  fun κ _ n c d p q h => matrix_stableRange_one κ n c d p q h

end GlobalTheory
end

section

namespace GlobalTheory.SymRes

def FreePos (ρ κ i j : ℕ) : Prop :=
  (i < κ ∧ j < κ ∧ i < j) ∨ (κ ≤ i ∧ i < κ + ρ ∧ j < κ) ∨ (i < κ ∧ κ + ρ < j) ∨ (κ ≤ i ∧ i < j)

def IsPat {K : Type} [CommRing K] {r : ℕ} (ρ κ : ℕ) (g : GL (Fin r) K) : Prop :=
  ∀ i j : Fin r, ¬ FreePos ρ κ i.val j.val → g.val i j = (1 : Matrix (Fin r) (Fin r) K) i j

theorem isPat_one {K : Type} [CommRing K] {r : ℕ} (ρ κ : ℕ) : IsPat ρ κ (1 : GL (Fin r) K) := fun _ _ _ => rfl

end GlobalTheory.SymRes
end

section

noncomputable section

open Matrix ValuativeRel

namespace GlobalTheory.PenVol

variable {k n : Type} [Field k] [ValuativeRel k] [Fintype n] [DecidableEq n]

theorem toBlocks_mul_fin_zero (g h : Matrix (n ⊕ Fin 0) (n ⊕ Fin 0) k) :
    (g * h).toBlocks₁₁ = g.toBlocks₁₁ * h.toBlocks₁₁ := by
  ext a b
  simp [Matrix.toBlocks₁₁, Matrix.mul_apply, Fintype.sum_sum_type]

theorem toBlocks_one_fin_zero : (1 : Matrix (n ⊕ Fin 0) (n ⊕ Fin 0) k).toBlocks₁₁ = 1 := by
  ext a b
  simp [Matrix.toBlocks₁₁, Matrix.one_apply]

def cosStab (J : Subgroup (GL (n ⊕ Fin 0) k)) (M : Submodule 𝒪[k] (n → k)) (c : (n → k) ⧸ M) :
    Subgroup (GL (n ⊕ Fin 0) k) where
  carrier := {g | g ∈ J ∧ ∀ y : n → k,
    (Submodule.Quotient.mk (g.val.toBlocks₁₁ *ᵥ y) : (n → k) ⧸ M) = c ↔ Submodule.Quotient.mk y = c}
  mul_mem' := by
    rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
    refine ⟨J.mul_mem hg hh, fun y => ?_⟩
    rw [show (g * h).val = g.val * h.val from rfl, toBlocks_mul_fin_zero, ← Matrix.mulVec_mulVec, hg', hh']
  one_mem' := ⟨J.one_mem, fun y => by
    rw [show (1 : GL (n ⊕ Fin 0) k).val = 1 from rfl, toBlocks_one_fin_zero, Matrix.one_mulVec]⟩
  inv_mem' := by
    rintro g ⟨hg, hg'⟩
    refine ⟨J.inv_mem hg, fun y => ?_⟩
    have e : g.val.toBlocks₁₁ *ᵥ ((g⁻¹ : GL (n ⊕ Fin 0) k).val.toBlocks₁₁ *ᵥ y) = y := by
      rw [Matrix.mulVec_mulVec, ← toBlocks_mul_fin_zero, show g.val * (g⁻¹ : GL (n ⊕ Fin 0) k).val = 1 from g.mul_inv,
        toBlocks_one_fin_zero, Matrix.one_mulVec]
    rw [← hg', e]

theorem mem_cosStab {J : Subgroup (GL (n ⊕ Fin 0) k)} {M : Submodule 𝒪[k] (n → k)} {c : (n → k) ⧸ M}
    {g : GL (n ⊕ Fin 0) k} : g ∈ cosStab J M c ↔ g ∈ J ∧ ∀ y : n → k,
      (Submodule.Quotient.mk (g.val.toBlocks₁₁ *ᵥ y) : (n → k) ⧸ M) = c ↔ Submodule.Quotient.mk y = c := Iff.rfl

theorem cosStab_le (J : Subgroup (GL (n ⊕ Fin 0) k)) (M : Submodule 𝒪[k] (n → k)) (c : (n → k) ⧸ M) :
    cosStab J M c ≤ J := fun _ h => h.1

end GlobalTheory.PenVol

end
end

section

open MeasureTheory

namespace GlobalTheory.ChainOnto

theorem map_restrict_isHaar : ∀ (G B : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [MeasurableSpace B] [BorelSpace B] [T2Space B] (ν : Measure G) [ν.IsHaarMeasure] (A : Subgroup G) (i : B →* G) (p : G →* B), IsOpen (A : Set G) → Continuous i → Continuous p → (∀ b, p (i b) = b) → (∀ b, i b ∈ A) → IsCompact {g : G | g ∈ A ∧ p g = 1} → (Measure.map p (ν.restrict A)).IsHaarMeasure := by
  intro G B _ _ _ _ _ _ _ _ _ _ _ ν _ A i p hA hi hp hpi hiA hK
  have hpm : Measurable p := hp.measurable
  have hAm : MeasurableSet (A : Set G) := hA.measurableSet
  have happ : ∀ S : Set B, MeasurableSet S → Measure.map p (ν.restrict A) S = ν (p ⁻¹' S ∩ A) := by
    intro S hS
    rw [Measure.map_apply hpm hS, Measure.restrict_apply (hpm hS)]

  have hpre : ∀ S : Set B, p ⁻¹' S ∩ A = (fun x : G × G => x.1 * x.2) '' ((i '' S) ×ˢ {g : G | g ∈ A ∧ p g = 1}) := by
    intro S
    ext g
    constructor
    · rintro ⟨hgS, hgA⟩
      refine ⟨(i (p g), (i (p g))⁻¹ * g), ⟨⟨p g, hgS, rfl⟩, ?_, ?_⟩, by simp⟩
      · exact A.mul_mem (A.inv_mem (hiA _)) hgA
      · simp [hpi]
    · rintro ⟨⟨x, y⟩, ⟨⟨s, hs, rfl⟩, hyA, hy1⟩, rfl⟩
      refine ⟨?_, A.mul_mem (hiA s) hyA⟩
      simp [hpi, hy1, hs]
  refine { lt_top_of_isCompact := ?_, map_mul_left_eq_self := ?_, open_pos := ?_ }
  · intro C hC
    rw [happ C hC.isClosed.measurableSet, hpre C]
    exact ((hC.image hi).prod hK).image continuous_mul |>.measure_lt_top
  · intro b
    ext S hS
    rw [Measure.map_apply (measurable_const_mul b) hS, happ _ (measurable_const_mul b hS), happ S hS]
    have : p ⁻¹' ((fun x => b * x) ⁻¹' S) ∩ A = (fun g => i b * g) ⁻¹' (p ⁻¹' S ∩ A) := by
      ext g
      simp only [Set.mem_inter_iff, Set.mem_preimage, map_mul, hpi, SetLike.mem_coe]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, A.mul_mem (hiA b) h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        have := A.mul_mem (A.inv_mem (hiA b)) h2
        simpa using this
    rw [this, measure_preimage_mul]
  · intro U hU hne
    rw [happ U hU.measurableSet]
    obtain ⟨u, hu⟩ := hne
    exact (hU.preimage hp |>.inter hA).measure_ne_zero ν ⟨i u, by simp [hpi, hu], hiA u⟩

end GlobalTheory.ChainOnto
end

section

namespace GlobalTheory.FiniteGenIntegerScalar

theorem exists_int_smul_mem_of_fg {E : Type} [Field E] {V : Type} [AddCommGroup V]
    [Module (NumberField.RingOfIntegers E) V]
    {L M : Submodule (NumberField.RingOfIntegers E) V}
    (h : ∀ x : V, ∃ N : ℤ, N ≠ 0 ∧ N • x ∈ L) (hM : M.FG) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ x ∈ M, N • x ∈ L := by
  classical
  obtain ⟨S, rfl⟩ := hM
  choose f hf0 hfL using h
  refine ⟨∏ s ∈ S, f s, Finset.prod_ne_zero_iff.mpr fun s _ => hf0 s, ?_⟩
  intro x hx
  let P : Submodule (NumberField.RingOfIntegers E) V :=
    { carrier := {y | (∏ s ∈ S, f s) • y ∈ L}
      add_mem' := fun {a b} ha hb => by
        show _ ∈ L
        rw [smul_add]
        exact L.add_mem ha hb
      zero_mem' := by
        show _ ∈ L
        rw [smul_zero]
        exact L.zero_mem
      smul_mem' := fun c y hy => by
        show _ ∈ L
        rw [smul_comm (∏ s ∈ S, f s) c y]
        exact L.smul_mem c hy }
  have hle : Submodule.span _ (S : Set V) ≤ P := by
    rw [Submodule.span_le]
    intro s hs
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem f hs
    show (∏ s ∈ S, f s) • s ∈ L
    rw [hk, mul_comm, mul_smul]
    exact zsmul_mem (hfL s) k
  exact hle hx

end GlobalTheory.FiniteGenIntegerScalar
end

section

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.PhiOneVal

def ColCond {E : Type} [Field E] [NumberField E] {a b : ℕ} (P : HeightOneSpectrum (𝓞 E)) (t : 𝓞 E)
    (x : (Fin a → E) →ₗ[E] (Fin b → E)) : Prop :=
  ∀ r : Fin a, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ c : Fin b → 𝓞 E,
    (∀ q, algebraMap (𝓞 E) E (c q) = algebraMap (𝓞 E) E s * x (Pi.single r 1) q) ∧
    ∀ q : Fin b, q.1 + 1 = b → t * (c q - if r.1 + 1 = a then s else 0) ∈ P.asIdeal

end GlobalTheory.PhiOneVal
end
end
