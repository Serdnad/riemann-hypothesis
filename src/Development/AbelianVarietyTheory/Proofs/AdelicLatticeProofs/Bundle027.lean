module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.SupportedAtSplit
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq
public import Formalism.UnipotentAdelicQuotients.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle014
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.DFinsupp
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle016
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle017
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RepresentationTheory.Semisimple
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle015
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
public import Mathlib.Analysis.Real.Sqrt
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001

@[expose] public section

section

noncomputable section

namespace GlobalTheory.UnRep.Compare

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceUnitaryEvaluation
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem evalAt_apply (v : HeightOneSpectrum (𝓞 F)) (a : FiniteAdeleRing (𝓞 F) F) : evalAt v a = a v := rfl

theorem loc_tmul (v : HeightOneSpectrum (𝓞 F)) (a : FiniteAdeleRing (𝓞 F) F) (x : E) :
    loc E v (a ⊗ₜ[F] x) = a v ⊗ₜ[F] x := rfl

theorem eq_zero_of_loc {x : RA F E} (h : ∀ v, loc E v x = 0) : x = 0 := by
  let b := Module.Basis.ofVectorSpace F E
  have key : ∀ (v : HeightOneSpectrum (𝓞 F)) (i) (y : RA F E),
      (Algebra.TensorProduct.basis (FiniteAdeleRing (𝓞 F) F) b).repr y i v =
        (Algebra.TensorProduct.basis (v.adicCompletion F) b).repr (loc E v y) i := by
    intro v i y
    rw [← evalAt_apply]
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      rw [loc_tmul, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.basis_repr_tmul]
      simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgHom.commutes,
        evalAt_apply v a]
    | add s t hs ht => simp only [map_add (f := _), Finsupp.add_apply, hs, ht]
  apply (Algebra.TensorProduct.basis (FiniteAdeleRing (𝓞 F) F) b).repr.injective
  ext i : 1
  refine DFunLike.ext _ _ fun v => ?_
  rw [key, h, map_zero, map_zero]
  rfl

theorem eq_of_loc {x y : RA F E} (h : ∀ v, loc E v x = loc E v y) : x = y :=
  sub_eq_zero.1 (eq_zero_of_loc fun v => by rw [map_sub, h, sub_self])


open Classical in
def ind (S : Set (HeightOneSpectrum (𝓞 F))) : FiniteAdeleRing (𝓞 F) F :=
  ⟨fun w => if w ∈ S then 1 else 0, Filter.Eventually.of_forall fun w => by
    by_cases h : w ∈ S
    · simp only [if_pos h]; exact one_mem _
    · simp only [if_neg h]; exact zero_mem _⟩

theorem ind_pos {S : Set (HeightOneSpectrum (𝓞 F))} {w} (h : w ∈ S) : ind S w = 1 := if_pos h

theorem ind_neg {S : Set (HeightOneSpectrum (𝓞 F))} {w} (h : w ∉ S) : ind S w = 0 := if_neg h

theorem loc_ind_pos {S : Set (HeightOneSpectrum (𝓞 F))} {w} (h : w ∈ S) :
    loc E w (ind S ⊗ₜ[F] (1 : E)) = 1 := by rw [loc_tmul, ind_pos h]; rfl

theorem isSplitPlace_of_splitPl (c : E ≃ₐ[F] E) {v : HeightOneSpectrum (𝓞 F)} (h : SplitPl c v) :
    IsSplitPlace E v := by
  obtain ⟨P, hP, hPv, a, ha, b, hb, hbP⟩ := h
  let σ : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv c.toRingEquiv
  have hσ : ∀ x : 𝓞 E, ((σ x : 𝓞 E) : E) = c x := fun _ => rfl
  refine ⟨P, P.comap σ, fun h => hbP ?_, hP, inferInstance, hPv, ?_⟩
  · rw [h, Ideal.mem_comap] at ha
    rwa [show b = σ a from Subtype.ext hb]
  · rw [← hPv]
    ext x
    have : σ (algebraMap (𝓞 F) (𝓞 E) x) = algebraMap (𝓞 F) (𝓞 E) x :=
      Subtype.ext (c.commutes (x : F))
    simp only [Ideal.mem_comap, this]

theorem aut_eq (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) (σ : E ≃ₐ[F] E) :
    σ = 1 ∨ σ = c := by
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  have hcard : Nat.card (E ≃ₐ[F] E) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard
  by_cases h : σ = 1
  · exact Or.inl h
  · exact Or.inr ((hy σ h).trans (hy c hc).symm)

theorem conj_conj (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) (x : E) : c (c x) = x := by
  rcases aut_eq c h2 hc (c * c) with h | h
  · exact DFunLike.congr_fun h x
  · exact absurd (mul_eq_left.1 h) hc

theorem moved_of_not_le (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    {P Q : Ideal (𝓞 E)} (hQ : Q.IsPrime)
    (h : P.comap (algebraMap (𝓞 F) (𝓞 E)) = Q.comap (algebraMap (𝓞 F) (𝓞 E))) (hPQ : ¬ P ≤ Q) :
    Moved c Q := by
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  obtain ⟨a, haP, haQ⟩ := Set.not_subset.1 hPQ
  let σ : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv c.toRingEquiv
  have hσ : ∀ x : 𝓞 E, ((σ x : 𝓞 E) : E) = c x := fun _ => rfl
  obtain ⟨m, hm⟩ : ((a * σ a : 𝓞 E) : E) ∈ Set.range (algebraMap F E) := by
    rw [IsGalois.mem_range_algebraMap_iff_fixed]
    intro f
    rcases aut_eq c h2 hc f with rfl | rfl
    · rfl
    · change f ((a : E) * f a) = (a : E) * f a
      rw [map_mul, conj_conj f h2 hc, mul_comm]
  have hint : IsIntegral ℤ m := by
    rw [← isIntegral_algebraMap_iff (B := E) , hm]
    exact (a * σ a).2
  obtain ⟨m', hm'⟩ : ∃ m' : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) m' = a * σ a := ⟨⟨m, hint⟩, Subtype.ext hm⟩
  have h1 : a * σ a ∈ Q := by
    rw [← hm', ← Ideal.mem_comap, ← h, Ideal.mem_comap, hm']
    exact P.mul_mem_right _ haP
  exact ⟨σ a, (hQ.mem_or_mem h1).resolve_left haQ, a, (conj_conj c h2 hc _).symm, haQ⟩

theorem splitPl_iff (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (v : HeightOneSpectrum (𝓞 F)) : SplitPl c v ↔ IsSplitPlace E v := by
  refine ⟨isSplitPlace_of_splitPl c, ?_⟩
  rintro ⟨w, w', hne, hw, hw', h, h'⟩
  by_cases hle : w ≤ w'
  · exact ⟨w, hw, h, moved_of_not_le c h2 hc hw (h'.trans h.symm) fun h => hne (le_antisymm hle h)⟩
  · exact ⟨w', hw', h', moved_of_not_le c h2 hc hw' (h.trans h'.symm) hle⟩

theorem support_iff (p : HeightOneSpectrum (𝓞 F) → Prop) {n : ℕ} (h : Matrix (Fin n) (Fin n) (RA F E)) :
    (∃ e : FiniteAdeleRing (𝓞 F) F, e * e = e ∧ {v | e v ≠ 0}.Finite ∧
      (∀ v, e v ≠ 0 → p v) ∧ (e ⊗ₜ[F] (1 : E)) • (h - 1) = h - 1) ↔
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), (∀ v ∈ T, p v) ∧ ∀ v ∉ T, h.map (loc E v) = 1 := by
  have hone : ∀ v : HeightOneSpectrum (𝓞 F), h.map (loc E v) = 1 ↔ ∀ i j, loc E v ((h - 1) i j) = 0 := by
    intro v
    rw [← Matrix.map_one (loc E v) (map_zero _) (map_one _), ← Matrix.ext_iff]
    simp only [Matrix.map_apply, Matrix.sub_apply, map_sub, sub_eq_zero]
  constructor
  · rintro ⟨e, -, hfin, hp, he⟩
    refine ⟨hfin.toFinset, fun v hv => hp v (hfin.mem_toFinset.1 hv), fun v hv => (hone v).2 fun i j => ?_⟩
    have h0 : e v = 0 := by
      by_contra h0
      exact hv (hfin.mem_toFinset.2 h0)
    rw [← he, Matrix.smul_apply, smul_eq_mul, map_mul, loc_tmul, h0, TensorProduct.zero_tmul, zero_mul]
  · rintro ⟨T, hp, hT⟩
    have hs : ∀ v, ind (T : Set (HeightOneSpectrum (𝓞 F))) v ≠ 0 → v ∈ T := fun v hv => by
      by_contra h0
      exact hv (ind_neg h0)
    refine ⟨ind T, ?_, T.finite_toSet.subset hs, fun v hv => hp v (hs v hv), ?_⟩
    · refine DFunLike.ext _ _ fun v => ?_
      change ind _ v * ind _ v = ind _ v
      by_cases hv : v ∈ (T : Set (HeightOneSpectrum (𝓞 F)))
      · rw [ind_pos hv, one_mul]
      · rw [ind_neg hv, zero_mul]
    · ext i j
      refine eq_of_loc fun v => ?_
      rw [Matrix.smul_apply, smul_eq_mul, map_mul]
      by_cases hv : v ∈ (T : Set (HeightOneSpectrum (𝓞 F)))
      · rw [loc_ind_pos hv, one_mul]
      · rw [(hone v).1 (hT v hv), mul_zero]


end GlobalTheory.UnRep.Compare
end
end

section

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep

theorem exists_anisotropic_orthogonal_basis :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G →
      ∃ x : Fin n → Fin n → E, (∀ i, hermE c G (x i) (x i) ≠ 0) ∧
        (∀ i j, i ≠ j → hermE c G (x i) (x j) = 0) ∧ Submodule.span E (Set.range x) = ⊤ := by
  intro F E _ _ _ _ _ c n G ⟨hc, _, hG, hdet⟩
  let σ : E →+* E := (c : E →+* E)
  have he : ∀ x y : Fin n → E, hermE c G x y = x ⬝ᵥ G *ᵥ (σ ∘ y) := fun x y =>
    (GlobalTheory.HermDiag.dotProduct_mulVec_comp_eq_sum σ G x y).symm
  obtain ⟨v, hv⟩ := GlobalTheory.HermDiag.exists_orthogonal_basis_dotProduct (c := σ) two_ne_zero hc hG
  have hd := GlobalTheory.HermDiag.congr_diagonal_of_orthogonal σ v hv
  refine ⟨v, fun i => ?_, fun i j hij => ?_, v.span_eq⟩
  · rw [he]
    exact GlobalTheory.HermDiag.ne_zero_of_congr_diagonal (GlobalTheory.HermDiag.det_of_basis_ne_zero v) hd hdet i
  · rw [he]
    exact hv i j hij

end GlobalTheory.UnRep
end

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory


open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical in
open scoped TensorProduct ContDiff nonZeroDivisors in
theorem _root_.GlobalTheory.isPrimeIdem_eq_indicator :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ Φ : _root_.HeckeCharacterZeroLocus.ThmBIn.AE F E ≃+* (mixedSpace E × FiniteAdeleRing (𝓞 E) E), (∀ x : E, Φ (_root_.HeckeCharacterZeroLocus.ThmBIn.incA F E x) = (mixedEmbedding E x, algebraMap E _ x)) → (∀ y, _root_.HeckeCharacterZeroLocus.ThmBIn.finPart F E y ∈ _root_.HeckeCharacterZeroLocus.ThmBIn.intAE F E ↔ ∀ P, Valued.v ((Φ y).2 P) ≤ 1) → (∀ v ε, _root_.HeckeCharacterZeroLocus.ThmBIn.IsPlaceIdem F v ε → (Φ (algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε)).1 = 0 ∧ ∀ P : HeightOneSpectrum (𝓞 E), (Φ (algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε)).2 P = if P.under (𝓞 F) = v then 1 else 0) → ∀ P e f, _root_.HeckeCharacterZeroLocus.ThmBIn.IsPrimeIdem σ P e f → ((Φ e).1 = 0 ∧ (Φ e).2 P = 1 ∧ ∀ Q, Q ≠ P → (Φ e).2 Q = 0) := by
  intro F E _ _ _ _ _ σ Φ hΦ hint hplace P e f hprime
  unfold _root_.HeckeCharacterZeroLocus.ThmBIn.IsPrimeIdem at hprime
  rcases hprime with ⟨hat, -⟩ | ⟨-, ⟨v, ε, hε, rfl⟩, hcrit⟩
  · unfold _root_.HeckeCharacterZeroLocus.ThmBIn.IsIdemAt _root_.HeckeCharacterZeroLocus.ThmBIn.IsSplitIdem at hat
    obtain ⟨⟨he, hce, v, ε, hε, hsum⟩, hcrit⟩ := hat
    have heε : e * algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε = e := by
      rw [← hsum, mul_add, he, hce, add_zero]
    exact (_root_.GlobalTheory.adele_idem_prime_criterion F E Φ hΦ hint hplace e P v ε hε he heε).mp hcrit
  · obtain ⟨h0, hind⟩ := hplace v ε hε
    have he : algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε * algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε =
        algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε := by
      apply Φ.injective
      rw [map_mul]
      refine Prod.ext ?_ ?_
      · rw [Prod.fst_mul, h0, mul_zero]
      · ext Q : 1
        change (Φ _).2 Q * (Φ _).2 Q = (Φ _).2 Q
        rw [hind Q]
        split_ifs <;> simp
    exact (_root_.GlobalTheory.adele_idem_prime_criterion F E Φ hΦ hint hplace _ P v ε hε he he).mp hcrit

end GlobalTheory
end

section

open NumberField IsDedekindDomain
open scoped Matrix WithZero

namespace GlobalTheory.LocalQuad

section Algebra

variable {k : Type*} [Field k]

theorem exists_norm_of_quaternary [CharZero k] {α β γ s : k} (hα : α ≠ 0) (hβ : β ≠ 0) (hγ : γ ≠ 0)
    (hs : s ^ 2 = α * β * γ) {x y z t : k} (h0 : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ t ≠ 0)
    (h : x ^ 2 - α * y ^ 2 - β * z ^ 2 + γ * t ^ 2 = 0) : ∃ X Y : k, β = X ^ 2 - α * Y ^ 2 := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact mul_ne_zero (mul_ne_zero hα hβ) hγ (by simpa using hs.symm)
  obtain ⟨u, hu⟩ : ∃ u, u = t * s / (α * β) := ⟨_, rfl⟩
  have hu2 : α * β * u ^ 2 = γ * t ^ 2 := by
    rw [hu, div_pow, mul_pow, hs]; field_simp
  have h1 : x ^ 2 - α * y ^ 2 = β * (z ^ 2 - α * u ^ 2) := by linear_combination h + hu2
  by_cases hD : z ^ 2 - α * u ^ 2 = 0
  · refine GlobalTheory.Published.HasseNormSt.of_isSquare hα ?_ β
    by_cases hu0 : u = 0
    · have hz : z = 0 := by simpa [hu0] using hD
      have ht : t = 0 := by
        have : γ * t ^ 2 = 0 := by rw [← hu2, hu0]; ring
        simpa [hγ] using this
      have hxy : x ^ 2 = α * y ^ 2 := by linear_combination h1 + β * hD
      have hy : y ≠ 0 := by
        rintro rfl
        have hx : x = 0 := by simpa using hxy
        simp [hx, hz, ht] at h0
      exact ⟨x / y, by field_simp; linear_combination -hxy⟩
    · exact ⟨z / u, by field_simp; linear_combination -hD⟩
  · refine ⟨(x * z + α * y * u) / (z ^ 2 - α * u ^ 2), (x * u + y * z) / (z ^ 2 - α * u ^ 2), ?_⟩
    field_simp
    linear_combination (-(z ^ 2 - α * u ^ 2)) * h1

theorem exists_quaternary_of_coordinates {α β γ : k} (hα : α ≠ 0) (hβ : β ≠ 0)
    {X₀ X₁ Y₀ Y₁ : k}
    (h1 : β = X₀ ^ 2 + α * β * γ * X₁ ^ 2 - α * (Y₀ ^ 2 + α * β * γ * Y₁ ^ 2))
    (h2 : X₀ * X₁ = α * (Y₀ * Y₁)) :
    ∃ x y z t : k, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ t ≠ 0) ∧
      x ^ 2 - α * y ^ 2 - β * z ^ 2 + γ * t ^ 2 = 0 := by
  by_cases hw : X₁ ^ 2 - α * Y₁ ^ 2 = 0
  · exact ⟨X₀, Y₀, 1, 0, by simp, by linear_combination -h1 - α * β * γ * hw⟩
  · refine ⟨-Y₁ * (α * β), -X₁ * β, -(X₀ * Y₁ - Y₀ * X₁) * α, (X₁ ^ 2 - α * Y₁ ^ 2) * (α * β),
      Or.inr (Or.inr (Or.inr (mul_ne_zero hw (mul_ne_zero hα hβ)))), ?_⟩
    linear_combination (-(α * β * (X₁ ^ 2 - α * Y₁ ^ 2))) * h1 - α * β * (X₀ * X₁ - α * (Y₀ * Y₁)) * h2

theorem isotropic_four_iff {a : Fin 4 → k} (ha : a 0 ≠ 0) :
    (∃ x : Fin 4 → k, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0) ↔
      ∃ x y z t : k, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ t ≠ 0) ∧
        x ^ 2 - (-(a 0 * a 1)) * y ^ 2 - (-(a 0 * a 2)) * z ^ 2 + (a 0 * a 3) * t ^ 2 = 0 := by
  constructor
  · rintro ⟨x, hx, h⟩
    rw [Fin.sum_univ_four] at h
    refine ⟨a 0 * x 0, x 1, x 2, x 3, ?_, by linear_combination a 0 * h⟩
    by_contra hc
    push Not at hc
    obtain ⟨h0, h1, h2, h3⟩ := hc
    apply hx
    funext i
    fin_cases i
    · simpa [ha] using h0
    · exact h1
    · exact h2
    · exact h3
  · rintro ⟨x, y, z, t, hx, h⟩
    refine ⟨![x / a 0, y, z, t], ?_, ?_⟩
    · intro hc
      have h0 := congrFun hc 0
      have h1 := congrFun hc 1
      have h2 := congrFun hc 2
      have h3 := congrFun hc 3
      simp [ha] at h0 h1 h2 h3
      simp [h0, h1, h2, h3] at hx
    · rw [Fin.sum_univ_four]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      field_simp
      linear_combination h

theorem isotropic_succ_iff {n : ℕ} {a : Fin (n + 1) → k} :
    (∃ x : Fin (n + 1) → k, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0) ↔
      ∃ (t : k) (z : Fin n → k), (t ≠ 0 ∨ z ≠ 0) ∧ a 0 * t ^ 2 + ∑ i, a i.succ * z i ^ 2 = 0 := by
  constructor
  · rintro ⟨x, hx, h⟩
    rw [Fin.sum_univ_succ] at h
    refine ⟨x 0, fun i => x i.succ, ?_, h⟩
    by_contra hc
    push Not at hc
    apply hx
    funext i
    refine Fin.cases hc.1 (fun j => congrFun hc.2 j) i
  · rintro ⟨t, z, hx, h⟩
    refine ⟨Fin.cons t z, ?_, by simpa [Fin.sum_univ_succ] using h⟩
    intro hc
    rcases hx with hx | hx
    · exact hx (by simpa using congrFun hc 0)
    · exact hx (funext fun i => by simpa using congrFun hc i.succ)

theorem exists_value_isotropic [CharZero k] {n : ℕ} {a a' : k} (ha : a ≠ 0) (ha' : a' ≠ 0)
    {b : Fin (n + 1) → k} (hb : b 0 ≠ 0) {x y : k} {z : Fin (n + 1) → k}
    (h0 : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) (h : a * x ^ 2 + (a' * y ^ 2 + ∑ i, b i * z i ^ 2) = 0) :
    ∃ x y : k, a * x ^ 2 + a' * y ^ 2 ≠ 0 ∧ ∀ μ : k, IsSquare (μ / (a * x ^ 2 + a' * y ^ 2)) →
      ∃ (t : k) (z : Fin (n + 1) → k), (t ≠ 0 ∨ z ≠ 0) ∧ μ * t ^ 2 + ∑ i, b i * z i ^ 2 = 0 := by
  have key : ∀ ν : k, ν ≠ 0 → ∀ z : Fin (n + 1) → k, ν + ∑ i, b i * z i ^ 2 = 0 →
      ∀ μ : k, IsSquare (μ / ν) →
      ∃ (t : k) (z : Fin (n + 1) → k), (t ≠ 0 ∨ z ≠ 0) ∧ μ * t ^ 2 + ∑ i, b i * z i ^ 2 = 0 := by
    rintro ν hν z hz μ ⟨s, hs⟩
    refine ⟨1, fun i => s * z i, Or.inl one_ne_zero, ?_⟩
    have : ∑ i, b i * (s * z i) ^ 2 = s ^ 2 * ∑ i, b i * z i ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [div_eq_iff hν] at hs
    rw [this, hs]
    linear_combination s ^ 2 * hz
  by_cases hμ : a * x ^ 2 + a' * y ^ 2 = 0
  · by_cases hz : z = 0
    · have hy : y ≠ 0 := by
        rintro rfl
        have hx : x = 0 := by simpa [ha] using hμ
        simp [hx, hz] at h0
      obtain ⟨X, Y, hXY⟩ := GlobalTheory.Published.HasseNormSt.of_isSquare (δ := -a' / a) (by simp [ha, ha'])
        ⟨x / y, by field_simp; linear_combination -hμ⟩ (-b 0 / a)
      have e : a * X ^ 2 + a' * Y ^ 2 = -b 0 := by
        field_simp at hXY
        linear_combination -hXY
      refine ⟨X, Y, by rw [e]; exact neg_ne_zero.2 hb, key _ (by rw [e]; exact neg_ne_zero.2 hb)
        (Pi.single 0 1) ?_⟩
      rw [e, Fin.sum_univ_succ]
      simp
    · refine ⟨1, 0, by simpa using ha, fun μ _ => ⟨0, z, Or.inr hz, ?_⟩⟩
      linear_combination h - hμ
  · exact ⟨x, y, hμ, key _ hμ z (by linear_combination h)⟩

theorem isotropic_of_injective {ι κ : Type*} [Fintype ι] [Fintype κ] (e : κ → ι)
    (he : Function.Injective e) {a : ι → k}
    (h : ∃ x : κ → k, x ≠ 0 ∧ ∑ j, a (e j) * x j ^ 2 = 0) :
    ∃ x : ι → k, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  classical
  obtain ⟨x, hx, h⟩ := h
  refine ⟨Function.extend e x 0, fun hc => hx (funext fun j => ?_), ?_⟩
  · simpa [he.extend_apply] using congrFun hc (e j)
  · rw [← h]
    symm
    refine Finset.sum_of_injOn e he.injOn (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_ ?_
    · intro i _ hi
      rw [Function.extend_apply' _ _ _ (by simpa using hi)]
      simp
    · intro j _
      rw [he.extend_apply]

theorem isotropic_real {ι : Type*} [Fintype ι] {a : ι → ℝ} {i j : ι} (hi : a i < 0) (hj : 0 < a j) :
    ∃ x : ι → ℝ, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  have hij : i ≠ j := by rintro rfl; linarith
  refine isotropic_of_injective ![i, j] ?_ ⟨![√(a j), √(-a i)], ?_, ?_⟩
  · intro p q h
    fin_cases p <;> fin_cases q <;> simp_all [eq_comm]
  · intro hc
    have := congrFun hc 0
    simp only [Matrix.cons_val_zero, Pi.zero_apply] at this
    exact (Real.sqrt_pos.2 hj).ne' this
  · rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Real.sq_sqrt hj.le, Real.sq_sqrt (by linarith)]
    ring

end Algebra

end GlobalTheory.LocalQuad
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.exists_rational_coord_polynomial_baseChange : ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (τ : Type) (P : MvPolynomial τ F), ∃ Q : β → MvPolynomial (τ × β) ℚ, ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → ∀ (x : τ → A) (k : β), b.repr (MvPolynomial.aeval x P) k = MvPolynomial.aeval (fun p : τ × β => b.repr (x p.1) p.2) (Q k) := by
  first | exact @GlobalTheory.ClassFin.exists_coord_polynomial | exact GlobalTheory.ClassFin.exists_coord_polynomial | (intros; apply GlobalTheory.ClassFin.exists_coord_polynomial <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.entries_bounded_of_conj_spanning_bounded' : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Type) [Fintype σ] (g : σ → Matrix ι ι ℂ), Submodule.span ℂ (Set.range g) = ⊤ → ∀ C : ℝ, ∃ C' : ℝ, ∀ P : Matrix ι ι ℂ, P.det = 1 → (∀ s i j, ‖(P * g s * P⁻¹) i j‖ ≤ C) → ∀ i j, ‖P i j‖ ≤ C' := by
  first | exact @GlobalTheory.ClassFin.entries_bounded_of_conj_spanning_bounded | exact GlobalTheory.ClassFin.entries_bounded_of_conj_spanning_bounded | (intros; apply GlobalTheory.ClassFin.entries_bounded_of_conj_spanning_bounded <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.exists_reynolds_of_completelyReducible' : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (S : Set (V →ₗ[ℂ] V)), (∀ U : Submodule ℂ V, (∀ s ∈ S, ∀ v ∈ U, s v ∈ U) → ∃ U' : Submodule ℂ V, (∀ s ∈ S, ∀ v ∈ U', s v ∈ U') ∧ IsCompl U U') → ∃ Rey : V →ₗ[ℂ] V, (∀ v, ∀ s ∈ S, s (Rey v) = Rey v) ∧ (∀ v, (∀ s ∈ S, s v = v) → Rey v = v) ∧ (∀ v, ∀ s ∈ S, Rey (s v) = Rey v) ∧ (∀ v, v - Rey v ∈ Submodule.span ℂ {x | ∃ s ∈ S, ∃ w, x = s w - w}) ∧ (∀ T : V →ₗ[ℂ] V, (∀ s ∈ S, ∀ v, T (s v) = s (T v)) → ∀ v, Rey (T v) = T (Rey v)) ∧ ∀ U : Submodule ℂ V, (∀ s ∈ S, ∀ v ∈ U, s v ∈ U) → ∀ v ∈ U, Rey v ∈ U := by
  first | exact @GlobalTheory.ClassFin.exists_reynolds_of_completelyReducible | exact GlobalTheory.ClassFin.exists_reynolds_of_completelyReducible | (intros; apply GlobalTheory.ClassFin.exists_reynolds_of_completelyReducible <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.isSemisimpleRepresentation_of_iSup_range_equivariant : ∀ (G : Type) [Group G] (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (J : Type) (V : J → Type) [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (r : ∀ j, Representation ℂ G (V j)) (p : ∀ j, V j →ₗ[ℂ] W), (∀ j, (r j).IsSemisimpleRepresentation) → (∀ j g v, p j (r j g v) = ρ g (p j v)) → (⨆ j, LinearMap.range (p j)) = ⊤ → ρ.IsSemisimpleRepresentation := by
  first | exact @GlobalTheory.ClassFin.isSemisimpleRepresentation_of_iSup_range | exact GlobalTheory.ClassFin.isSemisimpleRepresentation_of_iSup_range | (intros; apply GlobalTheory.ClassFin.isSemisimpleRepresentation_of_iSup_range <;> assumption)
end
