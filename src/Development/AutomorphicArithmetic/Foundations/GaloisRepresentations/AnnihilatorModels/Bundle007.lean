module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle239
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
public import Mathlib.RingTheory.Flat.TorsionFree
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.baseSmooth_of :
    SmoothClosed → SmoothReduced → BaseOfSmooth := by
  intro hC hR l O R _ _ _ _ _ _ ϖ hϖ hl _
  have hflat : Module.Flat O R := Algebra.Smooth.flat O R
  have hlO : (l : O) ∈ nonZeroDivisors O := mem_nonZeroDivisors_of_ne_zero hl
  refine ⟨?_, hC l O R hl, ?_⟩
  · have hreg : IsSMulRegular R (l : O) := Module.Flat.isSMulRegular_of_nonZeroDivisors hlO
    have key : ∀ x : R, (l : R) * x = 0 → x = 0 := by
      intro x hx
      apply hreg
      simp only [Algebra.smul_def, map_natCast, mul_zero]
      exact hx
    rw [mem_nonZeroDivisors_iff]
    exact ⟨key, fun x hx => key x (by rw [mul_comm]; exact hx)⟩
  · rw [Ideal.isRadical_iff_quotient_reduced]
    have hspan : Ideal.span {(algebraMap O R) ϖ} = (IsLocalRing.maximalIdeal O).map (algebraMap O R) := by
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span, Set.image_singleton]
    rw [hspan]
    haveI : Algebra.Smooth (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] R) :=
      Algebra.Smooth.baseChange O R (IsLocalRing.ResidueField O)
    have hred : IsReduced (IsLocalRing.ResidueField O ⊗[O] R) :=
      hR (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] R)
    haveI : IsReduced ((O ⧸ IsLocalRing.maximalIdeal O) ⊗[O] R) := hred
    let e := ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot R (IsLocalRing.maximalIdeal O)).restrictScalars O).trans
      (Algebra.TensorProduct.comm O R (O ⧸ IsLocalRing.maximalIdeal O))
    exact isReduced_of_injective e.toRingHom e.injective
end

section

noncomputable section

namespace UpperTheory.Gal.crystallineComparison

theorem normEx_of : MatRep → DetSplit → NormEx := by
  intro hMR hDS R S _ _ _ _ _ ι _ s
  obtain ⟨m, M, hM⟩ := hMR R S
  let φ : R →+* Polynomial (MvPolynomial ι R) := Polynomial.C.comp MvPolynomial.C
  refine ⟨(1 - (M 1).map φ + (Polynomial.X : Polynomial (MvPolynomial ι R)) • (M 1).map φ
    - ∑ k, (Polynomial.C (MvPolynomial.X (R := R) k) : Polynomial (MvPolynomial ι R)) • (M (s k)).map φ).det, ?_⟩
  intro B _ _ I _ z hz
  classical
  obtain ⟨P, Q, hPQ, hQ⟩ := hM B I z hz
  let ψ : B →+* Polynomial (MvPolynomial ι B) := Polynomial.C.comp MvPolynomial.C
  let F : Polynomial (MvPolynomial ι R) →+* Polynomial (MvPolynomial ι B) :=
    Polynomial.mapRingHom (MvPolynomial.map (algebraMap R B))
  have hPQ' : P.map ψ * Q.map ψ = 1 := by
    rw [← Matrix.map_mul, hPQ, Matrix.map_one ψ (map_zero _) (map_one _)]
  have key := hDS (Polynomial (MvPolynomial ι B)) m I (P.map ψ) (Q.map ψ) hPQ'
    (fun i => form fun k => z i (s k))
  rw [← key]
  have hmap : ∀ t : S, ((M t).map φ).map F = Q.map ψ * (Matrix.diagonal fun i => z i t).map ψ * P.map ψ := by
    intro t
    have : ((M t).map φ).map F = ((M t).map (algebraMap R B)).map ψ := by
      rw [Matrix.map_map, Matrix.map_map]
      congr 1
      funext r
      simp [φ, ψ, F]
    rw [this, hQ t, Matrix.map_mul, Matrix.map_mul]
  have hd : Matrix.diagonal (fun i => form fun k => z i (s k))
      = (Polynomial.X : Polynomial (MvPolynomial ι B)) • (1 : Matrix I I _)
        - ∑ k, (Polynomial.C (MvPolynomial.X (R := B) k) : Polynomial (MvPolynomial ι B))
          • (Matrix.diagonal fun i => z i (s k)).map ψ := by
    ext i j
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.sum_apply]
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs with h
    · subst h

      simp [form, ψ, map_sum, mul_comm]
    · simp
  have hs : ∀ (c : Polynomial (MvPolynomial ι R)) (A : Matrix (Fin m) (Fin m) (Polynomial (MvPolynomial ι R))),
      F.mapMatrix (c • A) = F c • F.mapMatrix A := by
    intro c A
    ext i j
    simp
  have h1 : (Matrix.diagonal fun i => z i 1).map ψ = 1 := by
    simp
  change F _ = _
  rw [RingHom.map_det]
  congr 1

  rw [map_sub, map_add (f := _), map_sub, map_one, map_sum]
  simp only [hs, RingHom.mapMatrix_apply, hmap, h1, Matrix.mul_one]
  rw [hd, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.mul_sum,
    Matrix.sum_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  simp [F]
  abel

end UpperTheory.Gal.crystallineComparison
end
end

section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.splitsBC_of :
    SplitsBC := by
  intro R R' S B _ _ _ _ _ _ _ _ _ I z hz
  let z' : I → (R' ⊗[R] S →ₐ[R'] B) := fun i =>
    Algebra.TensorProduct.lift (Algebra.ofId R' B) (z i) (fun _ _ => Commute.all _ _)
  have hz' : ∀ i (r : R') (s : S), z' i (r ⊗ₜ s) = algebraMap R' B r * z i s := by
    intro i r s
    simp [z', Algebra.ofId_apply]
  refine ⟨z', ?_, ?_⟩
  · have key : ∀ x, splitMap z' x =
        splitMap z (Algebra.TensorProduct.cancelBaseChange R R' B B S x) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [map_add (f := _), ha, hb]
      | tmul b y =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | add a c ha hc => simp only [tmul_add, map_add (f := _), ha, hc]
        | tmul r s =>
          funext i
          rw [splitMap_tmul, hz', Algebra.TensorProduct.cancelBaseChange_tmul, splitMap_tmul]
          simp [Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm]
    have hfun : (⇑(splitMap z') : B ⊗[R'] (R' ⊗[R] S) → (I → B)) =
        (splitMap z) ∘ (Algebra.TensorProduct.cancelBaseChange R R' B B S) := funext key
    unfold Splits
    rw [hfun]
    exact hz.comp (AlgEquiv.bijective _)
  · intro i s
    rw [hz']
    simp
end

section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.matchVal_of :
    IdemCover → ValLocal → MatchPart → MatchingVal := by
  intro hC hL hP B _ ϖ hϖ hv ι _ I I' _ _ _ _ N hI hI' u u' hS
  classical
  let J : (I ≃ I') → Ideal B := fun σ =>
    { carrier := {b | ∀ i k, ϖ ∣ b * (u i k - u' (σ i) k)}
      add_mem' := by
        intro a b ha hb i k
        rw [add_mul]
        exact dvd_add (ha i k) (hb i k)
      zero_mem' := by
        intro i k
        simp
      smul_mem' := by
        intro c b hb i k
        rw [smul_eq_mul, mul_assoc]
        exact Dvd.dvd.mul_left (hb i k) c }
  have hJ : ∀ σ b, b ∈ J σ ↔ ∀ i k, ϖ ∣ b * (u i k - u' (σ i) k) := fun _ _ => Iff.rfl
  obtain ⟨e, he, hmem⟩ := hC B (I ≃ I') J (by
    intro 𝔪 h𝔪
    let D : Finset B := (Finset.univ : Finset (I × I' × ι)).image fun p => u p.1 p.2.2 - u' p.2.1 p.2.2
    have hD : ∀ i i' k, u i k - u' i' k ∈ D := fun i i' k =>
      Finset.mem_image.2 ⟨(i, i', k), Finset.mem_univ _, rfl⟩
    obtain ⟨e, hid, hnot, h1, h2⟩ := hL B ϖ hv 𝔪 h𝔪.isPrime D ((N + 1) ^ N)
    obtain ⟨σ, hσ⟩ := hP B ϖ hϖ ι I I' N hI hI' u u' hS e hid
      (fun i i' k m hm => h1 _ (hD i i' k) m hm)
      (fun i i' k k' h => h2 _ (hD i i' k) _ (hD i i' k') h)
    exact ⟨σ, e, (hJ σ e).2 hσ, hid, hnot⟩)
  exact ⟨e, he, fun σ i k => (hJ σ (e σ)).1 (hmem σ) i k⟩
end

section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.matchPart_of :
    SameNormBasic → Matching → PermOfMap → MatchPart := by
  intro hSN hMatch hPerm B _ ϖ hϖ ι _ I I' _ _ N hI hI' u u' hsame e he hdiv hcmp
  obtain ⟨ρ, hρ⟩ : ∃ ρ : B →+* B ⧸ Ideal.span {1 - e}, ρ = Ideal.Quotient.mk _ := ⟨_, rfl⟩
  have hsurj : Function.Surjective ρ := by
    subst hρ
    exact Ideal.Quotient.mk_surjective
  have hker : ∀ a b : B, ρ a = ρ b ↔ a - b ∈ Ideal.span {1 - e} := by
    subst hρ
    exact fun a b => Ideal.Quotient.eq
  have he' : e * e = e := he
  have hρe : ρ e = 1 := by
    rw [← map_one ρ]
    exact (hker e 1).mpr (Ideal.mem_span_singleton'.mpr ⟨-1, by ring⟩)
  have L1 : ∀ a b : B, ρ a = ρ b → e * a = e * b := by
    intro a b hab
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ((hker a b).mp hab)
    linear_combination (-e) * hc + (-c) * he'
  have L2 : ∀ a b : B, ρ a ∣ ρ b → a ∣ e * b := by
    rintro a b ⟨c', hc'⟩
    obtain ⟨c, rfl⟩ := hsurj c'
    rw [← map_mul] at hc'
    have := L1 _ _ hc'
    exact ⟨e * c, by rw [this]; ring⟩
  have L3 : ∀ a b : B, a ∣ e * b → ρ a ∣ ρ b := by
    intro a b h
    have := map_dvd ρ h
    rwa [map_mul, hρe, one_mul] at this
  by_cases hu : IsUnit (ρ ϖ)
  · obtain ⟨σ⟩ : Nonempty (I ≃ I') := ⟨Fintype.equivOfCardEq (hI.trans hI'.symm)⟩
    refine ⟨σ, fun i k => L2 _ _ hu.dvd⟩
  have hnzd : ρ ϖ ∈ nonZeroDivisors (B ⧸ Ideal.span {1 - e}) := by
    have hr : ∀ z' : B ⧸ Ideal.span {1 - e}, z' * ρ ϖ = 0 → z' = 0 := by
      intro z' hz'
      obtain ⟨z, rfl⟩ := hsurj z'
      rw [← map_mul, ← map_zero ρ] at hz'
      have h1 := L1 _ _ hz'
      have h2 : e * z * ϖ = 0 := by
        rw [mul_zero] at h1
        rw [mul_assoc]
        exact h1
      have h3 : e * z = 0 := (mem_nonZeroDivisors_iff.mp hϖ).2 _ h2
      rw [← one_mul (ρ z), ← hρe, ← map_mul, h3, map_zero]
    rw [mem_nonZeroDivisors_iff]
    exact ⟨fun z hz => hr z (by rw [mul_comm]; exact hz), hr⟩
  have hle : Ideal.span {ϖ ^ (N + 1) ^ N} ≤ (Ideal.span {ρ ϖ ^ (N + 1) ^ N}).comap ρ := by
    rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [SetLike.mem_coe, Ideal.mem_comap, map_pow]
    exact Ideal.mem_span_singleton_self _
  have hsame' : SameNorm
      (redMod (ρ ϖ ^ (N + 1) ^ N) (Multiset.map (fun i k => ρ (u i k)) Finset.univ.val))
      (redMod (ρ ϖ ^ (N + 1) ^ N) (Multiset.map (fun i k => ρ (u' i k)) Finset.univ.val)) := by
    have := (hSN (B ⧸ Ideal.span {ϖ ^ (N + 1) ^ N}) ι).1 _ (Ideal.quotientMap _ ρ hle) _ _ hsame
    convert this using 1 <;>
      simp [redMod, Multiset.map_map, Function.comp_def, Ideal.quotientMap_mk]
  have hM := hMatch (B ⧸ Ideal.span {1 - e}) (ρ ϖ) hnzd hu ι N
    (Multiset.map (fun i k => ρ (u i k)) Finset.univ.val)
    (Multiset.map (fun i k => ρ (u' i k)) Finset.univ.val) (by simp [hI]) (by simp [hI']) hsame' ?_ ?_
  · simp only [redMod, Multiset.map_map] at hM
    obtain ⟨σ, hσ⟩ := hPerm I I' _ _ _ hM
    refine ⟨σ, fun i k => ?_⟩
    have := congrFun (hσ i) k
    simp only [Function.comp_apply] at this
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, ← map_sub] at this
    exact L2 _ _ this
  · intro x hx y hy k k' hxy
    simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and] at hx hy
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨i', rfl⟩ := hy
    rw [← map_sub, ← map_pow] at hxy
    rw [← map_sub, ← map_sub]
    rcases hcmp i i' k k' (L2 _ _ hxy) with h | h
    · exact Or.inl (L3 _ _ h)
    · exact Or.inr (L3 _ _ h)
  · intro x hx y hy k j hj
    simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and] at hx hy
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨i', rfl⟩ := hy
    have hm : (N + 1) ^ j ≤ (N + 1) ^ N := Nat.pow_le_pow_right (Nat.succ_pos N) hj
    rw [← map_sub, ← map_pow]
    rcases hdiv i i' k _ hm with h | h
    · exact Or.inl (L3 _ _ h)
    · exact Or.inr (L3 _ _ h)
end

section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

private theorem UpperTheory.Gal.crystallineComparison.one_not_mem {B : Type} [CommRing B] {𝔪 : Ideal B} (h𝔪 : 𝔪.IsPrime) :
    (1 : B) ∉ 𝔪 :=
  fun h => h𝔪.ne_top ((Ideal.eq_top_iff_one _).2 h)

private theorem UpperTheory.Gal.crystallineComparison.good_or {B : Type} [CommRing B] {𝔪 : Ideal B} (h𝔪 : 𝔪.IsPrime) (e : B) :
    e ∉ 𝔪 ∨ 1 - e ∉ 𝔪 := by
  by_contra h
  push_neg at h
  exact one_not_mem h𝔪 (by simpa using 𝔪.add_mem h.1 h.2)

private theorem UpperTheory.Gal.crystallineComparison.mul_not_mem {B : Type} [CommRing B] {𝔪 : Ideal B} (h𝔪 : 𝔪.IsPrime)
    {a b : B} (ha : a ∉ 𝔪) (hb : b ∉ 𝔪) : a * b ∉ 𝔪 :=
  fun h => (h𝔪.mem_or_mem h).elim ha hb

private theorem UpperTheory.Gal.crystallineComparison.dvd_st {B : Type} [CommRing B] {a b e : B} (e' : B) (h : a ∣ e * b) :
    a ∣ e' * e * b := by
  rw [mul_assoc]
  exact Dvd.dvd.mul_left h e'

private theorem UpperTheory.Gal.crystallineComparison.good_combine {B ι : Type} [CommRing B] {𝔪 : Ideal B} (h𝔪 : 𝔪.IsPrime)
    (s : Finset ι) (Q : ι → B → Prop) (st : ∀ i e e', Q i e → Q i (e' * e))
    (ex : ∀ i ∈ s, ∃ e : B, IsIdempotentElem e ∧ e ∉ 𝔪 ∧ Q i e) :
    ∃ e : B, IsIdempotentElem e ∧ e ∉ 𝔪 ∧ ∀ i ∈ s, Q i e := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, IsIdempotentElem.one, one_not_mem h𝔪, by simp⟩
  | insert a s ha ih =>
    obtain ⟨e, he, hem, hQ⟩ := ih fun i hi => ex i (Finset.mem_insert_of_mem hi)
    obtain ⟨e', he', hem', hQ'⟩ := ex a (Finset.mem_insert_self a s)
    refine ⟨e' * e, he'.mul he, mul_not_mem h𝔪 hem' hem, ?_⟩
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · rw [mul_comm]
      exact st _ _ _ hQ'
    · exact st _ _ _ (hQ i hi)

private theorem UpperTheory.Gal.crystallineComparison.power_good {B : Type} [CommRing B] {ϖ : B} (hv : ValLike ϖ) {𝔪 : Ideal B}
    (h𝔪 : 𝔪.IsPrime) (d : B) (m : ℕ) :
    ∃ e : B, IsIdempotentElem e ∧ e ∉ 𝔪 ∧ (d ∣ e * ϖ ^ m ∨ ϖ ^ m ∣ e * d) := by
  obtain ⟨e, he, h1, h2⟩ := hv d (ϖ ^ m) ⟨m, Ideal.subset_span (by simp)⟩
  rcases good_or h𝔪 e with g | g
  · exact ⟨e, he, g, Or.inr h1⟩
  · exact ⟨1 - e, he.one_sub, g, Or.inl h2⟩

private theorem UpperTheory.Gal.crystallineComparison.pair_good {B : Type} [CommRing B] {ϖ : B} (hv : ValLike ϖ) {𝔪 : Ideal B}
    (h𝔪 : 𝔪.IsPrime) (M : ℕ) (d d' : B) :
    ∃ e : B, IsIdempotentElem e ∧ e ∉ 𝔪 ∧
      ((∃ e₀ : B, IsIdempotentElem e₀ ∧ e₀ ∉ 𝔪 ∧ d ∣ e₀ * ϖ ^ M) → d ∣ e * d' ∨ d' ∣ e * d) := by
  by_cases h : ∃ e₀ : B, IsIdempotentElem e₀ ∧ e₀ ∉ 𝔪 ∧ d ∣ e₀ * ϖ ^ M
  · obtain ⟨e₀, h0, hm0, c, hc⟩ := h
    have h0' : e₀ * e₀ = e₀ := h0
    obtain ⟨f, hfd⟩ : ∃ f : B, f = e₀ * d + (1 - e₀) := ⟨_, rfl⟩
    have hf : e₀ * f = e₀ * d := by
      rw [hfd]
      linear_combination (d - 1) * h0'
    have hmem : ϖ ^ M ∈ Ideal.span {f, d'} := by
      have hP : ϖ ^ M = (e₀ * c + (1 - e₀) * ϖ ^ M) * f := by
        rw [hfd]
        linear_combination (-(c * d - c - d * ϖ ^ M + 2 * ϖ ^ M)) * h0' + e₀ * hc
      rw [hP]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    obtain ⟨e₁, h1, ⟨a, ha⟩, ⟨b, hb⟩⟩ := hv f d' ⟨M, hmem⟩
    have A : d' ∣ (e₀ * e₁) * d := ⟨e₀ * a, by linear_combination e₀ * ha - e₁ * hf⟩
    have C : d ∣ (e₀ * (1 - e₁)) * d' := ⟨e₀ * b, by linear_combination e₀ * hb + b * hf⟩
    rcases good_or h𝔪 e₁ with g | g
    · exact ⟨e₀ * e₁, h0.mul h1, mul_not_mem h𝔪 hm0 g, fun _ => Or.inr A⟩
    · exact ⟨e₀ * (1 - e₁), h0.mul h1.one_sub, mul_not_mem h𝔪 hm0 g, fun _ => Or.inl C⟩
  · exact ⟨1, IsIdempotentElem.one, one_not_mem h𝔪, fun h' => absurd h' h⟩

theorem UpperTheory.Gal.crystallineComparison.valLocal_of :
    ValLocal := by
  intro B _ ϖ hv 𝔪 h𝔪 D M
  obtain ⟨e₁, i₁, g₁, q₁⟩ := good_combine h𝔪 (D ×ˢ Finset.range (M + 1))
    (fun p e => p.1 ∣ e * ϖ ^ p.2 ∨ ϖ ^ p.2 ∣ e * p.1)
    (fun p e e' h => h.elim (fun h => Or.inl (dvd_st e' h)) (fun h => Or.inr (dvd_st e' h)))
    (fun p _ => power_good hv h𝔪 p.1 p.2)
  obtain ⟨e₂, i₂, g₂, q₂⟩ := good_combine h𝔪 (D ×ˢ D)
    (fun p e => (∃ e₀ : B, IsIdempotentElem e₀ ∧ e₀ ∉ 𝔪 ∧ p.1 ∣ e₀ * ϖ ^ M) →
      p.1 ∣ e * p.2 ∨ p.2 ∣ e * p.1)
    (fun p e e' h h' => (h h').elim (fun h => Or.inl (dvd_st e' h)) (fun h => Or.inr (dvd_st e' h)))
    (fun p _ => pair_good hv h𝔪 M p.1 p.2)
  refine ⟨e₂ * e₁, i₂.mul i₁, mul_not_mem h𝔪 g₂ g₁, ?_, ?_⟩
  · intro d hd m hm
    have := q₁ (d, m) (Finset.mk_mem_product hd (Finset.mem_range.2 (Nat.lt_succ_of_le hm)))
    exact this.elim (fun h => Or.inl (dvd_st e₂ h)) (fun h => Or.inr (dvd_st e₂ h))
  · intro d hd d' hd' hdv
    have := q₂ (d, d') (Finset.mk_mem_product hd hd') ⟨e₂ * e₁, i₂.mul i₁, mul_not_mem h𝔪 g₂ g₁, hdv⟩
    rw [mul_comm e₂ e₁]
    exact this.elim (fun h => Or.inl (dvd_st e₁ h)) (fun h => Or.inr (dvd_st e₁ h))
end

section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

private theorem descend (hS : SameNormBasic) {B ι : Type} [CommRing B] [Fintype ι] {a b : B} (hab : a ∣ b)
    {u u' : Multiset (ι → B)} (h : SameNorm (redMod b u) (redMod b u')) :
    SameNorm (redMod a u) (redMod a u') := by
  have hle : Ideal.span {b} ≤ Ideal.span {a} := Ideal.span_singleton_le_span_singleton.2 hab
  have := (hS (B ⧸ Ideal.span {b}) ι).1 (B ⧸ Ideal.span {a}) (Ideal.Quotient.factor hle) _ _ h
  simpa only [redMod, Multiset.map_map, Function.comp_def, Ideal.Quotient.factor_mk] using this

private theorem red_cons {B ι : Type} [CommRing B] (a : B) (x : ι → B) (u : Multiset (ι → B)) :
    redMod a (x ::ₘ u) = (fun k => Ideal.Quotient.mk (Ideal.span {a}) (x k)) ::ₘ redMod a u := by
  simp [redMod]

private theorem red_eq {B ι : Type} [CommRing B] {a : B} {x y : ι → B} (h : ∀ k, a ∣ x k - y k) :
    (fun k => Ideal.Quotient.mk (Ideal.span {a}) (x k)) = fun k => Ideal.Quotient.mk (Ideal.span {a}) (y k) := by
  funext k
  exact Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 (h k))

private theorem main (hS : SameNormBasic) (hM : MatchStep) {B : Type} [CommRing B] (ϖ : B)
    (h0 : ϖ ∈ nonZeroDivisors B) (h1 : ¬ IsUnit ϖ) {ι : Type} [Fintype ι] (N : ℕ) :
    ∀ c, c ≤ N → ∀ (u u' : Multiset (ι → B)), u.card = c → u'.card ≤ N →
    (∀ x ∈ u, ∀ y ∈ u', ∀ k k', x k - y k ∣ ϖ ^ (N + 1) ^ N → x k - y k ∣ x k' - y k' ∨ x k' - y k' ∣ x k - y k) →
    (∀ x ∈ u, ∀ y ∈ u', ∀ k, ∀ j ≤ N, x k - y k ∣ ϖ ^ (N + 1) ^ j ∨ ϖ ^ (N + 1) ^ j ∣ x k - y k) →
    SameNorm (redMod (ϖ ^ (N + 1) ^ c) u) (redMod (ϖ ^ (N + 1) ^ c) u') →
    redMod ϖ u = redMod ϖ u' := by
  have hnu : ∀ j : ℕ, j ≠ 0 → ¬ IsUnit (ϖ ^ j) := fun j hj h => h1 ((isUnit_pow_iff hj).mp h)
  intro c
  induction c with
  | zero =>
    intro _ u u' hu _ _ _ hsn
    have hu0 : u = 0 := Multiset.card_eq_zero.mp hu
    subst hu0
    haveI : Nontrivial (B ⧸ Ideal.span {ϖ ^ (N + 1) ^ 0}) := by
      refine nontrivial_of_ne 1 0 ?_
      intro h
      rw [← map_one (Ideal.Quotient.mk (Ideal.span {ϖ ^ (N + 1) ^ 0})),
        Ideal.Quotient.eq_zero_iff_mem, ← Ideal.eq_top_iff_one, Ideal.span_singleton_eq_top] at h
      exact hnu _ (by positivity) h
    have hc := (hS _ ι).2.2.1 inferInstance _ _ hsn
    have hu'0 : u' = 0 := by
      simp only [redMod, Multiset.card_map, Multiset.card_zero, Multiset.map_zero] at hc
      exact Multiset.card_eq_zero.mp hc.symm
    subst hu'0
    rfl
  | succ c ih =>
    intro hc u u' hu hu' hdiv hcmp hsn
    obtain ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.mp (by rw [hu]; exact Nat.succ_pos c)
    obtain ⟨u0, rfl⟩ := Multiset.exists_cons_of_mem hx
    have hxm : x ∈ x ::ₘ u0 := Multiset.mem_cons.mpr (Or.inl rfl)
    have hm : 0 < (N + 1) ^ c := by positivity
    have hle : (N + 1) ^ c ≤ (N + 1) ^ N := Nat.pow_le_pow_right (Nat.succ_pos N) (by omega)
    have hsn' : SameNorm (redMod (ϖ ^ ((N + 1) ^ c * (N + 1))) (x ::ₘ u0))
        (redMod (ϖ ^ ((N + 1) ^ c * (N + 1))) u') := by
      rw [← pow_succ]; exact hsn
    obtain ⟨y, hy, hxy⟩ := hM B ϖ h0 h1 ι N ((N + 1) ^ c) hm (x ::ₘ u0) u' hu' hsn' x hxm
      (fun y hy k k' h => hdiv x hxm y hy k k' (h.trans (pow_dvd_pow ϖ hle)))
      (fun y hy k => hcmp x hxm y hy k c (by omega))
    obtain ⟨u0', rfl⟩ := Multiset.exists_cons_of_mem hy
    have hsn2 : SameNorm (redMod (ϖ ^ (N + 1) ^ c) (x ::ₘ u0)) (redMod (ϖ ^ (N + 1) ^ c) (y ::ₘ u0')) :=
      descend hS (pow_dvd_pow ϖ (Nat.pow_le_pow_right (Nat.succ_pos N) (Nat.le_succ c))) hsn
    rw [red_cons, red_cons, red_eq hxy] at hsn2
    have hsn3 := (hS _ ι).2.1 _ _ _ hsn2
    have ih' := ih (by omega) u0 u0' (by simpa using hu) (by simp at hu'; omega)
      (fun a ha b hb => hdiv a (Multiset.mem_cons_of_mem ha) b (Multiset.mem_cons_of_mem hb))
      (fun a ha b hb => hcmp a (Multiset.mem_cons_of_mem ha) b (Multiset.mem_cons_of_mem hb)) hsn3
    rw [red_cons, red_cons, ih', red_eq (fun k => (dvd_pow_self ϖ hm.ne').trans (hxy k))]

theorem UpperTheory.Gal.crystallineComparison.matching_of :
    SameNormBasic → MatchStep → Matching := by
  intro hS hM B _ ϖ h0 h1 ι _ N u u' hu hu' hsn hdiv hcmp
  apply main hS hM ϖ h0 h1 N u.card hu u u' rfl hu' hdiv hcmp
  exact descend hS (pow_dvd_pow _ (Nat.pow_le_pow_right (Nat.succ_pos N) hu)) hsn
end

section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.smoothRed_of :
    SmoothReduced :=
  GlobalTheory.T.isReduced_of_smooth_over_field'
end
