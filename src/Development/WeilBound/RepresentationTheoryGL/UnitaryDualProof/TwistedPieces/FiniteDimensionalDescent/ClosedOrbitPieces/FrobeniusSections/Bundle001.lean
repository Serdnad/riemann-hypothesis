module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.RingTheory.AdjoinRoot

@[expose] public section

section

noncomputable section

namespace PositivityTheory.RgUd.TP.Desc.Piece.PSect

open Module Polynomial

theorem idem {k S : Type*} [Field k] [CommRing S] [Algebra k S] [FiniteDimensional k S] [IsReduced S] :
    ∃ (m : ℕ) (e : Fin m → S), (∀ t, IsIdempotentElem (e t)) ∧ ∑ t, e t = 1 ∧
      (∀ t t', t ≠ t' → e t * e t' = 0) ∧ ∀ t s, s * e t = 0 ∨ ∃ w, s * e t * w = e t := by
  classical
  have : IsArtinianRing S := IsArtinianRing.of_finite k S
  haveI : Fintype (MaximalSpectrum S) := Fintype.ofFinite _
  set φ := IsArtinianRing.equivPi S with hφ
  let σ := (Fintype.equivFin (MaximalSpectrum S)).symm
  refine ⟨Fintype.card (MaximalSpectrum S), fun t => φ.symm (Pi.single (σ t) 1), ?_, ?_, ?_, ?_⟩
  · intro t
    show _ * _ = _
    rw [← map_mul]
    congr 1
    ext M
    by_cases h : M = σ t
    · subst h; simp
    · simp [h]
  · apply φ.injective

    rw [map_sum, map_one]
    simp only [AlgEquiv.apply_symm_apply]
    rw [Equiv.sum_comp σ (fun M => (Pi.single M 1 : ∀ M : MaximalSpectrum S, S ⧸ M.asIdeal))]
    exact Finset.univ_sum_single (1 : ∀ M : MaximalSpectrum S, S ⧸ M.asIdeal)
  · intro t t' htt
    rw [← map_mul]
    have hne : σ t ≠ σ t' := fun h => htt (σ.injective h)
    have : (Pi.single (σ t) 1 * Pi.single (σ t') 1 : ∀ M : MaximalSpectrum S, S ⧸ M.asIdeal) = 0 := by
      ext M
      by_cases h1 : M = σ t
      · subst h1; simp [hne.symm]
      · simp [h1]
    rw [this, map_zero]
  · intro t s
    have := (σ t).isMaximal
    by_cases ha : φ s (σ t) = 0
    · left
      apply φ.injective
      rw [map_mul, AlgEquiv.apply_symm_apply, map_zero]
      ext M
      by_cases h1 : M = σ t
      · subst h1; simp [ha]
      · simp [h1]
    · right
      obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv ha
      refine ⟨φ.symm (Pi.single (σ t) b), ?_⟩
      apply φ.injective
      rw [map_mul, map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
      ext M
      by_cases h1 : M = σ t
      · subst h1; simp only [Pi.mul_apply, Pi.single_eq_same, mul_one]; exact hb
      · simp [h1]

theorem sEps {k R : Type*} [Field k] [CommRing R] [Algebra k R] [IsPrincipalIdealRing R] (S : Subalgebra k R)
    (hS : ∀ r : R, ∃ s ∈ S, IsNilpotent (r - s)) (q : ℕ) (hnil : ∀ r : R, IsNilpotent r → r ^ q = 0) :
    ∃ ε : R, IsNilpotent ε ∧ ∀ r : R, ∃ σ : Fin q → R, (∀ l, σ l ∈ S) ∧ r = ∑ l, σ l * ε ^ (l : ℕ) := by
  classical
  set ε := Submodule.IsPrincipal.generator (nilradical R) with hε
  have hspan : Ideal.span {ε} = nilradical R := Ideal.span_singleton_generator _
  have hεn : IsNilpotent ε := mem_nilradical.mp (Submodule.IsPrincipal.generator_mem _)
  refine ⟨ε, hεn, fun r => ?_⟩
  have key : ∀ n : ℕ, ∃ σ : Fin n → R, (∀ l, σ l ∈ S) ∧
      ∃ u : R, r = ∑ l, σ l * ε ^ (l : ℕ) + ε ^ n * u := by
    intro n
    induction n with
    | zero => exact ⟨Fin.elim0, fun l => l.elim0, r, by simp⟩
    | succ n ih =>
      obtain ⟨σ, hσ, u, hu⟩ := ih
      obtain ⟨s, hs, hn⟩ := hS u
      have hm : u - s ∈ Ideal.span {ε} := by rw [hspan]; exact mem_nilradical.mpr hn
      obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.mp hm
      refine ⟨Fin.snoc σ s, fun l => ?_, v, ?_⟩
      · refine Fin.lastCases ?_ (fun i => ?_) l
        · simpa using hs
        · simpa using hσ i
      · rw [Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
        rw [hu]
        have : u = s + v * ε := by rw [hv]; ring
        rw [this]
        ring
  obtain ⟨σ, hσ, u, hu⟩ := key q
  refine ⟨σ, hσ, ?_⟩
  rw [hu, hnil ε hεn, zero_mul, add_zero]

end PositivityTheory.RgUd.TP.Desc.Piece.PSect
end
end

section

noncomputable section

namespace PositivityTheory.RgUd.TP.Desc.Piece.PSect

open Module

def Tw (k : Type*) (_p _c : ℕ) : Type _ := k

variable {k : Type*} [Field k]

instance (p c : ℕ) : Field (Tw k p c) := inferInstanceAs (Field k)

instance (p c : ℕ) [Fact p.Prime] [CharP k p] : Algebra k (Tw k p c) :=
  RingHom.toAlgebra (show k →+* Tw k p c from iterateFrobenius k p c)

def Pw (k B : Type*) [Field k] [CommRing B] [Algebra k B] (q : ℕ) : Subalgebra k B :=
  Algebra.adjoin k (Set.range fun b : B => b ^ q)

theorem mem_Pw {B : Type*} [CommRing B] [Algebra k B] (p c : ℕ) [Fact p.Prime] [CharP k p]
    (hroot : ∀ a : k, ∃ w : B, w ^ (p ^ c) = algebraMap k B a) {b : B} :
    b ∈ Pw k B (p ^ c) ↔ ∃ w : B, w ^ (p ^ c) = b := by
  unfold Pw
  constructor
  · intro hb
    rcases subsingleton_or_nontrivial B with hB | hB
    · exact ⟨b, Subsingleton.elim _ _⟩
    have : CharP B p := charP_of_injective_algebraMap' k p
    induction hb using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      exact ⟨w, rfl⟩
    | algebraMap r => exact hroot r
    | add x y _ _ hx hy =>
      obtain ⟨w₁, rfl⟩ := hx
      obtain ⟨w₂, rfl⟩ := hy
      exact ⟨w₁ + w₂, add_pow_char_pow w₁ w₂ p c⟩
    | mul x y _ _ hx hy =>
      obtain ⟨w₁, rfl⟩ := hx
      obtain ⟨w₂, rfl⟩ := hy
      exact ⟨w₁ * w₂, mul_pow w₁ w₂ _⟩
  · rintro ⟨w, rfl⟩
    exact Algebra.subset_adjoin ⟨w, rfl⟩

theorem fc {B : Type*} [CommRing B] [Algebra k B] [FiniteDimensional k B] [IsReduced B]
    (p c : ℕ) [Fact p.Prime] [CharP k p] [FiniteDimensional k (Tw k p c)]
    (hroot : ∀ a : k, ∃ w : B, w ^ (p ^ c) = algebraMap k B a) :
    finrank k B = finrank k (Tw k p c) * finrank k (Pw k B (p ^ c)) := by
  classical
  letI iT : Module (Tw k p c) (Pw k B (p ^ c)) := inferInstanceAs (Module k (Pw k B (p ^ c)))
  have hadd : ∀ x y : B, (x + y) ^ (p ^ c) = x ^ (p ^ c) + y ^ (p ^ c) := by
    intro x y
    rcases subsingleton_or_nontrivial B with hB | hB
    · exact Subsingleton.elim _ _
    · haveI := charP_of_injective_algebraMap (algebraMap k B).injective p
      exact add_pow_char_pow x y p c
  have hmem : ∀ x : B, x ^ (p ^ c) ∈ Pw k B (p ^ c) := fun x =>
    Algebra.subset_adjoin ⟨x, rfl⟩
  let f : B →ₗ[k] RestrictScalars k (Tw k p c) (Pw k B (p ^ c)) :=
    { toFun := fun x => (⟨x ^ (p ^ c), hmem x⟩ : Pw k B (p ^ c))
      map_add' := fun x y => by
        apply Subtype.ext
        exact hadd x y
      map_smul' := fun a x => by
        apply Subtype.ext
        show (a • x) ^ (p ^ c) = ((algebraMap k (Tw k p c) a) • (⟨x ^ (p ^ c), hmem x⟩ : Pw k B (p ^ c)) : Pw k B (p ^ c)).1
        rw [smul_pow]
        rfl }
  have hinj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun x hx => ?_
    have h0 : x ^ (p ^ c) = 0 := congrArg (fun z : Pw k B (p ^ c) => (z : B)) hx
    exact IsReduced.eq_zero x ⟨_, h0⟩
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨w, hw⟩ := (mem_Pw p c hroot).1 (show (Pw k B (p ^ c)) from y).2
    exact ⟨w, Subtype.ext hw⟩
  letI : Module (Tw k p c) (RestrictScalars k (Tw k p c) (Pw k B (p ^ c))) :=
    RestrictScalars.moduleOrig k (Tw k p c) (Pw k B (p ^ c))
  haveI : Module.Free (Tw k p c) (RestrictScalars k (Tw k p c) (Pw k B (p ^ c))) :=
    show Module.Free k (Pw k B (p ^ c)) from inferInstance
  let e := LinearEquiv.ofBijective f ⟨hinj, hsurj⟩
  rw [e.finrank_eq, ← Module.finrank_mul_finrank k (Tw k p c)
    (RestrictScalars k (Tw k p c) (Pw k B (p ^ c)))]
  rfl

end PositivityTheory.RgUd.TP.Desc.Piece.PSect
end
end

section

noncomputable section

namespace PositivityTheory.RgUd.TP.Desc.Piece.PSect

open Module Polynomial

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]

def Iq (A : Type*) [CommRing A] [Algebra k A] (χ : k[X]) (q : ℕ) : Ideal A[X] :=
  Ideal.span {χ.map (algebraMap k A)} ⊔
    Ideal.span {y | ∃ r ∈ (Ideal.span {χ.map (algebraMap k A)}).radical, y = r ^ q}

abbrev Rq (A : Type*) [CommRing A] [Algebra k A] (χ : k[X]) (q : ℕ) : Type _ := A[X] ⧸ Iq A χ q

theorem rq_fin [FiniteDimensional k A] (χ : k[X]) (hχ : χ.Monic) (q : ℕ) :
    FiniteDimensional k (Rq A χ q) := by
  classical
  have hmon : (χ.map (algebraMap k A)).Monic := hχ.map _
  have : Module.Finite A (A[X] ⧸ Ideal.span {χ.map (algebraMap k A)}) := (AdjoinRoot.powerBasis' hmon).finite
  have hle : Ideal.span {χ.map (algebraMap k A)} ≤ Iq A χ q := le_sup_left
  let φ := Ideal.Quotient.factorₐ A hle
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ P, rfl⟩
  have : Module.Finite A (Rq A χ q) := Module.Finite.of_surjective φ.toLinearMap hsurj
  exact Module.Finite.trans A (Rq A χ q)

theorem rq_nil (χ : k[X]) (q : ℕ) (r : Rq A χ q) (hr : IsNilpotent r) : r ^ q = 0 := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨m, hm⟩ := hr
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hm ⊢
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · rw [pow_zero]
    exact Ideal.mem_sup_right (Ideal.subset_span ⟨0, Ideal.zero_mem _, (pow_zero _).symm⟩)
  · have hle : Iq A χ q ≤ (Ideal.span {χ.map (algebraMap k A)}).radical := by
      refine sup_le Ideal.le_radical ?_
      rw [Ideal.span_le]
      rintro _ ⟨r, hr, rfl⟩
      exact Ideal.pow_mem_of_mem _ hr q hq
    have hP : P ∈ (Ideal.span {χ.map (algebraMap k A)}).radical :=
      (Ideal.radical_isRadical _) ⟨m, hle hm⟩
    exact Ideal.mem_sup_right (Ideal.subset_span ⟨P, hP, rfl⟩)
private theorem isPrincipalIdealRing_pi {ι : Type*} [Finite ι] (R : ι → Type*) [∀ i, CommRing (R i)]
    (hR : ∀ i, IsPrincipalIdealRing (R i)) : IsPrincipalIdealRing (∀ i, R i) := by
  classical
  have := Fintype.ofFinite ι
  refine ⟨fun J => ?_⟩
  have hsurj : ∀ i, Function.Surjective (Pi.evalRingHom R i) := fun i y => ⟨Pi.single i y, by simp⟩
  have hgen : ∀ i, ∃ a : R i, J.map (Pi.evalRingHom R i) = Ideal.span {a} := fun i => by
    obtain ⟨a, ha⟩ := (hR i).principal (J.map (Pi.evalRingHom R i))
    exact ⟨a, ha⟩
  choose g hg using hgen
  have hgJ : g ∈ J := by
    have hpre : ∀ i, ∃ h ∈ J, h i = g i := fun i => by
      have hm : g i ∈ J.map (Pi.evalRingHom R i) := by
        rw [hg i]
        exact Ideal.subset_span rfl
      obtain ⟨h, hh, he⟩ := (Ideal.mem_map_iff_of_surjective _ (hsurj i)).mp hm
      exact ⟨h, hh, he⟩
    choose h hh he using hpre
    have e : g = ∑ i, Pi.single i (1 : R i) * h i := by
      funext j
      simp only [Finset.sum_apply, Pi.mul_apply]
      rw [Finset.sum_eq_single j]
      · rw [Pi.single_eq_same, one_mul, he]
      · intro i _ hij
        rw [Pi.single_eq_of_ne (Ne.symm hij), zero_mul]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    rw [e]
    exact J.sum_mem (fun i _ => J.mul_mem_left _ (hh i))
  refine ⟨g, le_antisymm ?_ ?_⟩
  · intro x hx
    have hc : ∀ i, ∃ c : R i, c * g i = x i := fun i => by
      have hm : x i ∈ J.map (Pi.evalRingHom R i) := Ideal.mem_map_of_mem _ hx
      rw [hg i] at hm
      exact Ideal.mem_span_singleton'.mp hm
    choose c hc using hc
    exact Ideal.mem_span_singleton'.mpr ⟨c, funext hc⟩
  · exact (Ideal.span_le).mpr (Set.singleton_subset_iff.mpr hgJ)

theorem rq_pir [FiniteDimensional k A] [IsReduced A] (χ : k[X]) (q : ℕ) :
    IsPrincipalIdealRing (Rq A χ q) := by
  classical
  have hA : IsArtinianRing A := IsArtinianRing.of_finite k A
  have hPI : IsPrincipalIdealRing ((I : MaximalSpectrum A) → (A ⧸ I.asIdeal)[X]) :=
    isPrincipalIdealRing_pi _ (fun I => by
      have := I.isMaximal
      letI : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field _
      exact EuclideanDomain.instIsPrincipalIdealRing)
  have hPI' : IsPrincipalIdealRing ((∀ I : MaximalSpectrum A, A ⧸ I.asIdeal)[X]) :=
    IsPrincipalIdealRing.of_surjective (Polynomial.piEquiv (fun I : MaximalSpectrum A => A ⧸ I.asIdeal)).symm
      (Polynomial.piEquiv _).symm.surjective
  have hAX : IsPrincipalIdealRing A[X] :=
    IsPrincipalIdealRing.of_surjective (Polynomial.mapEquiv (IsArtinianRing.equivPi A).symm.toRingEquiv)
      (Polynomial.mapEquiv _).surjective
  exact IsPrincipalIdealRing.of_surjective (Ideal.Quotient.mk (Iq A χ q)) Ideal.Quotient.mk_surjective

theorem rq_rep (χ : k[X]) (hχ : χ.Monic) (q d : ℕ) (hd : χ.natDegree ≤ d) (r : Rq A χ q) :
    ∃ a : Fin d → A, r = Ideal.Quotient.mk _ (∑ l : Fin d, C (a l) * X ^ (l : ℕ)) := by
  classical
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective r
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact ⟨0, by congr 1; exact Subsingleton.elim _ _⟩
  have hmon : (χ.map (algebraMap k A)).Monic := hχ.map _
  have hmem : P - P %ₘ χ.map (algebraMap k A) ∈ Iq A χ q := by
    have e : P - P %ₘ χ.map (algebraMap k A) = χ.map (algebraMap k A) * (P /ₘ χ.map (algebraMap k A)) := by
      have h := modByMonic_add_div P (χ.map (algebraMap k A))
      linear_combination -h
    rw [e]
    exact Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  have hdeg : (P %ₘ χ.map (algebraMap k A)).degree < d :=
    calc (P %ₘ χ.map (algebraMap k A)).degree < (χ.map (algebraMap k A)).degree := degree_modByMonic_lt _ hmon
      _ ≤ (χ.map (algebraMap k A)).natDegree := degree_le_natDegree
      _ ≤ d := by exact_mod_cast natDegree_map_le.trans hd
  refine ⟨fun l => (P %ₘ χ.map (algebraMap k A)).coeff l, ?_⟩
  rw [Ideal.Quotient.eq.mpr hmem]
  congr 1
  rw [show (∑ l : Fin d, C ((P %ₘ χ.map (algebraMap k A)).coeff (l : ℕ)) * X ^ (l : ℕ)) =
      ∑ i ∈ Finset.range d, C ((P %ₘ χ.map (algebraMap k A)).coeff i) * X ^ i from
    (Finset.sum_range (fun i => C ((P %ₘ χ.map (algebraMap k A)).coeff i) * X ^ i)).symm]
  by_cases h0 : P %ₘ χ.map (algebraMap k A) = 0
  · rw [h0]
    simp
  · have h := as_sum_range' _ d ((natDegree_lt_iff_degree_lt h0).mpr hdeg)
    simp only [← C_mul_X_pow_eq_monomial] at h
    exact h

theorem rq_lift {B : Type*} [Ring B] [Algebra k B] (ι : A →ₐ[k] B) (x : B) (hc : ∀ a, Commute (ι a) x)
    (χ : k[X]) (hχ : aeval x χ = 0) (q : ℕ)
    (hq : ∀ P : A[X], IsNilpotent (P.eval₂ ι.toRingHom x) → (P.eval₂ ι.toRingHom x) ^ q = 0) :
    ∃ ρ : Rq A χ q →ₐ[k] B, ∀ P : A[X], ρ (Ideal.Quotient.mk _ P) = P.eval₂ ι.toRingHom x := by
  let f : A[X] →+* B := Polynomial.eval₂RingHom' ι.toRingHom x hc
  have hf : ∀ P : A[X], f P = P.eval₂ ι.toRingHom x := fun P => rfl
  have hχ0 : f (χ.map (algebraMap k A)) = 0 := by
    rw [hf, Polynomial.eval₂_map]
    have e : ι.toRingHom.comp (algebraMap k A) = algebraMap k B := by
      ext c
      exact ι.commutes c
    rw [e, ← Polynomial.aeval_def, hχ]
  have hspan : ∀ P ∈ Ideal.span {χ.map (algebraMap k A)}, f P = 0 := by
    intro P hP
    obtain ⟨Q, rfl⟩ := Ideal.mem_span_singleton'.mp hP
    rw [map_mul, hχ0, mul_zero]
  have hle : Iq A χ q ≤ RingHom.ker f := by
    unfold Iq
    apply sup_le
    · intro P hP
      exact (RingHom.mem_ker).mpr (hspan P hP)
    · rw [Ideal.span_le]
      rintro _ ⟨r, hr, rfl⟩
      obtain ⟨m, hm⟩ := hr
      have hnil : IsNilpotent (r.eval₂ ι.toRingHom x) := ⟨m, by rw [← hf, ← map_pow, hspan _ hm]⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_pow, hf]
      exact hq r hnil
  let F : A[X] →ₐ[k] B :=
    { f with
      commutes' := fun c => by
        show Polynomial.eval₂ ι.toRingHom x (algebraMap k A[X] c) = algebraMap k B c
        rw [Polynomial.algebraMap_apply, Polynomial.eval₂_C]
        exact ι.commutes c }
  exact ⟨Ideal.Quotient.liftₐ _ F (fun a ha => hle ha), fun P => rfl⟩

end PositivityTheory.RgUd.TP.Desc.Piece.PSect
end
end
