module

public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.ClassGroup.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle227
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.Topology.Instances.Matrix
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicIntegersCompact.IsCompactAdicCompletionIntegers
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle228
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle229
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle216
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Etale.Weakly
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
public import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace GlobalTheory.BertiniC


open KaehlerDifferential in
theorem false_of_dependent_derivatives {k A κ : Type} [Field k] [CharZero k] [CommRing A] [Algebra k A]
    [Field κ] [Algebra k κ] [Algebra A κ] [IsScalarTower k A κ] [Algebra.EssFiniteType k κ]
    (n : ℕ) (δ : Fin n → Derivation k A A) (ω : Fin n → KaehlerDifferential k A)
    (hω : ∀ a : A, KaehlerDifferential.D k A a = ∑ l, δ l a • ω l)
    {ι : Type} [Fintype ι] (f : ι → A) (M : ℕ) (J : Finset (Fin M)) (i₀ : Fin M) (p₀ : ι)
    (hi₀ : i₀ ∈ J) (t : Fin M × ι → κ) (ht : AlgebraicIndependent k t) (c : Fin M → κ)
    (r1 : ∀ i ∈ J, ∑ p, t (i, p) * algebraMap A κ (f p) = 0)
    (r2 : ∀ l, ∑ i ∈ J, c i * ∑ p, t (i, p) * algebraMap A κ (δ l (f p)) = 0)
    (r3 : c i₀ - 1 = 0) (s : κ) (r4s : s * algebraMap A κ (f p₀) - 1 = 0) : False := by
  have r4 : algebraMap A κ (f p₀) ≠ 0 := by
    intro h
    rw [h, mul_zero, zero_sub, neg_eq_zero] at r4s
    exact one_ne_zero r4s
  have hlin := GlobalTheory.T.linearIndependent_kaehlerD_of_algebraicIndependent k κ t ht
  set m : Fin n → KaehlerDifferential k κ := fun l => KaehlerDifferential.map k k A κ (ω l) with hm
  have hdψ : ∀ a : A, D k κ (algebraMap A κ a) = ∑ l, algebraMap A κ (δ l a) • m l := by
    intro a

    rw [← KaehlerDifferential.map_D k k A κ, hω a, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [LinearMap.map_smul, algebraMap_smul]
  have e1 : ∀ i ∈ J, ∑ p, algebraMap A κ (f p) • D k κ (t (i, p)) =
      - ∑ p, t (i, p) • D k κ (algebraMap A κ (f p)) := by
    intro i hi
    have h := congrArg (D k κ) (r1 i hi)

    rw [map_sum, map_zero] at h
    simp only [Derivation.leibniz, Finset.sum_add_distrib] at h
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h
  have e2 : ∑ i ∈ J, c i • ∑ p, t (i, p) • D k κ (algebraMap A κ (f p)) = 0 := by
    have : ∑ i ∈ J, c i • ∑ p, t (i, p) • D k κ (algebraMap A κ (f p)) =
        ∑ l, (∑ i ∈ J, c i * ∑ p, t (i, p) * algebraMap A κ (δ l (f p))) • m l := by
      simp only [hdψ, Finset.smul_sum, Finset.sum_smul, Finset.mul_sum, smul_smul, mul_assoc]
      conv_rhs => rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    rw [this]
    simp [r2]
  have key : ∑ x ∈ J ×ˢ (Finset.univ : Finset ι), (c x.1 * algebraMap A κ (f x.2)) • D k κ (t x) = 0 := by
    rw [Finset.sum_product]
    simp only [mul_smul, ← Finset.smul_sum]
    rw [Finset.sum_congr rfl (fun i hi => by rw [e1 i hi]), ]
    simp only [smul_neg, Finset.sum_neg_distrib, e2, neg_zero]
  have := linearIndependent_iff'.1 hlin _ _ key (i₀, p₀) (by simp [hi₀])
  rw [sub_eq_zero.1 r3, one_mul] at this
  exact r4 this

section Construction

variable {k A : Type} [Field k] [CommRing A] [Algebra k A] {n : ℕ}
  (δ : Fin n → Derivation k A A) {ι : Type} [Fintype ι] (f : ι → A) {M : ℕ}
  (J : Finset (Fin M)) (i₀ : Fin M) (p₀ : ι)

abbrev Var (M : ℕ) (ι : Type) := (Fin M × ι) ⊕ (Fin M ⊕ Unit)


open MvPolynomial in
noncomputable def relIdeal : Ideal (MvPolynomial (Var M ι) A) :=
  Ideal.span {x | (∃ i ∈ J, x = ∑ p, X (Sum.inl (i, p)) * C (f p)) ∨
    (∃ l, x = ∑ i ∈ J, X (Sum.inr (Sum.inl i)) * ∑ p, X (Sum.inl (i, p)) * C (δ l (f p))) ∨
    x = X (Sum.inr (Sum.inl i₀)) - 1 ∨ x = X (Sum.inr (Sum.inr ())) * C (f p₀) - 1}

end Construction


open MvPolynomial in
theorem no_dependence_of_general : ∀ (k A : Type) [Field k] [CharZero k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A] (n : ℕ) (δ : Fin n → Derivation k A A) (ω : Fin n → KaehlerDifferential k A), (∀ a : A, KaehlerDifferential.D k A a = ∑ l, δ l a • ω l) → ∀ {ι : Type} [Fintype ι] (f : ι → A) (M : ℕ) (J : Finset (Fin M)) (i₀ : Fin M) (p₀ : ι), i₀ ∈ J → ∃ Q : MvPolynomial (Fin M × ι) k, Q ≠ 0 ∧ ∀ u : Fin M × ι → k, MvPolynomial.eval u Q ≠ 0 → ∀ (K : Type) [Field K] [Algebra k K] (φ : A →ₐ[k] K) (c : Fin M → K), φ (f p₀) ≠ 0 → c i₀ = 1 → (∀ i ∈ J, φ (∑ p, u (i, p) • f p) = 0) → ¬ ∀ l, ∑ i ∈ J, c i * φ (δ l (∑ p, u (i, p) • f p)) = 0 := by
  intro k A _ _ _ _ _ n δ ω hω ι _ f M J i₀ p₀ hi₀
  classical
  set I := relIdeal δ f J i₀ p₀ with hIdef
  let T := MvPolynomial (Var M ι) A ⧸ I
  let gm : MvPolynomial (Fin M × ι) k →ₐ[k] T :=
    aeval (fun x => Ideal.Quotient.mk I (X (Sum.inl x)))
  have g1mem : ∀ i ∈ J, (∑ p, X (Sum.inl (i, p)) * C (f p) : MvPolynomial (Var M ι) A) ∈ I :=
    fun i hi => Ideal.subset_span (Or.inl ⟨i, hi, rfl⟩)
  have g2mem : ∀ l, (∑ i ∈ J, X (Sum.inr (Sum.inl i)) * ∑ p, X (Sum.inl (i, p)) * C (δ l (f p)) :
      MvPolynomial (Var M ι) A) ∈ I :=
    fun l => Ideal.subset_span (Or.inr (Or.inl ⟨l, rfl⟩))
  have g3mem : (X (Sum.inr (Sum.inl i₀)) - 1 : MvPolynomial (Var M ι) A) ∈ I :=
    Ideal.subset_span (Or.inr (Or.inr (Or.inl rfl)))
  have g4mem : (X (Sum.inr (Sum.inr ())) * C (f p₀) - 1 : MvPolynomial (Var M ι) A) ∈ I :=
    Ideal.subset_span (Or.inr (Or.inr (Or.inr rfl)))
  have hni : ¬ Function.Injective gm := by
    intro hinj
    let S : Submonoid T := (nonZeroDivisors (MvPolynomial (Fin M × ι) k)).map gm
    have hS : ∀ Q : MvPolynomial (Fin M × ι) k, Q ≠ 0 → gm Q ∈ S := fun Q hQ =>
      Submonoid.mem_map_of_mem _ (mem_nonZeroDivisors_of_ne_zero hQ)
    have hdisj : Disjoint ((⊥ : Ideal T) : Set T) S := by
      rw [Set.disjoint_left]
      rintro x hx ⟨Q, hQ, rfl⟩
      have h0 : gm Q = 0 := (Submodule.mem_bot _).1 hx
      have : Q = 0 := hinj (by rw [h0, map_zero])
      exact nonZeroDivisors.ne_zero hQ this
    obtain ⟨𝔮, h𝔮, -, hd⟩ := Ideal.exists_le_prime_disjoint ⊥ S hdisj
    haveI := h𝔮
    let D := T ⧸ 𝔮
    let κ := FractionRing D
    let π : MvPolynomial (Var M ι) A →+* κ :=
      (algebraMap D κ).comp ((Ideal.Quotient.mk 𝔮).comp (Ideal.Quotient.mk I))
    have hπC : ∀ a : A, π (C a) = algebraMap A κ a := by
      intro a
      show algebraMap D κ (Ideal.Quotient.mk 𝔮 (Ideal.Quotient.mk I (C a))) = _
      rw [IsScalarTower.algebraMap_apply A D κ]
      rfl
    have hπI : ∀ x ∈ I, π x = 0 := by
      intro x hx
      show algebraMap D κ (Ideal.Quotient.mk 𝔮 (Ideal.Quotient.mk I x)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero, map_zero]
    have ht : AlgebraicIndependent k (fun x : Fin M × ι => π (X (Sum.inl x))) := by
      rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
      intro Q hQ
      by_contra hQ0
      have heq : (aeval (fun x : Fin M × ι => π (X (Sum.inl x))) :
          MvPolynomial (Fin M × ι) k →ₐ[k] κ) =
          (IsScalarTower.toAlgHom k D κ).comp ((Ideal.Quotient.mkₐ k 𝔮).comp gm) := by
        ext x
        simp [π, gm]
      rw [heq] at hQ
      have h1 : Ideal.Quotient.mk 𝔮 (gm Q) = 0 :=
        (IsFractionRing.injective D κ) (hQ.trans (map_zero _).symm)
      rw [Ideal.Quotient.eq_zero_iff_mem] at h1
      exact Set.disjoint_left.1 hd h1 (hS Q hQ0)
    apply false_of_dependent_derivatives n δ ω hω f M J i₀ p₀ hi₀ _ ht (fun i => π (X (Sum.inr (Sum.inl i))))
    · intro i hi
      have := hπI _ (g1mem i hi)

      simpa only [map_sum, map_mul, hπC] using this
    · intro l
      have := hπI _ (g2mem l)

      simpa only [map_sum, map_mul, hπC] using this
    · have h3 : π (X (Sum.inr (Sum.inl i₀)) - 1) = 0 := hπI _ g3mem
      rw [RingHom.map_sub, RingHom.map_one] at h3
      exact h3
    · have h4 := hπI _ g4mem
      rw [RingHom.map_sub, RingHom.map_mul, hπC, RingHom.map_one] at h4
      exact h4
  obtain ⟨Q, hQ0, hQ⟩ : ∃ Q, Q ≠ 0 ∧ gm Q = 0 := by
    by_contra hcon
    push_neg at hcon
    exact hni ((injective_iff_map_eq_zero gm).2 fun Q hQ => by_contra fun h => hcon Q h hQ)
  refine ⟨Q, hQ0, ?_⟩
  intro u hu K _ _ φ c hφ hc hrel hδ
  let e : MvPolynomial (Var M ι) A →+* K := eval₂Hom φ.toRingHom
    (Sum.elim (fun x => algebraMap k K (u x)) (Sum.elim c (fun _ => (φ (f p₀))⁻¹)))
  have hI : I ≤ RingHom.ker e := by
    rw [hIdef, relIdeal, Ideal.span_le]
    rintro x (⟨i, hi, rfl⟩ | ⟨l, rfl⟩ | rfl | rfl) <;> simp only [SetLike.mem_coe, RingHom.mem_ker]
    · have := hrel i hi

      simpa [e, map_sum, Algebra.smul_def] using this
    · have := hδ l

      simpa [e, map_sum, Algebra.smul_def] using this
    · simp [e, hc]
    · simp [e, inv_mul_cancel₀ hφ]
  let e' : T →+* K := Ideal.Quotient.lift I e (fun a ha => hI ha)
  have hcomp : e'.comp gm.toRingHom = (algebraMap k K).comp (eval u) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      show e' (gm (C a)) = algebraMap k K (eval u (C a))
      rw [MvPolynomial.aeval_C]
      show e (algebraMap k (MvPolynomial (Var M ι) A) a) = _
      rw [MvPolynomial.algebraMap_apply, eval₂Hom_C, eval_C]
      exact φ.commutes a
    · intro x
      show e' (gm (X x)) = algebraMap k K (eval u (X x))
      rw [MvPolynomial.aeval_X, eval_X]
      show e (X (Sum.inl x)) = _
      rw [eval₂Hom_X']
      rfl
  have := RingHom.congr_fun hcomp Q
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
  rw [hQ, map_zero] at this
  exact hu ((algebraMap k K).injective (this.symm.trans (map_zero _).symm))

end GlobalTheory.BertiniC
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_invariant_derivations_quotient_bialgebra : ∀ (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] (I : Ideal O) (d : ℕ) (l : Fin d → (A →ₗ[O] O ⧸ I)), (∀ i a b, l i (a * b) = Coalgebra.counit (R := O) a • l i b + Coalgebra.counit (R := O) b • l i a) → ∃ D : Fin d → Derivation (O ⧸ I) ((O ⧸ I) ⊗[O] A) ((O ⧸ I) ⊗[O] A), ∀ i a, Bialgebra.counitAlgHom (O ⧸ I) ((O ⧸ I) ⊗[O] A) (D i (1 ⊗ₜ a)) = l i a := by
  first | exact @GlobalTheory.quotient_base_change_invariant_derivations | exact GlobalTheory.quotient_base_change_invariant_derivations | (intros; apply GlobalTheory.quotient_base_change_invariant_derivations <;> assumption)
end

section

open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.steinitz_pi_ideals_linearEquiv_of_classGroup_prod : ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (ι : Type) [Fintype ι] (I J : ι → (Ideal R)⁰), ∏ i, ClassGroup.mk0 (I i) = ∏ i, ClassGroup.mk0 (J i) → Nonempty (((i : ι) → (I i : Ideal R)) ≃ₗ[R] ((i : ι) → (J i : Ideal R))) := by
  first | exact @GlobalTheory.SteinitzProd.steinitz | exact GlobalTheory.SteinitzProd.steinitz | (intros; apply GlobalTheory.SteinitzProd.steinitz <;> assumption)
end

section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

noncomputable section

namespace GlobalTheory.BoundedGL

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem isCompact_le (c : WithZero (Multiplicative ℤ)) :
    IsCompact {x : w.adicCompletion E | Valued.v x ≤ c} := by
  by_cases hc : c = 0
  · have e : {x : w.adicCompletion E | Valued.v x ≤ c} = {0} := by
      ext x
      simp [hc]
    rw [e]
    exact isCompact_singleton
  · obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer E
    set u : w.adicCompletion E := ((π ^ (-WithZero.log c) : E) : w.adicCompletion E) with hu
    have hvu : Valued.v u = c := by
      rw [hu, valuedAdicCompletion_eq_valuation', map_zpow₀, hπ, ← WithZero.exp_zsmul]
      simp [WithZero.exp_log hc]
    have hu0 : u ≠ 0 := by
      intro h
      rw [h, map_zero] at hvu
      exact hc hvu.symm
    have hO : IsCompact {x : w.adicCompletion E | Valued.v x ≤ 1} := by
      have := PI.IntAdCpctOpenWork.isCompact_adicCompletionIntegers w
      convert this using 1
      ext x
      simp [mem_adicCompletionIntegers]
    have e : {x : w.adicCompletion E | Valued.v x ≤ c} = (fun y => u * y) '' {x | Valued.v x ≤ 1} := by
      ext x
      constructor
      · intro hx
        refine ⟨u⁻¹ * x, ?_, by simp [hu0]⟩
        show Valued.v (u⁻¹ * x) ≤ 1
        rw [map_mul, map_inv₀, hvu]
        exact inv_mul_le_one_of_le₀ hx zero_le'
      · rintro ⟨y, hy, rfl⟩
        show Valued.v (u * y) ≤ c
        rw [map_mul, hvu]
        exact mul_le_of_le_one_right' hy
    rw [e]
    exact hO.image (continuous_const_mul u)

theorem isCompact_bounded : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (c : WithZero (Multiplicative ℤ)), IsCompact {g : GL (Fin n) (w.adicCompletion E) | ∀ i j,
      Valued.v ((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c ∧
      Valued.v (((g⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c} := by
  intro E _ _ w n c
  set K := w.adicCompletion E
  set S : Set (Matrix (Fin n) (Fin n) K) := {A | ∀ i j, Valued.v (A i j) ≤ c} with hS
  have hK : IsCompact S := by
    have h : IsCompact (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => {x : K | Valued.v x ≤ c}) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_le w c
    have e : S = (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => {x : K | Valued.v x ≤ c}) :=
      Set.ext fun x => ⟨fun hx i _ j _ => hx i j, fun hx i j => hx i trivial j trivial⟩
    rw [e]; exact h
  have h := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) K)).isCompact_preimage
    (hK.prod (hK.image MulOpposite.continuous_op))
  convert h using 1
  ext g
  simp only [hS, Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply,
    Set.mem_prod, (MulOpposite.op_injective).mem_set_image]
  exact ⟨fun hg => ⟨fun i j => (hg i j).1, fun i j => (hg i j).2⟩, fun hg i j => ⟨hg.1 i j, hg.2 i j⟩⟩

end GlobalTheory.BoundedGL
end
end

section

namespace GlobalTheory

theorem etale_away_quotient_eq_localization :
    ∀ (B D : Type) [CommRing B] [IsDedekindDomain B] [CommRing D] [Algebra B D] [Algebra.Etale B D]
      (f : B), f ≠ 0 → ∀ (P : Ideal B), P.IsMaximal → f ∈ P → ∀ (Q : Ideal D), Q.IsPrime →
      Q.comap (algebraMap B D) = P → (∀ d : D, ∃ b : B, d - algebraMap B D b ∈ Q) →
      ∃ g : D, (∀ a : Localization.Away g, ∃ b : B,
          a - algebraMap B (Localization.Away g) b ∈
            Ideal.span {algebraMap B (Localization.Away g) f}) ∧
        ∀ b : B, algebraMap B (Localization.Away g) b ∈
            Ideal.span {algebraMap B (Localization.Away g) f} ↔
          ∃ s : B, s ∉ P ∧ s * b ∈ Ideal.span {f} := by
  intro B D _ _ _ _ _ f hf P hP hfP Q hQ hQP hres

  have hQmax : Q.IsMaximal := by
    rw [Ideal.isMaximal_iff]
    refine ⟨fun h1 => ?_, fun J x hQJ hx hxJ => ?_⟩
    · have : (1 : B) ∈ Q.comap (algebraMap B D) := by simpa using h1
      rw [hQP] at this
      exact hP.ne_top ((Ideal.eq_top_iff_one _).2 this)
    · obtain ⟨b, hb⟩ := hres x
      have hbP : b ∉ P := by
        intro hbP
        apply hx
        have : algebraMap B D b ∈ Q := by
          rw [← Ideal.mem_comap, hQP]; exact hbP
        simpa using Q.add_mem hb this
      obtain ⟨c, hc⟩ : ∃ c : B, c * b - 1 ∈ P := by
        obtain ⟨c, i, hi, hci⟩ := hP.exists_inv hbP
        refine ⟨c, ?_⟩
        have : c * b - 1 = -i := by rw [← hci]; ring
        rw [this]; exact P.neg_mem hi
      have h1 : algebraMap B D (c * b - 1) ∈ Q := by
        rw [← Ideal.mem_comap, hQP]; exact hc
      have h2 : algebraMap B D c * x - 1 ∈ Q := by
        have : algebraMap B D c * x - 1 =
            algebraMap B D c * (x - algebraMap B D b) + algebraMap B D (c * b - 1) := by
          simp only [map_sub, map_mul, map_one]; ring
        rw [this]
        exact Q.add_mem (Q.mul_mem_left _ hb) h1
      have h3 : algebraMap B D c * x ∈ J := J.mul_mem_left _ hxJ
      have : (1 : D) = algebraMap B D c * x - (algebraMap B D c * x - 1) := by ring
      rw [this]
      exact J.sub_mem h3 (hQJ h2)
  obtain ⟨g, hgQ, hQ'⟩ := GlobalTheory.T.isolate_maximal_among_primes_containing_etale B D f hf Q hQmax
  refine ⟨g, ?_⟩
  haveI : Algebra.Etale D (Localization.Away g) := Algebra.Etale.of_isLocalizationAway g
  haveI : Algebra.Etale B (Localization.Away g) := Algebra.Etale.comp B D (Localization.Away g)
  have hφ : ∀ b : B, algebraMap B (Localization.Away g) b =
      algebraMap D (Localization.Away g) (algebraMap B D b) := fun b =>
    IsScalarTower.algebraMap_apply B D (Localization.Away g) b

  have hunit := GlobalTheory.T.localization_inverse_mod_f B D f P Q g hQP hQ'

  have hker : ∀ b : B, (∃ s : B, s ∉ P ∧ s * b ∈ Ideal.span {f}) →
      algebraMap B (Localization.Away g) b ∈
        Ideal.span {algebraMap B (Localization.Away g) f} := by
    rintro b ⟨s, hs, hsb⟩
    obtain ⟨t, ht⟩ := hunit s hs
    have h1 : algebraMap B (Localization.Away g) (s * b) ∈
        Ideal.span {algebraMap B (Localization.Away g) f} := by
      rw [Ideal.mem_span_singleton] at hsb ⊢
      obtain ⟨c, hc⟩ := hsb
      exact ⟨algebraMap B _ c, by rw [hc, map_mul]⟩
    have : algebraMap B (Localization.Away g) b = algebraMap B _ (s * b) * t -
        (algebraMap B _ s * t - 1) * algebraMap B (Localization.Away g) b := by
      rw [map_mul]; ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ h1) (Ideal.mul_mem_right _ _ ht)
  refine ⟨?_, fun b => ⟨fun hb => ?_, hker b⟩⟩
  ·
    obtain ⟨N, hN⟩ := GlobalTheory.T.dedekind_power_localization B f hf P hP
    have hPN : (P ^ N).map (algebraMap B (Localization.Away g)) ≤
        Ideal.span {algebraMap B (Localization.Away g) f} := by
      rw [Ideal.map_le_iff_le_comap]
      intro b hb
      exact hker b (hN b hb)
    have hfib : ∀ Q' : Ideal (Localization.Away g), Q'.IsPrime →
        P.map (algebraMap B (Localization.Away g)) ≤ Q' →
        Q' = Q.map (algebraMap D (Localization.Away g)) := by
      intro Q' hQ'p hPQ'
      have hc : Q'.comap (algebraMap D (Localization.Away g)) = Q := by
        apply hQ' _ (Ideal.comap_isPrime _ _)
        · rw [Ideal.mem_comap, ← hφ]
          exact hPQ' (Ideal.mem_map_of_mem _ hfP)
        · intro hg
          rw [Ideal.mem_comap] at hg
          exact hQ'p.ne_top (Ideal.eq_top_of_isUnit_mem _ hg
            (IsLocalization.Away.algebraMap_isUnit g))
      rw [← hc]
      exact (IsLocalization.map_under (Submonoid.powers g) (Localization.Away g) Q').symm
    have hle := GlobalTheory.T.etale_unique_prime_le_map_maximal B (Localization.Away g) P hP
      (Q.map (algebraMap D (Localization.Away g))) hfib
    have hres' := GlobalTheory.T.localization_residue_approximation B D P hP Q g hgQ hQP hres
    refine GlobalTheory.T.nilpotent_approximation_surjective B (Localization.Away g) P _ N (fun a => ?_) hPN
    obtain ⟨b, hb⟩ := hres' a
    exact ⟨b, Ideal.mem_sup_left (hle hb)⟩
  ·
    have hgu : IsUnit (algebraMap D (Localization.AtPrime Q) g) :=
      IsLocalization.map_units (Localization.AtPrime Q) (⟨g, hgQ⟩ : Q.primeCompl)
    let ρ : Localization.Away g →+* Localization.AtPrime Q := IsLocalization.Away.lift g hgu
    have hρ : ∀ d : D, ρ (algebraMap D (Localization.Away g) d) =
        algebraMap D (Localization.AtPrime Q) d :=
      fun d => IsLocalization.Away.lift_eq g hgu d
    have e : ∀ x : B, algebraMap B (Localization.AtPrime Q) x =
        ρ (algebraMap B (Localization.Away g) x) := by
      intro x
      rw [hφ, hρ, IsScalarTower.algebraMap_apply B D (Localization.AtPrime Q)]
    have hloc : algebraMap B (Localization.AtPrime Q) b ∈
        Ideal.span {algebraMap B (Localization.AtPrime Q) f} := by
      rw [Ideal.mem_span_singleton] at hb ⊢
      obtain ⟨c, hc⟩ := hb
      exact ⟨ρ c, by rw [e, e, hc, map_mul]⟩
    obtain ⟨s, hs, hsb⟩ := GlobalTheory.T.flat_localization_membership B D Q f b hloc
    rw [hQP] at hs
    exact ⟨s, hs, hsb⟩

end GlobalTheory
end

section

open IsLocalRing


theorem _root_.GlobalTheory.T.exists_complete_dvr_with_proportional_valuations : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ ψ : R →+* V, IsLocalHom ψ → ∀ (I : Type) [Finite I] (a : I → R) (k : I → ℕ), (∀ i, Associated (ψ (a i)) (ϖ ^ k i)) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (ϖ' : W) (ψ' : R →+* W) (m m' : ℕ) (k' : I → ℕ), IsAdicComplete (maximalIdeal W) W ∧ Irreducible ϖ' ∧ Function.Injective ψ' ∧ IsLocalHom ψ' ∧ 1 ≤ m ∧ 1 ≤ m' ∧ ∀ i, Associated (ψ' (a i)) (ϖ' ^ k' i) ∧ m * k' i = m' * k i := by
  first | exact @GlobalTheory.PropDvr.exists_cdvr_proportional | exact GlobalTheory.PropDvr.exists_cdvr_proportional | (intros; apply GlobalTheory.PropDvr.exists_cdvr_proportional <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_dvr_extension_of_essentially_etale_local : ∀ {K K' R S : Type} [Field K] [Field K'] [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] [IsLocalRing R] [IsLocalRing S] [Algebra R K] [Algebra S K'] [IsFractionRing R K] [IsFractionRing S K'] (φ : K →+* K') (σ : R →+* S) [IsLocalHom σ], σ.Flat → σ.FormallyEtale → σ.EssFiniteType → φ.comp (algebraMap R K) = (algebraMap S K').comp σ → ∀ V : ValuationSubring K, IsDiscreteValuationRing V → (∀ a, algebraMap R K a ∈ V) → ∃ (V' : ValuationSubring K') (h : ∀ x ∈ V, φ x ∈ V'), IsDiscreteValuationRing V' ∧ (∀ b, algebraMap S K' b ∈ V') ∧ (∀ x, φ x ∈ V' → x ∈ V) ∧ (φ.restrict V V' h).FormallyEtale ∧ (φ.restrict V V' h).EssFiniteType := by
  first | exact @GlobalTheory.exists_valuationSubring_extend_of_formallyEtale | exact GlobalTheory.exists_valuationSubring_extend_of_formallyEtale | (intros; apply GlobalTheory.exists_valuationSubring_extend_of_formallyEtale <;> assumption)
end

section

open Polynomial

theorem _root_.GlobalTheory.T.exists_dvr_localization_of_minimal_prime' : ∀ {κ : Type} [Field κ] (R : Subring κ) [IsNoetherianRing R] [IsIntegrallyClosed R] [IsFractionRing R κ] (Q : Ideal R) [Q.IsPrime], Q ≠ ⊥ → (∀ p : Ideal R, p.IsPrime → p ≠ ⊥ → p ≤ Q → p = Q) → ∃ W : ValuationSubring κ, IsDiscreteValuationRing W ∧ (∀ r : R, (r : κ) ∈ W) ∧ (∀ r : R, r ∉ Q → (r : κ)⁻¹ ∈ W) ∧ (∀ r : R, r ∈ Q → r ≠ 0 → (r : κ)⁻¹ ∉ W) ∧ (∀ w ∈ W, ∃ b s : R, s ∉ Q ∧ w = b / s) := by
  first | exact @GlobalTheory.exists_dvr_localization_of_minimal_prime | exact GlobalTheory.exists_dvr_localization_of_minimal_prime | (intros; apply GlobalTheory.exists_dvr_localization_of_minimal_prime <;> assumption)
end
