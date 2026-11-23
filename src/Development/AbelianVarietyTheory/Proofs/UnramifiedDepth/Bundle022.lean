module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle003
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FrobeniusLiftEmbeddingsUnit
import Mathlib.Algebra.CharP.Subring
public import Formalism.LocalToGlobal.CharacterGerms.GeNatCast
public import Mathlib.Data.Matrix.Mul
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle015
public import Formalism.LocalToGlobal.CharacterGerms.RowTieFB
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ActionConvergesLadicCauchyAndStar
public import ReciprocityTheory.DualLattices.Bundle021
public import Mathlib.CategoryTheory.Category.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Formalism.IncomingBounds.Bundle001
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.FieldTheory.Finite.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.ringHom_eq_of_congruent_integral_unramified : ∀ (C : Type) [Field C] (V : VF C) (O : Type) [CommRing O] (d : ℕ), 0 < d → ∀ ε : O, (∃ y, ε * ε - ε = (V.l : O) * y) → (∀ x : O, ∃ y, ε * (x ^ (V.l ^ d) - x) = (V.l : O) * y) → ∀ ψ φ : O →+* C, (∀ x, V.Ge 0 (ψ x)) → (∀ x, V.Ge 0 (φ x)) → V.MM (ψ ε - 1) → (∀ x, V.MM (ψ x - φ x)) → ψ = φ := by
  first | exact @GlobalTheory.CongruentCharacters.eq_of_congruent | exact GlobalTheory.CongruentCharacters.eq_of_congruent | (intros; apply GlobalTheory.CongruentCharacters.eq_of_congruent <;> assumption)
end

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.ResidueChar

theorem exists_pow_of_finite_field {K k : Type} [Field K] [Finite K] [CommRing k] [IsDomain k]
    (l : ℕ) [Fact l.Prime] [CharP K l] (f g : K →+* k) :
    ∃ j : ℕ, ∀ y, g y = f y ^ l ^ j := by
  classical
  have := Fintype.ofFinite K
  have hmem : ∀ y, g y ∈ f.range := fun y => by
    have h1 : (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial K) =
        ∏ a : K, (Polynomial.X - Polynomial.C a) := by
      have hm : (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial K).Monic :=
        Polynomial.monic_X_pow_sub (by
          rw [Polynomial.degree_X]; exact_mod_cast Fintype.one_lt_card)
      have := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm (by
        rw [FiniteField.roots_X_pow_card_sub_X,
          Polynomial.natDegree_X_pow_sub_X (R := K) Fintype.one_lt_card]
        rfl)
      rw [← this, FiniteField.roots_X_pow_card_sub_X]
      rfl
    have h2 := congrArg (Polynomial.eval₂RingHom f (g y)) h1
    rw [map_prod] at h2
    simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C] at h2
    rw [← map_pow, FiniteField.pow_card, sub_self] at h2
    obtain ⟨a, -, ha⟩ := Finset.prod_eq_zero_iff.1 h2.symm
    exact ⟨a, (sub_eq_zero.1 ha).symm⟩
  let e : K ≃+* f.range := RingEquiv.ofBijective f.rangeRestrict
    ⟨f.rangeRestrict.injective, f.rangeRestrict_surjective⟩
  let s : K →+* K := e.symm.toRingHom.comp (g.codRestrict f.range hmem)
  have hs : ∀ y, f (s y) = g y := fun y =>
    congrArg Subtype.val (e.apply_symm_apply (g.codRestrict f.range hmem y))
  let := ZMod.algebra K l
  let s' : K →ₐ[ZMod l] K := { s with
    commutes' := fun r => DFunLike.congr_fun
      (Subsingleton.elim (s.comp (algebraMap (ZMod l) K)) (algebraMap (ZMod l) K)) r }
  obtain ⟨j, hj⟩ := (FiniteField.bijective_frobeniusAlgHom_pow (ZMod l) K).2 s'
  refine ⟨j, fun y => ?_⟩
  have : s y = y ^ l ^ (j : ℕ) := by
    have h := DFunLike.congr_fun hj y
    simp only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card] at h
    exact h.symm
  rw [← hs, this, map_pow]

theorem exists_eq_of_ker_le {O k : Type} [CommRing O] [CommRing k] [IsDomain k] {d : ℕ} [NeZero d]
    (l : ℕ) [Fact l.Prime] [CharP k l] (φ : ZMod d → (O →+* k))
    (h : ∀ a x, φ (a + 1) x = φ a x ^ l) (g : O →+* k) (hg : ∀ x, φ 0 x = 0 → g x = 0) :
    ∃ a, ∀ x, g x = φ a x := by
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  have hq : 1 < l ^ d := Nat.one_lt_pow (NeZero.ne d) hl
  have hper : ∀ x, φ 0 x ^ l ^ d = φ 0 x := fun x => by
    rw [← TeichSeq.frob_iter l φ h]; simp
  have hfin : ((φ 0).range : Set k).Finite := by
    have hne : (Polynomial.X ^ l ^ d - Polynomial.X : Polynomial k) ≠ 0 :=
      (Polynomial.monic_X_pow_sub (by
        rw [Polynomial.degree_X]; exact_mod_cast hq)).ne_zero
    refine (Polynomial.finite_setOfPred_isRoot hne).subset ?_
    rintro _ ⟨x, rfl⟩
    simp [hper]
  have : Finite (φ 0).range := hfin
  let : Field (φ 0).range := (Finite.isField_of_domain _).toField
  let g' : (φ 0).range →+* k :=
    (φ 0).rangeRestrict.liftOfSurjective (φ 0).rangeRestrict_surjective
      ⟨g, fun x hx => hg x (congrArg Subtype.val (RingHom.mem_ker.1 hx))⟩
  have hg' : ∀ x, g' ((φ 0).rangeRestrict x) = g x := fun x =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ x
  obtain ⟨j, hj⟩ := exists_pow_of_finite_field l (φ 0).range.subtype g'
  refine ⟨0 + (j : ZMod d), fun x => ?_⟩
  rw [TeichSeq.frob_iter l φ h, ← hg', hj]
  rfl


open TeichSeq in
theorem main : ∀ (C : Type) [Field C] (V : VF C) (O : Type) [CommRing O] (d : ℕ) [NeZero d] (em : ZMod d → (O →+* C)), (∀ a x, V.Ge 0 (em a x)) → (∀ a x, V.MM (em (a + 1) x - em a x ^ V.l)) → ∀ ψ : O →+* C, (∀ x, V.Ge 0 (ψ x)) → (∀ x, (∀ a, V.MM (em a x)) → V.MM (ψ x)) → ∃ a, ∀ x, V.MM (ψ x - em a x) := by
  intro C _ V O _ d _ em hint hfrob ψ hψ hker
  have : Fact V.l.Prime := ⟨V.l_prime⟩
  let π : intRing V →+* intRing V ⧸ maxId V := Ideal.Quotient.mk _
  let e : ZMod d → (O →+* intRing V) := fun a => (em a).codRestrict (intRing V) (hint a)
  let φ : ZMod d → (O →+* intRing V ⧸ maxId V) := fun a => π.comp (e a)
  let p : O →+* intRing V := ψ.codRestrict (intRing V) hψ
  have hπ : ∀ u w : intRing V, π u = π w ↔ V.MM ((u : C) - w) := fun u w => Ideal.Quotient.eq
  have hπ0 : ∀ u : intRing V, π u = 0 ↔ V.MM (u : C) := fun u => Ideal.Quotient.eq_zero_iff_mem
  have hφ : ∀ a x, φ (a + 1) x = φ a x ^ V.l := fun a x => by
    show π (e (a + 1) x) = π (e a x) ^ V.l
    rw [← map_pow, hπ]
    exact hfrob a x
  have : CharP (intRing V ⧸ maxId V) V.l := by
    refine (CharP.charP_iff_prime_eq_zero V.l_prime).2 ?_
    rw [← map_natCast π, hπ0]
    simpa using mm_of_ge_one V VF.ge_l
  obtain ⟨a, ha⟩ := exists_eq_of_ker_le V.l φ hφ (π.comp p) (fun x hx => by
    refine (hπ0 (p x)).2 (hker x fun a => (hπ0 (e a x)).1 ?_)
    have := frob_iter V.l φ hφ 0 x a.val
    rw [hx, zero_pow (pow_ne_zero _ V.l_prime.ne_zero)] at this
    show φ a x = 0
    simpa using this)
  exact ⟨a, fun x => (hπ (p x) (e a x)).1 (ha x)⟩

end GlobalTheory.ResidueChar
end

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.frobenius_lift_embeddings_unit : ∀ (C : Type) [Field C] [CharZero C] (V : VF C), (∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) → ∀ (O : Type) [CommRing O] (d : ℕ) [NeZero d] (em : ZMod d → (O →+* C)), (∀ a x, V.Ge 0 (em a x)) → (∀ a x, V.MM (em (a + 1) x - em a x ^ V.l)) → (∀ a a' : ZMod d, a ≠ a' → ∃ x, V.v (em a x - em a' x) = 0) → (∃ ε : O, (∃ y, ε * ε - ε = (V.l : O) * y) ∧ (∀ a, V.MM (em a ε - 1)) ∧ ∀ x : O, (∀ a, V.MM (em a x)) → ∃ y, ε * x = (V.l : O) * y) → ∃ (N : ℕ) (ζ : ZMod d → C) (s : ℕ → O), V.v (N : C) = 0 ∧ (∀ a, ζ a ^ N = 1) ∧ Function.Injective ζ ∧ (∀ a, ζ (a + 1) = ζ a ^ V.l) ∧ (∀ n, ∃ y, s (n + 1) - s n = (V.l : O) ^ n * y) ∧ ∀ (a : ZMod d) (K : ℕ), ∃ n0, ∀ n ≥ n0, V.Ge K (ζ a - em a (s n)) := by
  first | exact @GlobalTheory.exists_teichmueller_sequence | exact GlobalTheory.exists_teichmueller_sequence | (intros; apply GlobalTheory.exists_teichmueller_sequence <;> assumption)
end

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.exists_integral_character_generalizedEigen : ∀ (C : Type) [Field C] (V : VF C) (O : Type) [CommRing O] (κ : Type) [Fintype κ] [DecidableEq κ] (L : O →+* Matrix κ κ C), (∀ x i j, V.Ge 0 (L x i j)) → ∀ (χ : O → C) (w : κ → C), w ≠ 0 → (∀ x, ∃ k : ℕ, ((L x - χ x • (1 : Matrix κ κ C)) ^ k).mulVec w = 0) → ∃ ψ : O →+* C, (∀ x, ψ x = χ x) ∧ ∀ x, V.Ge 0 (ψ x) := by
  first | exact @GlobalTheory.GenChar.exists_character | exact GlobalTheory.GenChar.exists_character | (intros; apply GlobalTheory.GenChar.exists_character <;> assumption)
end

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.actionConverges_ladic_cauchy_and_star : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (a : ℕ → O), (∀ n, ∃ y, a (n + 1) - a n = (V.l : O) ^ n * y) → ActCv Y a ∧ ActCv Y (fun n => star (a n)) := by
  first | exact @GlobalTheory.ActionLimit.main | exact GlobalTheory.ActionLimit.main | (intros; apply GlobalTheory.ActionLimit.main <;> assumption)
end

section

open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory

private def btPolySub (p : ℕ) (g : ℕ) (W : Type) [CommRing W] :
    Subalgebra W (MvPolynomial (Fin g) W) where
  carrier := {q | ∀ m : Fin g →₀ ℕ, (∃ i, ¬ p ∣ m i) →
    AddMonoidAlgebra.coeff q m ∈ Ideal.span {(p : W)}}
  add_mem' := by
    intro a b ha hb m hm
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    exact Ideal.add_mem _ (ha m hm) (hb m hm)
  mul_mem' := by
    intro a b ha hb m hm
    obtain ⟨i, hi⟩ := hm
    rw [MvPolynomial.coeff_mul]
    refine Ideal.sum_mem _ fun x hx => ?_
    have hx' : x.1 + x.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    by_cases h1 : p ∣ x.1 i
    · refine Ideal.mul_mem_left _ _ (hb _ ⟨i, fun h2 => hi ?_⟩)
      rw [← hx', Finsupp.add_apply]
      exact dvd_add h1 h2
    · exact Ideal.mul_mem_right _ _ (ha _ ⟨i, h1⟩)
  algebraMap_mem' := by
    intro r m hm
    obtain ⟨i, hi⟩ := hm
    rw [MvPolynomial.algebraMap_eq, MvPolynomial.coeff_C, ite_eq_right]
    · exact Ideal.zero_mem _
    · rintro rfl
      exact hi (by simp)

private lemma btPoly_map_tEval {R₀ : Type} [CommRing R₀] {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (f : MvPowerSeries ι R₀) {S S' : Type} [CommRing S] [Algebra R₀ S] [CommRing S']
    [Algebra R₀ S'] (φ : S →ₐ[R₀] S') (a : ι → S) :
    φ (tEval N f a) = tEval N f (fun i => φ (a i)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [tEval, map_sum, map_prod]

private lemma btPoly_unif {ι S : Type} [Fintype ι] [CommRing S] (a : ι → S)
    (h : ∀ i, IsNilpotent (a i)) : ∃ M, ∀ M' ≥ M, ∀ i, a i ^ M' = 0 := by
  choose n hn using h
  refine ⟨Finset.univ.sup n, fun M' hM i => ?_⟩
  exact pow_eq_zero_of_le ((Finset.le_sup (Finset.mem_univ i)).trans hM) (hn i)

private lemma btPoly_nil {R₀ : Type} [CommRing R₀]
    (H : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (f : MvPowerSeries ι R₀) (S : Type) [CommRing S]
      [Algebra R₀ S] (a : ι → S), (∀ i, IsNilpotent (a i)) →
      nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a))
    {g : ℕ} {B : BX R₀} {K : LAlg R₀} (ch : FormalChartAtZero B K g) (S : Type) [CommRing S] [Algebra R₀ S]
    (a : Fin g → S) (ha : ∀ i, IsNilpotent (a i)) (n : ℕ) :
    ∀ k, IsNilpotent (nsmulF ch.F a n k) := by
  have h0 : ∀ k, algebraMap R₀ S (MvPowerSeries.coeff 0 (ch.F k)) = 0 := by
    intro k
    have h1 := congrFun (ch.F_unit S 0 (fun _ => IsNilpotent.zero)) k
    have h2 := H (ch.F k) S (Sum.elim (0 : Fin g → S) (0 : Fin g → S))
      (by rintro (i | i) <;> exact IsNilpotent.zero)
    have h3 : Ideal.span (Set.range (Sum.elim (0 : Fin g → S) (0 : Fin g → S))) = ⊥ := by
      rw [Ideal.span_eq_bot]
      rintro _ ⟨i | i, rfl⟩ <;> rfl
    rw [h3, Ideal.mem_bot] at h2
    change nEval _ _ = 0 at h1
    rw [h1] at h2
    simpa using h2
  induction n with
  | zero => intro k; exact IsNilpotent.zero
  | succ n ih =>
    intro k
    have hn : ∀ i, IsNilpotent (Sum.elim (nsmulF ch.F a n) a i) := by
      rintro (i | i)
      · exact ih i
      · exact ha i
    have h2 := H (ch.F k) S _ hn
    rw [h0, sub_zero] at h2
    have h3 : Ideal.span (Set.range (Sum.elim (nsmulF ch.F a n) a)) ≤ nilradical S := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hn i
    exact h3 h2

theorem fAdd_nsmulF_eq_eval_poly_frob :
  (∀ {R₀ : Type} [CommRing R₀] {ι : Type} [Fintype ι] [DecidableEq ι] (f : MvPowerSeries ι R₀) (S : Type) [CommRing S] [Algebra R₀ S] (a : ι → S),
    (∀ N : ℕ, (∀ i, a i ^ N = 0) → nEval f a = tEval N f a) ∧
    ((∀ i, IsNilpotent (a i)) → (∀ (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S'), φ (nEval f a) = nEval f (fun i => φ (a i))) ∧
      nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a))) →
  (∀ {R₀ : Type} [CommRing R₀] (p : ℕ) [Fact p.Prime] {g : ℕ} {B : BX R₀} (K : LAlg R₀) (ch : FormalChartAtZero B K g), PSerFrobStatement p K ch) →
  (∀ {R₀ : Type} [CommRing R₀] (p : ℕ) [Fact p.Prime] {g : ℕ} {B : BX R₀} {K : LAlg R₀} (ch : FormalChartAtZero B K g) (W : Type) [CommRing W] [Algebra R₀ W] (c : Fin g → W),
    (∀ i, IsNilpotent (c i)) → ∀ N : ℕ, ∃ Γ : Fin g → MvPolynomial (Fin g) W,
      (∀ k m, (∃ i, ¬ p ∣ m i) → AddMonoidAlgebra.coeff (Γ k) m ∈ Ideal.span {(p : W)}) ∧
      ∀ y : Fin g → W, (∀ i, y i ^ N = 0) → fAdd ch.F c (nsmulF ch.F y p) = fun k => MvPolynomial.eval y (Γ k)) := by
  intro H1 H2 R₀ _ p _ g B K ch W _ _ c hc N
  obtain ⟨G, hG, hGe⟩ := H2 p K ch N
  let I : Ideal (MvPolynomial (Fin g) R₀) := Ideal.span (Set.range fun j => MvPolynomial.X j ^ N)
  let x : Fin g → MvPolynomial (Fin g) R₀ ⧸ I := fun j => Ideal.Quotient.mk I (MvPolynomial.X j)
  have hx : ∀ j, x j ^ N = 0 := fun j => by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨j, rfl⟩
  have hae : (MvPolynomial.aeval x : MvPolynomial (Fin g) R₀ →ₐ[R₀] _) = Ideal.Quotient.mkₐ R₀ I := by
    ext j; simp [x]
  have hnil : ∀ k, IsNilpotent (Ideal.Quotient.mk I (G k)) := fun k => by
    have := btPoly_nil (fun f S _ _ a ha => ((H1 f S a).2 ha).2) ch _ x (fun i => ⟨N, hx i⟩) p k
    rw [hGe _ x hx, hae] at this
    exact this
  obtain ⟨M₁, hM₁⟩ := btPoly_unif _ hnil
  obtain ⟨M₂, hM₂⟩ := btPoly_unif _ hc
  let z : Fin g ⊕ Fin g → MvPolynomial (Fin g) W :=
    Sum.elim (fun i => MvPolynomial.C (c i)) (fun i => MvPolynomial.map (algebraMap R₀ W) (G i))
  refine ⟨fun k => tEval (max M₁ M₂) (ch.F k) z, fun k => ?_, fun y hy => ?_⟩
  · change tEval (max M₁ M₂) (ch.F k) z ∈ btPolySub p g W
    unfold tEval
    refine Subalgebra.sum_mem _ fun e _ => Subalgebra.mul_mem _ ?_
      (Subalgebra.prod_mem _ fun i _ => Subalgebra.pow_mem _ ?_ _)
    · rw [IsScalarTower.algebraMap_apply R₀ W]
      exact Subalgebra.algebraMap_mem _ _
    · rcases i with i | i
      · exact Subalgebra.algebraMap_mem (btPolySub p g W) (c i)
      · intro m hm
        obtain ⟨r, hr⟩ := hG i m hm
        change AddMonoidAlgebra.coeff (MvPolynomial.map (algebraMap R₀ W) (G i)) m ∈ _
        rw [MvPolynomial.coeff_map, hr, map_mul, map_natCast]
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  · funext k
    have hI : ∀ q ∈ I, MvPolynomial.aeval y q = (0 : W) := by
      intro q hq
      have : I ≤ RingHom.ker (MvPolynomial.aeval y : MvPolynomial (Fin g) R₀ →ₐ[R₀] W) := by
        rw [Ideal.span_le]
        rintro _ ⟨j, rfl⟩
        simp [RingHom.mem_ker, hy j]
      exact this hq
    have e1 := btPoly_map_tEval (max M₁ M₂) (ch.F k)
      ((MvPolynomial.aeval y : MvPolynomial (Fin g) W →ₐ[W] W).restrictScalars R₀) z
    have e2 : (fun i => ((MvPolynomial.aeval y : MvPolynomial (Fin g) W →ₐ[W] W).restrictScalars R₀)
        (z i)) = Sum.elim c (fun k => MvPolynomial.aeval y (G k)) := by
      funext i
      rcases i with i | i
      · simp [z]
      · simp only [z, AlgHom.coe_restrictScalars', Sum.elim_inr]
        exact MvPolynomial.aeval_map_algebraMap W y (G i)
    rw [e2] at e1
    rw [hGe W y hy]
    change nEval _ _ = _
    rw [(H1 (ch.F k) W _).1 (max M₁ M₂), ← e1]
    · simp
    · rintro (i | i)
      · exact hM₂ _ (le_max_right _ _) i
      · have := hM₁ _ (le_max_left M₁ M₂) i
        rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at this
        have := hI _ this
        rwa [map_pow] at this

end GlobalTheory
end
