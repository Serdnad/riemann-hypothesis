module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle047
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle082
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import ReciprocityTheory.Hypotheses.GalCohDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Mathlib.LinearAlgebra.FreeModule.Norm
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
import Formalism.GaloisCohomology.StatementLoc

@[expose] public section

section

open Polynomial

noncomputable section

namespace GlobalTheory.LinSys

section Bounded

variable {k A : Type} [Field k] [CommRing A] [Algebra k A] [Algebra k[X] A]
  [IsScalarTower k k[X] A]

theorem repr_smul_const {n : ℕ} (b : Module.Basis (Fin n) k[X] A) (c : k) (f : A) (i : Fin n) :
    b.repr (c • f) i = C c * b.repr f i := by
  rw [← algebraMap_smul k[X] c f, map_smul, Finsupp.smul_apply, smul_eq_mul,
    Polynomial.algebraMap_eq]

def boundedIn {n : ℕ} (b : Module.Basis (Fin n) k[X] A) (D : Ideal A) (d : ℕ) : Submodule k A where
  carrier := {f | f ∈ D ∧ ∀ i, (b.repr f i).natDegree ≤ d}
  zero_mem' := ⟨D.zero_mem, fun i => by simp⟩
  add_mem' := fun {f g} hf hg => ⟨D.add_mem hf.1 hg.1, fun i => by
    rw [map_add (f := _), Finsupp.add_apply]
    exact (natDegree_add_le _ _).trans (max_le (hf.2 i) (hg.2 i))⟩
  smul_mem' := fun c f hf => ⟨by rw [Algebra.smul_def]; exact D.mul_mem_left _ hf.1, fun i => by
    rw [repr_smul_const]
    exact (natDegree_C_mul_le _ _).trans (hf.2 i)⟩

def coeffMap {n : ℕ} (b : Module.Basis (Fin n) k[X] A) (D : Ideal A) (d : ℕ) :
    boundedIn b D d →ₗ[k] (Fin n → Fin (d + 1) → k) where
  toFun f i j := (b.repr (f : A) i).coeff j
  map_add' f g := by ext i j; simp [coeff_add]
  map_smul' c f := by ext i j; simp [repr_smul_const, coeff_C_mul]

theorem coeffMap_injective {n : ℕ} (b : Module.Basis (Fin n) k[X] A) (D : Ideal A) (d : ℕ) :
    Function.Injective (coeffMap b D d) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  have h0 : ∀ i, b.repr (f : A) i = 0 := by
    intro i
    ext j
    by_cases hj : j ≤ d
    · have := congrFun (congrFun hf i) ⟨j, Nat.lt_succ_of_le hj⟩
      simpa [coeffMap] using this
    · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (f.2.2 i) (not_le.1 hj))]; simp
  have : (f : A) = 0 := by
    rw [← b.sum_repr (f : A)]; simp [h0]
  exact Subtype.ext this

instance finiteDimensional_boundedIn {n : ℕ} (b : Module.Basis (Fin n) k[X] A) (D : Ideal A)
    (d : ℕ) : FiniteDimensional k (boundedIn b D d) :=
  Module.Finite.of_injective (coeffMap b D d) (coeffMap_injective b D d)

end Bounded

theorem isCoprime_of_not_le {A : Type} [CommRing A] {M D : Ideal A} (hM : M.IsMaximal)
    (h : ¬ D ≤ M) : IsCoprime M D := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra h'
  exact h (le_sup_right.trans (hM.eq_of_le h' le_sup_left).ge)

end GlobalTheory.LinSys


open GlobalTheory.LinSys in
theorem GlobalTheory.linear_system_setup : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A] [Module.Free k[X] A] (N : ℕ) (P₀ : Ideal A), 1 ≤ N → P₀.IsMaximal → ∃ (r : ℕ) (V : Submodule k A) (D : Ideal A) (Q : Fin r → Ideal A) (f₀ : A), (FiniteDimensional k V ∧ (∀ v ∈ V, v ∈ D) ∧ (∀ i, (Q i).IsMaximal) ∧ Function.Injective Q ∧ (∀ i, Q i ≠ P₀) ∧ (∀ i, ¬ D ≤ Q i) ∧ ¬ D ≤ P₀ ∧ f₀ ∈ V ∧ f₀ ≠ 0 ∧ Ideal.span {f₀} = P₀ * D * ∏ i, Q i ^ N ∧ (∀ u : A, ∃ v ∈ V, u - v ∈ P₀ * ∏ i, Q i ^ (N - 1))) ∧ (∀ f ∈ V, f ≠ 0 → Module.finrank k (A ⧸ Ideal.span {f}) ≤ Module.finrank k (A ⧸ Ideal.span {f₀})) := by
  intro k A _ _ _ _ _ _ _ _ _ _ N P₀ hN hP
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set n := Module.finrank k[X] A
  let b : Module.Basis (Fin n) k[X] A := Module.finBasis k[X] A
  obtain ⟨c, lam, hdeg1, hdeg2⟩ := GlobalTheory.T.norm_degree_bound_polynomial_combination k A n b
  obtain ⟨p, hp2, hpP, hpP2⟩ := GlobalTheory.T.exists_degree_lt_two_correction_simple_zero k A n b P₀ (∑ i, (C (lam i) * X ^ 2) • b i) hP
  set f₁ : A := ∑ i, (C (lam i) * X ^ 2 + p i) • b i with hf₁def
  have hf₁eq : (∑ i, (C (lam i) * X ^ 2) • b i) + ∑ i, p i • b i = f₁ := by
    rw [hf₁def, ← Finset.sum_add_distrib]; simp [add_smul]
  rw [hf₁eq] at hpP hpP2
  obtain ⟨hf₁0, hf₁deg⟩ := hdeg2 2 p hp2
  obtain ⟨D, hD⟩ := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hpP)
  have hDP : ¬ D ≤ P₀ := by
    intro h
    apply hpP2
    have : Ideal.span {f₁} ≤ P₀ ^ 2 := by rw [hD, sq]; exact Ideal.mul_mono_right h
    exact (Ideal.span_singleton_le_iff_mem _).1 this
  have hf₁D : f₁ ∈ D := by
    have : Ideal.span {f₁} ≤ D := hD ▸ Ideal.mul_le_right
    exact (Ideal.span_singleton_le_iff_mem _).1 this
  set s := n * 2 + c with hs
  obtain ⟨q, r, Q, hqm, hqdeg, hQmax, hQinj, hf₁Q, hqQ⟩ := GlobalTheory.T.exists_squarefree_poly_distinct_zeros_on_curve k A f₁ s hf₁0
  set d := 2 + (M + 1) * s with hd
  have hspan : ∀ m : ℕ, Ideal.span {f₁ * algebraMap k[X] A (q ^ m)} = P₀ * D * ∏ i, Q i ^ m := by
    intro m
    rw [← Ideal.span_singleton_mul_span_singleton, hD, map_pow, ← Ideal.span_singleton_pow, hqQ,
      Finset.prod_pow]
  have hrepr₁ : ∀ i, b.repr f₁ i = C (lam i) * X ^ 2 + p i := by
    intro i; rw [hf₁def, b.repr_sum_self]
  have hdeg₁ : ∀ i, (b.repr f₁ i).natDegree ≤ 2 := by
    intro i
    rw [hrepr₁]
    exact (natDegree_add_le _ _).trans (max_le (natDegree_C_mul_X_pow_le _ _)
      (natDegree_le_iff_degree_le.2 (le_of_lt (hp2 i))))
  set f₀ : A := f₁ * algebraMap k[X] A (q ^ (M + 1)) with hf₀def
  have hf₀smul : f₀ = q ^ (M + 1) • f₁ := by rw [hf₀def, Algebra.smul_def, mul_comm]
  have hf₀0 : f₀ ≠ 0 := by
    rw [hf₀smul]; exact smul_ne_zero (pow_ne_zero _ hqm.ne_zero) hf₁0
  have hf₀V : f₀ ∈ boundedIn b D d := by
    refine ⟨D.mul_mem_right _ hf₁D, fun i => ?_⟩
    rw [hf₀smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
    refine (natDegree_mul_le).trans ?_
    rw [hqm.natDegree_pow, hqdeg]
    have := hdeg₁ i
    omega
  have hnorm₁ : Algebra.norm k[X] f₁ ≠ 0 := Algebra.norm_ne_zero_iff.2 hf₁0
  have hf₀deg : (Algebra.norm k[X] f₀).natDegree = n * d + c := by
    rw [hf₀def, map_mul, Algebra.norm_algebraMap_of_basis b, Fintype.card_fin,
      natDegree_mul hnorm₁ (pow_ne_zero _ (pow_ne_zero _ hqm.ne_zero)), hf₁deg,
      natDegree_pow, hqm.natDegree_pow, hqdeg, hd, hs]
    ring
  refine ⟨r, boundedIn b D d, D, Q, f₀, ⟨inferInstance, fun v hv => hv.1, hQmax, hQinj,
    fun i h => hf₁Q i (h ▸ hpP), fun i h => hf₁Q i (h hf₁D), hDP, hf₀V, hf₀0, hspan (M + 1),
    ?_⟩, ?_⟩
  · intro u
    have hcop : IsCoprime (P₀ * ∏ i, Q i ^ M) D :=
      (isCoprime_of_not_le hP hDP).mul_left
        (IsCoprime.prod_left fun i _ => (isCoprime_of_not_le (hQmax i) (fun h => hf₁Q i (h hf₁D))).pow_left)
    have h1 : (1 : A) ∈ (P₀ * ∏ i, Q i ^ M) ⊔ D := by
      rw [Ideal.isCoprime_iff_sup_eq.1 hcop]; trivial
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 h1
    have hqd : (Algebra.norm k[X] f₁).natDegree + (q ^ M).natDegree ≤ d + 1 := by
      rw [hqm.natDegree_pow, hqdeg, hf₁deg, hd, hs]; nlinarith
    obtain ⟨p', hp'd, hp'⟩ := GlobalTheory.T.exists_lowDegree_coords_mod_mul k A n b f₁ (q ^ M) d hf₁0 (pow_ne_zero _ hqm.ne_zero)
      hqd (u * y)
    rw [hspan M] at hp'
    have hP0 : P₀ * D * ∏ i, Q i ^ M ≤ D := Ideal.mul_le_left.trans Ideal.mul_le_right
    have hPI : P₀ * D * ∏ i, Q i ^ M ≤ P₀ * ∏ i, Q i ^ M := Ideal.mul_mono_left Ideal.mul_le_left
    refine ⟨∑ i, p' i • b i, ⟨?_, fun i => ?_⟩, ?_⟩
    · have : ∑ i, p' i • b i = u * y - (u * y - ∑ i, p' i • b i) := by ring
      rw [this]; exact D.sub_mem (D.mul_mem_left _ hy) (hP0 hp')
    · rw [b.repr_sum_self]; exact hp'd i
    · have : u - ∑ i, p' i • b i = u * x + (u * y - ∑ i, p' i • b i) := by
        linear_combination (-u) * hxy
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hx) (hPI hp')
  · intro f hf hf0
    rw [finrank_quotient_span_eq_natDegree_norm b hf0, finrank_quotient_span_eq_natDegree_norm b hf₀0,
      hf₀deg]
    have := hdeg1 d (fun i => b.repr f i) hf.2
    rwa [b.sum_repr] at this
end
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3

theorem homogeneous_lift_compatible : ∀ (l : ℕ) [Fact l.Prime] (w : ℕ) (p : (n : ℕ) → MvPolynomial (Fin 2) (ZMod (l ^ n))), (∀ n, (p n).IsHomogeneous w) → (∀ n, MvPolynomial.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n))) (p (n + 1)) = p n) → ∃ q : MvPolynomial (Fin 2) ℤ_[l], q.IsHomogeneous w ∧ (∀ n, MvPolynomial.map (PadicInt.toZModPow n) q = p n) ∧ ∀ q' : MvPolynomial (Fin 2) ℤ_[l], (∀ n, MvPolynomial.map (PadicInt.toZModPow n) q' = p n) → q' = q := by
  intro l _ w p hhom hcomp
  have hc1 : ∀ (m : Fin 2 →₀ ℕ) (n : ℕ),
      ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n)) ((p (n + 1)).coeff m) = (p n).coeff m := by
    intro m n
    rw [← hcomp n, MvPolynomial.coeff_map]
  have hc : ∀ (m : Fin 2 →₀ ℕ) (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂),
      ZMod.castHom (pow_dvd_pow l hk) (ZMod (l ^ k₁)) ((p k₂).coeff m) = (p k₁).coeff m := by
    intro m k₁ k₂ hk
    induction k₂, hk using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      rw [← ih, ← hc1 m k]
      show _ = ((ZMod.castHom (pow_dvd_pow l hk) (ZMod (l ^ k₁))).comp
        (ZMod.castHom (pow_dvd_pow l (Nat.le_succ k)) (ZMod (l ^ k)))) _
      rw [ZMod.castHom_comp]

  let f : ∀ k, MvPolynomial (Fin 2 →₀ ℕ) ℤ →+* ZMod (l ^ k) := fun k =>
    MvPolynomial.eval₂Hom (Int.castRingHom _) (fun m => (p k).coeff m)
  have hf : ∀ k₁ k₂ (hk : k₁ ≤ k₂),
      (ZMod.castHom (pow_dvd_pow l hk) (ZMod (l ^ k₁))).comp (f k₂) = f k₁ := by
    intro k₁ k₂ hk
    apply MvPolynomial.ringHom_ext
    · intro r; simp [f]
    · intro m
      simp only [f, RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      exact hc m k₁ k₂ hk
  let g := PadicInt.lift hf
  let c : (Fin 2 →₀ ℕ) → ℤ_[l] := fun m => g (MvPolynomial.X m)
  have hcn : ∀ m n, PadicInt.toZModPow n (c m) = (p n).coeff m := by
    intro m n
    have := congrArg (fun φ => φ (MvPolynomial.X m)) (PadicInt.lift_spec hf n)
    simpa [c, g, f] using this
  have hdeg : ∀ m, c m ≠ 0 → m.degree = w := by
    intro m hm
    by_contra hne
    apply hm
    refine (PadicInt.ext_of_toZModPow (p := l)).mp fun n => ?_
    rw [hcn, map_zero]
    by_contra h0
    apply hne
    rw [Finsupp.degree_eq_weight_one]
    exact hhom n h0
  have hfin : (Function.support c).Finite :=
    (Finsupp.finite_of_degree_le w).subset fun m hm => le_of_eq (hdeg m hm)
  let q : MvPolynomial (Fin 2) ℤ_[l] := ∑ m ∈ hfin.toFinset, MvPolynomial.monomial m (c m)
  have hq : ∀ m, q.coeff m = c m := by
    intro m
    simp only [q, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · simp only [Set.Finite.mem_toFinset, Function.mem_support, not_not] at h
      exact h.symm
  refine ⟨q, ?_, ?_, ?_⟩
  · intro m hm
    rw [hq] at hm
    have h := hdeg m hm
    rw [Finsupp.degree_eq_weight_one] at h
    exact h
  · intro n
    ext m
    rw [MvPolynomial.coeff_map, hq, hcn]
  · intro q' hq'
    apply MvPolynomial.ext
    intro m
    rw [hq]
    refine (PadicInt.ext_of_toZModPow (p := l)).mp fun n => ?_
    rw [hcn, ← hq' n, MvPolynomial.coeff_map]

end GlobalTheory.KZ.H3
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory

theorem mk_mem_sha1_iff_locally_coboundary {R : Type} [CommRing R] {Γ : Type} [Group Γ]
    [TopologicalSpace Γ] {I : Type} {D : I → Type} [∀ i, Group (D i)]
    [∀ i, TopologicalSpace (D i)] (φ : ∀ i, D i →* Γ) (hφ : ∀ i, Continuous (φ i)) {N : Type}
    [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [ContinuousConstSMul R N] (τ : Representation R Γ N) (z : Z1 τ) :
    (Submodule.Quotient.mk z : H1 τ) ∈ Sha1 τ φ hφ ↔
      ∀ i, ∃ b : N, ∀ g, z.1 (φ i g) = τ (φ i g) b - b := by
  simp only [Sha1, Submodule.mem_iInf, LinearMap.mem_ker]
  refine forall_congr' fun i => ?_
  have : resH1 τ (φ i) (hφ i) (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (restrictCocycles1 τ (φ i) (hφ i) z) := rfl
  rw [this, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, mem_coboundaries1]
  rfl

theorem sha1_exhausted_by_torsion_levels : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] (I : Type) [Finite I] (D : I → Type) [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)] (φ : ∀ i, D i →* Γ) (hφ : ∀ i, Continuous (φ i)) (A : Type) [AddCommGroup A] [Module ℤ_[l] A] [TopologicalSpace A] [DiscreteTopology A] (σ : Representation ℤ_[l] Γ A), (∀ a : A, ∃ r : ℕ, (l : ℤ_[l]) ^ r • a = 0) → ∃ P : ℕ → Submodule ℤ_[l] (Sha1 σ φ hφ), Monotone P ∧ (∀ y, ∃ r, y ∈ P r) ∧ ∀ (r : ℕ) (R : Type) [CommRing R] (N : Type) [AddCommGroup N] [Module R N] [TopologicalSpace N] [DiscreteTopology N] (τ : Representation R Γ N) (ι : N →+ A), Function.Injective ι → (∀ a : A, (l : ℤ_[l]) ^ r • a = 0 ↔ a ∈ Set.range ι) → (∀ g n, ι (τ g n) = σ g (ι n)) → (∀ a : A, (∀ i, ∃ b : A, (l : ℤ_[l]) ^ r • b = 0 ∧ ∀ g, σ (φ i g) a - a = σ (φ i g) b - b) → ∃ b : A, (l : ℤ_[l]) ^ r • b = 0 ∧ ∀ g, σ g a - a = σ g b - b) → Nat.card (P r) = Nat.card (Sha1 τ φ hφ) := by
  intro l _ Γ _ _ _ I _ D _ _ φ hφ A _ _ _ _ σ htor
  have hup : ∀ (r s : ℕ) (a : A), r ≤ s → (l : ℤ_[l]) ^ r • a = 0 → (l : ℤ_[l]) ^ s • a = 0 := by
    intro r s a hrs h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hrs
    rw [pow_add, mul_comm, mul_smul, h, smul_zero]
  let P : ℕ → Submodule ℤ_[l] (Sha1 σ φ hφ) := fun r =>
    { carrier := {x | ∃ z : Z1 σ, (Submodule.Quotient.mk z : H1 σ) = x.1 ∧
        (∀ g, (l : ℤ_[l]) ^ r • z.1 g = 0) ∧
        ∀ i, ∃ a : A, (l : ℤ_[l]) ^ r • a = 0 ∧ ∀ g, z.1 (φ i g) = σ (φ i g) a - a}
      zero_mem' := ⟨0, rfl, fun g => by simp, fun i => ⟨0, by simp, fun g => by simp⟩⟩
      add_mem' := by
        rintro x y ⟨z, hz, hz1, hz2⟩ ⟨w, hw, hw1, hw2⟩
        refine ⟨z + w, by rw [Submodule.Quotient.mk_add, hz, hw]; rfl, fun g => ?_, fun i => ?_⟩
        · change _ • (z.1 g + w.1 g) = 0
          rw [smul_add, hz1, hw1, add_zero]
        · obtain ⟨a, ha, ha'⟩ := hz2 i
          obtain ⟨b, hb, hb'⟩ := hw2 i
          refine ⟨a + b, by rw [smul_add, ha, hb, add_zero], fun g => ?_⟩
          change z.1 _ + w.1 _ = _
          rw [ha', hb', map_add (f := _)]; abel
      smul_mem' := by
        rintro c x ⟨z, hz, hz1, hz2⟩
        refine ⟨c • z, by rw [Submodule.Quotient.mk_smul, hz]; rfl, fun g => ?_, fun i => ?_⟩
        · change _ • (c • z.1 g) = 0
          rw [smul_comm, hz1, smul_zero]
        · obtain ⟨a, ha, ha'⟩ := hz2 i
          refine ⟨c • a, by rw [smul_comm, ha, smul_zero], fun g => ?_⟩
          change c • z.1 _ = _
          rw [ha', map_smul, smul_sub] }
  have hP : ∀ r x, x ∈ P r ↔ ∃ z : Z1 σ, (Submodule.Quotient.mk z : H1 σ) = x.1 ∧
        (∀ g, (l : ℤ_[l]) ^ r • z.1 g = 0) ∧
        ∀ i, ∃ a : A, (l : ℤ_[l]) ^ r • a = 0 ∧ ∀ g, z.1 (φ i g) = σ (φ i g) a - a :=
    fun r x => Iff.rfl
  refine ⟨P, ?_, ?_, ?_⟩
  · intro r s hrs x hx
    obtain ⟨z, hz, hz1, hz2⟩ := (hP r x).1 hx
    refine (hP s x).2 ⟨z, hz, fun g => hup r s _ hrs (hz1 g), fun i => ?_⟩
    obtain ⟨a, ha, ha'⟩ := hz2 i
    exact ⟨a, hup r s _ hrs ha, ha'⟩
  · rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    choose b hb using (mk_mem_sha1_iff_locally_coboundary φ hφ σ z).1 hy
    choose e he using htor
    have hfin : (Set.range z.1 ∪ Set.range b).Finite :=
      (isCompact_range z.2.1).finite_of_discrete.union (Set.finite_range b)
    obtain ⟨r, hr⟩ := (hfin.image e).bddAbove
    refine ⟨r, (hP r _).2 ⟨z, rfl, fun g => hup _ _ _ (hr ⟨_, Or.inl ⟨g, rfl⟩, rfl⟩) (he _),
      fun i => ⟨b i, hup _ _ _ (hr ⟨_, Or.inr ⟨i, rfl⟩, rfl⟩) (he _), hb i⟩⟩⟩
  · intro r R _ N _ _ _ _ τ ι hinj hrange heq hloc
    let ιZ : Z1 τ →+ Z1 σ :=
      { toFun := fun z => ⟨fun g => ι (z.1 g), continuous_of_discreteTopology.comp z.2.1,
          fun g h => by beta_reduce; rw [z.2.2, map_add (f := _), heq]⟩
        map_zero' := Subtype.ext (funext fun g => map_zero ι)
        map_add' := fun z w => Subtype.ext (funext fun g => map_add ι _ _) }
    have hιZ : ∀ z g, (ιZ z).1 g = ι (z.1 g) := fun _ _ => rfl
    let F : H1 τ →+ H1 σ := QuotientAddGroup.map
      ((B1 τ).comap (Z1 τ).subtype).toAddSubgroup ((B1 σ).comap (Z1 σ).subtype).toAddSubgroup ιZ
      (by
        intro z hz
        obtain ⟨m, hm⟩ := (mem_coboundaries1 τ _).1 hz
        refine (mem_coboundaries1 σ _).2 ⟨ι m, fun g => ?_⟩
        change ι (z.1 g) = _
        rw [← heq, ← map_sub]
        exact congrArg ι (hm g))
    have hF : ∀ z, F (Submodule.Quotient.mk z) = Submodule.Quotient.mk (ιZ z) := fun _ => rfl
    have hkill : ∀ n, (l : ℤ_[l]) ^ r • ι n = 0 := fun n => (hrange _).2 ⟨n, rfl⟩
    have hmem : ∀ x : H1 τ, x ∈ Sha1 τ φ hφ → ∃ h : F x ∈ Sha1 σ φ hφ, ⟨F x, h⟩ ∈ P r := by
      intro x hx
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      have h1 := (mk_mem_sha1_iff_locally_coboundary φ hφ τ z).1 hx
      have h2 : ∀ i, ∃ a : A, (l : ℤ_[l]) ^ r • a = 0 ∧
          ∀ g, (ιZ z).1 (φ i g) = σ (φ i g) a - a := by
        intro i
        obtain ⟨b, hb⟩ := h1 i
        exact ⟨ι b, hkill b, fun g => by rw [hιZ, hb, map_sub, heq]⟩
      refine ⟨?_, (hP r _).2 ⟨ιZ z, rfl, fun g => hkill _, h2⟩⟩
      rw [hF, mk_mem_sha1_iff_locally_coboundary]
      intro i
      obtain ⟨a, -, ha⟩ := h2 i
      exact ⟨a, ha⟩
    have hker : ∀ x : H1 τ, x ∈ Sha1 τ φ hφ → F x = 0 → x = 0 := by
      intro x hx h0
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      have h1 := (mk_mem_sha1_iff_locally_coboundary φ hφ τ z).1 hx
      rw [hF, Submodule.Quotient.mk_eq_zero] at h0
      obtain ⟨a, ha⟩ := (mem_coboundaries1 σ _).1 h0
      have ha' : ∀ g, ι (z.1 g) = σ g a - a := ha
      obtain ⟨b, hb, hb'⟩ := hloc a (fun i => by
        obtain ⟨b, hb⟩ := h1 i
        exact ⟨ι b, hkill b, fun g => by rw [← ha', hb, map_sub, heq]⟩)
      obtain ⟨n, rfl⟩ := (hrange b).1 hb
      rw [Submodule.Quotient.mk_eq_zero]
      refine (mem_coboundaries1 τ _).2 ⟨n, fun g => hinj ?_⟩
      change ι (z.1 g) = _
      rw [ha', hb', map_sub, heq]
    let f : Sha1 τ φ hφ → P r := fun x => ⟨⟨F x.1, (hmem x.1 x.2).1⟩, (hmem x.1 x.2).2⟩
    refine (Nat.card_eq_of_bijective f ⟨?_, ?_⟩).symm
    · intro x y hxy
      have h : F x.1 = F y.1 := congrArg (fun t : P r => t.1.1) hxy
      apply Subtype.ext
      rw [← sub_eq_zero]
      exact hker _ (sub_mem x.2 y.2) (by rw [map_sub, h, sub_self])
    · rintro ⟨x, hx⟩
      obtain ⟨z, hz, hz1, hz2⟩ := (hP r x).1 hx
      have hlift : ∀ g, ∃ n, ι n = z.1 g := fun g => (hrange _).1 (hz1 g)
      choose w hw using hlift
      have hwc : Continuous w := by
        have : w = Function.invFun ι ∘ z.1 := by
          funext g
          rw [Function.comp_apply, ← hw, Function.leftInverse_invFun hinj]
        rw [this]
        exact continuous_of_discreteTopology.comp z.2.1
      let z' : Z1 τ := ⟨w, hwc, fun g h => hinj (by rw [map_add (f := _), heq, hw, hw, hw, z.2.2])⟩
      have hz' : ιZ z' = z := Subtype.ext (funext hw)
      refine ⟨⟨Submodule.Quotient.mk z', ?_⟩, ?_⟩
      · rw [mk_mem_sha1_iff_locally_coboundary]
        intro i
        obtain ⟨a, ha, ha'⟩ := hz2 i
        obtain ⟨n, rfl⟩ := (hrange a).1 ha
        refine ⟨n, fun g => hinj ?_⟩
        change ι (w _) = _
        rw [hw, ha', map_sub, heq]
      · apply Subtype.ext
        apply Subtype.ext
        change F (Submodule.Quotient.mk z') = x.1
        rw [hF, hz', hz]

end GlobalTheory
end

end

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

theorem _root_.GlobalTheory.T.sha1_torsion_level_filtration : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] (I : Type) [Finite I] (D : I → Type) [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)] (φ : ∀ i, D i →* Γ) (hφ : ∀ i, Continuous (φ i)) (A : Type) [AddCommGroup A] [Module ℤ_[l] A] [TopologicalSpace A] [DiscreteTopology A] (σ : Representation ℤ_[l] Γ A), (∀ a : A, ∃ r : ℕ, (l : ℤ_[l]) ^ r • a = 0) → ∃ P : ℕ → Submodule ℤ_[l] (Sha1 σ φ hφ), Monotone P ∧ (∀ y, ∃ r, y ∈ P r) ∧ ∀ (r : ℕ) (R : Type) [CommRing R] (N : Type) [AddCommGroup N] [Module R N] [TopologicalSpace N] [DiscreteTopology N] (τ : Representation R Γ N) (ι : N →+ A), Function.Injective ι → (∀ a : A, (l : ℤ_[l]) ^ r • a = 0 ↔ a ∈ Set.range ι) → (∀ g n, ι (τ g n) = σ g (ι n)) → (∀ a : A, (∀ i, ∃ b : A, (l : ℤ_[l]) ^ r • b = 0 ∧ ∀ g, σ (φ i g) a - a = σ (φ i g) b - b) → ∃ b : A, (l : ℤ_[l]) ^ r • b = 0 ∧ ∀ g, σ g a - a = σ g b - b) → Nat.card (P r) = Nat.card (Sha1 τ φ hφ) := by
  first | exact @GlobalTheory.sha1_exhausted_by_torsion_levels | exact GlobalTheory.sha1_exhausted_by_torsion_levels | (intros; apply GlobalTheory.sha1_exhausted_by_torsion_levels <;> assumption)

end
end
