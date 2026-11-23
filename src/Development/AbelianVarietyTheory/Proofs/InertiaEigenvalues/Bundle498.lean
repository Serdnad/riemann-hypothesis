module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle289
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle384
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle450
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Formalism.LocalToGlobal.Divisibility.RowSideTie
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle385
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle194
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle489
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle341
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle269
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterDecompositionAndClassFunctionExpansion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle462
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle369
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle004

@[expose] public section

section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.MirabolicComparison

theorem tr_add {G : Type} [Group G] [Fintype G] (a : MonoidAlgebra ℂ G) (f h : G → ℂ) :
    tr a (fun x => f x + h x) = tr a f + tr a h := by
  simp [tr, mul_add, Finset.sum_add_distrib]

theorem tr_mul_const {G : Type} [Group G] [Fintype G] (a : MonoidAlgebra ℂ G) (f : G → ℂ) (c : ℂ) :
    tr a (fun x => f x * c) = tr a f * c := by
  simp only [tr, Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem tr_tr_list_nat {G H : Type} [Group G] [Fintype G] [Group H] [Fintype H]
    (a : MonoidAlgebra ℂ G) (b : MonoidAlgebra ℂ H) (ha : a * a = a) (hb : b * b = b) :
    ∀ L : List ((G → ℂ) × (H → ℂ)), (∀ p ∈ L, IsChar p.1 ∧ IsChar p.2) →
      ∃ n : ℕ, tr a (fun x => tr b (fun y => (L.map fun p => p.1 x * p.2 y).sum)) = n := by
  intro L
  induction L with
  | nil =>
    intro _
    exact ⟨0, by simp [tr]⟩
  | cons p L ih =>
    intro hL
    obtain ⟨m, hm⟩ := ih (fun q hq => hL q (List.mem_cons_of_mem _ hq))
    obtain ⟨n₁, hn₁⟩ := (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree G a p.1).1 ha (hL p (List.mem_cons_self ..)).1
    obtain ⟨n₂, hn₂⟩ := (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree H b p.2).1 hb (hL p (List.mem_cons_self ..)).2
    refine ⟨n₁ * n₂ + m, ?_⟩
    simp only [List.map_cons, List.sum_cons]
    rw [show (fun x => tr b (fun y => p.1 x * p.2 y + (L.map fun p => p.1 x * p.2 y).sum)) =
        (fun x => p.1 x * tr b p.2 + tr b (fun y => (L.map fun p => p.1 x * p.2 y).sum)) from by
      funext x
      rw [tr_add]
      congr 1
      simp only [tr, Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring]
    rw [tr_add, tr_mul_const, hm, hn₁, hn₂]
    push_cast
    ring

end GlobalTheory.GLq.MirabolicComparison

namespace GlobalTheory.GLq.MirabolicComparison

theorem isClass_of_isChar {G : Type} [Group G] {χ : G → ℂ} (h : IsChar χ) : IsClass χ := by
  obtain ⟨V, hV⟩ := h
  intro x y
  rw [← hV, ← hV]
  exact FDRep.char_conj V x y

theorem isChar_of_isIrr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsChar χ := by
  obtain ⟨V, _, hV⟩ := h
  exact ⟨V, hV⟩

theorem wh_der_nat (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (N i : ℕ) (hi : i ≤ N)
    (χ : Gn g N → ℂ) (hχ : IsChar χ) : ∃ n : ℕ, wh ψ (der ψ i χ) = n := by
  obtain ⟨L, hL, hLeq⟩ := (GlobalTheory.T.harishChandra_induction_character_restriction_decomp g i (N - i) N (by omega)).2 χ hχ
  have hres : (fun h : Gn g i => wh ψ (res i (N - i) χ h)) =
      fun h => tr (eU g (N - i) ψ) (fun y => (L.map fun p => p.1 h * p.2 y).sum) := by
    funext h
    simp only [wh]
    congr 1
    funext y
    exact hLeq h y
  show ∃ n : ℕ, tr (eU g i ψ) (fun h => wh ψ (res i (N - i) χ h)) = n
  rw [hres]
  exact tr_tr_list_nat _ _ (GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField g i 0 0 ψ).1 (GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField g (N - i) 0 0 ψ).1 L
    (fun p hp => ⟨isChar_of_isIrr (hL p hp).1, isChar_of_isIrr (hL p hp).2⟩)

theorem wh_der_zero (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (N : ℕ) (χ : Gn g N → ℂ) :
    wh ψ (der ψ 0 χ) = wh ψ χ := by
  haveI : Subsingleton (Gn g 0) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
  have h1 : (eU g 0 ψ).coeff 1 = 1 := by
    rw [(GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField g 0 0 0 ψ).2.1]; simp
  have hres : res 0 (N - 0) χ 1 = χ := by
    funext y
    change Gn g N at y
    simp only [res, Nat.zero_mul, pow_zero, inv_one, one_mul]
    rw [Finset.sum_eq_single y]
    · have : InPar 0 ((y : Gn g N) : Mt g N) ∧ tl 0 ((y : Gn g N) : Mt g N) = ((1 : Gn g 0) : Mt g 0) ∧
          br 0 (N - 0) ((y : Gn g N) : Mt g N) = ((y : Gn g (N - 0)) : Mt g (N - 0)) := by
        refine ⟨fun i j hj _ => absurd hj (Nat.not_lt_zero _), Subsingleton.elim _ _, ?_⟩
        funext i j
        simp [br, entN]
      rw [if_pos this]
    · intro x _ hx
      rw [if_neg]
      rintro ⟨_, _, hb⟩
      apply hx
      apply Units.ext
      rw [← hb]
      funext i j
      simp [br, entN]
    · intro h; exact absurd (Finset.mem_univ _) h
  show tr (eU g 0 ψ) (fun h => wh ψ (res 0 (N - 0) χ h)) = wh ψ χ
  simp only [tr]
  rw [Fintype.sum_subsingleton _ 1, h1, one_mul, hres]

end GlobalTheory.GLq.MirabolicComparison

namespace GlobalTheory.GLq.MirabolicComparison

theorem mirabolic_comparison : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (N k s : ℕ),
    N = k + 2 * s + 1 → 1 ≤ k → ∀ χ : Gn g N → ℂ, IsChar χ →
      ((g : ℝ) ^ k - (g : ℝ) ^ (k - 1)) * (wh ψ χ).re ≤ (tr (eJ g N k s ψ) χ).re := by
  intro g _ ψ hψ N k s hN hk χ hχ
  have hcl := isClass_of_isChar hχ
  rw [GlobalTheory.T.groupAlgebraTrace_patternIdempotent_exchange g ψ hψ N k s hN χ hcl, GlobalTheory.T.trace_unitriangularColumnVanishingIdempotent_eq_sum_derivatives g ψ hψ N k hk (by omega) χ hcl]
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast (Fact.out : g.Prime).one_lt.le
  have hterm : ∀ i a b, (wh ψ (der ψ i χ) * ((g : ℂ) ^ a - (g : ℂ) ^ b)).re =
      (wh ψ (der ψ i χ)).re * ((g : ℝ) ^ a - (g : ℝ) ^ b) := by
    intro i a b
    rw [show ((g : ℂ) ^ a - (g : ℂ) ^ b) = (((g : ℝ) ^ a - (g : ℝ) ^ b : ℝ) : ℂ) by push_cast; ring]
    exact Complex.re_mul_ofReal _ _
  have hnn : ∀ i, i ≤ N → 0 ≤ (wh ψ (der ψ i χ)).re := by
    intro i hi
    obtain ⟨n, hn⟩ := wh_der_nat g ψ N i hi χ hχ
    rw [hn]
    simp
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Finset.sum_range_succ', Complex.add_re, Complex.add_re, Complex.re_sum, hterm 0, wh_der_zero]
  have hrest : 0 ≤ ∑ i ∈ Finset.range k', (wh ψ (der ψ (i + 1) χ) *
      ((g : ℂ) ^ (k' + 1 - (i + 1)) - (g : ℂ) ^ (k' + 1 - (i + 1) - 1))).re := by
    apply Finset.sum_nonneg
    intro i hi
    rw [Finset.mem_range] at hi
    rw [hterm]
    apply mul_nonneg (hnn _ (by omega))
    rw [sub_nonneg]
    exact pow_le_pow_right₀ hg1 (by omega)
  have hlast := hnn (k' + 1) (by omega)
  have h0 : (wh ψ χ).re * ((g : ℝ) ^ (k' + 1 - 0) - (g : ℝ) ^ (k' + 1 - 0 - 1)) =
      ((g : ℝ) ^ (k' + 1) - (g : ℝ) ^ (k' + 1 - 1)) * (wh ψ χ).re := by
    simp only [Nat.sub_zero]
    ring
  linarith

end GlobalTheory.GLq.MirabolicComparison
end

section

noncomputable section

open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.GenericConstituent

variable {g : ℕ} [Fact g.Prime]

theorem wh_const_mul' (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (c : ℂ) (f : Gn g n → ℂ) :
    wh ψ (fun x => c * f x) = c * wh ψ f := by
  unfold wh tr
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

theorem wh_mul_const' (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (c : ℂ) (f : Gn g n → ℂ) :
    wh ψ (fun x => f x * c) = wh ψ f * c := by
  unfold wh tr
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

theorem wh_list_sum (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (L : List (Gn g n → ℂ)) :
    wh ψ L.sum = (L.map (wh ψ)).sum := by
  induction L with
  | nil => simp [wh, tr]
  | cons a L ih =>
    rw [List.sum_cons, List.map_cons, List.sum_cons, ← ih]
    unfold wh tr
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem ip_list_sum_right {G : Type} [Group G] [Fintype G] (ρ : G → ℂ) (L : List (G → ℂ)) :
    ip ρ L.sum = (L.map (ip ρ)).sum := by
  induction L with
  | nil => simp [ip]
  | cons a L ih =>
    rw [List.sum_cons, List.map_cons, List.sum_cons, ← ih]
    unfold ip
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem ip_sum_count {G : Type} [Group G] [Fintype G] (ρ : G → ℂ) (hρ : IsIrr ρ) (L : List (G → ℂ))
    (hL : ∀ σ ∈ L, IsIrr σ) : (L.map (ip ρ)).sum = (L.count ρ : ℂ) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.sum_cons, ih (fun σ hσ => hL σ (List.mem_cons_of_mem a hσ)), List.count_cons,
      (GlobalTheory.GLq.ZOrth.zorth G ρ a hρ (hL a List.mem_cons_self)).2.2]
    by_cases h : ρ = a
    · subst h; simp; ring
    · simp [h, Ne.symm h]

theorem isChar_of_isIrr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsChar χ := by
  obtain ⟨V, -, hV⟩ := h
  exact ⟨V, hV⟩

theorem isClass_of_isChar {n : ℕ} {χ : Gn g n → ℂ} (h : IsChar χ) : IsClass χ :=
  (GlobalTheory.charDec (Gn g n) χ).2.2.1 h

theorem wh_hcL_prod (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) :
    ∀ L : List (Pc g), (∀ p ∈ L, IsCusp p.2) → wh ψ (hcL L (degL L)) = (L.map fun p => wh ψ p.2).prod := by
  intro L
  induction L with
  | nil =>
    intro _
    exact GlobalTheory.GLq.Leibniz.wh_gl_zero ψ
  | cons p L ih =>
    intro hL
    have hp := hL p List.mem_cons_self
    have hL' : ∀ q ∈ L, IsCusp q.2 := fun q hq => hL q (List.mem_cons_of_mem p hq)
    have hβ : IsClass (hcL L (degL L)) :=
      isClass_of_isChar (GlobalTheory.gl_list_product_perm_char g L L (degL L) rfl
        (fun q hq => isChar_of_isIrr (hL' q hq).2.1)).1
    have hα : IsClass p.2 := isClass_of_isChar (isChar_of_isIrr hp.2.1)
    have hdeg : degL (p :: L) = p.1 + degL L := by simp [degL]
    rw [hcL_cons]
    unfold hc
    rw [GlobalTheory.GLq.WhMul.wh_hcT g ψ hψ p.1 (degL L) (degL (p :: L)) hdeg]
    · simp_rw [wh_const_mul']
      rw [wh_mul_const', ih hL', List.map_cons, List.prod_cons]
    · intro y x z
      simp only
      rw [hα]
    · intro x y z
      simp only
      rw [hβ]

theorem exists_generic_constituent : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 →
    ∀ (L : List (Pc g)) (n : ℕ), degL L = n → (∀ p ∈ L, IsCusp p.2) →
      ∃ ρ : Gn g n → ℂ, IsIrr ρ ∧ wh ψ ρ ≠ 0 ∧ ip ρ (hcL L n) ≠ 0 := by
  intro g _ ψ hψ L n hn hL
  subst hn
  have hwh : wh ψ (hcL L (degL L)) ≠ 0 := by
    rw [wh_hcL_prod ψ hψ L hL]
    refine List.prod_ne_zero fun h0 => ?_
    obtain ⟨p, hp, h1⟩ := List.mem_map.1 h0
    obtain ⟨m, hm, hm'⟩ := GlobalTheory.T.whittakerDimension_pos_of_cuspidal_character g ψ hψ p.1 p.2 (hL p hp)
    rw [hm'] at h1
    have : m = 0 := by exact_mod_cast h1
    omega
  have hch : IsChar (hcL L (degL L)) :=
    (GlobalTheory.gl_list_product_perm_char g L L (degL L) rfl (fun q hq => isChar_of_isIrr (hL q hq).2.1)).1
  obtain ⟨Lρ, hirr, hsum⟩ := (GlobalTheory.charDec _ (hcL L (degL L))).1 hch
  have hex : ∃ ρ ∈ Lρ, wh ψ ρ ≠ 0 := by
    by_contra hno
    push_neg at hno
    apply hwh
    rw [hsum, wh_list_sum]
    exact List.sum_eq_zero fun x hx => by
      obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.1 hx
      exact hno ρ hρ
  obtain ⟨ρ, hρ, hwρ⟩ := hex
  refine ⟨ρ, hirr ρ hρ, hwρ, ?_⟩
  rw [hsum, ip_list_sum_right, ip_sum_count ρ (hirr ρ hρ) Lρ hirr]
  exact Nat.cast_ne_zero.2 (List.count_pos_iff.2 hρ).ne'

end GlobalTheory.GLq.GenericConstituent
end
end

section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

noncomputable section

namespace GlobalTheory.EtaJoin.Side

theorem length_quot_map {R M M' : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (f : M →ₗ[R] M') (hf : Function.Injective f) (P Q : Submodule R M) :
    Module.length R (P.map f ⧸ (Q.map f).comap (P.map f).subtype) = Module.length R (P ⧸ Q.comap P.subtype) := by
  refine (LinearEquiv.length_eq (Submodule.Quotient.equiv (Q.comap P.subtype) ((Q.map f).comap (P.map f).subtype)
    (Submodule.equivMapOfInjective f hf P) ?_)).symm
  ext ⟨y, hy⟩
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨⟨x, hx⟩, hxQ, hxy⟩
    refine ⟨x, hxQ, ?_⟩
    have := congrArg Subtype.val hxy
    simpa using this
  · rintro ⟨x, hxQ, hxy⟩
    obtain ⟨x', hx', rfl⟩ := hy
    have : x = x' := hf hxy
    subst this
    exact ⟨⟨x, hx'⟩, hxQ, rfl⟩


open scoped _root_.Formalism.L2.Col in
theorem lenUW_map {K : Type} [Field K] [NumberField K] {V V' : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
    (φ : V →ₗ[K] V') (hφ : Function.Injective φ) (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) :
    _root_.Formalism.L2.Col.lenUW w (A.map (φ.restrictScalars (𝓞 K))) (B.map (φ.restrictScalars (𝓞 K))) = _root_.Formalism.L2.Col.lenUW w A B := by
  unfold _root_.Formalism.L2.Col.lenUW _root_.Formalism.L2.Col.lenW
  rw [_root_.Formalism.L2.Col.atW_map, _root_.Formalism.L2.Col.atW_map,
    length_quot_map (φ.restrictScalars (_root_.Formalism.L2.Col.Ow w)) hφ]

theorem lat_eq_map (D : D7) (μ : D.what₂.Tup) (j : ℕ) {n : ℕ} (e : (Fin n → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL μ j)
    (N : Submodule (𝓞 D.what₂.LL) (Fin n → D.what₂.LL))
    (hL : OLatTie D.what₂.embLL (D.what₂.MtLat μ j) ((D.what₂.jMt μ j).comp e.toLinearMap) N) :
    lat D μ j = N.map (e.toLinearMap.restrictScalars (𝓞 D.what₂.LL)) := by
  classical
  apply le_antisymm
  · rw [lat, Submodule.span_le]
    intro y hy
    obtain ⟨x, rfl⟩ := e.surjective y
    refine ⟨x, ?_, rfl⟩
    show x ∈ N
    rw [hL.2 x]
    refine ⟨fun v => if v = D.what₂.jMt μ j (e x) then 1 else 0, ?_⟩
    rw [Finset.sum_eq_single (D.what₂.jMt μ j (e x))]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd hy h
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, hc⟩ := (hL.2 x).1 hx
    choose! g hg using D.what₂.MtLat_sub μ j
    have hx' : e x = ∑ v ∈ (D.what₂.MtLat μ j).gen, (c v) • g v := by
      apply GlobalTheory.Mem.LiftForms.jMt_injective μ j

      rw [map_sum]
      have hc' : D.what₂.jMt μ j (e x) = ∑ v ∈ (D.what₂.MtLat μ j).gen, D.what₂.embLL (c v : D.what₂.LL) • v := hc
      rw [hc']
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [← algebraMap_smul D.what₂.LL (c v) (g v), map_smulₛₗ, hg v hv]
    show e x ∈ lat D μ j
    rw [hx']
    refine Submodule.sum_mem _ fun v hv => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    show D.what₂.jMt μ j (g v) ∈ (D.what₂.MtLat μ j).gen
    rw [hg v hv]
    exact hv

theorem zRat_and_etaRat_eq : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin m) (t : T), (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (s : ℕ), A.fam.Ok s → ∀ (i : Fin m) (t : T), FormsTie D.what₂.embLL ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lH D A P ψ i t) (lE D A P ψ i t) (D.what₂.eMt (tup t) ((i : ℕ) + 1)) → OLatTie D.what₂.embLL (D.what₂.MtLat (tup t) ((i : ℕ) + 1)) ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lNab D A P ψ i t) → Idx.Z0 D (tup t) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => (D.what₂.jMt (tup t) ((i : ℕ) + 1)) (eMt i t ((lZ0 D A P ψ Zs i t).mulVec (Pi.single k 1)))) → ZRat D (tup t) ((i : ℕ) + 1) ∧ ∀ w, etaRat D (tup t) ((i : ℕ) + 1) w = A.fam.etaJ P ψ Zs i t (D.plEq w) := by
  intro D G _ _ Pl0 T m A P ψ Zs tup eMt s hOk i t hF hL hZ
  obtain ⟨hinj, hrange, hproj⟩ := GlobalTheory.T.concreteProjector_eq_orthogonalProjection D G Pl0 T m A P ψ Zs tup eMt s hOk i t hF hZ
  have hB : BlockHyp (A.fam.L i t) (A.fam.lvlA P ψ) A.v0 s := ⟨hOk.conj, hOk.irr, hOk.lifts i t⟩
  have hcut := BlockDat.lf_cut_nab (Z := Zs.Zl i t) hB
  have hlat := lat_eq_map D (tup t) ((i : ℕ) + 1) (eMt i t) _ hL
  set e := eMt i t with he
  set ψL := (e.toLinearMap ∘ₗ (lZ0 D A P ψ Zs i t).mulVecLin) with hψL
  set R := ratSub D (tup t) ((i : ℕ) + 1) (Idx.Z0 D (tup t) ((i : ℕ) + 1)) with hR
  set Rp := ratSub D (tup t) ((i : ℕ) + 1) (Idx.Z0 D (tup t) ((i : ℕ) + 1))ᗮ with hRp
  have hbot : ∀ y, y ∈ R → y ∈ Rp → y = 0 := by
    intro y h1 h2
    apply GlobalTheory.Mem.LiftForms.jMt_injective (tup t) ((i : ℕ) + 1)
    rw [map_zero]
    have h3 : D.what₂.jMt (tup t) ((i : ℕ) + 1) y ∈ Idx.Z0 D (tup t) ((i : ℕ) + 1) ⊓ (Idx.Z0 D (tup t) ((i : ℕ) + 1))ᗮ :=
      ⟨h1, h2⟩
    rw [Submodule.inf_orthogonal_eq_bot] at h3
    exact h3
  have hmemR : ∀ z, ψL z ∈ R := fun z => by rw [hrange]; exact LinearMap.mem_range_self _ z
  have hup : up D (tup t) ((i : ℕ) + 1) =
      ((A.fam.L i t).Tl (A.fam.lvlA P ψ) (Zs.Zl i t)).map (ψL.restrictScalars (𝓞 D.what₂.LL)) := by
    ext y
    constructor
    · rintro ⟨hyR, hy⟩
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hy
      rw [hlat] at ha
      obtain ⟨x, hx, rfl⟩ := ha
      have hd : y - ψL ((lPrj D A P ψ Zs i t).mulVec x) = 0 := by
        apply hbot
        · exact R.sub_mem hyR (hmemR _)
        · have : y - ψL ((lPrj D A P ψ Zs i t).mulVec x) = (e x - ψL ((lPrj D A P ψ Zs i t).mulVec x)) + b := by
            rw [← hab]
            simp only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
            abel
          rw [this]
          exact Rp.add_mem (hproj x) hb
      refine ⟨(lPrj D A P ψ Zs i t).mulVec x, ⟨x, hx, rfl⟩, ?_⟩
      show ψL _ = y
      exact (sub_eq_zero.1 hd).symm
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨hmemR _, Submodule.mem_sup.2 ⟨e x, ?_, ψL ((lPrj D A P ψ Zs i t).mulVec x) - e x, ?_, ?_⟩⟩
      · rw [hlat]
        exact ⟨x, hx, rfl⟩
      · show _ ∈ Rp
        rw [← neg_sub]
        exact Rp.neg_mem (hproj x)
      · show e x + (ψL ((lPrj D A P ψ Zs i t).mulVec x) - e x) = ψL ((lPrj D A P ψ Zs i t).mulVec x)
        abel
  have hlow : low D (tup t) ((i : ℕ) + 1) =
      ((A.fam.L i t).cutZ (A.fam.lvlA P ψ) (Zs.Zl i t)).map (ψL.restrictScalars (𝓞 D.what₂.LL)) := by
    ext y
    constructor
    · rintro ⟨hy, hyR⟩
      have hyR' : y ∈ R := hyR
      rw [hrange] at hyR'
      obtain ⟨z, rfl⟩ := hyR'
      rw [hlat] at hy
      obtain ⟨x, hx, hxz⟩ := hy
      have hxz' : x = (lZ0 D A P ψ Zs i t).mulVec z := e.injective hxz
      refine ⟨z, ?_, rfl⟩
      rw [← hcut]
      show (lZ0 D A P ψ Zs i t).mulVec z ∈ lNab D A P ψ i t
      rw [← hxz']
      exact hx
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, hmemR z⟩
      rw [hlat]
      rw [← hcut] at hz
      exact ⟨(lZ0 D A P ψ Zs i t).mulVec z, hz, rfl⟩
  refine ⟨?_, fun w => ?_⟩
  · rw [ZRat, eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := e.surjective y
    refine Submodule.mem_sup.2 ⟨ψL ((lPrj D A P ψ Zs i t).mulVec x), hmemR _, e x - ψL ((lPrj D A P ψ Zs i t).mulVec x),
      hproj x, ?_⟩
    abel
  · rw [etaRat, hup, hlow, lenUW_map ψL hinj]
    rfl

end GlobalTheory.EtaJoin.Side
end
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.determinant_rec_compatible : StandardCosocleGL → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ) (rc : IrrGL (k := w.adicCompletion E) → WD h), LawsLit a ha e rc → ∀ (t : ℕ) χ hχ, rc (cls (IrrRep.det (Fin t) χ hχ)) = sumList ((List.range t).map fun j : ℕ => (rc (.ofChar χ hχ)).lpTw (((t : ℝ) - 1) / 2 - j)) := by
  first | exact @GlobalTheory.lawsLit_det | exact GlobalTheory.lawsLit_det | (intros; apply GlobalTheory.lawsLit_det <;> assumption)
end
