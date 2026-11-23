module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle072
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle087
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.SetTheory.Cardinal.Finite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle100
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap

@[expose] public section

section

open NumberField UniqueFactorizationMonoid GlobalTheory.StdLoc

noncomputable section

namespace GlobalTheory.CardGLQuot

theorem card_GL_field_real (κ : Type) [Field κ] [Finite κ] (n : ℕ) :
    (Nat.card (GL (Fin n) κ) : ℝ) = (Nat.card κ : ℝ) ^ (n ^ 2) * glVol (Nat.card κ) n := by
  haveI := Fintype.ofFinite κ
  have hq1 : 1 ≤ Nat.card κ := Nat.one_le_iff_ne_zero.mpr (Nat.card_pos).ne'
  have hq0 : (Nat.card κ : ℝ) ≠ 0 := by positivity
  have hIcc : Finset.Icc 1 n = Finset.Ioc 0 n := by
    ext i; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [glVol, hIcc]
  rw [Matrix.card_GL_field, Nat.cast_prod, ← Nat.card_eq_fintype_card]
  rw [Fin.prod_univ_eq_prod_range (fun i => ((Nat.card κ ^ n - Nat.card κ ^ i : ℕ) : ℝ)) n]
  rw [← Finset.prod_range_reflect]
  have hIoc : Finset.Ioc 0 n = (Finset.range n).map ⟨(· + 1), add_left_injective 1⟩ := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨x - 1, by omega, by omega⟩
    · rintro ⟨y, hy, rfl⟩; omega
  rw [hIoc, Finset.prod_map, sq, pow_mul,
    show ((Nat.card κ : ℝ) ^ n) ^ n = ∏ _j ∈ Finset.range n, (Nat.card κ : ℝ) ^ n by simp,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun j hj => ?_)
  have hj' : j < n := Finset.mem_range.mp hj
  have hle : Nat.card κ ^ (n - 1 - j) ≤ Nat.card κ ^ n := Nat.pow_le_pow_right hq1 (by omega)
  simp only [Function.Embedding.coeFn_mk]
  rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_pow, mul_sub, mul_one]
  congr 1
  have hsplit : (Nat.card κ : ℝ) ^ n = (Nat.card κ : ℝ) ^ (n - 1 - j) * (Nat.card κ : ℝ) ^ (j + 1) := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq0), mul_one]


open Classical in
theorem card_GL_eq_card_isUnit (S : Type) [CommRing S] [Fintype S] (n : ℕ) :
    Nat.card (GL (Fin n) S) =
      (Finset.univ.filter (fun A : Matrix (Fin n) (Fin n) S => IsUnit A)).card := by
  classical
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (Equiv.ofBijective (fun u => ⟨(u : Matrix (Fin n) (Fin n) S), u.isUnit⟩) ⟨?_, ?_⟩)
  · intro u v h; exact Units.ext (congrArg Subtype.val h)
  · rintro ⟨A, hA⟩; exact ⟨hA.unit, rfl⟩

theorem card_GL_of_residue {R k : Type} [CommRing R] [Finite R] [Field k] (π : R →+* k)
    (hπ : Function.Surjective π) (hu : ∀ x, IsUnit x ↔ π x ≠ 0) (n : ℕ) :
    (Nat.card (GL (Fin n) R) : ℝ) = (Nat.card R : ℝ) ^ (n ^ 2) * glVol (Nat.card k) n := by
  classical
  haveI := Fintype.ofFinite R
  haveI : Finite k := Finite.of_surjective π hπ
  haveI := Fintype.ofFinite k
  let φ : Matrix (Fin n) (Fin n) R →+ Matrix (Fin n) (Fin n) k := (π.mapMatrix).toAddMonoidHom
  have hφ : ∀ A, φ A = A.map π := fun A => rfl
  have hsurj : Function.Surjective φ := by
    intro B
    refine ⟨Matrix.of fun i j => (hπ (B i j)).choose, ?_⟩
    ext i j
    exact (hπ (B i j)).choose_spec
  have hunit : ∀ A, IsUnit A ↔ IsUnit (φ A) := by
    intro A
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.isUnit_iff_isUnit_det, hu, isUnit_iff_ne_zero, hφ,
      ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  set K := (Finset.univ.filter (fun A => φ A = 0)).card with hK
  have hfib : ∀ B, (Finset.univ.filter (fun A => φ A = B)).card = K :=
    fun B => AddMonoidHom.card_fiber_eq_of_mem_range φ (hsurj B) (hsurj 0)
  have h1 : (Finset.univ.filter (fun A : Matrix (Fin n) (Fin n) R => IsUnit A)).card =
      (Finset.univ.filter (fun B : Matrix (Fin n) (Fin n) k => IsUnit B)).card * K := by
    rw [Finset.card_eq_sum_card_fiberwise (f := φ)
      (t := Finset.univ.filter (fun B : Matrix (Fin n) (Fin n) k => IsUnit B))]
    · rw [Finset.sum_congr rfl (g := fun _ => K), Finset.sum_const, smul_eq_mul]
      intro B hB
      rw [← hfib B, Finset.filter_filter]
      congr 1
      refine Finset.filter_congr (fun A _ => ?_)
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨(hunit A).2 ?_, h⟩
        rw [h]; exact (Finset.mem_filter.1 hB).2
    · intro A hA
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hA ⊢
      exact (hunit A).1 hA
  have h2 : Fintype.card (Matrix (Fin n) (Fin n) R) = Fintype.card (Matrix (Fin n) (Fin n) k) * K := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := φ) (t := Finset.univ)]
    · rw [Finset.sum_congr rfl (g := fun _ => K), Finset.sum_const, smul_eq_mul, Finset.card_univ]
      intro B _
      exact hfib B
    · intro A _; exact Finset.mem_coe.2 (Finset.mem_univ _)
  have hcard : ∀ (S : Type) [Fintype S],
      (Fintype.card (Matrix (Fin n) (Fin n) S) : ℝ) = (Nat.card S : ℝ) ^ (n ^ 2) := by
    intro S _
    rw [← Nat.card_eq_fintype_card, show Nat.card (Matrix (Fin n) (Fin n) S) = Nat.card (Fin n → Fin n → S) from rfl,
      Nat.card_fun, Nat.card_fun, Nat.card_fin, ← pow_mul, ← sq]
    push_cast; rfl
  have hR : (Nat.card R : ℝ) ^ (n ^ 2) = (Nat.card k : ℝ) ^ (n ^ 2) * K := by
    rw [← hcard R, ← hcard k, h2, Nat.cast_mul]
  rw [card_GL_eq_card_isUnit, h1, Nat.cast_mul, ← card_GL_eq_card_isUnit, card_GL_field_real]
  linear_combination (-(glVol (Nat.card k) n)) * hR

theorem isUnit_quot_pow_iff {A : Type} [CommRing A] {w : Ideal A} (hw : w.IsMaximal) {c : ℕ} (hc : c ≠ 0)
    (x : A ⧸ w ^ c) : IsUnit x ↔ Ideal.Quotient.factor (Ideal.pow_le_self hc) x ≠ 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.Quotient.factor_mk, Ne, Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro h ha
    have hU := h.map (Ideal.Quotient.factor (Ideal.pow_le_self hc))
    rw [Ideal.Quotient.factor_mk, (Ideal.Quotient.eq_zero_iff_mem).2 ha] at hU
    haveI := hw.isPrime
    exact not_isUnit_zero hU
  · intro ha
    obtain ⟨y, i, hi, hyx⟩ := hw.exists_inv ha
    have hnil : IsNilpotent (Ideal.Quotient.mk (w ^ c) i) :=
      ⟨c, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow hi c⟩
    have hu : IsUnit (Ideal.Quotient.mk (w ^ c) (y * a)) := by
      have := hnil.isUnit_one_sub
      rwa [← map_one (Ideal.Quotient.mk (w ^ c)), ← map_sub,
        show (1 : A) - i = y * a by rw [← hyx]; ring] at this
    rw [map_mul] at hu
    exact isUnit_of_mul_isUnit_right hu

theorem natCard_quot {E : Type} [Field E] [NumberField E] (I : Ideal (𝓞 E)) :
    Nat.card (𝓞 E ⧸ I) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem card_GL_quot (E : Type) [Field E] [NumberField E] (𝔪 : Ideal (𝓞 E)) (h𝔪 : 𝔪 ≠ ⊥) (n : ℕ) :
    (Nat.card (GL (Fin n) (𝓞 E ⧸ 𝔪)) : ℝ) = ∏ w ∈ (normalizedFactors 𝔪).toFinset,
      (Ideal.absNorm w : ℝ) ^ ((normalizedFactors 𝔪).count w * n ^ 2) * glVol (Ideal.absNorm w : ℝ) n := by
  classical
  let e := IsDedekindDomain.quotientEquivPiFactors h𝔪
  have h1 : Nat.card (GL (Fin n) (𝓞 E ⧸ 𝔪)) = Nat.card (∀ P : (factors 𝔪).toFinset,
      GL (Fin n) (𝓞 E ⧸ (P : Ideal (𝓞 E)) ^ (factors 𝔪).count ↑P)) :=
    Nat.card_congr ((Units.mapEquiv ((e.mapMatrix).trans Matrix.piRingEquiv).toMulEquiv).trans
      MulEquiv.piUnits).toEquiv
  rw [h1, Nat.card_pi, Nat.cast_prod, ← factors_eq_normalizedFactors]
  rw [← Finset.prod_coe_sort (factors 𝔪).toFinset (fun w => (Ideal.absNorm w : ℝ) ^ ((factors 𝔪).count w * n ^ 2) *
    glVol (Ideal.absNorm w : ℝ) n)]
  refine Finset.prod_congr rfl (fun P _ => ?_)
  have hmem : (P : Ideal (𝓞 E)) ∈ factors 𝔪 := Multiset.mem_toFinset.1 P.2
  have hprime : Prime (P : Ideal (𝓞 E)) := prime_of_factor _ hmem
  have hbot : (P : Ideal (𝓞 E)) ≠ ⊥ := hprime.ne_zero
  have hmax : (P : Ideal (𝓞 E)).IsMaximal :=
    ((Ideal.isPrime_of_prime hprime)).isMaximal hbot
  have hc : (factors 𝔪).count (P : Ideal (𝓞 E)) ≠ 0 := (Multiset.count_pos.2 hmem).ne'
  letI : Field (𝓞 E ⧸ (P : Ideal (𝓞 E))) := Ideal.Quotient.field _
  haveI : Finite (𝓞 E ⧸ (P : Ideal (𝓞 E)) ^ (factors 𝔪).count ↑P) := by
    apply Nat.finite_of_card_ne_zero
    rw [natCard_quot, Ne, Ideal.absNorm_eq_zero_iff]
    exact pow_ne_zero _ hbot
  rw [card_GL_of_residue (Ideal.Quotient.factor (Ideal.pow_le_self hc)) (Ideal.Quotient.factor_surjective _)
    (isUnit_quot_pow_iff hmax hc) n, natCard_quot, natCard_quot, map_pow, Nat.cast_pow, ← pow_mul]

theorem card_GL_quot_prod : ∀ (E : Type) [Field E] [NumberField E] (𝔪 : Ideal (𝓞 E)), 𝔪 ≠ ⊥ → ∀ n : ℕ,
    (Nat.card (GL (Fin n) (𝓞 E ⧸ 𝔪)) : ℝ) = ∏ w ∈ (normalizedFactors 𝔪).toFinset,
      (Ideal.absNorm w : ℝ) ^ ((normalizedFactors 𝔪).count w * n ^ 2) * glVol (Ideal.absNorm w : ℝ) n :=
  fun E _ _ 𝔪 h𝔪 n => card_GL_quot E 𝔪 h𝔪 n

end GlobalTheory.CardGLQuot
end
end

section

open scoped Classical

namespace GlobalTheory.MassConj

theorem exists_out_mk_eq_smul {H α : Type} [Group H] [MulAction H α] (a : α) :
    ∃ g : H, Quotient.out (Quotient.mk (MulAction.orbitRel H α) a :
      MulAction.orbitRel.Quotient H α) = g • a := by
  have h := Quotient.mk_out (s := MulAction.orbitRel H α) a
  change MulAction.orbitRel H α _ _ at h
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
  obtain ⟨g, hg⟩ := h
  exact ⟨g, hg.symm⟩

theorem finsum_pairOrbit_fibre (G : Type) [Group G] (X : Type) [MulAction G X] (Γ : Subgroup G)
    (Φ : Γ → X → ℂ)
    (hΦ : ∀ δ γ : Γ, ∀ x : X, Φ (δ * γ * δ⁻¹) ((δ : G) • x) = Φ γ x) (γ₀ : Γ) :
    ∑ᶠ O : {O : MulAction.orbitRel.Quotient Γ (ConjPair Γ X) //
        ConjClasses.mk (Quotient.out O).elt = ConjClasses.mk γ₀},
        (1 / (Nat.card (MulAction.stabilizer Γ (Quotient.out O.1)) : ℂ)) *
          Φ (Quotient.out O.1).elt (Quotient.out O.1).pt =
      ∑ᶠ b : MulAction.orbitRel.Quotient (Γ ⊓ Subgroup.centralizer {(γ₀ : G)} : Subgroup G) X,
        (1 / (Nat.card (MulAction.stabilizer (Γ ⊓ Subgroup.centralizer {(γ₀ : G)} : Subgroup G)
          (Quotient.out b)) : ℂ)) * Φ γ₀ (Quotient.out b) := by
  set C : Subgroup G := Γ ⊓ Subgroup.centralizer {(γ₀ : G)} with hC
  have memC : ∀ δ : Γ, δ * γ₀ = γ₀ * δ → (δ : G) ∈ C := by
    intro δ h
    rw [hC, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    refine ⟨δ.2, ?_⟩
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    have := congrArg (fun z : Γ => (z : G)) h
    simpa using this.symm
  have commC : ∀ c : C, (⟨c, c.2.1⟩ : Γ) * γ₀ = γ₀ * ⟨c, c.2.1⟩ := by
    intro c
    have h2 := (Subgroup.mem_inf.mp c.2).2
    rw [Subgroup.mem_centralizer_iff] at h2
    have h := h2 γ₀ (Set.mem_singleton _)
    ext
    simp [h]
  let f : MulAction.orbitRel.Quotient C X →
      {O : MulAction.orbitRel.Quotient Γ (ConjPair Γ X) //
        ConjClasses.mk (Quotient.out O).elt = ConjClasses.mk γ₀} :=
    fun b => ⟨Quotient.mk _ ⟨γ₀, Quotient.out b⟩, by
      obtain ⟨δ, hδ⟩ := exists_out_mk_eq_smul (H := Γ) (ConjPair.mk γ₀ (Quotient.out b))
      rw [hδ, smul_elt, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
      exact ⟨δ⁻¹, by group⟩⟩
  have inj : Function.Injective f := by
    intro b b' hbb
    have h1 := congrArg Subtype.val hbb
    simp only [f] at h1
    have h2 := Quotient.exact h1
    change MulAction.orbitRel Γ _ _ _ at h2
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h2
    obtain ⟨δ, hδ⟩ := h2
    have he := congrArg ConjPair.elt hδ
    have hp := congrArg ConjPair.pt hδ
    simp only [smul_elt, smul_pt] at he hp
    have hcomm : δ * γ₀ = γ₀ * δ := by
      calc δ * γ₀ = δ * γ₀ * δ⁻¹ * δ := by group
        _ = γ₀ * δ := by rw [he]
    rw [← Quotient.out_eq b, ← Quotient.out_eq b']
    apply Quotient.sound
    change MulAction.orbitRel C X _ _
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    exact ⟨⟨δ, memC δ hcomm⟩, hp⟩
  have surj : Function.Surjective f := by
    rintro ⟨O, hO⟩
    rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at hO
    obtain ⟨δ, hδ⟩ := hO
    obtain ⟨c, hc⟩ := exists_out_mk_eq_smul (H := C) (δ • (Quotient.out O).pt)
    refine ⟨Quotient.mk _ (δ • (Quotient.out O).pt), ?_⟩
    apply Subtype.ext
    simp only [f]
    conv_rhs => rw [← Quotient.out_eq O]
    apply Quotient.sound
    change MulAction.orbitRel Γ _ _ _
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    refine ⟨(⟨c, c.2.1⟩ : Γ) * δ, ?_⟩
    rw [hc, mul_smul]
    ext
    · simp only [smul_elt]
      rw [hδ, commC c]
      group
    · simp only [smul_pt]
      rfl
  have term : ∀ b : MulAction.orbitRel.Quotient C X,
      (1 / (Nat.card (MulAction.stabilizer Γ (Quotient.out (f b).1)) : ℂ)) *
          Φ (Quotient.out (f b).1).elt (Quotient.out (f b).1).pt =
        (1 / (Nat.card (MulAction.stabilizer C (Quotient.out b)) : ℂ)) * Φ γ₀ (Quotient.out b) := by
    intro b
    obtain ⟨δ, hδ⟩ := exists_out_mk_eq_smul (H := Γ) (ConjPair.mk γ₀ (Quotient.out b))
    have hfb : (f b).1 = Quotient.mk _ (ConjPair.mk γ₀ (Quotient.out b)) := rfl
    rw [hfb, hδ, smul_elt, smul_pt]
    have hcard1 : Nat.card (MulAction.stabilizer Γ (δ • ConjPair.mk γ₀ (Quotient.out b))) =
        Nat.card (MulAction.stabilizer Γ (ConjPair.mk γ₀ (Quotient.out b))) :=
      Nat.card_congr (MulAction.stabilizerEquivStabilizer rfl).toEquiv.symm
    have h_to : ∀ s : MulAction.stabilizer Γ (ConjPair.mk γ₀ (Quotient.out b) : ConjPair Γ X),
        ((s : Γ) : G) ∈ C := fun s =>
      memC s.1 ((GlobalTheory.MassConj.mem_stabilizer_iff _ _).mp s.2).1
    have h_to' : ∀ s : MulAction.stabilizer Γ (ConjPair.mk γ₀ (Quotient.out b) : ConjPair Γ X),
        (⟨((s : Γ) : G), h_to s⟩ : C) ∈ MulAction.stabilizer C (Quotient.out b) := by
      intro s
      rw [MulAction.mem_stabilizer_iff]
      exact ((GlobalTheory.MassConj.mem_stabilizer_iff _ _).mp s.2).2
    have h_inv : ∀ t : MulAction.stabilizer C (Quotient.out b),
        (⟨((t : C) : G), (t : C).2.1⟩ : Γ) ∈
          MulAction.stabilizer Γ (ConjPair.mk γ₀ (Quotient.out b) : ConjPair Γ X) := by
      intro t
      rw [GlobalTheory.MassConj.mem_stabilizer_iff]
      exact ⟨commC t.1, MulAction.mem_stabilizer_iff.mp t.2⟩
    have hcard2 : Nat.card (MulAction.stabilizer Γ (ConjPair.mk γ₀ (Quotient.out b) : ConjPair Γ X)) =
        Nat.card (MulAction.stabilizer C (Quotient.out b)) :=
      Nat.card_congr
        { toFun := fun s => ⟨⟨((s : Γ) : G), h_to s⟩, h_to' s⟩
          invFun := fun t => ⟨⟨((t : C) : G), (t : C).2.1⟩, h_inv t⟩
          left_inv := fun s => rfl
          right_inv := fun t => rfl }
    have hphi : Φ (δ * γ₀ * δ⁻¹) (δ • Quotient.out b) = Φ γ₀ (Quotient.out b) :=
      hΦ δ γ₀ (Quotient.out b)
    rw [hcard1, hcard2, hphi]
  refine (finsum_comp_equiv (Equiv.ofBijective f ⟨inj, surj⟩)).symm.trans ?_
  exact finsum_congr term

end GlobalTheory.MassConj
end

section

open Polynomial Matrix GlobalTheory.LatOrb

namespace GlobalTheory.LatOrbIsLat

theorem single_mem_stdLat {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) (i : Fin n) :
    (Pi.single i (1 : K) : Fin n → K) ∈ stdLat O n := by
  rw [mem_stdLat]
  intro j
  by_cases h : j = i
  · subst h; exact ⟨1, by simp⟩
  · exact ⟨0, by simp [Pi.single_apply, h]⟩

theorem stdLat_eq_span {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) :
    stdLat O n = Submodule.span O (Set.range fun i : Fin n => (Pi.single i (1 : K) : Fin n → K)) := by
  apply le_antisymm
  · intro v hv
    rw [mem_stdLat] at hv
    choose a ha using hv
    have hv' : v = ∑ i, a i • (Pi.single i (1 : K) : Fin n → K) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, ha]
    rw [hv']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact single_mem_stdLat n i

theorem stdLat_fg {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) :
    (stdLat O n : Submodule O (Fin n → K)).FG := by
  rw [stdLat_eq_span]
  exact Submodule.fg_span (Set.finite_range _)

end GlobalTheory.LatOrbIsLat

open GlobalTheory.LatOrbIsLat in
theorem GlobalTheory.LatOrb.matLat_stdLat_isLatV : ∀ {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) (g : GL (Fin n) K),
    IsLatV O (matLat O g.val (stdLat O n)) := by
  intro O K _ _ _ n g
  refine ⟨(stdLat_fg n).map _, ?_⟩
  rw [eq_top_iff]
  intro v _
  set w : Fin n → K := (g⁻¹ : GL (Fin n) K).val *ᵥ v with hw
  have hgw : g.val *ᵥ w = v := by
    rw [hw, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hw' : w = ∑ i, w i • (Pi.single i (1 : K) : Fin n → K) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hv : v = ∑ i, w i • Matrix.mulVecLin g.val (Pi.single i (1 : K)) := by

    simp only [← map_smul, ← map_sum, ← hw']
    rw [Matrix.mulVecLin_apply, hgw]
  rw [hv]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  show _ ∈ matLat O g.val (stdLat O n)
  rw [mem_matLat]
  exact ⟨_, single_mem_stdLat n i, rfl⟩
end

section

open Polynomial Matrix GlobalTheory.LatOrb

namespace GlobalTheory.LatOrb

theorem isIntegral_of_mapsTo_lattice : ∀ {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) (M : Submodule O (Fin n → K)),
    IsLatV O M → ∀ c : Matrix (Fin n) (Fin n) K, (∀ v ∈ M, c *ᵥ v ∈ M) → IsIntegral O c := by
  intro O K _ _ _ n M hM c hc
  classical
  haveI : Module.Finite O M := Module.Finite.iff_fg.mpr hM.1
  let f : Module.End O M :=
    { toFun := fun v => ⟨c *ᵥ (v : Fin n → K), hc v v.2⟩
      map_add' := fun x y => by ext1; simp [Matrix.mulVec_add]
      map_smul' := fun a x => by
        ext1
        simp only [Submodule.coe_smul, RingHom.id_apply, SetLike.val_smul]
        rw [Matrix.mulVec_smul] }
  have hpow : ∀ k : ℕ, ∀ v : M, (c ^ k) *ᵥ (v : Fin n → K) = (((f ^ k) v : M) : Fin n → K) := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ, ← Matrix.mulVec_mulVec, pow_succ, Module.End.mul_apply]
      have h1 : ((f v : M) : Fin n → K) = c *ᵥ (v : Fin n → K) := rfl
      rw [← h1, ih]
  have key : ∀ q : O[X], ∀ v : M, aeval c q *ᵥ (v : Fin n → K) = (((aeval f q) v : M) : Fin n → K) := by
    intro q
    induction q using Polynomial.induction_on' with
    | add p q hp hq => intro v; simp [Matrix.add_mulVec, hp, hq]
    | monomial k a =>
      intro v
      rw [aeval_monomial, aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def,
        Matrix.smul_mulVec, LinearMap.smul_apply, Submodule.coe_smul, hpow]
  obtain ⟨p, hp, hpf⟩ := LinearMap.exists_monic_and_aeval_eq_zero O f
  refine ⟨p, hp, ?_⟩
  rw [← Polynomial.aeval_def]
  set A := aeval c p
  have hker : Submodule.span K (M : Set (Fin n → K)) ≤ LinearMap.ker (Matrix.mulVecLin A) := by
    rw [Submodule.span_le]
    intro v hv
    have := key p ⟨v, hv⟩
    rw [hpf] at this
    simpa using this
  rw [hM.2, top_le_iff, LinearMap.ker_eq_top] at hker
  have : Matrix.toLin' A = 0 := by rw [Matrix.toLin'_apply']; exact hker
  simpa using this

end GlobalTheory.LatOrb
end
