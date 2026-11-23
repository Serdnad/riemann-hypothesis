module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.MvPowerSeries.Substitution
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
public import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.AdicCompletion.RingHom
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.Algebra.Polynomial.Derivation
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.KummerPolynomial

@[expose] public section

section

open Polynomial

namespace GlobalTheory.TorusRoot

theorem exists_root_one (Ω : Type) [Field Ω] (p : ℕ) [hp : Fact p.Prime] [CharP Ω p]
    (A : Type) [CommRing A] [Algebra Ω A] (π : A →ₐ[Ω] Ω) (hπ : IsNilpotent (RingHom.ker π))
    (a : Aˣ) (ha : π a.val = 1) :
    ∃ (A' : Type) (_ : CommRing A') (_ : Algebra Ω A') (f : A →ₐ[Ω] A') (π' : A' →ₐ[Ω] Ω)
      (s : A'ˣ), Function.Injective f ∧ π'.comp f = π ∧ IsNilpotent (RingHom.ker π') ∧
      π' s.val = 1 ∧ s ^ p = Units.map (f : A →* A') a := by
  have hp0 : p ≠ 0 := hp.out.ne_zero
  haveI : Nontrivial A := π.toRingHom.domain_nontrivial
  let P : A[X] := X ^ p - C a.val
  have hP : P.Monic := monic_X_pow_sub_C _ hp0
  let f : A →ₐ[Ω] AdjoinRoot P := IsScalarTower.toAlgHom Ω A (AdjoinRoot P)
  have hf : ∀ x, f x = AdjoinRoot.of P x := fun x => rfl
  have hinj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    rw [hf, ← AdjoinRoot.mk_C, AdjoinRoot.mk_eq_zero] at hx
    by_contra hx0
    refine hP.not_dvd_of_degree_lt (C_ne_zero.2 hx0) ?_ hx
    rw [degree_C hx0, degree_X_pow_sub_C (Nat.pos_of_ne_zero hp0)]
    exact_mod_cast Nat.pos_of_ne_zero hp0
  have hev : P.eval₂ (π : A →+* Ω) 1 = 0 := by
    simp [P, eval₂_sub, ha]
  let g : AdjoinRoot P →+* Ω := AdjoinRoot.lift (π : A →+* Ω) 1 hev
  have hg : ∀ x, g (f x) = π x := fun x => by
    rw [hf]; exact AdjoinRoot.lift_of hev
  have hgr : g (AdjoinRoot.root P) = 1 := AdjoinRoot.lift_root hev
  let π' : AdjoinRoot P →ₐ[Ω] Ω :=
    { g with
      commutes' := fun c => by
        have : algebraMap Ω (AdjoinRoot P) c = f (algebraMap Ω A c) := (f.commutes c).symm
        change g _ = _
        rw [this, hg, π.commutes] }
  have hroot : AdjoinRoot.root P ^ p = f a.val := by
    have h := AdjoinRoot.eval₂_root P
    simp only [P, eval₂_sub, eval₂_X_pow, eval₂_C] at h
    exact sub_eq_zero.1 h
  have hu : IsUnit (AdjoinRoot.root P) := by
    rw [← isUnit_pow_iff hp0, hroot]
    exact a.isUnit.map f
  haveI : Nontrivial (AdjoinRoot P) := g.domain_nontrivial
  haveI : CharP (AdjoinRoot P) p :=
    charP_of_injective_algebraMap (algebraMap Ω (AdjoinRoot P)).injective p
  refine ⟨AdjoinRoot P, inferInstance, inferInstance, f, π', hu.unit, hinj, ?_, ?_, hgr, ?_⟩
  · ext x; exact hg x
  · set I : Ideal (AdjoinRoot P) := (RingHom.ker π).map f with hI
    have hIn : IsNilpotent I := by
      obtain ⟨n, hn⟩ := hπ
      refine ⟨n, ?_⟩
      rw [hI, ← Ideal.map_pow, hn]
      exact Ideal.map_bot
    set J : Ideal (AdjoinRoot P) := Ideal.span {AdjoinRoot.root P - 1} with hJ
    have hJn : IsNilpotent J := by
      obtain ⟨n, hn⟩ := hIn
      refine ⟨p * n, ?_⟩
      rw [pow_mul, Ideal.zero_eq_bot, eq_bot_iff, ← Ideal.zero_eq_bot, ← hn]
      apply Ideal.pow_right_mono
      rw [hJ, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem, sub_pow_char, hroot,
        one_pow, ← map_one f, ← map_sub]
      apply Ideal.mem_map_of_mem
      rw [RingHom.mem_ker, map_sub, ha, map_one, sub_self]
    obtain ⟨n, hn⟩ := (Commute.all I J).isNilpotent_add hIn hJn
    refine ⟨n, ?_⟩
    rw [Ideal.zero_eq_bot, eq_bot_iff, ← Ideal.zero_eq_bot, ← hn]
    apply Ideal.pow_right_mono
    intro x hx
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective x
    obtain ⟨r, hr⟩ : (X - C 1 : A[X]) ∣ q - C (q.eval 1) := X_sub_C_dvd_sub_C_eval
    have h1 : AdjoinRoot.mk P q = f (q.eval 1) + (AdjoinRoot.root P - 1) * AdjoinRoot.mk P r := by
      have := congrArg (AdjoinRoot.mk P) hr
      simp only [map_sub, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X, map_one] at this
      rw [hf, ← this]; ring
    have hx' : g (AdjoinRoot.mk P q) = 0 := hx
    rw [h1, map_add (f := _), map_mul, map_sub, hgr, map_one, sub_self, zero_mul, add_zero, hg] at hx'
    rw [h1, Ideal.add_eq_sup]
    exact Submodule.add_mem_sup (Ideal.mem_map_of_mem _ hx')
      (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  · ext
    simpa using hroot

theorem exists_root_fin (Ω : Type) [Field Ω] (p : ℕ) [hp : Fact p.Prime] [CharP Ω p] (n : ℕ) :
    ∀ (A : Type) [CommRing A] [Algebra Ω A] (π : A →ₐ[Ω] Ω) (_ : IsNilpotent (RingHom.ker π))
    (a : Fin n → Aˣ) (_ : ∀ i, π (a i).val = 1),
    ∃ (A' : Type) (_ : CommRing A') (_ : Algebra Ω A') (f : A →ₐ[Ω] A') (π' : A' →ₐ[Ω] Ω)
      (s : Fin n → A'ˣ), Function.Injective f ∧ π'.comp f = π ∧ IsNilpotent (RingHom.ker π') ∧
      (∀ i, π' (s i).val = 1) ∧ ∀ i, s i ^ p = Units.map (f : A →* A') (a i) := by
  induction n with
  | zero =>
    intro A _ _ π hπ a _
    exact ⟨A, inferInstance, inferInstance, AlgHom.id Ω A, π, a, Function.injective_id, rfl, hπ,
      fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    intro A _ _ π hπ a ha
    obtain ⟨B, _, _, f, ρ, s, hf, hρ, hρn, hs1, hs⟩ :=
      ih A π hπ (fun i => a i.succ) (fun i => ha i.succ)
    have h0 : ρ (Units.map (f : A →* B) (a 0)).val = 1 := by
      have := congrArg (fun φ : A →ₐ[Ω] Ω => φ (a 0).val) hρ
      simpa [ha 0] using this
    obtain ⟨C, _, _, g, σ, t, hg, hσ, hσn, ht1, ht⟩ :=
      exists_root_one Ω p B ρ hρn _ h0
    refine ⟨C, inferInstance, inferInstance, g.comp f, σ,
      Fin.cons t (fun i => Units.map (g : B →* C) (s i)), hg.comp hf, ?_, hσn, ?_, ?_⟩
    · rw [← AlgHom.comp_assoc, hσ, hρ]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using ht1
      · have := congrArg (fun φ : B →ₐ[Ω] Ω => φ (s j).val) hσ
        simpa [hs1 j] using this
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [Fin.cons_zero, ht]; rfl
      · rw [Fin.cons_succ, ← map_pow, hs j]; rfl

theorem exists_root_character :
    ∀ (Ω : Type) [Field Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p] (X : Type) [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (A : Type) [CommRing A] [Algebra Ω A]
    (π : A →ₐ[Ω] Ω), IsNilpotent (RingHom.ker π) → ∀ χ : Multiplicative X →* Aˣ,
    (∀ x, π (χ x).val = 1) →
    ∃ (A' : Type) (_ : CommRing A') (_ : Algebra Ω A') (f : A →ₐ[Ω] A') (π' : A' →ₐ[Ω] Ω)
      (χ' : Multiplicative X →* A'ˣ), Function.Injective f ∧ π'.comp f = π ∧
      IsNilpotent (RingHom.ker π') ∧ (∀ x, π' (χ' x).val = 1) ∧
      χ' ^ p = (Units.map (f : A →* A')).comp χ := by
  intro Ω _ p _ _ X _ _ _ A _ _ π hπ χ hχ
  let b := Module.finBasis ℤ X
  obtain ⟨B, _, _, f, ρ, s, hf, hρ, hρn, hs1, hs⟩ :=
    exists_root_fin Ω p _ A π hπ (fun i => χ (Multiplicative.ofAdd (b i))) (fun i => hχ _)
  let l : X →ₗ[ℤ] Additive Bˣ := b.constr ℤ (fun i => Additive.ofMul (s i))
  have hl : ∀ i, l (b i) = Additive.ofMul (s i) := fun i => b.constr_basis ℤ _ i
  let χ' : Multiplicative X →* Bˣ := AddMonoidHom.toMultiplicativeLeft l.toAddMonoidHom
  have hχ' : ∀ i, χ' (Multiplicative.ofAdd (b i)) = s i := fun i => by
    change Additive.toMul (l (b i)) = _
    rw [hl]; rfl
  have key : ∀ {G : Type} [CommGroup G] (φ ψ : Multiplicative X →* G),
      (∀ i, φ (Multiplicative.ofAdd (b i)) = ψ (Multiplicative.ofAdd (b i))) → φ = ψ := by
    intro G _ φ ψ h
    have : (MonoidHom.toAdditiveRight φ).toIntLinearMap =
        (MonoidHom.toAdditiveRight ψ).toIntLinearMap :=
      b.ext fun i => congrArg Additive.ofMul (h i)
    refine MonoidHom.ext fun x => ?_
    exact congrArg Additive.toMul (LinearMap.congr_fun this x.toAdd)
  refine ⟨B, inferInstance, inferInstance, f, ρ, χ', hf, hρ, hρn, ?_, ?_⟩
  · have : (Units.map (ρ : B →* Ω)).comp χ' = 1 := key _ _ fun i => by
      ext
      simpa [hχ'] using hs1 i
    intro x
    exact congrArg Units.val (DFunLike.congr_fun this x)
  · exact key _ _ fun i => by
      rw [MonoidHom.pow_apply, hχ', hs]; rfl

end GlobalTheory.TorusRoot
end

section

namespace GlobalTheory

theorem exists_forall_eq_pow_of_finite_field (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Finite F]
    (k : Type) [Field k] [CharP k p] (a b : F →+* k) : ∃ n : ℕ, ∀ x, b x = a x ^ p ^ n := by
  have : CharP F p := RingHom.charP a a.injective p
  let : Algebra (ZMod p) F := ZMod.algebra F p
  let : Algebra (ZMod p) k := ZMod.algebra k p
  let : Algebra F k := a.toAlgebra
  have : IsScalarTower (ZMod p) F k :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let b' : F →ₐ[ZMod p] k :=
    { b with
      commutes' := fun r => RingHom.congr_fun
        (Subsingleton.elim (b.comp (algebraMap (ZMod p) F)) (algebraMap (ZMod p) k)) r }
  obtain ⟨n, hn⟩ := FiniteField.exists_forall_apply_eq_pow (ZMod p) p F (b'.restrictNormal' F)
  refine ⟨n, fun x => ?_⟩
  have h := AlgHom.restrictNormal_commutes b' F x
  have h2 : b'.restrictNormal F x = x ^ p ^ n := by
    have := hn x
    rw [Nat.card_zmod] at this
    exact this
  rw [h2, map_pow] at h
  exact h.symm

theorem exists_forall_eq_pow_of_ker_le (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE]
    [Module.Finite ℤ OE] (k : Type) [Field k] [CharP k p] (σ₀ σ : OE →+* k)
    (h : ∀ x, σ₀ x = 0 → σ x = 0) : ∃ n : ℕ, ∀ x, σ x = σ₀ x ^ p ^ n := by
  let I : Ideal OE := RingHom.ker σ₀
  have : I.IsPrime := RingHom.ker_isPrime σ₀
  have hp : (p : OE ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
    simp [I, RingHom.mem_ker]
  have : Module.Finite ℤ (OE ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mk I).toIntAlgHom.toLinearMap
      Ideal.Quotient.mk_surjective
  have : Finite (OE ⧸ I) := by
    refine Module.finite_of_fg_torsion _ (fun x => ⟨⟨(p : ℤ), ?_⟩, ?_⟩)
    · exact mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    · change (p : ℤ) • x = 0
      rw [zsmul_eq_mul, Int.cast_natCast, hp, zero_mul]
  let : Field (OE ⧸ I) := (Finite.isField_of_domain (OE ⧸ I)).toField
  obtain ⟨n, hn⟩ := exists_forall_eq_pow_of_finite_field p (OE ⧸ I) k
    (Ideal.Quotient.lift I σ₀ (fun _ hx => hx)) (Ideal.Quotient.lift I σ (fun x hx => h x hx))
  exact ⟨n, fun x => hn (Ideal.Quotient.mk I x)⟩

end GlobalTheory
end

section

open scoped BigOperators
open Polynomial IntermediateField

namespace GlobalTheory

theorem minpoly_eq_X_pow_sub_C_of_pow_mem {K : Type} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (M : Subfield K) (hM : ∀ y : K, y ^ p ∈ M) (x : K) (hx : x ∉ M) :
    minpoly M x = X ^ p - C (⟨x ^ p, hM x⟩ : M) := by
  have hp : p.Prime := Fact.out
  symm
  apply minpoly.eq_of_irreducible_of_monic
  · apply X_pow_sub_C_irreducible_of_prime hp
    intro b hb
    apply hx
    have h1 : (b : K) ^ p = x ^ p := by
      have := congrArg (fun z : M => (z : K)) hb
      simpa using this
    have h2 : (b : K) = x := frobenius_inj K p (by simpa [frobenius_def] using h1)
    rw [← h2]; exact b.2
  · simp only [map_sub, map_pow, aeval_X, aeval_C]
    exact sub_self _
  · exact monic_X_pow_sub_C _ hp.ne_zero

theorem isIntegral_of_pow_mem_subfield {K : Type} [Field K] (p : ℕ) [Fact p.Prime]
    (M : Subfield K) (hM : ∀ y : K, y ^ p ∈ M) (x : K) : IsIntegral M x := by
  have hp : p.Prime := Fact.out
  refine ⟨X ^ p - C (⟨x ^ p, hM x⟩ : M), monic_X_pow_sub_C _ hp.ne_zero, ?_⟩
  rw [← aeval_def]
  simp only [map_sub, map_pow, aeval_X, aeval_C]
  exact sub_self _

theorem exists_pow_eq_of_forall_derivation_eq_zero (K : Type) [Field K] (p : ℕ) [Fact p.Prime]
    [CharP K p] (f : K) (hf : ∀ D : Derivation ℤ K K, D f = 0) : ∃ h : K, h ^ p = f := by
  have hp : p.Prime := Fact.out
  by_contra hne
  let S : Set (Subfield K) := {M | (∀ y : K, y ^ p ∈ M) ∧ f ∉ M}
  have h0 : (frobenius K p).fieldRange ∈ S := by
    refine ⟨fun y => ⟨y, rfl⟩, ?_⟩
    rintro ⟨y, hy⟩
    exact hne ⟨y, hy⟩
  obtain ⟨M, -, hM⟩ := zorn_le_nonempty₀ S (fun c hcS hc y hy => by
    refine ⟨sSup c, ⟨fun z => (le_sSup hy : y ≤ sSup c) ((hcS hy).1 z), ?_⟩,
      fun z hz => le_sSup hz⟩
    rw [Subfield.mem_sSup_of_directedOn ⟨y, hy⟩ hc.directedOn]
    rintro ⟨z, hz, hfz⟩
    exact (hcS hz).2 hfz) _ h0
  obtain ⟨hMp, hMf⟩ := hM.prop
  have hrank : ∀ x : K, x ∉ M → Module.finrank M M⟮x⟯ = p := by
    intro x hx
    rw [adjoin.finrank (isIntegral_of_pow_mem_subfield p M hMp x),
      minpoly_eq_X_pow_sub_C_of_pow_mem p M hMp x hx, natDegree_X_pow_sub_C _]
  have htop : ∀ x : K, x ∈ M⟮f⟯ := by
    intro x
    by_cases hx : x ∈ M
    · exact (M⟮f⟯).algebraMap_mem ⟨x, hx⟩
    have hle : M ≤ (M⟮x⟯).toSubfield := fun z hz => (M⟮x⟯).algebraMap_mem ⟨z, hz⟩
    have hfx : f ∈ M⟮x⟯ := by
      by_contra hcon
      have h1 : (M⟮x⟯).toSubfield ∈ S := ⟨fun y => hle (hMp y), hcon⟩
      exact hx (hM.le_of_ge h1 hle (mem_adjoin_simple_self M x))
    haveI := adjoin.finiteDimensional (isIntegral_of_pow_mem_subfield p M hMp x)
    have heq : M⟮f⟯ = M⟮x⟯ :=
      eq_of_le_of_finrank_eq (adjoin_simple_le_iff.mpr hfx) (by rw [hrank f hMf, hrank x hx])
    rw [heq]; exact mem_adjoin_simple_self M x
  have hsurj : Function.Surjective (aeval f : M[X] →ₐ[M] K) := by
    intro x
    have h1 : x ∈ (M⟮f⟯).toSubalgebra := htop x
    rw [adjoin_simple_toSubalgebra_of_isAlgebraic
      (isIntegral_of_pow_mem_subfield p M hMp f).isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at h1
    exact h1
  have hd : ∀ q : M[X], aeval f q = 0 → aeval f ((derivative' : Derivation M M[X] M[X]) q) = 0 := by
    intro q hq
    obtain ⟨r, rfl⟩ := minpoly.dvd M f hq
    have h1 : aeval f (derivative (minpoly M f)) = 0 := by
      rw [minpoly_eq_X_pow_sub_C_of_pow_mem p M hMp f hMf]
      simp [derivative_X_pow]
    simp [derivative'_apply, derivative_mul, h1]
  have h2 := hf ((Derivation.liftOfSurjective hsurj hd).restrictScalars ℤ)
  have h3 := Derivation.liftOfSurjective_apply hsurj hd X
  rw [Derivation.restrictScalars_apply] at h2
  simp only [aeval_X, derivative'_apply, derivative_X, map_one] at h3
  exact one_ne_zero (h3.symm.trans h2)

end GlobalTheory
end

section

namespace GlobalTheory.ChF

private theorem nonempty_padicInt_ringHom (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O]
    (I : Ideal O) [IsAdicComplete I O] (hp : (p : O) ∈ I) : Nonempty (ℤ_[p] →+* O) := by
  have hd : ∀ n : ℕ, ringChar (O ⧸ I ^ n) ∣ p ^ n := fun n => by
    apply ringChar.dvd
    rw [← map_natCast (Ideal.Quotient.mk (I ^ n)), Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
    exact Ideal.pow_mem_pow hp n
  refine ⟨IsAdicComplete.liftRingHom I
    (fun n => (ZMod.castHom (hd n) (O ⧸ I ^ n)).comp (PadicInt.toZModPow n)) ?_⟩
  intro m n hle
  rw [← PadicInt.zmod_cast_comp_toZModPow m n hle, ← RingHom.comp_assoc, ← RingHom.comp_assoc]
  congr 1
  exact RingHom.ext_zmod _ _

private theorem padicInt_ringHom_matrix_ext (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O]
    [IsHausdorff (Ideal.span {(p : O)}) O] (n : ℕ)
    (f g : ℤ_[p] →+* Matrix (Fin n) (Fin n) O) (c : ℤ_[p]) : f c = g c := by
  ext i j
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := Ideal.span {(p : O)}) inferInstance _ fun k => ?_
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp (PadicInt.appr_spec k c)
  have hc : c = (c.appr k : ℤ_[p]) + ((p ^ k : ℕ) : ℤ_[p]) * d := by
    rw [Nat.cast_pow, ← hd]; ring
  have h : f c - g c = (p ^ k : ℕ) • (f d - g d) := by
    rw [hc]
    simp only [map_add (f := _), map_mul, map_natCast, nsmul_eq_mul, mul_sub]
    abel
  have h' : f c i j - g c i j = (p : O) ^ k * (f d i j - g d i j) := by
    have := congrFun (congrFun h i) j
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.sub_apply, nsmul_eq_mul, Nat.cast_pow] at this
    exact this
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, h']
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem padicInt_algebra_of_isAdicComplete_and_matrix_unique :
    ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O],
      Nonempty (Algebra ℤ_[p] O) ∧ ∀ [Algebra ℤ_[p] O] (n : ℕ)
        (f : ℤ_[p] →+* Matrix (Fin n) (Fin n) O) (c : ℤ_[p]),
        f c = algebraMap ℤ_[p] O c • (1 : Matrix (Fin n) (Fin n) O) := by
  intro p _ O _ _
  refine ⟨?_, fun n f c => ?_⟩
  · obtain ⟨φ⟩ := nonempty_padicInt_ringHom p O _ (Ideal.mem_span_singleton_self _)
    exact ⟨φ.toAlgebra⟩
  · rw [padicInt_ringHom_matrix_ext p O n f
      ((algebraMap O (Matrix (Fin n) (Fin n) O)).comp (algebraMap ℤ_[p] O)) c,
      RingHom.comp_apply, Algebra.algebraMap_eq_smul_one (A := Matrix (Fin n) (Fin n) O)]

end GlobalTheory.ChF
end

section

namespace GlobalTheory.LogSubst

open MvPowerSeries

theorem coeff_pow_pow_eq_zero {C σ : Type} [CommRing C] {l : ℕ} (hl : 2 ≤ l)
    {u : MvPowerSeries σ C} (hu : constantCoeff u = 0) {μ : σ →₀ ℕ} {s : ℕ}
    (h : μ.degree ≤ s) : coeff μ (u ^ (l ^ s)) = 0 := by
  apply coeff_of_lt_order
  refine lt_of_lt_of_le ?_ (le_order_pow_of_constantCoeff_eq_zero _ hu)
  have : s < l ^ s := Nat.lt_pow_self (by omega)
  exact_mod_cast lt_of_le_of_lt h this

theorem coeff_subst_sum_pow_pow : ∀ (C : Type) [Field C] (σ τ I : Type) [Fintype σ] [Fintype τ] [Fintype I] (l : ℕ), 2 ≤ l → ∀ (co : I → ℕ → C) (t : I → MvPowerSeries σ C) (F : MvPowerSeries σ C) (f : σ → MvPowerSeries τ C), (∀ x, MvPowerSeries.constantCoeff (f x) = 0) → (∀ c, MvPowerSeries.constantCoeff (t c) = 0) → (∀ μ : σ →₀ ℕ, MvPowerSeries.coeff μ F = ∑ s ∈ Finset.range (μ.degree + 1), ∑ c, co c s * MvPowerSeries.coeff μ (t c ^ (l ^ s))) → ∀ ν : τ →₀ ℕ, MvPowerSeries.coeff ν (MvPowerSeries.subst f F) = ∑ s ∈ Finset.range (ν.degree + 1), ∑ c, co c s * MvPowerSeries.coeff ν ((MvPowerSeries.subst f (t c) : MvPowerSeries τ C) ^ (l ^ s)) := by
  intro C _ σ τ I _ _ _ l hl co t F f hf ht hF ν
  have hs : HasSubst f := hasSubst_of_constantCoeff_zero hf
  set G : MvPowerSeries σ C :=
    ∑ s ∈ Finset.range (ν.degree + 1), ∑ c, co c s • t c ^ (l ^ s) with hG
  have hord : ((ν.degree + 1 : ℕ) : ℕ∞) ≤ (F - G).order := by
    apply nat_le_order
    intro μ hμ
    rw [map_sub, hF μ, hG, sub_eq_zero]

    simp only [map_sum, coeff_smul]
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) ?_
    intro s _ hs'
    rw [Finset.mem_range] at hs'
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [coeff_pow_pow_eq_zero hl (ht c) (by omega), mul_zero]
  have h1 : (1 : ℕ∞) ≤ ⨅ i, (f i).order :=
    le_iInf fun i => one_le_order_iff_constCoeff_eq_zero.2 (hf i)
  have h2 : ((ν.degree + 1 : ℕ) : ℕ∞) ≤ (subst f (F - G) : MvPowerSeries τ C).order := by
    refine le_trans ?_ (le_order_subst hs (F - G))
    calc ((ν.degree + 1 : ℕ) : ℕ∞) = 1 * ((ν.degree + 1 : ℕ) : ℕ∞) := (one_mul _).symm
      _ ≤ _ := mul_le_mul' h1 hord
  have h3 : coeff ν (subst f (F - G) : MvPowerSeries τ C) = 0 := by
    apply coeff_of_lt_order
    refine lt_of_lt_of_le ?_ h2
    exact_mod_cast Nat.lt_succ_self _
  rw [← substAlgHom_apply hs, map_sub, map_sub, sub_eq_zero, substAlgHom_apply] at h3
  rw [h3, hG]

  simp only [map_sum, map_smul, map_pow, substAlgHom_apply, smul_eq_mul]

end GlobalTheory.LogSubst
end
