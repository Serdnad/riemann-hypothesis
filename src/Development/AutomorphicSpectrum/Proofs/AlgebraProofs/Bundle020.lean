module

public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle014
public import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
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
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Mathlib.RingTheory.RootsOfUnity.Lemmas
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle002
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.LocalRing.Module
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle013
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Finiteness.Nakayama
public import Mathlib.Algebra.BigOperators.Associated

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

namespace GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd

private theorem exists_hom_of_comp_snd_eq_comp_smul {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {M X Y : C} [MonObj M] [ModObj M X] (a b : Y ⟶ M ⊗ X)
    (h : b ≫ SemiCartesianMonoidalCategory.snd M X = a ≫ ModObj.smul (M := M) (X := X)) :
    ∃ r : Y ⟶ M ⊗ X, r ≫ SemiCartesianMonoidalCategory.snd M X = a ≫ SemiCartesianMonoidalCategory.snd M X ∧
      r ≫ ModObj.smul (M := M) (X := X) = b ≫ ModObj.smul (M := M) (X := X) := by
  have key : ∀ c : Y ⟶ M ⊗ X, c ≫ ModObj.smul (M := M) (X := X) =
      (c ≫ SemiCartesianMonoidalCategory.fst M X) • (c ≫ SemiCartesianMonoidalCategory.snd M X) := by
    intro c
    rw [CategoryTheory.Hom.smul_def, CartesianMonoidalCategory.lift_comp_fst_snd]
  refine ⟨CartesianMonoidalCategory.lift
    ((b ≫ SemiCartesianMonoidalCategory.fst M X) * (a ≫ SemiCartesianMonoidalCategory.fst M X))
    (a ≫ SemiCartesianMonoidalCategory.snd M X), CartesianMonoidalCategory.lift_snd _ _, ?_⟩
  rw [← CategoryTheory.Hom.smul_def, mul_smul, ← key a, ← h, ← key b]

theorem orbit_trans {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X] (x y w : X.left) :
    y ∈ orbit G X x → w ∈ orbit G X y → w ∈ orbit G X x := by
  simp only [GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot.orbit, Set.mem_image, Set.mem_preimage, Set.mem_singleton_iff]
  rintro ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := (ModObj.smul (M := G) (X := X)).left) (g := (SemiCartesianMonoidalCategory.snd G X).left)
    p q hq.symm
  have e₁ : (SemiCartesianMonoidalCategory.snd G X).left ≫ X.hom = (G ⊗ X).hom := Over.w _
  have e₂ : (ModObj.smul (M := G) (X := X)).left ≫ X.hom = (G ⊗ X).hom := Over.w _
  have hw : pullback.snd (ModObj.smul (M := G) (X := X)).left (SemiCartesianMonoidalCategory.snd G X).left ≫
      (G ⊗ X).hom =
      pullback.fst (ModObj.smul (M := G) (X := X)).left (SemiCartesianMonoidalCategory.snd G X).left ≫
      (G ⊗ X).hom := by
    rw [← e₂, pullback.condition_assoc, e₁, e₂]
  obtain ⟨r, hr₁, hr₂⟩ := exists_hom_of_comp_snd_eq_comp_smul
    (Y := Over.mk (pullback.fst (ModObj.smul (M := G) (X := X)).left
      (SemiCartesianMonoidalCategory.snd G X).left ≫ (G ⊗ X).hom))
    (Over.homMk (pullback.fst (ModObj.smul (M := G) (X := X)).left
      (SemiCartesianMonoidalCategory.snd G X).left) rfl)
    (Over.homMk (pullback.snd (ModObj.smul (M := G) (X := X)).left
      (SemiCartesianMonoidalCategory.snd G X).left) hw)
    (Over.OverMorphism.ext (by
      simp only [Over.comp_left, Over.homMk_left]
      exact pullback.condition.symm))
  refine ⟨r.left z, ?_, ?_⟩
  · have h₁ := congrArg Over.Hom.left hr₁
    simp only [Over.comp_left, Over.homMk_left] at h₁
    rw [← Scheme.Hom.comp_apply, h₁, Scheme.Hom.comp_apply, hz₁, hp]
  · have h₂ := congrArg Over.Hom.left hr₂
    simp only [Over.comp_left, Over.homMk_left] at h₂
    rw [← Scheme.Hom.comp_apply, h₂, Scheme.Hom.comp_apply, hz₂]

end GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd
end

section

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem fg_inf_restrictScalars_of_integers (C : Type) [Field C] (v : Valuation C NNReal) (O : Type)
    [CommRing O] [Algebra O C] (hv : v.Integers O) (V : Type) [AddCommGroup V] [Module C V]
    [Module O V] [IsScalarTower O C V] (L : Submodule O V) (U : Submodule C V) (hL : L.FG) :
    (L ⊓ U.restrictScalars O).FG := by
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  haveI : IsDomain O := hinj.isDomain
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  let f : L →ₗ[O] (V ⧸ U) := (U.mkQ.restrictScalars O).comp L.subtype
  haveI : Module.Finite O L := Module.Finite.iff_fg.2 hL
  haveI : Module.Finite O (LinearMap.range f) := inferInstance
  haveI : Module.Flat O (LinearMap.range f) := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    rintro ⟨x, hx⟩ ⟨⟨a, ha⟩, h⟩
    have h1 : a • x = 0 := congrArg Subtype.val h
    have ha0 : algebraMap O C a ≠ 0 := by
      intro h0
      exact nonZeroDivisors.ne_zero ha (hinj (by simpa using h0))
    rw [← algebraMap_smul C a x] at h1
    have : x = 0 := (smul_eq_zero.1 h1).resolve_left ha0
    simp [this]
  haveI : Module.Free O (LinearMap.range f) := Module.free_of_flat_of_isLocalRing
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f.rangeRestrict LinearMap.id
    f.surjective_rangeRestrict
  let p : L →ₗ[O] V := L.subtype.comp (LinearMap.id - s.comp f.rangeRestrict)
  have key : L ⊓ U.restrictScalars O = LinearMap.range p := by
    apply le_antisymm
    · rintro x ⟨hxL, hxU⟩
      refine ⟨⟨x, hxL⟩, ?_⟩
      have : f.rangeRestrict ⟨x, hxL⟩ = 0 := by
        apply Subtype.ext
        change U.mkQ x = 0
        exact (Submodule.Quotient.mk_eq_zero U).2 hxU
      simp [p, this]
    · rintro _ ⟨y, rfl⟩
      refine ⟨(y - s (f.rangeRestrict y)).2, ?_⟩
      have h2 : f.rangeRestrict (s (f.rangeRestrict y)) = f.rangeRestrict y :=
        LinearMap.congr_fun hs _
      have h3 : f (y - s (f.rangeRestrict y)) = 0 := by
        rw [map_sub, sub_eq_zero]
        exact (congrArg Subtype.val h2).symm
      exact (Submodule.Quotient.mk_eq_zero U).1 h3
  rw [key]
  exact Module.Finite.iff_fg.1 inferInstance

end GlobalTheory.CompanionTheory.Ar.HT
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem mem_of_pow_mem_of_integrally_closed {Ω : Type} [Field Ω] (R : Subring Ω)
    (hR : ∀ z : Ω, IsIntegral R z → z ∈ R) {z : Ω} {m : ℕ} (hm : 0 < m) (h : z ^ m ∈ R) :
    z ∈ R := by
  refine hR z ⟨Polynomial.X ^ m - Polynomial.C ⟨z ^ m, h⟩, Polynomial.monic_X_pow_sub_C _ hm.ne', ?_⟩
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
  exact sub_eq_zero.2 rfl

theorem valuation_pow_zpow_eq_of_mul_eq {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    {π α : F} {n k : ℤ} {m M : ℕ} (hπ : v.valuation F π = WithZero.exp (-1 : ℤ))
    (hα : v.valuation F α = WithZero.exp (-k)) (h : n * M = m * k) :
    v.valuation F ((π ^ n) ^ M) = v.valuation F (α ^ m) := by
  rw [map_pow, map_zpow₀, hπ, map_pow, hα, ← WithZero.exp_zsmul, ← WithZero.exp_nsmul,
    ← WithZero.exp_nsmul]
  congr 1
  simp only [smul_eq_mul, nsmul_eq_mul]
  linear_combination -h

theorem exists_global_generator : ∀ (F Ω X : Type) [Field F] [NumberField F] [Field Ω] (φ : F →+* Ω) (R : X → Subring Ω) (s : X → Ω) (pl : X → Option (HeightOneSpectrum (𝓞 F))) (r : HeightOneSpectrum (𝓞 F) →₀ ℚ), (∀ x, ∀ z : Ω, IsIntegral (R x) z → z ∈ R x) → (∀ x, pl x = none → (∀ a : F, φ a ∈ R x) ∧ s x ∈ R x ∧ s x ≠ 0 ∧ (s x)⁻¹ ∈ R x) → (∀ x v, pl x = some v → (∀ a : F, v.valuation F a ≤ 1 → φ a ∈ R x) ∧ ∃ (m : ℕ) (n : ℤ) (π : F), 0 < m ∧ (n : ℚ) = m * r v ∧ v.valuation F π = WithZero.exp (-1 : ℤ) ∧ s x ≠ 0 ∧ s x ^ m / φ π ^ n ∈ R x ∧ φ π ^ n / s x ^ m ∈ R x) → ∃ (M : ℕ) (α : F), 0 < M ∧ α ≠ 0 ∧ (∀ v : HeightOneSpectrum (𝓞 F), ∃ n : ℤ, (n : ℚ) = M * r v ∧ v.valuation F α = WithZero.exp (-n)) ∧ ∀ x, s x ^ M / φ α ∈ R x ∧ φ α / s x ^ M ∈ R x := by
  intro F Ω X _ _ _ φ R s pl r hR hgen hsp
  obtain ⟨M, α, hM, hα0, hval⟩ := exists_pow_principal F r
  refine ⟨M, α, hM, hα0, hval, fun x => ?_⟩
  cases hx : pl x with
  | none =>
    obtain ⟨hφ, hs, -, hsi⟩ := hgen x hx
    have hαi : (φ α)⁻¹ ∈ R x := by
      rw [← map_inv₀]
      exact hφ _
    constructor
    · rw [div_eq_mul_inv]
      exact (R x).mul_mem ((R x).pow_mem hs M) hαi
    · rw [div_eq_mul_inv, ← inv_pow]
      exact (R x).mul_mem (hφ α) ((R x).pow_mem hsi M)
  | some v =>
    obtain ⟨hφ, m, n, π, hm, hn, hπ, hs0, h1, h2⟩ := hsp x v hx
    obtain ⟨k, hk, hαv⟩ := hval v
    have hkey : n * (M : ℤ) = m * k := by
      have : ((n * M : ℤ) : ℚ) = ((m * k : ℤ) : ℚ) := by
        push_cast
        rw [hn, hk]
        ring
      exact_mod_cast this
    have hv := valuation_pow_zpow_eq_of_mul_eq v hπ hαv hkey
    have hπ0 : π ≠ 0 := by
      rintro rfl
      rw [map_zero] at hπ
      exact WithZero.coe_ne_zero hπ.symm
    have hφπ : φ π ≠ 0 := (map_ne_zero φ).2 hπ0
    have hφα : φ α ≠ 0 := (map_ne_zero φ).2 hα0
    have hP : φ π ^ n ≠ 0 := zpow_ne_zero _ hφπ
    have hβ : v.valuation F ((π ^ n) ^ M / α ^ m) = 1 := by
      rw [map_div₀, hv, div_self]
      exact (Valuation.ne_zero_iff _).2 (pow_ne_zero _ hα0)
    have hβ1 : φ ((π ^ n) ^ M / α ^ m) ∈ R x := hφ _ hβ.le
    have hβ2 : φ ((π ^ n) ^ M / α ^ m)⁻¹ ∈ R x := hφ _ (by rw [map_inv₀, hβ, inv_one])
    constructor
    · apply mem_of_pow_mem_of_integrally_closed (R x) (hR x) hm
      have he : (s x ^ M / φ α) ^ m = (s x ^ m / φ π ^ n) ^ M * φ ((π ^ n) ^ M / α ^ m) := by
        simp only [map_div₀, map_pow, map_zpow₀]
        rw [div_pow, div_pow, ← pow_mul, ← pow_mul, mul_comm M m, div_mul_div_comm,
          mul_comm (s x ^ (m * M)), mul_div_mul_left _ _ (pow_ne_zero _ hP)]
      rw [he]
      exact (R x).mul_mem ((R x).pow_mem h1 M) hβ1
    · apply mem_of_pow_mem_of_integrally_closed (R x) (hR x) hm
      have he : (φ α / s x ^ M) ^ m = (φ π ^ n / s x ^ m) ^ M * φ ((π ^ n) ^ M / α ^ m)⁻¹ := by
        simp only [map_inv₀, map_div₀, map_pow, map_zpow₀]
        rw [div_pow, div_pow, ← pow_mul, ← pow_mul, mul_comm M m, inv_div, div_mul_div_comm,
          mul_comm ((φ π ^ n) ^ M), mul_div_mul_right _ _ (pow_ne_zero _ hP)]
      rw [he]
      exact (R x).mul_mem ((R x).pow_mem h2 M) hβ2

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Flat.DegCurve

namespace GlobalTheory.CompanionTheory.Ar.Flat.StepIdeal

theorem exists_colength_one (k A : Type) [Field k] [CommRing A] [Algebra k A] [Finite A]
    (χ : A →ₐ[k] k) (e : A) (J : Ideal A) (he : IsIdempotentElem e) (hχ : χ e = 1)
    (hnil : ∀ t ∈ RingHom.ker χ, IsNilpotent (e * t)) (hJe : J ≤ Ideal.span {e}) (hJ0 : J ≠ ⊥) :
    ∃ (J₁ : Ideal A) (t : A) (l : A →ₗ[k] k), J₁ < J ∧ t ∈ J ∧
      (∀ a ∈ J, ∃ c : k, a - algebraMap k A c * t ∈ J₁) ∧
      (∀ a ∈ RingHom.ker χ, a * t ∈ J₁) ∧ (∀ a ∈ J₁, l a = 0) ∧ l t = 1 := by
  classical
  set m := RingHom.ker χ with hm
  have hfix : ∀ a ∈ J, e * a = a := by
    intro a ha
    obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton'.mp (hJe ha)
    calc e * (x * e) = x * (e * e) := by ring
      _ = x * e := by rw [he.eq]
  have hJ : ¬ J ≤ m * J := by
    intro hle
    have hfg : (J : Submodule A A).FG := IsNoetherian.noetherian J
    obtain ⟨r, hr, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m
      (J : Submodule A A) hfg (by rwa [Ideal.smul_eq_mul])
    apply hJ0
    rw [eq_bot_iff]
    intro a ha
    have hs : 1 - r ∈ m := by
      have := m.neg_mem hr
      rwa [neg_sub] at this
    have hsa : (1 - r) * a = a := by
      have h0 : r * a = 0 := by simpa [smul_eq_mul] using hr0 a ha
      rw [sub_mul, one_mul, h0, sub_zero]
    have hpow : ∀ n : ℕ, (e * (1 - r)) ^ n * a = a := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        calc (e * (1 - r)) ^ (n + 1) * a = (e * (1 - r)) ^ n * (e * ((1 - r) * a)) := by ring
          _ = a := by rw [hsa, hfix a ha, ih]
    obtain ⟨n, hn⟩ := hnil (1 - r) hs
    rw [Ideal.mem_bot, ← hpow n, hn, zero_mul]
  obtain ⟨t, htJ, htW⟩ := SetLike.not_le_iff_exists.mp hJ
  let W : Submodule k A := (m * J).restrictScalars k
  have hq : W.mkQ t ≠ 0 := by
    rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact htW
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual k (A ⧸ W), φ (W.mkQ t) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hq ((Module.forall_dual_apply_eq_zero_iff k _).mp hcon)
  set l : A →ₗ[k] k := (φ (W.mkQ t))⁻¹ • (φ ∘ₗ W.mkQ) with hl
  have hlt : l t = 1 := by
    rw [hl, LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul, inv_mul_cancel₀ hφ]
  have hlW : ∀ a ∈ m * J, l a = 0 := by
    intro a ha
    have : W.mkQ a = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ha
    rw [hl, LinearMap.smul_apply, LinearMap.comp_apply, this, map_zero, smul_zero]
  have hdec : ∀ r : A, r - algebraMap k A (χ r) ∈ m := by
    intro r
    rw [hm, RingHom.mem_ker]
    simp
  let J₁ : Ideal A :=
    { carrier := {a | a ∈ J ∧ l a = 0}
      add_mem' := fun {a b} ha hb => ⟨J.add_mem ha.1 hb.1, by rw [map_add (f := _), ha.2, hb.2, add_zero]⟩
      zero_mem' := ⟨J.zero_mem, map_zero l⟩
      smul_mem' := fun c a ha => by
        refine ⟨J.mul_mem_left c ha.1, ?_⟩
        have hsplit : c * a = χ c • a + (c - algebraMap k A (χ c)) * a := by
          rw [Algebra.smul_def]
          ring
        change l (c * a) = 0
        rw [hsplit, map_add (f := _), map_smul, ha.2, smul_zero, zero_add]
        exact hlW _ (Ideal.mul_mem_mul (hdec c) ha.1) }
  have hmemJ₁ : ∀ a, a ∈ J₁ ↔ a ∈ J ∧ l a = 0 := fun a => Iff.rfl
  refine ⟨J₁, t, l, ?_, htJ, ?_, ?_, ?_, hlt⟩
  · rw [SetLike.lt_iff_le_and_exists]
    refine ⟨fun a ha => ((hmemJ₁ a).mp ha).1, t, htJ, fun h => ?_⟩
    have := ((hmemJ₁ t).mp h).2
    rw [hlt] at this
    exact one_ne_zero this
  · intro a ha
    refine ⟨l a, (hmemJ₁ _).mpr ⟨J.sub_mem ha (J.mul_mem_left _ htJ), ?_⟩⟩
    rw [← Algebra.smul_def, map_sub, map_smul, hlt, smul_eq_mul, mul_one, sub_self]
  · intro a ha
    exact (hmemJ₁ _).mpr ⟨J.mul_mem_left a htJ, hlW _ (Ideal.mul_mem_mul ha htJ)⟩
  · intro a ha
    exact ((hmemJ₁ a).mp ha).2

end GlobalTheory.CompanionTheory.Ar.Flat.StepIdeal
end

section

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem primRoot_sub_one_pow_associated {O : Type*} [CommRing O] [IsDomain O] {p : ℕ}
    (hp : p.Prime) {ζ : O} (hζ : IsPrimitiveRoot ζ p) :
    Associated ((ζ - 1) ^ (p - 1)) (p : O) := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  have h := hζ.prod_one_sub_pow_eq_order
  have h2 : Associated (∏ _k ∈ Finset.range n, (ζ - 1)) (∏ k ∈ Finset.range n, (1 - ζ ^ (k + 1))) := by
    refine Associated.prod _ _ _ fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    have hc : (k + 1).Coprime (n + 1) :=
      (Nat.coprime_of_lt_prime (by omega) (by omega) hp).symm
    have := hζ.associated_sub_one_pow_sub_one_of_coprime hc
    rw [← neg_sub (ζ ^ (k + 1)) 1]
    exact this.neg_right
  rw [h, Finset.prod_const, Finset.card_range] at h2
  simpa using h2

end GlobalTheory.CompanionTheory.Ar.HT
end
