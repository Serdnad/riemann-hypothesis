module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Algebra.Module.ZLattice.Summable
public import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.RingTheory.LocalRing.Module

@[expose] public section

section

open NumberField

namespace GlobalTheory

open Submodule

theorem torsion_pow_card_succ {R : Type} [CommRing R] [IsDedekindDomain R]
    (M : Type) [AddCommGroup M] [Module R M] (w0 : Ideal R) (hmax : w0.IsMaximal) (hne : w0 ≠ ⊥)
    (hdiv : ∀ c : R, c ≠ 0 → Function.Surjective (fun g : M => c • g)) (j : ℕ) :
    Nat.card (torsionBySet R M ((w0 ^ (j + 1) : Ideal R) : Set R)) =
      Nat.card (torsionBySet R M ((w0 ^ j : Ideal R) : Set R)) *
        Nat.card (torsionBySet R M ((w0 : Ideal R) : Set R)) := by
  have hlt : w0 ^ 2 < w0 := by simpa using Ideal.pow_succ_lt_pow hne 1
  obtain ⟨c0, hc0, hc02⟩ := SetLike.exists_of_lt hlt
  have hdvd : w0 ∣ Ideal.span {c0} := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hc0)
  obtain ⟨b, hb⟩ := hdvd
  have hbw : ¬ b ≤ w0 := by
    intro hle
    apply hc02
    have : Ideal.span {c0} ≤ w0 ^ 2 := by rw [hb, pow_two]; exact Ideal.mul_mono_right hle
    exact this (Ideal.subset_span rfl)
  have hbtop : b ⊔ w0 = ⊤ := by
    by_contra h
    exact hbw (le_sup_left.trans (hmax.eq_of_le h le_sup_right).symm.le)
  have hcop : ∀ n : ℕ, b ⊔ w0 ^ n = ⊤ := by
    intro n
    rw [← Ideal.isCoprime_iff_sup_eq]
    exact (Ideal.isCoprime_iff_sup_eq.mpr hbtop).pow_right
  have hc0ne : c0 ≠ 0 := by rintro rfl; exact hc02 (zero_mem _)

  let Tj := torsionBySet R M ((w0 ^ j : Ideal R) : Set R)
  let Tj1 := torsionBySet R M ((w0 ^ (j + 1) : Ideal R) : Set R)
  let T1 := torsionBySet R M ((w0 : Ideal R) : Set R)
  have hmapsto : ∀ x ∈ Tj1, c0 • x ∈ Tj := by
    intro x hx
    rw [mem_torsionBySet_iff] at hx ⊢
    rintro ⟨a, ha⟩
    have : a * c0 ∈ w0 ^ (j + 1) := by rw [pow_succ]; exact Ideal.mul_mem_mul ha hc0
    simpa [smul_smul] using hx ⟨_, this⟩
  let φ : Tj1 →ₗ[R] Tj :=
    { toFun := fun x => ⟨c0 • (x : M), hmapsto x x.2⟩
      map_add' := fun x y => by ext; simp
      map_smul' := fun r x => by ext; simp [smul_comm c0 r] }
  have hsurj : Function.Surjective φ := by
    rintro ⟨g, hg⟩
    obtain ⟨g', hg'⟩ := hdiv c0 hc0ne g
    simp only at hg'
    have h1 : (1 : R) ∈ b ⊔ w0 ^ (j + 1) := by rw [hcop]; trivial
    obtain ⟨v, hv, u, hu, huv⟩ := Submodule.mem_sup.mp h1
    have hmem : v • g' ∈ Tj1 := by
      rw [mem_torsionBySet_iff]
      rintro ⟨a, ha⟩
      have hav : a * v ∈ w0 ^ j * Ideal.span {c0} := by
        rw [hb, ← mul_assoc, ← pow_succ]
        exact Ideal.mul_mem_mul ha hv
      obtain ⟨z, hz, hzc⟩ := (Submodule.mem_mul_span_singleton).mp hav
      simp only
      rw [smul_smul, ← hzc, ← smul_smul, hg']
      exact (mem_torsionBySet_iff _ _).mp hg ⟨z, hz⟩
    refine ⟨⟨v • g', hmem⟩, ?_⟩
    ext
    simp only [φ, LinearMap.coe_mk, AddHom.coe_mk]
    rw [smul_comm, hg']
    have hug : u • g = 0 := by
      have : u ∈ w0 ^ j := Ideal.pow_le_pow_right (Nat.le_succ j) hu
      exact (mem_torsionBySet_iff _ _).mp hg ⟨u, this⟩
    have : v = 1 - u := by rw [← huv]; ring
    rw [this, sub_smul, one_smul, hug, sub_zero]
  have hsub : T1 ≤ Tj1 := torsionBySet_le_torsionBySet_of_subset (by
    intro a ha
    exact Ideal.pow_le_self (Nat.succ_ne_zero j) ha)
  have hker : ∀ x : Tj1, x ∈ LinearMap.ker φ ↔ (x : M) ∈ T1 := by
    intro x
    rw [LinearMap.mem_ker]
    constructor
    · intro hx
      have hx' : c0 • (x : M) = 0 := by
        have := congrArg Subtype.val hx
        simpa [φ] using this
      rw [mem_torsionBySet_iff]
      rintro ⟨a, ha⟩
      have hw : w0 ≤ Ideal.span {c0} ⊔ w0 ^ (j + 1) := by
        have e : w0 * (b ⊔ w0 ^ j) = Ideal.span {c0} ⊔ w0 ^ (j + 1) := by
          rw [Ideal.mul_sup, ← hb, ← pow_succ']
        rw [hcop, Ideal.mul_top] at e
        exact e.le
      obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp (hw ha)
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hs
      have key : (r * c0 + t) • (x : M) = 0 := by
        rw [add_smul, mul_smul, hx', smul_zero, zero_add]
        exact (mem_torsionBySet_iff _ _).mp x.2 ⟨t, ht⟩
      rwa [hst] at key
    · intro hx
      ext
      simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, ZeroMemClass.coe_zero]
      exact (mem_torsionBySet_iff _ _).mp hx ⟨c0, hc0⟩
  have e1 : Nat.card (Tj1 ⧸ LinearMap.ker φ) = Nat.card Tj :=
    Nat.card_congr (φ.quotKerEquivOfSurjective hsurj).toEquiv
  have e2 : Nat.card (LinearMap.ker φ) = Nat.card T1 :=
    Nat.card_congr
      { toFun := fun x => ⟨(x.1 : M), (hker x.1).mp x.2⟩
        invFun := fun y => ⟨⟨y.1, hsub y.2⟩, (hker _).mpr y.2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker φ), e1, e2, mul_comm]

theorem torsion_pow_card (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M]
    [Module (𝓞 F) M] (w0 : Ideal (𝓞 F)) (h : ℕ) :
    w0.IsMaximal → w0 ≠ ⊥ → (∀ c : 𝓞 F, c ≠ 0 → Function.Surjective (fun g : M => c • g)) →
    Nat.card (Submodule.torsionBySet (𝓞 F) M (w0 : Set (𝓞 F))) = Nat.card (𝓞 F ⧸ w0) ^ h →
    ∀ j : ℕ, Nat.card (Submodule.torsionBySet (𝓞 F) M ((w0 ^ j : Ideal (𝓞 F)) : Set (𝓞 F))) =
      Nat.card (𝓞 F ⧸ w0) ^ (j * h) := by
  intro hmax hne hdiv h1 j
  induction j with
  | zero =>
    simp only [pow_zero, zero_mul]
    have : torsionBySet (𝓞 F) M ((⊤ : Ideal (𝓞 F)) : Set (𝓞 F)) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [mem_torsionBySet_iff] at hx
      simpa using hx ⟨1, trivial⟩
    rw [Ideal.one_eq_top, this]
    simp
  | succ n ih =>
    rw [torsion_pow_card_succ M w0 hmax hne hdiv n, ih, h1, ← pow_add]
    ring_nf

end GlobalTheory
end

section

open TensorProduct LinearMap Function

namespace GlobalTheory.NilpotentFlat

theorem rTensor_lTensor_apply {R : Type} [CommRing R] {M M' A A' : Type} [AddCommGroup M]
    [Module R M] [AddCommGroup M'] [Module R M'] [AddCommGroup A] [Module R A] [AddCommGroup A']
    [Module R A'] (g : M →ₗ[R] M') (f : A →ₗ[R] A') (x : M ⊗[R] A) :
    rTensor A' g (lTensor M f x) = lTensor M' f (rTensor A g x) := by
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, rTensor_comp_lTensor, lTensor_comp_rTensor]

theorem rTensor_injective_of_flat_baseChange {A C M N' N : Type} [CommRing A] [CommRing C]
    [Algebra A C] [AddCommGroup M] [Module A M] [Module.Flat C (C ⊗[A] M)]
    [AddCommGroup N'] [AddCommGroup N] [Module C N'] [Module C N] [Module A N'] [Module A N]
    [IsScalarTower A C N'] [IsScalarTower A C N] (ι : N' →ₗ[C] N) (hι : Injective ι) :
    Injective ((ι.restrictScalars A).rTensor M) := by
  let e' := AlgebraTensorModule.cancelBaseChange A C C N' M
  let e := AlgebraTensorModule.cancelBaseChange A C C N M
  have h1 : Injective (ι.rTensor (C ⊗[A] M)) :=
    Module.Flat.rTensor_preserves_injective_linearMap ι hι
  have key : ∀ z, (ι.restrictScalars A).rTensor M (e' z) = e (ι.rTensor (C ⊗[A] M) z) := by
    intro z
    induction z with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul n t =>
      induction t with
      | add a b ha hb => simp only [tmul_add, map_add (f := _), ha, hb]
      | tmul c b => simp [e, e']
  intro x y h
  obtain ⟨x, rfl⟩ := e'.surjective x
  obtain ⟨y, rfl⟩ := e'.surjective y
  rw [key, key] at h
  rw [h1 (e.injective h)]

theorem lTensor_injective_of_flat {A C F N' N : Type} [CommRing A] [CommRing C] [Algebra A C]
    [AddCommGroup F] [Module A F] [Module C F] [IsScalarTower A C F] [Module.Flat C F]
    [AddCommGroup N'] [AddCommGroup N] [Module A N'] [Module A N] (ι : N' →ₗ[A] N)
    (hι : Injective (ι.rTensor C)) : Injective (ι.lTensor F) := by
  let e' := AlgebraTensorModule.cancelBaseChange A C C F N'
  let e := AlgebraTensorModule.cancelBaseChange A C C F N
  have hι' : Injective (ι.baseChange C) := (LinearMap.lTensor_inj_iff_rTensor_inj (M := C) ι).mpr hι
  have h1 : Injective ((ι.baseChange C).lTensor F) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hι'
  have key : ∀ z, ι.lTensor F (e' z) = e ((ι.baseChange C).lTensor F z) := by
    intro z
    induction z with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul n t =>
      induction t with
      | add a b ha hb => simp only [tmul_add, map_add (f := _), ha, hb]
      | tmul c b => simp [e, e']
  intro x y h
  obtain ⟨x, rfl⟩ := e'.surjective x
  obtain ⟨y, rfl⟩ := e'.surjective y
  rw [key, key] at h
  rw [h1 (e.injective h)]

variable {B : Type} [CommRing B]

theorem rTensor_injective_of_extension {K L : Type} [AddCommGroup K] [Module B K]
    [AddCommGroup L] [Module B L] [Module.Flat B L] (i : K →ₗ[B] L)
    {N₁ N₂ N₃ : Type} [AddCommGroup N₁] [Module B N₁] [AddCommGroup N₂] [Module B N₂]
    [AddCommGroup N₃] [Module B N₃] (g₁ : N₁ →ₗ[B] N₂) (g₂ : N₂ →ₗ[B] N₃)
    (hg : Exact g₁ g₂) (hg₁ : Injective g₁) (hg₂ : Surjective g₂)
    (h₁ : Injective (i.rTensor N₁)) (h₃ : Injective (i.rTensor N₃)) :
    Injective (i.rTensor N₂) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have h2 : g₂.lTensor K x = 0 := by
    apply (injective_iff_map_eq_zero _).mp h₃
    rw [rTensor_lTensor_apply, hx, map_zero]
  obtain ⟨x₁, rfl⟩ := (lTensor_exact K hg hg₂ x).mp h2
  have h4 : i.rTensor N₁ x₁ = 0 := by
    apply (injective_iff_map_eq_zero _).mp
      (Module.Flat.lTensor_preserves_injective_linearMap (M := L) g₁ hg₁)
    rw [← rTensor_lTensor_apply, hx]
  simp [(injective_iff_map_eq_zero _).mp h₁ _ h4]

theorem rTensor_injective_quotient (I : Ideal B) {K L M : Type} [AddCommGroup K] [Module B K]
    [AddCommGroup L] [Module B L] [AddCommGroup M] [Module B M] (i : K →ₗ[B] L) (π : L →ₗ[B] M)
    (hi : Injective i) (hex : Exact i π) (hπ : Surjective π)
    (hIM : Injective (I.subtype.rTensor M)) : Injective (i.rTensor (B ⧸ I)) := by
  have h := lTensor_injective_of_exact_of_exact_of_rTensor_injective
    (LinearMap.exact_subtype_mkQ I) (Submodule.mkQ_surjective I) hex hπ hIM
    (Module.Flat.lTensor_preserves_injective_linearMap (M := B) i hi)
  exact (lTensor_inj_iff_rTensor_inj (B ⧸ I) i).mp h

theorem rTensor_injective_of_quotient_module (I : Ideal B) {K L M : Type} [AddCommGroup K]
    [Module B K] [AddCommGroup L] [Module B L] [AddCommGroup M] [Module B M] (i : K →ₗ[B] L)
    (π : L →ₗ[B] M) (hex : Exact i π) (hπ : Surjective π)
    [Module.Flat (B ⧸ I) ((B ⧸ I) ⊗[B] M)] (hI : Injective (i.rTensor (B ⧸ I)))
    (N : Type) [AddCommGroup N] [Module (B ⧸ I) N] [Module B N] [IsScalarTower B (B ⧸ I) N] :
    Injective (i.rTensor N) := by
  let p : (N →₀ (B ⧸ I)) →ₗ[B ⧸ I] N := Finsupp.linearCombination (B ⧸ I) id
  have hp : Surjective p := fun n => ⟨Finsupp.single n 1, by simp [p]⟩
  have h := lTensor_injective_of_exact_of_exact_of_rTensor_injective
    (f₁ := (LinearMap.ker p).subtype.restrictScalars B) (f₂ := p.restrictScalars B)
    (LinearMap.exact_subtype_ker_map p) hp hex hπ
    (rTensor_injective_of_flat_baseChange (LinearMap.ker p).subtype (Submodule.injective_subtype _))
    (lTensor_injective_of_flat (C := B ⧸ I) (F := N →₀ (B ⧸ I)) i hI)
  exact (lTensor_inj_iff_rTensor_inj N i).mp h

theorem rTensor_injective_of_pow_smul_eq_bot (I : Ideal B) {K L : Type} [AddCommGroup K]
    [Module B K] [AddCommGroup L] [Module B L] [Module.Flat B L] (i : K →ₗ[B] L)
    (hbase : ∀ (N : Type) [AddCommGroup N] [Module (B ⧸ I) N] [Module B N]
      [IsScalarTower B (B ⧸ I) N], Injective (i.rTensor N)) (n : ℕ) :
    ∀ (N : Type) [AddCommGroup N] [Module B N], (I ^ n • ⊤ : Submodule B N) = ⊥ →
      Injective (i.rTensor N) := by
  induction n with
  | zero =>
    intro N _ _ hN
    have h0 : ∀ x : N, x = 0 := fun x => by
      have hx : x ∈ (I ^ 0 • ⊤ : Submodule B N) := by
        rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]; trivial
      rw [hN] at hx
      simpa using hx
    have hz : ∀ z : K ⊗[B] N, z = 0 := fun z => by
      induction z with
      | tmul k x => rw [h0 x, tmul_zero]
      | add a b ha hb => rw [ha, hb, add_zero]
    intro a b _
    rw [hz a, hz b]
  | succ n ih =>
    intro N _ _ hN
    let S : Submodule B N := I • ⊤
    refine rTensor_injective_of_extension i S.subtype S.mkQ (LinearMap.exact_subtype_mkQ S)
      S.injective_subtype (Submodule.mkQ_surjective S) (ih S ?_) (hbase (N ⧸ S))
    apply Submodule.map_injective_of_injective S.injective_subtype
    rw [Submodule.map_smul'', Submodule.map_bot, Submodule.map_subtype_top, ← Submodule.mul_smul,
      ← pow_succ, hN]

theorem flat_of_isNilpotent : ∀ (B : Type) [CommRing B] (I : Ideal B), IsNilpotent I →
    ∀ (M : Type) [AddCommGroup M] [Module B M],
      Module.Flat (B ⧸ I) (M ⧸ (I • ⊤ : Submodule B M)) →
      Function.Injective (TensorProduct.lift ((LinearMap.lsmul B M).comp I.subtype)) →
      Module.Flat B M := by
  intro B _ I hI M _ _ hflat hinj
  obtain ⟨n, hn⟩ := hI
  let π : (M →₀ B) →ₗ[B] M := Finsupp.linearCombination B id
  have hπ : Surjective π := fun m => ⟨Finsupp.single m 1, by simp [π]⟩
  let K := LinearMap.ker π
  have hex : Exact K.subtype π := LinearMap.exact_subtype_ker_map π
  have hIM : Injective (I.subtype.rTensor M) := by
    have e : TensorProduct.lift ((LinearMap.lsmul B M).comp I.subtype) =
        (TensorProduct.lid B M).toLinearMap ∘ₗ I.subtype.rTensor M := by
      ext a m
      simp
    rw [e, LinearMap.coe_comp] at hinj
    exact hinj.of_comp
  let e : ((B ⧸ I) ⊗[B] M) ≃ₗ[B ⧸ I] (M ⧸ (I • ⊤ : Submodule B M)) :=
    (TensorProduct.quotTensorEquivQuotSMul M I).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  haveI : Module.Flat (B ⧸ I) ((B ⧸ I) ⊗[B] M) := Module.Flat.of_linearEquiv e
  have hq := rTensor_injective_quotient I K.subtype π K.injective_subtype hex hπ hIM
  have hall := rTensor_injective_of_pow_smul_eq_bot I K.subtype
    (rTensor_injective_of_quotient_module I K.subtype π hex hπ hq) n
  rw [Module.Flat.iff_lTensor_injective']
  intro J
  refine lTensor_injective_of_exact_of_exact_of_rTensor_injective hex hπ
    (LinearMap.exact_subtype_mkQ J) (Submodule.mkQ_surjective J) (hall (B ⧸ J) ?_)
    (Module.Flat.lTensor_preserves_injective_linearMap _ J.injective_subtype)
  rw [hn, Submodule.zero_eq_bot, Submodule.bot_smul]

end GlobalTheory.NilpotentFlat
end

section

open SchwartzMap

noncomputable section

namespace GlobalTheory.SchwartzTranslateSum

theorem summable_one_add_norm_inv_pow' {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] {N : ℕ}
    (hN : Module.finrank ℤ Λ < N) : Summable fun z : Λ => ((1 + ‖z‖)⁻¹) ^ N := by
  classical
  refine Summable.of_nonneg_of_le (fun z => by positivity) (fun z => ?_)
    ((ZLattice.summable_norm_pow_inv Λ N hN).add (hasSum_ite_eq (0 : Λ) (1 : ℝ)).summable)
  by_cases hz : z = 0
  · subst hz
    simp
  · have h0 : 0 < ‖z‖ := norm_pos_iff.2 hz
    simp only [hz, if_false, add_zero]
    gcongr
    linarith

theorem summable_seminorm_mul_translate {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (h f : SchwartzMap V ℂ) (hh : HasCompactSupport h)
    (u : Λ → SchwartzMap V ℂ) (hu : ∀ (l : Λ) (x : V), u l x = h (x + l) * f x) (k n : ℕ) :
    Summable (fun l => SchwartzMap.seminorm ℂ k n (u l)) := by
  obtain ⟨R, hR⟩ := hh.isCompact.isBounded.subset_closedBall (0 : V)
  set N := Module.finrank ℤ Λ + 1 with hNdef
  have hw : Summable fun l : Λ => ((1 + ‖l‖)⁻¹) ^ N :=
    summable_one_add_norm_inv_pow' Λ (Nat.lt_succ_self _)
  set S := (Finset.Iic (k + N, n)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℂ m.1 m.2) f
    with hSdef
  set A := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 i h
    with hAdef
  set R' := max R 0 with hR'def
  have hR'0 : 0 ≤ R' := le_max_right _ _
  set D := (1 + R') ^ N * 2 ^ (k + N) * S with hDdef
  have hS0 : 0 ≤ S := apply_nonneg _ _
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => by positivity
  have hD0 : 0 ≤ D := by positivity
  clear_value D A S R' N
  refine (hw.mul_left (A * D)).of_nonneg_of_le (fun l => apply_nonneg _ _) (fun l => ?_)
  refine SchwartzMap.seminorm_le_bound ℂ k n (u l) (by positivity) (fun x => ?_)
  have hfun : (u l : V → ℂ) = fun y => h (y + l) * f y := funext (hu l)
  rw [hfun]
  have hsh : ContDiff ℝ n (fun y => h (y + (l : V))) :=
    ((h.smooth ⊤).of_le (by exact_mod_cast le_top)).comp (contDiff_id.add contDiff_const)
  have hsf : ContDiff ℝ n (f : V → ℂ) := (f.smooth ⊤).of_le (by exact_mod_cast le_top)
  have hleib := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) hsh hsf x (n := n) le_rfl
  simp_rw [iteratedFDeriv_comp_add_right] at hleib
  by_cases hx : x + (l : V) ∈ tsupport h
  · have hxl : ‖x + (l : V)‖ ≤ R' := by
      have := hR hx
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact this.trans (hR'def ▸ le_max_left _ _)
    have hl : 1 + ‖l‖ ≤ (1 + R') * (1 + ‖x‖) := by
      have : ‖(l : V)‖ ≤ ‖x + (l : V)‖ + ‖x‖ := by
        calc ‖(l : V)‖ = ‖(x + (l : V)) - x‖ := by simp
          _ ≤ ‖x + (l : V)‖ + ‖x‖ := norm_sub_le _ _
      have hn' : ‖l‖ = ‖(l : V)‖ := rfl
      nlinarith [norm_nonneg x]
    have hB : ∀ m ≤ n, ‖x‖ ^ k * ‖iteratedFDeriv ℝ m f x‖ ≤ D * ((1 + ‖l‖)⁻¹) ^ N := by
      intro m hm
      have h1 := one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k + N, n)) (k := k + N) (n := m)
        le_rfl hm f x
      have h1' : (1 + ‖x‖) ^ (k + N) * ‖iteratedFDeriv ℝ m f x‖ ≤ 2 ^ (k + N) * S := by rw [hSdef]; exact h1
      have hpos : 0 < (1 + ‖l‖) ^ N := by positivity
      rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ hpos]
      calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ m f x‖ * (1 + ‖l‖) ^ N
          ≤ (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ m f x‖ * ((1 + R') * (1 + ‖x‖)) ^ N := by
            gcongr
            linarith [norm_nonneg x]
        _ = (1 + R') ^ N * ((1 + ‖x‖) ^ (k + N) * ‖iteratedFDeriv ℝ m f x‖) := by
            rw [mul_pow, pow_add]; ring
        _ ≤ (1 + R') ^ N * (2 ^ (k + N) * S) := by gcongr
        _ = D := by rw [hDdef]; ring
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => h (y + (l : V)) * f y) x‖
        ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i h (x + l)‖ * ‖iteratedFDeriv ℝ (n - i) f x‖ := by gcongr
      _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i h (x + l)‖ *
            (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f x‖) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 i h *
            (D * ((1 + ‖l‖)⁻¹) ^ N) := by
            refine Finset.sum_le_sum fun i _ => ?_
            exact mul_le_mul (mul_le_mul_of_nonneg_left
              (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ h i _) (by positivity))
              (hB _ (Nat.sub_le _ _)) (by positivity) (by positivity)
      _ = A * D * ((1 + ‖l‖)⁻¹) ^ N := by
            rw [hAdef, Finset.sum_mul, Finset.sum_mul]
            exact Finset.sum_congr rfl fun i _ => by ring
  · have hz : ∀ i, iteratedFDeriv ℝ i h (x + l) = 0 := fun i =>
      Function.notMem_support.1 fun hm => hx (support_iteratedFDeriv_subset i hm)
    simp only [hz, norm_zero, mul_zero, zero_mul, Finset.sum_const_zero] at hleib
    have : ‖iteratedFDeriv ℝ n (fun y => h (y + (l : V)) * f y) x‖ = 0 :=
      le_antisymm hleib (norm_nonneg _)
    rw [this, mul_zero]
    exact mul_nonneg (mul_nonneg hA0 hD0) (by positivity)

end GlobalTheory.SchwartzTranslateSum
end
end

section

set_option autoImplicit false

open NumberField MvPolynomial

noncomputable section

namespace GlobalTheory.SZShift

theorem totalDegree_aeval_le_of_deg_le_one {σ τ F E : Type} [CommRing F] [CommRing E] [Algebra F E]
    (g : σ → MvPolynomial τ E) (hg : ∀ i, (g i).totalDegree ≤ 1) (P : MvPolynomial σ F) :
    (aeval g P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum]

  rw [map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun d hd => ?_)
  rw [aeval_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.algebraMap_apply, totalDegree_C, zero_add, Finsupp.prod]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hd)
  rw [Finsupp.sum]
  refine Finset.sum_le_sum fun i _ => ?_
  exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (d i) (hg i))

end GlobalTheory.SZShift
end
end
