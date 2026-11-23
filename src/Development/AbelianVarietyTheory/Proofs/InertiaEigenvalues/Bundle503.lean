module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlternatingDifferenceTermWindow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle103
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle148
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle496
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle190
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle006
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle003
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle164
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle491
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineIffMemH1f
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle501
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle363
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle492
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle007
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.SplitRowIffOfIsEmpty
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle411
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle403
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle478
import Formalism.LocalRingCardinality.Bundle002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
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
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe

@[expose] public section

section

noncomputable section

namespace GlobalTheory.UnitLemma.Desc

open GlobalTheory.UnitLemma Polynomial

theorem exists_isIntegral_pow_smul : ∀ (K : UQ) (B : InvAlg K) (a : K.O), K.Small a → ∀ x : B.A,
    ∃ k : ℕ, IsIntegral K.O ((al K a ^ k) • x) := GlobalTheory.T.exists_isIntegral_smallElement_pow_smul

theorem isIntegral_or_of_fieldFactor : ∀ (K : UQ) (B : InvAlg K) (f y z : B.A), IsIdempotentElem f →
    (∀ w, f * w ≠ 0 → ∃ v, f * w * v = f) → f * y * z = f →
    IsIntegral K.O (f * y) ∨ IsIntegral K.O (f * z) := GlobalTheory.T.isIntegral_or_isIntegral_inv_in_fieldFactor

theorem exists_pow_smul_mem_adjoin_g : ∀ (K : UQ) (B : InvAlg K) (a : K.O), B.P.Separable → K.Small a →
    ∃ N : ℕ, ∀ r : B.A, IsIntegral K.O r → (al K a ^ N) • r ∈ Algebra.adjoin K.O {B.g} := GlobalTheory.T.exists_pow_smul_mem_adjoin_gen_of_separable

variable {K : UQ} (B : InvAlg K)

theorem al_ne (a : K.O) (ha : K.Small a) : al K a ≠ 0 := by
  intro h
  exact ha.1 ((IsFractionRing.injective K.O K.E) (by simpa using h))

theorem sigma_smul (c : K.E) (x : B.A) : B.σ (c • x) = K.c c • B.σ x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, B.σ_alg]

theorem isIntegral_idem {f : B.A} (hf : IsIdempotentElem f) : IsIntegral K.O f :=
  ⟨X ^ 2 - X, by
    have : (X ^ 2 - X : K.O[X]) = X ^ 2 - C 1 * X ^ 1 := by simp
    rw [this]; exact monic_X_pow_sub (by simp), by simp [sq, hf.eq]⟩

theorem isIntegral_pow_smul (a : K.O) (n : ℕ) {x : B.A} (hx : IsIntegral K.O x) :
    IsIntegral K.O ((al K a ^ n) • x) := by
  have : (al K a ^ n) • x = algebraMap K.O B.A (a ^ n) * x := by
    simp only [al, Algebra.smul_def, IsScalarTower.algebraMap_apply K.O K.E B.A, map_pow]
  rw [this]; exact isIntegral_algebraMap.mul hx

theorem not_isIntegral_inv_smul (a : K.O) (ha : K.Small a) {f : B.A} (hf : IsIdempotentElem f)
    (hf0 : f ≠ 0) : ¬ IsIntegral K.O ((al K a ^ (-1 : ℤ)) • f) := by
  apply GlobalTheory.UnitLemma.Desc.Window.not_isIntegral_inv_smul_idem <;> assumption

theorem smul_mem_of_adjoin (M : Submodule K.O B.A) (hM : ∀ y ∈ M, B.g * y ∈ M) {s : B.A}
    (hs : s ∈ Algebra.adjoin K.O {B.g}) : ∀ m ∈ M, s * m ∈ M := by
  let T : Subalgebra K.O B.A :=
    { carrier := {s | ∀ m ∈ M, s * m ∈ M}
      mul_mem' := fun {x y} hx hy m hm => by rw [mul_assoc]; exact hx _ (hy m hm)
      one_mem' := fun m hm => by rw [one_mul]; exact hm
      add_mem' := fun {x y} hx hy m hm => by rw [add_mul]; exact M.add_mem (hx m hm) (hy m hm)
      zero_mem' := fun m hm => by rw [zero_mul]; exact M.zero_mem
      algebraMap_mem' := fun c m hm => by rw [← Algebra.smul_def]; exact M.smul_mem c hm }
  have : Algebra.adjoin K.O {B.g} ≤ T := Algebra.adjoin_le (by
    intro x hx; rw [Set.mem_singleton_iff.1 hx]; exact hM)
  exact this hs

theorem exists_pos : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e π : ι → B.A) (S : Finset ι)
    (a : K.O), B.P.Separable → K.Small a → IsFrame B e π S →
    ∃ N : ℕ, ∀ M ∈ B.Lin, ∃ p : ι → ℤ, Pos B a e N M p := by
  intro K B ι _ e π S a hP ha hF
  obtain ⟨N0, hN0⟩ := exists_pow_smul_mem_adjoin_g K B a hP ha
  refine ⟨N0 + 1, fun M hM => ?_⟩
  set t := al K a with ht_def
  have ht : t ≠ 0 := al_ne a ha
  have hct : K.c t = t := ha.2.2
  have hRM : ∀ r : B.A, IsIntegral K.O r → ∀ m ∈ M, (t ^ N0) • (r * m) ∈ M := fun r hr m hm => by
    rw [← smul_mul_assoc]; exact smul_mem_of_adjoin B M hM.2.1 (hN0 r hr) m hm
  have core : ∀ f : B.A, IsIdempotentElem f → (∀ w, f * w ≠ 0 → ∃ v, f * w * v = f) →
      ∀ (q : ℤ) (m : B.A), m ∈ M → ¬ IsIntegral K.O ((t ^ (-q)) • (f * m)) →
      ∀ r : B.A, IsIntegral K.O r → (t ^ (q + N0)) • (f * r) ∈ M := by
    intro f hf hfld q m hm hni r hr
    have hy0 : f * ((t ^ (-q)) • m) ≠ 0 := by
      intro h0; apply hni; rw [← mul_smul_comm, h0]; exact isIntegral_zero
    obtain ⟨z, hz⟩ := hfld _ hy0
    have hfz : IsIntegral K.O (f * z) := by
      rcases isIntegral_or_of_fieldFactor K B f ((t ^ (-q)) • m) z hf hfld hz with h | h
      · exact (hni (by rwa [mul_smul_comm] at h)).elim
      · exact h
    have key : (t ^ (q + N0)) • (f * r) = (t ^ N0) • ((r * (f * z)) * m) := by
      have e1 : f * r = (t ^ (-q)) • ((r * (f * z)) * m) := by
        calc f * r = r * (f * ((t ^ (-q)) • m) * z) := by rw [hz]; ring
          _ = _ := by simp only [Algebra.smul_def]; ring
      rw [e1, smul_smul, ← zpow_add₀ ht, show q + N0 + -q = (N0 : ℤ) by ring, zpow_natCast]
    rw [key]; exact hRM _ (hr.mul hfz) m hm
  have hpos : ∀ i, ∃ pi : ℤ, (∀ r : B.A, IsIntegral K.O r → (t ^ (pi + ↑(N0 + 1))) • (e i * r) ∈ M) ∧
      ∀ m ∈ M, IsIntegral K.O ((t ^ (-pi)) • (e i * m)) := by
    intro i
    obtain ⟨f, hf, hf0, hfld, hS, hnS⟩ := hF.1.2 i
    have hfe : f * e i = f := by
      by_cases hi : i ∈ S
      · rw [(hS hi).1, hf.eq]
      · rw [(hnS hi).2, mul_add, hf.eq, (hnS hi).1, add_zero]
    let P : Set ℤ := {p | ∀ m ∈ M, IsIntegral K.O ((t ^ (-p)) • (e i * m))}
    have hne : P.Nonempty := by
      obtain ⟨s, hs⟩ := hM.1.1
      choose k hk using fun x : B.A => exists_isIntegral_pow_smul K B a ha (e i * x)
      refine ⟨-((s.sup k : ℕ) : ℤ), fun m hm => ?_⟩
      rw [neg_neg, zpow_natCast]
      rw [← hs] at hm
      induction hm using Submodule.span_induction with
      | mem x hx =>
        have hle : k x ≤ s.sup k := Finset.le_sup hx
        rw [← Nat.sub_add_cancel hle, pow_add, ← smul_smul]
        exact isIntegral_pow_smul B a _ (hk x)
      | zero => rw [mul_zero, smul_zero]; exact isIntegral_zero
      | add x y _ _ hx hy => rw [mul_add, smul_add]; exact hx.add hy
      | smul c x _ hx =>
        rw [Algebra.smul_def c x, ← mul_assoc, mul_comm (e i), mul_assoc, ← mul_smul_comm]
        exact isIntegral_algebraMap.mul hx
    have hbdd : BddAbove P := by
      have hm0 : ∃ m ∈ M, f * m ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        have hle : Submodule.span K.E (M : Set B.A) ≤ LinearMap.ker (LinearMap.mulLeft K.E f) := by
          rw [Submodule.span_le]; intro m hm; exact hcon m hm
        rw [hM.1.2] at hle
        have := hle (Submodule.mem_top : (1 : B.A) ∈ ⊤)
        simp at this; exact hf0 this
      obtain ⟨m0, hm0, hfm0⟩ := hm0
      obtain ⟨z, hz⟩ := hfld m0 hfm0
      obtain ⟨k, hk⟩ := exists_isIntegral_pow_smul K B a ha (f * z)
      refine ⟨k, fun p hp => ?_⟩
      by_contra hlt
      push_neg at hlt
      have h1 : IsIntegral K.O ((t ^ (-p)) • (e i * m0)) := hp m0 hm0
      have h2 : IsIntegral K.O ((t ^ (-p)) • (e i * m0) * (t ^ k • (f * z)) * f) :=
        (h1.mul hk).mul (isIntegral_idem B hf)
      have hq : e i * m0 * (f * z) * f = f := by
        calc e i * m0 * (f * z) * f = (f * e i) * m0 * z * f := by ring
          _ = f := by rw [hfe, hz, hf.eq]
      have h3 : (t ^ (-p)) • (e i * m0) * (t ^ k • (f * z)) * f = (t ^ ((k : ℤ) - p)) • f := by
        rw [sub_eq_add_neg, zpow_add₀ ht, zpow_natCast]
        simp only [Algebra.smul_def, map_mul]
        linear_combination (algebraMap K.E B.A (t ^ (-p)) * algebraMap K.E B.A (t ^ k)) * hq
      have h4 : (t ^ (-1 : ℤ)) • f = (t ^ ((p - k - 1 : ℤ).toNat)) • ((t ^ ((k : ℤ) - p)) • f) := by
        rw [smul_smul, ← zpow_natCast, ← zpow_add₀ ht, Int.toNat_of_nonneg (by omega),
          show (p - k - 1 : ℤ) + (k - p) = -1 by ring]
      exact not_isIntegral_inv_smul B a ha hf hf0 (h4 ▸ isIntegral_pow_smul B a _ (h3 ▸ h2))
    obtain ⟨pi, hmem, hnot⟩ : ∃ pi, pi ∈ P ∧ pi + 1 ∉ P :=
      ⟨sSup P, Int.csSup_mem hne hbdd, fun h => by have := le_csSup hbdd h; omega⟩
    refine ⟨pi, fun r hr => ?_, hmem⟩
    have hnot' : ¬ ∀ m ∈ M, IsIntegral K.O ((t ^ (-(pi + 1))) • (e i * m)) := hnot
    push_neg at hnot'
    obtain ⟨m, hm, hni⟩ := hnot'
    have hexp : pi + ↑(N0 + 1) = (pi + 1) + N0 := by push_cast; ring
    rw [hexp]
    by_cases hi : i ∈ S
    · rw [(hS hi).1] at hni ⊢
      exact core f hf hfld (pi + 1) m hm hni r hr
    · obtain ⟨hff, hei⟩ := hnS hi
      have Hf : ∀ r : B.A, IsIntegral K.O r → (t ^ (pi + 1 + N0)) • (f * r) ∈ M := by
        by_cases h1 : IsIntegral K.O ((t ^ (-(pi + 1))) • (f * m))
        · have h2 : ¬ IsIntegral K.O ((t ^ (-(pi + 1))) • (B.σ f * m)) := by
            intro h2; apply hni; rw [hei, add_mul, smul_add]; exact h1.add h2
          have h3 : ¬ IsIntegral K.O ((t ^ (-(pi + 1))) • (f * B.σ m)) := by
            intro h3; apply h2
            have := isIntegral_sigma K B _ h3
            rwa [sigma_smul, map_mul, B.σ_σ, map_zpow₀, hct] at this
          exact core f hf hfld (pi + 1) (B.σ m) (hM.2.2 m hm) h3
        · exact core f hf hfld (pi + 1) m hm h1
      rw [hei, add_mul, smul_add]
      refine M.add_mem (Hf r hr) ?_
      have := hM.2.2 _ (Hf (B.σ r) (isIntegral_sigma K B _ hr))
      rwa [sigma_smul, map_mul, B.σ_σ, map_zpow₀, hct] at this
  choose p hp using hpos
  exact ⟨p, hp⟩

end GlobalTheory.UnitLemma.Desc
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section
namespace GlobalTheory.ClassPet

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem cong_mul {N : ℕ} {a b : GAf L n} (ha : NG.Cong L n N a) (hb : NG.Cong L n N b) :
    NG.Cong L n N (a * b) := by
  apply GlobalTheory.IsotOrth.cong_mul <;> assumption

theorem cong_one (N : ℕ) : NG.Cong L n N (1 : GAf L n) := by
  refine ⟨Subgroup.one_mem _, fun i j => ⟨0, Subring.zero_mem _, ?_⟩⟩
  simp

theorem cong_inv {N : ℕ} {a : GAf L n} (ha : NG.Cong L n N a) : NG.Cong L n N a⁻¹ := by
  apply GlobalTheory.IsotOrth.cong_inv <;> assumption


variable (L n) in
def congSub (N : ℕ) : Subgroup (GAf L n) where
  carrier := {κ | NG.Cong L n N κ}
  mul_mem' := cong_mul
  one_mem' := cong_one N
  inv_mem' := cong_inv

theorem congSub_le_umax (N : ℕ) : congSub L n N ≤ Umax L n := fun _ h => h.1

theorem congSub_mul_le (N M : ℕ) : congSub L n (N * M) ≤ congSub L n N := fun _ h => NG.Cong.of_mul_left L n h

end GlobalTheory.ClassPet

namespace GlobalTheory.ClassPet

section Grp
variable {G : Type*} [Group G]

theorem relIndex_ne_zero_of_cover {H K : Subgroup G} (F : Finset G) (hF : ∀ κ ∈ K, ∃ f ∈ F, f⁻¹ * κ ∈ H)
    (hle : H ≤ K) : H.relIndex K ≠ 0 := by
  classical
  haveI : Finite (K ⧸ H.subgroupOf K) := by
    let φ : F → K ⧸ H.subgroupOf K := fun f =>
      if h : (f : G) ∈ K then ((⟨f, h⟩ : K) : K ⧸ H.subgroupOf K) else ((1 : K) : K ⧸ H.subgroupOf K)
    refine Finite.of_surjective φ (fun q => ?_)
    induction q using QuotientGroup.induction_on with
    | H κ =>
      obtain ⟨f, hf, hfκ⟩ := hF κ κ.2
      have hfK : f ∈ K := by
        have := K.mul_mem κ.2 (K.inv_mem (hle hfκ))
        simpa using this
      refine ⟨⟨f, hf⟩, ?_⟩
      simp only [φ, dif_pos hfK]
      exact QuotientGroup.eq.2 (by simpa [Subgroup.mem_subgroupOf] using hfκ)
  show (H.subgroupOf K).index ≠ 0
  exact Subgroup.index_ne_zero_of_finite

theorem exists_cosetReps {H K : Subgroup G} (hle : H ≤ K) (hne : H.relIndex K ≠ 0) :
    ∃ F : Finset G, (∀ u ∈ F, u ∈ K) ∧ (∀ κ ∈ K, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ H) ∧ F.card = H.relIndex K := by
  classical
  haveI : (H.subgroupOf K).FiniteIndex := ⟨hne⟩
  haveI : Fintype (K ⧸ H.subgroupOf K) := Fintype.ofFinite _
  let o : K ⧸ H.subgroupOf K → G := fun q => ((Quotient.out q : K) : G)
  have ho : Function.Injective o := by
    intro q q' h
    have : Quotient.out q = Quotient.out q' := Subtype.ext h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', this]
  refine ⟨Finset.univ.image o, ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hu
    exact (Quotient.out q).2
  · intro κ hκ
    refine ⟨o ((⟨κ, hκ⟩ : K) : K ⧸ H.subgroupOf K), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, ?_⟩
    · have h := QuotientGroup.eq.1 (QuotientGroup.out_eq' ((⟨κ, hκ⟩ : K) : K ⧸ H.subgroupOf K))
      simpa [Subgroup.mem_subgroupOf, o] using h
    · rintro u ⟨hu, hu'⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hu
      have : q = ((⟨κ, hκ⟩ : K) : K ⧸ H.subgroupOf K) := by
        rw [← QuotientGroup.out_eq' q]
        exact QuotientGroup.eq.2 (by simpa [Subgroup.mem_subgroupOf, o] using hu')
      rw [this]
  · rw [Finset.card_image_of_injective _ ho, Finset.card_univ]
    show _ = (H.subgroupOf K).index
    rw [Subgroup.index, Nat.card_eq_fintype_card]

theorem norm_eq_one_of_relIndex {J K : Subgroup G} (hle : K ≤ J) (hne : K.relIndex J ≠ 0) (χ : J →* ℂˣ)
    (hχ : ∀ κ (h : κ ∈ K), χ ⟨κ, hle h⟩ = 1) (κ : J) : ‖((χ κ : ℂˣ) : ℂ)‖ = 1 := by
  haveI : (K.subgroupOf J).FiniteIndex := ⟨hne⟩
  obtain ⟨i, j, hij, e⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun i : ℕ => ((κ ^ i : J) : J ⧸ K.subgroupOf J))
  have hmem : ((κ ^ i)⁻¹ * κ ^ j : J) ∈ K.subgroupOf J := QuotientGroup.eq.1 e
  have h1 : χ ((κ ^ i)⁻¹ * κ ^ j) = 1 := by
    have := hχ _ (Subgroup.mem_subgroupOf.1 hmem)
    rwa [Subtype.coe_eta] at this
  have h2 : ((χ κ : ℂˣ) : ℂ) ^ i = ((χ κ : ℂˣ) : ℂ) ^ j := by
    rw [map_mul, map_inv, map_pow, map_pow, inv_mul_eq_one] at h1
    have := congrArg (fun u : ℂˣ => (u : ℂ)) h1
    simpa using this
  have h3 : ‖((χ κ : ℂˣ) : ℂ)‖ ^ i = ‖((χ κ : ℂˣ) : ℂ)‖ ^ j := by rw [← norm_pow, ← norm_pow, h2]
  have hpos : 0 < ‖((χ κ : ℂˣ) : ℂ)‖ := norm_pos_iff.2 (Units.ne_zero _)
  by_contra hne1
  exact hij (pow_right_injective₀ hpos hne1 h3)

end Grp

section Sum
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (a : NG.AlgWt L n)
  (β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ) (J : Subgroup (GAf L n)) (T : Finset (GAf L n))

theorem classSum_add_left (f₁ f₂ f' : GAf L n → a.W) :
    classSum a β J T (f₁ + f₂) f' = classSum a β J T f₁ f' + classSum a β J T f₂ f' := by
  simp only [classSum, Pi.add_apply, LinearMap.map_add₂, mul_add, Finset.sum_add_distrib]

theorem classSum_smul_left (c : ℂ) (f f' : GAf L n → a.W) :
    classSum a β J T (c • f) f' = starRingEnd ℂ c * classSum a β J T f f' := by
  simp only [classSum, Pi.smul_apply, LinearMap.map_smulₛₗ₂, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => by ring

theorem classSum_add_right (f f₁ f₂ : GAf L n → a.W) :
    classSum a β J T f (f₁ + f₂) = classSum a β J T f f₁ + classSum a β J T f f₂ := by
  simp only [classSum, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem classSum_smul_right (c : ℂ) (f f' : GAf L n → a.W) :
    classSum a β J T f (c • f') = c * classSum a β J T f f' := by
  simp only [classSum, Pi.smul_apply, map_smul, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => by ring

theorem classSum_conj (hβ : IsInvForm a β) (f f' : GAf L n → a.W) :
    classSum a β J T f' f = starRingEnd ℂ (classSum a β J T f f') := by

  simp only [classSum, map_sum, map_mul, map_inv₀, map_natCast]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hβ.1 (f' t) (f t)]

end Sum

end GlobalTheory.ClassPet
end
end

section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions

namespace GlobalTheory.FontaineExtensionCriteria


open GlobalTheory.Per.FontaineBound in
theorem fontCore_of_tied {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)
    (K : FinExt l) : LocalSituation.fontCore (P.PD K) := by
  intro LL _ _ _ O _ _ hO A
  have : FiniteDimensional ℚ_[l] LL := hO.2.1
  have hd := ddR_finite_le (P.PD K) (isField_of_tied T) A.ρ
  refine ⟨?_, hd, fun hc => ?_⟩
  · have := isDomain_cris (P.PD K) (isField_of_tied T)
    have := (P.PD K).finK₀
    refine finite_finrank_le (P.PD K).actB (fun b b' hb h => GlobalTheory.T.ratio_invariant_in_K0 l P AI T K b' b hb fun g hg => ?_) A.ρ
    have h1 := h ⟨g, hg⟩
    rw [P.PD_actB, P.PD_actB] at h1
    rw [mul_comm, h1, mul_comm]
  · refine (GlobalTheory.Per.CrisDR.abstract_cmp (P.PD K) A.ρ
      (fun m x hx b hb => GlobalTheory.T.injective_tensor_Bcris_to_BdR l P AI T K m x hx b ?_) hd.1 hd.2 hc).1
    simpa only [P.PD_ι] using hb

theorem strictness_of_tied {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) :
    GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.Strictness l P :=
  (GlobalTheory.DeRhamCompare.strict_iff P).1 (GlobalTheory.DRFil.deRhamComparison l P AI ⟨T⟩).2.2.2.2.2.1

theorem extCrys_of_tied : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    Nonempty (LocTied l P AI) → GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.ExtCrys P :=
  fun P _ ⟨T⟩ => GlobalTheory.CrysExt.extCrys P (fontCore_of_tied T) (strictness_of_tied T)

end GlobalTheory.FontaineExtensionCriteria
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

namespace GlobalTheory.SplitRowAll

theorem splitRow_at : ∀ D : D7, SplitRow_at D := by
  intro D
  refine ⟨fun l hl => GlobalTheory.T.split_prime_implies_places_split D.host l hl, fun i hi => ⟨?_, ?_, ?_, ?_⟩⟩
  · intro w hw
    have h2 : D.nd.l i ∉ D.host.small := ((primeClass_eq_splitK_iff _).1 hi.2.2.2.2.2).1
    exact (GlobalTheory.T.K0_eq_and_good_of_ne D i h2 hi.2.2.1 hi.2.2.2.1 w hw).1
  · rintro w hw τ ⟨h1, h2⟩
    rcases GlobalTheory.SplitRowProbe.embIn_xor D i w hw τ with h | h
    · exact h.2 h2
    · exact h.2 h1
  · exact GlobalTheory.T.splitPrime_place_cmType_conjugate D i hi
  · exact GlobalTheory.T.cmHalfTypePlaces_meet_conjugatePairs_and_count D i hi

end GlobalTheory.SplitRowAll
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.JSW.Central

def centralFns (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ω : HChar E) :
    Submodule ℂ (GA E a → ℂ) where
  carrier := {F | ∀ (z : Neutral.B1.Ideles E) (g : GA E a),
    F (GeneralLinearGroup.scalar (Fin a) z * g) = ((ω.1 z : ℂˣ) : ℂ) * F g}
  add_mem' hF hG z g := by simp [hF z g, hG z g, mul_add]
  zero_mem' _ _ := by simp
  smul_mem' c F hF z g := by simp [hF z g, mul_left_comm]

end GlobalTheory.JSW.Central
end
end
