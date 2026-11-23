module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.EqOneOfMemLev
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrData
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual UpperTheory.V.Af UpperTheory.V.Af.Tw
open scoped Pointwise

section SlopeTestRemainingChoices

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K L] [Algebra L Ω]
  [Algebra K Ω] [IsScalarTower K L Ω]

omit [NumberField L] in
private theorem int_mem (A : ValuationSubring Ω) (x : 𝓞 L) : algebraMap L Ω (x : L) ∈ A := by
  have hb : IsIntegral ℤ (algebraMap L Ω (x : L)) := x.isIntegral_coe.map (algebraMap L Ω).toIntAlgHom
  have h : IsIntegral A (algebraMap L Ω (x : L)) := hb.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  rw [← hy]
  exact y.2

private theorem place_between {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (hA : IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 L), IsPlaceOver A w ∧ w.asIdeal.LiesOver v.asIdeal := by
  let f : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A (int_mem A)
  let P : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap f
  have hP : ∀ x : 𝓞 L, A.valuation (algebraMap L Ω (x : L)) < 1 ↔ x ∈ P := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  have hu : v.asIdeal = P.under (𝓞 K) := by
    ext x
    rw [← hA x, Ideal.under, Ideal.mem_comap, ← hP, IsScalarTower.algebraMap_apply K L Ω]
    rfl
  have hne : P ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [hu, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  exact ⟨⟨P, inferInstance, hne⟩, hP, ⟨hu⟩⟩

private theorem normV_under (w : HeightOneSpectrum (𝓞 L)) :
    normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  have hnorm {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
      normV v = Ideal.absNorm v.asIdeal := by
    rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hnorm, hnorm]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 L) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

omit [NumberField K] in
private theorem frob_val {A : ValuationSubring Ω} {q : ℕ} (hq : q ≠ 0) {σ : G K Ω} (hσ : IsFrob A q σ) {x : Ω}
    (hx : A.valuation x ≤ 1) : A.valuation (σ x) ≤ 1 ∧ (A.valuation x < 1 → A.valuation (σ x) < 1) := by
  have e : σ x = (σ x - x ^ q) + x ^ q := by ring
  have h1 := hσ.2 x hx
  constructor
  · rw [e]
    exact Valuation.map_add_le _ h1.le (by rw [map_pow]; exact pow_le_one₀ zero_le hx)
  · intro h
    rw [e]
    exact Valuation.map_add_lt _ h1 (by rw [map_pow]; exact pow_lt_one₀ zero_le h hq)

omit [NumberField K] in
private theorem frob_sq {A : ValuationSubring Ω} {q : ℕ} (hq : q ≠ 0) {σ : G K Ω} (hσ : IsFrob A q σ) :
    IsFrob A (q ^ 2) (σ * σ) := by
  refine ⟨mul_mem hσ.1 hσ.1, fun x hx => ?_⟩
  have h1 := hσ.2 x hx
  have h2 := (frob_val hq hσ h1.le).2 h1
  have hxq : A.valuation (x ^ q) ≤ 1 := by rw [map_pow]; exact pow_le_one₀ zero_le hx
  have h3 := hσ.2 (x ^ q) hxq
  have e : (σ * σ) x - x ^ q ^ 2 = σ (σ x - x ^ q) + (σ (x ^ q) - (x ^ q) ^ q) := by
    rw [AlgEquiv.mul_apply, map_sub, sq, pow_mul]; ring
  rw [e]
  exact Valuation.map_add_lt _ h2 h3

end SlopeTestRemainingChoices

theorem UpperTheory.V.Af.Tw.frobInert :
    UpperTheory.V.Af.Tw.FrobInert := by
  intro F L Ω _ _ _ _ _ _ _ _ _ _ _ h2 v A hU hA σ hσ hn
  obtain ⟨w, hw, hwv⟩ := place_between (L := L) hA
  have : Algebra.IsQuadraticExtension F L := ⟨h2⟩
  have : IsGalois F L := inferInstance
  have hq : normV v ≠ 0 := by
    rw [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
    exact (lt_trans zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm v)).ne'
  have hu : w.under (𝓞 F) = v := HeightOneSpectrum.ext hwv.over.symm
  set c : L ≃ₐ[F] L := AlgEquiv.restrictNormalHom L σ with hc
  have hcx : ∀ x : L, algebraMap L Ω (c x) = σ (algebraMap L Ω x) := fun x =>
    AlgEquiv.restrictNormal_commutes σ L x
  have hc1 : c ≠ 1 := fun h => hn ⟨{ σ with
    commutes' := fun x => by
      have := hcx x
      rw [h] at this
      exact this.symm }, rfl⟩
  have := w.isMaximal
  have hcw : c • w.asIdeal = w.asIdeal := by
    have hmax : (c • w.asIdeal).IsMaximal := by
      exact Ideal.map_isMaximal_of_equiv (MulSemiringAction.toRingEquiv _ _ c)
    refine hmax.eq_of_le w.isPrime.ne_top ?_
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 hy |> fun h => (⟨c⁻¹ • y, h, smul_inv_smul c y⟩ : ∃ x ∈ w.asIdeal, c • x = y)
    rw [← hw] at hx ⊢
    have e : algebraMap L Ω ((c • x : 𝓞 L) : L) = σ (algebraMap L Ω (x : L)) := hcx x
    rw [e]
    exact (frob_val hq hσ hx.le).2 hx
  have huniq : ∀ P : Ideal (𝓞 L), P.IsPrime → P.LiesOver v.asIdeal → P = w.asIdeal := by
    intro P _ _
    obtain ⟨g, hg⟩ := Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal w.asIdeal P (L ≃ₐ[F] L)
    have hcard : Nat.card (L ≃ₐ[F] L) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
    by_cases hg1 : g = 1
    · rw [← hg, hg1, one_smul]
    · obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : L ≃ₐ[F] L)).1 hcard
      rw [← hg, hy g hg1, ← hy c hc1, hcw]
  have hf : w.asIdeal.inertiaDeg (𝓞 F) = 2 := by
    have := v.isPrime
    letI : Unique (v.asIdeal.primesOver (𝓞 L)) :=
      ⟨⟨⟨w.asIdeal, w.isPrime, hwv⟩⟩, fun P => Subtype.ext (huniq P.1 P.2.1 P.2.2)⟩
    have hs := Ideal.sum_ramification_inertia_eq_card (p := v.asIdeal) (S := 𝓞 L) (G := L ≃ₐ[F] L)
    rw [Fintype.sum_unique, IsGalois.card_aut_eq_finrank, h2] at hs
    have he := hU w hu
    rw [hu, Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot] at he
    change w.asIdeal.ramificationIdx (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 F) = 2 at hs
    rwa [he, one_mul] at hs
  refine ⟨w, fun u => ⟨fun h => HeightOneSpectrum.ext (huniq _ u.isPrime ⟨by rw [← h]; rfl⟩), fun h => h ▸ hu⟩,
    hw, fun t ht => ?_⟩
  have h3 := frob_sq hq hσ
  rw [← ht] at h3
  rw [normV_under (K := F), hu, hf]
  exact ⟨h3.1, h3.2⟩
end

section

theorem UpperTheory.V.Af.Tw.verGroup :
    UpperTheory.V.Af.Tw.VerGroup := by
  unfold UpperTheory.V.Af.Tw.VerGroup
  intro H Γ B _ _ _ _ _ _ _ _ _ r hr hidx κ hκ
  classical
  set R := r.range with hR
  have hinj : Function.Injective r := hr.injective
  have hrs : ∀ s, r s ∈ R := fun s => MonoidHom.mem_range.mpr ⟨s, rfl⟩
  have hmem : ∀ a b : Γ, a * b ∈ R ↔ (a ∈ R ↔ b ∈ R) := fun a b =>
    Subgroup.mul_mem_iff_of_index_two hidx
  have hnorm : R.Normal := Subgroup.normal_of_index_eq_two hidx
  have hsq : ∀ g, g ∉ R → g * g ∈ R := fun g _ => (hmem g g).mpr Iff.rfl
  obtain ⟨g0, hg0⟩ : ∃ g0 : Γ, g0 ∉ R := by
    by_contra hcon
    push_neg at hcon
    have htop : R = ⊤ := eq_top_iff.mpr fun x _ => hcon x
    rw [htop, Subgroup.index_top] at hidx
    exact absurd hidx (by norm_num)
  let pre : Γ → H := fun γ => if h : γ ∈ R then (MonoidHom.mem_range.mp h).choose else 1
  have hpre : ∀ γ, γ ∈ R → r (pre γ) = γ := fun γ h => by
    dsimp only [pre]
    rw [dite_eq_left h]
    exact (MonoidHom.mem_range.mp h).choose_spec
  let k : Γ → B := fun γ => κ (pre γ)
  have kr : ∀ s, k (r s) = κ s := fun s => by
    show κ (pre (r s)) = κ s
    rw [hinj (hpre _ (hrs s))]
  have kmul : ∀ a, a ∈ R → ∀ b, b ∈ R → k (a * b) = k a * k b := by
    intro a ha b hb
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp ha
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hb
    rw [← map_mul, kr, kr, kr, map_mul]
  have kinv : ∀ a, a ∈ R → k a⁻¹ = (k a)⁻¹ := by
    intro a ha
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp ha
    rw [← map_inv, kr, kr, map_inv]
  have k1 : k 1 = 1 := by
    have h := kr 1
    rwa [map_one, map_one] at h
  have L : ∀ g, g ∉ R → ∀ x, x ∈ R → k (g * x * g⁻¹) = k (g0 * x * g0⁻¹) := by
    intro g hg x hx
    have hh : g0⁻¹ * g ∈ R :=
      (hmem _ _).mpr (iff_of_false (fun h => hg0 (by simpa using R.inv_mem h)) hg)
    have hc : g0 * (g0⁻¹ * g) * g0⁻¹ ∈ R := hnorm.conj_mem _ hh g0
    have hx' : g0 * x * g0⁻¹ ∈ R := hnorm.conj_mem _ hx g0
    have e1 : g * x * g⁻¹ = (g0 * (g0⁻¹ * g) * g0⁻¹) * (g0 * x * g0⁻¹) *
        (g0 * (g0⁻¹ * g) * g0⁻¹)⁻¹ := by group
    rw [e1, kmul _ (R.mul_mem hc hx') _ (R.inv_mem hc), kmul _ hc _ hx', kinv _ hc,
      mul_inv_cancel_comm]
  let f : Γ → B := fun γ => if γ ∈ R then k γ * k (g0 * γ * g0⁻¹) else k (γ * γ)
  have fin : ∀ γ, γ ∈ R → f γ = k γ * k (g0 * γ * g0⁻¹) := fun γ h => if_pos h
  have fout : ∀ γ, γ ∉ R → f γ = k (γ * γ) := fun γ h => if_neg h
  have fmul : ∀ x y, f (x * y) = f x * f y := by
    intro x y
    by_cases hx : x ∈ R <;> by_cases hy : y ∈ R
    · have hxy := R.mul_mem hx hy
      have cx := hnorm.conj_mem _ hx g0
      have cy := hnorm.conj_mem _ hy g0
      rw [fin _ hxy, fin _ hx, fin _ hy,
        show g0 * (x * y) * g0⁻¹ = (g0 * x * g0⁻¹) * (g0 * y * g0⁻¹) by group,
        kmul _ hx _ hy, kmul _ cx _ cy, mul_mul_mul_comm]
    · have hxy : x * y ∉ R := fun h => hy (((hmem x y).mp h).mp hx)
      have c1 : y * x * y⁻¹ ∈ R := hnorm.conj_mem _ hx y
      rw [fout _ hxy, fin _ hx, fout _ hy,
        show x * y * (x * y) = x * (y * x * y⁻¹) * (y * y) by group,
        kmul _ (R.mul_mem hx c1) _ (hsq y hy), kmul _ hx _ c1, L y hy x hx]
    · have hxy : x * y ∉ R := fun h => hx (((hmem x y).mp h).mpr hy)
      have c1 : x * y * x⁻¹ ∈ R := hnorm.conj_mem _ hy x
      rw [fout _ hxy, fout _ hx, fin _ hy,
        show x * y * (x * y) = (x * y * x⁻¹) * (x * x) * y by group,
        kmul _ (R.mul_mem c1 (hsq x hx)) _ hy, kmul _ c1 _ (hsq x hx), L x hx y hy,
        mul_comm (k (g0 * y * g0⁻¹)), mul_assoc, mul_comm (k (g0 * y * g0⁻¹))]
    · have hxy : x * y ∈ R := (hmem x y).mpr (iff_of_false hx hy)
      have hyx : y * x ∈ R := (hmem y x).mpr (iff_of_false hy hx)
      have hyy := hsq y hy
      have hxx := hsq x hx
      have c1 : x * (y * y) * x⁻¹ ∈ R := hnorm.conj_mem _ hyy x
      rw [fin _ hxy, fout _ hx, fout _ hy, ← L y hy _ hxy,
        show y * (x * y) * y⁻¹ = y * x by group, ← kmul _ hxy _ hyx,
        show x * y * (y * x) = x * (y * y) * x⁻¹ * (x * x) by group,
        kmul _ c1 _ hxx, L x hx _ hyy, ← L y hy _ hyy,
        show y * (y * y) * y⁻¹ = y * y by group, mul_comm]
  let ν : Γ →* B :=
    { toFun := f
      map_one' := by
        show f 1 = 1
        rw [fin _ R.one_mem, mul_one, mul_inv_cancel, k1, mul_one]
      map_mul' := fmul }
  have hσ : Continuous (fun s : H => pre (g0 * r s * g0⁻¹)) := by
    rw [hr.toIsEmbedding.toIsInducing.continuous_iff]
    have hcomp : (r ∘ fun s : H => pre (g0 * r s * g0⁻¹)) = fun s => g0 * r s * g0⁻¹ :=
      funext fun s => hpre _ (hnorm.conj_mem _ (hrs s) g0)
    rw [hcomp]
    exact (continuous_const.mul hr.continuous).mul continuous_const
  have hνr : (ν ∘ r) = fun s => κ s * κ (pre (g0 * r s * g0⁻¹)) := by
    funext s
    show f (r s) = _
    rw [fin _ (hrs s), kr]
  have hcont : Continuous ν := by
    apply continuous_of_continuousAt_one
    have h1 : ContinuousAt (ν ∘ r) 1 := by
      rw [hνr]
      exact (hκ.mul (hκ.comp hσ)).continuousAt
    rw [hr.continuousAt_iff, map_one] at h1
    exact h1
  refine ⟨ν, hcont, fun g hg => ⟨fun s s' hs => ?_, fun t ht => ?_⟩⟩
  · show κ s * κ s' = f (r s)
    rw [fin _ (hrs s), kr, ← L g hg _ (hrs s), ← hs, kr]
  · show κ t = f g
    rw [fout _ hg, ← ht, kr]
end

section

namespace UpperTheory.V.Af.Tw

private theorem glue_ext {G H B : Type*} [CommGroup G] [CommGroup H] [CommGroup B] (hB : KStar.Choice.IsDiv B)
    (p : G →* H) (f : G →* B) (h : ∀ x, p x = 1 → f x = 1) : ∃ F : H →* B, ∀ x, F (p x) = f x := by
  classical
  obtain ⟨F, hF⟩ := hB.exists_extension p.range
    ((QuotientGroup.lift p.ker f (fun x hx => (MonoidHom.mem_ker).2 (h x ((MonoidHom.mem_ker).1 hx)))).comp
      (QuotientGroup.quotientKerEquivRange p).symm.toMonoidHom)
  refine ⟨F, fun x => (hF ⟨p x, x, rfl⟩).trans ?_⟩
  have hx : (QuotientGroup.quotientKerEquivRange p).symm ⟨p x, x, rfl⟩ = (x : G ⧸ p.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hx]
  rfl

private theorem glue_exp (n M l : ℕ) (hM : 0 < M) (hl : l.Prime) :
    ∃ e k : ℕ, e ≡ 1 [MOD n] ∧ 0 < k ∧ (n.Coprime l → k.Coprime l) ∧ M ∣ e * k := by
  by_cases hc : n.Coprime l
  · have hM0 : M ≠ 0 := hM.ne'
    have hco : n.Coprime (l ^ M.factorization l) := Nat.Coprime.pow_right _ hc
    obtain ⟨e, he1, he0⟩ := Nat.chineseRemainder hco 1 0
    refine ⟨e, M / l ^ M.factorization l, he1, Nat.ordCompl_pos l hM0,
      fun _ => (Nat.coprime_ordCompl hl hM0).symm, ?_⟩
    have hd : l ^ M.factorization l ∣ e := (Nat.modEq_zero_iff_dvd).1 he0
    calc M = l ^ M.factorization l * (M / l ^ M.factorization l) :=
          (Nat.ordProj_mul_ordCompl_eq_self M l).symm
      _ ∣ e * (M / l ^ M.factorization l) := mul_dvd_mul_right hd _
  · exact ⟨1, M, Nat.ModEq.refl 1, hM, fun h' => absurd h' hc, by simp⟩

theorem glue : Glue := by
  unfold Glue
  intro I J K B _ _ _ _ hB i d c σ U V N g n M l hM hl h1 h2 h3 h4 h5 h6 h7 h8
  obtain ⟨e, k, he, hk0, hkc, hMk⟩ := glue_exp n M l hM hl
  obtain ⟨p₀, hp₀⟩ : ∃ p₀ : J × K × U →* I, ∀ z, p₀ z = i z.1 * d z.2.1 * (z.2.2 : I) :=
    ⟨i.comp (MonoidHom.fst _ _) * d.comp ((MonoidHom.fst _ _).comp (MonoidHom.snd _ _)) *
      U.subtype.comp ((MonoidHom.snd _ _).comp (MonoidHom.snd _ _)), fun z => rfl⟩
  have hq : ∀ z, p₀ z = 1 → (z.2.2 : I) / c z.2.2 = d (σ z.2.1 / z.2.1) := by
    intro z hz
    rw [hp₀] at hz
    have hu : (z.2.2 : I) = (i z.1 * d z.2.1)⁻¹ := eq_inv_of_mul_eq_one_right hz
    rw [hu, map_inv, map_mul, h1, h2, map_div]
    simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  obtain ⟨pθ, hpθ⟩ : ∃ pθ : p₀.ker × V →* I,
      ∀ w, pθ w = d (σ (w.1 : J × K × U).2.1 / (w.1 : J × K × U).2.1) * (w.2 : I) :=
    ⟨d.comp ((σ / MonoidHom.id K).comp ((MonoidHom.fst _ _).comp ((MonoidHom.snd _ _).comp
      (p₀.ker.subtype.comp (MonoidHom.fst _ _))))) * V.subtype.comp (MonoidHom.snd _ _), fun w => rfl⟩
  obtain ⟨fθ, hfθ⟩ : ∃ fθ : p₀.ker × V →* B,
      ∀ w, fθ w = (N (w.1 : J × K × U).1 * g ((w.1 : J × K × U).2.2 : I))⁻¹ :=
    ⟨((N.comp (MonoidHom.fst _ _) * g.comp (U.subtype.comp ((MonoidHom.snd _ _).comp
      (MonoidHom.snd _ _)))).comp (p₀.ker.subtype.comp (MonoidHom.fst _ _)))⁻¹, fun w => rfl⟩
  obtain ⟨θ₁, hθ₁⟩ := glue_ext hB pθ fθ (by
    rintro ⟨⟨⟨a, x, u⟩, hz⟩, v⟩ hw
    rw [hpθ] at hw
    rw [hfθ]
    dsimp only at hw ⊢
    have hz' : p₀ (a, x, u) = 1 := MonoidHom.mem_ker.1 hz
    rw [hp₀] at hz'
    dsimp only at hz'
    have hv : d (σ x / x) = (v : I)⁻¹ := eq_inv_of_mul_eq_one_left hw
    have hσ : σ x = x := h7 x (by rw [hv]; exact inv_mem v.2)
    obtain ⟨a', ha', hN⟩ := h5 x hσ
    have hiu : i (a * a') = (u : I)⁻¹ := by
      rw [map_mul, ha']
      exact eq_inv_of_mul_eq_one_left hz'
    have h4' := h4 (a * a') (by rw [hiu]; exact inv_mem u.2)
    rw [hiu, map_inv, map_mul, hN, mul_one] at h4'
    rw [← h4', inv_mul_cancel, inv_one])
  obtain ⟨θ, hθ⟩ : ∃ θ : I →* B, ∀ y, θ y = θ₁ y ^ e := ⟨(powMonoidHom e).comp θ₁, fun y => rfl⟩
  have hV : ∀ v ∈ V, θ₁ v = 1 := by
    intro v hv
    have h := hθ₁ (1, ⟨v, hv⟩)
    rw [hpθ, hfθ] at h
    simpa using h
  have hZ : ∀ z, p₀ z = 1 → θ (z.2.2 / c z.2.2) = (N z.1 * g z.2.2)⁻¹ := by
    intro z hz
    have h := hθ₁ (⟨z, MonoidHom.mem_ker.2 hz⟩, 1)
    rw [hpθ, hfθ] at h
    dsimp only at h
    simp only [OneMemClass.coe_one, mul_one] at h
    rw [hθ, hq z hz, h]
    have hw : ((N z.1 * g z.2.2)⁻¹) ^ n = 1 := by
      have hmem : d (σ z.2.1 / z.2.1) ∈ U := by
        rw [← hq z hz]
        exact div_mem z.2.2.2 (h3 _ z.2.2.2)
      rw [← h, ← map_pow, ← map_pow, h6 _ hmem, map_one, map_one]
    rw [pow_eq_pow_mod e hw, show e % n = 1 % n from he, ← pow_eq_pow_mod 1 hw, pow_one]
  obtain ⟨f, hf⟩ : ∃ f : J × K × U →* B, ∀ z, f z = N z.1 * (g z.2.2 * θ (z.2.2 / c z.2.2)) :=
    ⟨N.comp (MonoidHom.fst _ _) * (g.comp (U.subtype.comp ((MonoidHom.snd _ _).comp
      (MonoidHom.snd _ _))) * θ.comp ((U.subtype / c.comp U.subtype).comp
      ((MonoidHom.snd _ _).comp (MonoidHom.snd _ _)))), fun z => rfl⟩
  obtain ⟨ψ, hψ⟩ := glue_ext hB p₀ f (by
    intro z hz
    rw [hf, hZ z hz, ← mul_assoc, mul_inv_cancel])
  refine ⟨ψ, θ, fun a => ?_, fun x => ?_, fun u hu => ?_, fun v hv => ?_, k, hk0, hkc, fun u hu => ?_⟩
  · have h := hψ (a, 1, 1)
    rw [hp₀, hf] at h
    simpa using h
  · have h := hψ (1, x, 1)
    rw [hp₀, hf] at h
    simpa using h
  · have h := hψ (1, 1, ⟨u, hu⟩)
    rw [hp₀, hf] at h
    simpa using h
  · rw [hθ, hV v hv, one_pow]
  · obtain ⟨j, hj⟩ := hMk
    rw [hθ, ← pow_mul, ← map_pow, hj, pow_mul]
    exact hV _ (pow_mem (h8 u hu) j)

end UpperTheory.V.Af.Tw
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Af
open scoped Pointwise

theorem UpperTheory.V.Af.Tw.conjPlace :
    UpperTheory.V.Af.Tw.ConjPlace := by
  intro F L Ω _ _ _ _ _ _ _ _ _ _ _ h g hg w w' A hA hne hun
  haveI : Algebra.IsQuadraticExtension F L := ⟨h⟩
  have hc : Nat.card (L ≃ₐ[F] L) = 2 := (IsGalois.card_aut_eq_finrank F L).trans h
  obtain ⟨t, -, hu⟩ := (Nat.card_eq_two_iff' (1 : L ≃ₐ[F] L)).1 hc
  have h1 : g.restrictNormal L = t := by
    refine hu _ fun h1 => hg ?_
    refine ⟨AlgEquiv.ofRingEquiv (f := g.toRingEquiv) fun y => ?_, AlgEquiv.ext fun _ => rfl⟩
    have := AlgEquiv.restrictNormal_commutes g L y
    rw [h1] at this
    exact this.symm
  have hlift : ∀ x : L, g (algebraMap L Ω x) = algebraMap L Ω (t x) := fun x => by
    rw [← h1]
    exact (AlgEquiv.restrictNormal_commutes g L x).symm
  haveI := w.isPrime
  haveI := w'.isPrime
  haveI : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
  haveI : w'.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨congrArg HeightOneSpectrum.asIdeal hun.symm⟩
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (w.under (𝓞 F)).asIdeal w.asIdeal w'.asIdeal
    (L ≃ₐ[F] L)
  obtain rfl : σ = t := hu σ fun h0 => hne (HeightOneSpectrum.ext (by rw [← hσ, h0, one_smul]))
  have hA' : ∀ x, g.toRingEquiv x ∈ g • A ↔ x ∈ A := fun x => ValuationSubring.smul_mem_pointwise_smul_iff
  refine ⟨g • A, fun x => ?_, fun s s' hs => ?_⟩
  · obtain ⟨y, rfl⟩ := MulAction.surjective σ x
    rw [← hσ, Ideal.smul_mem_pointwise_smul_iff, ← hA y, ← val_lt_one hA']
    have h2 : g.toRingEquiv (algebraMap L Ω (y : L)) = algebraMap L Ω ((σ • y : 𝓞 L) : L) := hlift y
    rw [h2]
  · have hss : ∀ x, s' (g x) = g (s x) := fun x => by
      refine (DFunLike.congr_fun hs (g x)).trans ?_
      show g (s (g.symm (g x))) = _
      rw [AlgEquiv.symm_apply_apply]
    have hD : s ∈ Dec (F := L) A → s' ∈ Dec (F := L) (g • A) := fun hs0 => by
      refine mem_Dec.2 ?_
      show resG F L Ω s' • g • A = g • A
      have h3 : resG F L Ω s • A = A := mem_Dec.1 hs0
      rw [hs, ← mul_smul, inv_mul_cancel_right, mul_smul, h3]
    have hle : ∀ y, (g • A).valuation (g y) ≤ 1 → A.valuation y ≤ 1 := fun y hy =>
      (A.valuation_le_one_iff _).2 ((hA' y).1 (((g • A).valuation_le_one_iff _).1 hy))
    refine ⟨fun hI => ⟨hD hI.1, fun x hx => ?_⟩, fun q hF => ⟨hD hF.1, fun x hx => ?_⟩⟩
    · obtain ⟨y, rfl⟩ := g.surjective x
      rw [hss, ← map_sub]
      exact (val_lt_one hA' _).2 (hI.2 y (hle y hx))
    · obtain ⟨y, rfl⟩ := g.surjective x
      rw [hss, ← map_pow, ← map_sub]
      exact (val_lt_one hA' _).2 (hF.2 y (hle y hx))
end
