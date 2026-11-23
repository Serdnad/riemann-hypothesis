module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.EtaleCohomology.EtaleSheaves.Bundle050
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES

private theorem UpperTheory.Cb.idempotent_lift_succ_pow {R : Type*} [CommRing R] (σ : R →+* R) (P : R) (I : Ideal R) (k : ℕ)
    (a : R) (ha : a ∈ I) (h1 : P ^ (k + 1) ∣ a + σ a - 1) (h2 : P ^ (k + 1) ∣ a * σ a) :
    ∃ a' ∈ I, P ^ (k + 2) ∣ a' + σ a' - 1 ∧ P ^ (k + 2) ∣ a' * σ a' := by
  obtain ⟨c, hc⟩ := h1
  obtain ⟨d, hd⟩ := h2
  refine ⟨3 * a ^ 2 - 2 * a ^ 3, ?_, ?_, ?_⟩
  · have h3 : a ^ 2 * (3 - 2 * a) ∈ I := I.mul_mem_right _ (by
      rw [pow_two]
      exact I.mul_mem_left _ ha)
    have e : 3 * a ^ 2 - 2 * a ^ 3 = a ^ 2 * (3 - 2 * a) := by ring
    rw [e]
    exact h3
  · have e1 : 3 * a ^ 2 - 2 * a ^ 3 + σ (3 * a ^ 2 - 2 * a ^ 3) - 1 =
        -3 * (a + σ a - 1) ^ 2 - 2 * (a + σ a - 1) ^ 3 + 6 * (a * σ a) * (a + σ a - 1) := by
      simp only [map_sub, map_mul, map_pow, map_ofNat]
      ring
    rw [e1, hc, hd]
    exact ⟨P ^ k * (-3 * c ^ 2 - 2 * P ^ (k + 1) * c ^ 3 + 6 * d * c), by ring⟩
  · have e2 : (3 * a ^ 2 - 2 * a ^ 3) * σ (3 * a ^ 2 - 2 * a ^ 3) =
        (a * σ a) ^ 2 * ((3 - 2 * a) * (3 - 2 * σ a)) := by
      simp only [map_sub, map_mul, map_pow, map_ofNat]
      ring
    rw [e2, hd]
    exact ⟨P ^ k * d ^ 2 * ((3 - 2 * a) * (3 - 2 * σ a)), by ring⟩

private theorem UpperTheory.Cb.exists_idempotent_lift_pow {R : Type*} [CommRing R] (σ : R →+* R) (P : R) (I : Ideal R)
    (a : R) (ha : a ∈ I) (h1 : P ∣ a + σ a - 1) (h2 : P ∣ a * σ a) (k : ℕ) :
    ∃ a' ∈ I, P ^ (k + 1) ∣ a' + σ a' - 1 ∧ P ^ (k + 1) ∣ a' * σ a' := by
  induction k with
  | zero => exact ⟨a, ha, by simpa using h1, by simpa using h2⟩
  | succ k ih =>
    obtain ⟨b, hb, hb1, hb2⟩ := ih
    exact UpperTheory.Cb.idempotent_lift_succ_pow σ P I k b hb hb1 hb2

theorem UpperTheory.Cb.exists_mem_uIdeal_idempotent_mod_prime_pow :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (r : ℤ) (w : Ideal (𝓞 D.F)) (e : ℕ), w ≠ ⊤ → uIdeal D r ≤ w → ∃ a ∈ uIdeal D r, (p : 𝓞 D.F) ^ e ∣ a + D.bar a - 1 ∧ (p : 𝓞 D.F) ^ e ∣ a * D.bar a := by
  intro p _ D r w e hw hle
  have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
  set x : 𝓞 D.F := D.ω - (r : 𝓞 D.F) with hx
  set N : ℤ := r ^ 2 - D.tr * r + D.nm with hN
  set s : ℤ := D.tr - 2 * r with hs
  have hbx : D.bar x = D.bar D.ω - (r : 𝓞 D.F) := by
    simp [x, map_sub, map_intCast]
  have hxN : x * D.bar x = (N : 𝓞 D.F) := by
    rw [hbx]
    push_cast [N]
    linear_combination D.nm_eq - (r : 𝓞 D.F) * D.tr_eq
  have hxs : x + D.bar x = (s : 𝓞 D.F) := by
    rw [hbx]
    push_cast [s]
    linear_combination D.tr_eq
  have hpN : (p : ℤ) ∣ N := by
    by_contra hnd
    obtain ⟨u, v, huv⟩ := (Irreducible.coprime_iff_not_dvd hp.irreducible).mpr hnd
    apply hw
    rw [Ideal.eq_top_iff_one]
    have hpw : ((p : ℤ) : 𝓞 D.F) ∈ w := by
      have := hle (p_mem_uIdeal D r)
      simpa using this
    have hNw : ((N : ℤ) : 𝓞 D.F) ∈ w := by
      rw [← hxN]
      exact w.mul_mem_right _ (hle (sub_mem_uIdeal D r))
    have h1 : ((u * p + v * N : ℤ) : 𝓞 D.F) ∈ w := by
      push_cast
      exact w.add_mem (w.mul_mem_left _ (by simpa using hpw)) (w.mul_mem_left _ hNw)
    rw [huv] at h1
    simpa using h1
  have hps : ¬ (p : ℤ) ∣ s := by
    intro hd
    apply D.disc_p
    have e : D.tr ^ 2 - 4 * D.nm = s ^ 2 - 4 * N := by
      simp only [s, N]
      ring
    rw [e]
    exact dvd_sub (dvd_pow hd two_ne_zero) (dvd_mul_of_dvd_right hpN 4)
  obtain ⟨u, v, huv⟩ := (Irreducible.coprime_iff_not_dvd hp.irreducible).mpr hps
  obtain ⟨N', hN'⟩ := hpN
  have ha : (v : 𝓞 D.F) * x ∈ uIdeal D r := (uIdeal D r).mul_mem_left _ (sub_mem_uIdeal D r)
  have h1 : (p : 𝓞 D.F) ∣ (v : 𝓞 D.F) * x + D.bar ((v : 𝓞 D.F) * x) - 1 := by
    refine ⟨-(u : 𝓞 D.F), ?_⟩
    rw [map_mul, map_intCast]
    have e : (v : 𝓞 D.F) * x + (v : 𝓞 D.F) * D.bar x - 1 = (v : 𝓞 D.F) * (x + D.bar x) - 1 := by ring
    rw [e, hxs]
    have huv' : ((u * p + v * s : ℤ) : 𝓞 D.F) = 1 := by rw [huv]; simp
    push_cast at huv'
    linear_combination huv'
  have h2 : (p : 𝓞 D.F) ∣ (v : 𝓞 D.F) * x * D.bar ((v : 𝓞 D.F) * x) := by
    refine ⟨(v : 𝓞 D.F) ^ 2 * (N' : 𝓞 D.F), ?_⟩
    rw [map_mul, map_intCast]
    have e : (v : 𝓞 D.F) * x * ((v : 𝓞 D.F) * D.bar x) = (v : 𝓞 D.F) ^ 2 * (x * D.bar x) := by ring
    rw [e, hxN, hN']
    push_cast
    ring
  obtain ⟨a', ha', h1', h2'⟩ := UpperTheory.Cb.exists_idempotent_lift_pow (D.bar : 𝓞 D.F →+* 𝓞 D.F) (p : 𝓞 D.F)
    (uIdeal D r) _ ha (by simpa using h1) (by simpa using h2) e
  refine ⟨a', ha', ?_, ?_⟩
  · exact (pow_dvd_pow _ (Nat.le_succ e)).trans (by simpa using h1')
  · exact (pow_dvd_pow _ (Nat.le_succ e)).trans (by simpa using h2')
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace UpperTheory.Cb.RestrictionCovers
open LateralTheory.E.CechSigmaProof LateralTheory.E.CechSigma_xy1Pf_Lev

private theorem mem_iInf_fin {T : Type*} [TopologicalSpace T] {m : ℕ}
    (U : Fin m → TopologicalSpace.Opens T) (x : T) : x ∈ ⨅ k, U k ↔ ∀ k, x ∈ U k := by
  refine ⟨fun h k => (iInf_le U k) h, fun h => ?_⟩
  rw [← Finset.inf_univ_eq_iInf, ← SetLike.mem_coe, TopologicalSpace.Opens.coe_finset_inf]
  simp [Finset.inf_eq_iInf, h]

section
variable {X : Scheme.{0}} (O : X.Opens) {ι : Type} (V : ι → X.Opens) (hV : ∀ j, V j ≤ O) {n : ℕ}

abbrev P (n : ℕ) : Scheme.{0} :=
  widePullback O.toScheme (fun _ : Fin (n + 1) => ∐ fun j => (V j).toScheme) (fun _ => cov O V hV)

private theorem ι_cov (i : ι) : Sigma.ι (fun j => (V j).toScheme) i ≫ cov O V hV ≫ O.ι = (V i).ι := by
  simp [cov]

variable (W : (Fin (n + 1) → ι) → X.Opens) (hW : ∀ j x, x ∈ W j ↔ ∀ k, x ∈ V (j k))

include hW in
theorem le_V (j) (k) : W j ≤ V (j k) := fun x hx => (hW j x).1 hx k

include hV hW in
theorem le_O (j) : W j ≤ O := (le_V V W hW j 0).trans (hV _)

def cmp (j : Fin (n + 1) → ι) : (W j).toScheme ⟶ P O V hV n :=
  WidePullback.lift (X.homOfLE (le_O O V hV W hW j))
    (fun k => X.homOfLE (le_V V W hW j k) ≫ Sigma.ι (fun j => (V j).toScheme) (j k))
    (fun k => by
      rw [← cancel_mono O.ι]
      simp [cov])

theorem cmp_base (j) : cmp O V hV W hW j ≫ WidePullback.base _ = X.homOfLE (le_O O V hV W hW j) :=
  WidePullback.lift_base ..

theorem cmp_π (j) (k) : cmp O V hV W hW j ≫ WidePullback.π _ k =
    X.homOfLE (le_V V W hW j k) ≫ Sigma.ι (fun j => (V j).toScheme) (j k) :=
  WidePullback.lift_π ..

def PJ (j : Fin (n + 1) → ι) : (P O V hV n).Opens :=
  ⨅ k, (WidePullback.π (fun _ : Fin (n + 1) => cov O V hV) k) ⁻¹ᵁ
    (Sigma.ι (fun j => (V j).toScheme) (j k)).opensRange

theorem mem_PJ (j) (x : P O V hV n) : x ∈ PJ O V hV j ↔
    ∀ k, ∃ z, Sigma.ι (fun j => (V j).toScheme) (j k) z =
      WidePullback.π (fun _ : Fin (n + 1) => cov O V hV) k x := by
  rw [PJ, mem_iInf_fin]
  rfl

include hW in
theorem hr (j) : Set.range ((PJ O V hV j).ι ≫
    WidePullback.base (fun _ : Fin (n + 1) => cov O V hV) ≫ O.ι) ⊆ Set.range (W j).ι := by
  rintro _ ⟨y, rfl⟩
  rw [Scheme.Opens.range_ι]
  refine (hW j _).2 fun k => ?_
  obtain ⟨z, hz⟩ := (mem_PJ O V hV j _).1 y.2 k
  have e : (V (j k)).ι z = ((PJ O V hV j).ι ≫
      WidePullback.base (fun _ : Fin (n + 1) => cov O V hV) ≫ O.ι) y := by
    rw [← ι_cov O V hV (j k), Scheme.Hom.comp_apply, hz, ← WidePullback.π_arrow _ k]
    simp only [Scheme.Hom.comp_apply, Category.assoc]
    rfl
  rw [← e]
  exact (V (j k)).ι_apply z ▸ z.2

def rr (j : Fin (n + 1) → ι) : (PJ O V hV j).toScheme ⟶ (W j).toScheme :=
  IsOpenImmersion.lift (W j).ι _ (private_decl% (hr O V hV W hW j))

theorem rr_ι (j) : rr O V hV W hW j ≫ (W j).ι =
    (PJ O V hV j).ι ≫ WidePullback.base (fun _ : Fin (n + 1) => cov O V hV) ≫ O.ι :=
  IsOpenImmersion.lift_fac _ _ _

theorem rr_cmp (j) : rr O V hV W hW j ≫ cmp O V hV W hW j = (PJ O V hV j).ι := by
  apply WidePullback.hom_ext
  · intro k
    have hs : Set.range ((PJ O V hV j).ι ≫ WidePullback.π (fun _ : Fin (n + 1) => cov O V hV) k) ⊆
        Set.range (Sigma.ι (fun j => (V j).toScheme) (j k)) := by
      rintro _ ⟨y, rfl⟩
      obtain ⟨z, hz⟩ := (mem_PJ O V hV j _).1 y.2 k
      exact ⟨z, by rw [hz, Scheme.Hom.comp_apply]; rfl⟩
    rw [Category.assoc, cmp_π, ← IsOpenImmersion.lift_fac _ _ hs, ← Category.assoc]
    congr 1
    rw [← cancel_mono (V (j k)).ι, Category.assoc, Scheme.homOfLE_ι, rr_ι, ← ι_cov O V hV (j k),
      IsOpenImmersion.lift_fac_assoc, Category.assoc, WidePullback.π_arrow_assoc]
  · rw [Category.assoc, cmp_base, ← cancel_mono O.ι, Category.assoc, Scheme.homOfLE_ι, rr_ι,
      Category.assoc]

private theorem hr3 (j) : Set.range (cmp O V hV W hW j) ⊆ Set.range (PJ O V hV j).ι := by
  rintro _ ⟨w, rfl⟩
  rw [Scheme.Opens.range_ι]
  refine (mem_PJ O V hV j _).2 fun k => ⟨X.homOfLE (le_V V W hW j k) w, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← cmp_π O V hV W hW j k, Scheme.Hom.comp_apply]

def ss (j : Fin (n + 1) → ι) : (W j).toScheme ⟶ (PJ O V hV j).toScheme :=
  IsOpenImmersion.lift (PJ O V hV j).ι _ (private_decl% (hr3 O V hV W hW j))

theorem ss_ι (j) : ss O V hV W hW j ≫ (PJ O V hV j).ι = cmp O V hV W hW j :=
  IsOpenImmersion.lift_fac _ _ _

theorem ss_rr (j) : ss O V hV W hW j ≫ rr O V hV W hW j = 𝟙 _ := by
  rw [← cancel_mono (W j).ι, Category.assoc, rr_ι, ← Category.assoc, ss_ι, ← Category.assoc,
    cmp_base, Scheme.homOfLE_ι, Category.id_comp]

theorem rr_ss (j) : rr O V hV W hW j ≫ ss O V hV W hW j = 𝟙 _ := by
  rw [← cancel_mono (PJ O V hV j).ι, Category.assoc, ss_ι, rr_cmp, Category.id_comp]

instance cmp_open (j) : IsOpenImmersion (cmp O V hV W hW j) := by
  have : IsIso (ss O V hV W hW j) := ⟨rr O V hV W hW j, ss_rr .., rr_ss ..⟩
  rw [← ss_ι]
  infer_instance

private theorem cmp_disj : Pairwise (Function.onFun Disjoint
    (fun j => Set.range (cmp O V hV W hW j))) := by
  intro a b hab
  rw [Function.onFun, Set.disjoint_left]
  rintro _ ⟨u, rfl⟩ ⟨v, hv⟩
  obtain ⟨k, hk⟩ : ∃ k, a k ≠ b k := by
    by_contra h
    push_neg at h
    exact hab (funext h)
  have e : Sigma.ι (fun j => (V j).toScheme) (b k) (X.homOfLE (le_V V W hW b k) v) =
      Sigma.ι (fun j => (V j).toScheme) (a k) (X.homOfLE (le_V V W hW a k) u) := by
    rw [← Scheme.Hom.comp_apply, ← cmp_π O V hV W hW b k, Scheme.Hom.comp_apply, hv,
      ← Scheme.Hom.comp_apply, cmp_π, Scheme.Hom.comp_apply]
  exact hk (congrArg Sigma.fst ((sigmaι_eq_iff _ _ _ _ _).mp e)).symm

instance cmp_sigma_open : IsOpenImmersion (Sigma.desc (cmp O V hV W hW)) :=
  isOpenImmersion_sigmaDesc _ _ (cmp_disj O V hV W hW)

instance cmp_sigma_surj : Surjective (Sigma.desc (cmp O V hV W hW)) := by
  refine ⟨fun x => ?_⟩
  have hx : ∀ k, ∃ i, ∃ z, Sigma.ι (fun j => (V j).toScheme) i z =
      WidePullback.π (fun _ : Fin (n + 1) => cov O V hV) k x := by
    intro k
    obtain ⟨⟨i, z⟩, hz⟩ := (sigmaMk (fun j => (V j).toScheme)).surjective
      (WidePullback.π (fun _ : Fin (n + 1) => cov O V hV) k x)
    rw [sigmaMk_mk] at hz
    exact ⟨i, z, hz⟩
  choose j z hz using hx
  have hm : x ∈ PJ O V hV j := (mem_PJ O V hV j x).2 fun k => ⟨z k, hz k⟩
  let y : (PJ O V hV j).toScheme := ⟨x, hm⟩
  have key : (rr O V hV W hW j ≫ cmp O V hV W hW j) y = x := by
    rw [rr_cmp]
    exact (PJ O V hV j).ι_apply _
  refine ⟨(Sigma.ι (fun j => (W j).toScheme) j) (rr O V hV W hW j y), ?_⟩
  rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]
  exact (Scheme.Hom.comp_apply _ _ _).symm.trans key

instance cmp_sigma_iso : IsIso (Sigma.desc (cmp O V hV W hW)) :=
  (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, inferInstance⟩

end

end UpperTheory.Cb.RestrictionCovers

namespace UpperTheory.Cb.RestrictionCovers
open LateralTheory.E.CechSigmaProof LateralTheory.E.CechSigma_xy1Pf_Lev

theorem nat_sq {Y X : Scheme.{0}} (g : Y ⟶ X) (O : X.Opens) {ι : Type} (V : ι → X.Opens)
    (hV : ∀ j, V j ≤ O) (n : ℕ)
    (hW : ∀ (j : Fin (n + 1) → ι) x, x ∈ (⨅ k, V (j k)) ↔ ∀ k, x ∈ V (j k))
    (hW' : ∀ (j : Fin (n + 1) → ι) x, x ∈ g ⁻¹ᵁ (⨅ k, V (j k)) ↔ ∀ k, x ∈ g ⁻¹ᵁ V (j k)) :
    Limits.Sigma.desc (cmp (g ⁻¹ᵁ O) (fun j => g ⁻¹ᵁ V j) (fun j => pre_le g (hV j)) _ hW') ≫
        wpMap (sqS g O V hV) n =
      Limits.Sigma.map (fun j : Fin (n + 1) → ι => g ∣_ (⨅ k, V (j k))) ≫
        Limits.Sigma.desc (cmp O V hV _ hW) := by
  apply Sigma.hom_ext
  intro j
  simp only [Sigma.ι_desc_assoc, Sigma.ι_map_assoc, Sigma.ι_desc]
  apply WidePullback.hom_ext
  · intro k
    simp only [wpMap, sqS, Category.assoc, WidePullback.lift_π, Arrow.homMk_left]
    rw [← Category.assoc, cmp_π, cmp_π, Category.assoc, Sigma.ι_map, ← Category.assoc,
      ← Category.assoc]
    congr 1
    rw [← cancel_mono (V (j k)).ι, Category.assoc, morphismRestrict_ι, ← Category.assoc,
      Scheme.homOfLE_ι, Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι]
  · simp only [wpMap, sqS, Category.assoc, WidePullback.lift_base, Arrow.homMk_right]
    rw [← Category.assoc, cmp_base, cmp_base, ← cancel_mono O.ι, Category.assoc, morphismRestrict_ι,
      ← Category.assoc, Scheme.homOfLE_ι, Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι]

end UpperTheory.Cb.RestrictionCovers

open LateralTheory.E.CechSigmaProof LateralTheory.E.CechSigma_xy1Pf_Lev UpperTheory.Cb.RestrictionCovers in
theorem UpperTheory.Cb.cechLevel_iso_sigma_intersections_of_coprod :
    LateralTheory.E.t_E3Cut.Coprod → LateralTheory.E.CechSigma_xy1Pf_Lev.SchemeLevel := by
  intro _ Y X g O ι V hV n
  have hW : ∀ (j : Fin (n + 1) → ι) x, x ∈ (⨅ k, V (j k)) ↔ ∀ k, x ∈ V (j k) :=
    fun j x => mem_iInf_fin (fun k => V (j k)) x
  have hW' : ∀ (j : Fin (n + 1) → ι) x, x ∈ g ⁻¹ᵁ (⨅ k, V (j k)) ↔ ∀ k, x ∈ g ⁻¹ᵁ V (j k) :=
    fun j x => mem_iInf_fin (fun k => V (j k)) (g x)
  exact ⟨(Arrow.isoMk (asIso (Limits.Sigma.desc (cmp (g ⁻¹ᵁ O) (fun j => g ⁻¹ᵁ V j)
    (fun j => pre_le g (hV j)) _ hW'))) (asIso (Limits.Sigma.desc (cmp O V hV _ hW)))
    (nat_sq g O V hV n hW hW')).symm⟩
end
end
