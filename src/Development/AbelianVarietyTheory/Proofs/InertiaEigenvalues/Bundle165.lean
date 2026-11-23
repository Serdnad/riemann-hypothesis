module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle140
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle096
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle119
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
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.FieldTheory.Galois.Infinite
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc.AlmostTrace

variable {l : ℕ} [Fact l.Prime]

theorem Ks_le_Kinf (K : FinExt l) (i : ℕ) : Ks K i ≤ Kinf K := by
  unfold Ks Kinf
  exact sup_le_sup_left (IntermediateField.adjoin.mono ℚ_[l] {x : Om l | x ^ l ^ i = 1}
    {x : Om l | ∃ j : ℕ, x ^ l ^ j = 1} fun x hx => (⟨i, hx⟩ : ∃ j : ℕ, x ^ l ^ j = 1)) _

theorem Ks_mono (K : FinExt l) : Monotone (Ks K) := by
  intro i j hij
  unfold Ks
  refine sup_le_sup_left (IntermediateField.adjoin.mono ℚ_[l] {x : Om l | x ^ l ^ i = 1}
    {x : Om l | x ^ l ^ j = 1} fun x hx => ?_) _
  obtain ⟨c, hc⟩ := pow_dvd_pow l hij
  have hx' : x ^ l ^ i = 1 := hx
  show x ^ l ^ j = 1
  rw [hc, pow_mul, hx', one_pow]

theorem Kinf_eq_iSup (K : FinExt l) : Kinf K = ⨆ i, Ks K i := by
  refine le_antisymm ?_ (iSup_le fun i => Ks_le_Kinf K i)
  have h0 : K0 K ≤ Ks K 0 := by
    unfold Ks
    exact le_sup_left
  unfold Kinf
  refine sup_le (h0.trans (le_iSup (Ks K) 0)) ?_
  rw [IntermediateField.adjoin_le_iff]
  rintro x ⟨j, hj⟩
  have hx : x ∈ Ks K j := by
    unfold Ks
    exact (le_sup_right : IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ l ^ j = 1} ≤ _)
      (IntermediateField.subset_adjoin _ _ hj)
  exact le_iSup (Ks K) j hx

theorem exists_mem_Ks (K : FinExt l) {x : Om l} (hx : x ∈ Kinf K) : ∃ i, x ∈ Ks K i := by
  rw [Kinf_eq_iSup] at hx
  have h : x ∈ ((⨆ i, Ks K i : IntermediateField ℚ_[l] (Om l)) : Set (Om l)) := hx
  rw [IntermediateField.coe_iSup_of_directed (Ks_mono K).directed_le, Set.mem_iUnion] at h
  exact h

theorem Hinf_le_Gj (K : FinExt l) (i : ℕ) : Hinf K ≤ Gj K i := by
  unfold Hinf Gj
  exact IntermediateField.fixingSubgroup_antitone (Ks_le_Kinf K i)

theorem exists_Gj_subset (K : FinExt l) {U : Set (GQ l)} (hU : IsOpen U)
    (hH : (Hinf K : Set (GQ l)) ⊆ U) : ∃ i₀, ∀ i ≥ i₀, (Gj K i : Set (GQ l)) ⊆ U := by
  have hcl : ∀ i, IsClosed ((Gj K i : Set (GQ l))) := fun i =>
    InfiniteGalois.fixingSubgroup_isClosed (Ks K i)
  have hanti : Antitone fun i => ((Gj K i : Set (GQ l))) := fun i j hij =>
    IntermediateField.fixingSubgroup_antitone (Ks_mono K hij)
  have hinter : Uᶜ ∩ ⋂ i, (Gj K i : Set (GQ l)) = ∅ := by
    ext σ
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨hσU, hσ⟩
    apply hσU
    apply hH
    show σ ∈ (Kinf K).fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    obtain ⟨i, hi⟩ := exists_mem_Ks K hx
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 (Set.mem_iInter.1 hσ i) x hi
  obtain ⟨i₀, hi₀⟩ := hU.isClosed_compl.isCompact.elim_directed_family_closed
    (fun i => (Gj K i : Set (GQ l))) hcl (Set.disjoint_iff_inter_eq_empty.mpr hinter) hanti.directed_ge
  refine ⟨i₀, fun i hi σ hσ => ?_⟩
  by_contra hσU
  have hmem : σ ∈ Uᶜ ∩ (Gj K i₀ : Set (GQ l)) := ⟨hσU, hanti hi hσ⟩
  exact Set.disjoint_left.1 hi₀ hmem.1 hmem.2

theorem sum_mem_Kinf (K : FinExt l) (L : IntermediateField ℚ_[l] (Om l)) (S : Finset (GQ l))
    (hS : ∀ s ∈ S, s ∈ Hinf K)
    (hrep : ∀ h ∈ Hinf K, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ L.fixingSubgroup) {b : Om l} (hb : b ∈ L) :
    ∑ s ∈ S, s b ∈ Kinf K := by
  classical
  rw [← InfiniteGalois.fixedField_fixingSubgroup (Kinf K), IntermediateField.mem_fixedField_iff]
  intro h hh
  have hex : ∀ s ∈ S, ∃ t, t ∈ S ∧ t⁻¹ * (h * s) ∈ L.fixingSubgroup := fun s hs =>
    (hrep (h * s) (mul_mem hh (hS s hs))).exists
  choose! φ hφS hφF using hex

  rw [map_sum]
  refine Finset.sum_nbij φ hφS ?_ ?_ ?_
  · intro s₁ hs₁ s₂ hs₂ he
    have h₁ := hφF s₁ hs₁
    have h₂ := hφF s₂ hs₂
    rw [he] at h₁
    have hm : s₁⁻¹ * s₂ ∈ L.fixingSubgroup := by
      have := mul_mem (inv_mem h₁) h₂
      rwa [show ((φ s₂)⁻¹ * (h * s₁))⁻¹ * ((φ s₂)⁻¹ * (h * s₂)) = s₁⁻¹ * s₂ by group] at this
    exact (hrep s₂ (hS s₂ hs₂)).unique ⟨hs₁, hm⟩ ⟨hs₂, by rw [inv_mul_cancel]; exact one_mem _⟩
  · intro t ht
    obtain ⟨s, ⟨hs, hsm⟩, -⟩ := hrep (h⁻¹ * t) (mul_mem (inv_mem hh) (hS t ht))
    refine ⟨s, Finset.mem_coe.2 hs, ?_⟩
    have hm : t⁻¹ * (h * s) ∈ L.fixingSubgroup := by
      have := inv_mem hsm
      rwa [show (s⁻¹ * (h⁻¹ * t))⁻¹ = t⁻¹ * (h * s) by group] at this
    exact (hrep (h * s) (mul_mem hh (hS s hs))).unique ⟨hφS s hs, hφF s hs⟩ ⟨ht, hm⟩
  · intro s hs
    have hfix := (IntermediateField.mem_fixingSubgroup_iff _ _).1 (hφF s hs) b hb
    have key : (φ s) (((φ s)⁻¹ * (h * s)) b) = h (s b) := by
      rw [← AlgEquiv.mul_apply, mul_inv_cancel_left, AlgEquiv.mul_apply]
    rw [hfix] at key
    exact key.symm

theorem exists_finite_level (K : FinExt l) (L : IntermediateField ℚ_[l] (Om l)) (S : Finset (GQ l))
    (hS : ∀ s ∈ S, s ∈ Hinf K)
    (hrep : ∀ h ∈ Hinf K, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ L.fixingSubgroup) :
    ∃ L' : FinExt l, L'.1 ≤ L ∧ ∃ i₀, ∀ i ≥ i₀, ∀ h ∈ Gj K i,
      ∃! s, s ∈ S ∧ s⁻¹ * h ∈ (L'.1 ⊔ Ks K i).fixingSubgroup := by
  classical
  have hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → ∃ x ∈ L, (s⁻¹ * t) x ≠ x := by
    intro s hs t ht hst
    by_contra hne
    push Not at hne
    apply hst
    have hmem : s⁻¹ * t ∈ L.fixingSubgroup := (IntermediateField.mem_fixingSubgroup_iff _ _).2 hne
    exact (hrep t (hS t ht)).unique ⟨hs, hmem⟩ ⟨ht, by rw [inv_mul_cancel]; exact one_mem _⟩
  choose! xf hxL hxne using hsep
  let T : Finset (Om l) := ((S ×ˢ S).filter fun p => p.1 ≠ p.2).image fun p => xf p.1 p.2
  have hTmem : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → xf s t ∈ (T : Set (Om l)) := by
    intro s hs t ht hst
    simp only [T, Finset.coe_image, Finset.coe_filter]
    exact ⟨(s, t), ⟨Finset.mem_product.2 ⟨hs, ht⟩, hst⟩, rfl⟩
  let L' : FinExt l := ⟨IntermediateField.adjoin ℚ_[l] (T : Set (Om l)),
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x⟩
  have hL'L : L'.1 ≤ L := by
    show IntermediateField.adjoin ℚ_[l] (T : Set (Om l)) ≤ L
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    simp only [T, Finset.coe_image, Finset.coe_filter, Set.mem_image] at hx
    obtain ⟨p, ⟨hp, hpne⟩, rfl⟩ := hx
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.1 hp
    exact hxL p.1 hp1 p.2 hp2 hpne
  have : FiniteDimensional ℚ_[l] L'.1 := L'.2
  let U : Set (GQ l) := ⋃ s ∈ S, {σ | s⁻¹ * σ ∈ L'.1.fixingSubgroup}
  have hUo : IsOpen U := isOpen_biUnion fun s _ =>
    (IntermediateField.fixingSubgroup_isOpen L'.1).preimage (continuous_const.mul continuous_id)
  have hHU : (Hinf K : Set (GQ l)) ⊆ U := by
    intro σ hσ
    obtain ⟨s, ⟨hs, hsm⟩, -⟩ := hrep σ hσ
    exact Set.mem_biUnion hs (IntermediateField.fixingSubgroup_antitone hL'L hsm)
  obtain ⟨i₀, hi₀⟩ := exists_Gj_subset K hUo hHU
  refine ⟨L', hL'L, i₀, fun i hi h hh => ?_⟩
  obtain ⟨s, hs, hsm⟩ := Set.mem_iUnion₂.1 (hi₀ i hi hh)
  have hsG : s⁻¹ * h ∈ Gj K i := mul_mem (inv_mem (Hinf_le_Gj K i (hS s hs))) hh
  refine ⟨s, ⟨hs, ?_⟩, ?_⟩
  · rw [IntermediateField.fixingSubgroup_sup]
    exact ⟨hsm, hsG⟩
  · rintro t ⟨ht, htm⟩
    by_contra hts
    have htm' : t⁻¹ * h ∈ L'.1.fixingSubgroup :=
      IntermediateField.fixingSubgroup_antitone le_sup_left htm
    have hm : t⁻¹ * s ∈ L'.1.fixingSubgroup := by
      have := mul_mem htm' (inv_mem hsm)
      rwa [show t⁻¹ * h * (s⁻¹ * h)⁻¹ = t⁻¹ * s by group] at this
    have hxT : xf t s ∈ L'.1 := IntermediateField.subset_adjoin _ _ (hTmem t ht s hs hts)
    exact hxne t ht s hs hts ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hm _ hxT)

theorem trace_almost_onto_of_levels
    (hd : ∀ (K L' : FinExt l) (ε : ℝ), 0 < ε → ∃ i₀ : ℕ, ∀ i ≥ i₀, ∀ S : Finset (GQ l),
      (∀ s ∈ S, s ∈ Gj K i) →
      (∀ h ∈ Gj K i, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ (L'.1 ⊔ Ks K i).fixingSubgroup) →
      ∃ b : Om l, b ∈ L'.1 ⊔ Ks K i ∧ ‖b‖ ≤ 1 ∧ 1 - ε ≤ ‖∑ s ∈ S, s b‖)
    (K : FinExt l) (L : IntermediateField ℚ_[l] (Om l)) (S : Finset (GQ l)) (hKL : Kinf K ≤ L)
    (hS : ∀ s ∈ S, s ∈ Hinf K)
    (hrep : ∀ h ∈ Hinf K, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ L.fixingSubgroup)
    (a : Om l) (ha : a ∈ Kinf K) (ha1 : ‖a‖ < 1) :
    ∃ b : Om l, b ∈ L ∧ ‖b‖ ≤ 1 ∧ ∑ s ∈ S, s b = a := by
  classical
  by_cases ha0 : a = 0
  · exact ⟨0, zero_mem _, by simp, by simp [ha0]⟩
  obtain ⟨L', hL'L, i₀, hi₀⟩ := exists_finite_level K L S hS hrep
  have hε : 0 < 1 - ‖a‖ := by linarith
  obtain ⟨i₁, hi₁⟩ := hd K L' (1 - ‖a‖) hε
  obtain ⟨b₀, hb₀, hb₀1, htr⟩ := hi₁ (max i₀ i₁) (le_max_right _ _) S
    (fun s hs => Hinf_le_Gj K _ (hS s hs)) (hi₀ (max i₀ i₁) (le_max_left _ _))
  have hb₀L : b₀ ∈ L := (sup_le hL'L ((Ks_le_Kinf K _).trans hKL)) hb₀
  have htK : ∑ s ∈ S, s b₀ ∈ Kinf K := sum_mem_Kinf K L S hS hrep hb₀L
  set t := ∑ s ∈ S, s b₀ with ht
  have hta : ‖a‖ ≤ ‖t‖ := by linarith
  have ht0 : t ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hta
    exact ha0 (norm_le_zero_iff.1 hta)
  have hc : a / t ∈ Kinf K := div_mem ha htK
  refine ⟨a / t * b₀, mul_mem (hKL hc) hb₀L, ?_, ?_⟩
  · rw [norm_mul, norm_div]
    have h1 : ‖a‖ / ‖t‖ ≤ 1 := (div_le_one (norm_pos_iff.2 ht0)).2 hta
    calc ‖a‖ / ‖t‖ * ‖b₀‖ ≤ 1 * 1 := mul_le_mul h1 hb₀1 (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · have hfix : ∀ s ∈ S, s (a / t) = a / t := fun s hs =>
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 (hS s hs) _ hc
    rw [Finset.sum_congr rfl fun s hs => by rw [map_mul, hfix s hs], ← Finset.mul_sum,
      ← ht, div_mul_cancel₀ a ht0]

end GlobalTheory.Cyc.AlmostTrace
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial

noncomputable section

namespace GlobalTheory.Cyc

variable {l : ℕ} [Fact l.Prime]

theorem descent_act_chiC {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (hact : IsActC act)
    (χ : GQ l →* ℚ_[l]ˣ) (i : ℤ) (g h : GQ l) : act g (chiC χ i h) = chiC χ i h := by
  unfold chiC
  rw [IsScalarTower.algebraMap_apply ℚ_[l] (Om l) (PadicComplex l), ← PadicComplex.coe_eq, hact.1,
    AlgEquiv.commutes]

theorem descent_chiC_mul (χ : GQ l →* ℚ_[l]ˣ) (i : ℤ) (g h : GQ l) :
    chiC χ i (g * h) = chiC χ i g * chiC χ i h := by
  unfold chiC
  rw [map_mul, mul_zpow, Units.val_mul, map_mul]

theorem descent_chiC_pow (χ : GQ l →* ℚ_[l]ˣ) (i : ℤ) (n : ℕ) (g : GQ l) :
    chiC χ (i * n) g = chiC χ i g ^ n := by
  unfold chiC
  rw [zpow_mul, zpow_natCast, Units.val_pow_eq_pow_val, map_pow]

theorem descent_chiC_zero (χ : GQ l →* ℚ_[l]ˣ) (g : GQ l) : chiC χ 0 g = 1 := by
  simp [chiC]

theorem descent_chiC_one (χ : GQ l →* ℚ_[l]ˣ) (i : ℤ) : chiC χ i 1 = 1 := by
  simp [chiC]

theorem descent_conj {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (hact : IsActC act)
    (χ : GQ l →* ℚ_[l]ˣ) (i : ℤ) (H : Subgroup (GQ l)) (y : PadicComplex l)
    (hy : ∀ g ∈ H, chiC χ i g * act g y = y) :
    ∃ F : GQ l ⧸ H → PadicComplex l, F ((1 : GQ l) : GQ l ⧸ H) = y ∧
      (∀ q, F q = 0 → y = 0) ∧ ∀ (g : GQ l) q, chiC χ i g * act g (F q) = F (g • q) := by
  have key : ∀ g σ : GQ l, chiC χ i (g * σ) * act (g * σ) y
      = chiC χ i g * act g (chiC χ i σ * act σ y) := by
    intro g σ
    rw [descent_chiC_mul, map_mul act, map_mul (act g), descent_act_chiC hact, mul_assoc]
    rfl
  refine ⟨fun q => Quotient.liftOn' q (fun σ => chiC χ i σ * act σ y) ?_, ?_, ?_, ?_⟩
  · intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab
    have := key a (a⁻¹ * b)
    rw [hy _ hab, mul_inv_cancel_left] at this
    exact this.symm
  · change chiC χ i 1 * act 1 y = y
    rw [descent_chiC_one, map_one, one_mul]
    rfl
  · intro q
    induction q using QuotientGroup.induction_on with
    | H σ =>
      intro h
      change chiC χ i σ * act σ y = 0 at h
      have := key σ⁻¹ σ
      rw [h, map_zero, mul_zero, inv_mul_cancel, descent_chiC_one, map_one, one_mul] at this
      exact this
  · intro g q
    induction q using QuotientGroup.induction_on with
    | H σ => exact (key g σ).symm

theorem invariants_of_subgroup {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)}
    (hact : IsActC act) (χ : GQ l →* ℚ_[l]ˣ) (G : Subgroup (GQ l))
    (E : IntermediateField ℚ_[l] (Om l))
    (hG : ∀ (i : ℤ) (y : PadicComplex l), (∀ g ∈ G, chiC χ i g * act g y = y) →
      (i ≠ 0 → y = 0) ∧ (i = 0 → y ∈ inC E))
    (K : FinExt l) (i : ℤ) (y : PadicComplex l) (hy : ∀ g ∈ GK K, chiC χ i g * act g y = y) :
    (i ≠ 0 → y = 0) ∧ (i = 0 → y ∈ inC K.1) := by
  classical
  haveI := K.2
  haveI : IsGalois ℚ_[l] (Om l) := {}
  haveI : (GK K).FiniteIndex := ⟨by
    rw [GK, ← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact Module.finrank_pos.ne'⟩
  haveI : Fintype (GQ l ⧸ GK K) := Fintype.ofFinite _
  obtain ⟨F, hF1, hF0, hF⟩ := descent_conj hact χ i (GK K) y hy
  constructor
  · intro hi
    have hN := (hG (i * (Fintype.card (GQ l ⧸ GK K) : ℕ)) (∏ q, F q) (fun g _ => by
      rw [descent_chiC_pow, map_prod, ← Finset.card_univ, ← Finset.prod_const,
        ← Finset.prod_mul_distrib]
      simp only [hF]
      exact Equiv.prod_comp (MulAction.toPerm g) F)).1
      (mul_ne_zero hi (by exact_mod_cast Fintype.card_ne_zero))
    obtain ⟨q, -, hq⟩ := Finset.prod_eq_zero_iff.1 hN
    exact hF0 q hq
  · rintro rfl
    simp only [descent_chiC_zero, one_mul] at hF hy
    set P : (PadicComplex l)[X] := ∏ q, (X - C (F q)) with hP
    have hmon : P.Monic := monic_prod_of_monic _ _ fun q _ => monic_X_sub_C _
    have hmap : ∀ g : GQ l, P.map (act g : PadicComplex l →+* PadicComplex l) = P := by
      intro g
      rw [hP, Polynomial.map_prod]
      simp only [Polynomial.map_sub, map_X, map_C, RingHom.coe_coe, hF]
      exact Equiv.prod_comp (MulAction.toPerm g) fun q => (X - C (F q) : (PadicComplex l)[X])
    have hlift : P ∈ lifts (algebraMap (Om l) (PadicComplex l)) := by
      rw [lifts_iff_coeff_lifts]
      intro n
      obtain ⟨x, -, hx⟩ := (hG 0 (P.coeff n) (fun g _ => by
        rw [descent_chiC_zero, one_mul]
        conv_rhs => rw [← hmap g, coeff_map]
        rfl)).2 rfl
      exact ⟨x, hx⟩
    obtain ⟨Q, hQ, -, hQm⟩ := lifts_and_degree_eq_and_monic hlift hmon
    have hint : IsIntegral (Om l) y := by
      refine ⟨Q, hQm, ?_⟩
      rw [← eval_map, hQ, hP, eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ ((1 : GQ l) : GQ l ⧸ GK K)) (by simp [hF1])
    obtain ⟨x, rfl⟩ := minpoly.mem_range_of_degree_eq_one (Om l) y
      (IsAlgClosed.degree_eq_one_of_irreducible _ (minpoly.irreducible hint))
    refine ⟨x, ?_, rfl⟩
    rw [← InfiniteGalois.fixedField_fixingSubgroup K.1]
    refine (IntermediateField.mem_fixedField_iff _ _).2 fun g hg => ?_
    have := hy g hg
    rw [← PadicComplex.coe_eq, hact.1] at this
    exact (algebraMap (Om l) (PadicComplex l)).injective this

end GlobalTheory.Cyc
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc

theorem eventually_apply_eq {l : ℕ} [Fact l.Prime] (x : Om l) (g₀ : GQ l) :
    ∀ᶠ g : GQ l in nhds g₀, g x = g₀ x := by
  have hS := stabilizer_isOpen_of_isIntegral (K := ℚ_[l]) x
  have hc : Continuous fun g : GQ l => g₀⁻¹ * g := continuous_const.mul continuous_id
  have hmem : (fun g : GQ l => g₀⁻¹ * g) g₀ ∈ (MulAction.stabilizer (GQ l) x : Set (GQ l)) := by
    simp
  filter_upwards [hc.continuousAt.preimage_mem_nhds (hS.mem_nhds hmem)] with g hg
  have hg' : (g₀⁻¹ * g) x = x := hg
  have := congrArg g₀ hg'
  simpa [AlgEquiv.mul_apply] using this

theorem IsActC.continuous_orbit (l : ℕ) [Fact l.Prime]
    (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (h : IsActC act) (y : PadicComplex l) :
    Continuous (fun g => act g y) := by
  obtain ⟨hext, hiso⟩ := h
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨x, hx⟩ : ∃ x : Om l, dist y (x : PadicComplex l) < ε / 2 :=
    UniformSpace.Completion.denseRange_coe.exists_dist_lt y (half_pos hε)
  filter_upwards [eventually_apply_eq x g₀] with g hg
  have h1 : act g y - act g₀ y = act g (y - x) - act g₀ (y - x) := by
    rw [map_sub, map_sub, hext g x, hext g₀ x, hg]
    ring
  rw [dist_eq_norm, h1]
  calc ‖act g (y - x) - act g₀ (y - x)‖ ≤ ‖act g (y - x)‖ + ‖act g₀ (y - x)‖ := norm_sub_le _ _
    _ = 2 * ‖y - x‖ := by rw [hiso, hiso]; ring
    _ < ε := by rw [← dist_eq_norm]; linarith

end GlobalTheory.Cyc
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc

noncomputable def cycChar (l : ℕ) [Fact l.Prime] : GQ l →* ℚ_[l]ˣ :=
  (Units.map (PadicInt.Coe.ringHom (p := l)).toMonoidHom).comp
    ((cyclotomicCharacter (Om l) l).comp (MulSemiringAction.toRingAut (GQ l) (Om l)))

theorem _root_.GlobalTheory.Cyc.isCyc_cycChar (l : ℕ) [Fact l.Prime] :
    _root_.GlobalTheory.Cyc.IsCyc (_root_.GlobalTheory.Cyc.cycChar l) := by
  intro g m ζ h
  set x : ℤ_[l] := (cyclotomicCharacter (_root_.Formalism.BasicNotions.Loc.Om l) l (MulSemiringAction.toRingAut _ _ g) : ℤ_[l])
    with hx
  refine ⟨(PadicInt.toZModPow m x).val, ?_, ?_⟩
  · have hmem : x - ((PadicInt.toZModPow m x).val : ℤ_[l]) ∈ Ideal.span {(l : ℤ_[l]) ^ m} := by
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val,
        sub_self]
    have h2 : ‖((x - ((PadicInt.toZModPow m x).val : ℤ_[l]) : ℤ_[l]) : ℚ_[l])‖ ≤
        (l : ℝ) ^ (-(m : ℤ)) :=
      (PadicInt.norm_le_pow_iff_mem_span_pow _ m).2 hmem
    have h3 : ((_root_.GlobalTheory.Cyc.cycChar l g : ℚ_[l]ˣ) : ℚ_[l]) = (x : ℚ_[l]) := rfl
    rw [h3]
    rw [PadicInt.coe_sub, PadicInt.coe_natCast] at h2
    exact h2
  · exact cyclotomicCharacter.spec l (MulSemiringAction.toRingAut _ _ g) ζ h

theorem _root_.GlobalTheory.Cyc.exists_isCyc :
    ∀ (l : ℕ) [Fact l.Prime], ∃ χ : _root_.Formalism.BasicNotions.Loc.GQ l →* ℚ_[l]ˣ, _root_.GlobalTheory.Cyc.IsCyc χ :=
  fun l _ => ⟨_root_.GlobalTheory.Cyc.cycChar l, _root_.GlobalTheory.Cyc.isCyc_cycChar l⟩

end GlobalTheory.Cyc
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.unramifiedQuadratic_trace_eq_add_star : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E], ∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y := by
  first | exact @GlobalTheory.trace_eq_add_star | exact GlobalTheory.trace_eq_add_star | (intros; apply GlobalTheory.trace_eq_add_star <;> assumption)
end

section

open GlobalTheory.UnitLemma Matrix MeasureTheory

theorem _root_.GlobalTheory.T.mem_range_algebraMap_of_star_eq : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [GlobalTheory.JR.Unram F E] (y : E), star y = y → ∃ x : F, algebraMap F E x = y := by
  first | exact @GlobalTheory.JR.Unram.mem_range_of_star_eq | exact GlobalTheory.JR.Unram.mem_range_of_star_eq | (intros; apply GlobalTheory.JR.Unram.mem_range_of_star_eq <;> assumption)
end

section

open GlobalTheory.PMonE

namespace GlobalTheory

theorem PMonE.generalLemma_allOrders : ∀ N : ℕ, GLOnto N ∧ GLCount N := by
  intro N
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact GlobalTheory.T.additiveSystem_surjectivity_and_count_order_zero
  · exact ⟨GlobalTheory.T.additiveSystemIntegralSurjectivity_of_one N hN GlobalTheory.T.additiveSystem_generalLemma_orderOne.1, GlobalTheory.T.additiveSystemIntegralSolutionCount_of_order_one N hN GlobalTheory.T.additiveSystem_generalLemma_orderOne.2⟩

end GlobalTheory
end
