module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair ValuativeRel NumberField Filter
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.SplitApprox

variable {D : D7}

theorem cA_tmul (a : AF D.host.F) (x : D.host.E) : cA D (a ⊗ₜ[D.host.F] x) = a ⊗ₜ[D.host.F] star x := rfl

theorem cA_cA (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rw [cA_tmul, cA_tmul, star_star]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem finPart_tmul (a : AF D.host.F) (x : D.host.E) :
    finPart D (a ⊗ₜ[D.host.F] x) = sndA D.host.F a ⊗ₜ[D.host.F] x := rfl

theorem approx_gen {F A B E : Type} [Field F] [CharZero F] [CommRing A] [CommRing B] [CommRing E] [Algebra F A]
    [Algebra F B] [Algebra F E] (φ : A → B) (σ : E →+* E) (fp : A ⊗[F] E →+* B ⊗[F] E) (c : A ⊗[F] E →+* A ⊗[F] E)
    (hfp : ∀ a x, fp (a ⊗ₜ[F] x) = φ a ⊗ₜ[F] x) (h1 : φ 1 = 1) (hc : ∀ a x, c (a ⊗ₜ[F] x) = a ⊗ₜ[F] σ x)
    (O : Set B) (I : AddSubgroup (B ⊗[F] E)) (hI : ∀ b ∈ O, ∀ x : E, IsIntegral ℤ x → b ⊗ₜ[F] x ∈ I)
    (hE : ∀ x : E, ∃ m : ℤ, m ≠ 0 ∧ IsIntegral ℤ (m • x)) (N : ℕ)
    (hB : ∀ y : B, ∃ (f : F) (β : B), β ∈ O ∧ y = algebraMap F B f + N • β) (z : A ⊗[F] E) :
    ∃ x : E, ∃ a ∈ I, ∃ a' ∈ I, fp (z - 1 ⊗ₜ[F] x) = N * a ∧ fp (c z - c (1 ⊗ₜ[F] x)) = N * a' := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, zero_mem _, 0, zero_mem _, by simp, by simp⟩
  | add x y hx hy =>
    obtain ⟨d, a, ha, a', ha', h, h'⟩ := hx
    obtain ⟨e, b, hb, b', hb', g, g'⟩ := hy
    refine ⟨d + e, a + b, add_mem ha hb, a' + b', add_mem ha' hb', ?_, ?_⟩
    · rw [mul_add, ← h, ← g, ← map_add (f := _), TensorProduct.tmul_add]; congr 1; ring
    · rw [mul_add, ← h', ← g', ← map_add fp, TensorProduct.tmul_add, map_add c, map_add c]; congr 1; ring
  | tmul a x =>
    obtain ⟨m, hm, hx⟩ := hE x
    have hm' : (m : F) ≠ 0 := Int.cast_ne_zero.2 hm
    obtain ⟨f, β, hβ, hy⟩ := hB ((m : F)⁻¹ • φ a)
    have key : ∀ x : E, fp (a ⊗ₜ[F] x - 1 ⊗ₜ[F] (f • (m • x))) = N * (β ⊗ₜ[F] (m • x)) := by
      intro x
      have e2 : φ a ⊗ₜ[F] x = ((m : F)⁻¹ • φ a) ⊗ₜ[F] (m • x) := by
        rw [TensorProduct.smul_tmul, ← Int.cast_smul_eq_zsmul F, smul_smul, inv_mul_cancel₀ hm', one_smul]
      rw [map_sub, hfp, hfp, h1, e2, hy, TensorProduct.add_tmul, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul f, add_sub_cancel_left, ← TensorProduct.smul_tmul', nsmul_eq_mul]
    have hx' : IsIntegral ℤ (m • σ x) := by
      rw [← map_zsmul]
      exact hx.map σ.toIntAlgHom
    refine ⟨f • (m • x), _, hI _ hβ _ hx, _, hI _ hβ _ hx', key x, ?_⟩
    rw [hc, ← TensorProduct.smul_tmul, hc, TensorProduct.smul_tmul, map_zsmul]
    exact key _

theorem cancel_gen {F R : Type} [Field F] [CharZero F] [CommRing R] [Algebra F R] {N : ℕ} (hN : 0 < N) {a b : R}
    (h : (N : R) * a = N * b) : a = b := by
  have : IsUnit (N : R) := by
    have := (IsUnit.mk0 (N : F) (Nat.cast_ne_zero.2 hN.ne')).map (algebraMap F R)
    rwa [map_natCast] at this
  exact this.mul_left_cancel h

theorem tmul_mem {a : Af D.host.F} (ha : a ∈ intAf D.host.F) {x : D.host.E} (hx : IsIntegral ℤ x) :
    a ⊗ₜ[D.host.F] x ∈ intAE D :=
  AddSubgroup.subset_closure ⟨a, ha, ⟨x, hx⟩, rfl⟩

theorem mul_mem_intAE {a b : Af D.host.F ⊗[D.host.F] D.host.E} (ha : a ∈ intAE D) (hb : b ∈ intAE D) :
    a * b ∈ intAE D := by
  induction ha using AddSubgroup.closure_induction with
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx
  | mem x hx =>
    induction hb using AddSubgroup.closure_induction with
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | neg x _ hx => rw [mul_neg]; exact neg_mem hx
    | mem y hy =>
      obtain ⟨a, ha, x, rfl⟩ := hx
      obtain ⟨b, hb, y, rfl⟩ := hy
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      refine tmul_mem (fun v => ?_) (x.2.mul y.2)
      rw [map_mul]; exact mul_mem (ha v) (hb v)

theorem approx (N : ℕ) (hN : 0 < N) (z : AE D) : ∃ c : D.host.E, ∃ A ∈ intAE D, ∃ A' ∈ intAE D,
    finPart D (z - incA D c) = N * A ∧ finPart D (cA D z - incA D (star c)) = N * A' :=
  approx_gen (F := D.host.F) (sndA D.host.F) (starRingEnd D.host.E) (finPart D) (cA D) finPart_tmul (map_one _) cA_tmul
    (intAf D.host.F) (intAE D) (fun _ hb _ hx => tmul_mem hb hx)
    (fun x => ((IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2
      (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x)).exists_integral_multiple) N
    (GlobalTheory.AdLat.strong_approximation_mod_nat D.host.F N hN).1 z

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_le (p : SplitPt D k) (N : ℕ) (hN : 0 < N) (z : AE D) (A : Af D.host.F ⊗[D.host.F] D.host.E)
    (hA : A ∈ intAE D) (h : finPart D z = N * A) : valuation k (p.pr z) ≤ valuation k (N : k) := by
  have hNE : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hNk : (N : k) ≠ 0 := by
    have := (map_ne_zero (p.pr.comp (incA D))).2 hNE
    rwa [map_natCast] at this
  have he : finPart D p.e ∈ intAE D := by
    have := (p.int_iff 1).1 (one_mem _)
    rwa [← map_one p.pr, p.sec_pr, mul_one] at this
  have h0 : (N : AE D) * p.sec (p.pr z / N) = p.e * z := by
    rw [← p.sec_pr, ← nsmul_eq_mul, ← AddMonoidHom.map_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ hNk]
  have h1 := congrArg (finPart D) h0
  rw [RingHom.map_mul, RingHom.map_mul, h, mul_left_comm] at h1
  have h1' : finPart D (N : AE D) = N := map_natCast (finPart D) N
  rw [h1'] at h1
  have h2 := cancel_gen (F := D.host.F) hN h1
  have h3 : p.pr z / N ∈ 𝒪[k] := (p.int_iff _).2 (by rw [h2]; exact mul_mem_intAE he hA)
  have h4 : valuation k (p.pr z / N) ≤ 1 := h3
  have h5 : p.pr z = N * (p.pr z / N) := (mul_div_cancel₀ _ hNk).symm
  rw [h5, map_mul]
  exact mul_le_of_le_one_right' h4

theorem exists_nat (q : Unif k) : valuation k ((q.1 : 𝒪[k]) : k) < 1 ∧
    ∃ N : ℕ, 0 < N ∧ valuation k (N : k) < valuation k ((q.1 : 𝒪[k]) : k) := by
  have hlt : ∀ x : 𝒪[k], ¬ IsUnit x → valuation k (x : k) < 1 := fun x hx =>
    Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 hx
  have hq := hlt _ q.2.not_isUnit
  refine ⟨hq, ?_⟩
  classical
  letI := Fintype.ofFinite (IsLocalRing.ResidueField 𝒪[k])
  set Q := Fintype.card (IsLocalRing.ResidueField 𝒪[k])
  have hQ : (Q : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    exact FiniteField.cast_card_eq_zero _
  rw [q.2.maximalIdeal_eq, Ideal.mem_span_singleton] at hQ
  obtain ⟨r, hr⟩ := hQ
  have hr' : (Q : k) = (q.1 : k) * r := by exact_mod_cast congrArg (fun x : 𝒪[k] => (x : k)) hr
  have hle : valuation k (Q : k) ≤ valuation k ((q.1 : 𝒪[k]) : k) := by
    rw [hr', map_mul]; exact mul_le_of_le_one_right' r.2
  have hq0 : 0 < valuation k ((q.1 : 𝒪[k]) : k) := by
    rw [Valuation.pos_iff]
    exact fun h => q.2.ne_zero (Subtype.ext h)
  refine ⟨Q * Q, Nat.mul_pos Fintype.card_pos Fintype.card_pos, ?_⟩
  rw [Nat.cast_mul, map_mul]
  exact (mul_le_mul' hle hle).trans_lt (mul_lt_of_lt_one_right hq0 hq)

theorem exists_unif_unit : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (q : Unif k), ∃ c : D.host.E, valuation k (p.pr (incA D c)) = valuation k ((q.1 : 𝒪[k]) : k) ∧ valuation k (p.pr (incA D (star c))) = 1 := by
  intro D k _ _ _ _ p q
  obtain ⟨hq, N, hN, hNq⟩ := exists_nat q
  have hs : p.sec 1 = p.e := by rw [← map_one p.pr, p.sec_pr, mul_one]
  have he : p.pr p.e = 1 := by rw [← hs, p.pr_sec]
  have hce : p.pr (cA D p.e) = 0 := by
    have h : p.e * cA D p.e = 0 := p.split.2.1
    have := congrArg p.pr h
    rwa [map_mul, he, one_mul, map_zero] at this
  have hcq : ∀ a, p.pr (cA D (p.sec a)) = 0 := fun a => by
    have h : p.sec a = p.e * p.sec a := by rw [← p.sec_pr, p.pr_sec]
    rw [h, map_mul, map_mul, hce, zero_mul]
  obtain ⟨c, A, hA, A', hA', h, h'⟩ := approx N hN (p.sec (q.1 : k) + cA D p.e)
  have v1 := val_le p N hN _ A hA h
  have v2 := val_le p N hN _ A' hA' h'
  rw [map_sub, map_add (f := _), p.pr_sec, hce, add_zero] at v1
  rw [map_sub, map_add (f := _), map_add (f := _), hcq, cA_cA, he, zero_add] at v2
  refine ⟨c, ?_, ?_⟩
  · exact Valuation.map_eq_of_sub_lt _ (by rw [Valuation.map_sub_swap]; exact v1.trans_lt hNq)
  · rw [← map_one (valuation k)]
    exact Valuation.map_eq_of_sub_lt _ (by rw [Valuation.map_sub_swap, map_one]; exact v2.trans_lt (hNq.trans hq))

end GlobalTheory.FinPl.SplitApprox
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl

open IsDedekindDomain NumberField
open scoped TensorProduct

namespace GlobalTheory.FinPl

section General

variable {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V]

theorem exists_int_smul_mem_of_mem_span (M : Submodule (𝓞 E) V) {y : V}
    (hy : y ∈ Submodule.span E (M : Set V)) : ∃ c : ℤ, c ≠ 0 ∧ c • y ∈ M := by
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h1 : (a * b) • x = b • (a • x) := by rw [mul_comm, mul_smul]
    have h2 : (a * b) • y = a • (b • y) := by rw [mul_smul]
    rw [smul_add, h1, h2]
    exact M.add_mem (zsmul_mem hax b) (zsmul_mem hby a)
  | smul e x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨c, hc, hint⟩ := exists_integral_multiples ℤ ℚ ({e} : Finset E)
    have he : IsIntegral ℤ (c • e) := hint e (by simp)
    refine ⟨c * a, mul_ne_zero hc ha, ?_⟩
    obtain ⟨o, ho⟩ : ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = c • e := ⟨⟨c • e, he⟩, rfl⟩
    have h : (c * a) • (e • x) = o • (a • x) := by
      rw [← algebraMap_smul E o (a • x), ho, mul_smul, smul_comm a e x, smul_assoc]
    rw [h]
    exact M.smul_mem o hax

theorem exists_int_smul_le (L M : Submodule (𝓞 E) V) (hL : L.FG)
    (hM : Submodule.span E (M : Set V) = ⊤) : ∃ d : ℤ, d ≠ 0 ∧ ∀ x ∈ L, d • x ∈ M := by
  classical
  obtain ⟨G, rfl⟩ := hL
  have hg : ∀ g ∈ G, ∃ c : ℤ, c ≠ 0 ∧ c • g ∈ M := fun g _ =>
    exists_int_smul_mem_of_mem_span M (by rw [hM]; trivial)
  choose! c hc0 hcM using hg
  refine ⟨∏ g ∈ G, c g, Finset.prod_ne_zero_iff.2 hc0, fun x hx => ?_⟩
  let N : Submodule (𝓞 E) V :=
    { carrier := {y | (∏ g ∈ G, c g) • y ∈ M}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, smul_add] at *; exact M.add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun r y hy => by
        simp only [Set.mem_setOf_eq] at *
        rw [smul_comm]; exact M.smul_mem r hy }
  have hle : Submodule.span (𝓞 E) (G : Set V) ≤ N := by
    rw [Submodule.span_le]
    intro g hg
    show (∏ g ∈ G, c g) • g ∈ M
    rw [← Finset.mul_prod_erase G c hg, mul_comm, mul_smul]
    exact zsmul_mem (hcM g hg) _
  exact hle hx

end General

variable {D : D7}

theorem finite_places_int (d : ℤ) (hd : d ≠ 0) :
    {v : Pl D | ((d : 𝓞 D.host.F)) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {((d : 𝓞 D.host.F))} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hd
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem pairA_tmul_int_gen {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (d : ℤ) (hd : d ≠ 0)
    (α : Af F) (e : E) :
    pairA F 0 α ⊗ₜ[F] (1 * e) = pairA F 0 ((d : F)⁻¹ • α) ⊗ₜ[F] (1 * (d • e)) := by
  have hdF : (d : F) ≠ 0 := Int.cast_ne_zero.2 hd
  have h : (d : F) • pairA F 0 ((d : F)⁻¹ • α) = pairA F 0 α := by
    have h1 : (d : F) • pairA F 0 ((d : F)⁻¹ • α) = pairA F 0 ((d : F) • (d : F)⁻¹ • α) :=
      Prod.ext (smul_zero (d : F)) rfl
    rw [h1, smul_smul, mul_inv_cancel₀ hdF, one_smul]
  rw [one_mul, one_mul, ← Int.cast_smul_eq_zsmul F, ← TensorProduct.smul_tmul, h]

theorem latV_le_of_int_smul (S : HSp D) (L M : Lat S) (d : ℤ) (hd : d ≠ 0)
    (hLM : ∀ x ∈ L, d • x ∈ M) (v : Pl D) (hv : ((d : 𝓞 D.host.F)) ∉ v.asIdeal) :
    latV S L (· = v) ≤ latV S M (· = v) := by
  rw [latV, latMul, AddSubgroup.closure_le]
  rintro y ⟨α, hα, hsupp, a, ha, x, hx, rfl⟩
  rw [Set.mem_singleton_iff] at ha
  subst ha
  have hval : Valued.v (algebraMap D.host.F (v.adicCompletion D.host.F) (d : D.host.F)) = 1 := by
    have h1 := (v.valuation_eq_one_iff_notMem (K := D.host.F)).mpr hv
    have h2 := v.valuedAdicCompletion_eq_valuation' (K := D.host.F) ((d : D.host.F))
    have h4 : (((d : 𝓞 D.host.F)) : D.host.F) = ((d : D.host.F)) :=
      map_intCast (algebraMap (𝓞 D.host.F) D.host.F) _
    exact h2.trans (h4 ▸ h1)
  apply AddSubgroup.subset_closure
  refine ⟨((d : D.host.F))⁻¹ • α, ?_, ?_, 1, rfl, d • x, hLM x hx, ?_⟩
  · intro w
    rw [map_smul]
    by_cases hw : w = v
    · subst hw
      have hαw := hα w
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hαw ⊢
      rw [Algebra.smul_def, map_mul, map_inv₀, map_inv₀, hval, inv_one, one_mul]
      exact hαw
    · rw [hsupp w hw, smul_zero]
      exact zero_mem _
  · intro w hw
    rw [map_smul, hsupp w hw, smul_zero]
  · funext i
    exact pairA_tmul_int_gen d hd α (x i)

theorem latV_eq_off_finite : ∀ (D : D7) (S : HSp D) (L M : Lat S), Submodule.IsFullLattice D.host.E L →
    Submodule.IsFullLattice D.host.E M → ∃ T : Finset (Pl D), ∀ v, v ∉ T → latV S L (· = v) = latV S M (· = v) := by
  intro D S L M hL hM
  obtain ⟨d₁, hd₁, h₁⟩ := exists_int_smul_le L M hL.fg hM.span_eq_top
  obtain ⟨d₂, hd₂, h₂⟩ := exists_int_smul_le M L hM.fg hL.span_eq_top
  have hd : d₁ * d₂ ≠ 0 := mul_ne_zero hd₁ hd₂
  refine ⟨(finite_places_int (D := D) (d₁ * d₂) hd).toFinset, fun v hv => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Int.cast_mul] at hv
  have hv₁ : ((d₁ : 𝓞 D.host.F)) ∉ v.asIdeal := fun h => hv (v.asIdeal.mul_mem_right _ h)
  have hv₂ : ((d₂ : 𝓞 D.host.F)) ∉ v.asIdeal := fun h => hv (v.asIdeal.mul_mem_left _ h)
  exact le_antisymm (latV_le_of_int_smul S L M d₁ hd₁ h₁ v hv₁) (latV_le_of_int_smul S M L d₂ hd₂ h₂ v hv₂)

end GlobalTheory.FinPl
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair ValuativeRel NumberField Filter IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

theorem eventually_extUnram_two_notMem : ∀ D : D7, ∀ᶠ v : Pl D in cofinite, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.ExtUnramAt D v ∧ (2 : 𝓞 D.host.F) ∉ v.asIdeal := by
  intro D
  rw [Filter.eventually_cofinite]
  have h2 : (2 : 𝓞 D.host.F) ≠ 0 := two_ne_zero
  have hB : (Ideal.span {(2 : 𝓞 D.host.F)}) ≠ 0 := by
    simpa [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using h2
  have hfin2 := Ideal.finite_factors hB
  have hfinD := Ideal.finite_factors
    (differentIdeal_ne_bot (A := 𝓞 D.host.F) (B := 𝓞 D.host.E))
  have hfinU : ((fun Q : HeightOneSpectrum (𝓞 D.host.E) => Q.asIdeal.under (𝓞 D.host.F)) ''
      {Q | Q.asIdeal ∣ differentIdeal (𝓞 D.host.F) (𝓞 D.host.E)}).Finite := hfinD.image _
  have hfinA : {v : Pl D | v.asIdeal ∈ (fun Q : HeightOneSpectrum (𝓞 D.host.E) => Q.asIdeal.under (𝓞 D.host.F)) ''
      {Q | Q.asIdeal ∣ differentIdeal (𝓞 D.host.F) (𝓞 D.host.E)}}.Finite :=
    hfinU.preimage (f := fun v : Pl D => v.asIdeal)
      (fun a _ b _ h => HeightOneSpectrum.ext h)
  refine (hfinA.union hfin2).subset fun v hv => ?_
  by_cases h : (2 : 𝓞 D.host.F) ∈ v.asIdeal
  · right
    exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 h)
  · left
    have hE : ¬ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.ExtUnramAt D v := fun hu => hv ⟨hu, h⟩
    unfold GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.ExtUnramAt at hE
    push_neg at hE
    obtain ⟨P, hP, hL, hU⟩ := hE
    have hover : v.asIdeal = P.under (𝓞 D.host.F) := hL.over
    have hPb : P ≠ ⊥ := by
      rintro rfl
      apply v.ne_bot
      rw [hover, Ideal.under_bot]
    refine ⟨⟨P, hP, hPb⟩, ?_, hover.symm⟩
    by_contra hd
    exact hU (not_dvd_differentIdeal_iff.1 hd)

end GlobalTheory.FinPl
end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open IsDedekindDomain NumberField

namespace GlobalTheory.VacLoc

variable {D : D7}

open scoped Classical

def indP (D : D7) (X : Set (Pl D)) : Af D.host.F :=
  ⟨fun v => if v ∈ X then 1 else 0, Filter.Eventually.of_forall fun v => by
    by_cases h : v ∈ X <;> simp [h, one_mem, zero_mem]⟩

theorem evalV_indP (X : Set (Pl D)) (v : Pl D) :
    evalV D.host.F v (indP D X) = if v ∈ X then 1 else 0 := rfl

theorem indicatorAdele_mem_integralAdeles (X : Set (Pl D)) : indP D X ∈ intAf D.host.F := by
  intro v; rw [evalV_indP]; by_cases h : v ∈ X <;> simp [h, one_mem, zero_mem]

theorem finiteAdele_ext {a b : Af D.host.F} (h : ∀ v, evalV D.host.F v a = evalV D.host.F v b) : a = b :=
  RestrictedProduct.ext _ _ h

theorem indicatorAdele_singleton_mul_singleton (X Y : Set (Pl D)) : indP D X * indP D Y = indP D (X ∩ Y) := by
  apply finiteAdele_ext; intro v; rw [map_mul, evalV_indP, evalV_indP, evalV_indP]
  by_cases hX : v ∈ X <;> by_cases hY : v ∈ Y <;> simp [hX, hY]

theorem indicatorAdele_union_of_disjoint {X Y : Set (Pl D)} (h : Disjoint X Y) : indP D X + indP D Y = indP D (X ∪ Y) := by
  apply finiteAdele_ext; intro v; rw [map_add (f := _), evalV_indP, evalV_indP, evalV_indP]
  by_cases hX : v ∈ X <;> by_cases hY : v ∈ Y <;> simp [hX, hY]
  exact Set.disjoint_left.mp h hX hY

theorem indicatorAdele_univ : indP D Set.univ = 1 := by
  apply finiteAdele_ext; intro v; rw [evalV_indP, map_one]; simp

theorem indicatorAdele_empty : indP D ∅ = 0 := by
  apply finiteAdele_ext; intro v; rw [evalV_indP, map_zero]; simp

end GlobalTheory.VacLoc

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LatLevel


open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
theorem exists_finset_of_nhds_zero {F : Type} [Field F] [NumberField F] (V : Set (Af F)) (hV : IsOpen V)
    (h0 : (0 : Af F) ∈ V) :
    ∃ s : Finset (HeightOneSpectrum (𝓞 F)), ∀ γ ∈ Formalism.MainNotions.StandardLattice.intAf F, (∀ v ∈ s, evalV F v γ = 0) → γ ∈ V := by
  set f := RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite with hf
  have hc : Continuous f := (RestrictedProduct.isOpenEmbedding_structureMap
    (fun v => Valued.isOpen_integer _)).continuous
  have hO : IsOpen (f ⁻¹' V) := hV.preimage hc
  have hz : (0 : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) ∈ f ⁻¹' V := h0
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hO _ hz
  refine ⟨I, fun γ hγ hs => ?_⟩
  let x : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F := fun v => ⟨γ v, hγ v⟩
  have hx : x ∈ (I : Set _).pi u := by
    intro v hv
    have h1 : x v = 0 := Subtype.ext (hs v hv)
    rw [h1]
    exact (hu v hv).2
  have := hsub hx
  exact this

end GlobalTheory.LatLevel

namespace GlobalTheory.LatLevel

theorem smul_mem_open_of_vanish : ∀ (D : D7) (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (P : Pl D → Prop) (U : AddSubgroup (WO S T)), IsOpen (U : Set (WO S T)) → ∀ u ∈ latO S T LS LT P, ∃ s : Finset (Pl D), ∀ γ ∈ intAf D.host.F, (∀ v ∈ s, evalV D.host.F v γ = 0) → pairA D.host.F 0 γ • u ∈ U := by
  intro D S T LS LT P U hU u _hu
  letI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have hg : Continuous fun β : Af D.host.F => (pairA D.host.F 0 β) • u := by
    have h1 : Continuous fun β : Af D.host.F => pairA D.host.F 0 β :=
      continuous_const.prodMk continuous_id
    exact h1.smul continuous_const
  obtain ⟨s, hs⟩ := exists_finset_of_nhds_zero _ (hU.preimage hg)
    (by
      show pairA D.host.F 0 0 • u ∈ (U : Set (WO S T))
      have : pairA D.host.F 0 0 = 0 := rfl
      rw [this, zero_smul]
      exact U.zero_mem)
  exact ⟨s, fun γ hγ hv => hs γ hγ hv⟩

end GlobalTheory.LatLevel
end
end
