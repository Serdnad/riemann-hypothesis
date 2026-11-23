module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2208
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2205
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExpEqOfPeriodsOfMarking
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle043
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem powerSeries_expansion_image_dense_with_denominator {p : ℕ} [Fact p.Prime] (D : Datum p) (N : ℕ) (hN : 0 < N) (hNp : N.Coprime p)
    (z : AfP p ⊗[ℚ] VQ D) : ∃ (w : VQ D) (e : AfP p ⊗[ℚ] VQ D), e ∈ LaHat D ∧
      z = (1 : AfP p) ⊗ₜ[ℚ] w + N • e := by
  obtain ⟨t, ht0, htc, ht⟩ := DenEnd.exists_coprime_nsmul_mem D z
  obtain ⟨x, e, he, hx⟩ := exists_inAf_add_nsmul_of_mem_laHat p D (t * N) (Nat.mul_pos ht0 hN)
    (Nat.Coprime.mul_left htc hNp) (t • z) ht
  have ht' : (t : ℚ) ≠ 0 := by exact_mod_cast ht0.ne'
  refine ⟨(t : ℚ)⁻¹ • ((1 : ℚ) ⊗ₜ[ℤ] x), e, he, ?_⟩
  have h1 : t • ((1 : AfP p) ⊗ₜ[ℚ] ((t : ℚ)⁻¹ • ((1 : ℚ) ⊗ₜ[ℤ] x))) = inAf D x := by
    rw [inAf, ← Nat.cast_smul_eq_nsmul ℚ, ← TensorProduct.tmul_smul, smul_smul, mul_inv_cancel₀ ht', one_smul]
  have h2 : t • z = t • ((1 : AfP p) ⊗ₜ[ℚ] ((t : ℚ)⁻¹ • ((1 : ℚ) ⊗ₜ[ℤ] x)) + N • e) := by
    rw [hx, smul_add, h1, smul_smul]
  rw [← Nat.cast_smul_eq_nsmul ℚ t, ← Nat.cast_smul_eq_nsmul ℚ t] at h2
  exact smul_right_injective _ ht' h2

theorem UpperTheory.Gal.W2.rdDense_of :
    UpperTheory.Gal.W2.RdDense := by
  intro p _ D G L x h₁ n hn z
  let T : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) :=
    L.actG h₁⁻¹ * actOn L.rep (AfP p) (x : AfP p ⊗[ℚ] G.C)
  let S : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) :=
    actOn L.rep (AfP p) ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) * L.actG h₁
  have hTS : T * S = 1 := by
    have e1 : actOn L.rep (AfP p) (x : AfP p ⊗[ℚ] G.C) *
        actOn L.rep (AfP p) ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have e2 : L.actG h₁⁻¹ * L.actG h₁ = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    change (L.actG h₁⁻¹ * actOn L.rep (AfP p) (x : AfP p ⊗[ℚ] G.C)) *
      (actOn L.rep (AfP p) ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) * L.actG h₁) = 1
    rw [_root_.mul_assoc, ← _root_.mul_assoc (actOn L.rep (AfP p) (x : AfP p ⊗[ℚ] G.C)), e1, _root_.one_mul, e2]
  obtain ⟨m, hm0, hmc, hm⟩ := DenEnd.exists_coprime_nsmul_map_mem p D T
  obtain ⟨k, n', hn', hnn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p (Fact.out : p.Prime).ne_one
  have hn0 : 0 < n' := Nat.pos_of_ne_zero fun h => hn' (h ▸ dvd_zero p)
  have hnc : n'.Coprime p := ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hn').symm
  obtain ⟨w, e, he, hz⟩ := powerSeries_expansion_image_dense_with_denominator D (n' * m) (Nat.mul_pos hn0 hm0) (Nat.Coprime.mul_left hnc hmc) (S z)
  have hint : IsIntAf (algebraMap ℚ (AfP p) ((p : ℚ)⁻¹ ^ k)) := fun u => by
    rw [map_pow, map_pow]; exact pow_mem (DenEnd.isIntAf_inv u) k
  have hz2 : z = T (S z) := by
    rw [← Module.End.mul_apply, hTS]; rfl
  have hr : rd L x h₁ w = T ((1 : AfP p) ⊗ₜ[ℚ] w) := rfl
  have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  refine ⟨w, algebraMap ℚ (AfP p) ((p : ℚ)⁻¹ ^ k) • (m • T e), DenEnd.smul_mem D hint (hm e he), ?_⟩
  rw [hr, hz2, hz, map_add (f := _), map_nsmul]
  congr 1
  rw [algebraMap_smul, hnn]
  simp only [← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  congr 1
  have hpk : (p : ℚ) ^ k * ((p : ℚ)⁻¹) ^ k = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hp, one_pow]
  push_cast
  linear_combination (-((n' : ℚ) * m)) * hpk
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.rigid_of :
    UpperTheory.Gal.W2.Rigid := by
  intro O _ bar g ρ Λ N D' t P w h hN hfull hper ⟨hiso, hmark⟩ hPw
  obtain ⟨-, hinj, hd, hspan, Hm, -, hpos, hIm⟩ := hper
  let σw : Module.End ℤ D'.La := (w.toLinearMap.toAddMonoidHom).toIntLinearMap
  have hσ : ∀ a, σw a = w a := fun _ => rfl
  let hR : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) := h.toLinearMap.restrictScalars ℝ
  let B : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ (fun u v => (hermForm Hm u v).im)
    (fun a b c => by simp [hermForm]) (fun r a b => by simp [hermForm])
    (fun a b c => by simp [hermForm, Matrix.mulVec_add]) (fun r a b => by simp [hermForm, Matrix.mulVec_smul])
  have hB : B.compl₁₂ hR hR = B := by
    refine LinearMap.ext_on_range hspan fun a => LinearMap.ext_on_range hspan fun b => ?_
    show (hermForm Hm (h (P a)) (h (P b))).im = (hermForm Hm (P a) (P b)).im
    rw [← hPw, ← hPw, hIm, hIm, hiso]
  have hq : ∀ u, (hermForm Hm u u).re = B (Complex.I • u) u := fun u => by
    show _ = (hermForm Hm (Complex.I • u) u).im
    simp [hermForm]
  have hbd := GlobalTheory.ExpUnique.isBounded_sublevel (q := fun u => (hermForm Hm u u).re)
    (by unfold hermForm; fun_prop) (fun r u => by
      simp only [hq]
      rw [smul_comm, map_smul, map_smul, LinearMap.smul_apply, smul_smul, sq, smul_eq_mul]) hpos
  have key : σw = 1 := by
    refine GlobalTheory.ExpUnique.end_eq_one_of_invariant D'.La σw (fun a b hab => w.injective hab)
      (fun a => (hermForm Hm (P a) (P a)).re) (fun c => ?_) (fun a => ?_) N hN fun a => ?_
    · refine Set.Finite.of_finite_image (f := P) ((Metric.finite_isBounded_inter_isClosed
        (s := P.range) DiscreteTopology.isDiscrete (hbd c) AddSubgroup.isClosed_of_discrete).subset ?_) hinj.injOn
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨ha, a, rfl⟩
    · have h1 : h (Complex.I • P a) = Complex.I • h (P a) := map_smul h _ _
      simp only [hq, hσ, hPw]
      rw [← h1]
      have h2 := LinearMap.congr_fun₂ hB (Complex.I • P a) (P a)
      rw [LinearMap.compl₁₂_apply] at h2
      exact h2
    · obtain ⟨i, f, rfl⟩ := hfull a
      obtain ⟨e₀, he₀⟩ := hmark i
      refine ⟨e₀ + w f - f, ?_⟩
      have h3 : w (t i + N • f) = w (t i) + N • w f := by rw [map_add (f := _), map_nsmul]
      rw [hσ, h3, he₀, smul_sub, smul_add]
      abel
  intro u
  rw [← hσ, key]
  rfl
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem exists_extend {M V E : Type} [AddCommGroup M] [AddCommGroup V] [AddCommGroup E] [Module ℚ E]
    (j : M →+ V) (hj : Function.Injective j) (hd : ∀ w, ∃ (m : ℕ) (u : M), m ≠ 0 ∧ m • w = j u) (P : M →+ E) :
    ∃ Q : V →+ E, ∀ u, Q (j u) = P u := by
  choose m u hm h using hd
  have key : ∀ w (n : ℕ) (v : M), n ≠ 0 → n • w = j v →
      ((m w : ℚ)⁻¹) • P (u w) = ((n : ℚ)⁻¹) • P v := by
    intro w n v hn hv
    have h1 : n • u w = m w • v := hj (by
      rw [map_nsmul, map_nsmul, ← h w, ← hv, smul_comm])
    have h2 : n • P (u w) = m w • P v := by rw [← map_nsmul, ← map_nsmul, h1]
    have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
    have hm' : (m w : ℚ) ≠ 0 := by exact_mod_cast hm w
    have h3 : (n : ℚ) • P (u w) = (m w : ℚ) • P v := by
      rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, h2]
    calc ((m w : ℚ)⁻¹) • P (u w) = ((m w : ℚ)⁻¹ * (n : ℚ)⁻¹) • ((n : ℚ) • P (u w)) := by
          rw [smul_smul]; congr 1; field_simp
      _ = ((n : ℚ)⁻¹) • P v := by rw [h3, smul_smul]; congr 1; field_simp
  refine ⟨AddMonoidHom.mk' (fun w => ((m w : ℚ)⁻¹) • P (u w)) ?_, ?_⟩
  · intro a b
    have hab : (m a * m b) • (a + b) = j (m b • u a + m a • u b) := by
      rw [map_add (f := _), map_nsmul, map_nsmul, ← h a, ← h b, smul_add, mul_smul, mul_smul,
        smul_comm (m a) (m b) a]
    have hk := key (a + b) (m a * m b) _ (mul_ne_zero (hm a) (hm b)) hab
    have hma : (m a : ℚ) ≠ 0 := by exact_mod_cast hm a
    have hmb : (m b : ℚ) ≠ 0 := by exact_mod_cast hm b
    rw [hk, map_add (f := _), map_nsmul, map_nsmul, smul_add, ← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ,
      smul_smul, smul_smul]
    push_cast
    congr 2 <;> field_simp
  · intro v
    have hk := key (j v) 1 v one_ne_zero (by simp)
    simpa using hk

private theorem finrank_eq_of_place {M V : Type} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    [AddCommGroup V] [Module ℚ V] (j : M →+ V) (hj : Function.Injective j)
    (hd : ∀ w, ∃ (m : ℕ) (u : M), m ≠ 0 ∧ m • w = j u) :
    Module.finrank ℤ M = Module.finrank ℚ V :=
  _root_.UpperTheory.Reformulated.B.FinrankIntEqFinrankRat.finrank_eq_of_place j hj hd

private theorem period_of_basis {M : Type} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M] {g : ℕ}
    (P : M →+ (Fin g → ℂ)) (hs : Submodule.span ℝ (Set.range P) = ⊤)
    (hc : Module.finrank ℤ M = 2 * g) :
    Function.Injective P ∧ DiscreteTopology P.range := by
  let b := Module.finBasis ℤ M
  let v : Fin (Module.finrank ℤ M) → (Fin g → ℂ) := fun i => P (b i)
  have hPx : ∀ x, P x = ∑ i, (b.repr x i) • v i := by
    intro x
    conv_lhs => rw [← b.sum_repr x]

    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_zsmul _ _ _
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range v) := by
    rw [← hs]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, rfl⟩
    rw [hPx]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact zsmul_mem (Submodule.subset_span (Set.mem_range_self i)) _
  have hfr : Fintype.card (Fin (Module.finrank ℤ M)) = Module.finrank ℝ (Fin g → ℂ) := by
    rw [Fintype.card_fin, hc, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  have li : LinearIndependent ℝ v := linearIndependent_of_top_le_span_of_card_eq_finrank hsp hfr
  refine ⟨(injective_iff_map_eq_zero P).mpr fun x hx => ?_, ?_⟩
  · have h0 : ∑ i, ((b.repr x i : ℤ) : ℝ) • v i = 0 := by
      rw [← hx, hPx]
      exact Finset.sum_congr rfl fun i _ => Int.cast_smul_eq_zsmul ℝ _ _
    have h1 := Fintype.linearIndependent_iff.mp li _ h0
    apply b.repr.injective
    ext i
    simpa using h1 i
  · let bb : Module.Basis (Fin (Module.finrank ℤ M)) ℝ (Fin g → ℂ) := Module.Basis.mk li hsp
    have hset : (P.range : Set (Fin g → ℂ)) = (Submodule.span ℤ (Set.range bb) : Set (Fin g → ℂ)) := by
      have hb : Set.range bb = Set.range v := by
        rw [Module.Basis.coe_mk]
      rw [hb]
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        show P x ∈ Submodule.span ℤ (Set.range v)
        rw [hPx]
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      · intro hy
        have hy' : y ∈ Submodule.span ℤ (Set.range v) := hy
        induction hy' using Submodule.span_induction with
        | mem a ha => obtain ⟨i, rfl⟩ := ha; exact ⟨b i, rfl⟩
        | zero => exact zero_mem P.range
        | add a c _ _ h1 h2 => exact add_mem (h1 (by assumption)) (h2 (by assumption))
        | smul r a _ h1 => exact zsmul_mem (h1 (by assumption)) r
    have hd : DiscreteTopology (Submodule.span ℤ (Set.range bb)) := inferInstance
    have hd' : DiscreteTopology ((Submodule.span ℤ (Set.range bb) : Set (Fin g → ℂ))) := hd
    rw [← hset] at hd'
    exact hd'

private theorem herm_smul_mat {g : ℕ} (r : ℂ) (H : Matrix (Fin g) (Fin g) ℂ) (x y : Fin g → ℂ) :
    hermForm (r • H) x y = r * hermForm H x y := by
  simp [hermForm, Matrix.smul_mulVec, dotProduct_smul]

private theorem herm_nsmul {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (m n : ℕ) (x y : Fin g → ℂ) :
    hermForm H (m • x) (n • y) = ((m : ℂ) * n) * hermForm H x y := by
  simp only [hermForm]
  rw [← Nat.cast_smul_eq_nsmul ℂ m x, ← Nat.cast_smul_eq_nsmul ℂ n y, star_smul, Matrix.mulVec_smul,
    smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul, star_natCast]
  ring

private theorem herm_scale {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) {r : ℝ} (hr : 0 < r) :
    ((r : ℂ) • Hm).IsHermitian ∧ ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm ((r : ℂ) • Hm) z z).re := by
  refine ⟨?_, fun z hz => ?_⟩
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hH.eq]
    simp
  · rw [herm_smul_mat, Complex.re_ofReal_mul]
    exact mul_pos hr (hpos z hz)

theorem UpperTheory.Gal.W2.placePer_of :
    UpperTheory.Gal.W2.PlacePer := by
  intro p _ D G L β ρ D' j hpl
  obtain ⟨hinj, hact, hden, s, hs, hEF⟩ := hpl
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hform : ∀ (m n : ℕ) (u w : VQ D),
      formB L β (m • u) (n • w) = (m : ℚ) * n * formB L β u w := by
    intro m n u w
    simp only [formB, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
    ring
  refine ⟨fun P hP => ?_, fun Q hQ hrk => ?_⟩
  · obtain ⟨hPa, -, -, hPs, Hm, hH, hpos, hIm⟩ := hP
    obtain ⟨Q, hQ⟩ := exists_extend j hinj hden P
    have hsc := herm_scale hH hpos (inv_pos.mpr hsR)
    refine ⟨Q, ⟨fun c w => ?_, ?_, ((((s : ℝ))⁻¹ : ℝ) : ℂ) • Hm, hsc.1, hsc.2, fun u w => ?_⟩, hQ⟩
    · obtain ⟨m, a, hm, h⟩ := hden w
      refine nsmul_right_injective hm ?_
      show m • Q (actQ D c w) = m • (ρ c *ᵥ Q w)
      have e1 : m • Q (actQ D c w) = P (c • a) := by
        rw [← map_nsmul, ← map_nsmul (actQ D c), h, ← hact, hQ]
      have e2 : m • (ρ c *ᵥ Q w) = ρ c *ᵥ P a := by
        rw [← hQ, ← h, map_nsmul, Matrix.mulVec_smul]
      rw [e1, e2, hPa]
    · rw [eq_top_iff, ← hPs]
      apply Submodule.span_mono
      rintro _ ⟨x, rfl⟩
      exact ⟨j x, hQ x⟩
    · obtain ⟨m, a, hm, ha⟩ := hden u
      obtain ⟨n, b, hn, hb⟩ := hden w
      have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      have h1 : hermForm (((((s : ℝ))⁻¹ : ℝ) : ℂ) • Hm) (Q (j a)) (Q (j b)) =
          (((m : ℝ) * n : ℝ) : ℂ) * hermForm (((((s : ℝ))⁻¹ : ℝ) : ℂ) • Hm) (Q u) (Q w) := by
        rw [← ha, ← hb, map_nsmul, map_nsmul, herm_nsmul]
        push_cast
        rfl
      have h2 : (hermForm (((((s : ℝ))⁻¹ : ℝ) : ℂ) • Hm) (Q (j a)) (Q (j b))).im =
          ((s : ℝ))⁻¹ * (D'.EF a b : ℝ) := by
        rw [herm_smul_mat, hQ, hQ, Complex.im_ofReal_mul, hIm]
      have h3 : (D'.EF a b : ℝ) = (s : ℝ) * ((m : ℝ) * n * (formB L β u w : ℚ)) := by
        have h4 := hEF a b
        rw [← ha, ← hb, hform] at h4
        exact_mod_cast h4
      rw [h1, Complex.im_ofReal_mul, h3] at h2
      have hs0 : (s : ℝ) ≠ 0 := hsR.ne'
      have h5 : ((m : ℝ) * n) * (hermForm (((((s : ℝ))⁻¹ : ℝ) : ℂ) • Hm) (Q u) (Q w)).im =
          ((m : ℝ) * n) * (formB L β u w : ℚ) := by
        rw [h2]
        field_simp
      exact mul_left_cancel₀ (mul_ne_zero hmR hnR) h5
  · obtain ⟨hQa, hQs, Hm, hH, hpos, hIm⟩ := hQ
    have hc : Module.finrank ℤ D'.La = 2 * D.g := by
      rw [finrank_eq_of_place j hinj hden, hrk]
      haveI : Module.Free ℤ D.La := D.freeLa
      exact Module.finrank_baseChange
    have hs' : Submodule.span ℝ (Set.range (Q.comp j)) = ⊤ := by
      rw [eq_top_iff, ← hQs]
      apply Submodule.span_le.mpr
      rintro _ ⟨w, rfl⟩
      obtain ⟨m, a, hm, h⟩ := hden w
      have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
      have e : Q w = (m : ℝ)⁻¹ • Q (j a) := by
        rw [← h, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hm', one_smul]
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    obtain ⟨hi, hdisc⟩ := period_of_basis (Q.comp j) hs' hc
    have hsc := herm_scale hH hpos hsR
    refine ⟨fun c u => ?_, hi, hdisc, hs', ((s : ℝ) : ℂ) • Hm, hsc.1, hsc.2, fun x y => ?_⟩
    · simp only [AddMonoidHom.comp_apply]
      rw [hact, hQa]
    · simp only [AddMonoidHom.comp_apply]
      rw [herm_smul_mat, Complex.im_ofReal_mul, hIm]
      have h4 := hEF x y
      exact_mod_cast h4.symm
end
