module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CoeffSlD
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle084
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle090
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle192
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlMulToRingEquiv
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bundle006
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KmapComp
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
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
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

private theorem nle {l : ℕ} [Fact l.Prime] (c : Coef l) {a : Qbar l} (ha : a ∈ c.O) : ‖a‖ ≤ 1 := by
  have hi : IsIntegral ℤ_[l] a := (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨a, ha⟩ : c.O)).map c.O.val
  have hq : IsIntegral ℚ_[l] a := Algebra.IsIntegral.isIntegral a
  change spectralValue (minpoly ℚ_[l] a) ≤ 1
  rw [spectralValue_le_one_iff (minpoly.monic hq)]
  intro k
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hi, Polynomial.coeff_map]
  exact PadicInt.norm_le_one _

private theorem sadd {l : ℕ} [Fact l.Prime] {δ : ℝ} {a b : Qbar l} (ha : ‖a‖ ≤ δ) (hb : ‖b‖ ≤ δ) : ‖a + b‖ ≤ δ :=
  (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

private theorem smul' {l : ℕ} [Fact l.Prime] {δ : ℝ} {a b : Qbar l} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ δ) : ‖a * b‖ ≤ δ := by
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans hb

private theorem shift {l : ℕ} [Fact l.Prime] {U : Type} [CommGroup U] [Fintype U] {δ : ℝ} (hδ : 0 ≤ δ) (η F : U → Qbar l) (t : U)
    (c : Qbar l) (h : ∀ y, ‖η (y * t) - η y * c‖ ≤ δ) (hF : ∀ y, ‖F y‖ ≤ 1) :
    ‖∑ y, η y * F (y * t⁻¹) - c * ∑ y, η y * F y‖ ≤ δ := by
  have e : ∑ y, η y * F (y * t⁻¹) = ∑ y, η (y * t) * F y :=
    (Fintype.sum_equiv (Equiv.mulRight t) _ _ fun y => by simp).symm
  rw [e, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hδ fun y _ => ?_
  have : η (y * t) * F y - c * (η y * F y) = F y * (η (y * t) - η y * c) := by ring
  rw [this]
  exact smul' (hF y) (h y)

private theorem unit_of {l r : ℕ} [hl : Fact l.Prime] (hr : r ≠ 0) (y : (ZMod (l ^ r))ˣ) :
    ∃ u : ℤ_[l]ˣ, (u : ℤ_[l]) = ((y : ZMod (l ^ r)).val : ℕ) := by
  have h := Nat.Coprime.coprime_dvd_right (dvd_pow_self l hr) (ZMod.val_coe_unit_coprime y)
  have : IsUnit (((y : ZMod (l ^ r)).val : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact h.symm
  exact this

private theorem inv_cg {l r : ℕ} [hl : Fact l.Prime] (c : Coef l) (hr : r ≠ 0) (e : ℕ) (y t : (ZMod (l ^ r))ˣ) (τ : ℤ_[l]ˣ)
    (h : PadicInt.toZModPow r (τ : ℤ_[l]) = t) :
    ‖((((((y * t : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val : ℕ) : Qbar l)) ^ e)⁻¹ -
      (((((y : ZMod (l ^ r)).val : ℕ) : Qbar l)) ^ e)⁻¹ * ((algebraMap ℤ_[l] (Qbar l) τ) ^ e)⁻¹‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  obtain ⟨u, hu⟩ := unit_of hr (y * t)
  obtain ⟨v, hv⟩ := unit_of hr y
  have h1 : (l : ℤ_[l]) ^ r ∣ ((v * τ : ℤ_[l]ˣ) : ℤ_[l]) - u := by
    rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, Units.val_mul, map_mul, hu, hv, h,
      map_natCast, map_natCast, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, Units.val_mul, sub_self]
  obtain ⟨k, hk⟩ := h1.trans (sub_dvd_pow_sub_pow _ _ e)
  have inv : ∀ w : ℤ_[l]ˣ, (algebraMap ℤ_[l] (Qbar l) w ^ e)⁻¹ = algebraMap ℤ_[l] (Qbar l) ((w⁻¹ : ℤ_[l]ˣ) ^ e) := fun w => by
    apply inv_eq_of_mul_eq_one_right
    rw [← map_pow, ← map_mul, ← mul_pow, Units.mul_inv, one_pow, map_one]
  rw [← map_natCast (algebraMap ℤ_[l] (Qbar l)) (ZMod.val _), ← map_natCast (algebraMap ℤ_[l] (Qbar l)) (ZMod.val _), ← hu, ← hv,
    inv, inv, inv, ← map_mul, ← map_sub]
  have e1 : ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ^ e - ((v⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ^ e * ((τ⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ^ e =
      (k * ((u⁻¹ * (v * τ)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ^ e) * (l : ℤ_[l]) ^ r := by
    have a1 : ((u⁻¹ * (v * τ)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ^ e * ((v * τ : ℤ_[l]ˣ) : ℤ_[l]) ^ e = ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ^ e := by
      rw [← mul_pow, ← Units.val_mul, inv_mul_cancel_right]
    have a2 : ((u⁻¹ * (v * τ)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ^ e * (u : ℤ_[l]) ^ e =
        ((v⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ^ e * ((τ⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ^ e := by
      rw [← mul_pow, ← mul_pow, ← Units.val_mul, ← Units.val_mul, mul_comm u⁻¹, inv_mul_cancel_right, mul_inv]
    rw [← a1, ← a2, ← mul_sub, hk]; ring
  rw [e1, map_mul, map_pow, map_natCast]
  exact smul' (nle c (c.O.algebraMap_mem _)) le_rfl

theorem UpperTheory.V.Z.Kato.Nb.sSpec :
    UpperTheory.V.Z.Kato.Nb.SSpec := by
  intro l hl Ω _ _ _ ι e gN A W ε X pr N _ x c d gm ψ cf hA he hW p r hp hlp a δ k ha hδ hk Y V b hY hb H
  obtain ⟨hθ, h1, hmul, hψ, hρ, -, -⟩ := sInteg l Ω ι e gN A W ε X pr N x c d gm ψ cf hA he hW
  rcases eq_or_ne r 0 with rfl | hr
  · refine ⟨0, fun i => zero_mem _, fun s i => ?_⟩
    have z : ∀ y : (ZMod (l ^ 0))ˣ, (y : ZMod (l ^ 0)).val = 0 := fun y =>
      Nat.lt_one_iff.1 (by simpa using ZMod.val_lt (y : ZMod (l ^ 0)))
    simp only [Cg, spec, z, Nat.cast_zero, zero_pow (show e ≠ 0 by omega), inv_zero, zero_mul, zero_smul, Finset.sum_const_zero]
    simp
  have hS := (sSlD Ω ε X N (Nat.pos_of_ne_zero (NeZero.ne N))).2.2.2.2.2.2.2
  let rd : (ZMod (l ^ r))ˣ →* (ZMod l)ˣ := Units.map (ZMod.castHom (dvd_pow_self l hr) (ZMod l)).toMonoidHom
  have hrd : ∀ y, chiK l ψ r y = ψ (rd y : (ZMod l)ˣ) := fun y => by
    rw [chiK, ZMod.natCast_val]; rfl
  set η : (ZMod (l ^ r))ˣ → Qbar l := fun x => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r x with hη
  have uO : ∀ w : ℤ_[l]ˣ, (algebraMap ℤ_[l] (Qbar l) w)⁻¹ ∈ cf.O := fun w => by
    rw [show (algebraMap ℤ_[l] (Qbar l) w)⁻¹ = algebraMap ℤ_[l] (Qbar l) (w⁻¹ : ℤ_[l]ˣ) from
      inv_eq_of_mul_eq_one_right (by rw [← map_mul, Units.mul_inv, map_one])]
    exact cf.O.algebraMap_mem _
  have ηO : ∀ y, η y ∈ cf.O := fun y => by
    obtain ⟨u, hu⟩ := unit_of hr y
    simp only [hη]
    rw [← map_natCast (algebraMap ℤ_[l] (Qbar l)), ← hu, ← inv_pow, hrd]
    exact mul_mem (pow_mem (uO u) e) (hψ _)
  have key : ∀ (t : (ZMod (l ^ r))ˣ) (τ : ℤ_[l]ˣ), PadicInt.toZModPow r (τ : ℤ_[l]) = t → ∀ y,
      ‖η (y * t) - η y * (((algebraMap ℤ_[l] (Qbar l) τ) ^ e)⁻¹ * ψ (rd t : (ZMod l)ˣ))‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := fun t τ h y => by
    simp only [hη]
    rw [hrd, hrd, map_mul, hmul]
    have := smul' (nle cf (mul_mem (hψ (rd y)) (hψ (rd t)))) (inv_cg cf hr e y t τ h)
    convert this using 2
    ring
  have hp1 : (p : ZMod l) = 1 := by
    obtain ⟨m, hm⟩ := hlp
    rw [show p = l * m + 1 by have := hp.pos; omega]
    simp
  have hcop : Nat.Coprime l p := by
    rw [Nat.Prime.coprime_iff_not_dvd hl.out, ← ZMod.natCast_eq_zero_iff, hp1]
    exact one_ne_zero
  obtain ⟨π, hπ⟩ : IsUnit (p : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]; exact hcop
  have hq : IsUnit (p : ZMod (l ^ r)) := (ZMod.isUnit_iff_coprime _ _).2 (hcop.symm.pow_right r)
  have hinv : inv1 (l ^ r) p = hq.unit⁻¹ := dif_pos hq
  have hπ' : algebraMap ℤ_[l] (Qbar l) π = p := by rw [hπ, map_natCast]
  have hrq : ((rd hq.unit : (ZMod l)ˣ) : ZMod l) = 1 := by
    rw [← hp1]; exact map_natCast (ZMod.castHom (dvd_pow_self l hr) (ZMod l)) p
  have k1 := key hq.unit π (by rw [hπ, map_natCast]; rfl)
  have k2 := key (hq.unit ^ 2) (π ^ 2) (by rw [Units.val_pow_eq_pow_val, map_pow, hπ, map_natCast]; rfl)
  rw [hπ', hrq, h1] at k1
  rw [Units.val_pow_eq_pow_val, map_pow, hπ', map_pow, Units.val_pow_eq_pow_val, hrq, one_pow, h1] at k2
  have hpO : (p : Qbar l)⁻¹ ∈ cf.O := hπ' ▸ uO π
  have hp0 : (p : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hpn : ‖(p : Qbar l)‖ ≤ 1 := nle cf (natCast_mem _ p)
  refine ⟨fun i => (p : Qbar l)⁻¹ * ∑ y, η y * b y i, fun i => mul_mem hpO (sum_mem fun y _ => mul_mem (ηO y) (hb y i)), fun s i => ?_⟩
  have k3 := key (cycMod ℚ Ω l r s) (cycZ ℚ Ω l s) rfl
  have hth : ((algebraMap ℤ_[l] (Qbar l) (cycZ ℚ Ω l s : ℤ_[l]ˣ)) ^ e)⁻¹ * ψ (rd (cycMod ℚ Ω l r s) : (ZMod l)ˣ) = thK l e ψ s := by
    have a1 : rd (cycMod ℚ Ω l r s) = cycM l s := by
      rw [(sCycZ Ω l r s).1]; exact (hS (l ^ r) s).2.2.2.2 l (dvd_pow_self l hr)
    have a2 := (hS (l ^ 1) s).2.2.2.2 l (dvd_pow_self l one_ne_zero)
    rw [← (sCycZ Ω l 1 s).1] at a2
    rw [a1, ← a2, thK, ZMod.natCast_val]; rfl
  rw [hth] at k3
  have h0 := norm_nonneg (((l : ℕ) : Qbar l) ^ r)
  have s1 := shift h0 η (fun y => Y s y i) _ _ k1 fun y => hY s y i
  have s2 := shift h0 η (fun y => Y s y i) _ _ k2 fun y => hY s y i
  have s3 := fun j => shift h0 η (fun y => b y j) _ _ k3 fun y => nle cf (hb y j)
  have s0 := IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (s := Finset.univ) h0 fun y _ => smul' (nle cf (ηO y)) (H s y i)
  have hθ0 : thK l e ψ s ≠ 0 := fun h => by simpa [h] using hθ s
  have hWρ : ∀ j, mat W s i j = thK l e ψ s * rhoK W e ψ s i j := fun j => by
    rw [rhoK, Matrix.smul_apply, smul_eq_mul, mul_inv_cancel_left₀ hθ0]
  have E : ∑ y, η y * (((p : Qbar l) • V s y) i - (k • ((p : Qbar l) • Y s y - a • Y s (y * inv1 (l ^ r) p) +
          ((p : Qbar l) ^ (2 * e - 1) * δ) • Y s (y * inv1 (l ^ r) p ^ 2)) +
          (rhoK W e ψ s *ᵥ b (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) - b y)) i) =
      p * ∑ y, η y * V s y i - (k * (p * ∑ y, η y * Y s y i - a * ∑ y, η y * Y s (y * hq.unit⁻¹) i +
        ((p : Qbar l) ^ (2 * e - 1) * δ) * ∑ y, η y * Y s (y * (hq.unit ^ 2)⁻¹) i) +
        (rhoK W e ψ s i 0 * ∑ y, η y * b (y * (cycMod ℚ Ω l r s)⁻¹) 0 + rhoK W e ψ s i 1 * ∑ y, η y * b (y * (cycMod ℚ Ω l r s)⁻¹) 1 -
          ∑ y, η y * b y i)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [hinv, inv_pow, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  rw [E] at s0
  have fin := smul' (nle cf hpO) (sadd (sadd (sadd (sadd s0 (smul' (a := -(k * a)) (by rw [norm_neg]; exact smul' hk ha) s1))
    (smul' (a := k * ((p : Qbar l) ^ (2 * e - 1) * δ)) (smul' hk (smul' (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hpn) hδ)) s2))
    (smul' (nle cf (hρ s i 0)) (s3 0))) (smul' (nle cf (hρ s i 1)) (s3 1)))
  unfold Cg
  convert fin using 2
  simp only [spec, eul, Finset.sum_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, hWρ]
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  rw [show 2 * (e' + 1) - 1 = 2 * e' + 1 by omega]
  field_simp
  ring
end

section

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

namespace UpperTheory.V.Z.Kato.Nb

private theorem hi_perm (N l p : ℕ) (hl : l.Prime) (hN : 0 < N) (hp : p.Prime) (hc : Nat.Coprime p (l * N))
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gam N l) :
    ∃ π : Equiv.Perm (Fin (p + 1)), ∀ i, ∃ γ' ∈ Gam N l,
      GlobalTheory.HeckeFamilyMatrices.tqFam p (sgD N l p) i * (γ : Matrix (Fin 2) (Fin 2) ℤ) =
        (γ' : Matrix (Fin 2) (Fin 2) ℤ) * GlobalTheory.HeckeFamilyMatrices.tqFam p (sgD N l p) (π i) := by
  have hpl : ¬ p ∣ N * l := by
    intro h
    have := Nat.Coprime.coprime_dvd_right h (by rw [mul_comm]; exact hc)
    exact hp.one_lt.ne' ((Nat.coprime_self p).1 this)
  have hpN : p.Coprime N := Nat.Coprime.coprime_dvd_right (dvd_mul_left N l) hc
  have hpNl : p.Coprime (N * l) := by rw [mul_comm]; exact hc
  have hD := Betti.isDiam_sgD (N := N) (l := l) (d := p) hN.ne' hl.ne_zero hpN
  have hD' := Betti.isDiam_sgD (N := N * l) (l := l) (d := p) (Nat.mul_ne_zero hN.ne' hl.ne_zero) hl.ne_zero hpNl
  set σ := sgD N l p with hσ
  set σ' := sgD (N * l) l p with hσ'
  have hdia : GlobalTheory.Hk.IsDia N l p σ' := by
    refine ⟨CongruenceSubgroup.Gamma0_mem.1 hD'.1.1, ?_⟩
    have h2 := congrArg (ZMod.castHom (dvd_mul_right N l) (ZMod N)) hD'.2
    simpa [GlobalTheory.KZ.en] using h2
  have hδ : σ * σ'⁻¹ ∈ Gam N l := by
    refine ⟨?_, Subgroup.mul_mem _ hD.1.2 (Subgroup.inv_mem _ hD'.1.2)⟩
    have h0 := CongruenceSubgroup.Gamma0_mem.1 hD.1.1
    have h1 := hD.2
    have h0' : (((σ' : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N) = 0 := by
      have := congrArg (ZMod.castHom (dvd_mul_right N l) (ZMod N)) (CongruenceSubgroup.Gamma0_mem.1 hD'.1.1)
      simpa using this
    have h1' : (((σ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N) = p := by
      have h2 := congrArg (ZMod.castHom (dvd_mul_right N l) (ZMod N)) hD'.2
      simpa [GlobalTheory.KZ.en] using h2
    simp only [GlobalTheory.KZ.en] at h1
    have hdet := σ.det_coe
    have hdet' := σ'.det_coe
    rw [Matrix.det_fin_two] at hdet hdet'
    have e1 := congrArg (Int.cast : ℤ → ZMod N) hdet
    have e2 := congrArg (Int.cast : ℤ → ZMod N) hdet'
    push_cast at e1 e2
    rw [h0, h1] at e1
    rw [h0', h1'] at e2
    show σ * σ'⁻¹ ∈ CongruenceSubgroup.Gamma1 N
    rw [CongruenceSubgroup.Gamma1_mem]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    push_cast
    rw [h0, h1, h0', h1']
    refine ⟨?_, ?_, ?_⟩
    all_goals first | linear_combination e1 | linear_combination e2 | ring
  obtain ⟨π, hπ⟩ := GlobalTheory.HkInv.perm N l p σ' γ hp hpl hdia hγ
  let D : Fin (p + 1) → SL(2, ℤ) := fun i => if (i : ℕ) < p then 1 else σ * σ'⁻¹
  have hDm : ∀ i, D i ∈ Gam N l := by
    intro i
    simp only [D]
    split_ifs
    · exact one_mem _
    · exact hδ
  have hT : ∀ i, GlobalTheory.HeckeFamilyMatrices.tqFam p σ i = (D i : Matrix (Fin 2) (Fin 2) ℤ) * GlobalTheory.HeckeFamilyMatrices.tqFam p σ' i := by
    intro i
    simp only [GlobalTheory.HeckeFamilyMatrices.tqFam, D]
    split_ifs
    · simp
    · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc, ← Matrix.mul_assoc ((σ'⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ),
        ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
  refine ⟨π, fun i => ?_⟩
  obtain ⟨γ', hγ', he⟩ := hπ i
  refine ⟨D i * γ' * (D (π i))⁻¹, mul_mem (mul_mem (hDm i) hγ') (inv_mem (hDm _)), ?_⟩
  rw [hT i, hT (π i), Matrix.mul_assoc]
  erw [he]
  rw [← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
    mul_assoc (D i * γ'), inv_mul_cancel, mul_one]

private theorem hi_det (p : ℕ) (hp : 0 < p) (σ : SL(2, ℤ)) (i : Fin (p + 1)) : 0 < (GlobalTheory.HeckeFamilyMatrices.tqFam p σ i).det := by
  unfold GlobalTheory.HeckeFamilyMatrices.tqFam
  split_ifs
  · simp [Matrix.det_fin_two]
    exact_mod_cast hp
  · rw [Matrix.det_mul, GlobalTheory.HeckeFamilyMatrices.mat, σ.det_coe, one_mul]
    simp [GlobalTheory.HeckeFamilyMatrices.dg, Matrix.det_fin_two]
    exact_mod_cast hp

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]

private theorem hi_sum (N p : ℕ) (a : X.Fn l) :
    X.heckeT N l p a = ∑ i : Fin (p + 1), X.act l (GlobalTheory.HeckeFamilyMatrices.tqFam p (sgD N l p) i) a := by
  rw [Fin.sum_univ_castSucc]
  simp only [GlobalTheory.KZ.Tower.heckeT, LinearMap.add_apply, LinearMap.sum_apply]
  congr 1
  · rw [← Fin.sum_univ_eq_sum_range (fun j => (X.act l !![1, (j : ℤ); 0, (p : ℤ)]) a)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [GlobalTheory.HeckeFamilyMatrices.tqFam]
  · simp [GlobalTheory.HeckeFamilyMatrices.tqFam, GlobalTheory.HeckeFamilyMatrices.dg]

private theorem hi_act (N p : ℕ) (hN : 0 < N) (hp : p.Prime) (hc : Nat.Coprime p (l * N))
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gam N l) :
    ∃ (π : Equiv.Perm (Fin (p + 1))) (g : Fin (p + 1) → SL(2, ℤ)), (∀ i, g i ∈ Gam N l) ∧ ∀ a : X.Fn l,
      X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeT N l p a) =
        ∑ i, X.act l (GlobalTheory.HeckeFamilyMatrices.tqFam p (sgD N l p) (π i)) (X.act l (g i : Matrix (Fin 2) (Fin 2) ℤ) a) := by
  obtain ⟨π, hπ⟩ := hi_perm N l p (Fact.out) hN hp hc γ hγ
  choose g hg he using hπ
  refine ⟨π, g, hg, fun a => ?_⟩
  have hd1 : ∀ δ : SL(2, ℤ), 0 < (δ : Matrix (Fin 2) (Fin 2) ℤ).det := fun δ => by rw [δ.det_coe]; exact one_pos

  rw [hi_sum X l N p a, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [GlobalTheory.KZ.Tower.act_act Ω ε X l _ _ (hi_det p hp.pos _ i) (hd1 γ), GlobalTheory.KZ.Tower.act_act Ω ε X l _ _ (hd1 (g i)) (hi_det p hp.pos _ (π i)), he i]

private theorem hi_pol_sum (w : ℕ) {ι : Type} (S : Finset ι) (t : ι → X.Fn l) (h : ∀ i, t i ∈ X.Pol l w) :
    ∑ i ∈ S, t i ∈ X.Pol l w := by
  choose c hcA hcu using h
  refine ⟨fun k => ∑ i ∈ S, c i k, fun k => Submodule.sum_mem _ fun i _ => hcA i k, fun u => ?_⟩
  simp only [Finset.sum_apply, hcu, Finset.smul_sum]
  rw [Finset.sum_comm]

private theorem hi_rep_sum (n : ℕ) {ι : Type} (S : Finset ι) (c : ι → X.Khat l)
    (h : ∀ i, ∃ f ∈ X.Un (l ^ n), UpperTheory.Kd.K4.Rep X l n f (c i)) : ∃ f ∈ X.Un (l ^ n), UpperTheory.Kd.K4.Rep X l n f (∑ i ∈ S, c i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨1, fun W _ => ⟨1, by simp⟩, ?_⟩
    simp [UpperTheory.Kd.K4.Rep, GlobalTheory.KZ.Tower.cls]
  | insert i S hi ih =>
    obtain ⟨f, hf, hr⟩ := ih
    obtain ⟨f', hf', hr'⟩ := h i
    refine ⟨f' * f, fun W hW => ?_, ?_⟩
    · obtain ⟨g, hg⟩ := hf W hW
      obtain ⟨g', hg'⟩ := hf' W hW
      refine ⟨g' * g, ?_⟩
      have : ((f' * f : X.Kˣ) : X.K) / ((g' * g : X.Kˣ) : X.K) ^ (l ^ n) = ((f' : X.K) / (g' : X.K) ^ (l ^ n)) * ((f : X.K) / (g : X.K) ^ (l ^ n)) := by
        rw [Units.val_mul, Units.val_mul, mul_pow, div_mul_div_comm]
      rw [this, map_mul, hg, hg', one_mul]
    · unfold UpperTheory.Kd.K4.Rep at *
      rw [Finset.sum_insert hi, map_add (f := _), hr, hr']
      simp only [GlobalTheory.KZ.Tower.cls, ofMul_mul, TensorProduct.tmul_add, Submodule.Quotient.mk_add]

private theorem hi_polMod_sum (w n : ℕ) {ι : Type} (S : Finset ι) (t : ι → X.Fn l) (h : ∀ i, PolMod X l w n (t i)) :
    PolMod X l w n (∑ i ∈ S, t i) := by
  choose c hc hcu using h
  refine ⟨fun k => ∑ i ∈ S, c i k, fun k => hi_rep_sum X l n S (fun i => c i k) (fun i => hc i k), fun u => ?_⟩
  simp only [Finset.sum_apply, hcu, Finset.smul_sum]
  rw [Finset.sum_comm]

private theorem hi_B [IsAlgClosure ℚ Ω] (N w p : ℕ) (hN : 0 < N) (hp : p.Prime) (hc : Nat.Coprime p (l * N))
    (b : X.Fn l) (hb : b ∈ X.B N l w) : X.heckeT N l p b ∈ X.B N l w := by
  have hA := (GlobalTheory.KZ.kmap_A_stable ε X ε.injective (by obtain ⟨φ, h1, h2⟩ := X.j_hol; exact ⟨φ, h2, h1⟩) l).1
  have key : ∀ x ∈ X.BSet N l w, X.heckeT N l p x ∈ X.BSet N l w := by
    rintro x ⟨hxP, hxI⟩
    refine ⟨?_, fun γ hγ => ?_⟩
    · rw [hi_sum X l N p x]
      exact hi_pol_sum X l w Finset.univ _ (fun i => GlobalTheory.T.intMatrixAction_mem_homogeneousPolyFunctions X l w _ (fun a ha => hA _ a ha) x hxP)
    · obtain ⟨π, g, hg, he⟩ := hi_act X l N p hN hp hc γ hγ
      rw [he x, hi_sum X l N p x]
      calc _ = ∑ i, X.act l (GlobalTheory.HeckeFamilyMatrices.tqFam p (sgD N l p) (π i)) x :=
            Finset.sum_congr rfl fun i _ => by rw [hxI _ (hg i)]
        _ = _ := Equiv.sum_comp π (fun i => X.act l (GlobalTheory.HeckeFamilyMatrices.tqFam p (sgD N l p) i) x)
  have hle : X.B N l w ≤ (X.B N l w).comap (X.heckeT N l p) :=
    Submodule.span_le.2 (fun x hx => Submodule.subset_span (key x hx))
  exact hle hb

end UpperTheory.V.Z.Kato.Nb

theorem UpperTheory.V.Z.Kato.Nb.sHeckeInv :
    UpperTheory.V.Z.Kato.Nb.SHeckeInv := by
  intro Ω _ _ _ ε X l _ N w n p hN hp hc a ha
  obtain ⟨⟨t, hPt, hCt⟩, hinv, b, hbB, hbL⟩ := ha
  obtain ⟨hEq, -, -, hSum, -, hAct, -⟩ := sApi Ω ε X l n
  have hPolAct := (sInvApi Ω ε X l N w n).2.2.2.2.2.2.2
  have hH : ∀ x y, CgF X l n x y → CgF X l n (X.heckeT N l p x) (X.heckeT N l p y) := by
    intro x y hxy
    rw [hi_sum X l N p x, hi_sum X l N p y]
    exact hSum _ Finset.univ _ _ (fun i _ => hAct _ _ _ hxy)
  refine ⟨⟨∑ i, X.act l (GlobalTheory.HeckeFamilyMatrices.tqFam p (sgD N l p) i) t, ?_, ?_⟩, fun γ hγ => ?_, X.heckeT N l p b, hi_B X l N w p hN hp hc b hbB, fun u => ?_⟩
  · exact hi_polMod_sum X l w n Finset.univ _ (fun i => hPolAct _ t (hi_det p hp.pos _ i) hPt)
  · rw [hi_sum X l N p a]
    exact hSum _ Finset.univ _ _ (fun i _ => hAct _ _ _ hCt)
  · obtain ⟨π, g, hg, he⟩ := hi_act X l N p hN hp hc γ hγ
    rw [he a]
    have h2 : X.heckeT N l p a = ∑ i, X.act l (GlobalTheory.HeckeFamilyMatrices.tqFam p (sgD N l p) (π i)) a := by
      rw [hi_sum X l N p a]
      exact (Equiv.sum_comp π (fun i => X.act l (GlobalTheory.HeckeFamilyMatrices.tqFam p (sgD N l p) i) a)).symm
    rw [h2]
    exact hSum _ Finset.univ _ _ (fun i _ => hAct _ _ _ (hinv (g i) (hg i)))
  · have hba : CgF X l n b ((l : ℤ_[l]) ^ cL X l N w • a) := fun u => by simpa using hbL u
    have := hH _ _ hba u
    simpa [map_smul] using this
end
