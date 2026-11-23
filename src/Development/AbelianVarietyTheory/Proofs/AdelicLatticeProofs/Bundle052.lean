module

import CompanionTheory.SpectralGeometry.LocalGlobalProofs.HermitianCharacters.SelfDualLatticeFiltrationCharacter
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle011
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NormOneApproximationAtLevelPrimes
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle025
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle009
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle050
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle021
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
import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

noncomputable section

namespace GlobalTheory.QNorm

theorem exists_mem_only (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ a : 𝓞 F, a ≠ 0 ∧ a ∈ v.asIdeal ∧
      ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → a ∉ w.asIdeal := by
  apply GlobalTheory.CompanionTheory.AdeleCharLocal.exists_mem_only <;> assumption

theorem sUnits_rank :
    ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))),
      Module.finrank ℤ (Additive (sUnits F S)) + 1 = S.card + Fintype.card (InfinitePlace F) := by
  intro F _ _ S
  classical
  have hunit : ∀ (u : (𝓞 F)ˣ) (v : HeightOneSpectrum (𝓞 F)),
      v.valuation F (algebraMap (𝓞 F) F u) = 1 := by
    intro u v
    rw [HeightOneSpectrum.valuation_eq_one_iff_notMem]
    intro hu
    exact v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hu u.isUnit)
  let f0 : (𝓞 F)ˣ →* sUnits F S :=
    (Units.map (algebraMap (𝓞 F) F).toMonoidHom).codRestrict _
      (fun u => (mem_sUnits F S _).2 fun v _ => hunit u v)
  let f : Additive (𝓞 F)ˣ →ₗ[ℤ] Additive (sUnits F S) :=
    (MonoidHom.toAdditive f0).toIntLinearMap
  let g0 : Additive (sUnits F S) →+ (S → ℤ) :=
    AddMonoidHom.mk' (fun x v => WithZero.log
      ((v : HeightOneSpectrum (𝓞 F)).valuation F (((Additive.toMul x : sUnits F S) : Fˣ) : F))) (by
      intro a b
      funext v
      simp only [toMul_add, Subgroup.coe_mul, Units.val_mul, map_mul, Pi.add_apply]
      exact WithZero.log_mul (by simp) (by simp))
  let g := g0.toIntLinearMap
  have hker : LinearMap.ker g = LinearMap.range f := by
    apply le_antisymm
    · intro x hx
      set y : Fˣ := ((Additive.toMul x : sUnits F S) : Fˣ) with hy
      have hall : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (y : F) = 1 := by
        intro v
        by_cases hv : v ∈ S
        · have h : WithZero.log (v.valuation F (y : F)) = 0 :=
            congrFun (LinearMap.mem_ker.1 hx) ⟨v, hv⟩
          have hne : v.valuation F (y : F) ≠ 0 := by simp
          rw [← WithZero.exp_log hne, h, WithZero.exp_zero]
        · exact (mem_sUnits F S _).1 (Additive.toMul x).2 v hv
      obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F (y : F)
        (fun v => (hall v).le)
      obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F (y : F)⁻¹
        (fun v => by rw [map_inv₀, hall v, inv_one])
      have hab : a * b = 1 := by
        apply IsFractionRing.injective (𝓞 F) F
        rw [map_mul, ha, hb, map_one, mul_inv_cancel₀ y.ne_zero]
      refine ⟨Additive.ofMul (Units.mkOfMulEqOne a b hab), ?_⟩
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Units.ext
      exact ha
    · rintro _ ⟨u, rfl⟩
      rw [LinearMap.mem_ker]
      funext v
      change WithZero.log ((v : HeightOneSpectrum (𝓞 F)).valuation F
        (algebraMap (𝓞 F) F (Additive.toMul u : (𝓞 F)ˣ))) = 0
      rw [hunit, WithZero.log_one]
  have hinj : Function.Injective f := by
    intro a b hab
    apply Additive.toMul.injective
    apply Units.ext
    apply IsFractionRing.injective (𝓞 F) F
    exact congrArg (fun x : Additive (sUnits F S) => (((Additive.toMul x : sUnits F S) : Fˣ) : F)) hab
  have hfin : Module.Finite ℤ (Additive (sUnits F S)) :=
    Module.Finite.iff_addGroup_fg.2 (GroupFG.iff_add_fg.1 (sUnits_fg F S))
  have hrange : Module.finrank ℤ (LinearMap.range g) = S.card := by
    apply le_antisymm
    · refine (Submodule.finrank_le _).trans ?_
      simp
    · have key : ∀ v : S, ∃ c : ℤ, c ≠ 0 ∧ Pi.single v c ∈ LinearMap.range g := by
        intro v
        obtain ⟨a, ha0, hav, haw⟩ := exists_mem_only F v
        have ha0' : algebraMap (𝓞 F) F a ≠ 0 := by simpa using ha0
        have hw : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v →
            w.valuation F (algebraMap (𝓞 F) F a) = 1 := fun w hw =>
          (HeightOneSpectrum.valuation_eq_one_iff_notMem w).2 (haw w hw)
        refine ⟨WithZero.log ((v : HeightOneSpectrum (𝓞 F)).valuation F (algebraMap (𝓞 F) F a)),
          ?_, Additive.ofMul ⟨Units.mk0 _ ha0', (mem_sUnits F S _).2 fun w hwS =>
            hw w (fun e => hwS (e ▸ v.2))⟩, ?_⟩
        · intro h0
          have hne : (v : HeightOneSpectrum (𝓞 F)).valuation F (algebraMap (𝓞 F) F a) ≠ 0 := by
            simpa using ha0
          have h1 : (v : HeightOneSpectrum (𝓞 F)).valuation F (algebraMap (𝓞 F) F a) = 1 := by
            rw [← WithZero.exp_log hne, h0, WithZero.exp_zero]
          exact (HeightOneSpectrum.valuation_eq_one_iff_notMem _).1 h1 hav
        · funext w
          change WithZero.log ((w : HeightOneSpectrum (𝓞 F)).valuation F
            (algebraMap (𝓞 F) F a)) = _
          by_cases hwv : w = v
          · subst hwv; simp
          · rw [Pi.single_eq_of_ne hwv, hw w (fun e => hwv (Subtype.ext e)), WithZero.log_one]
      choose c hc0 hc using key
      have hli : LinearIndependent ℤ (fun v : S => (⟨Pi.single v (c v), hc v⟩ : LinearMap.range g)) :=
        LinearIndependent.of_comp (LinearMap.range g).subtype
          (Pi.linearIndependent_single_of_ne_zero hc0)
      simpa using hli.fintype_card_le_finrank
  have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.ker g)
  rw [g.quotKerEquivRange.finrank_eq, hrange, hker, LinearMap.finrank_range_of_inj hinj,
    NumberField.Units.finrank_eq, NumberField.Units.rank] at h1
  have h2 : 0 < Fintype.card (InfinitePlace F) := Fintype.card_pos
  omega

end GlobalTheory.QNorm

end
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.aeval_sum_elim_eq_zero_of_mem_pts' : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) → ∀ F : MvPolynomial ((ι × ι) ⊕ (ι × ι)) ℚ, (∀ g ∈ Γ, ∀ h ∈ Γ, MvPolynomial.aeval (Sum.elim (fun ij : ι × ι => g ij.1 ij.2) (fun ij : ι × ι => h ij.1 ij.2)) F = (0 : ℂ)) → ∀ (R : Type) [CommRing R] [Algebra ℚ R], ∀ x ∈ pts Γ R, ∀ y ∈ pts Γ R, MvPolynomial.aeval (Sum.elim (fun ij : ι × ι => x ij.1 ij.2) (fun ij : ι × ι => y ij.1 ij.2)) F = (0 : R) := by
  first | exact @GlobalTheory.ClassFin.aeval_sum_elim_eq_zero_of_mem_pts | exact GlobalTheory.ClassFin.aeval_sum_elim_eq_zero_of_mem_pts | (intros; apply GlobalTheory.ClassFin.aeval_sum_elim_eq_zero_of_mem_pts <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct

namespace GlobalTheory.UTrans

theorem tvGen_adjust : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), Module.finrank F E = 2 → IsHerm (c : E →+* E) G → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ m ∈ TvGen (c : E →+* E) G, ∀ b : ℕ, 0 < b → ∀ N : ℕ, ∃ m' ∈ TvGen (c : E →+* E) G, ∃ k e : ℕ, k.Coprime b ∧ ∀ v ∈ L, (∃ w ∈ L, k • (m' *ᵥ v - m *ᵥ v) = b ^ N • w) ∧ b ^ e • (m' *ᵥ v) ∈ L ∧ b ^ e • (m'⁻¹ *ᵥ v) ∈ L := by
  intro F E _ _ _ _ _ c n G hFE hG L hL hsp m hm b hb
  induction hm using Submonoid.closure_induction with
  | mem m hm =>
    intro N
    obtain ⟨x, t, hx, ht, rfl⟩ := hm
    obtain ⟨t', k, e, ht', hk, H⟩ := GlobalTheory.T.exists_traceZero_adjustment_of_hermitian_lattice F E c n G hFE hG L hL hsp x t (b ^ (N + 1)) (by positivity) ht
    have hinv : (tv (c : E →+* E) G x t')⁻¹ = tv (c : E →+* E) G x (-t') := by
      apply Matrix.inv_eq_right_inv
      rw [(GlobalTheory.T.transvection_identities_unitary E n (c : E →+* E) G hG.invol hG.herm).2.2.1, hx]
      ext i j
      simp [tv]
    refine ⟨_, Submonoid.subset_closure ⟨x, t', hx, ht', rfl⟩, k, (N + 1) * e,
      (Nat.coprime_pow_right_iff (Nat.succ_pos N) _ _).1 hk, fun v hv => ?_⟩
    obtain ⟨⟨w, hw, h1⟩, h2, h3⟩ := H v hv
    refine ⟨⟨b • w, L.smul_of_tower_mem _ hw, ?_⟩, ?_, ?_⟩
    · rw [h1, smul_smul, pow_succ]
    · rwa [pow_mul]
    · rwa [pow_mul, hinv]
  | one =>
    intro N
    refine ⟨1, one_mem _, 1, 0, by simp, fun v hv => ⟨⟨0, zero_mem _, by simp⟩, ?_, ?_⟩⟩ <;> simpa using hv
  | mul m₁ m₂ _ _ ih₁ ih₂ =>
    intro N
    obtain ⟨p, -, k₀, e₀, hk₀, H₀⟩ := ih₁ 0
    have hden : ∀ v ∈ L, (k₀ * b ^ e₀) • (m₁ *ᵥ v) ∈ L := by
      intro v hv
      obtain ⟨⟨w, hw, h1⟩, h2, -⟩ := H₀ v hv
      have : (k₀ * b ^ e₀) • (m₁ *ᵥ v) = k₀ • b ^ e₀ • (p *ᵥ v) - b ^ e₀ • (b ^ 0 • w) := by
        rw [← h1]; module
      rw [this]
      exact sub_mem (L.smul_of_tower_mem _ h2) (L.smul_of_tower_mem _ (L.smul_of_tower_mem _ hw))
    obtain ⟨q₂, hq₂, k₂, e₂, hk₂, H₂⟩ := ih₂ (N + e₀)
    obtain ⟨q₁, hq₁, k₁, e₁, hk₁, H₁⟩ := ih₁ (N + e₂)
    refine ⟨q₁ * q₂, mul_mem hq₁ hq₂, k₀ * k₁ * k₂, e₁ + e₂,
      Nat.Coprime.mul_left (Nat.Coprime.mul_left hk₀ hk₁) hk₂, fun v hv => ⟨?_, ?_, ?_⟩⟩
    · obtain ⟨⟨w₂, hw₂, a1⟩, a2, -⟩ := H₂ v hv
      obtain ⟨⟨w₁, hw₁, b1⟩, -, -⟩ := H₁ _ a2
      have hb' : ((b : E) ^ e₂) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hb.ne')
      have b2 : k₁ • (q₁ *ᵥ (q₂ *ᵥ v) - m₁ *ᵥ (q₂ *ᵥ v)) = b ^ N • w₁ := by
        apply smul_right_injective (Fin n → E) hb'
        simp only [Matrix.mulVec_smul] at b1
        linear_combination (norm := module) b1
      have a3 : k₂ • (m₁ *ᵥ (q₂ *ᵥ v) - m₁ *ᵥ (m₂ *ᵥ v)) = b ^ (N + e₀) • (m₁ *ᵥ w₂) := by
        rw [← Matrix.mulVec_smul, ← a1, Matrix.mulVec_smul, Matrix.mulVec_sub]
      refine ⟨(k₀ * k₂) • w₁ + k₁ • (k₀ * b ^ e₀) • (m₁ *ᵥ w₂),
        add_mem (L.smul_of_tower_mem _ hw₁) (L.smul_of_tower_mem _ (hden _ hw₂)), ?_⟩
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      linear_combination (norm := module) (k₀ * k₂) • b2 + (k₀ * k₁) • a3
    · have := (H₁ _ (H₂ v hv).2.1).2.1
      rwa [Matrix.mulVec_smul, smul_smul, ← pow_add, Matrix.mulVec_mulVec] at this
    · have := (H₂ _ (H₁ v hv).2.2).2.2
      rwa [Matrix.mulVec_smul, smul_smul, ← pow_add, Matrix.mulVec_mulVec, ← Matrix.mul_inv_rev, add_comm] at this

end GlobalTheory.UTrans
end

section

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.normOne_approximation_at_level_primes : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E), (∀ x, c (c x) = x) → c ≠ 1 → ∀ (u : E) (N D : ℕ), u * c u = 1 → 0 < N → 0 < D → ∃ u' : E, u' * c u' = 1 ∧ (∃ t : ℕ, t.Coprime N ∧ ∃ b : 𝓞 E, (t : E) * (u' / u - 1) = (D : E) * (b : E)) ∧ ∃ s : 𝓞 E, SplitOr c N s ∧ (∃ b : 𝓞 E, (s : E) * (u' - 1) = (D : E) * (b : E)) ∧ ∃ b : 𝓞 E, (s : E) * (u'⁻¹ - 1) = (D : E) * (b : E) := by
  first | exact @GlobalTheory.UnRep.normOne_approx | exact GlobalTheory.UnRep.normOne_approx | (intros; apply GlobalTheory.UnRep.normOne_approx <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep.SmallMat

open GlobalTheory.AdLat.Translate

theorem exists_dvd_pow_mul_coprime (N m : ℕ) (hm : m ≠ 0) :
    ∃ t k : ℕ, t.Coprime N ∧ m ∣ N ^ k * t := by
  induction m using induction_on_primes with
  | zero => exact absurd rfl hm
  | one => exact ⟨1, 0, by simp, by simp⟩
  | prime_mul p a hp ih =>
    obtain ⟨t, k, ht, h⟩ := ih (right_ne_zero_of_mul hm)
    by_cases hpN : p ∣ N
    · refine ⟨t, k + 1, ht, ?_⟩
      rw [pow_succ', mul_assoc]
      exact mul_dvd_mul hpN h
    · refine ⟨p * t, k, Nat.Coprime.mul_left ((Nat.Prime.coprime_iff_not_dvd hp).2 hpN) ht, ?_⟩
      rw [mul_left_comm]
      exact mul_dvd_mul_left p h

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem exists_indicator (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ e : FiniteAdeleRing (𝓞 F) F, (∀ v ∈ S, e v = 1) ∧ ∀ v ∉ S, e v = 0 := by
  classical
  refine ⟨⟨fun v => if v ∈ S then 1 else 0, Filter.Eventually.of_forall fun v => ?_⟩,
    fun v hv => if_pos hv, fun v hv => if_neg hv⟩
  beta_reduce
  split_ifs
  · exact one_mem (v.adicCompletionIntegers F)
  · exact zero_mem (v.adicCompletionIntegers F)

theorem exists_nsmul_integral (b : FiniteAdeleRing (𝓞 F) F) :
    ∃ m : ℕ, m ≠ 0 ∧ ∀ v, (m • b) v ∈ v.adicCompletionIntegers F := by
  obtain ⟨x, a, ha, rfl⟩ := exists_eq_algebraMap_add_nsmul F 1 one_pos b
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ ({x} : Finset F)
  have hc : IsIntegral ℤ (y • x) := hy x (by simp)
  have hc' : IsIntegral ℤ (y.natAbs • x) := by
    rcases Int.natAbs_eq y with h | h
    · have : y.natAbs • x = y • x := by
        conv_rhs => rw [h]
        simp
      rw [this]; exact hc
    · have : y.natAbs • x = -(y • x) := by
        conv_rhs => rw [h]
        simp
      rw [this]; exact hc.neg
  refine ⟨y.natAbs, Int.natAbs_ne_zero.2 hy0, fun v => ?_⟩
  rw [smul_add, ← map_nsmul]
  refine add_mem ?_ (nsmul_mem (nsmul_mem (ha v) 1) _)
  exact v.coe_mem_adicCompletionIntegers (K := F) (⟨y.natAbs • x, hc'⟩ : 𝓞 F)

theorem exists_coprime_nsmul_integral (N : ℕ) (b : FiniteAdeleRing (𝓞 F) F)
    (hb : ∀ v : HeightOneSpectrum (𝓞 F), (N : 𝓞 F) ∈ v.asIdeal → b v = 0) :
    ∃ t : ℕ, t.Coprime N ∧ ∀ v, (t • b) v ∈ v.adicCompletionIntegers F := by
  obtain ⟨m, hm, h⟩ := exists_nsmul_integral b
  obtain ⟨t, k, ht, c, hc⟩ := exists_dvd_pow_mul_coprime N m hm
  refine ⟨t, ht, fun v => ?_⟩
  change t • b v ∈ _
  by_cases hv : (N : 𝓞 F) ∈ v.asIdeal
  · rw [hb v hv, smul_zero]; exact zero_mem _
  · have h1 : c • (m • b v) ∈ v.adicCompletionIntegers F := nsmul_mem (h v) c
    rw [smul_smul, mul_comm, ← hc, mul_smul, nsmul_eq_mul,
      HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, Nat.cast_pow, map_pow] at h1
    have hN : Valued.v ((N : ℕ) : v.adicCompletion F) = 1 := by
      have h1 := (v.valuation_eq_one_iff_notMem (K := F)).mpr hv
      have h2 := v.valuedAdicCompletion_eq_valuation' (K := F) ((N : ℕ) : F)
      have h3 : (algebraMap F (v.adicCompletion F)) ((N : ℕ) : F) =
        ((N : ℕ) : v.adicCompletion F) := map_natCast _ _
      rw [← h3]
      have h4 : (((N : ℕ) : 𝓞 F) : F) = ((N : ℕ) : F) :=
        map_natCast (algebraMap (𝓞 F) F) _
      exact h2.trans (h4 ▸ h1)
    rw [hN, one_pow, one_mul] at h1
    exact h1

theorem fm_add (A B : Matrix (Fin n) (Fin n) E) : fm F (A + B) = fm F A + fm F B := by
  ext i j
  simp [fm, TensorProduct.tmul_add]

theorem fm_zero : fm F (0 : Matrix (Fin n) (Fin n) E) = 0 := by
  ext i j
  simp [fm]

theorem nsmul_tmul_one (d : ℕ) (a : FiniteAdeleRing (𝓞 F) F) :
    ((d • a) ⊗ₜ[F] (1 : E) : RA F E) = d • (a ⊗ₜ[F] (1 : E) : RA F E) := by
  induction d with
  | zero => simp
  | succ d ih => rw [succ_nsmul, succ_nsmul, TensorProduct.add_tmul, ih]

theorem exists_approx (S : Set (Fin n → E))
    (hS : ∀ M : Matrix (Fin n) (Fin n) (RA F E), ∃ d : ℕ, 0 < d ∧ ∀ z ∈ hat F S, d • (M *ᵥ z) ∈ hat F S)
    (M : Matrix (Fin n) (Fin n) (RA F E)) (D : ℕ) (hD : 0 < D) :
    ∃ M₀ : Matrix (Fin n) (Fin n) E, ∀ z ∈ hat F S, ∃ w ∈ hat F S, (M - fm F M₀) *ᵥ z = D • w := by
  let P : Matrix (Fin n) (Fin n) (RA F E) → Prop := fun M =>
    ∃ M₀ : Matrix (Fin n) (Fin n) E, ∀ z ∈ hat F S, ∃ w ∈ hat F S, (M - fm F M₀) *ᵥ z = D • w
  have hadd : ∀ A B, P A → P B → P (A + B) := by
    rintro A B ⟨A₀, hA⟩ ⟨B₀, hB⟩
    refine ⟨A₀ + B₀, fun z hz => ?_⟩
    obtain ⟨u, hu, hu'⟩ := hA z hz
    obtain ⟨w, hw, hw'⟩ := hB z hz
    refine ⟨u + w, add_mem hu hw, ?_⟩
    rw [smul_add, ← hu', ← hw', ← Matrix.add_mulVec, fm_add, add_sub_add_comm]
  have hzero : P 0 := ⟨0, fun z _ => ⟨0, zero_mem _, by simp [fm_zero]⟩⟩
  have hgen : ∀ (a : FiniteAdeleRing (𝓞 F) F) (B : Matrix (Fin n) (Fin n) E),
      P ((a ⊗ₜ[F] (1 : E) : RA F E) • fm F B) := by
    intro a B
    obtain ⟨d, hd, hB⟩ := hS (fm F B)
    obtain ⟨r, a', ha', rfl⟩ := exists_eq_algebraMap_add_nsmul F (D * d) (Nat.mul_pos hD hd) a
    refine ⟨r • B, fun z hz => ⟨_, hat_smul_int ha' (hB z hz), ?_⟩⟩
    have h1 : fm F (r • B) =
        (algebraMap F (FiniteAdeleRing (𝓞 F) F) r ⊗ₜ[F] (1 : E) : RA F E) • fm F B := by
      ext i j
      simp only [fm, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    rw [h1, TensorProduct.add_tmul, add_smul, add_sub_cancel_left, Matrix.smul_mulVec,
      nsmul_tmul_one, smul_assoc, mul_smul, smul_comm d]
  have hsingle : ∀ i j (t : RA F E), P (Matrix.single i j t) := by
    intro i j t
    induction t using TensorProduct.induction_on with
    | zero => rw [Matrix.single_zero]; exact hzero
    | tmul a y =>
      have := hgen a (Matrix.single i j y)
      convert this using 1
      ext k l
      simp only [fm, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, Matrix.single_apply]
      split_ifs <;> simp
    | add s t hs ht => rw [Matrix.single_add]; exact hadd _ _ hs ht
  change P M
  rw [Matrix.matrix_eq_sum_single M]
  exact Finset.sum_induction _ P hadd hzero fun i _ =>
    Finset.sum_induction _ P hadd hzero fun j _ => hsingle i j _

theorem exists_coprime_small (S : Set (Fin n → E)) (N D : ℕ) (e : FiniteAdeleRing (𝓞 F) F)
    (M : Matrix (Fin n) (Fin n) (RA F E)) (hD : 0 < D)
    (hM : ∃ d : ℕ, 0 < d ∧ ∀ z ∈ hat F S, d • (M *ᵥ z) ∈ hat F S)
    (he : ∀ v : HeightOneSpectrum (𝓞 F), (N : 𝓞 F) ∈ v.asIdeal → e v = 0) :
    ∃ t : ℕ, t.Coprime N ∧ ∀ z ∈ hat F S, ∃ w ∈ hat F S,
      t • (((e ⊗ₜ[F] (1 : E) : RA F E) • M) *ᵥ z) = D • w := by
  obtain ⟨d, hd, hM⟩ := hM
  have hK : ((D * d : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 (Nat.mul_pos hD hd).ne'
  set b : FiniteAdeleRing (𝓞 F) F :=
    algebraMap F (FiniteAdeleRing (𝓞 F) F) ((D * d : ℕ) : F)⁻¹ * e with hb
  have hbe : e = (D * d) • b := by
    rw [hb, nsmul_eq_mul, ← mul_assoc, ← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)),
      ← map_mul, mul_inv_cancel₀ hK, map_one, one_mul]
  obtain ⟨t, ht, h⟩ := exists_coprime_nsmul_integral N b fun v hv => by
    change _ * e v = 0
    rw [he v hv, mul_zero]
  refine ⟨t, ht, fun z hz => ⟨_, hat_smul_int h (hM z hz), ?_⟩⟩
  rw [hbe, Matrix.smul_mulVec, nsmul_tmul_one, nsmul_tmul_one, smul_assoc, smul_assoc, mul_smul,
    smul_comm t D, smul_comm d]

end GlobalTheory.UnRep.SmallMat


open GlobalTheory.UnRep.SmallMat GlobalTheory.AdLat.Translate in
theorem GlobalTheory.UnRep.idempotent_adeles_small_matrices : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ), ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → (∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∃ e : FiniteAdeleRing (𝓞 F) F, (∀ v ∈ S, e v = 1) ∧ ∀ v ∉ S, e v = 0) ∧ (∀ M : Matrix (Fin n) (Fin n) (RA F E), ∃ d : ℕ, 0 < d ∧ ∀ z ∈ hat F (L : Set (Fin n → E)), d • (M *ᵥ z) ∈ hat F (L : Set (Fin n → E))) ∧ (∀ (M : Matrix (Fin n) (Fin n) (RA F E)) (D : ℕ), 0 < D → ∃ M₀ : Matrix (Fin n) (Fin n) E, ∀ z ∈ hat F (L : Set (Fin n → E)), ∃ w ∈ hat F (L : Set (Fin n → E)), (M - fm F M₀) *ᵥ z = D • w) ∧ (∀ (N D : ℕ) (e : FiniteAdeleRing (𝓞 F) F) (M : Matrix (Fin n) (Fin n) (RA F E)), 0 < D → (∀ v : HeightOneSpectrum (𝓞 F), (N : 𝓞 F) ∈ v.asIdeal → e v = 0) → ∃ t : ℕ, t.Coprime N ∧ ∀ z ∈ hat F (L : Set (Fin n → E)), ∃ w ∈ hat F (L : Set (Fin n → E)), t • (((e ⊗ₜ[F] (1 : E)) • M) *ᵥ z) = D • w) ∧ ∀ (a : FiniteAdeleRing (𝓞 F) F), (∀ v, a v ∈ v.adicCompletionIntegers F) → ∀ z ∈ hat F (L : Set (Fin n → E)), (a ⊗ₜ[F] (1 : E)) • z ∈ hat F (L : Set (Fin n → E)) := by
  intro F E _ _ _ _ _ n L hL hsp
  have h4 := (GlobalTheory.AdLat.hat_rational_points_and_approx F E n L hL hsp).2.2.2
  have h2 := fun M : Matrix (Fin n) (Fin n) (RA F E) => exists_bound M hL h4
  exact ⟨exists_indicator, h2, exists_approx _ h2,
    fun N D e M hD he => exists_coprime_small _ N D e M hD (h2 M) he,
    fun a ha z hz => hat_smul_int ha hz⟩
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.pow_countPlacesNotLocalPower_le_index : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (ζ δ : F) (S : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → (finNorm p F δ S).index ≠ 0 ∧ p ^ tNon p F δ S ≤ (finNorm p F δ S).index := by
  first | exact @GlobalTheory.CNorm.pow_tNon_le_index_finNorm | exact GlobalTheory.CNorm.pow_tNon_le_index_finNorm | (intros; apply GlobalTheory.CNorm.pow_tNon_le_index_finNorm <;> assumption)
end
