module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle346
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle349
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle093
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle208
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlMulToRingEquiv
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle115
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle342
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle023
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle018
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003

@[expose] public section

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.GamComm

theorem intCast_eq_of_dvd {K M : ℕ} (hK : K ∣ M) {x y : ℤ} (h : (x : ZMod M) = y) : (x : ZMod K) = y := by
  simpa only [map_intCast] using congrArg (ZMod.castHom hK (ZMod K)) h

theorem gamma_le_of_dvd {K M : ℕ} (hK : K ∣ M) : CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma K := by
  intro γ hγ
  obtain ⟨h1, h2, h3, h4⟩ := CongruenceSubgroup.Gamma_mem.1 hγ
  refine CongruenceSubgroup.Gamma_mem.2 ⟨?_, ?_, ?_, ?_⟩
  · simpa using intCast_eq_of_dvd hK (y := 1) (by simpa using h1)
  · simpa using intCast_eq_of_dvd hK (y := 0) (by simpa using h2)
  · simpa using intCast_eq_of_dvd hK (y := 0) (by simpa using h3)
  · simpa using intCast_eq_of_dvd hK (y := 1) (by simpa using h4)

theorem mul_inv_mem_Gam (N l : ℕ) (g δ : SL(2, ℤ))
    (hg : g ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l)
    (hδ : δ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l)
    (h00 : (en δ 0 0 : ZMod N) = en g 0 0) (h11 : (en δ 1 1 : ZMod N) = en g 1 1) : g * δ⁻¹ ∈ Gam N l := by
  refine Subgroup.mem_inf.2 ⟨?_, mul_mem (Subgroup.mem_inf.1 hg).2 (inv_mem (Subgroup.mem_inf.1 hδ).2)⟩
  have a1 : (en g 1 0 : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.1 (Subgroup.mem_inf.1 hg).1
  have a2 : (en δ 1 0 : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.1 (Subgroup.mem_inf.1 hδ).1
  have hdet : (en δ 0 0 : ZMod N) * en δ 1 1 - en δ 0 1 * en δ 1 0 = 1 := by
    have h := δ.det_coe
    rw [Matrix.det_fin_two] at h
    have := congrArg (Int.cast : ℤ → ZMod N) h
    simpa [en] using this
  have e00 : en (g * δ⁻¹) 0 0 = en g 0 0 * en δ 1 1 - en g 0 1 * en δ 1 0 := by
    simp [en, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have e10 : en (g * δ⁻¹) 1 0 = en g 1 0 * en δ 1 1 - en g 1 1 * en δ 1 0 := by
    simp [en, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have e11 : en (g * δ⁻¹) 1 1 = en g 1 1 * en δ 0 0 - en g 1 0 * en δ 0 1 := by
    simp [en, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  refine (CongruenceSubgroup.Gamma1_mem N _).2 ⟨?_, ?_, ?_⟩
  · change ((en (g * δ⁻¹) 0 0 : ℤ) : ZMod N) = 1
    rw [e00]; push_cast
    linear_combination hdet - (en δ 1 1 : ZMod N) * h00 + ((en δ 0 1 : ZMod N) - en g 0 1) * a2
  · change ((en (g * δ⁻¹) 1 1 : ℤ) : ZMod N) = 1
    rw [e11]; push_cast
    linear_combination hdet - (en δ 0 0 : ZMod N) * h11 + (en δ 0 1 : ZMod N) * a2 - (en δ 0 1 : ZMod N) * a1
  · change ((en (g * δ⁻¹) 1 0 : ℤ) : ZMod N) = 0
    rw [e10]; push_cast
    rw [a1, a2]; ring

theorem act_galB_comm : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (N l w : ℕ) [Fact l.Prime], 1 ≤ N → ∀ b ∈ X.BSet N l w, ∀ δ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l, ∀ s : Ω ≃ₐ[ℚ] Ω, X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) (X.galB l s b) = X.galB l s (X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) b) := by
  intro Ω _ _ _ ε X N l w _ hN b hb δ hδ s
  funext u
  refine AdicCompletion.ext fun n => ?_
  have hcls := GlobalTheory.KZ.H3.cls_props Ω ε X l n
  have hF := hcls.2.2.2.2.2.1
  obtain ⟨f, hf⟩ := hcls.1 (AdicCompletion.eval (idl l) (X.Kl l) n
    (b ![(mZl l (δ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0,
      (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * (mZl l (δ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 1]))
  obtain ⟨M₀, hM₀, hlev⟩ := X.level (f : X.K)
  have hlp : 0 < l := (Fact.out : l.Prime).pos
  obtain ⟨M, hM, hM0, hMN, hMl, hMn⟩ : ∃ M : ℕ, 0 < M ∧ M₀ ∣ M ∧ N ∣ M ∧ l ∣ M ∧ l ^ n ∣ M :=
    ⟨M₀ * N * l * l ^ n, by positivity, ⟨N * l * l ^ n, by ring⟩, ⟨M₀ * l * l ^ n, by ring⟩,
      ⟨M₀ * N * l ^ n, by ring⟩, ⟨M₀ * N * l, by ring⟩⟩
  obtain ⟨ζ, hζ, i, hi, hs, hχ⟩ := GlobalTheory.exists_primitiveRoot_pow_cyclotomicCharacter l n M hM hMn s
  obtain ⟨g, h00, h01, h10, h11⟩ := GlobalTheory.exists_sl2_conj_diag_zmod M i hi δ
  have hc : (en δ 0 0 : ZMod M) = en g 0 0 ∧ (en δ 0 1 : ZMod M) = ((i : ℤ) : ZMod M) * en g 0 1 ∧
      ((i : ℤ) : ZMod M) * en δ 1 0 = en g 1 0 ∧ (en δ 1 1 : ZMod M) = en g 1 1 :=
    ⟨h00, by simpa only [Int.cast_natCast] using h01, by simpa only [Int.cast_natCast] using h10, h11⟩
  have hrec := X.recip M f hM (fun γ hγ => hlev γ (gamma_le_of_dvd hM0 hγ)) ζ hζ s i
    (by rw [zpow_natCast, hs]) g δ hc
  have h10' : (((i : ℤ) * en δ 1 0 : ℤ) : ZMod M) = en g 1 0 := by push_cast; exact h10
  have hg0 : ∀ K : ℕ, K ∣ M → δ ∈ CongruenceSubgroup.Gamma0 K → g ∈ CongruenceSubgroup.Gamma0 K := fun K hK h => by
    have a : (en δ 1 0 : ZMod K) = 0 := CongruenceSubgroup.Gamma0_mem.1 h
    refine CongruenceSubgroup.Gamma0_mem.2 ((intCast_eq_of_dvd hK h10').symm.trans ?_)
    rw [Int.cast_mul, a, mul_zero]
  have hgam : g * δ⁻¹ ∈ Gam N l :=
    mul_inv_mem_Gam N l g δ
      (Subgroup.mem_inf.2 ⟨hg0 N hMN (Subgroup.mem_inf.1 hδ).1, hg0 l hMl (Subgroup.mem_inf.1 hδ).2⟩) hδ
      (intCast_eq_of_dvd hMN h00) (intCast_eq_of_dvd hMN h11)
  have hact : X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) b = X.act l (g : Matrix (Fin 2) (Fin 2) ℤ) b := by
    have e : (g : Matrix (Fin 2) (Fin 2) ℤ) =
        ((g * δ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (δ : Matrix (Fin 2) (Fin 2) ℤ) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right]
    rw [e, ← Tower.act_act Ω ε X l _ _ (by rw [Matrix.SpecialLinearGroup.det_coe]; exact one_pos)
      (by rw [Matrix.SpecialLinearGroup.det_coe]; exact one_pos), hb.2 _ hgam]
  have hpol := StabGal.eval_Pol_congr X l w b hb.1 n _ _
    (StabGal.twist_congr l n M hMn δ g i (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) hc
      (by simpa only [Int.cast_natCast] using hχ) u)
  rw [hact]
  have hL := hF (X.sl (toGQ (δ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv _ _ (hF (X.gal s) _ _ hf.symm)
  have hR := hF (X.gal s) _ _ (hF (X.sl (toGQ (g : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv _ _ (hpol.symm.trans hf.symm))
  refine hL.trans (Eq.trans ?_ hR.symm)
  congr 1
  apply Units.ext
  change X.sl (toGQ (δ : Matrix (Fin 2) (Fin 2) ℤ)) (X.gal s f) = X.gal s (X.sl (toGQ (g : Matrix (Fin 2) (Fin 2) ℤ)) f)
  rw [StabGal.toGQ_SL, StabGal.toGQ_SL, hrec]

end GlobalTheory.KZ.GamComm
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory


open Polynomial in
theorem coefO_dvd_pow_l {l : ℕ} [Fact l.Prime] (c : Coef l) {x : Qbar l} (hx : x ∈ c.O)
    (h0 : x ≠ 0) : ∃ k : ℕ, ∃ u ∈ c.O, x * u = ((l : ℕ) : Qbar l) ^ k := by
  haveI := c.fin
  haveI := c.dvr
  set x' : c.O := ⟨x, hx⟩
  have hx0 : x' ≠ 0 := fun h => h0 (congrArg Subtype.val h)
  have hint : IsIntegral ℤ_[l] x' := Algebra.IsIntegral.isIntegral x'
  obtain ⟨p, hpm, hp⟩ := hint
  rw [← aeval_def] at hp
  obtain ⟨q, hpq, hq⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hpm.ne_zero 0
  simp only [map_zero, sub_zero] at hpq hq
  rw [X_dvd_iff] at hq
  have hqx : aeval x' q = 0 := by
    rw [hpq, map_mul, map_pow, aeval_X] at hp
    exact (mul_eq_zero.mp hp).resolve_left (pow_ne_zero _ hx0)
  obtain ⟨r, hr⟩ := (X_dvd_sub_C : X ∣ q - C (q.coeff 0))
  have hrel : algebraMap ℤ_[l] c.O (q.coeff 0) = x' * (-(aeval x' r)) := by
    have := congrArg (aeval x') hr
    rw [map_sub, aeval_C, map_mul, aeval_X, hqx] at this
    linear_combination -this
  set a := q.coeff 0 with ha
  set w : ℤ_[l]ˣ := PadicInt.unitCoeff hq
  have hspec : a = (w : ℤ_[l]) * (l : ℤ_[l]) ^ a.valuation := PadicInt.unitCoeff_spec hq
  have haw : a * ((w⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) = (l : ℤ_[l]) ^ a.valuation := by
    calc a * ((w⁻¹ : ℤ_[l]ˣ) : ℤ_[l])
        = ((w : ℤ_[l]) * (l : ℤ_[l]) ^ a.valuation) * ((w⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) := by rw [← hspec]
      _ = (l : ℤ_[l]) ^ a.valuation := by
        rw [mul_comm, ← mul_assoc]; simp
  refine ⟨a.valuation, (((-(aeval x' r)) * algebraMap ℤ_[l] c.O ((w⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) : c.O) : Qbar l),
    Subtype.property _, ?_⟩
  have h2 : x' * ((-(aeval x' r)) * algebraMap ℤ_[l] c.O ((w⁻¹ : ℤ_[l]ˣ) : ℤ_[l]))
      = algebraMap ℤ_[l] c.O ((l : ℤ_[l]) ^ a.valuation) := by
    rw [← mul_assoc, ← hrel, ← map_mul, haw]
  have h3 := congrArg Subtype.val h2
  simpa using h3

end GlobalTheory

namespace GlobalTheory

theorem rat_unram_to_int_unram : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l) (B : ValuationSubring Ω), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → ∃ m : ℕ, ∀ (Y : G ℚ Ω → Fin 2 → Qbar l) (v : Fin 2 → Qbar l), (∀ s i, Y s i ∈ c.O) → (∀ s ∈ Ine (F := ℚ) B, Y s = mat W s *ᵥ v - v) → ∃ t : Fin 2 → Qbar l, (∀ i, t i ∈ c.O) ∧ ∀ s ∈ Ine (F := ℚ) B, (((l : ℕ) : Qbar l) ^ m) • Y s = mat W s *ᵥ t - t := by
  intro l _ Ω _ _ W c B _hW hWO
  let A : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l) := fun s => mat W s - 1
  have hAO : ∀ s i j, A s i j ∈ c.O := by
    intro s i j
    simp only [A, Matrix.sub_apply, Matrix.one_apply]
    split_ifs
    · exact sub_mem (hWO s i j) (one_mem _)
    · simpa using hWO s i j
  have hmv : ∀ s (w : Fin 2 → Qbar l) i,
      (mat W s *ᵥ w - w) i = A s i 0 * w 0 + A s i 1 * w 1 := by
    intro s w i
    rw [show mat W s *ᵥ w - w = A s *ᵥ w by simp [A, Matrix.sub_mulVec]]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  by_cases h2 : ∃ s ∈ Ine (F := ℚ) B, ∃ s' ∈ Ine (F := ℚ) B, ∃ i i' : Fin 2,
      A s i 0 * A s' i' 1 - A s i 1 * A s' i' 0 ≠ 0
  · obtain ⟨s, hs, s', hs', i, i', hd⟩ := h2
    obtain ⟨k, u, hu, hdu⟩ := coefO_dvd_pow_l c
      (sub_mem (mul_mem (hAO s i 0) (hAO s' i' 1)) (mul_mem (hAO s i 1) (hAO s' i' 0))) hd
    refine ⟨k, fun Y v hY hYv => ⟨((l : ℕ) : Qbar l) ^ k • v, ?_, ?_⟩⟩
    · have hP := hY s i
      have hQ := hY s' i'
      rw [hYv s hs, hmv] at hP
      rw [hYv s' hs', hmv] at hQ
      intro j
      fin_cases j
      · have e : ((l : ℕ) : Qbar l) ^ k • v 0 = u * (A s' i' 1 * (A s i 0 * v 0 + A s i 1 * v 1)
            - A s i 1 * (A s' i' 0 * v 0 + A s' i' 1 * v 1)) := by
          rw [smul_eq_mul]; linear_combination (-(v 0)) * hdu
        simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply]
        rw [e]
        exact mul_mem hu (sub_mem (mul_mem (hAO _ _ _) hP) (mul_mem (hAO _ _ _) hQ))
      · have e : ((l : ℕ) : Qbar l) ^ k • v 1 = u * (A s i 0 * (A s' i' 0 * v 0 + A s' i' 1 * v 1)
            - A s' i' 0 * (A s i 0 * v 0 + A s i 1 * v 1)) := by
          rw [smul_eq_mul]; linear_combination (-(v 1)) * hdu
        simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply]
        rw [e]
        exact mul_mem hu (sub_mem (mul_mem (hAO _ _ _) hQ) (mul_mem (hAO _ _ _) hP))
    · intro s₀ hs₀
      rw [hYv s₀ hs₀, smul_sub, Matrix.mulVec_smul]
  · push_neg at h2
    by_cases h1 : ∃ s ∈ Ine (F := ℚ) B, ∃ i j, A s i j ≠ 0
    · obtain ⟨s, hs, i, j, hα⟩ := h1
      obtain ⟨k, u, hu, hαu⟩ := coefO_dvd_pow_l c (hAO s i j) hα
      refine ⟨k, fun Y v hY hYv => ⟨Pi.single j (u * Y s i), ?_, ?_⟩⟩
      · intro j'
        rcases eq_or_ne j' j with rfl | h
        · simpa using mul_mem hu (hY s i)
        · simp [h]
      · intro s' hs'
        have hc : Y s i = A s i 0 * v 0 + A s i 1 * v 1 := by rw [hYv s hs, hmv]
        ext i'
        rw [Pi.smul_apply, hmv, hYv s' hs', hmv, hc]
        have hdet := h2 s hs s' hs' i i'
        fin_cases j
        · simp only [Fin.zero_eta, Fin.isValue] at hαu ⊢
          simp [Pi.single_apply]
          linear_combination (-(A s' i' 0 * v 0 + A s' i' 1 * v 1)) * hαu + u * v 1 * hdet
        · simp only [Fin.mk_one, Fin.isValue] at hαu ⊢
          simp [Pi.single_apply]
          linear_combination (-(A s' i' 0 * v 0 + A s' i' 1 * v 1)) * hαu - u * v 0 * hdet
    · push_neg at h1
      refine ⟨0, fun Y v _ hYv => ⟨0, fun _ => zero_mem _, fun s hs => ?_⟩⟩
      ext i
      rw [Pi.smul_apply, hYv s hs, hmv, hmv]
      simp [h1 s hs]

end GlobalTheory
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

namespace GlobalTheory.KumUnit

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem cg_trans {m : ℕ} {x y z : Qbar l} (h : Cg m x y) (h' : Cg m y z) : Cg m x z := by
  unfold Cg at *
  have hm := IsUltrametricDist.norm_add_le_max (x - y) (y - z)
  rw [sub_add_sub_cancel] at hm
  exact hm.trans (max_le h h')

theorem cg_symm {m : ℕ} {x y : Qbar l} (h : Cg m x y) : Cg m y x := by
  unfold Cg at *
  rwa [norm_sub_rev]

theorem cg_sum {m : ℕ} {ι : Type} (S : Finset ι) {x y : ι → Qbar l} (h : ∀ i ∈ S, Cg m (x i) (y i)) :
    Cg m (∑ i ∈ S, x i) (∑ i ∈ S, y i) := by
  unfold Cg
  rw [← Finset.sum_sub_distrib]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) h

theorem cg_mul_left {m : ℕ} {o x y : Qbar l} (ho : ‖o‖ ≤ 1) (h : Cg m x y) : Cg m (o * x) (o * y) := by
  unfold Cg at *
  rw [← mul_sub, norm_mul]
  calc ‖o‖ * ‖x - y‖ ≤ 1 * ‖x - y‖ := mul_le_mul_of_nonneg_right ho (norm_nonneg _)
    _ = ‖x - y‖ := one_mul _
    _ ≤ _ := h

end GlobalTheory.KumUnit
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory.InertCoh

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def cob (W : R2 Ω l) (c : Coef l) (I : Subgroup (G ℚ Ω)) : Submodule c.O (G ℚ Ω → Fin 2 → Qbar l) where
  carrier := {z | ∃ v : Fin 2 → Qbar l, ∀ s ∈ I, z s = mat W s *ᵥ v - v}
  zero_mem' := ⟨0, fun s _ => by simp⟩
  add_mem' := by
    rintro a b ⟨v, hv⟩ ⟨w, hw⟩
    refine ⟨v + w, fun s hs => ?_⟩
    simp only [Pi.add_apply, hv s hs, hw s hs, Matrix.mulVec_add]
    abel
  smul_mem' := by
    rintro k a ⟨v, hv⟩
    refine ⟨k • v, fun s hs => ?_⟩
    simp only [Pi.smul_apply, hv s hs, Matrix.mulVec_smul, smul_sub]

def coc (W : R2 Ω l) (c : Coef l) (I : Subgroup (G ℚ Ω)) : Submodule c.O (G ℚ Ω → Fin 2 → Qbar l) where
  carrier := {z | (∀ i, Continuous fun s => z s i) ∧ (∀ s i, z s i ∈ c.O) ∧
    ∀ s ∈ I, ∀ t ∈ I, z (s * t) = z s + mat W s *ᵥ z t}
  zero_mem' := ⟨fun i => continuous_const, fun s i => c.O.zero_mem, fun s _ t _ => by simp⟩
  add_mem' := by
    rintro a b ⟨ha1, ha2, ha3⟩ ⟨hb1, hb2, hb3⟩
    refine ⟨fun i => (ha1 i).add (hb1 i), fun s i => c.O.add_mem (ha2 s i) (hb2 s i), fun s hs t ht => ?_⟩
    simp only [Pi.add_apply, ha3 s hs t ht, hb3 s hs t ht, Matrix.mulVec_add]
    abel
  smul_mem' := by
    rintro k a ⟨ha1, ha2, ha3⟩
    refine ⟨fun i => ?_, fun s i => ?_, fun s hs t ht => ?_⟩
    · simp only [Pi.smul_apply, Subalgebra.smul_def, smul_eq_mul]
      exact continuous_const.mul (ha1 i)
    · simp only [Pi.smul_apply, Subalgebra.smul_def, smul_eq_mul]
      exact c.O.mul_mem k.2 (ha2 s i)
    · simp only [Pi.smul_apply, ha3 s hs t ht, Matrix.mulVec_smul, smul_add]

theorem mem_cob {W : R2 Ω l} {c : Coef l} {I : Subgroup (G ℚ Ω)} {z : G ℚ Ω → Fin 2 → Qbar l} :
    z ∈ cob W c I ↔ ∃ v : Fin 2 → Qbar l, ∀ s ∈ I, z s = mat W s *ᵥ v - v := Iff.rfl

theorem mem_coc {W : R2 Ω l} {c : Coef l} {I : Subgroup (G ℚ Ω)} {z : G ℚ Ω → Fin 2 → Qbar l} :
    z ∈ coc W c I ↔ (∀ i, Continuous fun s => z s i) ∧ (∀ s i, z s i ∈ c.O) ∧
      ∀ s ∈ I, ∀ t ∈ I, z (s * t) = z s + mat W s *ᵥ z t := Iff.rfl

end GlobalTheory.InertCoh

end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem qbarLVectorCongruent_integralMatrix_mulVec {l : ℕ} [Fact l.Prime] (c : Coef l) (M : Matrix (Fin 2) (Fin 2) (Qbar l))
    (hM : ∀ i j, M i j ∈ c.O) {n : ℕ} {v w : Fin 2 → Qbar l} (h : Cv n v w) :
    Cv n (M *ᵥ v) (M *ᵥ w) := by
  intro i
  unfold Cg
  have e : (M *ᵥ v) i - (M *ᵥ w) i = M i 0 * (v 0 - w 0) + M i 1 * (v 1 - w 1) := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_le_one_of_mem_coef c (hM i 0))).trans (h 0)
  · rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_le_one_of_mem_coef c (hM i 1))).trans (h 1)

theorem limit_cocycle_mem_cocycles : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l), (∀ s i j, mat W s i j ∈ c.O) → ∀ (a : ℕ → G ℚ Ω → Fin 2 → Qbar l) (z : G ℚ Ω → Fin 2 → Qbar l), (∀ n s t, Cv n (a n (s * t)) (a n s + mat W s *ᵥ a n t)) → (∀ n s, ∀ᶠ t in nhds s, Cv n (a n t) (a n s)) → (∀ n s, Cv n (z s) (a n s)) → z ∈ Z1 (Loc.colRep W) := by
  intro l _ Ω _ _ W c hW a z hco hloc hz
  rw [mem_Z1_iff_cocycle]
  refine ⟨?_, ?_⟩
  · refine continuous_pi fun i => ?_
    refine continuous_iff_continuousAt.2 fun s => ?_
    have key : Filter.Tendsto (fun t => z t i) (nhds s) (@nhds (Qbar l) UniformSpace.toTopologicalSpace (z s i)) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      obtain ⟨n, hn⟩ := (tendsto_norm_l_pow (l := l)).eventually (gt_mem_nhds hε) |>.exists
      filter_upwards [hloc n s] with t ht
      have h1 : Cg n (z t i) (z s i) :=
        cg_trans (hz n t i) (cg_trans (ht i) (cg_symm (hz n s i)))
      rw [dist_eq_norm]
      exact lt_of_le_of_lt h1 hn
    exact key
  · intro s t
    have hcol : ∀ v, (Loc.colRep W s) v = mat W s *ᵥ v := by
      intro v; simp [Loc.colRep, Matrix.toLin'_apply]
    rw [hcol]
    funext i
    refine eq_of_forall_cg fun n => ?_
    have hA : Cv n (z (s * t)) (a n (s * t)) := hz n (s * t)
    have hB := hco n s t
    have hC : Cv n (a n s + mat W s *ᵥ a n t) (z s + mat W s *ᵥ z t) := by
      intro j
      have h2 := qbarLVectorCongruent_integralMatrix_mulVec c (mat W s) (hW s) (cv_symm (hz n t)) j
      have h3 := cg_symm (hz n s j)
      unfold Cg at h2 h3 ⊢
      have e : (a n s + mat W s *ᵥ a n t) j - (z s + mat W s *ᵥ z t) j
          = (a n s j - z s j) + ((mat W s *ᵥ a n t) j - (mat W s *ᵥ z t) j) := by
        simp only [Pi.add_apply]; ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h3 h2)
    exact (cv_trans hA (cv_trans hB hC)) i

end GlobalTheory.Ord2
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem GlobalTheory.Ord2.locConst_mod_pow :
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (c : Coef l) (W : R2 Ω l), Continuous W →
      (∀ s i j, mat W s i j ∈ c.O) → ∀ (n : ℕ) (s : G ℚ Ω), ∀ᶠ t in nhds s, ∀ i j,
        ∃ o ∈ c.O, mat W t i j - mat W s i j = (l : Qbar l) ^ n * o := by
  intro l _ Ω _ _ c W hW hO n s
  have hc : ∀ i j, Continuous fun t => mat W t i j := fun i j =>
    ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (Qbar l))).comp hW).matrix_elem i j
  have hr : 0 < ‖((l : ℕ) : Qbar l) ^ n‖ := by
    rw [norm_pos_iff]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
  have hev : ∀ᶠ t in nhds s, mat W t i j ∈ Metric.closedBall (mat W s i j) ‖((l : ℕ) : Qbar l) ^ n‖ :=
    (hc i j).continuousAt.preimage_mem_nhds (Metric.closedBall_mem_nhds _ hr)
  filter_upwards [hev] with t ht
  rw [Metric.mem_closedBall, dist_eq_norm] at ht
  have hmem : mat W t i j - mat W s i j ∈ c.O := c.O.sub_mem (hO t i j) (hO s i j)
  obtain ⟨o, ho⟩ := (GlobalTheory.Coef.norm_le_norm_pow_iff_dvd l c n ⟨_, hmem⟩).1 ht
  refine ⟨(o : Qbar l), o.2, ?_⟩
  have := congrArg (fun x : c.O => (x : Qbar l)) ho
  simpa using this
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.local_character_h1_finite_levels : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (A : ValuationSubring Ω), OverL l A → ∀ θ : ↥(Dec (F := ℚ) A) →* c.Oˣ, Continuous (fun g => ((θ g : c.Oˣ) : c.O)) → (∃ g, θ g ≠ 1) → (∃ g, θ g ≠ (UpperTheory.V.Base.chiO ℚ Ω l c.O).comp (Dec (F := ℚ) A).subtype g) → ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → Finite (H1 (Formalism.GaloisCohomology.scalRep (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) θ)) ∧ Nat.card (H1 (Formalism.GaloisCohomology.scalRep (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) θ)) ≤ C * Nat.card (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) := by
  first | exact @GlobalTheory.LocChar.local_character_h1_bound | exact GlobalTheory.LocChar.local_character_h1_bound | (intros; apply GlobalTheory.LocChar.local_character_h1_bound <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory

theorem exists_isPlaceOver_rat :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (q : Pl),
      ∃ B : ValuationSubring Ω, IsPlaceOver B q := by
  intro Ω _ _ _ q
  exact ReciprocityTheory.Gal.exists_isPlaceOver Ω q

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.coboundary_of_orthogonal_dualCharacter_modPrimePow : LocalFiniteness → LocalTateDuality → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (A : ValuationSubring Ω), OverL l A → ∀ θ θ' : ↥(Dec (F := ℚ) A) →* c.Oˣ, Continuous (fun g => ((θ g : c.Oˣ) : c.O)) → Continuous (fun g => ((θ' g : c.Oˣ) : c.O)) → θ * θ' = (UpperTheory.V.Base.chiO ℚ Ω l c.O).comp (Dec (F := ℚ) A).subtype → ∀ n : ℕ, 1 ≤ n → ∀ b : ↥(Dec (F := ℚ) A) → c.O, Continuous b → (∀ s t, ((l : ℕ) : c.O) ^ n ∣ b (s * t) - (b s + ((θ s : c.Oˣ) : c.O) * b t)) → (∀ a : ↥(Dec (F := ℚ) A) → c.O, Continuous a → (∀ s t, ((l : ℕ) : c.O) ^ n ∣ a (s * t) - (a s + ((θ' s : c.Oˣ) : c.O) * a t)) → ∃ u : ↥(Dec (F := ℚ) A) → c.O, Continuous u ∧ ∀ s t, ((l : ℕ) : c.O) ^ n ∣ b s * (((θ' s : c.Oˣ) : c.O) * a t) - ((((θ s : c.Oˣ) : c.O) * ((θ' s : c.Oˣ) : c.O)) * u t - u (s * t) + u s)) → ∃ x : c.O, ∀ s, ((l : ℕ) : c.O) ^ n ∣ b s - (((θ s : c.Oˣ) : c.O) * x - x) := by
  first | exact @GlobalTheory.Ord2.LocCharPerfect.perfect | exact GlobalTheory.Ord2.LocCharPerfect.perfect | (intros; apply GlobalTheory.Ord2.LocCharPerfect.perfect <;> assumption)
end
