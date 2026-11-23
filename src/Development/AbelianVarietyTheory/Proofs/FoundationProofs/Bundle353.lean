module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle018
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle061
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle090
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle023
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle093
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle020
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle213
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesCoeffRingHomMapCoeff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlMulToRingEquiv
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle079
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle092
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFixedCongrAxLemmaOddPrime
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle346
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
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory.KZ

theorem spLink_of_spec_approx (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (e : ℕ)
    (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l)
    (y : G ℚ Ω → Fin 2 → Qbar l)
    (h : ∀ r, ∀ s ∈ Ine (F := ℚ) A, cycBar ℚ Ω l s = 1 →
      ‖y s 1 - spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (Y r) s 1‖ ≤
        ‖((l : ℕ) : Qbar l) ^ r‖) :
    SpLink A e χ (fun r s x => Y r s x 1) y := by
  intro n
  refine ⟨n, fun r hr s hs hc => ?_⟩
  have h1 := h r s hs hc
  have heq : spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (Y r) s 1 =
      sp (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (fun s x => Y r s x 1) s := by
    simp only [spec, sp, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [heq] at h1
  unfold Cg
  refine h1.trans ?_
  rw [norm_pow, norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _) hr

end GlobalTheory.KZ
end

section

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.GammaZeroComm

theorem act_eq_self_of_mem_B {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l w : ℕ)
    [Fact l.Prime] {b : X.Fn l} (hb : b ∈ X.B N l w) {h : SL(2, ℤ)} (hh : h ∈ Gam N l) :
    X.act l (h : Matrix (Fin 2) (Fin 2) ℤ) b = b := by
  induction hb using Submodule.span_induction with
  | mem x hx => exact hx.2 h hh
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
  | smul c x _ hx => rw [map_smul, hx]

theorem eval_kmap_congr {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    (φ : X.K ≃+* X.K) (n : ℕ) {x y : X.Khat l} (h : x - y ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l))) :
    AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ x) = AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ y) := by
  rw [← sub_eq_zero, ← map_sub, ← map_sub]
  refine Submodule.smul_induction_on h (fun r hr m _ => ?_) (fun a b ha hb => ?_)
  · rw [map_smul, map_smul]
    obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ m))
    rw [← hz, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · rw [map_add (f := _), map_add (f := _), ha, hb, add_zero]

theorem exists_twist (M : ℕ) (e e' : ℤ) (he : (e : ZMod M) * e' = 1) (γ : SL(2, ℤ)) :
    ∃ γ₁ : SL(2, ℤ), (en γ 0 0 : ZMod M) = en γ₁ 0 0 ∧ (en γ 0 1 : ZMod M) = e * en γ₁ 0 1 ∧
      (e : ZMod M) * en γ 1 0 = en γ₁ 1 0 ∧ (en γ 1 1 : ZMod M) = en γ₁ 1 1 := by
  have hdet : (en γ 0 0 : ZMod M) * en γ 1 1 - en γ 0 1 * en γ 1 0 = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this
    have h2 := congrArg (Int.cast : ℤ → ZMod M) this
    push_cast at h2
    exact h2
  obtain ⟨γ₁, hγ₁⟩ := GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective M
    ⟨!![(en γ 0 0 : ZMod M), e' * en γ 0 1; e * en γ 1 0, en γ 1 1], by
      rw [Matrix.det_fin_two_of]; linear_combination hdet - (en γ 0 1 : ZMod M) * en γ 1 0 * he⟩
  have hent : ∀ i j, (en γ₁ i j : ZMod M) =
      (!![(en γ 0 0 : ZMod M), e' * en γ 0 1; e * en γ 1 0, en γ 1 1] : Matrix (Fin 2) (Fin 2) (ZMod M)) i j :=
    fun i j => congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) (ZMod M) => g.1 i j) hγ₁
  refine ⟨γ₁, ?_, ?_, ?_, ?_⟩
  · rw [hent]; rfl
  · rw [hent]
    show _ = (e : ZMod M) * (e' * en γ 0 1)
    rw [← mul_assoc, he, one_mul]
  · rw [hent]; rfl
  · rw [hent]; rfl

theorem cong_of_dvd {M K : ℕ} (hK : K ∣ M) {e : ℤ} {γ γ₁ : SL(2, ℤ)}
    (h : (en γ 0 0 : ZMod M) = en γ₁ 0 0 ∧ (en γ 0 1 : ZMod M) = e * en γ₁ 0 1 ∧
      (e : ZMod M) * en γ 1 0 = en γ₁ 1 0 ∧ (en γ 1 1 : ZMod M) = en γ₁ 1 1) :
    (en γ 0 0 : ZMod K) = en γ₁ 0 0 ∧ (en γ 0 1 : ZMod K) = e * en γ₁ 0 1 ∧
      (e : ZMod K) * en γ 1 0 = en γ₁ 1 0 ∧ (en γ 1 1 : ZMod K) = en γ₁ 1 1 := by
  obtain ⟨h00, h01, h10, h11⟩ := h
  have e00 := congrArg (ZMod.castHom hK (ZMod K)) h00
  have e01 := congrArg (ZMod.castHom hK (ZMod K)) h01
  have e10 := congrArg (ZMod.castHom hK (ZMod K)) h10
  have e11 := congrArg (ZMod.castHom hK (ZMod K)) h11
  simp only [map_mul, map_intCast] at e00 e01 e10 e11
  exact ⟨e00, e01, e10, e11⟩

theorem twist_mul_inv_mem {N l M : ℕ} (hN : N ∣ M) (hl : l ∣ M) {e : ℤ} {γ γ₁ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l)
    (h : (en γ 0 0 : ZMod M) = en γ₁ 0 0 ∧ (en γ 0 1 : ZMod M) = e * en γ₁ 0 1 ∧
      (e : ZMod M) * en γ 1 0 = en γ₁ 1 0 ∧ (en γ 1 1 : ZMod M) = en γ₁ 1 1) :
    γ₁ * γ⁻¹ ∈ Gam N l := by
  obtain ⟨a00, -, a10, a11⟩ := cong_of_dvd hN h
  obtain ⟨-, -, b10, -⟩ := cong_of_dvd hl h
  have cN : (en γ 1 0 : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.1 hγ.1
  have cl : (en γ 1 0 : ZMod l) = 0 := CongruenceSubgroup.Gamma0_mem.1 hγ.2
  have hdet : (en γ 0 0 : ZMod N) * en γ 1 1 - en γ 0 1 * en γ 1 0 = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this
    have h2 := congrArg (Int.cast : ℤ → ZMod N) this
    push_cast at h2
    exact h2
  have m00 : (γ₁ * γ⁻¹ : SL(2, ℤ)).1 0 0 = en γ₁ 0 0 * en γ 1 1 - en γ₁ 0 1 * en γ 1 0 := by
    simp [en, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]; ring
  have m10 : (γ₁ * γ⁻¹ : SL(2, ℤ)).1 1 0 = en γ₁ 1 0 * en γ 1 1 - en γ₁ 1 1 * en γ 1 0 := by
    simp [en, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]; ring
  have m11 : (γ₁ * γ⁻¹ : SL(2, ℤ)).1 1 1 = en γ₁ 1 1 * en γ 0 0 - en γ₁ 1 0 * en γ 0 1 := by
    simp [en, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]; ring
  rw [cN] at a10 hdet
  rw [cl] at b10
  refine ⟨(CongruenceSubgroup.Gamma1_mem N _).2 ⟨?_, ?_, ?_⟩, CongruenceSubgroup.Gamma0_mem.2 ?_⟩
  · rw [m00]; push_cast; rw [← a00, cN]; linear_combination hdet
  · rw [m11]; push_cast; rw [← a11, ← a10]; linear_combination hdet
  · rw [m10]; push_cast; rw [← a10, cN]; ring
  · rw [m10]; push_cast; rw [← b10, cl]; ring

theorem twist_vec {l n M : ℕ} [Fact l.Prime] (hM : l ^ n ∣ M) {e : ℤ} {χ : ℤ_[l]} (hχ : (e : ℤ_[l]) - χ ∈ (idl l) ^ n)
    {γ γ₁ : SL(2, ℤ)}
    (h : (en γ 0 0 : ZMod M) = en γ₁ 0 0 ∧ (en γ 0 1 : ZMod M) = e * en γ₁ 0 1 ∧
      (e : ZMod M) * en γ 1 0 = en γ₁ 1 0 ∧ (en γ 1 1 : ZMod M) = en γ₁ 1 1) (u : Fin 2 → ℤ_[l]) (i : Fin 2) :
    (![(mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0, χ * (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 1] :
      Fin 2 → ℤ_[l]) i - (mZl l (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ ![u 0, χ * u 1]) i ∈ (idl l) ^ n := by
  obtain ⟨e00, e01, e10, e11⟩ := cong_of_dvd hM h
  rw [Ideal.span_singleton_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero] at hχ ⊢
  rw [map_intCast] at hχ
  simp only [en] at e00 e01 e10 e11
  rw [hχ] at e01 e10
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, mZl, Matrix.map_apply, map_add (f := _), map_mul, map_intCast]
  · rw [← e00, e01]; ring
  · rw [← e10, ← e11]; ring

theorem galB_act_comm : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l → ∀ (s : Ω ≃ₐ[ℚ] Ω), ∀ b ∈ X.B N l w, X.galB l s (X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b) = X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) (X.galB l s b) := by
  intro Ω _ _ _ ε X _ _ N l w _ _ hN _ _ γ hγ s b hb
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hl : l.Prime := Fact.out
  funext u
  apply AdicCompletion.ext
  intro n
  set χ : ℤ_[l] := (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) with hχ
  obtain ⟨M0, hM0, hlev⟩ := X.eval_kmap_levelRed l
    (b ![(mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0, χ * (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 1]) n
  obtain ⟨M, hM, hNM, hlM, hlnM, hM0M⟩ : ∃ M : ℕ, 0 < M ∧ N ∣ M ∧ l ∣ M ∧ l ^ n ∣ M ∧ M0 ∣ M :=
    ⟨N * l * l ^ n * M0, Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) hl.pos) (pow_pos hl.pos n)) hM0,
      ⟨l * l ^ n * M0, by ring⟩, ⟨N * l ^ n * M0, by ring⟩, ⟨N * l * M0, by ring⟩, ⟨N * l * l ^ n, by ring⟩⟩
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  obtain ⟨e, he, heχ⟩ := exists_int_exponent_cyclotomic l s n M hM hlnM
  obtain ⟨e', he', -⟩ := exists_int_exponent_cyclotomic l s.symm n M hM hlnM
  have hee : (e : ZMod M) * e' = 1 := by
    have h1 : ζ ^ (e * e') = ζ := by
      rw [_root_.zpow_mul, ← he ζ hζ, ← map_zpow₀, ← he' ζ hζ, AlgEquiv.apply_symm_apply]
    have h0 : ζ ≠ 0 := hζ.ne_zero hM.ne'
    have h2 : ζ ^ (e * e' - 1) = 1 := by rw [zpow_sub_one₀ h0, h1, mul_inv_cancel₀ h0]
    have h3 := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (e * e') M).2 ((hζ.zpow_eq_one_iff_dvd _).1 h2)
    push_cast at h3
    exact h3.symm
  obtain ⟨γ₁, hc⟩ := exists_twist M e e' hee γ
  have hpos : ∀ g : SL(2, ℤ), 0 < (g : Matrix (Fin 2) (Fin 2) ℤ).det := fun g => by rw [g.det_coe]; exact one_pos
  have hact : X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = X.act l (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) b := by
    conv_lhs => rw [← act_eq_self_of_mem_B X N l w hb (twist_mul_inv_mem hNM hlM hγ hc)]
    rw [Tower.act_act Ω ε X l _ _ (hpos _) (hpos _), ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right]
  rw [hact]
  show AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l (X.gal s)
      (X.kmap l (X.sl (toGQ (γ₁ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv
        (b (mZl l (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ ![u 0, χ * u 1])))) =
    AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l (X.sl (toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv
      (X.kmap l (X.gal s)
        (b ![(mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0, χ * (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 1])))
  rw [Tower.kmap_kmap, Tower.kmap_kmap, Betti.toGQ_sl, Betti.toGQ_sl,
    ← eval_kmap_congr X l _ n (X.B_sub_mem N l w b hb n _ _ (twist_vec hlnM heχ hc u))]
  refine hlev _ _ fun f hf => ?_
  exact X.recip M f hM (fun g hg => hf g (LevelRed.gamma_le_of_dvd hM0M hg)) ζ hζ s e (he ζ hζ) γ₁ γ hc

end GlobalTheory.KZ.GammaZeroComm
end
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.GalUpper

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

theorem map_eq_zpow_of_pow_eq_one (s : Ω ≃ₐ[ℚ] Ω) {L : ℕ} (hL : 0 < L) {e : ℤ}
    (he : ∀ ζ : Ω, IsPrimitiveRoot ζ L → s ζ = ζ ^ e) {ω : Ω} (hω : ω ^ L = 1) : s ω = ω ^ e := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero L := ⟨hL.ne'⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω L
  obtain ⟨i, -, rfl⟩ := hξ.eq_pow_of_pow_eq_one hω
  rw [map_pow, he ξ hξ, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm]

theorem eOm_mul_int (ε : Ω →+* ℂ) (x : ℚ) (k : ℤ) : eOm ε (x * k) = eOm ε x ^ k := by
  apply ε.injective
  rw [map_zpow₀, eOm_spec ε ε.injective, eOm_spec ε ε.injective, ← Complex.exp_int_mul]
  congr 1; push_cast; ring

theorem gal_sl_upper (ε : Ω →+* ℂ) (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (M q : ℕ) (hq : 0 < q) (e : ℤ)
    (he : ∀ ω : Ω, ω ^ (M * q) = 1 → s ω = ω ^ e) (j : ℤ) (f : X.K)
    (hf : ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) :
    X.gal s (X.sl (toGQ !![1, j; 0, (q : ℤ)]) f) = X.sl (toGQ !![1, j * e; 0, (q : ℤ)]) (X.gal s f) := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have key : ∀ (a : ℤ) (g : X.K) (t : ℚ), (X.exp (X.sl (toGQ !![1, a; 0, (q : ℤ)]) g)).coeff t =
      eOm ε (t * a) * (X.exp g).coeff (t * q) := by
    intro a g t
    have h := Tower.exp_upper_int ε X 1 a q one_pos (by exact_mod_cast hq) g (t * q)
    have e1 : t * q * ((1 : ℤ) : ℚ) / ((q : ℤ) : ℚ) = t := by push_cast; field_simp
    have e2 : t * q * (a : ℚ) / ((q : ℤ) : ℚ) = t * a := by push_cast; field_simp
    rwa [e1, e2] at h
  apply (X.exp : X.K →+* HahnSeries ℚ Ω).injective
  ext t
  change (X.exp (X.gal s _)).coeff t = (X.exp (X.sl _ _)).coeff t
  rw [X.gal_exp, key, key, X.gal_exp, map_mul]
  by_cases h0 : (X.exp f).coeff (t * q) = 0
  · rw [h0, map_zero, mul_zero, mul_zero]
  · congr 1
    have h1 := GlobalTheory.KroneckerCongruence.eOm_level X M f hf _ h0
    have h2 : eOm ε (t * j) ^ (M * q) = 1 := by
      rw [← zpow_natCast, ← eOm_mul_int,
        show t * j * (((M * q : ℕ) : ℤ) : ℚ) = t * q * M * j by push_cast; ring, eOm_mul_int, h1, _root_.one_zpow]
    rw [he _ h2, ← eOm_mul_int]
    congr 1; push_cast; ring


omit [IsAlgClosure ℚ Ω] in
theorem eval_eq_zero_of_mem {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (φ : X.K ≃+* X.K)
    {x : X.Khat l} (hx : x ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l))) :
    AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ x) = 0 := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr y _
    rw [map_smul, map_smul]
    obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ y))
    rw [← hz, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · intro x y hx hy
    rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]


omit [IsAlgClosure ℚ Ω] in
theorem act_upper_add {ε : Ω →+* ℂ} (X : Tower Ω ε) {N l w : ℕ} [Fact l.Prime] {b : X.Fn l} (hb : b ∈ X.B N l w)
    (q : ℕ) (hq : 0 < q) (a t : ℤ) :
    X.act l !![1, a + t * q; 0, (q : ℤ)] b = X.act l !![1, a; 0, (q : ℤ)] b := by
  let γ : SL(2, ℤ) := ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩
  have hγ : γ ∈ Gam N l := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [CongruenceSubgroup.Gamma1_mem]; simp [γ]
    · rw [CongruenceSubgroup.Gamma0_mem]; simp [γ]
  have hinv : X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b := by
    induction hb using Submodule.span_induction with
    | mem x hx => exact hx.2 γ hγ
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
    | smul c x _ hx => rw [map_smul, hx]
  have hm : (!![1, a + t * q; 0, (q : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ) =
      (γ : Matrix (Fin 2) (Fin 2) ℤ) * !![1, a; 0, (q : ℤ)] := by
    simp [γ]
  rw [hm, ← Tower.act_act Ω ε X l _ _ (by rw [γ.det_coe]; exact one_pos)
    (by simp [Matrix.det_fin_two]; exact hq), hinv]

theorem galB_act_upper : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ (s : Ω ≃ₐ[ℚ] Ω) (q : ℕ) (e : ℤ), 0 < q → (∀ ζ : Ω, IsPrimitiveRoot ζ q → s ζ = ζ ^ e) → ∀ (j : ℤ), ∀ b ∈ X.B N l w, X.galB l s (X.act l !![1, j; 0, (q : ℤ)] b) = X.act l !![1, j * e; 0, (q : ℤ)] (X.galB l s b) := by
  intro Ω _ _ _ ε X hε hj N l w _ hl hN hNl hw s q e hq he j b hb
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero q := ⟨hq.ne'⟩
  have hlp : l.Prime := Fact.out
  have hb' := GlobalTheory.T.galB_mem_kummer_invariant_set ε X hε hj N l w hl hN hNl hw s b hb
  funext u
  apply AdicCompletion.ext
  intro n
  set χ : ℤ_[l] := (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) with hχ
  set v : Fin 2 → ℤ_[l] := mZl l !![1, j; 0, (q : ℤ)] *ᵥ ![u 0, χ * u 1] with hv
  obtain ⟨M, hM, hred⟩ := GlobalTheory.T.towerPadicCompletionMap_eval_depends_on_level X l (b v) n
  have hL : 0 < M * q * l ^ n := Nat.mul_pos (Nat.mul_pos hM hq) (pow_pos hlp.pos n)
  obtain ⟨d, hd, hdχ⟩ := GlobalTheory.T.exists_int_exponent_congr_cyclotomicCharacter l s n (M * q * l ^ n) hL (dvd_mul_left _ _)
  have hd' : ∀ ω : Ω, ω ^ (M * q) = 1 → s ω = ω ^ d := fun ω hω =>
    map_eq_zpow_of_pow_eq_one s hL hd (by rw [pow_mul, hω, one_pow])
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω q
  have hξ0 : ξ ≠ 0 := hξ.ne_zero hq.ne'
  have hde : (q : ℤ) ∣ d - e := by
    rw [← hξ.zpow_eq_one_iff_dvd, zpow_sub₀ hξ0, ← he ξ hξ,
      ← hd' ξ (by rw [mul_comm, pow_mul, hξ.pow_eq_one, one_pow])]
    exact div_self ((map_ne_zero s).2 hξ0)
  obtain ⟨t, ht⟩ := hde
  have hjd : j * d = j * e + (j * t) * q := by linear_combination j * ht
  rw [← act_upper_add X hb' q hq (j * e) (j * t), ← hjd]
  set v' : Fin 2 → ℤ_[l] := mZl l !![1, j * d; 0, (q : ℤ)] *ᵥ u with hv'
  change AdicCompletion.eval (idl l) (X.Kl l) n
      (X.kmap l (X.gal s) (X.kmap l (X.sl (toGQ !![1, j; 0, (q : ℤ)])).toRingEquiv (b v))) =
    AdicCompletion.eval (idl l) (X.Kl l) n
      (X.kmap l (X.sl (toGQ !![1, j * d; 0, (q : ℤ)])).toRingEquiv (X.kmap l (X.gal s) (b ![v' 0, χ * v' 1])))
  rw [Tower.kmap_kmap, Tower.kmap_kmap,
    hred _ ((X.gal s).trans (X.sl (toGQ !![1, j * d; 0, (q : ℤ)])).toRingEquiv)
      (fun f hf => gal_sl_upper ε X s M q hq d hd' j f hf), ← sub_eq_zero, ← map_sub, ← map_sub]
  apply eval_eq_zero_of_mem
  refine GlobalTheory.T.bettiFunction_sub_mem_of_columns_congr X N l w b hb n _ _ ?_
  intro i
  fin_cases i
  · have h := Ideal.mul_mem_left _ (-((j : ℤ_[l]) * u 1)) hdχ
    convert h using 1
    simp [hv, hv', mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · convert Ideal.zero_mem _
    simp [hv, hv', mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring

end GlobalTheory.KZ.GalUpper
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_fixed_congr_axLemma_oddPrime : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A →
  ∀ (H : Subgroup (G ℚ Ω)), H ≤ Dec (F := ℚ) A → ∀ (m : ℕ) (x : Ω), x ∈ A →
  (∀ h ∈ H, GlobalTheory.Glue.CgA A l (m + 1) (h x) x) → ∃ y ∈ A, (∀ h ∈ H, h y = y) ∧ GlobalTheory.Glue.CgA A l m x y := by
  first | exact @GlobalTheory.AxSen.exists_fixed_congr | exact GlobalTheory.AxSen.exists_fixed_congr | (intros; apply GlobalTheory.AxSen.exists_fixed_congr <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2

variable {l : ℕ} [Fact l.Prime]

theorem norm_l_pow_anti {m n : ℕ} (h : n ≤ m) :
    ‖((l : ℕ) : Qbar l) ^ m‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := by
  rw [norm_pow, norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) norm_natCast_l_lt_one.le h

theorem isCompact_coef (c : Coef l) : IsCompact (c.O : Set (Qbar l)) := by
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := ℤ_[l]) (M := c.O)
  let f : (Fin k → ℤ_[l]) → Qbar l :=
    fun v => ∑ i, algebraMap ℤ_[l] (Qbar l) (v i) * (s i : Qbar l)
  have hcont : Continuous f := by
    have ha : Continuous (algebraMap ℤ_[l] (Qbar l)) := by
      have : ⇑(algebraMap ℤ_[l] (Qbar l)) = fun a : ℤ_[l] => algebraMap ℚ_[l] (Qbar l) (a : ℚ_[l]) := by
        funext a; exact IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l) a
      rw [this]
      exact (continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val
    exact continuous_finsetSum _ fun i _ => (ha.comp (continuous_apply i)).mul continuous_const
  have heq : (c.O : Set (Qbar l)) = Set.range f := by
    ext x
    constructor
    · intro hx
      have hmem : (⟨x, hx⟩ : c.O) ∈ Submodule.span ℤ_[l] (Set.range s) := by rw [hs]; trivial
      obtain ⟨v, hv⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[l]).1 hmem
      refine ⟨v, ?_⟩
      have := congrArg (fun y : c.O => (y : Qbar l)) hv
      simp only [AddSubmonoidClass.coe_finsetSum] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Algebra.smul_def]
      rfl
    · rintro ⟨v, rfl⟩
      exact c.O.sum_mem fun i _ => c.O.mul_mem (c.O.algebraMap_mem _) (s i).2
  rw [heq]
  exact isCompact_range hcont

theorem cg_of_le {a : ℕ → Qbar l} (h : ∀ n, Cg n (a (n + 1)) (a n)) {n m : ℕ} (hnm : n ≤ m) :
    Cg n (a m) (a n) := by
  induction m, hnm using Nat.le_induction with
  | base => unfold Cg; simp
  | succ m hm ih =>
    have h1 : Cg n (a (m + 1)) (a m) := by
      unfold Cg at *; exact (h m).trans (norm_l_pow_anti hm)
    exact cg_trans h1 ih

theorem exists_limit_coef : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (X : Type) (a : ℕ → X → Qbar l),
    (∀ n x, a n x ∈ c.O) → (∀ n x, Cg n (a (n + 1) x) (a n x)) →
    ∃ z : X → Qbar l, (∀ x, z x ∈ c.O) ∧ ∀ n x, Cg n (z x) (a n x) := by
  intro l _ c X a hO hC
  have key : ∀ x, ∃ y ∈ (c.O : Set (Qbar l)), ∀ n, Cg n y (a n x) := by
    intro x
    have hle : ∀ n m, n ≤ m → ‖a m x - a n x‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ :=
      fun n m h => cg_of_le (a := fun k => a k x) (fun k => hC k x) h
    have hcs : CauchySeq (fun m => a m x) := by
      rw [Metric.cauchySeq_iff']
      intro ε hε
      obtain ⟨N, hN⟩ := (tendsto_norm_l_pow (l := l)).eventually (gt_mem_nhds hε) |>.exists_forall_of_atTop
      refine ⟨N, fun m hm => ?_⟩
      rw [dist_eq_norm]
      exact (hle N m hm).trans_lt (hN N le_rfl)
    obtain ⟨y, hy, hlim⟩ := cauchySeq_tendsto_of_isComplete (isCompact_coef c).isComplete
      (fun m => hO m x) hcs
    refine ⟨y, hy, fun n => ?_⟩
    unfold Cg
    have ht : Filter.Tendsto (fun m => ‖a m x - a n x‖) Filter.atTop (nhds ‖y - a n x‖) :=
      (hlim.sub_const _).norm
    exact le_of_tendsto ht (Filter.eventually_atTop.2 ⟨n, fun m hm => hle n m hm⟩)
  choose z hz using key
  exact ⟨z, fun x => (hz x).1, fun n x => (hz x).2 n⟩

end GlobalTheory.Ord2

end
end
