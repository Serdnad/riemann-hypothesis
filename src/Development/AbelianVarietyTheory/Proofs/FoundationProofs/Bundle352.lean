module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlMulToRingEquiv
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeSha
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle341
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle342
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle018
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory.KZ

theorem tame_of_shCoc : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (c : Coef l) (W : R2 Ω l) (y : G ℚ Ω → Fin 2 → Qbar l) (n : ℕ) (w : Pl) (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n))) (Y : G ℚ Ω → Multiplicative (ZMod (l ^ n)) → Fin 2 → Qbar l) (P u : Qbar l) (b : Fin 2 → Qbar l), ShCoc (mat W) ψ Y → (∀ x i, Continuous fun s => Y s x i) → (∀ s x i, Y s x i ∈ c.O) → P ∈ c.O → ‖u‖ = 1 → (∀ i, b i ∈ c.O) → (∀ s, ∑ x, Y s x = P • y s + (mat W s *ᵥ b - b)) → (∀ (B : ValuationSubring Ω) (σ : G ℚ Ω), IsPlaceOver B w → IsFrob B (normV w) σ → Cg n P (u * (mat W σ - 1).det)) → (∀ q : Pl, q ≠ w → ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧ ∃ t : Multiplicative (ZMod (l ^ n)) → Fin 2 → Qbar l, (∀ x i, t x i ∈ c.O) ∧ ∀ s ∈ Ine (F := ℚ) B, ∀ x, Y s x = mat W s *ᵥ t x - t x) → Tame c W y n w ψ := by
  intro l _ Ω _ _ c W y n w ψ Y P u b hY hcont hint hP hu hb hsum hfrob hunr
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero n (Fact.out : l.Prime).ne_zero⟩
  refine ⟨fun s a => Y s (Multiplicative.ofAdd (-a)), P, u, b, ?_, fun s a i => hint s _ i, hP, hu, hb, ?_, ?_, hfrob, ?_⟩
  · exact continuous_pi fun a => continuous_pi fun i => hcont _ i
  · intro s t a
    simp only
    rw [hY s t (Multiplicative.ofAdd (-a))]
    congr 3
    rw [neg_sub, sub_eq_neg_add]
    rfl
  · intro s
    rw [finsum_eq_sum_of_fintype, ← hsum s]
    exact Fintype.sum_equiv ((Equiv.neg (ZMod (l ^ n))).trans Multiplicative.ofAdd) _ _ (fun a => rfl)
  · intro q hq hl
    obtain ⟨B, hB, t, ht, hts⟩ := hunr q hq hl
    exact ⟨B, hB, fun a => t (Multiplicative.ofAdd (-a)), fun a i => ht _ i, fun s hs a => hts s hs _⟩

end GlobalTheory.KZ

end
end

section

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

theorem toGQ_diag_nat_one_ent (q : ℕ) (hq : 0 < q) :
    ent (toGQ !![(q : ℤ), 0; 0, 1]) 0 0 = (q : ℚ) ∧ ent (toGQ !![(q : ℤ), 0; 0, 1]) 0 1 = 0 ∧
    ent (toGQ !![(q : ℤ), 0; 0, 1]) 1 0 = 0 ∧ ent (toGQ !![(q : ℤ), 0; 0, 1]) 1 1 = 1 := by
  have h : (0 : ℤ) < (!![(q : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    rw [Matrix.det_fin_two_of]; omega
  unfold ent toGQ
  rw [dite_eq_left h]
  simp

theorem eOm_zero_of_injective_diag {Ω : Type} [Field Ω] (ε : Ω →+* ℂ) (hε : Function.Injective ε) : eOm ε 0 = 1 := by
  unfold eOm
  simp only [Rat.cast_zero, mul_zero, Complex.exp_zero]
  rw [← map_one ε]
  exact Function.leftInverse_invFun hε 1

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem Tower.exp_sl_diag_coeff (X : Tower Ω ε) (hε : Function.Injective ε) (q : ℕ) (hq : 0 < q) (f : X.K) (r : ℚ) :
    (X.exp (X.sl (toGQ !![(q : ℤ), 0; 0, 1]) f)).coeff r = (X.exp f).coeff (r / q) := by
  obtain ⟨h00, h01, h10, h11⟩ := toGQ_diag_nat_one_ent q hq
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have h := X.exp_upper _ h10 f (r / q)
  rw [h00, h01, h11, mul_zero, zero_div, eOm_zero_of_injective_diag ε hε, one_mul, div_one, div_mul_cancel₀ r hqQ] at h
  exact h

theorem Tower.gal_sl_diag (X : Tower Ω ε) (hε : Function.Injective ε) (q : ℕ) (hq : 0 < q)
    (s : Ω ≃ₐ[ℚ] Ω) (f : X.K) :
    X.gal s (X.sl (toGQ !![(q : ℤ), 0; 0, 1]) f) = X.sl (toGQ !![(q : ℤ), 0; 0, 1]) (X.gal s f) := by
  apply RingHom.injective X.exp.toRingHom
  ext r
  show (X.exp _).coeff r = (X.exp _).coeff r
  rw [X.gal_exp, X.exp_sl_diag_coeff hε q hq, X.exp_sl_diag_coeff hε q hq, X.gal_exp]

theorem mZl_diag_nat_one_mulVec (l : ℕ) [Fact l.Prime] (q : ℕ) (c : ℤ_[l]) (u : Fin 2 → ℤ_[l]) :
    mZl l !![(q : ℤ), 0; 0, 1] *ᵥ ![u 0, c * u 1] =
      ![(mZl l !![(q : ℤ), 0; 0, 1] *ᵥ u) 0, c * (mZl l !![(q : ℤ), 0; 0, 1] *ᵥ u) 1] := by
  funext i
  fin_cases i <;> simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem Tower.galB_act_diag : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → ∀ (l : ℕ) [Fact l.Prime] (q : ℕ), 0 < q → ∀ (s : Ω ≃ₐ[ℚ] Ω) (b : X.Fn l),
      X.galB l s (X.act l !![(q : ℤ), 0; 0, 1] b) = X.act l !![(q : ℤ), 0; 0, 1] (X.galB l s b) := by
  intro Ω _ _ ε X hε l _ q hq s b
  funext u
  simp only [Tower.galB, Tower.act, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Tower.kmap_kmap, Tower.kmap_kmap, mZl_diag_nat_one_mulVec]
  have hφ : (X.sl (toGQ !![(q : ℤ), 0; 0, 1])).toRingEquiv.trans (X.gal s) =
      (X.gal s).trans (X.sl (toGQ !![(q : ℤ), 0; 0, 1])).toRingEquiv :=
    RingEquiv.ext fun f => X.gal_sl_diag hε q hq s f
  rw [hφ]

end GlobalTheory.KZ
end
end

section

open GlobalTheory.KZ Matrix

namespace GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem Tower.gal_mul_apply (X : Tower Ω ε) (s s' : Ω ≃ₐ[ℚ] Ω) (f : X.K) :
    X.gal (s * s') f = X.gal s (X.gal s' f) := by
  apply (X.exp : X.K →+* HahnSeries ℚ Ω).injective
  ext r
  show (X.exp (X.gal (s * s') f)).coeff r = (X.exp (X.gal s (X.gal s' f))).coeff r
  rw [X.gal_exp, X.gal_exp, X.gal_exp]
  rfl

theorem Tower.galB_mul (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (s s' : Ω ≃ₐ[ℚ] Ω) (b : X.Fn l) :
    X.galB l (s * s') b = X.galB l s (X.galB l s' b) := by
  funext u
  simp only [Tower.galB, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Tower.kmap_kmap]
  have hg : X.gal (s * s') = (X.gal s').trans (X.gal s) := by
    ext f; exact X.gal_mul_apply s s' f
  have hc : (cyclotomicCharacter Ω l (s * s').toRingEquiv : ℤ_[l]) =
      (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * (cyclotomicCharacter Ω l s'.toRingEquiv : ℤ_[l]) := by
    have : (s * s').toRingEquiv = s.toRingEquiv * s'.toRingEquiv := rfl
    rw [this, map_mul, Units.val_mul]
  rw [hg, hc]
  congr 2
  funext i
  fin_cases i <;> simp [mul_comm, mul_left_comm]

end GlobalTheory.KZ
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

theorem Tower.sum_act_upper_mul_unit {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ)
    [Fact l.Prime] (c : X.Fn l) (hc : ∀ t : ℤ, X.act l !![1, t; 0, 1] c = c) (q : ℕ) (e : ℤ) (hq : 0 < q)
    (he : IsCoprime e (q : ℤ)) :
    ∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ) * e; 0, (q : ℤ)] c =
      ∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ); 0, (q : ℤ)] c := by
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  set f : ℤ → X.Fn l := fun r => X.act l !![1, r; 0, (q : ℤ)] c with hf
  have step : ∀ x : ℤ, X.act l !![1, x; 0, (q : ℤ)] c = f (x % q) := by
    intro x
    have hm : !![1, x; 0, (q : ℤ)] = !![(1 : ℤ), x / q; 0, 1] * !![1, x % q; 0, (q : ℤ)] := by
      have := Int.emod_add_mul_ediv x q
      ext i k; fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linarith
    rw [hm, ← Tower.act_act Ω ε X l _ _ (by simp [Matrix.det_fin_two]) (by simp [Matrix.det_fin_two]; exact hq), hc]
  let g : ℕ → ℕ := fun j => (((j : ℤ) * e) % q).toNat
  have hg : ∀ j, ((g j : ℕ) : ℤ) = ((j : ℤ) * e) % q := fun j =>
    Int.toNat_of_nonneg (Int.emod_nonneg _ hq'.ne')
  have hgr : ∀ j, g j < q := fun j => by
    have h1 := Int.emod_lt_of_pos ((j : ℤ) * e) hq'
    have h2 := hg j
    omega
  have hinj : Set.InjOn g (Finset.range q) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    have h : ((i : ℤ) * e) % q = ((j : ℤ) * e) % q := by rw [← hg, ← hg, hij]
    have hd : (q : ℤ) ∣ ((j : ℤ) - i) * e := by
      rw [sub_mul]; exact (Int.ModEq.dvd h)
    have hd' : (q : ℤ) ∣ (j : ℤ) - i := he.symm.dvd_of_dvd_mul_right hd
    have h0 := Int.eq_zero_of_abs_lt_dvd hd' (by rw [abs_lt]; constructor <;> omega)
    omega
  have himg : (Finset.range q).image g = Finset.range q := by
    apply Finset.eq_of_subset_of_card_le
    · intro r hr; simp only [Finset.mem_image] at hr; obtain ⟨j, _, rfl⟩ := hr; exact Finset.mem_range.2 (hgr j)
    · rw [Finset.card_image_of_injOn hinj]
  calc ∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ) * e; 0, (q : ℤ)] c
      = ∑ j ∈ Finset.range q, f ((g j : ℕ) : ℤ) := by
        refine Finset.sum_congr rfl fun j _ => ?_; rw [step, hg]
    _ = ∑ r ∈ (Finset.range q).image g, f (r : ℤ) := (Finset.sum_image (f := fun r : ℕ => f (r : ℤ)) hinj).symm
    _ = ∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ); 0, (q : ℤ)] c := by rw [himg]

end GlobalTheory.KZ
end

section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

noncomputable section

namespace GlobalTheory.KZ

theorem mul_inv_mem_Gam_of_isDiam {N l d : ℕ} {s t : SL(2, ℤ)} (hs : IsDiam N l d s) (ht : IsDiam N l d t) :
    s * t⁻¹ ∈ Gam N l := by
  obtain ⟨hs0, hsd⟩ := hs
  obtain ⟨ht0, htd⟩ := ht
  rw [Subgroup.mem_inf] at hs0 ht0
  refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mul_mem _ hs0.2 (Subgroup.inv_mem _ ht0.2)⟩
  have hsN := CongruenceSubgroup.Gamma0_mem.1 hs0.1
  have htN := CongruenceSubgroup.Gamma0_mem.1 ht0.1
  have ds := s.det_coe
  have dt := t.det_coe
  rw [Matrix.det_fin_two] at ds dt
  have ds' : ((s 0 0 * s 1 1 - s 0 1 * s 1 0 : ℤ) : ZMod N) = 1 := by rw [ds]; simp
  have dt' : ((t 0 0 * t 1 1 - t 0 1 * t 1 0 : ℤ) : ZMod N) = 1 := by rw [dt]; simp
  push_cast at ds' dt'
  simp only [en] at hsd htd
  rw [CongruenceSubgroup.Gamma1_mem]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
  push_cast
  refine ⟨?_, ?_, ?_⟩
  · linear_combination ds' + (s 0 0 : ZMod N) * (htd - hsd) + (s 0 1 : ZMod N) * hsN - (s 0 1 : ZMod N) * htN
  · linear_combination dt' + (t 0 0 : ZMod N) * (hsd - htd) + (t 0 1 : ZMod N) * htN - (t 0 1 : ZMod N) * hsN
  · linear_combination (t 1 1 : ZMod N) * hsN - (s 1 1 : ZMod N) * htN

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem Tower.act_eq_of_mem_B (X : Tower Ω ε) {N l w : ℕ} [Fact l.Prime] {b : X.Fn l} (hb : b ∈ X.B N l w)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gam N l) : X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b := by
  induction hb using Submodule.span_induction with
  | mem x hx => exact hx.2 γ hγ
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
  | smul c x _ hx => rw [map_smul, hx]

theorem Tower.act_isDiam_eq (X : Tower Ω ε) {N l w d : ℕ} [Fact l.Prime] {b : X.Fn l} (hb : b ∈ X.B N l w)
    {s : SL(2, ℤ)} (hs : IsDiam N l d s) :
    X.act l (s : Matrix (Fin 2) (Fin 2) ℤ) b = X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b := by
  have ht : IsDiam N l d (sgD N l d) := Classical.epsilon_spec ⟨s, hs⟩
  have hγ := mul_inv_mem_Gam_of_isDiam hs ht
  have e : s = (s * (sgD N l d)⁻¹) * sgD N l d := by group
  have hpos : ∀ g : SL(2, ℤ), 0 < (g : Matrix (Fin 2) (Fin 2) ℤ).det := fun g => by rw [g.det_coe]; exact one_pos
  rw [e, Matrix.SpecialLinearGroup.coe_mul, ← Tower.act_act Ω ε X l _ _ (hpos _) (hpos _) b,
    X.act_eq_of_mem_B hb hγ]

theorem isThB_act_isDiam_iff : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n w d : ℕ) (b : X.Fn l), b ∈ X.B N l w →
    ∀ s : SL(2, ℤ), IsDiam N l d s → ∀ φ : HahnSeries ℚ Ω,
  IsThB X A N l n (X.act l (s : Matrix (Fin 2) (Fin 2) ℤ) b) φ ↔
    IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) φ := by
  intro Ω _ _ _ ε X A N l _ n w d b hb s hs φ
  rw [X.act_isDiam_eq hb hs]

end GlobalTheory.KZ
end
end

section

noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

namespace GlobalTheory.CoefCoord

variable {l : ℕ} [Fact l.Prime]

theorem norm_le_one_of_isIntegral (x : PadicAlgCl l) (h : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  change spectralValue (minpoly ℚ_[l] x) ≤ 1
  rw [spectralValue_le_one_iff (minpoly.monic hi)]
  intro n
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
  exact PadicInt.norm_le_one _

theorem norm_le_one (c : Coef l) (x : c.O) : ‖(x : PadicAlgCl l)‖ ≤ 1 :=
  norm_le_one_of_isIntegral _
    ((isIntegral_algHom_iff c.O.val Subtype.val_injective).2 (Algebra.IsIntegral.isIntegral x))

theorem norm_unit (c : Coef l) (u : c.Oˣ) : ‖((u : c.O) : PadicAlgCl l)‖ = 1 := by
  have h1 := norm_le_one c u
  have h2 := norm_le_one c (↑u⁻¹ : c.O)
  have h3 : ((u : c.O) : PadicAlgCl l) * ((↑u⁻¹ : c.O) : PadicAlgCl l) = 1 := by
    rw [← Subalgebra.coe_mul, Units.mul_inv]; rfl
  have h4 := congrArg norm h3
  rw [norm_mul, norm_one] at h4
  have h5 : ‖((u : c.O) : PadicAlgCl l)‖ * ‖((↑u⁻¹ : c.O) : PadicAlgCl l)‖ ≤ ‖((u : c.O) : PadicAlgCl l)‖ :=
    mul_le_of_le_one_right (norm_nonneg _) h2
  linarith

theorem norm_natCast_lt_one : ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)) l, PadicAlgCl.norm_extends, Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)

theorem norm_algebraMap_padicInt (a : ℤ_[l]) : ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ = ‖a‖ := by
  show ‖algebraMap ℚ_[l] (PadicAlgCl l) (a : ℚ_[l])‖ = ‖a‖
  rw [PadicAlgCl.norm_extends]; rfl

theorem exists_eq_pow_mul (c : Coef l) (m : ℕ) (x : c.O)
    (hx : ‖(x : PadicAlgCl l)‖ ≤ ‖((l : ℕ) : PadicAlgCl l) ^ m‖) : ∃ z : c.O, x = (l : c.O) ^ m * z := by
  by_cases h0 : x = 0
  · exact ⟨0, by simp [h0]⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hπ
  have hl0 : ((l : ℕ) : c.O) ≠ 0 := by
    intro h
    have h' := congrArg (fun y : c.O => (y : PadicAlgCl l)) h
    simp only [SubringClass.coe_natCast, ZeroMemClass.coe_zero] at h'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h'
  obtain ⟨e, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hπ
  set q := ‖(π : PadicAlgCl l)‖ with hqdef
  have hlq : ‖((l : ℕ) : PadicAlgCl l)‖ = q ^ e := by
    have h' := congrArg (fun y : c.O => ‖(y : PadicAlgCl l)‖) hw
    simp only [SubringClass.coe_natCast, Subalgebra.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow,
      norm_unit, one_mul] at h'
    exact h'
  have hq0 : 0 < q := by
    rw [hqdef, norm_pos_iff]
    intro h
    exact hπ.ne_zero (Subtype.ext h)
  have hq1 : q < 1 := by
    rcases (norm_le_one c π).lt_or_eq with h | h
    · exact h
    · exfalso
      have := (norm_natCast_lt_one (l := l))
      rw [hlq, hqdef, h, one_pow] at this
      exact lt_irrefl _ this
  have hxq : ‖(((u : c.O) * π ^ k : c.O) : PadicAlgCl l)‖ = q ^ k := by
    simp only [Subalgebra.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow, norm_unit, one_mul]
    rfl
  rw [hxq, norm_pow, hlq, ← pow_mul] at hx
  have hk : e * m ≤ k := (pow_le_pow_iff_right_of_lt_one₀ hq0 hq1).1 hx
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
  refine ⟨(u : c.O) * (↑w⁻¹ : c.O) ^ m * π ^ r, ?_⟩
  rw [hw]
  have h2 : ((w : c.O) * (↑w⁻¹ : c.O)) ^ m = 1 := by rw [Units.mul_inv, one_pow]
  linear_combination (-((u : c.O) * π ^ (e * m + r))) * h2

theorem norm_sub_val_le (m : ℕ) (a : ℤ_[l]) :
    ‖algebraMap ℤ_[l] (PadicAlgCl l) a - (((PadicInt.toZModPow m a).val : ℕ) : PadicAlgCl l)‖
      ≤ ‖((l : ℕ) : PadicAlgCl l) ^ m‖ := by
  have hk : a - (((PadicInt.toZModPow m a).val : ℕ) : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow (p := l) m) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton'] at hk
  obtain ⟨t, ht⟩ := hk
  have e : algebraMap ℤ_[l] (PadicAlgCl l) a - (((PadicInt.toZModPow m a).val : ℕ) : PadicAlgCl l)
      = algebraMap ℤ_[l] (PadicAlgCl l) t * ((l : ℕ) : PadicAlgCl l) ^ m := by
    have := congrArg (algebraMap ℤ_[l] (PadicAlgCl l)) ht
    simp only [map_mul, map_pow, map_natCast, map_sub] at this
    rw [this]
  rw [e, norm_mul, norm_algebraMap_padicInt]
  exact mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one t)

theorem coe_eq_sum {ι : Type} [Fintype ι] (c : Coef l) (b : Module.Basis ι ℤ_[l] c.O) (y : c.O) :
    (y : PadicAlgCl l) = ∑ i, ((b i : c.O) : PadicAlgCl l) * algebraMap ℤ_[l] (PadicAlgCl l) (b.repr y i) := by
  conv_lhs => rw [← b.sum_repr y]
  rw [AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Subalgebra.coe_smul, Algebra.smul_def, mul_comm]

theorem coord_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (m : ℕ), ∃ (ι : Type) (_ : Fintype ι) (o : ι → Qbar l)
    (crd : Qbar l → ι → ZMod (l ^ m)), (∀ i, o i ∈ c.O ∧ ‖o i‖ ≤ 1) ∧
    (∀ x ∈ c.O, ∀ y ∈ c.O, crd (x + y) = crd x + crd y) ∧ (∀ x ∈ c.O, Cg m x 0 → crd x = 0) ∧
    (∀ x ∈ c.O, Cg m x (∑ i, o i * ((crd x i).val : Qbar l))) ∧
    (∀ n : ι → ZMod (l ^ m), Cg m (∑ i, o i * ((n i).val : Qbar l)) 0 → n = 0) := by
  intro l _ c m
  classical
  let b := Module.Free.chooseBasis ℤ_[l] c.O
  let crd : Qbar l → Module.Free.ChooseBasisIndex ℤ_[l] c.O → ZMod (l ^ m) := fun x i =>
    if hx : x ∈ c.O then PadicInt.toZModPow m (b.repr ⟨x, hx⟩ i) else 0
  have hcrd : ∀ (x : Qbar l) (hx : x ∈ c.O) i, crd x i = PadicInt.toZModPow m (b.repr ⟨x, hx⟩ i) :=
    fun x hx i => dif_pos hx
  have hkill : ∀ x ∈ c.O, Cg m x 0 → crd x = 0 := by
    intro x hx h
    unfold Cg at h
    rw [sub_zero] at h
    obtain ⟨z, hz⟩ := exists_eq_pow_mul c m ⟨x, hx⟩ h
    funext i
    rw [hcrd x hx i, hz]
    have e : ((l : c.O) ^ m * z) = ((l : ℤ_[l]) ^ m) • z := by
      rw [Algebra.smul_def, map_pow, map_natCast]
    rw [e, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, map_pow, map_natCast, ← Nat.cast_pow,
      ZMod.natCast_self, zero_mul]
    rfl
  refine ⟨Module.Free.ChooseBasisIndex ℤ_[l] c.O, inferInstance, fun i => ((b i : c.O) : PadicAlgCl l), crd,
    fun i => ⟨(b i).2, norm_le_one c (b i)⟩, ?_, hkill, ?_, ?_⟩
  · intro x hx y hy
    funext i
    rw [hcrd _ (add_mem hx hy), Pi.add_apply, hcrd x hx, hcrd y hy,
      show (⟨x + y, add_mem hx hy⟩ : c.O) = ⟨x, hx⟩ + ⟨y, hy⟩ from rfl, map_add, Finsupp.add_apply, map_add]
  · intro x hx
    unfold Cg
    have hx' := coe_eq_sum c b ⟨x, hx⟩
    change x = _ at hx'
    simp only [hcrd x hx]
    rw [congrArg (fun t => t - _) hx', ← Finset.sum_sub_distrib]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
    rw [← mul_sub, norm_mul]
    exact (mul_le_mul (norm_le_one c (b i)) (norm_sub_val_le m _) (norm_nonneg _) zero_le_one).trans (by rw [one_mul])
  · intro n hn
    set y : Qbar l := ∑ i, ((b i : c.O) : PadicAlgCl l) * (((n i).val : ℕ) : Qbar l) with hydef
    have hy : y ∈ c.O := Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (b i).2 (Subalgebra.natCast_mem _ _)
    have hyb : (⟨y, hy⟩ : c.O) = ∑ i, (((n i).val : ℕ) : ℤ_[l]) • b i := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Subalgebra.coe_smul, Algebra.smul_def, map_natCast, mul_comm]
    have h0 := hkill y hy hn
    funext i
    have := congrFun h0 i
    rw [hcrd y hy i, hyb, b.repr_sum_self, map_natCast, ZMod.natCast_zmod_val] at this
    exact this

end GlobalTheory.CoefCoord
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_unitCharacter_of_integral_cyclotomic_product : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (c : Coef l) (A : ValuationSubring Ω) (k k' : G ℚ Ω → Qbar l), ContinuousOn k (Dec (F := ℚ) A) → (∀ s ∈ Dec (F := ℚ) A, k s ∈ c.O ∧ k' s ∈ c.O ∧ k s * k' s = eps l s) → (∀ s ∈ Dec (F := ℚ) A, ∀ t ∈ Dec (F := ℚ) A, k (s * t) = k s * k t) → ∃ θ : ↥(Dec (F := ℚ) A) →* c.Oˣ, Continuous (fun g => ((θ g : c.Oˣ) : c.O)) ∧ ∀ g, (((θ g : c.Oˣ) : c.O) : Qbar l) = k g := by
  first | exact @GlobalTheory.LocChar.unit_of_integral | exact GlobalTheory.LocChar.unit_of_integral | (intros; apply GlobalTheory.LocChar.unit_of_integral <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.not_congruent_zero_intCast_mul_prime_pow : ∀ (l : ℕ) [Fact l.Prime] (t k : ℕ) (d : ℤ), d ≠ 0 → |d| < (l : ℤ) ^ t → ¬ Cg (t + k) ((d : Qbar l) * ((l : ℕ) : Qbar l) ^ k) 0 := by
  first | exact @GlobalTheory.Ord2.IntNorm.not_cg_int_mul_pow | exact GlobalTheory.Ord2.IntNorm.not_cg_int_mul_pow | (intros; apply GlobalTheory.Ord2.IntNorm.not_cg_int_mul_pow <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.irreducible_restriction_of_iso : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (l : ℕ) [Fact l.Prime] (W W' : R2 Ω l), RepIso W W' → IsIrr (W.comp (H0g W).subtype) → IsIrr (W'.comp (H0g W').subtype) := by
  first | exact @GlobalTheory.IrrConj.irr_of_repIso | exact GlobalTheory.IrrConj.irr_of_repIso | (intros; apply GlobalTheory.IrrConj.irr_of_repIso <;> assumption)
end
