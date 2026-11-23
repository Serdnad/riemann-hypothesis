module

import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle054
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Analysis.Analytic.Order
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle139
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle111
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle053
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle112
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle141
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle142
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle140
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle138
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
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KZ.JInt

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

lemma det_pos (g : GQ) : 0 < ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 := by
  have h := g.2
  rw [Matrix.mem_glpos] at h
  simpa [ent, Matrix.det_fin_two] using h

lemma den_ne (g : GQ) {z : ℂ} (hz : z ∈ Hs) : (ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  have hz' : 0 < z.im := hz
  simp at him hre
  have hc : ent g 1 0 = 0 := by
    rcases him with h1 | h1
    · exact h1
    · exact absurd h1 hz'.ne'
  rw [hc] at hre
  simp at hre
  have := det_pos g
  rw [hc, hre] at this
  simp at this

lemma mob_im (g : GQ) {z : ℂ} (hz : z ∈ Hs) : mob g z ∈ Hs := by
  apply GlobalTheory.FNMob.mob_mem <;> assumption

lemma mob_diff (g : GQ) : DifferentiableOn ℂ (mob g) Hs := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  show DifferentiableAt ℂ (fun z => ((ent g 0 0 : ℂ) * z + (ent g 0 1 : ℂ)) / ((ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ))) z
  exact ((differentiableAt_id.const_mul _).add_const _).div
    ((differentiableAt_id.const_mul _).add_const _) (den_ne g hz)

def holR (X : Tower Ω ε) : Subring X.K where
  carrier := {h | ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an h = (φ : Mero)}
  mul_mem' := by
    rintro a b ⟨φ, hφ, ha⟩ ⟨ψ, hψ, hb⟩
    exact ⟨φ * ψ, hφ.mul hψ, by rw [map_mul, ha, hb]; rfl⟩
  one_mem' := ⟨fun _ => 1, differentiableOn_const 1, by rw [map_one]; rfl⟩
  add_mem' := by
    rintro a b ⟨φ, hφ, ha⟩ ⟨ψ, hψ, hb⟩
    exact ⟨φ + ψ, hφ.add hψ, by rw [map_add (f := _), ha, hb]; rfl⟩
  zero_mem' := ⟨fun _ => 0, differentiableOn_const 0, by rw [map_zero]; rfl⟩
  neg_mem' := by
    rintro a ⟨φ, hφ, ha⟩
    exact ⟨-φ, hφ.neg, by rw [map_neg, ha]; rfl⟩

end GlobalTheory.KZ.JInt

namespace GlobalTheory.KZ.JInt


open Polynomial in
theorem jK_sl_isIntegral : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
    ∀ g : GQ, IsIntegral (Algebra.adjoin Ω {X.jK}) (X.sl g X.jK) := by
  intro Ω _ _ _ ε Tw hε hj g
  set f := Tw.sl g Tw.jK with hf
  obtain ⟨M, hM, hlev⟩ := Tw.level f
  haveI : NeZero M := ⟨hM.ne'⟩
  let red : SL(2, ℤ) →* SL(2, ZMod M) := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))

  have hred : ∀ γ γ' : SL(2, ℤ), red γ = red γ' → Tw.sl (ofSL γ) f = Tw.sl (ofSL γ') f := by
    intro γ γ' h
    have hmem : γ' * γ⁻¹ ∈ CongruenceSubgroup.Gamma M := by
      rw [CongruenceSubgroup.Gamma_mem']
      show red (γ' * γ⁻¹) = 1
      rw [map_mul, map_inv, h, mul_inv_cancel]
    have e : γ' = (γ' * γ⁻¹) * γ := by group
    rw [e, map_mul, Tw.sl_mul, hlev _ hmem]
  let S : Set Tw.K := Set.range fun γ : SL(2, ℤ) => Tw.sl (ofSL γ) f
  have hSfin : S.Finite := by
    classical
    let F : SL(2, ZMod M) → Tw.K := fun γb => if h : ∃ γ, red γ = γb then Tw.sl (ofSL h.choose) f else 0
    apply (Set.finite_range F).subset
    rintro _ ⟨γ, rfl⟩
    refine ⟨red γ, ?_⟩
    have h : ∃ γ', red γ' = red γ := ⟨γ, rfl⟩
    simp only [F, dif_pos h]
    exact hred _ _ h.choose_spec
  let T := hSfin.toFinset
  have hT : ∀ y, y ∈ T ↔ y ∈ S := fun y => Set.Finite.mem_toFinset hSfin
  let P : Tw.K[X] := ∏ y ∈ T, (X - C y)
  have hPmon : P.Monic := monic_prod_of_monic _ _ fun y _ => monic_X_sub_C y
  have hfT : f ∈ T := by
    rw [hT]; exact ⟨1, by simp [Tw.sl_one]⟩
  have hPf : P.eval f = 0 := by
    rw [eval_prod]
    exact Finset.prod_eq_zero hfT (by simp)

  have hinv : ∀ (δ : SL(2, ℤ)) (n : ℕ), Tw.sl (ofSL δ) (P.coeff n) = P.coeff n := by
    intro δ n
    have hmap : P.map ((Tw.sl (ofSL δ) : Tw.K ≃ₐ[Ω] Tw.K) : Tw.K →+* Tw.K) = P := by
      simp only [P, Polynomial.map_prod, Polynomial.map_sub, map_X, map_C]
      refine Finset.prod_nbij' (fun y => Tw.sl (ofSL δ) y) (fun y => Tw.sl (ofSL δ⁻¹) y) ?_ ?_ ?_ ?_ ?_
      · intro y hy
        rw [hT] at hy ⊢
        obtain ⟨γ, rfl⟩ := hy
        exact ⟨γ * δ, by simp only [map_mul, Tw.sl_mul]⟩
      · intro y hy
        rw [hT] at hy ⊢
        obtain ⟨γ, rfl⟩ := hy
        exact ⟨γ * δ⁻¹, by simp only [map_mul, Tw.sl_mul]⟩
      · intro y _
        rw [← Tw.sl_mul, ← map_mul, mul_inv_cancel, map_one, Tw.sl_one]
      · intro y _
        rw [← Tw.sl_mul, ← map_mul, inv_mul_cancel, map_one, Tw.sl_one]
      · intro y _
        rfl
    have := congrArg (fun p => p.coeff n) hmap
    simpa [coeff_map] using this

  obtain ⟨φ, hφ, hjφ⟩ := hj
  have hmemS : ∀ y ∈ T, y ∈ holR Tw := by
    intro y hy
    rw [hT] at hy
    obtain ⟨γ, rfl⟩ := hy
    have e : Tw.sl (ofSL γ) f = Tw.sl (g * ofSL γ) Tw.jK := by rw [Tw.sl_mul]
    show Tw.sl (ofSL γ) f ∈ holR Tw
    rw [e]
    exact ⟨fun z => φ (mob (g * ofSL γ) z),
      hφ.comp (mob_diff _) (fun z hz => mob_im _ hz), Tw.an_sl _ _ _ hjφ⟩
  let Q : (holR Tw)[X] := ∏ y ∈ T.attach, (X - C ⟨y.1, hmemS y.1 y.2⟩)
  have hQ : Q.map (holR Tw).subtype = P := by
    simp only [Q, P, Polynomial.map_prod, Polynomial.map_sub, map_X, map_C, Subring.subtype_apply]
    exact Finset.prod_attach T (fun y => X - C y)
  have hhol : ∀ n, P.coeff n ∈ holR Tw := by
    intro n
    rw [← hQ, coeff_map]
    exact (Q.coeff n).2

  have hA : ∀ n, P.coeff n ∈ Algebra.adjoin Ω {Tw.jK} := fun n =>
    GlobalTheory.T.slTwo_invariant_holomorphic_mem_adjoin_jInvariant ε Tw hε ⟨φ, hφ, hjφ⟩ (P.coeff n) (fun δ => hinv δ n) (hhol n)
  have hlift : P ∈ lifts (algebraMap (Algebra.adjoin Ω {Tw.jK}) Tw.K) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hA n⟩, rfl⟩
  obtain ⟨q, hqmap, -, hqmon⟩ := lifts_and_natDegree_eq_and_monic hlift hPmon
  exact ⟨q, hqmon, by rw [eval₂_eq_eval_map, hqmap, hPf]⟩

end GlobalTheory.KZ.JInt
end
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

lemma isDia_mul_of_isDia {N l : ℕ} {d e : ℤ} {σ τ : SL(2, ℤ)} (hσ : IsDia N l d σ)
    (hτ : IsDia N l e τ) : IsDia N l (d * e) (σ * τ) := by
  obtain ⟨h1, h2⟩ := hσ
  obtain ⟨h3, h4⟩ := hτ
  have h1' : ((σ 1 0 : ℤ) : ZMod N) = 0 := by
    have := congrArg (ZMod.castHom (dvd_mul_right N l) (ZMod N)) h1
    simpa using this
  refine ⟨?_, ?_⟩
  · simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [h1, h3]; ring
  · simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [h1', h2, h4]; ring

lemma heckeT_congr_dia {N l q : ℕ} {k : ℤ} {σ τ : SL(2, ℤ)} (hN : 0 < N)
    (hσ : IsDia N l q σ) (hτ : IsDia N l q τ) (f : ModularForm (lev N l) k) :
    heckeT k q σ ⇑f = heckeT k q τ ⇑f := by
  have := GlobalTheory.T.diamondOperatorOfMatrix_congr N l k q σ τ hN hσ hτ f
  unfold dia at this
  unfold heckeT
  rw [this]

lemma heckeT_coeff_formula_comm_distinct_primes {q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r) (kq kr : ℂ)
    (a b c e : ℕ → ℂ) (n : ℕ) :
    a (r * (q * n)) + kr * (if r ∣ q * n then b (q * n / r) else 0)
      + kq * (if q ∣ n then c (r * (n / q)) + kr * (if r ∣ n / q then e (n / q / r) else 0)
        else 0)
    = a (q * (r * n)) + kq * (if q ∣ r * n then c (r * n / q) else 0)
      + kr * (if r ∣ n then b (q * (n / r)) + kq * (if q ∣ n / r then e (n / r / q) else 0)
        else 0) := by
  have hcop : Nat.Coprime q r := (Nat.coprime_primes hq hr).2 hqr
  have i1 : r ∣ q * n ↔ r ∣ n := hcop.symm.dvd_mul_left
  have i2 : q ∣ r * n ↔ q ∣ n := hcop.dvd_mul_left
  have ha : r * (q * n) = q * (r * n) := by ring
  simp only [ha, i1, i2]
  by_cases hqn : q ∣ n <;> by_cases hrn : r ∣ n
  · have i3 : r ∣ n / q := by
      obtain ⟨m, rfl⟩ := hqn
      rw [Nat.mul_div_cancel_left _ hq.pos]
      exact (hcop.symm.dvd_mul_left).1 hrn
    have i4 : q ∣ n / r := by
      obtain ⟨m, rfl⟩ := hrn
      rw [Nat.mul_div_cancel_left _ hr.pos]
      exact (hcop.dvd_mul_left).1 hqn
    have d1 : q * n / r = q * (n / r) := Nat.mul_div_assoc q hrn
    have d2 : r * n / q = r * (n / q) := Nat.mul_div_assoc r hqn
    have d3 : n / r / q = n / q / r := by
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm]
    simp only [hqn, hrn, i3, i4, if_true, d1, d2, d3]
    ring
  · have i3 : ¬ r ∣ n / q := by
      intro h
      exact hrn (h.trans (Nat.div_dvd_of_dvd hqn))
    have d2 : r * n / q = r * (n / q) := Nat.mul_div_assoc r hqn
    simp only [hqn, hrn, i3, if_true, if_false, d2]
    ring
  · have i4 : ¬ q ∣ n / r := by
      intro h
      exact hqn (h.trans (Nat.div_dvd_of_dvd hrn))
    have d1 : q * n / r = q * (n / r) := Nat.mul_div_assoc q hrn
    simp only [hqn, hrn, i4, if_true, if_false, d1]
    ring
  · simp only [hqn, hrn, if_false]
    ring

theorem heckeT_comm : ∀ (N l q r : ℕ) (k : ℤ) (σ τ : SL(2, ℤ)), 0 < N → q.Prime → r.Prime →
    ¬ q ∣ N * l → ¬ r ∣ N * l → GlobalTheory.Hk.IsDia N l q σ → GlobalTheory.Hk.IsDia N l r τ →
    ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k,
      GlobalTheory.Hk.heckeT k q σ (GlobalTheory.Hk.heckeT k r τ ⇑f) = GlobalTheory.Hk.heckeT k r τ (GlobalTheory.Hk.heckeT k q σ ⇑f) := by
  intro N l q r k σ τ hN hq hr hqN hrN hσ hτ f
  by_cases hqr : q = r
  · subst hqr
    obtain ⟨g, hg⟩ := GlobalTheory.T.heckeTOperatorExplicit_modularForm N l q k τ hN hq hqN hτ f
    rw [heckeT_congr_dia hN hσ hτ f, ← hg, heckeT_congr_dia hN hσ hτ g]
  · obtain ⟨gr, hgr⟩ := GlobalTheory.T.heckeTOperatorExplicit_modularForm N l r k τ hN hr hrN hτ f
    obtain ⟨gq, hgq⟩ := GlobalTheory.T.heckeTOperatorExplicit_modularForm N l q k σ hN hq hqN hσ f
    obtain ⟨h1, hh1⟩ := GlobalTheory.T.heckeTOperatorExplicit_modularForm N l q k σ hN hq hqN hσ gr
    obtain ⟨h2, hh2⟩ := GlobalTheory.T.heckeTOperatorExplicit_modularForm N l r k τ hN hr hrN hτ gq
    obtain ⟨fσ, hfσ⟩ := GlobalTheory.T.diamondOperatorOfMatrix_modularForm_gamma1InterGamma0 N l k q σ hN hσ f
    obtain ⟨fτ, hfτ⟩ := GlobalTheory.T.diamondOperatorOfMatrix_modularForm_gamma1InterGamma0 N l k r τ hN hτ f
    have dσ : dia k σ ⇑gr = heckeT k r τ ⇑fσ := by
      rw [hgr, hfσ, GlobalTheory.T.hecke_operator_commutes_diamond N l r k q τ σ hN hr hrN hτ hσ f]
    have dτ : dia k τ ⇑gq = heckeT k q σ ⇑fτ := by
      rw [hgq, hfτ, GlobalTheory.T.hecke_operator_commutes_diamond N l q k r σ τ hN hq hqN hσ hτ f]
    have dd : dia k τ ⇑fσ = dia k σ ⇑fτ := by
      have h' : IsDia N l ((r : ℤ) * q) (σ * τ) := by
        rw [mul_comm]; exact isDia_mul_of_isDia hσ hτ
      rw [hfσ, hfτ, GlobalTheory.T.diamondOperatorOfMatrix_comp_mul N l k q r σ τ (σ * τ) hN hσ hτ (isDia_mul_of_isDia hσ hτ) f,
        GlobalTheory.T.diamondOperatorOfMatrix_comp_mul N l k r q τ σ (σ * τ) hN hτ hσ h' f]
    have key : h1 = h2 := by
      apply GlobalTheory.T.modularForm_gamma1InterGamma0_ext_qExpansionCoeff N l k hN
      intro n
      rw [hh1, hh2, GlobalTheory.T.qExpansionCoeff_heckeTOperator_gamma1InterGamma0 N l q k σ hN hq hqN hσ gr, GlobalTheory.T.qExpansionCoeff_heckeTOperator_gamma1InterGamma0 N l r k τ hN hr hrN hτ gq,
        dσ, dτ, GlobalTheory.T.qExpansionCoeff_heckeTOperator_gamma1InterGamma0 N l r k τ hN hr hrN hτ fσ, GlobalTheory.T.qExpansionCoeff_heckeTOperator_gamma1InterGamma0 N l q k σ hN hq hqN hσ fτ,
        hgr, hgq, GlobalTheory.T.qExpansionCoeff_heckeTOperator_gamma1InterGamma0 N l r k τ hN hr hrN hτ f, GlobalTheory.T.qExpansionCoeff_heckeTOperator_gamma1InterGamma0 N l q k σ hN hq hqN hσ f,
        dd, hfσ, hfτ]
      exact heckeT_coeff_formula_comm_distinct_primes hq hr hqr _ _ _ _ _ _ n
    rw [← hgr, ← hgq, ← hh1, ← hh2, key]

end GlobalTheory.Hk
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem _root_.GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties : (∀ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (((a : Mero) = (b : Mero)) ↔ ∀ z ∈ Hs, a z = b z)) ∧ (∀ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (∀ z ∈ Hs, a z * b z = 0) → (∀ z ∈ Hs, a z = 0) ∨ (∀ z ∈ Hs, b z = 0)) ∧ (∀ (g : GQ) (φ ψ : ℂ → ℂ), (φ : Mero) = (ψ : Mero) → ((fun z => φ (mob g z) : ℂ → ℂ) : Mero) = ((fun z => ψ (mob g z) : ℂ → ℂ) : Mero)) ∧ (∀ (φ ψ : ℂ → ℂ), (φ : Mero) = (ψ : Mero) → ∀ τ ∈ Hs, ∀ᶠ z in nhdsWithin τ {τ}ᶜ, φ z = ψ z) ∧ (∀ (m : ℕ) (a b : ℂ → ℂ), 0 < m → DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (∀ z ∈ Hs, a z ^ m = b z ^ m) → ∃ k : ℕ, ∀ z ∈ Hs, a z = Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / (m : ℂ)) * b z) := by
  first | exact @GlobalTheory.KZ.Germ.main | exact GlobalTheory.KZ.Germ.main | (intros; apply GlobalTheory.KZ.Germ.main <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem _root_.GlobalTheory.T.exists_holomorphic_root_upperHalfPlane : ∀ (h : ℂ → ℂ) (m : ℕ), 0 < m → DifferentiableOn ℂ h Hs → (∀ τ ∈ Hs, ∃ k : ℕ, analyticOrderAt h τ = ((m * k : ℕ) : ℕ∞)) → ∃ r : ℂ → ℂ, DifferentiableOn ℂ r Hs ∧ ∀ z ∈ Hs, r z ^ m = h z := by
  first | exact @GlobalTheory.KZ.H3.uhp_root | exact GlobalTheory.KZ.H3.uhp_root | (intros; apply GlobalTheory.KZ.H3.uhp_root <;> assumption)
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

theorem _root_.GlobalTheory.T.kummer_automorphism_moves_integers_almost_unit : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ F : Subfield L, ApproxRoot p v F → 0 < v (p : L) → v (p : L) < 1 → ∀ (G : Type) [Group G] [MulSemiringAction G L] (σ : G), (∀ x ∈ F, σ • x = x) → ∀ ζ α : L, IsPrimitiveRoot ζ p → α ≠ 0 → α ^ p ∈ F → σ • α = ζ * α → Moves v ⊤ σ := by
  first | exact @GlobalTheory.AlmostEt.kummer_moves | exact GlobalTheory.AlmostEt.kummer_moves | (intros; apply GlobalTheory.AlmostEt.kummer_moves <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.hahnSeries_eq_of_qExpansionSumAbove_eventually_eq : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (C C' C'' : ℝ) (φ φ' : ℂ → ℂ) (h h' : HahnSeries ℚ Ω), Den h → Den h' → HS ε C φ h → HS ε C' φ' h' → (∀ z : ℂ, C'' < z.im → φ z = φ' z) → h = h' := by
  first | exact @GlobalTheory.FN.hs_uniq | exact GlobalTheory.FN.hs_uniq | (intros; apply GlobalTheory.FN.hs_uniq <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver : ∀ E : Subring ℂ, (∀ f : ℍ → ℂ, f ∈ GlobalTheory.FN.ring E ↔ InR E f) ∧ ∀ c ∈ E, InR E fun _ => c := by
  first | exact @GlobalTheory.FN.mem_ring_iff_inR | exact GlobalTheory.FN.mem_ring_iff_inR | (intros; apply GlobalTheory.FN.mem_ring_iff_inR <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.hasSomeLevelOver_compGLTwoPosRat : ∀ (E : Subring ℂ) (g : GQ) (f : ℍ → ℂ), (∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) → InR E f → InR E (GlobalTheory.FN.cmp g f) := by
  first | exact @GlobalTheory.FN.inR_cmp | exact GlobalTheory.FN.inR_cmp | (intros; apply GlobalTheory.FN.inR_cmp <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.exists_cuspExpansion_discriminant_integer_leading_one : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ), ∃ h : HahnSeries ℚ Ω, IsExp ε DD h ∧ h ≠ 0 ∧ h.leadingCoeff = 1 ∧ ∀ r : ℚ, ∃ n : ℤ, h.coeff r = n := by
  first | exact @GlobalTheory.FNExpD.expD | exact GlobalTheory.FNExpD.expD | (intros; apply GlobalTheory.FNExpD.expD <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.mem_modularFunctionFractionField_of_qExpansions : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (a : ℂ → ℂ) (M : ℕ), 0 < M → DifferentiableOn ℂ a Hs → (∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ z ∈ Hs, a (mob (ofSL γ) z) = a z) → (∀ γ : SL(2, ℤ), ∃ (c : ℤ → Ω) (n0 : ℤ), (∀ n < n0, c n = 0) ∧ ∀ z ∈ Hs, HasSum (fun n : ℤ => ε (c n) * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z / M)) (a (mob (ofSL γ) z))) → ∃ f : T.K, T.an f = (a : Mero) := by
  first | exact @GlobalTheory.FN.exists_of_qexp | exact GlobalTheory.FN.exists_of_qexp | (intros; apply GlobalTheory.FN.exists_of_qexp <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.eq_zero_of_mem_aug_of_isEig_of_not_intertwine : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (J N : Set G) (θ : G → ℂ), Datum J θ → Datum N (fun _ => 1) → (∀ y ∈ N, (y ∈ J ∧ θ y = 1) ∨ ∃ j ∈ J, y * j * y⁻¹ ∈ J ∧ θ j ≠ θ (y * j * y⁻¹)) → ∀ u ∈ aug π N (fun _ => 1), IsEig π J θ u → u = 0 := by
  first | exact @GlobalTheory.PsType.eig_eq_zero_of_mem_aug_of_not_intertwine | exact GlobalTheory.PsType.eig_eq_zero_of_mem_aug_of_not_intertwine | (intros; apply GlobalTheory.PsType.eig_eq_zero_of_mem_aug_of_not_intertwine <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.isEig_apply_of_sub_mem_aug : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (J N₀ N₁ : Set G) (θ : G → ℂ) (z : G), Datum J θ → Datum N₀ (fun _ => 1) → (∀ y ∈ N₀, y ∈ J ∧ θ y = 1) → (∀ y, y ∈ N₁ ↔ z * y * z⁻¹ ∈ N₀) → (∀ j ∈ J, ∃ y ∈ N₀, z⁻¹ * (y⁻¹ * j) * z ∈ J ∧ θ (z⁻¹ * (y⁻¹ * j) * z) = θ j) → ∀ u u' : V, IsEig π J θ u → IsEig π N₁ (fun _ => 1) u' → u - u' ∈ aug π N₁ (fun _ => 1) → IsEig π J θ (π z u') := by
  first | exact @GlobalTheory.PsType.isEig_translate_of_sub_mem_aug | exact GlobalTheory.PsType.isEig_translate_of_sub_mem_aug | (intros; apply GlobalTheory.PsType.isEig_translate_of_sub_mem_aug <;> assumption)
end
