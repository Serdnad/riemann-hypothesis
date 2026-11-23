module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle250
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle398
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightGoodReductionAtPrime
public import Formalism.SharpRestriction.LevelLetterCocycles.SecondComparisonInCoordinates
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle354
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle400
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle401
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg
import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.SqrtNegL

open Polynomial

theorem natDegree_minpoly_sqrt (l : ℕ) [Fact l.Prime] (F : IntermediateField ℚ_[l] (Om l)) (y : Om l)
    (hF : F ≤ MaximalUnramifiedExtension l) (hy : y ^ 2 = -(l : Om l)) (hyK : y ∉ MaximalUnramifiedExtension l) :
    (minpoly F y).natDegree = 2 := by
  have hint : IsIntegral F y := (Algebra.IsIntegral.isIntegral (R := ℚ_[l]) y).tower_top
  have hmon : (X ^ 2 + C ((l : ℕ) : F)).Monic :=
    (monic_X_pow 2).add_of_left (degree_C_le.trans_lt (by simp))
  have hdeg : (X ^ 2 + C ((l : ℕ) : F)).natDegree = 2 := by
    rw [natDegree_add_eq_left_of_natDegree_lt] <;> simp
  have hev : aeval y (X ^ 2 + C ((l : ℕ) : F)) = 0 := by
    simp [hy]
  have h1 : (minpoly F y).natDegree ≤ 2 :=
    hdeg ▸ natDegree_le_natDegree (minpoly.min F y hmon hev)
  have h2 : 0 < (minpoly F y).natDegree := minpoly.natDegree_pos hint
  have h3 : (minpoly F y).natDegree ≠ 1 := by
    intro h
    obtain ⟨a, ha⟩ := minpoly.natDegree_eq_one_iff.mp h
    apply hyK
    rw [← ha]
    exact hF a.2
  omega

theorem structure_sqrt_neg : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (K : FinExt l) (M : IntermediateField ℚ_[l] (Om l)) (y : Om l), M ≤ MaximalUnramifiedExtension l → y ^ 2 = -(l : Om l) → y ∉ MaximalUnramifiedExtension l → y ∈ IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1} → K.1 = M ⊔ IntermediateField.adjoin ℚ_[l] {y} → K.1 = K0 K ⊔ IntermediateField.adjoin ℚ_[l] {y} ∧ K.1 ≤ Ks K 1 ∧ Module.finrank ↥(K0 K) ↥K.1 = 2 ∧ Module.finrank ℚ_[l] ↥(Ks K 1) = (l - 1) / 2 * Module.finrank ℚ_[l] ↥K.1 := by
  intro l _ hl2 K M y hM hy hyK hyz hK
  have hyK1 : y ∈ K.1 := hK ▸ (le_sup_right : IntermediateField.adjoin ℚ_[l] {y} ≤ _)
      (IntermediateField.mem_adjoin_simple_self _ _)
  have hMK0 : M ≤ K0 K := le_inf (hK ▸ le_sup_left) hM
  have hA : IntermediateField.adjoin ℚ_[l] {y} ≤ K.1 :=
    (IntermediateField.adjoin_simple_le_iff).2 hyK1
  have e1 : K.1 = K0 K ⊔ IntermediateField.adjoin ℚ_[l] {y} :=
    le_antisymm (hK.le.trans (sup_le_sup_right hMK0 _)) (sup_le inf_le_left hA)
  have e2 : K.1 ≤ Ks K 1 := by
    rw [e1]
    exact sup_le_sup_left ((IntermediateField.adjoin_simple_le_iff).2 hyz) _
  have hd := natDegree_minpoly_sqrt l (K0 K) y inf_le_right hy hyK
  have hf : Module.finrank ℚ_[l] ↥K.1 = Module.finrank ℚ_[l] ↥(K0 K) * 2 := by
    rw [← hd, ← GlobalTheory.HubLoc.finrank_sup_adjoin, ← e1]
  have hpos := GlobalTheory.HubLoc.finrank_maxUnramifiedSubfield_padicFinExt_pos K
  have := K.2
  have htow := Module.finrank_mul_finrank ℚ_[l] ↥(K0 K) ↥K.1
  have e3 : Module.finrank ↥(K0 K) ↥K.1 = 2 := by
    rw [hf] at htow
    exact Nat.eq_of_mul_eq_mul_left hpos htow
  refine ⟨e1, e2, e3, ?_⟩
  rw [GlobalTheory.HubLoc.finrank_Ks_eq l K 1 one_pos, hf]
  have hodd : Odd l := (Fact.out : l.Prime).odd_of_ne_two hl2
  have hev : 2 ∣ l - 1 := by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k, by omega⟩
  obtain ⟨k, hk⟩ := hev
  rw [hk]
  rw [Nat.sub_self, pow_zero, one_mul]
  rw [Nat.mul_div_cancel_left k two_pos]
  ring

end GlobalTheory.SqrtNegL
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.PartialTraceGain

theorem sum_range_mul_eq {M : Type*} [AddCommMonoid M] (f : ℕ → M) (a b : ℕ) :
    ∑ i ∈ Finset.range (a * b), f i = ∑ i ∈ Finset.range a, ∑ j ∈ Finset.range b, f (i + a * j) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_range_succ, add_comm (a * b) i]

theorem norm_natCast_lt_one (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : Om l)‖ < 1 := by
  have h : ((l : ℕ) : Om l) = algebraMap ℚ_[l] (Om l) (l : ℚ_[l]) := by simp
  rw [h, norm_algebraMap']
  exact Padic.norm_p_lt_one

def fixedAdd {l : ℕ} [Fact l.Prime] (H : Subgroup (GQ l)) : AddSubgroup (Om l) where
  carrier := {x | ∀ g ∈ H, g x = x}
  add_mem' := fun {a b} ha hb g hg => by rw [map_add (f := _), ha g hg, hb g hg]
  zero_mem' := fun g _ => map_zero g
  neg_mem' := fun {a} ha g hg => by rw [map_neg, ha g hg]

theorem apply_mem_fixedAdd {l : ℕ} [Fact l.Prime] {H : Subgroup (GQ l)} (hH : H.Normal)
    (σ : GQ l) {x : Om l} (hx : x ∈ fixedAdd H) : σ x ∈ fixedAdd H := by
  intro g hg
  have h1 := hx _ (hH.conj_mem' g hg σ)
  have h2 : g * σ = σ * (σ⁻¹ * g * σ) := by group
  calc g (σ x) = (g * σ) x := rfl
    _ = σ ((σ⁻¹ * g * σ) x) := by rw [h2]; rfl
    _ = σ x := by rw [h1]

theorem apply_sum_pow {l : ℕ} [Fact l.Prime] (σ : GQ l) (m : ℕ) {x : Om l}
    (hx : (σ ^ m) x = x) :
    σ (∑ j ∈ Finset.range m, (σ ^ j) x) = ∑ j ∈ Finset.range m, (σ ^ j) x := by
  have h1 : σ (∑ j ∈ Finset.range m, (σ ^ j) x) = ∑ j ∈ Finset.range m, (σ ^ (j + 1)) x := by

    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_succ']; rfl
  have h2 := Finset.sum_range_succ' (fun j => (σ ^ j) x) m
  rw [Finset.sum_range_succ, hx] at h2
  rw [h1]
  simpa using h2.symm

theorem pow_apply_of_fixed {l : ℕ} [Fact l.Prime] (σ : GQ l) {y : Om l} (hy : σ y = y) (i : ℕ) :
    (σ ^ i) y = y := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [pow_succ]
    change (σ ^ i) (σ y) = y
    rw [hy, ih]

theorem norm_sum_pow_le : ∀ (l : ℕ) [Fact l.Prime] (γ : GQ l), γ ∈ (MaximalUnramifiedExtension l).fixingSubgroup → ∀ (H : ℕ → Subgroup (GQ l)) (k : ℕ), (∀ n, (H n).Normal) → (∀ n, (H n).index ≠ 0) → (∀ n, (H n).index ≤ l ^ (k + n)) → (∀ n, γ ^ l ^ n ∈ H n) → (∀ n, ∀ h ∈ H n, ∃ i : ℕ, ((γ ^ l ^ n) ^ i)⁻¹ * h ∈ H (n + 1)) → ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ (n : ℕ) (x : Om l), (∀ g ∈ H n, g x = x) → ‖∑ i ∈ Finset.range (l ^ n), (γ ^ i) x‖ ≤ ρ ^ n * ‖x‖ := by
  intro l hl γ hγ H k hN hI hIle hpow hgen
  have hp : l.Prime := hl.out
  have hl1 : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hp.one_le
  have ha0 : 0 ≤ ‖((l : ℕ) : Om l)‖ := norm_nonneg _
  have ha1 := norm_natCast_lt_one l
  have hpk : (1 : ℝ) ≤ (l : ℝ) ^ (k + 1) := one_le_pow₀ hl1
  have he0 : (0 : ℝ) < (1 : ℝ) / (l : ℝ) ^ (k + 1) := by positivity
  have he1 : (1 : ℝ) / (l : ℝ) ^ (k + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact hpk
  set ρ : ℝ := ‖((l : ℕ) : Om l)‖ ^ ((1 : ℝ) / (l : ℝ) ^ (k + 1)) with hρ
  have hρ0 : 0 ≤ ρ := Real.rpow_nonneg ha0 _
  have hρ1 : ρ < 1 := Real.rpow_lt_one ha0 ha1 he0
  have haρ : ‖((l : ℕ) : Om l)‖ ≤ ρ := by
    have := Real.rpow_le_rpow_of_exponent_ge' ha0 ha1.le he0.le he1
    rwa [Real.rpow_one] at this
  have hmax : max (ρ ^ (l - 1)) ‖((l : ℕ) : Om l)‖ ≤ ρ := by
    refine max_le ?_ haρ
    have h2 := hp.two_le
    exact pow_le_of_le_one hρ0 hρ1.le (by omega)
  refine ⟨ρ, hρ0, hρ1, fun n => ?_⟩
  induction n with
  | zero => intro x _; simp
  | succ n ih =>
    intro x hx
    set σ : GQ l := γ ^ l ^ n with hσ
    have hσl : σ ^ l = γ ^ l ^ (n + 1) := by rw [hσ, ← pow_mul, ← pow_succ]
    have hxS : x ∈ fixedAdd (H (n + 1)) := hx
    set y : Om l := ∑ j ∈ Finset.range l, (σ ^ j) x with hy
    have hyS : y ∈ fixedAdd (H (n + 1)) :=
      sum_mem fun j _ => apply_mem_fixedAdd (hN _) _ hxS
    have hσy : σ y = y := apply_sum_pow σ l (by rw [hσl]; exact hx _ (hpow _))
    have hyH : ∀ g ∈ H n, g y = y := by
      intro g hg
      obtain ⟨i, hi⟩ := hgen n g hg
      have h1 := hyS _ hi
      have h2 : g = σ ^ i * ((σ ^ i)⁻¹ * g) := by group
      calc g y = (σ ^ i) (((σ ^ i)⁻¹ * g) y) := by
            conv_lhs => rw [h2]
            rfl
        _ = y := by rw [h1, pow_apply_of_fixed σ hσy]
    have hmove : ∀ z ∈ fixedAdd (H (n + 1)), ‖σ z - z‖ ≤ ρ * ‖z‖ := by
      intro z hz
      have := GlobalTheory.T.norm_inertia_pow_prime_pow_sub_le l γ hγ (H (n + 1)) (hN _) (hI _) (k + (n + 1)) (n + 1) (hIle _)
        (hpow _) n (by omega) z hz
      rwa [show k + (n + 1) - n = k + 1 by omega] at this
    have hyn : ‖y‖ ≤ ρ * ‖x‖ :=
      (GlobalTheory.T.norm_sum_pow_apply_le_and_norm_pow_prime_sub_le l σ (fixedAdd (H (n + 1))) ρ hρ0 hρ1.le
        (fun z hz => apply_mem_fixedAdd (hN _) σ hz) hmove x hxS).1.trans
        (mul_le_mul_of_nonneg_right hmax (norm_nonneg _))
    have hsum : ∑ i ∈ Finset.range (l ^ (n + 1)), (γ ^ i) x
        = ∑ i ∈ Finset.range (l ^ n), (γ ^ i) y := by
      rw [pow_succ, sum_range_mul_eq]
      refine Finset.sum_congr rfl fun i _ => ?_

      rw [hy, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [pow_add, pow_mul]; rfl
    rw [hsum]
    calc _ ≤ ρ ^ n * ‖y‖ := ih y hyH
      _ ≤ ρ ^ n * (ρ * ‖x‖) := mul_le_mul_of_nonneg_left hyn (pow_nonneg hρ0 _)
      _ = ρ ^ (n + 1) * ‖x‖ := by ring

end GlobalTheory.PartialTraceGain
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation

theorem _root_.GlobalTheory.T.nonempty_thetaOnBdRPlus_periodData : ∀ (D : Formalism.BasicNotions.D7) (l : ℕ) [Fact l.Prime], Nonempty (ThetaL (D.loc l) (D.locA l)) := by
  first | exact @GlobalTheory.ThetaTie.nonempty_thetaL | exact GlobalTheory.ThetaTie.nonempty_thetaL | (intros; apply GlobalTheory.ThetaTie.nonempty_thetaL <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.weight_good_reduction_at_prime : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), admitted D HW F → Conclusion5 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; TBeAt S := by
  first | exact @GlobalTheory.TwistTors.twist_torsion_facts | exact GlobalTheory.TwistTors.twist_torsion_facts | (intros; apply GlobalTheory.TwistTors.twist_torsion_facts <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.WachUnit

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem unitGen_exists : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), ∃ e, Formalism.MainNotions.WachCoordinates.Br.UnitGen ((HW l).W K s LL h) e := by
  intro D HW F l _ K s LL h
  obtain ⟨e, -, -, -, -, hN, -, hφ, hγ, hfree⟩ := GlobalTheory.WachUnit.unitVector D HW F l K s LL h
  exact ⟨e, hN, hφ, hγ, hfree⟩

end GlobalTheory.WachUnit
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.thetaLift_goodRow_point_good : ∀ (D : D7), SumRepresentations.Conclusion42 D → ∀ (i : D.nd.Loc) (σ : D.what₂.FT) (P : D.naut.AV i) (x : D.nd.X i), D.nd.goodRow σ → thetaOf D.nd D.naut i σ P → D.naut.ptV i P = some x → x ∈ ZgoodN D.nd D.naut i ∧ AtM D.nd D.naut i σ := by
  first | exact @GlobalTheory.GoodLiftPoint.good_of_lift | exact GlobalTheory.GoodLiftPoint.good_of_lift | (intros; apply GlobalTheory.GoodLiftPoint.good_of_lift <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.exists_integral_model_rep_coeffRing : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc) (a : ℕ) (ρ : GE N →* GL (Fin a) (Qbar (N.l i))), SumRepresentations.At.ContQ N i ρ → (∀ g s t, ∃ x, A.iotaQ i x = ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i))) s t) → ∃ (r : GE N →* GL (Fin a) (N.O i)) (Pm : GL (Fin a) (Qbar (N.l i))), ∀ g, mapRep (iotaOQ N A i) r g = Pm⁻¹ * ρ g * Pm := by
  first | exact @GlobalTheory.IntegralModelOverCoeff.exists_integral_model_rep | exact GlobalTheory.IntegralModelOverCoeff.exists_integral_model_rep | (intros; apply GlobalTheory.IntegralModelOverCoeff.exists_integral_model_rep <;> assumption)
end
