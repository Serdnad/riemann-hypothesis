module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QminorSwapAdjacent
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle105
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfTateTwistInvariantFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle046
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle047
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle106
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle107
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryTorusUnipotentCosetTransportIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep Formalism.REAL

namespace GlobalTheory.CapAdInv

section Algebra

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem qdet_ad {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E) (P Q : Matrix (Fin n) (Fin n) ℂ)
    (hQP : Q * P = 1) (u : ℂ) :
    qdet (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) u = qdet E u := by
  first
  | exact @_root_.GlobalTheory.QuantumMinorAdjacentSwap.qdet_conj
  | exact _root_.GlobalTheory.QuantumMinorAdjacentSwap.qdet_conj
  | (apply _root_.GlobalTheory.QuantumMinorAdjacentSwap.qdet_conj <;> assumption)
  | (intros; apply _root_.GlobalTheory.QuantumMinorAdjacentSwap.qdet_conj <;> assumption)
  | (intros; apply @_root_.GlobalTheory.QuantumMinorAdjacentSwap.qdet_conj <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.QuantumMinorAdjacentSwap.qdet_conj ..)

theorem qdet_semiconj {n : ℕ} (E E' : Fin n → Fin n → A) (R : A) (h : ∀ a b, R * E a b = E' a b * R) (u : ℂ) :
    R * qdet E u = qdet E' u * R := by
  have hp : ∀ {t : ℕ} (x y : Fin t → A), (∀ k, R * x k = y k * R) →
      R * (List.ofFn x).prod = (List.ofFn y).prod * R := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      intro x y h
      simp only [List.ofFn_succ, List.prod_cons]
      rw [← mul_assoc, h, mul_assoc, ih _ _ (fun k => h k.succ), mul_assoc]
  simp only [qdet, qminor, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← mul_assoc, ← (Int.cast_commute _ R).eq, mul_assoc, mul_assoc, hp]
  intro k
  simp only [Tm, mul_add, add_mul, h]
  split_ifs
  · rw [Algebra.commutes]
  · simp

end Algebra

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem rt_lie (y : GL (Fin a) (Cinf E)) (X : Matrix (Fin a) (Fin a) (Cinf E)) :
    rt E a (infGL E a y) * lie E a (toL X) = lie E a (toL (y.val * X * (y⁻¹).val)) * rt E a (infGL E a y) := by
  refine LinearMap.ext fun φ => Subtype.ext <| funext fun g => ?_
  change fderiv ℝ (chart φ.1 (g * infGL E a y)) (oneL E a) (toL X) =
    fderiv ℝ (chart (fun x => φ.1 (x * infGL E a y)) g) (oneL E a) (toL (y.val * X * (y⁻¹).val))
  have hd : DifferentiableAt ℝ (chart φ.1 g) (toL y.val) :=
    (contDiffAt_chart φ.2 g (val_mem_invSet y)).differentiableAt (by simp)
  have e1 : lmul (toL y.val) (oneL E a) = toL y.val := mul_one y.val
  have e2 : rmul (toL y.val) (oneL E a) = toL y.val := one_mul y.val
  rw [chart_mul, chart_rt_inf, fderiv_comp _ (by rw [e1]; exact hd) (lmul (toL y.val)).differentiableAt,
    fderiv_comp _ (by rw [e2]; exact hd) (rmul (toL y.val)).differentiableAt, e1, e2,
    ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv]
  exact congrArg (fun Z => fderiv ℝ (chart φ.1 g) (toL y.val) (toL Z)) (Units.inv_mul_cancel_right (y.val * X) y).symm


omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem mul_atEmb (τ : E →+* ℂ) (x : Cinf E) (z : ℂ) : x * atEmb τ z = atEmb τ (coord τ x * z) := by
  classical
  funext w
  unfold atEmb coord
  by_cases hw : w = InfinitePlace.mk τ
  · subst hw; split_ifs <;> simp
  · simp [Pi.single_eq_of_ne hw]

theorem rt_lieS (y : GL (Fin a) (Cinf E)) (τ : E →+* ℂ) (i j : Fin a) (z : ℂ) :
    rt E a (infGL E a y) * lieS E a i j (atEmb τ z) =
      (∑ k, ∑ l, lieS E a k l (atEmb τ (coord τ (y.val k i) * coord τ ((y⁻¹).val j l) * z))) *
        rt E a (infGL E a y) := by
  rw [lieS_apply, rt_lie]
  congr 1
  have e : y.val * Matrix.single i j (atEmb τ z) * (y⁻¹).val =
      ∑ k, ∑ l, Matrix.single k l (atEmb τ (coord τ (y.val k i) * coord τ ((y⁻¹).val j l) * z)) := by
    rw [Matrix.matrix_eq_sum_single (y.val * Matrix.single i j (atEmb τ z) * (y⁻¹).val)]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    congr 1
    rw [← map_mul, ← mul_atEmb]
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and, mul_right_comm]
  rw [e]
  let L : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] Module.End ℂ (Sm E a) := lie E a
  have key : ∀ f : Fin a → Fin a → Matrix (Fin a) (Fin a) (Cinf E), L (∑ k, ∑ l, f k l) = ∑ k, ∑ l, L (f k l) :=
    fun f => by simp only [map_sum]
  exact key _

theorem rt_Eop (y : GL (Fin a) (Cinf E)) (τ : E →+* ℂ) (i j : Fin a) :
    rt E a (infGL E a y) * Eop τ i j =
      (∑ k, ∑ l, (coord τ (y.val k i) * coord τ ((y⁻¹).val j l)) • Eop τ k l) * rt E a (infGL E a y) := by
  rw [Eop, mul_smul_comm, mul_sub, mul_smul_comm, rt_lieS, rt_lieS, ← smul_mul_assoc, ← sub_mul, ← smul_mul_assoc]
  congr 1
  simp only [Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  generalize coord τ (y.val k i) * coord τ ((y⁻¹).val j l) = c
  have hL : ∀ w : ℂ, lieS E a k l (atEmb τ w) =
      (w.re : ℂ) • lieS E a k l (atEmb τ 1) + (w.im : ℂ) • lieS E a k l (atEmb τ Complex.I) := fun w => by
    rw [atEmb_eq τ w, map_add (f := _), map_smul, map_smul]
    rfl
  rw [hL (c * 1), hL (c * Complex.I), Eop]
  conv_rhs => rw [← Complex.re_add_im c]
  simp only [mul_one, Complex.mul_I_re, Complex.mul_I_im, Complex.ofReal_neg]
  match_scalars
  · ring
  · linear_combination ((c.im : ℂ) / 2) * Complex.I_mul_I

theorem cap_commute_rt_infGL : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (τ : E →+* ℂ) (u : ℂ)
    (y : GL (Fin a) (Cinf E)), Commute (cap (a := a) τ u) (rt E a (infGL E a y)) := by
  intro E _ _ _ a τ u y
  have h := qdet_semiconj _ _ _ (rt_Eop y τ) (u + ((a : ℂ) - 1) / 2)
  have hQP : ((y⁻¹).val.map (coord τ)) * (y.val.map (coord τ)) = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul]; simp
  have h2 := qdet_ad _ (glRel_Eop τ) _ _ hQP (u + ((a : ℂ) - 1) / 2)
  simp only [Matrix.map_apply] at h2
  rw [h2] at h
  exact h.symm

end GlobalTheory.CapAdInv
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem exists_factor_of_range {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* D) (ι : B →+* D)
    (hι : Function.Injective ι) (h : ∀ x, f x ∈ ι.range) : ∃ u : A →+* B, ∀ x, ι (u x) = f x := by
  let e : B ≃+* ι.range := RingEquiv.ofBijective ι.rangeRestrict
    ⟨fun a b hab => hι (congrArg Subtype.val hab), ι.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp (f.codRestrict ι.range h), fun x => ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply (f.codRestrict ι.range h x))

theorem padic_mem_range {l : ℕ} [Fact l.Prime] {B D : Type} [CommRing B] [CommRing D] (g : ℚ_[l] →+* D)
    (ι : B →+* D) (hz : ∀ z : ℤ_[l], g z ∈ ι.range) (hl : IsUnit (l : B)) (q : ℚ_[l]) : g q ∈ ι.range := by
  obtain ⟨w, hw⟩ := hl.exists_right_inv
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have h1 : g (l : ℚ_[l])⁻¹ = ι w := by
    have a : (l : D) * ι w = 1 := by simpa using congrArg ι hw
    have b : g (l : ℚ_[l])⁻¹ * (l : D) = 1 := by
      rw [← map_natCast g, ← map_mul, inv_mul_cancel₀ hl0, map_one]
    calc g (l : ℚ_[l])⁻¹ = g (l : ℚ_[l])⁻¹ * ((l : D) * ι w) := by rw [a, mul_one]
      _ = ι w := by rw [← mul_assoc, b, one_mul]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖(l : ℚ_[l]) ^ n * q‖ ≤ 1 := by
    have hp : ‖(l : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one
    have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hp).mul_const ‖q‖
    rw [zero_mul] at ht
    obtain ⟨n, hn⟩ := (ht.eventually (ge_mem_nhds one_pos)).exists
    exact ⟨n, by rwa [norm_mul, norm_pow]⟩
  have e : q = ((l : ℚ_[l])⁻¹) ^ n * ((⟨_, hn⟩ : ℤ_[l]) : ℚ_[l]) := by
    change q = _ * ((l : ℚ_[l]) ^ n * q)
    rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hl0, one_pow, one_mul]
  rw [e, map_mul, map_pow, h1]
  exact mul_mem (pow_mem (ι.mem_range_self w) n) (hz _)

theorem exists_unram_to_cris : ∀ (l : ℕ) [Fact l.Prime], ∀ (o : Om l →+* Per.BdRp l) (ι : Per.Bcris l →+* Per.BdR l), IsSec o → Function.Injective ι → (∀ a : Per.Ainf l, ι (Per.aB l a) = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l a)) → IsUnit (l : Per.Bcris l) → ∃ u : ↥(MaximalUnramifiedExtension l) →+* Per.Bcris l, ∀ c : ↥(MaximalUnramifiedExtension l), ι (u c) = algebraMap (Per.BdRp l) (Per.BdR l) (o (c : Om l)) := by
  intro l _ o ι ho hι ha hl
  let f : Om l →+* Per.BdR l := (algebraMap (Per.BdRp l) (Per.BdR l)).comp o
  have hq : ∀ q : ℚ_[l], f (algebraMap ℚ_[l] (Om l) q) ∈ ι.range :=
    padic_mem_range (f.comp (algebraMap ℚ_[l] (Om l))) ι
      (fun z => ⟨Per.aB l (Per.zA l z), (ha _).trans (by
        rw [← ho.z]; rfl)⟩) hl
  let S : Subalgebra ℚ_[l] (Om l) :=
    { (ι.range.comap f).toSubsemiring with algebraMap_mem' := hq }
  have key : ∀ x ∈ MaximalUnramifiedExtension l, f x ∈ ι.range := by
    intro x hx
    unfold MaximalUnramifiedExtension at hx
    rw [← IntermediateField.mem_toSubalgebra, IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
      (fun y _ => Algebra.IsAlgebraic.isAlgebraic y)] at hx
    refine (Algebra.adjoin_le (S := S) ?_) hx
    rintro c ⟨m, h0, h1, h2⟩
    obtain ⟨⟨xb, hxb⟩, h⟩ := GlobalTheory.T.rootOfUnity_prime_to_teichmuller_lift l o ho c m h0 h1 h2
    refine ⟨Per.aB l (Per.tm xb), ?_⟩
    exact (ha _).trans (by rw [(h xb hxb).2.2]; rfl)
  exact exists_factor_of_range (f.comp (MaximalUnramifiedExtension l).val.toRingHom) ι hι (fun x => key x x.2)

end GlobalTheory.MemLoc
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.frobenius_acris_decomposition_mu_power : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → ∀ w : Per.Acris l, (l : Per.Acris l) * w = algebraMap (Per.Ainf l) (Per.Acris l) (mu e) ^ (l - 1) → ∀ y : Per.Acris l, ∃ (a : Per.Ainf l) (z : Per.Acris l), phiA l y = algebraMap (Per.Ainf l) (Per.Acris l) a + w * z := by
  first | exact @GlobalTheory.MemLoc.phiA_mem_ainf_add | exact GlobalTheory.MemLoc.phiA_mem_ainf_add | (intros; apply GlobalTheory.MemLoc.phiA_mem_ainf_add <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → (∀ (n : ℕ) (y : Per.BdRp l), y ∈ Per.FilP l n ↔ aDp l (xi e) ^ n ∣ y) ∧ (∀ y : Per.BdRp l, aDp l (xi e) * y = 0 → y = 0) ∧ IsAdicComplete (Ideal.span {aDp l (xi e)}) (Per.BdRp l) ∧ (∀ n : ℕ, Function.Surjective (Per.ev l n)) := by
  first | exact @GlobalTheory.MemLoc.filtration_eq_xi_pow | exact GlobalTheory.MemLoc.filtration_eq_xi_pow | (intros; apply GlobalTheory.MemLoc.filtration_eq_xi_pow <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.eq_zero_of_tateTwist_invariant_finiteExtension : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (K : FinExt l) (i : ℤ) (x : ℂ_[l]), i ≠ 0 → (∀ g ∈ GK K, Per.σC g x * (algebraMap ℚ_[l] ℂ_[l] ((C.χ g : ℤ_[l]) : ℚ_[l])) ^ i = x) → x = 0 := by
  first | exact @GlobalTheory.MemLoc.tate_twist_invariants | exact GlobalTheory.MemLoc.tate_twist_invariants | (intros; apply GlobalTheory.MemLoc.tate_twist_invariants <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.periodRings_galoisAction_laws_frobenius_comm : ∀ (l : ℕ) [Fact l.Prime], (∀ (g h : Per.Gq l) (x : Per.Bcris l), Per.σB (g * h) x = Per.σB g (Per.σB h x)) ∧ (∀ x : Per.Bcris l, Per.σB 1 x = x) ∧ (∀ (g h : Per.Gq l) (x : Per.BdR l), Per.σD (g * h) x = Per.σD g (Per.σD h x)) ∧ (∀ x : Per.BdR l, Per.σD 1 x = x) ∧ (∀ (g : Per.Gq l) (x : Per.Bcris l), Per.φB l (Per.σB g x) = Per.σB g (Per.φB l x)) ∧ (∀ (g : Per.Gq l) (a : Per.Ainf l), Per.σB g (Per.aB l a) = Per.aB l (Per.σA g a)) ∧ (∀ a : Per.Ainf l, Per.φB l (Per.aB l a) = Per.aB l (Per.φA l a)) ∧ (∀ (g : Per.Gq l) (z : ℤ_[l]), Per.σA g (Per.zA l z) = Per.zA l z) ∧ (∀ z : ℤ_[l], Per.φA l (Per.zA l z) = Per.zA l z) ∧ (∀ (g : Per.Gq l) (y : Per.BdRp l), Per.σD g (algebraMap (Per.BdRp l) (Per.BdR l) y) = algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp g y)) ∧ (∀ (g : Per.Gq l) (a : Per.Ainf l), Per.σDp g (aDp l a) = aDp l (Per.σA g a)) ∧ (∀ (g : Per.Gq l) (x : Per.Acris l), Per.σB g (algebraMap (Per.Acris l) (Per.Bcris l) x) = algebraMap (Per.Acris l) (Per.Bcris l) (sigA g x)) ∧ ∀ x : Per.Acris l, Per.φB l (algebraMap (Per.Acris l) (Per.Bcris l) x) = algebraMap (Per.Acris l) (Per.Bcris l) (phiA l x) := by
  first | exact @GlobalTheory.MemLoc.ActLaws.act_laws | exact GlobalTheory.MemLoc.ActLaws.act_laws | (intros; apply GlobalTheory.MemLoc.ActLaws.act_laws <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorusPart

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem mono_gtTorus_and_factor {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {A : Type}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {ρ : R →+* A} {D : Out.DegPre R} {e : ℕ}
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {G₀ : Over (Sp A)} [GrpObj G₀]
    {φ : G₀.left ⟶ G.left} (g : Out.GtCoord I D e G) (hρ : ∀ x ∈ I ^ (e + 1), ρ x = 0)
    (h : IsGrpPullback G₀ G (spMap ρ) φ) :
    Mono (gtTorus g hρ h) ∧ ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
      (i : splitTorus (Sp A) X ⟶ G₀), IsMonHom i →
        ∃ r : D.X →+ X, i = GlobalTheory.SplitTorus.torusMap _ r ≫ gtTorus g hρ h := by
  have := g.i_hom; have := g.q_hom; have := D.P.isAb.proper
  have : IsProper (Out.thickObj R I e D.P.A).hom := inferInstanceAs (IsProper (pullback.snd _ _))
  obtain ⟨q', hq', hk'⟩ := exists_isKernel_pullTorus (isGrpPullback_thickLift hρ h) g.i g.q g.isKernel
  have hk : IsPullback (gtTorus g hρ h) (toUnit _) q' η[_] := hk'
  have : IsProper ((Over.pullback (thickPt e hρ)).obj (Out.thickObj R I e D.P.A)).hom :=
    inferInstanceAs (IsProper (pullback.snd _ _))
  haveI : ConnectedSpace (Sp A) := GlobalTheory.SplitTorus.connectedSpace_of_isLocalRing A
  have hm : Mono (gtTorus g hρ h) := ⟨fun a b k => hk.hom_ext k (toUnit_unique _ _)⟩
  refine ⟨hm, fun X _ _ _ i hi => ?_⟩
  haveI := hi; haveI := hq'
  have ht : i ≫ q' = toUnit _ ≫ η[_] :=
    splitTorus_hom_proper_trivial_local A X _ (i ≫ q') inferInstance
  let u := hk.lift i (toUnit _) ht
  have hu : u ≫ gtTorus g hρ h = i := hk.lift_fst _ _ _
  have : IsMonHom u := Serre.isMonHom_of_mul_comp u fun T x y => by
    rw [← cancel_mono (gtTorus g hρ h), MonObj.mul_comp (x ≫ u), Category.assoc, Category.assoc,
      Category.assoc, hu, MonObj.mul_comp]
  obtain ⟨r, hr⟩ := GlobalTheory.SplitTorus.exists_eq_torusMap u
  exact ⟨r, by rw [← hr, hu]⟩

theorem mono_gtTorus_unif_and_factor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (t : SAB H (Sp R)) (P : PELUnif I t)
    (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (a : R →+* A) (e : ℕ) (ha : ∀ x ∈ I ^ (e + 1), a x = 0)
    (G₀ : Over (Sp A)) [GrpObj G₀] (φ : G₀.left ⟶ t.G.left) (h : IsGrpPullback G₀ t.G (spMap a) φ),
    Mono (GlobalTheory.TorusPart.gtTorus (P.U.gt e) ha h) ∧
    ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp A) X ⟶ G₀), IsMonHom i →
      ∃ ρ : P.D.toPre.X →+ X, i = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.gtTorus (P.U.gt e) ha h := by
  intro E _ _ _ H R _ _ I t P A _ _ _ a e ha G₀ _ φ h
  exact mono_gtTorus_and_factor (P.U.gt e) ha h

end GlobalTheory.TorusPart
end
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open ReciprocityTheory.ChartRestriction.G GlobalTheory.Points
open Classical

noncomputable section
namespace GlobalTheory.ZH.RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

def constHom (M : RatModel o Ω) (U : M.Z.Opens) : o →+* Γ(M.Z, U) :=
  (M.s.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom

theorem finiteType_constHom (M : RatModel o Ω) {U : M.Z.Opens} (hU : IsAffineOpen U) :
    (M.constHom U).FiniteType := by
  have := M.lft
  have h1 : (M.s.appLE ⊤ U (fun _ _ => trivial)).hom.FiniteType :=
    M.s.finiteType_appLE (isAffineOpen_top _) hU _
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of o)).symm.commRingCatIsoToRingEquiv.surjective
  exact h1.comp h2

variable {Ω' : Type} [Field Ω'] [Algebra o Ω']

theorem exists_nbhd_of_map_O (M : RatModel o Ω) (M' : RatModel o Ω') (φ : Ω →ₐ[o] Ω') {z' : M'.Z} {z : M.Z}
    (hz : ∀ a ∈ M.O z, φ a ∈ M'.O z') :
    ∃ (V : M'.Z.Opens) (U : M.Z.Opens), z' ∈ V ∧ IsAffineOpen U ∧ (U : Set M.Z).Nonempty ∧
      ∀ x ∈ M.ringOn U, φ x ∈ M'.ringOn V := by
  obtain ⟨U, hU, hzU, -⟩ := exists_isAffineOpen_mem_and_subset (U := (⊤ : M.Z.Opens)) (x := z) trivial
  have hUne : (U : Set M.Z).Nonempty := ⟨z, hzU⟩
  letI := (M.constHom U).toAlgebra
  obtain ⟨s, hs⟩ := (M.finiteType_constHom hU).out
  let V : M'.Z.Opens := ⟨⋂ f ∈ s, {w | φ (valF M.pt U f) ∈ M'.O w},
    isOpen_biInter_finset fun f _ => M'.isOpen_setOf_mem_O _⟩
  have hzV : z' ∈ V := Set.mem_iInter₂.2 fun f _ => hz _ (valF_mem_O hzU f)
  have hsV : ∀ f ∈ s, φ (valF M.pt U f) ∈ M'.ringOn V := fun f hf =>
    mem_ringOn.2 fun w hw => Set.mem_iInter₂.1 hw f hf
  have key : ∀ f : Γ(M.Z, U), φ (valF M.pt U f) ∈ M'.ringOn V := by
    intro f
    have hf : f ∈ Algebra.adjoin o (s : Set Γ(M.Z, U)) := hs ▸ Algebra.mem_top
    induction hf using Algebra.adjoin_induction with
    | mem x hx => exact hsV x hx
    | algebraMap r =>
      have e : valF M.pt U (algebraMap o Γ(M.Z, U) r) = algebraMap o Ω r := M.valF_constFn hUne r
      rw [e, AlgHom.commutes]
      exact Subalgebra.algebraMap_mem _ r
    | add x y _ _ hx hy =>
      rw [← M.res_apply U hUne, map_add (f := _), map_add (f := _), res_apply, res_apply]
      exact add_mem hx hy
    | mul x y _ _ hx hy =>
      rw [← M.res_apply U hUne, map_mul, map_mul, res_apply, res_apply]
      exact mul_mem hx hy
  refine ⟨V, U, hzV, hU, hUne, fun x hx => ?_⟩
  obtain ⟨f, rfl⟩ := (mem_ringOn_iff_exists hUne).1 hx
  exact key f

theorem exists_isHom_of_map_O :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω']
      (M' : RatModel o Ω') (φ : Ω →ₐ[o] Ω'), (∀ z' : M'.Z, ∃ z : M.Z, ∀ a ∈ M.O z, φ a ∈ M'.O z') →
        ∃ f : M'.Z ⟶ M.Z, M.IsHom M' φ f := by
  intro o Ω _ _ _ M Ω' _ _ M' φ h
  refine exists_isHom_of_local fun z' => ?_
  obtain ⟨z, hz⟩ := h z'
  exact exists_nbhd_of_map_O M M' φ hz

end GlobalTheory.ZH.RatModel
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd

theorem _root_.GlobalTheory.T.heckeAlgebra_comp_unitaryGroupAntidiagTransport_mem : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x)), (∀ x, x ∈ intL K ↔ g x ∈ intL K) → ∀ (n : ℕ) (h' : GU σ' n → ℂ), h' ∈ Hecke ℂ (KU σ' n) → (fun y => h' (guMap g hg n y)) ∈ Hecke ℂ (KU σ n) := by
  first | exact @GlobalTheory.SatInd.guMap_hecke_comap | exact GlobalTheory.SatInd.guMap_hecke_comap | (intros; apply GlobalTheory.SatInd.guMap_hecke_comap <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd

theorem _root_.GlobalTheory.T.inertHeckeOperator_indep_of_inertDatum : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv Dv' : InertDatum L n v w) (U : Subgroup (GAf L n)) (W : Type) [AddCommGroup W] [Module ℂ W] (h' : GU Dv'.σw n → ℂ), IsBiInv (KU Dv'.σw n) h' → ∀ f : GAf L n → W, heckeFunI L n U Dv' h' f = heckeFunI L n U Dv (fun y => h' (guMap (gEquiv Dv Dv') (gEquiv_comm Dv Dv') n y)) f := by
  first | exact @GlobalTheory.SatInd.heckeFunI_indepDatum | exact GlobalTheory.SatInd.heckeFunI_indepDatum | (intros; apply GlobalTheory.SatInd.heckeFunI_indepDatum <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd

theorem _root_.GlobalTheory.T.unitarySatake_invariant_antidiagTransport : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x)), (∀ x, x ∈ intL K ↔ g x ∈ intL K) → ∀ (ϖ ϖ' : K) (q n m : ℕ) (h' : GU σ' n → ℂ), IsBiInv (KU σ' n) h' → (∀ (a : Fin m → ℤ) (y : GU σ n), (∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = tMat ϖ n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ↔ (∃ u : GU σ' n, IsUnipU u ∧ ∃ k ∈ KU σ' n, ((guMap g hg n y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = tMat ϖ' n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) → ∀ α : Fin m → ℂ, SatU ϖ q (fun y => h' (guMap g hg n y)) α = SatU ϖ' q h' α := by
  first | exact @GlobalTheory.SatInd.satU_guMap | exact GlobalTheory.SatInd.satU_guMap | (intros; apply GlobalTheory.SatInd.satU_guMap <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd

theorem _root_.GlobalTheory.T.unitaryTorus_unipotent_coset_transport_iff : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x)), (∀ x, x ∈ intL K ↔ g x ∈ intL K) → ∀ (ϖ ϖ' : K) (q q' n m : ℕ), IsUnramInv ϖ σ q → IsUnramInv ϖ' σ' q' → 2 * m ≤ n → ∀ (a : Fin m → ℤ) (y : GU σ n), (∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = tMat ϖ n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ↔ (∃ u : GU σ' n, IsUnipU u ∧ ∃ k ∈ KU σ' n, ((guMap g hg n y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = tMat ϖ' n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  first | exact @GlobalTheory.SatInd.cosetT_iff | exact GlobalTheory.SatInd.cosetT_iff | (intros; apply GlobalTheory.SatInd.cosetT_iff <;> assumption)
end
