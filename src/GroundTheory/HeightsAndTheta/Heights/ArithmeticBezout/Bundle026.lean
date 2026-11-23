module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PIncidenceZeroLocus
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle016
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ProjChowNonzero

theorem aeval_smul_of_isHomogeneous {Ω : Type*} [Field Ω] [Algebra ℂ Ω] {n m : ℕ}
    {φ : MvPolynomial (Fin n) ℂ} (hφ : φ.IsHomogeneous m) (c : Ω) (x : Fin n → Ω) :
    aeval (c • x) φ = c ^ m * aeval x φ := by
  simp only [aeval_def, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg := hφ.degree_eq_sum_deg_support hd
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← hdeg]
  ring

theorem aeval_smul_eq_zero {Ω : Type*} [Field Ω] [Algebra ℂ Ω] {n : ℕ}
    {W : Ideal (MvPolynomial (Fin n) ℂ)} (hW : IsHomogIdeal W) {x : Fin n → Ω}
    (hx : ∀ q ∈ W, aeval x q = 0) (c : Ω) : ∀ q ∈ W, aeval (c • x) q = 0 := by
  intro q hq

  rw [← sum_homogeneousComponent q, map_sum]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [aeval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous d q), hx _ (hW q hq d), mul_zero]

theorem eq_zero_of_isFiniteProjection {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [Algebra ℂ Ω] {n d : ℕ}
    {W : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ} (hW : IsHomogIdeal W)
    (hA : ComplexSets.IsFiniteProjection W A) {x : Fin n → Ω} (hx : ∀ q ∈ W, aeval x q = 0)
    (hAx : ∀ i, aeval x (ComplexSets.linPoly A i) = 0) : x = 0 := by
  funext j
  by_contra hj
  obtain ⟨p, hpm, hp⟩ := hA.finite.to_isIntegral (Ideal.Quotient.mk W (X j))
  set q := Polynomial.eval₂ (ComplexSets.pullback A).toRingHom (X j) p with hq_def
  have hq : q ∈ W := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, hq_def, Polynomial.hom_eval₂]
    exact hp

  set ψ : MvPolynomial (Fin d) ℂ →+* Ω := (algebraMap ℂ Ω).comp (eval 0) with hψ
  have hcomp : ∀ c : Ω, ((aeval (c • x) : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Ω) : MvPolynomial (Fin n) ℂ →+* Ω).comp
      (ComplexSets.pullback A).toRingHom = ψ := by
    intro c
    refine MvPolynomial.ringHom_ext (fun a => by simp [hψ, ComplexSets.pullback]) fun i => ?_
    have h1 := aeval_smul_of_isHomogeneous (Ω := Ω) (m := 1) ?_ c x (φ := ComplexSets.linPoly A i)
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        ComplexSets.pullback, aeval_X, hψ, eval_X, Pi.zero_apply, map_zero]
      rw [h1, hAx i, mul_zero]
    · exact IsHomogeneous.sum _ _ _ fun j _ => (isHomogeneous_C_mul_X _ _)
  have hroot : ∀ c : Ω, (p.map ψ).eval (c * x j) = 0 := by
    intro c
    have h := aeval_smul_eq_zero hW hx c q hq
    rw [hq_def, ← AlgHom.coe_toRingHom, Polynomial.hom_eval₂, hcomp c] at h
    simpa [Polynomial.eval_map] using h
  have hzero : p.map ψ = 0 := Polynomial.funext fun r => by
    have := hroot (r / x j)
    rw [div_mul_cancel₀ r hj] at this
    simpa using this
  exact (hpm.map ψ).ne_zero hzero

theorem aeval_ne_zero_of_not_incidence {n k : ℕ} {W : Ideal (MvPolynomial (Fin n) ℂ)}
    {f : MvPolynomial (Fin k × Fin n) ℂ} (hW : IsHomogIdeal W) (hf : IsChowForm W k f)
    (v : Fin k × Fin n → AlgebraicClosure ℂ)
    (hv : ∀ y : Fin n → AlgebraicClosure ℂ, (∀ q ∈ W, aeval y q = 0) →
      (∀ i, ∑ j, v (i, j) * y j = 0) → y = 0) :
    aeval v f ≠ 0 := by
  intro h0
  have hinc : ∀ g ∈ incIdeal W k, aeval v g = 0 := by
    intro g hg
    have hmem : ∀ u ∈ incidence W k, aeval u g = 0 := by
      simpa only [incIdeal, Submodule.mem_iInf, RingHom.mem_ker] using hg
    obtain ⟨h, rfl⟩ := (hf.2 g).mp hmem
    rw [map_mul, h0, zero_mul]
  obtain ⟨y, hy0, hyW, hyv⟩ := IncidenceZeroLocus.proof ℂ n k W hW (AlgebraicClosure ℂ) v hinc
  exact hy0 (hv y hyW hyv)

abbrev Loc (e : ℕ) : Type := Localization.Away (X 0 : MvPolynomial (Fin (e + 1)) ℂ)

theorem projVar_zero_ne (e : ℕ) : projVar e 0 ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial (Fin (e + 1)) ℂ) _)).mpr (X_ne_zero 0)

def toK (e : ℕ) : Loc e →+* FractionRing (MvPolynomial (Fin (e + 1)) ℂ) :=
  IsLocalization.Away.lift (X 0) (g := algebraMap _ _) (IsUnit.mk0 _ (projVar_zero_ne e))

def pt (e : ℕ) : Fin (e + 1) → ℂ := fun i => if i = 0 then 1 else 0

def atPt (e : ℕ) : Loc e →+* AlgebraicClosure ℂ :=
  IsLocalization.Away.lift (X 0) (g := (algebraMap ℂ (AlgebraicClosure ℂ)).comp (eval (pt e)))
    (by simp [pt])

def locPar {n e : ℕ} (A : Matrix (Fin (e + 1)) (Fin n) ℂ) (ij : Fin (e + 1) × Fin n) : Loc e :=
  Fin.cases (motive := fun _ => Loc e)
    (algebraMap ℂ (Loc e) (A 0 ij.2) * IsLocalization.Away.invSelf (X 0 : MvPolynomial (Fin (e + 1)) ℂ))
    (fun i => algebraMap (MvPolynomial (Fin (e + 1)) ℂ) (Loc e)
      (X i.succ * C (A 0 ij.2) - X 0 * C (A i.succ ij.2))) ij.1

theorem toK_injective (e : ℕ) : Function.Injective (toK e) := by
  have h1 : Function.Injective (algebraMap (MvPolynomial (Fin (e + 1)) ℂ) (Loc e)) :=
    IsLocalization.injective (Loc e) (powers_le_nonZeroDivisors_of_noZeroDivisors (X_ne_zero 0))
  have h2 := IsFractionRing.injective (MvPolynomial (Fin (e + 1)) ℂ)
    (FractionRing (MvPolynomial (Fin (e + 1)) ℂ))
  exact (IsLocalization.lift_injective_iff _).mpr fun a b => h1.eq_iff.trans h2.eq_iff.symm

theorem toK_invSelf (e : ℕ) :
    toK e (IsLocalization.Away.invSelf (X 0 : MvPolynomial (Fin (e + 1)) ℂ)) = (projVar e 0)⁻¹ := by
  have h := congrArg (toK e) (IsLocalization.Away.mul_invSelf (S := Loc e) (X 0 : MvPolynomial (Fin (e + 1)) ℂ))
  rw [map_mul, map_one, toK, IsLocalization.Away.lift_eq] at h
  exact (eq_inv_of_mul_eq_one_right h)

theorem atPt_invSelf (e : ℕ) :
    atPt e (IsLocalization.Away.invSelf (X 0 : MvPolynomial (Fin (e + 1)) ℂ)) = 1 := by
  have h := congrArg (atPt e) (IsLocalization.Away.mul_invSelf (S := Loc e) (X 0 : MvPolynomial (Fin (e + 1)) ℂ))
  rw [map_mul, map_one] at h
  unfold atPt at h ⊢
  rw [IsLocalization.Away.lift_eq] at h
  simpa [pt] using h

theorem toK_algebraMap (e : ℕ) (a : ℂ) :
    toK e (algebraMap ℂ (Loc e) a) = algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)) a := by
  rw [IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Fin (e + 1)) ℂ) (Loc e), toK,
    IsLocalization.Away.lift_eq, ← IsScalarTower.algebraMap_apply]

theorem atPt_algebraMap (e : ℕ) (a : ℂ) :
    atPt e (algebraMap ℂ (Loc e) a) = algebraMap ℂ (AlgebraicClosure ℂ) a := by
  rw [IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Fin (e + 1)) ℂ) (Loc e), atPt,
    IsLocalization.Away.lift_eq]
  simp

theorem value_eq {n e : ℕ} (A : Matrix (Fin (e + 1)) (Fin n) ℂ) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) :
    eval (fun j => projPar A (.inr j))
        (Vertical.specRest (algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ))) f (projPar A)) =
      toK e (aeval (locPar A) f) := by
  rw [Vertical.specRest, eval₂_comp_left, aeval_def, eval₂_comp_left]
  congr 1
  · ext a
    simp [toK_algebraMap]
  · funext ⟨i, j⟩
    cases i using Fin.cases with
    | zero => simp [locPar, projPar, map_mul, toK_algebraMap, toK_invSelf, div_eq_mul_inv]
    | succ i =>
      simp [locPar, projPar, toK, IsLocalization.Away.lift_eq, projVar,
        IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Fin (e + 1)) ℂ)
          (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)), mul_comm]

theorem atPt_aeval {n e : ℕ} (A : Matrix (Fin (e + 1)) (Fin n) ℂ) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) :
    atPt e (aeval (locPar A) f) =
      aeval (fun ij : Fin (e + 1) × Fin n => Fin.cases (motive := fun _ => AlgebraicClosure ℂ)
        (algebraMap ℂ _ (A 0 ij.2)) (fun i => -algebraMap ℂ _ (A i.succ ij.2)) ij.1) f := by
  rw [aeval_def, eval₂_comp_left, aeval_def]
  congr 1
  · ext a
    simp [atPt_algebraMap]
  · funext ⟨i, j⟩
    cases i using Fin.cases with
    | zero => simp [locPar, atPt_algebraMap, atPt_invSelf]
    | succ i => simp [locPar, atPt, IsLocalization.Away.lift_eq, pt, Fin.succ_ne_zero]

end ProjChowNonzero

theorem ProjChowNonzero.proof : ProjChowNonzero.Statement := by
  intro n e W f A hW hf hA
  rw [ProjChowNonzero.value_eq]
  intro h0
  have h1 : aeval (ProjChowNonzero.locPar A) f = 0 :=
    (map_eq_zero_iff _ (ProjChowNonzero.toK_injective e)).mp h0
  have h2 := congrArg (ProjChowNonzero.atPt e) h1
  rw [map_zero, ProjChowNonzero.atPt_aeval] at h2
  refine ProjChowNonzero.aeval_ne_zero_of_not_incidence hW.isHomog hf _ (fun y hyW hyv => ?_) h2
  refine ProjChowNonzero.eq_zero_of_isFiniteProjection hW.isHomog hA hyW fun i => ?_
  have hi := hyv i
  cases i using Fin.cases with
  | zero => simpa [ComplexSets.linPoly] using hi
  | succ i =>
    simp only [Fin.cases_succ, neg_mul, Finset.sum_neg_distrib, neg_eq_zero] at hi
    simpa [ComplexSets.linPoly] using hi

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ProjSecDomain

abbrev Kf (e : ℕ) : Type := FractionRing (MvPolynomial (Fin (e + 1)) ℂ)

variable {n e : ℕ} (W : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (e + 1)) (Fin n) ℂ)

abbrev S : Type :=
  Vertical.SecAlg (W.map (MvPolynomial.map (algebraMap ℂ (Kf e)))) (projPar A)

theorem map_linPoly (k : Fin (e + 1)) :
    MvPolynomial.map (algebraMap ℂ (Kf e)) (ComplexSets.linPoly A k) =
      linForm fun j => algebraMap ℂ (Kf e) (A k j) := by

  simp [ComplexSets.linPoly, linForm, map_sum]

theorem projVar_ne_zero (k : Fin (e + 1)) : projVar e k ≠ 0 := by
  rw [projVar, ne_eq, IsFractionRing.to_map_eq_zero_iff]; exact X_ne_zero k

theorem chartForm_eq : Vertical.chartForm (projPar A) =
    C (projVar e 0)⁻¹ * linForm fun j => algebraMap ℂ (Kf e) (A 0 j) := by
  simp [Vertical.chartForm, linForm, projPar, Finset.mul_sum, div_eq_mul_inv, mul_comm, mul_left_comm]

theorem secForm_eq (i : Fin e) : Vertical.secForm (projPar A) i =
    C (projVar e i.succ) * (linForm fun j => algebraMap ℂ (Kf e) (A 0 j)) -
      C (projVar e 0) * linForm fun j => algebraMap ℂ (Kf e) (A i.succ j) := by
  simp [Vertical.secForm, linForm, projPar, Finset.mul_sum, ← Finset.sum_sub_distrib, sub_mul, mul_assoc]

variable {W A}

theorem mk_row (k : Fin (e + 1)) :
    Ideal.Quotient.mk (Vertical.secIdeal (W.map (MvPolynomial.map (algebraMap ℂ (Kf e)))) (projPar A))
        (linForm fun j => algebraMap ℂ (Kf e) (A k j)) =
      algebraMap (Kf e) (S W A) (projVar e k) := by
  set q := Ideal.Quotient.mk (Vertical.secIdeal (W.map (MvPolynomial.map (algebraMap ℂ (Kf e)))) (projPar A))
  have hC : ∀ c, q (C c) = algebraMap (Kf e) (S W A) c := fun _ => rfl
  have hu : q (C (projVar e 0)) * q (C ((projVar e 0)⁻¹)) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ (projVar_ne_zero 0), map_one, map_one]
  have hch : q (Vertical.chartForm (projPar A) - 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  rw [map_sub, map_one, chartForm_eq, map_mul] at hch
  have ha0 : q (linForm fun j => algebraMap ℂ (Kf e) (A 0 j)) = q (C (projVar e 0)) := by
    linear_combination q (C (projVar e 0)) * hch - q (linForm fun j => algebraMap ℂ (Kf e) (A 0 j)) * hu
  induction k using Fin.cases with
  | zero => rw [ha0, hC]
  | succ i =>
    have hs : q (Vertical.secForm (projPar A) i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2
        (Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)))
    rw [secForm_eq, map_sub, map_mul, map_mul, ha0] at hs
    rw [← hC]
    linear_combination (-q (C ((projVar e 0)⁻¹))) * hs +
      (q (C (projVar e i.succ)) - q (linForm fun j => algebraMap ℂ (Kf e) (A i.succ j))) * hu

variable (W A)

def psi : MvPolynomial (Fin n) ℂ ⧸ W →+* S W A :=
  Ideal.Quotient.lift W
    ((Ideal.Quotient.mk _).comp (MvPolynomial.map (algebraMap ℂ (Kf e))))
    fun _ hf => Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf)))

def M : Submonoid (MvPolynomial (Fin n) ℂ ⧸ W) :=
  (nonZeroDivisors (MvPolynomial (Fin (e + 1)) ℂ)).map (ComplexSets.projHom W A)

abbrev T : Type := Localization (M W A)

def kappa : Kf e →+* T W A :=
  IsLocalization.lift (M := nonZeroDivisors (MvPolynomial (Fin (e + 1)) ℂ)) (S := Kf e) (P := T W A)
    (g := (algebraMap _ (T W A)).comp (ComplexSets.projHom W A).toRingHom)
    fun y => IsLocalization.map_units (T W A) (⟨_, Submonoid.mem_map_of_mem _ y.2⟩ : M W A)

def phi : MvPolynomial (Fin n) (Kf e) →+* T W A :=
  eval₂Hom (kappa W A) fun j => algebraMap _ (T W A) (Ideal.Quotient.mk W (X j))

variable {W A}

theorem psi_mk (f : MvPolynomial (Fin n) ℂ) : psi W A (Ideal.Quotient.mk W f) =
    Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap ℂ (Kf e)) f) := rfl

theorem projHom_X (k : Fin (e + 1)) :
    ComplexSets.projHom W A (X k) = Ideal.Quotient.mk W (ComplexSets.linPoly A k) := by
  rw [ComplexSets.projHom, AlgHom.comp_apply, ComplexSets.pullback, aeval_X]; rfl

theorem psi_comp_projHom :
    (psi W A).comp (ComplexSets.projHom W A).toRingHom =
      (algebraMap (Kf e) (S W A)).comp (algebraMap (MvPolynomial (Fin (e + 1)) ℂ) (Kf e)) := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun k => ?_)
  · have h1 : algebraMap (MvPolynomial (Fin (e + 1)) ℂ) (Kf e) (C r) = algebraMap ℂ (Kf e) r :=
      (IsScalarTower.algebraMap_apply ℂ _ (Kf e) r).symm
    have h2 : ComplexSets.projHom W A (C r) = Ideal.Quotient.mk W (C r) := (ComplexSets.projHom W A).commutes r
    rw [RingHom.comp_apply, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h1, h2, psi_mk,
      map_C]
    rfl
  · rw [RingHom.comp_apply, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, projHom_X,
      psi_mk, map_linPoly, mk_row]
    rfl

theorem kappa_alg (p : MvPolynomial (Fin (e + 1)) ℂ) :
    kappa W A (algebraMap _ (Kf e) p) = algebraMap _ (T W A) (ComplexSets.projHom W A p) := by
  unfold kappa; exact IsLocalization.lift_eq _ p

theorem phi_C (c : Kf e) : phi W A (C c) = kappa W A c := eval₂Hom_C _ _ _

theorem phi_map (f : MvPolynomial (Fin n) ℂ) :
    phi W A (MvPolynomial.map (algebraMap ℂ (Kf e)) f) = algebraMap _ (T W A) (Ideal.Quotient.mk W f) := by
  have : (phi W A).comp (MvPolynomial.map (algebraMap ℂ (Kf e))) =
      (algebraMap _ (T W A)).comp (Ideal.Quotient.mk W) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
    · rw [RingHom.comp_apply, RingHom.comp_apply, map_C, phi_C,
        IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Fin (e + 1)) ℂ) (Kf e), kappa_alg, AlgHom.commutes]
      rfl
    · rw [RingHom.comp_apply, RingHom.comp_apply, map_X, phi, eval₂Hom_X']
  exact RingHom.congr_fun this f

theorem phi_row (k : Fin (e + 1)) :
    phi W A (linForm fun j => algebraMap ℂ (Kf e) (A k j)) = kappa W A (projVar e k) := by
  rw [← map_linPoly, phi_map, projVar, kappa_alg, projHom_X]

theorem secIdeal_le_ker :
    Vertical.secIdeal (W.map (MvPolynomial.map (algebraMap ℂ (Kf e)))) (projPar A) ≤
      RingHom.ker (phi W A) := by
  have hu : kappa W A (projVar e 0)⁻¹ * kappa W A (projVar e 0) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (projVar_ne_zero 0), map_one]
  refine sup_le (sup_le ?_ ?_) ?_
  · rw [Ideal.map_le_iff_le_comap]; intro f hf
    rw [Ideal.mem_comap, RingHom.mem_ker, phi_map, Ideal.Quotient.eq_zero_iff_mem.2 hf, map_zero]
  · rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, secForm_eq, map_sub, map_mul, map_mul, phi_C, phi_C, phi_row,
      phi_row]
    ring
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one,
      chartForm_eq, map_mul, phi_C, phi_row, hu, sub_self]

variable (W A)

def g : S W A →+* T W A := Ideal.Quotient.lift _ (phi W A) fun _ hf => RingHom.mem_ker.1 (secIdeal_le_ker hf)

theorem psi_unit (y : M W A) : IsUnit (psi W A y) := by
  obtain ⟨_, p, hp, rfl⟩ := y
  have h := RingHom.congr_fun (psi_comp_projHom (W := W) (A := A)) p
  rw [RingHom.comp_apply, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
  rw [h]
  exact (IsUnit.mk0 _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hp)).map _

def chi : T W A →+* S W A :=
  IsLocalization.lift (M := M W A) (S := T W A) (P := S W A) (g := psi W A) (psi_unit W A)

variable {W A}

theorem chi_kappa : (chi W A).comp (kappa W A) = algebraMap (Kf e) (S W A) := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial (Fin (e + 1)) ℂ)) ?_
  rw [RingHom.comp_assoc, kappa, IsLocalization.lift_comp, ← RingHom.comp_assoc, chi,
    IsLocalization.lift_comp, psi_comp_projHom]

theorem chi_g (s : S W A) : chi W A (g W A s) = s := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective s
  have : (chi W A).comp (phi W A) = Ideal.Quotient.mk _ := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
    · rw [RingHom.comp_apply, phi_C, ← RingHom.comp_apply, chi_kappa]; rfl
    · rw [RingHom.comp_apply, phi, eval₂Hom_X', chi, IsLocalization.lift_eq, psi_mk, map_X]
  show chi W A (phi W A f) = _
  exact RingHom.congr_fun this f

theorem proof : ProjSecDomain.Statement := by
  intro n e W A hW hA
  have hM : M W A ≤ nonZeroDivisors _ := by
    rintro _ ⟨p, hp, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero fun h =>
      nonZeroDivisors.ne_zero hp (hA.injective (by rw [map_zero]; exact h))
  have : IsDomain (T W A) := IsLocalization.isDomain_localization hM
  refine ⟨Function.Injective.isDomain (g W A) (Function.LeftInverse.injective chi_g), ?_⟩
  let _ : Algebra (MvPolynomial (Fin (e + 1)) ℂ) (MvPolynomial (Fin n) ℂ ⧸ W) :=
    (ComplexSets.projHom W A).toRingHom.toAlgebra
  have hint (j : Fin n) : IsIntegral (Kf e) (Ideal.Quotient.mk
      (Vertical.secIdeal (W.map (MvPolynomial.map (algebraMap ℂ (Kf e)))) (projPar A)) (X j)) := by
    have := IsIntegral.map_of_comp_eq (algebraMap _ (Kf e)) (psi W A) psi_comp_projHom.symm
      (hA.finite.to_isIntegral (Ideal.Quotient.mk W (X j)))
    rwa [psi_mk, map_X] at this
  have : Algebra.IsIntegral (Kf e) (S W A) := ⟨fun s => by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective s
    induction f using MvPolynomial.induction_on with
    | C c => exact isIntegral_algebraMap
    | add p q hp hq => rw [map_add (f := _)]; exact hp.add hq
    | mul_X p j hp => rw [map_mul]; exact hp.mul (hint j)⟩
  have : Algebra.FiniteType (Kf e) (S W A) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ (Kf e) _)
      (Ideal.Quotient.mkₐ_surjective _ _)
  exact Algebra.IsIntegral.finite

end ProjSecDomain

end

end GroundTheory.Heights₂.Heights
end
