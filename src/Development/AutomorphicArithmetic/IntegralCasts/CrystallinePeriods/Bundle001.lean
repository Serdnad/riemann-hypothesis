module

public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.UniformContinuousConstSMulOfIsIsometricSMul
public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.TruncLogEqOfPowEqZero
public import Mathlib.RingTheory.Smooth.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
public import Mathlib.RingTheory.Smooth.AdicCompletion
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Ideal Polynomial

namespace Reformulated.AutPerF

universe u v

section Trunc

variable {B : Type*} [CommRing B] [Algebra ℚ B]

theorem truncLog_zero (N : ℕ) : truncLog N (0 : B) = 0 := by simp [truncLog]

theorem derivative_truncLog_mul (N : ℕ) (z : B[X]) (hz : z ^ N = 0) :
    derivative (truncLog N z) * (1 + z) = derivative z := by
  have h1 : derivative (truncLog N z) = derivative z * ∑ k ∈ Finset.range N, (-z) ^ k := by
    rw [truncLog, derivative_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [derivative_smul, derivative_pow_succ, neg_pow z]
    have e : (C ((k : B) + 1) : B[X]) = algebraMap ℚ B[X] (k + 1) := by simp
    have e2 : ((-1 : B[X])) ^ k = algebraMap ℚ B[X] ((-1) ^ k) := by simp
    rw [e, e2, Algebra.smul_def, ← mul_assoc, ← mul_assoc, ← map_mul,
      div_mul_cancel₀ _ (by positivity)]
    ring
  have h2 := geom_sum_mul_neg (-z) N
  rw [neg_pow z N, hz, mul_zero, sub_zero, sub_neg_eq_add] at h2
  rw [h1, mul_assoc, h2, mul_one]

theorem truncLog_add {n : ℕ} {x y : B} (hx : x ^ n = 0) (hy : y ^ n = 0)
    (hxy : (x + y + x * y) ^ n = 0) :
    truncLog n (x + y + x * y) = truncLog n x + truncLog n y := by
  have hX : IsNilpotent (C x * X : B[X]) := ⟨n, by rw [mul_pow, ← C_pow, hx, C_0, zero_mul]⟩
  have hY : IsNilpotent (C y : B[X]) := ⟨n, by rw [← C_pow, hy, C_0]⟩
  obtain ⟨M, hM⟩ : IsNilpotent (C x * X + C y + C x * X * C y : B[X]) :=
    (Commute.all _ _).isNilpotent_add ((Commute.all _ _).isNilpotent_add hX hY)
      ((Commute.all _ _).isNilpotent_mul_left hY)
  set N := max M n
  have hM' := pow_eq_zero_of_le (le_max_left M n) hM
  have hX' : (C x * X : B[X]) ^ N = 0 := by
    rw [mul_pow, ← C_pow, pow_eq_zero_of_le (le_max_right M n) hx, C_0, zero_mul]
  have d1 := derivative_truncLog_mul N _ hM'
  have d2 := derivative_truncLog_mul N _ hX'
  have hu : IsUnit (1 + (C x * X + C y + C x * X * C y) : B[X]) :=
    IsNilpotent.isUnit_one_add ⟨M, hM⟩
  have hD : derivative (truncLog N (C x * X + C y + C x * X * C y) - truncLog N (C x * X)) = 0 := by
    refine hu.mul_right_cancel ?_
    rw [derivative_sub, sub_mul, d1, zero_mul,
      show (1 + (C x * X + C y + C x * X * C y) : B[X]) = (1 + C x * X) * (1 + C y) by ring,
      ← mul_assoc, d2]
    simp
    ring
  haveI : HasUniqueDiv B := HasUniqueDiv.of_module_rat B
  have hC := eq_C_of_derivative_eq_zero hD
  have e1 := congrArg (evalRingHom 1) hC
  have e0 := congrArg (evalRingHom 0) hC
  rw [map_sub, map_truncLog, map_truncLog] at e0 e1
  simp only [coe_evalRingHom, eval_add, eval_mul, eval_C, eval_X, mul_one, mul_zero, zero_add,
    zero_mul, add_zero, truncLog_zero, sub_zero] at e0 e1
  rw [← truncLog_eq_of_pow_eq_zero hx (le_max_right M n),
    ← truncLog_eq_of_pow_eq_zero hy (le_max_right M n),
    ← truncLog_eq_of_pow_eq_zero hxy (le_max_right M n), e0, ← e1]
  ring

end Trunc

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]

namespace BdRPlus

theorem eval_pow_eq_zero {x : BdRPlus p R} (hx : theta p R x = 0) (n : ℕ) :
    eval p R n x ^ n = 0 := evalₐ_pow_eq_zero _ ((theta_eq_zero_iff x).1 hx) n

theorem log_congr {u v : BdRPlus p R} (h : u = v) (hu : theta p R u = 1) (hv : theta p R v = 1) :
    log u hu = log v hv := by subst h; rfl

theorem log_mul (u v : BdRPlus p R) (hu : theta p R u = 1) (hv : theta p R v = 1) :
    log (u * v) (by rw [map_mul, hu, hv, one_mul]) = log u hu + log v hv := by
  refine ext_eval fun n => ?_
  have e : eval p R n (u * v - 1) =
      eval p R n (u - 1) + eval p R n (v - 1) + eval p R n (u - 1) * eval p R n (v - 1) := by
    rw [← map_mul, ← map_add (f := _), ← map_add (f := _)]; congr 1; ring
  rw [map_add (f := _), eval_log, eval_log, eval_log, e]
  refine truncLog_add (eval_pow_eq_zero (by simp [hu]) n) (eval_pow_eq_zero (by simp [hv]) n) ?_
  rw [← e]
  exact eval_pow_eq_zero (by simp [hu, hv]) n

theorem eval_two_log (u : BdRPlus p R) (hu : theta p R u = 1) :
    eval p R 2 (log u hu) = eval p R 2 (u - 1) := by
  rw [eval_log, truncLog, Finset.sum_range_succ, Finset.sum_range_one,
    eval_pow_eq_zero (x := u - 1) (by simp [hu]) 2]
  simp

def logTeich (η : tateModule p R) : BdRPlus p R :=
  log (algebraMap (Ainf p R) _ (Ainf.teich p η.1)) (by
    rw [IsScalarTower.algebraMap_apply _ (AinfInv p R), theta_algebraMap, AinfInv.theta_algebraMap,
      Ainf.theta_teich, show PreTilt.untilt η.1 = 1 from η.2, map_one])

theorem p_mul_inv : (p : BdRPlus p R) * algebraMap ℚ_[p] _ (p : ℚ_[p])⁻¹ = 1 := by
  rw [← map_natCast (algebraMap ℚ_[p] (BdRPlus p R)), ← map_mul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero), map_one]

def teichDivP (ϖ : PFlat p R) : BdRPlus p R :=
  algebraMap (Ainf p R) _ (Ainf.teich p ϖ.1) * algebraMap ℚ_[p] _ (p : ℚ_[p])⁻¹

theorem theta_teichDivP (ϖ : PFlat p R) : theta p R (teichDivP ϖ) = 1 := by
  rw [teichDivP, map_mul, IsScalarTower.algebraMap_apply _ (AinfInv p R), theta_algebraMap,
    AinfInv.theta_algebraMap, Ainf.theta_teich, ϖ.2, map_natCast, ← map_natCast (theta p R),
    ← map_mul, p_mul_inv, map_one]

def logFlat (ϖ : PFlat p R) : BdRPlus p R := log (teichDivP ϖ) (theta_teichDivP ϖ)

theorem logFlat_twist (η : tateModule p R) (ϖ : PFlat p R) :
    logFlat (ϖ.twist η) = logTeich η + logFlat ϖ := by
  rw [logFlat, logFlat, logTeich, ← log_mul]
  exact log_congr (by simp [teichDivP, PFlat.twist, mul_assoc]) _ _

end BdRPlus

end Reformulated.AutPerF
end
end

section

noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u v w

variable (p : ℕ) [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
variable {U : Type w} [CommRing U] [Fact ¬IsUnit (p : U)] [IsAdicComplete (span {(p : U)}) U]

theorem AinfInv.kerTheta_le_comap (f : R →+* S) :
    AinfInv.kerTheta p R ≤ (AinfInv.kerTheta p S).comap (AinfInv.map p f) := by
  intro x hx
  rw [Ideal.mem_comap, RingHom.mem_ker, AinfInv.theta_map, RingHom.mem_ker.1 hx, map_zero]


namespace BdRPlus

def map (f : R →+* S) : BdRPlus p R →+* BdRPlus p S :=
  adicMap _ _ (AinfInv.map p f) (AinfInv.kerTheta_le_comap p f)

variable {p}

theorem eval_map (f : R →+* S) (n : ℕ) (x : BdRPlus p R) :
    eval p S n (map p f x) = Ideal.quotientMap _ (AinfInv.map p f)
      (pow_le_comap_pow (AinfInv.kerTheta_le_comap p f) n) (eval p R n x) :=
  evalₐ_adicMap _ _ _ _ n x

@[simp] theorem map_algebraMap (f : R →+* S) (x : AinfInv p R) :
    map p f (algebraMap _ _ x) = algebraMap _ _ (AinfInv.map p f x) :=
  adicMap_algebraMap _ _ _ _ x

@[simp] theorem map_algebraMap_ainf (f : R →+* S) (x : Ainf p R) :
    map p f (algebraMap _ _ x) = algebraMap _ _ (Ainf.map p f x) := by
  rw [IsScalarTower.algebraMap_apply _ (AinfInv p R), map_algebraMap, AinfInv.map_algebraMap,
    ← IsScalarTower.algebraMap_apply]

@[simp] theorem map_id (x : BdRPlus p R) : map p (RingHom.id R) x = x :=
  adicMap_eq_id _ _ _ AinfInv.map_id x

theorem map_map (f : R →+* S) (g : S →+* U) (x : BdRPlus p R) :
    map p g (map p f x) = map p (g.comp f) x :=
  adicMap_adicMap _ _ _ _ _ _ _ _ _ (AinfInv.map_map f g) x

theorem theta_eq_of_eval_one {x : BdRPlus p R} {a : AinfInv p R}
    (h : eval p R 1 x = Ideal.Quotient.mk _ a) : theta p R x = AinfInv.theta p R a := by
  have h1 := AdicCompletion.factorₐ_evalₐ_one (AinfInv.kerTheta p R) x
  change Ideal.Quotient.factor _ (eval p R 1 x) = _ at h1
  rw [h] at h1
  change RingHom.kerLift _ (AdicCompletion.evalOneₐ (AinfInv.kerTheta p R) x) = _
  rw [← h1]
  rfl

theorem theta_map (f : R →+* S) (x : BdRPlus p R) :
    theta p S (map p f x) = awayMap p f (theta p R x) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (eval p R 1 x)
  rw [theta_eq_of_eval_one ha.symm, ← AinfInv.theta_map]
  apply theta_eq_of_eval_one
  rw [eval_map, ← ha, Ideal.quotientMap_mk]


variable (p) in
def mapEquiv (e : R ≃+* S) : BdRPlus p R ≃+* BdRPlus p S :=
  RingEquiv.ofRingHom (map p e.toRingHom) (map p e.symm.toRingHom)
    (by ext x; simp [map_map]) (by ext x; simp [map_map])

end BdRPlus

namespace BdR

def map (e : R ≃+* S) : BdR p R ≃+* BdR p S :=
  IsFractionRing.ringEquivOfRingEquiv (BdRPlus.mapEquiv p e)

variable {p}

theorem hom_ext {B : Type*} [CommRing B] {f g : BdR p R →+* B}
    (h : ∀ x : BdRPlus p R, f (algebraMap _ _ x) = g (algebraMap _ _ x)) : f = g :=
  IsLocalization.ringHom_ext (nonZeroDivisors (BdRPlus p R)) (RingHom.ext h)

@[simp] theorem map_algebraMap (e : R ≃+* S) (x : BdRPlus p R) :
    map p e (algebraMap _ _ x) = algebraMap _ _ (BdRPlus.map p (e : R →+* S) x) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ x

@[simp] theorem map_refl (x : BdR p R) : map p (RingEquiv.refl R) x = x :=
  RingHom.congr_fun (hom_ext (f := (map p (RingEquiv.refl R) : _ →+* _)) (g := RingHom.id _)
    (by simp)) x

theorem map_map (e : R ≃+* S) (e' : S ≃+* U) (x : BdR p R) :
    map p e' (map p e x) = map p (e.trans e') x :=
  RingHom.congr_fun (hom_ext (f := (map p e').toRingHom.comp (map p e).toRingHom)
    (g := (map p (e.trans e')).toRingHom) (by simp [BdRPlus.map_map])) x

end BdR

end Reformulated.AutPerF
end
end

section

noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u v w

variable (p : ℕ) [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)]

section Witt

variable {k : Type w} [CommRing k] [CharP k p] [PerfectRing k p]












end Witt

section FracWitt

variable {k : Type w} [Field k] [CharP k p] [PerfectRing k p]





end FracWitt

variable [IsAdicComplete (span {(p : R)}) R]



namespace BdRPlus

variable {p}

variable {F : Type v} {L : Type w} [CommRing F] [CommRing L] [Algebra F L]

theorem exists_section [Algebra.FormallySmooth F L]
    (hθ : Function.Surjective (AinfInv.theta p R)) (ι : F →+* AinfInv p R)
    (j : L →+* Localization.Away (p : R))
    (hj : ∀ a : F, j (algebraMap F L a) = AinfInv.theta p R (ι a)) :
    ∃ s : L →+* BdRPlus p R, (∀ x, theta p R (s x) = j x) ∧
      ∀ a : F, s (algebraMap F L a) = algebraMap (AinfInv p R) _ (ι a) := by
  letI : Algebra F (AinfInv p R) := ι.toAlgebra
  let e := RingHom.quotientKerEquivOfSurjective hθ
  let f : L →ₐ[F] AinfInv p R ⧸ AinfInv.kerTheta p R :=
    { e.symm.toRingHom.comp j with
      commutes' := fun a => by
        change e.symm (j (algebraMap F L a)) = Ideal.Quotient.mk _ (ι a)
        rw [RingEquiv.symm_apply_eq, hj]
        rfl }
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_adicCompletionEvalOneₐ_comp_eq f
  refine ⟨g.toRingHom, fun x => ?_, fun a => g.commutes a⟩
  have h1 : AdicCompletion.evalOneₐ (AinfInv.kerTheta p R) (g x) = e.symm (j x) :=
    AlgHom.congr_fun hg x
  change e (AdicCompletion.evalOneₐ (AinfInv.kerTheta p R) (g x)) = j x
  rw [h1, RingEquiv.apply_symm_apply]

def «section» [Algebra.FormallySmooth F L]
    (hθ : Function.Surjective (AinfInv.theta p R)) (ι : F →+* AinfInv p R)
    (j : L →+* Localization.Away (p : R))
    (hj : ∀ a : F, j (algebraMap F L a) = AinfInv.theta p R (ι a)) : L →+* BdRPlus p R :=
  (exists_section hθ ι j hj).choose

end BdRPlus

end Reformulated.AutPerF
end
end

section

noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u v w

variable (p : ℕ) [Fact p.Prime]
variable {C : Type u} [NormedField C] [CompleteSpace C] [CharZero C] [Fact (‖(p : C)‖ < 1)]
variable (O : ValuationSubring C) [IsUnitBall O]

namespace BdRPlus

def thetaC : BdRPlus p O →+* C :=
  (IsUnitBall.awayEquiv O p).toRingEquiv.toRingHom.comp (theta p O)

variable {p O}

theorem thetaC_apply (x : BdRPlus p O) :
    thetaC p O x = IsUnitBall.awayEquiv O p (theta p O x) := rfl

@[simp] theorem thetaC_algebraMap (x : Ainf p O) :
    thetaC p O (algebraMap _ _ x) = (Ainf.theta p O x : C) := by
  rw [thetaC_apply, IsScalarTower.algebraMap_apply (Ainf p O) (AinfInv p O), theta_algebraMap,
    AinfInv.theta_algebraMap, IsUnitBall.awayEquiv_algebraMap]

theorem ker_thetaC : RingHom.ker (thetaC p O) = RingHom.ker (theta p O) := by
  ext x
  rw [RingHom.mem_ker, RingHom.mem_ker, thetaC_apply,
    map_eq_zero_iff _ (IsUnitBall.awayEquiv O p).injective]

variable [IsAlgClosed C]

section General

variable {F : Type v} {L : Type w} [Field F] [Field L] [Algebra F L] [CharZero F]
  [Algebra.IsAlgebraic F L]

end General

end BdRPlus

section Padic

variable [NormedAlgebra ℚ_[p] C]



variable [IsAlgClosed C] {L : Type w} [Field L] [Algebra ℚ_[p] L] [Algebra.IsAlgebraic ℚ_[p] L]

variable {p O}

end Padic

section Witt

variable [IsAlgClosed C] {k : Type v} [Field k] [CharP k p] [PerfectRing k p]
variable {L : Type w} [Field L] [Algebra (FractionRing (WittVector p k)) L]
  [Algebra.IsAlgebraic (FractionRing (WittVector p k)) L]

omit [CompleteSpace C] [CharZero C] [Fact (‖(p : C)‖ < 1)] [IsUnitBall O] [IsAlgClosed C] in
theorem charZero_wittVector : CharZero (WittVector p k) := by
  refine ⟨fun m n h => ?_⟩
  have hinj : Function.Injective ((WittVector.map (ZMod.castHom (dvd_refl p) k)).comp
      (WittVector.equiv p).symm.toRingHom) :=
    (WittVector.map_injective _ (RingHom.injective _)).comp (WittVector.equiv p).symm.injective
  exact Nat.cast_injective (R := ℤ_[p]) (hinj (by rw [map_natCast, map_natCast, h]))

instance : CharZero (FractionRing (WittVector p k)) :=
  haveI := charZero_wittVector p (k := k)
  inferInstance

variable {p O}

end Witt

end Reformulated.AutPerF
end
end
