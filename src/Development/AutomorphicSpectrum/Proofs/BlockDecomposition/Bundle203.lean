module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle005
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle006
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle197
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle199
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle026

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

noncomputable section

namespace GlobalTheory.CompanionTheory.KunGlue.ShiftCoh

variable {K : Type} [Field K]

def ev (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) : (Sh ς k C).X n ≃ₗ[K] C.X m where
  toFun y := y ⟨m, h⟩
  invFun x := fun m' => (show m = m'.1 by have := m'.2; omega) ▸ x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv y := by
    funext ⟨m', h'⟩
    obtain rfl : m' = m := by omega
    rfl
  right_inv _ := rfl

theorem ev_apply (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) (y : (Sh ς k C).X n) :
    ev ς k C h y = y ⟨m, h⟩ := rfl

theorem d_apply_succ (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) (y : (Sh ς k C).X n) (h' : m + 1 + k = n + 1) :
    (Sh ς k C).d n y ⟨m + 1, h'⟩ = (ς : ℤ) • C.d m (y ⟨m, h⟩) := rfl

theorem d_apply_zero (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {n : ℕ} (y : (Sh ς k C).X n) (h' : 0 + k = n + 1) :
    (Sh ς k C).d n y ⟨0, h'⟩ = 0 := rfl

theorem unit_smul_eq_zero (ς : ℤˣ) {M : Type*} [AddCommGroup M] {x : M} : (ς : ℤ) • x = 0 ↔ x = 0 := by
  rcases Int.units_eq_one_or ς with rfl | rfl <;> simp

theorem unit_smul_smul (ς : ℤˣ) {M : Type*} [AddCommGroup M] (x : M) : (ς : ℤ) • (ς : ℤ) • x = x := by
  rcases Int.units_eq_one_or ς with rfl | rfl <;> simp

theorem ext_at (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) {y z : (Sh ς k C).X n}
    (e : y ⟨m, h⟩ = z ⟨m, h⟩) : y = z :=
  (ev ς k C h).injective e

theorem mem_Z_iff (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) (y : (Sh ς k C).X n) :
    (Sh ς k C).d n y = 0 ↔ C.d m (y ⟨m, h⟩) = 0 := by
  have h' : m + 1 + k = n + 1 := by omega
  constructor
  · intro e
    have := congrFun e ⟨m + 1, h'⟩
    rw [d_apply_succ ς k C h y h'] at this
    exact (unit_smul_eq_zero ς).1 this
  · intro e
    refine ext_at ς k C h' ?_
    rw [d_apply_succ ς k C h y h', e, smul_zero]
    rfl

theorem mem_B_iff (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) (y : (Sh ς k C).X n) :
    y ∈ (Sh ς k C).B n ↔ y ⟨m, h⟩ ∈ C.B m := by
  cases n with
  | zero =>
    obtain rfl : m = 0 := by omega
    constructor
    · intro e
      have e' : y = 0 := e
      rw [e']
      exact Submodule.zero_mem _
    · intro e
      have e' : y ⟨0, h⟩ = 0 := e
      have : y = 0 := ext_at ς k C h e'
      rw [this]
      exact Submodule.zero_mem _
  | succ n =>
    cases m with
    | zero =>
      constructor
      · rintro ⟨x, rfl⟩
        rw [d_apply_zero ς k C x h]
        exact Submodule.zero_mem _
      · intro e
        have e' : y ⟨0, h⟩ = 0 := e
        have : y = 0 := ext_at ς k C h e'
        rw [this]
        exact Submodule.zero_mem _
    | succ m =>
      have h0 : m + k = n := by omega
      constructor
      · rintro ⟨x, rfl⟩
        rw [d_apply_succ ς k C h0 x h]
        exact ⟨(ς : ℤ) • x ⟨m, h0⟩, by rw [map_zsmul]⟩
      · rintro ⟨z, hz⟩
        refine ⟨(ev ς k C h0).symm ((ς : ℤ) • z), ext_at ς k C h ?_⟩
        rw [d_apply_succ ς k C h0 _ h]
        change (ς : ℤ) • C.d m ((ev ς k C h0) ((ev ς k C h0).symm ((ς : ℤ) • z))) = _
        rw [LinearEquiv.apply_symm_apply, map_zsmul, unit_smul_smul, hz]

def evZ (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) : C.Z m ≃ₗ[K] (Sh ς k C).Z n :=
  LinearEquiv.ofSubmodules (ev ς k C h).symm (C.Z m) ((Sh ς k C).Z n) (by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine (mem_Z_iff ς k C h _).2 ?_
      change C.d m ((ev ς k C h) ((ev ς k C h).symm x)) = 0
      rw [LinearEquiv.apply_symm_apply]
      exact hx
    · intro hy
      exact ⟨ev ς k C h y, (mem_Z_iff ς k C h y).1 hy, (ev ς k C h).symm_apply_apply y⟩)

theorem evZ_coe (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) (x : C.Z m) :
    ev ς k C h (evZ ς k C h x).1 = x.1 :=
  (ev ς k C h).apply_symm_apply x.1

def evH (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) : C.H m ≃ₗ[K] (Sh ς k C).H n :=
  Submodule.Quotient.equiv _ _ (evZ ς k C h) (by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : x.1 ∈ C.B m := hx
      change (evZ ς k C h x).1 ∈ (Sh ς k C).B n
      refine (mem_B_iff ς k C h _).2 ?_
      have := evZ_coe ς k C h x
      rw [ev_apply] at this
      rw [this]
      exact hx'
    · intro hy
      have hy' : y.1 ∈ (Sh ς k C).B n := hy
      refine ⟨(evZ ς k C h).symm y, ?_, (evZ ς k C h).apply_symm_apply y⟩
      change ((evZ ς k C h).symm y).1 ∈ C.B m
      have := evZ_coe ς k C h ((evZ ς k C h).symm y)
      rw [LinearEquiv.apply_symm_apply, ev_apply] at this
      rw [← this]
      exact (mem_B_iff ς k C h _).1 hy')

theorem main : ∀ {K : Type} [Field K] (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) (n : ℕ), (n < k → Subsingleton ((Sh ς k C).H n)) ∧ ∀ (m : ℕ) (h : m + k = n), ∃ e : C.H m ≃ₗ[K] (Sh ς k C).H n, ∀ (y : (Sh ς k C).X n) (hy : (Sh ς k C).d n y = 0) (hy' : C.d m (y ⟨m, h⟩) = 0), e (C.cls (y ⟨m, h⟩) hy') = (Sh ς k C).cls y hy := by
  intro K _ ς k C n
  refine ⟨fun hn => ?_, fun m h => ⟨evH ς k C h, fun y hy hy' => ?_⟩⟩
  · have : IsEmpty {m : ℕ // m + k = n} := ⟨fun x => by have := x.2; omega⟩
    have hX : Subsingleton ((Sh ς k C).X n) :=
      inferInstanceAs (Subsingleton (∀ m : {m : ℕ // m + k = n}, C.X m.1))
    have hZ : Subsingleton ((Sh ς k C).Z n) := ⟨fun a b => Subtype.ext (hX.elim _ _)⟩
    exact Quotient.instSubsingletonQuotient _
  · refine congrArg (Submodule.Quotient.mk (p := ((Sh ς k C).B n).submoduleOf ((Sh ς k C).Z n))) (Subtype.ext ?_)
    exact (ev ς k C h).symm_apply_apply y

end GlobalTheory.CompanionTheory.KunGlue.ShiftCoh
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

noncomputable section

namespace GlobalTheory.CompanionTheory.KunGlue.DsumCoh

variable {K : Type} [Field K] {I : Type 1} [DecidableEq I] (E : I → Cx.{1} K)

def inj (i : I) : Cx.Hom (E i) (Dsum E) (RingHom.id K) where
  f n := DirectSum.lof K I (fun i => (E i).X n) i
  comm n x := by
    change DirectSum.lmap (fun i => (E i).d n) (DirectSum.lof K I (fun i => (E i).X n) i x) = _
    rw [DirectSum.lmap_lof]
    rfl

def prj (i : I) : Cx.Hom (Dsum E) (E i) (RingHom.id K) where
  f n := DirectSum.component K I (fun i => (E i).X n) i
  comm n x := by
    change (E i).d n (DirectSum.component K I (fun i => (E i).X n) i x) =
      DirectSum.component K I (fun i => (E i).X (n + 1)) i (DirectSum.lmap (fun i => (E i).d n) x)
    induction x using DirectSum.induction_on with
    | zero => simp
    | of j y =>
      rw [← DirectSum.lof_eq_of K, DirectSum.lmap_lof]
      by_cases h : j = i
      · subst h
        simp only [DirectSum.component.lof_self]
      · rw [DirectSum.component.of, DirectSum.component.of, dite_eq_right h, dite_eq_right h, map_zero]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]

def toH (n : ℕ) : (⨁ i, (E i).H n) →ₗ[K] (Dsum E).H n :=
  DirectSum.toModule K I _ fun i => (inj E i).mapH n

theorem prj_toH (n : ℕ) (i : I) (y : ⨁ i, (E i).H n) :
    (prj E i).mapH n (toH E n y) = DirectSum.component K I (fun i => (E i).H n) i y := by
  have hcl : ∀ (x y : (E i).X n) (hx : (E i).d n x = 0) (hy : (E i).d n y = 0), x = y →
      (E i).cls x hx = (E i).cls y hy := by
    rintro x _ _ _ rfl
    rfl
  induction y using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of j z =>
    obtain ⟨a, ha, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj z
    have h1 : (Dsum E).d n ((inj E j).f n a) = 0 := CrystallineSemistableComparison.CechClassBoundaries.cyc (inj E j) a ha
    rw [← DirectSum.lof_eq_of K, toH, DirectSum.toModule_lof, CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' (inj E j) a ha h1,
      CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' (prj E i) _ h1 (CrystallineSemistableComparison.CechClassBoundaries.cyc (prj E i) _ h1)]
    by_cases hji : j = i
    · subst hji
      rw [DirectSum.component.lof_self]
      exact hcl _ _ _ _ (DirectSum.component.lof_self K _ _)
    · rw [DirectSum.component.of, dite_eq_right hji]
      rw [← CrystallineSemistableComparison.CechClassBoundaries.cls_zero' (K := E i) (n := n) (map_zero _)]
      refine hcl _ _ _ _ ?_
      show DirectSum.component K I (fun i ↦ (E i).X n) i (DirectSum.lof K I (fun i ↦ (E i).X n) j a) = 0
      rw [DirectSum.component.of, dite_eq_right hji]
  | add y₁ y₂ h₁ h₂ => simp only [map_add (f := _), h₁, h₂]

theorem toH_injective (n : ℕ) : Function.Injective (toH E n) := by
  refine (injective_iff_map_eq_zero (toH E n)).2 fun y hy ↦ ?_
  refine DirectSum.ext fun i ↦ ?_
  have h := prj_toH E n i y
  rw [hy, map_zero] at h
  rw [DirectSum.apply_eq_component K, ← h]
  rfl

theorem toH_surjective (n : ℕ) : Function.Surjective (toH E n) := by
  classical
  intro z
  obtain ⟨x, hx, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj z
  have hc : ∀ i, (E i).d n ((prj E i).f n x) = 0 := fun i ↦ CrystallineSemistableComparison.CechClassBoundaries.cyc (prj E i) x hx
  have hci : ∀ i, (Dsum E).d n ((inj E i).f n ((prj E i).f n x)) = 0 := fun i ↦ CrystallineSemistableComparison.CechClassBoundaries.cyc (inj E i) _ (hc i)
  have hsum : ∀ S : Finset I, ∀ h : (Dsum E).d n (∑ i ∈ S, (inj E i).f n ((prj E i).f n x)) = 0,
      (Dsum E).cls (∑ i ∈ S, (inj E i).f n ((prj E i).f n x)) h =
        ∑ i ∈ S, (Dsum E).cls ((inj E i).f n ((prj E i).f n x)) (hci i) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro h
      simp only [Finset.sum_empty]
      exact CrystallineSemistableComparison.CechClassBoundaries.cls_zero' h
    | insert j S hj ih =>
      intro h
      have hS : (Dsum E).d n (∑ i ∈ S, (inj E i).f n ((prj E i).f n x)) = 0 := by

        rw [map_sum]
        exact Finset.sum_eq_zero fun i _ ↦ hci i
      simp only [Finset.sum_insert hj]
      rw [CrystallineSemistableComparison.CechClassBoundaries.cls_add _ _ (hci j) hS, ih hS]
  have hx_eq : ∑ i ∈ DFinsupp.support x, (inj E i).f n ((prj E i).f n x) = x := by
    conv_rhs => rw [← DirectSum.sum_support_of x]
    rfl
  refine ⟨∑ i ∈ DFinsupp.support x, DirectSum.lof K I (fun i ↦ (E i).H n) i ((E i).cls _ (hc i)), ?_⟩

  rw [map_sum]
  simp only [toH, DirectSum.toModule_lof]
  have hx' : (Dsum E).d n (∑ i ∈ DFinsupp.support x, (inj E i).f n ((prj E i).f n x)) = 0 := by
    rw [hx_eq]
    exact hx
  rw [Finset.sum_congr rfl fun i _ ↦ CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' (inj E i) _ (hc i) (hci i), ← hsum _ hx']
  exact (CrystallineSemistableComparison.CechClassBoundaries.cls_eq _ _ _ _).2 (by rw [hx_eq, sub_self]; exact zero_mem _)

end GlobalTheory.CompanionTheory.KunGlue.DsumCoh

theorem GlobalTheory.CompanionTheory.KunGlue.dsum_coh : ∀ {K : Type} [Field K] {I : Type 1} [DecidableEq I] (E : I → Cx.{1} K) (n : ℕ),
    ∃ e : (⨁ i, (E i).H n) ≃ₗ[K] (Dsum E).H n, ∀ (i : I) (x : (E i).X n) (hx : (E i).d n x = 0)
      (hx' : (Dsum E).d n (DirectSum.lof K I (fun i => (E i).X n) i x) = 0),
      e (DirectSum.lof K I (fun i => (E i).H n) i ((E i).cls x hx)) =
        (Dsum E).cls (DirectSum.lof K I (fun i => (E i).X n) i x) hx' := by
  intro K _ I _ E n
  refine ⟨LinearEquiv.ofBijective (DsumCoh.toH E n) ⟨DsumCoh.toH_injective E n, DsumCoh.toH_surjective E n⟩,
    fun i x hx hx' ↦ ?_⟩
  rw [LinearEquiv.ofBijective_apply, DsumCoh.toH, DirectSum.toModule_lof]
  exact CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' (DsumCoh.inj E i) x hx hx'
end
end

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

noncomputable section

namespace GlobalTheory.CompanionTheory.FilMul

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

theorem divided_power_xi_zero : A.dxi0 0 = 1 := Subtype.ext (by simp [PAlg.dxi0, dpw])

theorem factorial_mul_dpw (k : ℕ) :
    (k.factorial : WL l A.A) * dpw k A.xi = algebraMap A.W (WL l A.A) A.xi ^ k := by
  rw [dpw, ← mul_assoc, Ring.mul_inverse_cancel _ (A.isUnit_natCast k.factorial_ne_zero), one_mul]

theorem factorial_mul_divided_power_xi (k : ℕ) :
    (k.factorial : A.Acr0) * A.dxi0 k = algebraMap A.W A.Acr0 A.xi ^ k :=
  Subtype.ext (by
    have h := factorial_mul_dpw A k
    simpa [PAlg.dxi0] using h)

theorem divided_power_xi_mul (i j : ℕ) :
    A.dxi0 i * A.dxi0 j = ((i + j).choose i : A.Acr0) * A.dxi0 (i + j) := by
  apply Subtype.ext
  show dpw i A.xi * dpw j A.xi = (((i + j).choose i : ℕ) : WL l A.A) * dpw (i + j) A.xi
  have hi := A.isUnit_natCast i.factorial_ne_zero
  have hj := A.isUnit_natCast j.factorial_ne_zero
  have h : (((i + j).choose i : ℕ) : WL l A.A) * (i.factorial : WL l A.A) * (j.factorial : WL l A.A)
      = ((i + j).factorial : WL l A.A) := by
    rw [Nat.choose_symm_add, ← Nat.cast_mul, ← Nat.cast_mul,
      Nat.add_choose_mul_factorial_mul_factorial i j]
  apply hj.mul_left_cancel
  apply hi.mul_left_cancel
  calc (i.factorial : WL l A.A) * ((j.factorial : WL l A.A) * (dpw i A.xi * dpw j A.xi))
      = ((i.factorial : WL l A.A) * dpw i A.xi) * ((j.factorial : WL l A.A) * dpw j A.xi) := by ring
    _ = ((i + j).factorial : WL l A.A) * dpw (i + j) A.xi := by
        rw [factorial_mul_dpw, factorial_mul_dpw, factorial_mul_dpw, pow_add]
    _ = (i.factorial : WL l A.A) * ((j.factorial : WL l A.A)
          * ((((i + j).choose i : ℕ) : WL l A.A) * dpw (i + j) A.xi)) := by
        rw [← h]; ring

theorem Fil0_zero : A.Fil0 0 = ⊤ :=
  (Ideal.eq_top_iff_one _).2 (Ideal.subset_span ⟨0, le_rfl, (divided_power_xi_zero A).symm⟩)

theorem Fil0_mul_le (r s : ℕ) : A.Fil0 r * A.Fil0 s ≤ A.Fil0 (r + s) := by
  unfold PAlg.Fil0
  rw [Ideal.span_mul_span', Ideal.span_le]
  rintro _ ⟨_, ⟨i, hi, rfl⟩, _, ⟨j, hj, rfl⟩, rfl⟩
  show A.dxi0 i * A.dxi0 j ∈ Ideal.span _
  rw [divided_power_xi_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i + j, by omega, rfl⟩)

theorem Fil_eq_map (n r : ℕ) : A.Fil n r = (A.Fil0 r).map (A.mkAcr n) := by
  unfold PAlg.Fil PAlg.Fil0
  rw [Ideal.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨_, ⟨k, hk, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, hk, rfl⟩

theorem PFil_eq_map (n : ℕ) : A.PFil n = A.PFil0.map (A.mkAcr n) := by
  rw [PAlg.PFil, PAlg.PFil0, Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_natCast,
    Fil_eq_map]

theorem Fil_zero (n : ℕ) : A.Fil n 0 = ⊤ := by
  rw [Fil_eq_map, Fil0_zero, Ideal.map_top]

theorem Fil_mul_le (n r s : ℕ) : A.Fil n r * A.Fil n s ≤ A.Fil n (r + s) := by
  rw [Fil_eq_map, Fil_eq_map, Fil_eq_map, ← Ideal.map_mul]
  exact Ideal.map_mono (Fil0_mul_le A r s)

theorem main : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), A.Fil0 0 = ⊤ ∧
    (∀ i j, A.dxi0 i * A.dxi0 j = ((i + j).choose i : A.Acr0) * A.dxi0 (i + j)) ∧
    (∀ k, (k.factorial : A.Acr0) * A.dxi0 k = algebraMap A.W A.Acr0 A.xi ^ k) ∧
    (∀ r s, A.Fil0 r * A.Fil0 s ≤ A.Fil0 (r + s)) ∧
    (∀ n r, A.Fil n r = (A.Fil0 r).map (A.mkAcr n)) ∧
    (∀ n, A.PFil n = A.PFil0.map (A.mkAcr n)) ∧
    (∀ n, A.Fil n 0 = ⊤) ∧ ∀ n r s, A.Fil n r * A.Fil n s ≤ A.Fil n (r + s) :=
  fun A => ⟨Fil0_zero A, divided_power_xi_mul A, factorial_mul_divided_power_xi A, Fil0_mul_le A, Fil_eq_map A,
    PFil_eq_map A, Fil_zero A, Fil_mul_le A⟩

end GlobalTheory.CompanionTheory.FilMul
end
end

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PAlgNat

variable {l : ℕ} [Fact l.Prime]

theorem mapAcris_acrisOfTilt {A B : PAlg l} (f : A ⟶ B) (a : A.A) :
    mapAcr f 1 (A.aTo1 a) = B.aTo1 (Hom.f f a) := by
  have h := A.aTo1_coeff (WittVector.teichmuller l a)
  rw [WittVector.teichmuller_coeff_zero] at h
  have h' := B.aTo1_coeff (WittVector.teichmuller l (Hom.f f a))
  rw [WittVector.teichmuller_coeff_zero] at h'
  rw [h, h', mapAcr_toAcr, mapW, WittVector.map_teichmuller]

theorem mapAcr_expand {A B : PAlg l} (f : A ⟶ B) (c : ℕ →₀ A.A) :
    mapAcr f 1 (A.expand c) = B.expand (c.mapRange (Hom.f f) (map_zero _)) := by
  rw [expand, expand, map_finsuppSum, Finsupp.sum_mapRange_index (fun k => by simp)]
  refine Finsupp.sum_congr fun k _ => ?_
  rw [map_mul, mapAcris_acrisOfTilt, mapAcr_dxi]

theorem mapU_sharp {A B : PAlg l} (f : A ⟶ B) (a : A.A) :
    mapU f (A.sharp a) = B.sharp (Hom.f f a) := by
  change mapU f (A.th (WittVector.teichmuller l a)) = B.th (WittVector.teichmuller l (Hom.f f a))
  rw [mapU_th, mapW, WittVector.map_teichmuller]

theorem mapUnits_unitsOfTilt {A B : PAlg l} (f : A ⟶ B) (a : A.A) :
    mapUn f 1 (A.aToU1 a) = B.aToU1 (Hom.f f a) := by
  rw [sharpMap_eq, sharpMap_eq, ← mapU_sharp]
  rfl

theorem mk_mapAcr_toAcr {A B : PAlg l} (f : A ⟶ B) (n : ℕ) (x : A.W) :
    Ideal.Quotient.mk (B.Fil n 1) (mapAcr f n (A.toAcr n x)) = B.uToQ n (mapU f (A.th x)) := by
  rw [mapAcr_toAcr, mapU_th, uToQ_th]

theorem algebraMap_eq_acrisOfTilt (A : PAlg l) (x : Ainf l) :
    algebraMap (Ainf l) (A.Acr 1) x = A.aTo1 (A.s (x.coeff 0)) := by
  have h := A.aTo1_coeff (A.sW x)
  have e : (A.sW x).coeff 0 = A.s (x.coeff 0) := WittVector.map_coeff _ _ _
  rw [e] at h
  rw [h]
  rfl

theorem expand_nat {l : ℕ} [Fact l.Prime] (A : PAlg l) (B : PAlg l) (f : A ⟶ B) :
    (∀ a, mapAcr f 1 (A.aTo1 a) = B.aTo1 (Hom.f f a)) ∧
    (∀ c : ℕ →₀ A.A, mapAcr f 1 (A.expand c) = B.expand (c.mapRange (Hom.f f) (map_zero _))) ∧
    (∀ a, mapU f (A.sharp a) = B.sharp (Hom.f f a)) ∧
    (∀ a, mapUn f 1 (A.aToU1 a) = B.aToU1 (Hom.f f a)) ∧
    (∀ n x, Ideal.Quotient.mk (B.Fil n 1) (mapAcr f n (A.toAcr n x)) = B.uToQ n (mapU f (A.th x))) ∧
    ∀ x : Ainf l, algebraMap (Ainf l) (A.Acr 1) x = A.aTo1 (A.s (x.coeff 0)) :=
  ⟨mapAcris_acrisOfTilt f, mapAcr_expand f, mapU_sharp f, mapUnits_unitsOfTilt f, mk_mapAcr_toAcr f, algebraMap_eq_acrisOfTilt A⟩

end GlobalTheory.CompanionTheory.PAlgNat
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeSite

theorem wU_le_KS : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (D : E.LineData X) {N m : ℕ}
    (i : X ⟶ PSpace K N) (y : Fin m → MvPolynomial (Fin (N + 1)) K) (s : ℕ), IsTautologicalLineAt D N i → wU q i y s ≤ KS q s (𝒱D D) := by
  intro K _ X q D N m i y s hO T hT
  obtain ⟨k, hQ, V, ⟨j, rfl⟩, hV⟩ := hT
  exact ⟨hQ, wch i j, GlobalTheory.T.chart_open_mem_cover_of_O1 D N i hO j, fun x hx => (hV hx).2⟩

end GlobalTheory.CompanionTheory.ConeSite
end

section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isPullO_comp_block_decomposition : ∀ (R : Type) [CommRing R] (X Y Z : Over (Sp R)) (f : X ⟶ Y) (g : Y ⟶ Z)
    (a : HO1 Z.hom) (b : HO1 Y.hom) (c : HO1 X.hom), IsPullO (wOver g) a b → IsPullO (wOver f) b c →
    IsPullO (wOver (f ≫ g)) a c := by
  first | exact @GlobalTheory.CompanionTheory.Axis.PullO.isPullO_wOver_comp | exact GlobalTheory.CompanionTheory.Axis.PullO.isPullO_wOver_comp | (intros; apply GlobalTheory.CompanionTheory.Axis.PullO.isPullO_wOver_comp <;> assumption)
end
