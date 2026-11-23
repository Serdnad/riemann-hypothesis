module

public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Data.Matrix.PEquiv
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Valuation.Integers
public import ReciprocityTheory.DualLattices.Bundle002
public import ReciprocityTheory.DualLattices.Bundle010
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
public import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.DualLattices.UpSmith
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.DualLattices.DvdOfCoeffZero
public import ReciprocityTheory.DualLattices.Bundle003
public import ReciprocityTheory.DualLattices.Bundle006
public import ReciprocityTheory.DualLattices.MemDualLat
public import ReciprocityTheory.DualLattices.ValUntiltESubOne
public import ReciprocityTheory.DualLattices.Bundle011
public import ReciprocityTheory.DualLattices.Bundle005
public import ReciprocityTheory.DualLattices.Bundle001

@[expose] public section

section

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up.Smith

section general

variable {R : Type} [CommRing R]

def Vm {N : ℕ} (j0 : Fin (N + 1)) (s : Fin (N + 1) → R) : Matrix (Fin (N + 1)) (Fin (N + 1)) R :=
  Matrix.of fun k l =>
    if l = j0 then (if k = j0 then 1 else 0) else ((if k = l then 1 else 0) - (if k = j0 then s l else 0))

theorem det_Vm {N : ℕ} (j0 : Fin (N + 1)) (s : Fin (N + 1) → R) : (Vm j0 s).det = 1 := by
  rw [Matrix.det_succ_column (Vm j0 s) j0, Finset.sum_eq_single j0]
  · have hsub : (Vm j0 s).submatrix j0.succAbove j0.succAbove = 1 := by
      ext k l
      simp only [Matrix.submatrix_apply, Vm, Matrix.of_apply, Fin.succAbove_ne, ite_false,
        sub_zero, Matrix.one_apply, (Fin.succAbove_right_injective).eq_iff]
    rw [hsub, Matrix.det_one]
    simp [Vm, ← two_mul, pow_mul]
  · intro k _ hk
    simp [Vm, hk]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem mul_Vm {m N : ℕ} (X : Matrix (Fin m) (Fin (N + 1)) R) (j0 : Fin (N + 1))
    (s : Fin (N + 1) → R) (i : Fin m) (l : Fin (N + 1)) :
    (X * Vm j0 s) i l = if l = j0 then X i j0 else X i l - s l * X i j0 := by
  classical
  simp only [Matrix.mul_apply, Vm, Matrix.of_apply]
  by_cases hl : l = j0
  · simp [hl]
  · simp only [hl, ite_false, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring

theorem VmT_mul {N n : ℕ} (j0 : Fin (N + 1)) (u : Fin (N + 1) → R) (Y : Matrix (Fin (N + 1)) (Fin n) R)
    (k : Fin (N + 1)) (l : Fin n) :
    ((Vm j0 u)ᵀ * Y) k l = if k = j0 then Y j0 l else Y k l - u k * Y j0 l := by
  classical
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Vm, Matrix.of_apply]
  by_cases hk : k = j0
  · simp [hk]
  · simp only [hk, ite_false, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul]
    simp [Finset.sum_ite_eq']

def piv {N : ℕ} (i0 : Fin (N + 1)) : Equiv.Perm (Fin (N + 1)) :=
  (finSuccEquiv N).trans (finSuccEquiv' i0).symm

theorem piv_zero {N : ℕ} (i0 : Fin (N + 1)) : piv i0 0 = i0 := by
  simp [piv, finSuccEquiv_zero]

theorem piv_succ {N : ℕ} (i0 : Fin (N + 1)) (l : Fin N) : piv i0 l.succ = i0.succAbove l := by
  simp [piv, finSuccEquiv_succ]

def bd1 {N M : ℕ} (P : Matrix (Fin N) (Fin M) R) : Matrix (Fin (N + 1)) (Fin (M + 1)) R :=
  Matrix.of fun i j => Fin.cases (Fin.cases 1 (fun _ => 0) j) (fun l => Fin.cases 0 (fun k => P l k) j) i

@[simp] theorem blockOne_zero_zero_alt {N M : ℕ} (P : Matrix (Fin N) (Fin M) R) : bd1 P 0 0 = 1 := rfl
@[simp] theorem blockOne_zero_succ_alt {N M : ℕ} (P : Matrix (Fin N) (Fin M) R) (k : Fin M) :
    bd1 P 0 k.succ = 0 := rfl
@[simp] theorem blockOne_succ_succ_alt {N M : ℕ} (P : Matrix (Fin N) (Fin M) R) (l : Fin N) (k : Fin M) :
    bd1 P l.succ k.succ = P l k := rfl

theorem det_blockOne_alt {N : ℕ} (P : Matrix (Fin N) (Fin N) R) : (bd1 P).det = P.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [blockOne_zero_zero_alt, blockOne_zero_succ_alt, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, mul_one,
    Fin.val_zero, pow_zero, one_mul]
  congr 1

theorem blockOne_mul_mul_blockOne {d n : ℕ} (P : Matrix (Fin d) (Fin d) R) (Cm : Matrix (Fin (d + 1)) (Fin (n + 1)) R)
    (Q : Matrix (Fin n) (Fin n) R) (h0 : ∀ k : Fin n, Cm 0 k.succ = 0)
    (h1 : ∀ l : Fin d, Cm l.succ 0 = 0) :
    (bd1 P * Cm * bd1 Q) 0 0 = Cm 0 0 ∧ (∀ k : Fin n, (bd1 P * Cm * bd1 Q) 0 k.succ = 0) ∧
      (∀ l : Fin d, (bd1 P * Cm * bd1 Q) l.succ 0 = 0) ∧
      ∀ (l : Fin d) (k : Fin n), (bd1 P * Cm * bd1 Q) l.succ k.succ =
        (P * (Matrix.of fun (l : Fin d) (k : Fin n) => Cm l.succ k.succ) * Q) l k := by
  have bd1_succ_zero {N M : ℕ} (X : Matrix (Fin N) (Fin M) R) (l : Fin N) :
      bd1 X l.succ 0 = 0 := rfl
  have hPC0 : ∀ j : Fin (n + 1), (bd1 P * Cm) 0 j = Cm 0 j := by
    intro j; simp [Matrix.mul_apply, Fin.sum_univ_succ]
  have hPCs : ∀ (l : Fin d) (j : Fin (n + 1)), (bd1 P * Cm) l.succ j = ∑ m, P l m * Cm m.succ j := by
    intro l j; simp [Matrix.mul_apply, Fin.sum_univ_succ, bd1_succ_zero]
  refine ⟨?_, fun k => ?_, fun l => ?_, fun l k => ?_⟩
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, hPC0, h0]
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, hPC0, h0]
  · rw [Matrix.mul_apply, Fin.sum_univ_succ]
    simp [hPCs, h1, bd1_succ_zero]
  · rw [Matrix.mul_apply, Fin.sum_univ_succ]
    simp only [hPCs, blockOne_zero_succ_alt, mul_zero, zero_add, blockOne_succ_succ_alt, Matrix.mul_apply, Matrix.of_apply]

theorem isUnit_det_perm {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    IsUnit (σ.toPEquiv.toMatrix : Matrix (Fin N) (Fin N) R).det := by
  have h := Matrix.det_permutation (R := R) σ
  simp only [Equiv.Perm.permMatrix] at h
  rw [h]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]

end general

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

theorem smith_mat (hv : v.Integers R) : ∀ (d n : ℕ) (A : Matrix (Fin d) (Fin n) R),
    ∃ (P : Matrix (Fin d) (Fin d) R) (Q : Matrix (Fin n) (Fin n) R) (a : Fin d → R),
      IsUnit P.det ∧ IsUnit Q.det ∧ ∀ j k, (P * A * Q) j k = if (k : ℕ) = (j : ℕ) then a j else 0 := by
  intro d
  induction d with
  | zero =>
    intro n A
    exact ⟨1, 1, Fin.elim0, by simp, by simp, fun j => j.elim0⟩
  | succ d ih =>
    intro n A
    cases n with
    | zero =>
      exact ⟨1, 1, 0, by simp, by simp, fun j k => k.elim0⟩
    | succ n =>
      classical
      set g : Fin (n + 1) → Fin (d + 1) → R := fun j i => A i j with hg
      have hp := exists_pivot (v := v) (b := d) (ι := Fin (n + 1)) hv g
      obtain ⟨i0, a, u, s, hu, -, hs, hz, hnz⟩ := hp
      by_cases ha : a = 0
      · have hA : A = 0 := by
          ext i j
          have := congrFun (hz ha j) i
          simpa [hg] using this
        exact ⟨1, 1, 0, by simp, by simp, fun j k => by simp [hA]⟩
      · obtain ⟨j0, hj0, hs0⟩ := hnz ha
        have hAj0 : ∀ i, A i j0 = a * u i := fun i => by
          have := congrFun hj0 i
          simpa [hg] using this
        have hAi0 : ∀ l, A i0 l = a * s l := fun l => by
          have := hs l
          simpa [hg] using this
        set B := (Vm i0 u)ᵀ * A * Vm j0 s with hBdef
        have hB : ∀ k l, B k l = if k = i0 then (if l = j0 then a else 0) else
            (if l = j0 then 0 else A k l - s l * (a * u k)) := by
          intro k l
          rw [hBdef, Matrix.mul_assoc, VmT_mul, mul_Vm, mul_Vm]
          by_cases hk : k = i0 <;> by_cases hl : l = j0
          · subst hk; subst hl; simp [hAj0, hu]
          · subst hk; simp [hl, hAi0, hs0]; ring
          · subst hl; simp [hk, hAj0, hu]; ring
          · simp [hk, hl, hAj0, hAi0, hu]; ring
        set A'' : Matrix (Fin d) (Fin n) R := Matrix.of fun l k => B (i0.succAbove l) (j0.succAbove k)
        obtain ⟨P'', Q'', a'', hP'', hQ'', hD''⟩ := ih n A''
        set Cm := B.submatrix (piv i0) (piv j0) with hCm
        have hCeq : ((piv i0).toPEquiv.toMatrix : Matrix (Fin (d + 1)) (Fin (d + 1)) R) * B * ((piv j0).symm.toPEquiv.toMatrix : Matrix (Fin (n + 1)) (Fin (n + 1)) R) = Cm := by
          rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_symm]
          rfl
        have h0 : ∀ k : Fin n, Cm 0 k.succ = 0 := by
          intro k
          simp only [hCm, Matrix.submatrix_apply, piv_zero, piv_succ, hB, ite_true,
            Fin.succAbove_ne, ite_false]
        have h1 : ∀ l : Fin d, Cm l.succ 0 = 0 := by
          intro l
          simp only [hCm, Matrix.submatrix_apply, piv_zero, piv_succ, hB, Fin.succAbove_ne, ite_false,
            ite_true]
        have hsub : (Matrix.of fun (l : Fin d) (k : Fin n) => Cm l.succ k.succ) = A'' := by
          ext l k
          simp only [hCm, Matrix.of_apply, Matrix.submatrix_apply, piv_succ]
          rfl
        obtain ⟨e00, e0s, es0, ess⟩ := blockOne_mul_mul_blockOne P'' Cm Q'' h0 h1
        refine ⟨bd1 P'' * ((piv i0).toPEquiv.toMatrix : Matrix (Fin (d + 1)) (Fin (d + 1)) R) * (Vm i0 u)ᵀ,
          Vm j0 s * ((piv j0).symm.toPEquiv.toMatrix : Matrix (Fin (n + 1)) (Fin (n + 1)) R) * bd1 Q'', Fin.cons a a'', ?_, ?_, ?_⟩
        · rw [Matrix.det_mul, Matrix.det_mul, det_blockOne_alt, Matrix.det_transpose, det_Vm, mul_one]
          exact hP''.mul (isUnit_det_perm _)
        · rw [Matrix.det_mul, Matrix.det_mul, det_blockOne_alt, det_Vm, one_mul]
          exact (isUnit_det_perm _).mul hQ''
        · have hfull : bd1 P'' * ((piv i0).toPEquiv.toMatrix : Matrix (Fin (d + 1)) (Fin (d + 1)) R) * (Vm i0 u)ᵀ * A *
              (Vm j0 s * ((piv j0).symm.toPEquiv.toMatrix : Matrix (Fin (n + 1)) (Fin (n + 1)) R) * bd1 Q'') = bd1 P'' * Cm * bd1 Q'' := by
            rw [← hCeq, hBdef]
            simp only [Matrix.mul_assoc]
          intro j k
          rw [hfull]
          refine Fin.cases ?_ (fun l => ?_) j <;> refine Fin.cases ?_ (fun k' => ?_) k
          · rw [e00]
            simp [hCm, piv_zero, hB]
          · rw [e0s]
            simp
          · rw [es0]
            simp
          · rw [ess, hsub, hD'']
            simp [Fin.val_succ]

end ReciprocityTheory.PGsh.Up.Smith
end
end

section

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up.PullbackHopfOrder

open ReciprocityTheory.PGsh.L2

section Hopf

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

def pullHopf {N X : Type} [AddCommGroup N] [Fintype N] [DecidableEq N] [AddCommGroup X]
    [Fintype X] [DecidableEq X] (ψ : X →+ N) (AA : HopfOrder (C := C) R N)
    (hlat : IsLat R (AA.carrier.map (LinearMap.funLeft R C ψ))) : HopfOrder (C := C) R X where
  carrier := AA.carrier.map (LinearMap.funLeft R C ψ)
  lat := hlat
  le_int := by
    rintro _ ⟨f, hf, rfl⟩ x
    exact AA.le_int hf (ψ x)
  one_mem := ⟨1, AA.one_mem, rfl⟩
  mul_mem := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, AA.mul_mem f g hf hg, rfl⟩
  comul := by
    rintro _ ⟨f, hf, rfl⟩
    rw [← SecondCohomologyLattice.map_tensorSpan (⇑ψ) AA.carrier]
    refine ⟨addPull R N f, AA.comul f hf, ?_⟩
    funext x
    simp [addPull, LinearMap.funLeft_apply, map_add (f := _)]
  antipode := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨fun x => f (-x), AA.antipode f hf, funext fun x => by simp [LinearMap.funLeft_apply]⟩

theorem pullHopf_carrier {N X : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    [AddCommGroup X] [Fintype X] [DecidableEq X] (ψ : X →+ N) (AA : HopfOrder (C := C) R N)
    (hlat : IsLat R (AA.carrier.map (LinearMap.funLeft R C ψ))) :
    (pullHopf ψ AA hlat).carrier = AA.carrier.map (LinearMap.funLeft R C ψ) := rfl

theorem isLat_map_equiv {X K : Type} [Fintype X] [DecidableEq X] {_ : Fintype K} {_ : DecidableEq K}
    (e : X ≃ K) {M : Submodule R (K → C)} (hM : IsLat R M) :
    IsLat R (M.map (LinearMap.funLeft R C e)) := by
  obtain ⟨B, hB, rfl⟩ := hM
  refine ⟨B.submatrix e e, by rwa [Matrix.det_submatrix_equiv_self], ?_⟩
  rw [Submodule.map_span, ← Set.range_comp]
  have h1 : (fun j x => (B.submatrix e e) x j) =
      (⇑(LinearMap.funLeft R C e) ∘ fun j x => B x j) ∘ e := by
    funext j x
    rfl
  rw [h1, e.surjective.range_comp]

theorem hopfLat {K : Type} {_ : AddCommGroup K} {_ : Fintype K} {_ : DecidableEq K}
    (A : HopfOrder (C := C) R K) : IsLat R A.carrier := A.lat

theorem isLat_pull (v : Valuation C NNReal) (hv : v.Integers R) {N X : Type} [AddCommGroup N]
    [Fintype N] [DecidableEq N] [AddCommGroup X] [Fintype X] [DecidableEq X]
    (ψ : X →+ N) (hψ : Function.Injective ψ) (AA : HopfOrder (C := C) R N) :
    IsLat R (AA.carrier.map (LinearMap.funLeft R C ψ)) := by
  classical
  obtain ⟨⟨AK, hAK⟩, -⟩ := h2 C R v hv N ψ.range AA
  let e := AddMonoidHom.ofInjective hψ
  have hmap : (AA.carrier.map (resK ψ.range)).map (LinearMap.funLeft R C e.toEquiv) =
      AA.carrier.map (LinearMap.funLeft R C ψ) := by
    rw [← Submodule.map_comp]
    congr 1
  rw [← hmap, ← hAK]
  exact isLat_map_equiv e.toEquiv (hopfLat AK)

end Hopf

section Split

variable {S : Type} [CommRing S] {n k : Type} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]

theorem exists_split (e : Matrix n n S) (he : e * e = e) (B : Matrix n k S)
    (hr : LinearMap.range B.mulVecLin = LinearMap.range e.mulVecLin)
    (hk : LinearMap.ker B.mulVecLin = ⊥) : ∃ L : Matrix k n S, L * B = 1 ∧ B * L = e := by
  have hcol : ∀ j : n, ∃ c : k → S, B *ᵥ c = e *ᵥ Pi.single j 1 := by
    intro j
    have hmem : e *ᵥ Pi.single j 1 ∈ LinearMap.range B.mulVecLin := by
      rw [hr]
      exact ⟨_, rfl⟩
    obtain ⟨c, hc⟩ := hmem
    exact ⟨c, hc⟩
  choose c hc using hcol
  let L : Matrix k n S := Matrix.of fun i j => c j i
  have hBL : B * L = e := by
    ext i j
    have h1 := congrFun (hc j) i
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at h1
    rw [← h1]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, L]
  have heB : e * B = B := by
    ext i j
    have hmem : B *ᵥ Pi.single j 1 ∈ LinearMap.range e.mulVecLin := by
      rw [← hr]
      exact ⟨_, rfl⟩
    obtain ⟨w, hw⟩ := hmem
    have h2 : e *ᵥ (B *ᵥ Pi.single j 1) = B *ᵥ Pi.single j 1 := by
      rw [← hw]
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, he]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h2
    simpa [Matrix.col_apply] using congrFun h2 i
  have hinj : Function.Injective B.mulVecLin := LinearMap.ker_eq_bot.1 hk
  refine ⟨L, ?_, hBL⟩
  ext i j
  have h3 : B *ᵥ ((L * B) *ᵥ Pi.single j 1) = B *ᵥ Pi.single j 1 := by
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hBL, heB]
  have h4 : (L * B) *ᵥ Pi.single j 1 = Pi.single j 1 := hinj h3
  rw [Matrix.mulVec_single_one] at h4
  have h5 := congrFun h4 i
  simp only [Matrix.col_apply] at h5
  rw [h5, Matrix.one_apply, Pi.single_apply]

end Split

end ReciprocityTheory.PGsh.Up.PullbackHopfOrder
end
end

section

namespace ReciprocityTheory.PGsh

theorem a0 (p : ℕ) [Fact p.Prime] : TiltStructureStatement p := by
  intro C _ _ _ v O _ _ hv _ _
  have hK : KerThetaStatement p O := kerTheta (p := p) (C := C) (v := v) (O := O) hv
  have hO : ∀ x : O, (p : O) * x = 0 → x = 0 := by
    intro x hx
    have hp0 : (p : C) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)
    have h1 := congrArg (algebraMap O C) hx
    rw [map_mul, map_natCast, map_zero] at h1
    apply hv.hom_inj
    rw [map_zero]
    exact (mul_eq_zero.mp h1).resolve_left hp0
  obtain ⟨pf, hpf⟩ := exists_pflat (p := p) (hv := hv)
  exact ⟨⟨pf, hpf⟩, exists_eps (p := p) (hv := hv), hK,
    xiNu p C v O hK, regular (p := p) (O := O) (hO := hO), flatW' (p := p) (O := O)⟩

end ReciprocityTheory.PGsh
end

section

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

private lemma stdJ_form' {D : Type} [CommRing D] {g : ℕ}
    (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) D) (i j : Fin g ⊕ Fin g) :
    (Mᵀ * stdJ D g * M) i j =
      ∑ a, (M (Sum.inr a) i * M (Sum.inl a) j - M (Sum.inl a) i * M (Sum.inr a) j) := by
  simp [stdJ, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Finset.sum_sub_distrib,
    sub_eq_add_neg, add_comm]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  ring

private lemma stdJ_eq (D : Type) [CommRing D] (g : ℕ) :
    stdJ D g = fromBlocks 1 (-1) 0 1 * fromBlocks 1 0 1 1 * fromBlocks 1 (-1) 0 1 := by
  rw [stdJ]
  simp [Matrix.fromBlocks_multiply]

private lemma det_stdJ (D : Type) [CommRing D] (g : ℕ) : (stdJ D g).det = 1 := by
  rw [stdJ_eq, Matrix.det_mul, Matrix.det_mul]
  simp [Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂]

theorem u1 : IsotypicAveragingStatement := by
  intro S _ g m Ht Bt E cp εT εL π hπ hT hT1 hL hL1 hHt hE hBH
  intro Bt'
  have hBt' : Bt' = ∑ i, εL i * Bt * εT i := rfl
  have hLt : ∀ i, (εL i)ᵀ * Ht = Ht * εT (π i) := by
    intro i
    have h := hHt (π i)
    rw [hπ] at h
    exact h.symm
  have hHtL : ∀ i, Htᵀ * εL i = (εT (π i))ᵀ * Htᵀ := by
    intro i
    have h := congrArg Matrix.transpose (hLt i)
    simpa [Matrix.transpose_mul] using h
  have part2 : ∀ i, Bt' * εT i = εL i * Bt' := by
    intro i
    have l : ∀ j, εL j * Bt * εT j * εT i = if j = i then εL j * Bt * εT j else 0 := by
      intro j
      rw [Matrix.mul_assoc (εL j * Bt), hT j i]
      split_ifs with h
      · subst h; rfl
      · simp
    have r : ∀ j, εL i * (εL j * Bt * εT j) = if j = i then εL j * Bt * εT j else 0 := by
      intro j
      by_cases h : j = i
      · subst h
        rw [if_pos rfl, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hL, if_pos rfl]
      · rw [if_neg h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hL, if_neg (Ne.symm h),
          Matrix.zero_mul, Matrix.zero_mul]
    rw [hBt', Matrix.sum_mul, Matrix.mul_sum]
    simp only [l, r]
  have hA : Bt'ᵀ * Ht = ∑ i, (εT i)ᵀ * Btᵀ * Ht * εT (π i) := by
    rw [hBt', Matrix.transpose_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.transpose_mul, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
    rw [hLt i]
  have hB : Htᵀ * Bt' = ∑ i, (εT i)ᵀ * Htᵀ * Bt * εT (π i) := by
    rw [hBt', Matrix.mul_sum, ← Equiv.sum_comp π (fun i => Htᵀ * (εL i * Bt * εT i))]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [← Matrix.mul_assoc]
    rw [hHtL (π i), hπ]
  have part1 : Bt'ᵀ * Ht - Htᵀ * Bt' = cp • E := by
    rw [hA, hB, ← Finset.sum_sub_distrib]
    have h : ∀ i, (εT i)ᵀ * Btᵀ * Ht * εT (π i) - (εT i)ᵀ * Htᵀ * Bt * εT (π i) =
        cp • (E * εT (π i)) := by
      intro i
      rw [Matrix.mul_assoc ((εT i)ᵀ) Btᵀ Ht, Matrix.mul_assoc ((εT i)ᵀ) Htᵀ Bt, ← Matrix.sub_mul,
        ← Matrix.mul_sub, hBH, Matrix.mul_smul, hE i, Matrix.smul_mul, Matrix.mul_assoc, hT,
        if_pos rfl]
    simp only [h]
    rw [← Finset.smul_sum, ← Matrix.mul_sum, Equiv.sum_comp π εT, hT1, Matrix.mul_one]
  have hJ : (Matrix.fromRows Ht Bt')ᵀ * stdJ S g * Matrix.fromRows Ht Bt' = cp • E := by
    rw [← part1]
    ext i j
    rw [stdJ_form']
    simp [Matrix.sub_apply, Matrix.mul_apply, Finset.sum_sub_distrib]
  refine ⟨part1, part2, ?_⟩
  rw [det_sq_eq E _ cp hJ, det_stdJ, mul_one]

end ReciprocityTheory.PGsh.Up
end
end
