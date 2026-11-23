module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.MemIntegersOfMemIntAd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdBlocks
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.KExpCut
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DoubleCosetSingleUnfolding

@[expose] public section

section

noncomputable section

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.SlabNDensePf

open Formalism.L2.SG Formalism.L2.SG.PoincareInHH Formalism.L2.SG.Pf.Unip Formalism.L2.SG.Pf.UnipB

section Gen

variable {R : Type*} [CommRing R] (O : Subring R)

def cg_C {α β : Type*} (c : ℕ) (A : Matrix α β R) : Prop := ∀ i j, ∃ t ∈ O, A i j = (c : R) * t

def cg_D {α β : Type*} (m : ℕ) (A : Matrix α β R) : Prop := ∀ i j, (m : R) * A i j ∈ O

variable {O} {α β γ : Type*}

theorem cg_C_zero (c : ℕ) : cg_C O c (0 : Matrix α β R) := fun _ _ => ⟨0, zero_mem _, by simp⟩

theorem cg_C_add {c : ℕ} {A B : Matrix α β R} (hA : cg_C O c A) (hB : cg_C O c B) : cg_C O c (A + B) := by
  intro i j
  obtain ⟨s, hs, e1⟩ := hA i j
  obtain ⟨t, ht, e2⟩ := hB i j
  exact ⟨s + t, add_mem hs ht, by rw [Matrix.add_apply, e1, e2, mul_add]⟩

theorem cg_C_neg {c : ℕ} {A : Matrix α β R} (hA : cg_C O c A) : cg_C O c (-A) := by
  intro i j
  obtain ⟨s, hs, e1⟩ := hA i j
  exact ⟨-s, neg_mem hs, by rw [Matrix.neg_apply, e1, mul_neg]⟩

theorem cg_C_sub {c : ℕ} {A B : Matrix α β R} (hA : cg_C O c A) (hB : cg_C O c B) : cg_C O c (A - B) := by
  rw [sub_eq_add_neg]; exact cg_C_add hA (cg_C_neg hB)

theorem cg_C_sum {ι : Type*} {s : Finset ι} {c : ℕ} {A : ι → Matrix α β R} (h : ∀ k ∈ s, cg_C O c (A k)) :
    cg_C O c (∑ k ∈ s, A k) :=
  Finset.sum_induction _ (cg_C O c) (fun _ _ => cg_C_add) (cg_C_zero c) h

theorem cg_C_dvd {c k : ℕ} {A : Matrix α β R} (hA : cg_C O (c * k) A) : cg_C O c A := by
  intro i j
  obtain ⟨s, hs, e1⟩ := hA i j
  exact ⟨k * s, mul_mem (natCast_mem _ _) hs, by rw [e1]; push_cast; ring⟩

theorem cg_D_of_C {m k : ℕ} {A A' : Matrix α β R} (hA : cg_D O m A) (h : cg_C O k (A' - A)) :
    cg_D O m A' := by
  intro i j
  obtain ⟨s, hs, e1⟩ := h i j
  have e2 : A' i j = A i j + k * s := by rw [← e1, Matrix.sub_apply]; ring
  rw [e2, mul_add, ← mul_assoc]
  exact add_mem (hA i j) (mul_mem (mul_mem (natCast_mem _ m) (natCast_mem _ k)) hs)

theorem cg_D_mul_right {m : ℕ} (k : ℕ) {A : Matrix α β R} (hA : cg_D O m A) : cg_D O (m * k) A := by
  intro i j
  rw [Nat.cast_mul, mul_comm (m : R), mul_assoc]
  exact mul_mem (natCast_mem _ _) (hA i j)

theorem cg_D_mul_left {m : ℕ} (k : ℕ) {A : Matrix α β R} (hA : cg_D O m A) : cg_D O (k * m) A := by
  intro i j
  rw [Nat.cast_mul, mul_assoc]
  exact mul_mem (natCast_mem _ _) (hA i j)

theorem cg_C_mul_left [Fintype β] {m c : ℕ} {P : Matrix α β R} {A : Matrix β γ R} (hP : cg_D O m P)
    (hA : cg_C O (c * m) A) : cg_C O c (P * A) := by
  choose t ht e using hA
  intro i j
  refine ⟨∑ k, ((m : R) * P i k) * t k j, sum_mem fun k _ => mul_mem (hP i k) (ht k j), ?_⟩
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [e k j]; push_cast; ring

theorem cg_C_mul_right [Fintype β] {m c : ℕ} {A : Matrix α β R} {Q : Matrix β γ R}
    (hA : cg_C O (c * m) A) (hQ : cg_D O m Q) : cg_C O c (A * Q) := by
  choose t ht e using hA
  intro i j
  refine ⟨∑ k, t i k * ((m : R) * Q k j), sum_mem fun k _ => mul_mem (ht i k) (hQ k j), ?_⟩
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [e i k]; push_cast; ring

theorem cg_D_mul [Fintype β] {m k : ℕ} {P : Matrix α β R} {Q : Matrix β γ R} (hP : cg_D O m P)
    (hQ : cg_D O k Q) : cg_D O (m * k) (P * Q) := by
  intro i j
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine sum_mem fun l _ => ?_
  rw [show ((m * k : ℕ) : R) * (P i l * Q l j) = ((m : R) * P i l) * ((k : R) * Q l j) by push_cast; ring]
  exact mul_mem (hP i l) (hQ l j)

theorem cg_D_pow [Fintype α] [DecidableEq α] {m : ℕ} {A : Matrix α α R} (hA : cg_D O m A) :
    ∀ j : ℕ, cg_D O (m ^ j) (A ^ j) := by
  intro j
  induction j with
  | zero =>
    intro i k
    rw [pow_zero, pow_zero, Nat.cast_one, one_mul, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  | succ j ih =>
    rw [pow_succ, pow_succ]
    exact cg_D_mul ih hA

theorem cg_pow [Fintype α] [DecidableEq α] {m : ℕ} {A A' : Matrix α α R} (hA : cg_D O m A)
    (hA' : cg_D O m A') : ∀ (j c : ℕ), cg_C O (c * m ^ j) (A' - A) → cg_C O c (A' ^ j - A ^ j) := by
  intro j
  induction j with
  | zero => intro c _; simpa using cg_C_zero (O := O) (α := α) (β := α) c
  | succ j ih =>
    intro c h
    have e : A' ^ (j + 1) - A ^ (j + 1) = (A' ^ j - A ^ j) * A' + A ^ j * (A' - A) := by
      rw [pow_succ, pow_succ, Matrix.sub_mul, Matrix.mul_sub]; abel
    rw [e]
    refine cg_C_add (cg_C_mul_right (ih (c * m) ?_) hA') (cg_C_mul_left (cg_D_pow hA j) ?_)
    · rwa [show c * m * m ^ j = c * m ^ (j + 1) by ring]
    · exact cg_C_dvd (k := m) (by rwa [show c * m ^ j * m = c * m ^ (j + 1) by ring])

theorem cg_geo [Fintype α] [DecidableEq α] {m : ℕ} {A A' : Matrix α α R} (hA : cg_D O m A)
    (hA' : cg_D O m A') (N c : ℕ) (h : cg_C O (c * m ^ N) (A' - A)) : cg_C O c (geo N A' - geo N A) := by
  unfold geo
  rw [← Finset.sum_sub_distrib]
  refine cg_C_sum fun j hj => cg_pow hA hA' j c ?_
  have hj' : j ≤ N := (Finset.mem_range.1 hj).le
  refine cg_C_dvd (k := m ^ (N - j)) ?_
  rwa [mul_assoc, ← pow_add, Nat.add_sub_cancel' hj']

theorem cg_C_half [Invertible (2 : R)] {c : ℕ} {A : Matrix α β R} (h : cg_C O (2 * c) A) :
    cg_C O c ((⅟2 : R) • A) := by
  intro i j
  obtain ⟨t, ht, e⟩ := h i j
  refine ⟨t, ht, ?_⟩
  rw [Matrix.smul_apply, e, smul_eq_mul]
  push_cast
  linear_combination ((c : R) * t) * invOf_mul_self (2 : R)

theorem cg_D_half [Invertible (2 : R)] {m : ℕ} {A : Matrix α β R} (h : cg_D O m A) :
    cg_D O (2 * m) ((⅟2 : R) • A) := by
  intro i j
  have e : ((2 * m : ℕ) : R) * ((⅟2 : R) • A) i j = (m : R) * A i j := by
    rw [Matrix.smul_apply, smul_eq_mul]
    push_cast
    linear_combination ((m : R) * A i j) * invOf_mul_self (2 : R)
  rw [e]; exact h i j

theorem cg_cay [Fintype α] [DecidableEq α] [Invertible (2 : R)]
    (hden : ∀ A : Matrix α α R, ∃ m : ℕ, 1 ≤ m ∧ cg_D O m A) (N : ℕ) (Z : Matrix α α R) (c : ℕ)
    (hc : 1 ≤ c) :
    ∃ c' : ℕ, 1 ≤ c' ∧ ∀ Z' : Matrix α α R, cg_C O c' (Z' - Z) → cg_C O c (cay N Z' - cay N Z) := by
  obtain ⟨mZ, hmZ, hZ⟩ := hden Z
  obtain ⟨mG, hmG, hG⟩ := hden (geo N ((⅟2 : R) • Z))
  refine ⟨2 * (c * (mZ * mG) * (2 * mZ) ^ N), ?_, fun Z' h => ?_⟩
  · have h1 : 0 < (2 * mZ) ^ N := pow_pos (Nat.mul_pos two_pos hmZ) N
    exact Nat.mul_pos two_pos (Nat.mul_pos (Nat.mul_pos hc (Nat.mul_pos hmZ hmG)) h1)
  have hY : cg_D O (2 * mZ) ((⅟2 : R) • Z) := cg_D_half hZ
  have hYd : cg_C O (c * (mZ * mG) * (2 * mZ) ^ N) ((⅟2 : R) • Z' - (⅟2 : R) • Z) := by
    rw [← smul_sub]; exact cg_C_half h
  have hY' : cg_D O (2 * mZ) ((⅟2 : R) • Z') := cg_D_of_C hY hYd
  have hGd := cg_geo hY hY' N (c * (mZ * mG)) hYd
  have hZ0 : cg_D O (mZ * mG) Z := cg_D_mul_right mG hZ
  have hG0 : cg_D O (mZ * mG) (geo N ((⅟2 : R) • Z)) := cg_D_mul_left mZ hG
  have hG0' := cg_D_of_C hG0 hGd
  have e : cay N Z' - cay N Z = (Z' - Z) * geo N ((⅟2 : R) • Z') +
      Z * (geo N ((⅟2 : R) • Z') - geo N ((⅟2 : R) • Z)) := by
    unfold cay; simp only [Matrix.sub_mul, Matrix.mul_sub]; abel
  rw [e]
  refine cg_C_add (cg_C_mul_right ?_ hG0') (cg_C_mul_left hZ0 hGd)
  exact cg_C_dvd (k := 2 * (2 * mZ) ^ N)
    (by rwa [show c * (mZ * mG) * (2 * (2 * mZ) ^ N) = 2 * (c * (mZ * mG) * (2 * mZ) ^ N) by ring])

end Gen

section Adelic

theorem cg_D_exists {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {α β : Type} [Fintype α] [Fintype β] (A : Matrix α β (E ⊗[F] Af F)) :
    ∃ m : ℕ, 1 ≤ m ∧ cg_D (IntAf F E) m A := by
  obtain ⟨m, hm, h⟩ := Formalism.L2.SG.Pf.Tau.TraceIntegralityAlt.uniform_nat_mul (IntAf F E) (fun p : α × β => A p.1 p.2)
    (fun p => Formalism.L2.SG.Pf.Tau.TraceIntegralityAlt.exists_nat_mul_IntAf _)
  exact ⟨m, hm, fun i j => h (i, j)⟩

end Adelic

theorem cayley_continuous : CayCont := by
  intro D X Z c hc
  exact cg_cay (O := IntAf X.B.I.F X.B.I.E) (fun A => cg_D_exists A) _ Z c hc

end Formalism.L2.SG.Pf.SlabNDensePf
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.IdBlocks Formalism.L2.SG.Full
  Formalism.L2.SG.PoincareInHH.Cut

def IdMeetKeyC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), NeatKu X u Y.hK →
    ∀ (ρ ρ' : (Y.cs u).Cl) (t : GTerm X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u)), t.isId →
      Meets (Y.cs u) (Y.cs u) t ρ ρ' →
        ρ = ρ' ∧ t.lin ∈ NLam ((Y.cs u).lamOf ρ) (lf D (X.Fu u))

def VolColC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (ρ : (Y.cs u).Cl) (Ω : Set X.B.I.Ginf),
    IsSFund X.B.I (Formalism.L2.SG.TermOp.KExpCut.NOcol (X.Fu u) (Y.cs u) ρ) Ω → X.muN u Ω = X.muN u (Y.FN u)

end Formalism.L2.SG.Pf.IdMeet
end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.KExpCut
  Formalism.L2.SG.Full Formalism.L2.SG.Pf.Slab
open Matrix

namespace Formalism.L2.SG.Pf.SlabCoverPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def GFInfInj : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (s : X.B.I.GA), s ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I → s.1 = 1 → s = 1

def NStrongApprox : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (ρ : (Y.cs u).Cl) (n : X.B.I.Gf),
    X.LevelSubgroupNormalized → n ∈ X.NfinU u → ∃ ν ∈ Srat X u,
      (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * (ν.2 * n) * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u) ∈ X.K2

def NDense : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (n : X.B.I.Gf), n ∈ X.NfinU u →
    ∀ U : Set X.B.I.Gf, IsOpen U → n ∈ U →
      ∃ ν ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I, ν.1 ∈ X.NinfU u ∧ ν.2 ∈ X.NfinU u ∧ ν.2 ∈ U

def NLift : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (ρ : (Y.cs u).Cl) (t : X.B.I.Ginf),
    t ∈ NOcol (X.Fu u) (Y.cs u) ρ → ∃ s ∈ Srat X u, s.1 = t ∧
      (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * s.2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u) ∈ X.K2

def NRatLam : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (ρ : (Y.cs u).Cl) (ν : X.B.I.GA),
    X.LevelSubgroupNormalized → ν ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I → ν.1 ∈ X.NinfU u → ν.2 ∈ X.NfinU u →
    (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * ν.2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u) ∈ X.K2 →
    ν.1 ∈ NOcol (X.Fu u) (Y.cs u) ρ

def RatLeviC : Prop := ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), RatLevi X u

def PsiDdC : Prop := ∀ (D : D7) (X : HidaSetting D), PsiDd X

theorem hfin_sfin {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (h : Hfin X u) :
    (h : X.B.I.Gf) ∈ SfinU X u := by
  rw [Formalism.L2.SG.PoincareInHH.Cut.sfin_iff]
  refine ⟨?_, ?_⟩
  · intro a
    have e := h.2 (X.eR a) (by simp [fixSet])
    try beta_reduce
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, e, sub_self]
    exact Submodule.zero_mem _
  · have e := h.2 (X.zR u) (by simp [fixSet])
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, e, sub_self]
    exact Submodule.zero_mem _

theorem gam_srat {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (γ : X.B.I.GA) (hγ : γ ∈ Gam X u) :
    γ ∈ Srat X u := by
  obtain ⟨h1, h2⟩ := hγ
  obtain ⟨h21, h22⟩ := h2
  refine ⟨h1, Subgroup.subset_closure ⟨?_, hfin_sfin X u ⟨γ.2, h22⟩⟩⟩
  rw [Formalism.L2.SG.PoincareInHH.Cut.sinf_iff]
  intro v
  refine ⟨?_, ?_⟩
  · intro a
    have e := h21 v (X.eR a) (by simp [fixSet])
    try beta_reduce
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, e, sub_self]
    exact Submodule.zero_mem _
  · have e := h21 v (X.zR u) (by simp [fixSet])
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, e, sub_self]
    exact Submodule.zero_mem _

theorem iotaF_coe {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (γ : Gam X u) :
    ((iotaF X u γ : Hfin X u) : X.B.I.Gf) = (γ : X.B.I.GA).2 := rfl

end Formalism.L2.SG.Pf.SlabCoverPf
end
end
