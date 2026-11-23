module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle002
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle012
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle008
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle007
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle006
public import GroundTheory.ArithmeticGeometry.ToricVarieties.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle002
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
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
public import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.GR ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up

namespace PositivityTheory.Xgn.A_pt_af_type

variable {o C : Type} [CommRing o] [Field C] [Algebra o C]

theorem mem_mul_std (RC : Subalgebra o C) (p : ℕ) {X : Type} (f : X → C) :
    f ∈ mulLat (p : C) (stdLat RC X) ↔ ∀ y, f y ∈ pInt (C := C) RC p := by
  constructor
  · rintro ⟨g, hg, rfl⟩ y
    have hy : g y ∈ RC := hg y (Set.mem_univ y)
    refine Submodule.mem_span_singleton.2 ⟨⟨g y, hy⟩, ?_⟩
    change g y * (p : C) = (p : C) * g y
    ring
  · intro h
    choose a ha using fun y => Submodule.mem_span_singleton.1 (h y)
    refine ⟨fun y => (a y : C), fun y _ => (a y).2, ?_⟩
    funext y
    rw [← ha y]
    change (p : C) * (a y : C) = (a y : C) * (p : C)
    ring

theorem pInt_mem (RC : Subalgebra o C) (p : ℕ) {c : C} (h : c ∈ pInt (C := C) RC p) : c ∈ RC := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 h
  change (a : C) * (p : C) ∈ RC
  exact RC.mul_mem a.2 (natCast_mem RC p)

theorem coe_mem_pInt (RC : Subalgebra o C) (p : ℕ) {c : RC} (h : c ∈ Ideal.span {(p : RC)}) :
    (c : C) ∈ pInt (C := C) RC p := by
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 h
  refine Submodule.mem_span_singleton.2 ⟨a, ?_⟩
  change (a : C) * (p : C) = _
  push_cast
  rfl

theorem mem_af (RC : Subalgebra o C) (p : ℕ) {F : Type} [Zero F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ}
    (D : LieLatticeData C F n Sg r s) (χ : F → C) (u : Fin n → C) :
    u ∈ D.af RC p χ ↔ ∃ g ∈ D.M, ∀ y : Fin n → F,
      (∑ k, u k * χ (y k)) - g y ∈ pInt (C := C) RC p := by
  have hl : ∀ y : Fin n → F, linMap n χ u y = ∑ k, u k * χ (y k) := by
    intro y
    simp [linMap, Fintype.linearCombination_apply, Finset.sum_apply]
  change linMap n χ u ∈ D.M ⊔ mulLat (p : C) (stdLat RC _) ↔ _
  rw [AddSubgroup.mem_sup]
  constructor
  · rintro ⟨g, hg, f, hf, h⟩
    refine ⟨g, hg, fun y => ?_⟩
    have := (mem_mul_std RC p f).1 hf y
    rw [← hl, ← h]
    simpa using this
  · rintro ⟨g, hg, h⟩
    refine ⟨g, hg, linMap n χ u - g, (mem_mul_std RC p _).2 fun y => ?_, by abel⟩
    rw [Pi.sub_apply, hl]
    exact h y

theorem mem_dotDual (RC : Subalgebra o C) {m : ℕ} (L : AddSubgroup (Fin m → C)) (u : Fin m → C) :
    u ∈ dotDual RC L ↔ ∀ l ∈ L, l ⬝ᵥ u ∈ RC := by
  simp only [dotDual, AddSubgroup.mem_iInf]
  rfl

theorem congr_lin (RC : Subalgebra o C) (p : ℕ) {I : Type} [Fintype I] {n : ℕ}
    (Pm : Matrix (Fin n) I RC) (a : I → RC) (b : Fin n → RC)
    (h : ∀ k, (∑ j, Pm k j * a j) - b k ∈ Ideal.span {(p : RC)}) (l : Fin n → RC) :
    algebraMap RC C (∑ j, Matrix.vecMul l Pm j * a j) - ∑ k, (l k : C) * (b k : C)
      ∈ pInt (C := C) RC p := by
  have h1 : ∑ k, l k * ((∑ j, Pm k j * a j) - b k) ∈ Ideal.span {(p : RC)} :=
    Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (h k)
  have h2 : ∑ k, l k * ((∑ j, Pm k j * a j) - b k)
      = (∑ j, Matrix.vecMul l Pm j * a j) - ∑ k, l k * b k := by
    simp only [mul_sub, Finset.sum_sub_distrib, Matrix.vecMul, dotProduct, Finset.sum_mul,
      Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
  rw [h2] at h1
  have h3 := coe_mem_pInt RC p h1
  have h4 : (((∑ j, Matrix.vecMul l Pm j * a j) - ∑ k, l k * b k : RC) : C)
      = algebraMap RC C (∑ j, Matrix.vecMul l Pm j * a j) - ∑ k, (l k : C) * (b k : C) := by
    change algebraMap RC C ((∑ j, Matrix.vecMul l Pm j * a j) - ∑ k, l k * b k) = _

    rw [map_sub, map_sum (algebraMap RC C) (fun k => l k * b k)]
    simp only [map_mul]
    rfl
  rwa [h4] at h3

theorem dot_eq (RC : Subalgebra o C) {I : Type} [Fintype I] {n : ℕ}
    (J : Matrix I (Fin n) RC) (l : I → RC) (u : Fin n → C) :
    (∑ j, (l j : C) * (J.map (algebraMap RC C)).mulVec u j)
      = (fun k => ((Matrix.vecMul l J k : RC) : C)) ⬝ᵥ u := by
  have h : ∀ k, ((Matrix.vecMul l J k : RC) : C) = ∑ j, (l j : C) * algebraMap RC C (J j k) := by
    intro k
    change algebraMap RC C (∑ j, l j * J j k) = _

    rw [map_sum]
    simp only [map_mul]
    rfl
  simp only [h, Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_mul, Finset.mul_sum,
    mul_assoc]
  rw [Finset.sum_comm]

end PositivityTheory.Xgn.A_pt_af_type

open PositivityTheory.Xgn.A_pt_af_type in
theorem PositivityTheory.Xgn.t_pt_af_type : ∀ {o C : Type} [CommRing o] [Field C] [Algebra o C] (RC : Subalgebra o C) (p : ℕ) [Fact p.Prime] {I : Type} [Fintype I] [DecidableEq I] (MM : Submodule RC ((I → ZMod p) → C)), MM ≤ intFun RC _ → ∀ {F : Type} [Field F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData C F n Sg r s) (χ : F → RC), χ 0 = 0 → χ 1 = 1 → ∀ (i : (Fin n → F) →+ (I → ZMod p)) (π : (I → ZMod p) →+ (Fin n → F)), (∀ y, π (i y) = y) → (∀ h ∈ MM, (fun x => h (i (π x))) ∈ MM) → (MM.map (LinearMap.funLeft RC C (i : (Fin n → F) → (I → ZMod p)))).toAddSubgroup = D.M → ∀ (Pm : Matrix (Fin n) I RC) (J : Matrix I (Fin n) RC), Pm * J = 1 → (∀ (k : Fin n) (x : I → ZMod p), (∑ j, Pm k j * ((x j).val : RC)) - χ (π x k) ∈ Ideal.span {(p : RC)}) → (∀ l ∈ afLat p MM, Matrix.vecMul l (J * Pm) ∈ afLat p MM) → (∀ l : Fin n → RC, (fun k => (l k : C)) ∈ D.af RC p (fun a => (χ a : C)) ↔ Matrix.vecMul l Pm ∈ afLat p MM) ∧ ∀ u : Fin n → C, u ∈ D.hh RC p (fun a => (χ a : C)) ↔ ∀ l ∈ afLat p MM, (∑ j, (l j : C) * (J.map (algebraMap RC C)).mulVec u j) ∈ RC := by
  intro o C _ _ _ RC p _ I _ _ MM hint F _ _ n Sg r s D χ h0 h1 i π hπ hst hM Pm J hPJ hc hAF
  have hMM : ∀ g, g ∈ D.M ↔ ∃ h ∈ MM, (fun y => h (i y)) = g := by
    intro g
    rw [← hM]
    exact Submodule.mem_map
  have P1 : ∀ l : Fin n → RC, (fun k => (l k : C)) ∈ D.af RC p (fun a => (χ a : C)) ↔
      Matrix.vecMul l Pm ∈ afLat p MM := by
    intro l
    rw [mem_af]
    constructor
    · rintro ⟨g, hg, h⟩
      obtain ⟨h', hh', rfl⟩ := (hMM g).1 hg
      refine ⟨_, hst h' hh', fun x => ?_⟩
      have e1 := congr_lin RC p Pm (fun j => ((x j).val : RC)) (fun k => χ (π x k))
        (fun k => hc k x) l
      have e2 := h (π x)
      have e3 := Submodule.neg_mem _ (Submodule.add_mem _ e1 e2)
      convert e3 using 1
      ring
    · rintro ⟨g, hg, h⟩
      refine ⟨_, (hMM _).2 ⟨g, hg, rfl⟩, fun y => ?_⟩
      have e1 := congr_lin RC p Pm (fun j => ((i y j).val : RC)) (fun k => χ (π (i y) k))
        (fun k => hc k (i y)) l
      rw [hπ] at e1
      have e2 := h (i y)
      have e3 := Submodule.neg_mem _ (Submodule.add_mem _ e1 e2)
      convert e3 using 1
      ring
  have hco : ∀ u ∈ D.af RC p (fun a => (χ a : C)), ∀ k, u k ∈ RC := by
    intro u hu k
    obtain ⟨g, hg, h⟩ := (mem_af RC p D _ u).1 hu
    obtain ⟨h', hh', rfl⟩ := (hMM g).1 hg
    have e1 := pInt_mem RC p (h (Pi.single k 1))
    have e2 : ∑ j, u j * ((χ ((Pi.single k 1 : Fin n → F) j) : RC) : C) = u k := by
      rw [Finset.sum_eq_single k]
      · simp [h1]
      · intro j _ hj
        simp [Pi.single_eq_of_ne hj, h0]
      · simp
    rw [e2] at e1
    have e3 : h' (i (Pi.single k 1)) ∈ RC := by
      have := hint hh'
      obtain ⟨a, ha⟩ := this (i (Pi.single k 1))
      rw [← ha]
      exact a.2
    simpa using RC.add_mem e1 e3
  refine ⟨P1, fun u => ?_⟩
  rw [LieLatticeData.hh, mem_dotDual]
  constructor
  · intro h l hl
    rw [dot_eq]
    refine h _ ((P1 _).2 ?_)
    rw [Matrix.vecMul_vecMul]
    exact hAF l hl
  · intro h l hl
    let l' : Fin n → RC := fun k => ⟨l k, hco l hl k⟩
    have e := h _ ((P1 l').1 hl)
    rw [dot_eq, Matrix.vecMul_vecMul, hPJ, Matrix.vecMul_one] at e
    exact e
end

section

open GlobalTheory.CompanionTheory.Ar.Num

namespace PositivityTheory.Xgn.A_dotdual_bc

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_dotDual (R : Subalgebra o Ω) {m : ℕ} (L : AddSubgroup (Fin m → Ω)) (w : Fin m → Ω) :
    w ∈ dotDual R L ↔ ∀ v ∈ L, v ⬝ᵥ w ∈ R := by
  simp only [dotDual, AddSubgroup.mem_iInf, AddSubgroup.mem_comap]
  rfl

theorem dot_bij (m : ℕ) : Function.Bijective (dotProductBilin Ω Ω (m := Fin m) (A := Ω)).flip := by
  have h : ⇑(dotProductBilin Ω Ω (m := Fin m) (A := Ω)).flip = ⇑(dotProductEquiv Ω (Fin m)) := by
    funext w
    ext j
    simp [dotProductBilin, dotProductEquiv]
  rw [h]
  exact (dotProductEquiv Ω (Fin m)).bijective

theorem exists_system (R : Subalgebra o Ω) {m : ℕ} (L : AddSubgroup (Fin m → Ω))
    (h : LocFree R m L) : ∃ (k : ℕ) (v l : Fin k × Fin m → Fin m → Ω), (∀ i, v i ∈ L) ∧
      (∀ i, l i ∈ dotDual R L) ∧ ∀ j j', ∑ i, l i j * v i j' = if j' = j then 1 else 0 := by
  let L' : Submodule R (Fin m → Ω) :=
    { L with smul_mem' := fun a e he => h.1 a a.2 e he }
  obtain ⟨k, φ, v, hφ, hv⟩ := LocFreeProj.exists_dualBasis (L := L') (r := m) h
  refine ⟨k, fun i => v i, fun i j => φ i (Pi.single j 1), fun i => (v i).2, fun i => ?_,
    fun j j' => ?_⟩
  · rw [mem_dotDual]
    intro e he
    have h1 : e ⬝ᵥ (fun j => φ i (Pi.single j 1)) = φ i e := by
      rw [LinearMap.pi_apply_eq_sum_univ (φ i) e, dotProduct]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_eq_mul]
      congr 2
      funext j'
      simp [Pi.single_apply, eq_comm]
    rw [h1]
    exact hφ i e he
  · have := congrFun (hv (Pi.single j 1)) j'
    simpa [Finset.sum_apply, Pi.single_apply] using this

theorem bc_dot {C : Type} [Field C] [Algebra Ω C] {m : ℕ} (a b : Fin m → Ω) :
    bcMap Ω C (Fin m) a ⬝ᵥ bcMap Ω C (Fin m) b = algebraMap Ω C (a ⬝ᵥ b) := by

  simp [dotProduct, bcMap, map_sum]

end PositivityTheory.Xgn.A_dotdual_bc

open PositivityTheory.Xgn.A_dotdual_bc in
theorem PositivityTheory.Xgn.t_dotdual_bc : ∀ {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (R : Subalgebra o Ω) (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ (m : ℕ) (L : AddSubgroup (Fin m → Ω)), LocFree R m L → LocFree R m (dotDual R L) ∧ dotDual R (dotDual R L) = L ∧ dotDual RC (spanOver RC (bcMap Ω C (Fin m) '' L)) = spanOver RC (bcMap Ω C (Fin m) '' (dotDual R L : AddSubgroup (Fin m → Ω))) := by
  intro o Ω C _ _ _ _ _ _ _ R RC hR m L h
  obtain ⟨h1, h2⟩ := DualLattice.locFree_dual R (dotProductBilin Ω Ω (m := Fin m) (A := Ω))
    (dot_bij m) m L (dotDual R L) h (fun w => mem_dotDual R L w)
  refine ⟨h1, ?_, ?_⟩
  · ext v
    rw [mem_dotDual, h2]
    refine forall₂_congr fun w _ => ?_
    rw [dotProduct_comm]
    rfl
  obtain ⟨k, v, l, hv, hl, hs⟩ := exists_system R L h
  apply le_antisymm
  · intro u hu
    rw [mem_dotDual] at hu
    have key : u = ∑ i, (bcMap Ω C (Fin m) (v i) ⬝ᵥ u) • bcMap Ω C (Fin m) (l i) := by
      funext j
      have h3 : ∀ j', ∑ i, algebraMap Ω C (l i j) * algebraMap Ω C (v i j')
          = if j' = j then 1 else 0 := fun j' => by
        have := congrArg (algebraMap Ω C) (hs j j')

        rw [map_sum] at this
        simp only [map_mul] at this
        rw [this]
        split_ifs <;> simp
      have h4 : ∀ (x : Fin m → Ω) j, bcMap Ω C (Fin m) x j = algebraMap Ω C (x j) := fun _ _ => rfl
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, dotProduct, h4, Finset.sum_mul]
      rw [Finset.sum_comm]
      calc u j = ∑ j', (if j' = j then 1 else 0) * u j' := by simp
        _ = _ := Finset.sum_congr rfl fun j' _ => by
          rw [← h3, Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
    rw [key]
    refine AddSubgroup.sum_mem _ fun i _ => AddSubgroup.subset_closure ?_
    refine ⟨_, hu _ (AddSubgroup.subset_closure ⟨1, RC.one_mem, _, ⟨v i, hv i, rfl⟩, ?_⟩), _,
      ⟨l i, hl i, rfl⟩, rfl⟩
    rw [one_smul]
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, _, ⟨w, hw, rfl⟩, rfl⟩
    refine (mem_dotDual _ _ _).2 fun x hx => ?_
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨b, hb, _, ⟨e, he, rfl⟩, rfl⟩ := hx
      rw [smul_dotProduct, dotProduct_smul, bc_dot, smul_eq_mul, smul_eq_mul]
      exact RC.mul_mem hb (RC.mul_mem ha (hR _ ((mem_dotDual R L w).1 hw e he)))
    | zero => rw [zero_dotProduct]; exact RC.zero_mem
    | add x y _ _ hx hy => rw [add_dotProduct]; exact RC.add_mem hx hy
    | neg x _ hx => rw [neg_dotProduct]; exact RC.neg_mem hx
end

section

open GlobalTheory.CompanionTheory.Ar.Num

namespace PositivityTheory.Xgn.A_ha_lattice

theorem dvr_of_height_one {A S : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (q : Ideal A) [q.IsPrime] (h1 : q.height = 1) [CommRing S] [IsDomain S] [Algebra A S]
    [IsLocalization.AtPrime S q] : IsDiscreteValuationRing S := by
  have hloc : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S q
  have hN : IsNoetherianRing S := IsLocalization.isNoetherianRing q.primeCompl S inferInstance
  have hI : IsIntegrallyClosed S :=
    isIntegrallyClosed_of_isLocalization S q.primeCompl q.primeCompl_le_nonZeroDivisors
  have hd : ringKrullDim S = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q S, h1]; rfl
  have hf : ¬ IsField S := fun h => by
    rw [ringKrullDim_eq_zero_of_isField h] at hd
    exact absurd hd (by decide)
  have hk : Ring.KrullDimLE 1 S := Ring.krullDimLE_iff.2 (by rw [hd]; rfl)
  have key : IsDiscreteValuationRing S ↔ IsIntegrallyClosed S ∧ ∃! P : Ideal S, P ≠ ⊥ ∧ P.IsPrime :=
    (IsDiscreteValuationRing.TFAE S hf).out 1 4
  refine key.2 ⟨hI, IsLocalRing.maximalIdeal S,
    ⟨IsLocalRing.isField_iff_maximalIdeal_eq.not.1 hf, inferInstance⟩, ?_⟩
  rintro P ⟨hP0, hP⟩
  exact IsLocalRing.eq_maximalIdeal (Ring.krullDimLE_one_iff_of_noZeroDivisors.1 hk P hP0 hP)

theorem mem_of_testPt {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (p : ℕ)
    (hp : p.Prime) (hp0 : (p : Ω) ≠ 0) (hN : IsNoetherianRing R) (hF : IsFractionRing R Ω)
    (hI : IsIntegrallyClosedIn R Ω) (a : Ω) (m : ℕ) (hm : (p : Ω) ^ m * a ∈ R)
    (h : ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C),
      IsTestPt p R RC → algebraMap Ω C a ∈ RC) : a ∈ R := by
  have hIC : IsIntegrallyClosed R := (isIntegrallyClosed_iff_isIntegrallyClosedIn Ω).2 hI
  obtain ⟨y, hy⟩ := GroundTheory.Arith.Toric.mem_range_of_forall_height_one (A := R) (K := Ω) a
    (fun q hq h1 => by
      by_cases hpq : (p : R) ∈ q
      · let S : Subalgebra R Ω :=
          Localization.subalgebra.ofField Ω q.primeCompl q.primeCompl_le_nonZeroDivisors
        have hS : IsDiscreteValuationRing S := dvr_of_height_one q h1
        let A : Subalgebra o Ω := S.restrictScalars o
        have hA : IsDiscreteValuationRing A := hS
        have hAF : IsFractionRing A Ω := (inferInstance : IsFractionRing S Ω)
        have hu : ¬ IsUnit (p : A) := by
          intro hu
          have hu' : IsUnit (algebraMap R S (p : R)) := by
            rw [map_natCast]; exact hu
          exact ((IsLocalization.AtPrime.isUnit_to_map_iff S q _).1 hu') hpq
        obtain ⟨C, _, _, _, _, RC, hT, hRC⟩ := PositivityTheory.Xgn.t_testpt_exists A p hp hp0 hA hAF hu
        have hT' : IsTestPt p R RC :=
          ⟨hT.1, hT.2.1, hT.2.2.1, fun b hb => hT.2.2.2 b (S.algebraMap_mem ⟨b, hb⟩)⟩
        obtain ⟨b, s, hs, hab⟩ := hRC a (h C RC hT')
        refine ⟨b, s, hs, ?_⟩
        have hs0 : algebraMap R Ω s ≠ 0 := by
          intro h0
          have : s = 0 := Subtype.ext h0
          exact hs (this ▸ q.zero_mem)
        rw [hab, mul_assoc, inv_mul_cancel₀ hs0, mul_one]
      · refine ⟨⟨_, hm⟩, (p : R) ^ m, fun h' => hpq (hq.mem_of_pow_mem m h'), ?_⟩
        rw [map_pow, map_natCast, mul_comm]
        rfl)
  rw [← hy]
  exact y.2

theorem exists_ext {Ω C : Type} [Field Ω] [Field C] [Algebra Ω C] {ι : Type} [Fintype ι]
    (ψ : Module.Dual Ω (ι → Ω)) :
    ∃ Φ : Module.Dual C (ι → C), ∀ e, Φ (bcMap Ω C ι e) = algebraMap Ω C (ψ e) := by
  classical
  refine ⟨Fintype.linearCombination C fun i => algebraMap Ω C (ψ (Pi.single i 1)), fun e => ?_⟩
  conv_rhs => rw [pi_eq_sum_univ' e]

  simp [Fintype.linearCombination_apply, bcMap, map_sum]

end PositivityTheory.Xgn.A_ha_lattice

theorem PositivityTheory.Xgn.t_ha_lattice : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (p : ℕ), p.Prime → (p : Ω) ≠ 0 → IsNoetherianRing R → IsFractionRing R Ω → IsIntegrallyClosedIn R Ω → ∀ {ι : Type} [Fintype ι] (N : ℕ) (L : AddSubgroup (ι → Ω)), LocFree R N L → ∀ v : ι → Ω, (∃ m : ℕ, (p : Ω) ^ m • v ∈ L) → (∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), IsTestPt p R RC → bcMap Ω C ι v ∈ spanOver RC (bcMap Ω C ι '' L)) → v ∈ L := by
  intro o Ω _ _ _ R p hp hp0 hN hF hI ι _ N L hL v hv h
  obtain ⟨m, hm⟩ := hv
  refine Reflexive.locFree_reflexive R N L hL v fun ψ hψ => ?_
  refine PositivityTheory.Xgn.A_ha_lattice.mem_of_testPt R p hp hp0 hN hF hI (ψ v) m ?_ ?_
  · have := hψ _ hm
    rwa [map_smul, smul_eq_mul] at this
  · intro C _ _ _ _ RC hT
    obtain ⟨Φ, hΦ⟩ := PositivityTheory.Xgn.A_ha_lattice.exists_ext (C := C) ψ
    have key : ∀ x ∈ spanOver RC (bcMap Ω C ι '' L), Φ x ∈ RC := by
      intro x hx
      induction hx using AddSubgroup.closure_induction with
      | mem x hx =>
        obtain ⟨c, hc, _, ⟨e, he, rfl⟩, rfl⟩ := hx
        rw [map_smul, smul_eq_mul, hΦ]
        exact RC.mul_mem hc (hT.2.2.2 _ (hψ e he))
      | zero => simp
      | add x y _ _ hx hy => rw [map_add (f := _)]; exact RC.add_mem hx hy
      | neg x _ hx => rw [map_neg]; exact RC.neg_mem hx
    rw [← hΦ]
    exact key _ (h C RC hT)
end

section

open MvPolynomial

namespace PositivityTheory.Xgn.MultihomogeneousLine

theorem sum_scale {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {n : ℕ}
    (u : Fin n → MvPolynomial (Σ k, ι k) ℤ) (a : K → ℕ)
    (hu : ∀ j, GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (u j) a) (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    ∑ j, ‖eval (fun p => c p.1 * z p) (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2 =
      (∏ k, ‖c k‖ ^ a k) ^ 2 * ∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [PositivityTheory.Xgn.multihomogeneous_eval_scale K ι (u j) a c z (hu j), norm_mul, mul_pow, norm_prod]
  simp only [norm_pow]

theorem sum_pos {σ : Type} {n : ℕ} (u : Fin n → MvPolynomial σ ℤ) (z : σ → ℂ)
    (h : ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j)) ≠ 0) :
    0 < ∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2 := by
  obtain ⟨j, hj⟩ := h
  exact Finset.sum_pos' (fun i _ => sq_nonneg _)
    ⟨j, Finset.mem_univ j, pow_pos (norm_pos_iff.mpr hj) 2⟩

theorem sqrt_scale (x y N D : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt ((x ^ 2 * N) / (y ^ 2 * D)) = x / y * Real.sqrt (N / D) := by
  rw [mul_div_mul_comm, ← div_pow, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (div_nonneg hx hy)]

end PositivityTheory.Xgn.MultihomogeneousLine

theorem PositivityTheory.Xgn.multihomogeneous_line_bundle : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (a b : K → ℕ) (n : ℕ) (u v : Fin n → MvPolynomial (Σ k, ι k) ℤ), (∀ j, GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (u j) a) → (∀ j, GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (v j) b) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j)) ≠ 0) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j)) ≠ 0) → ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm A → ReciprocityTheory.ChartRestriction.G.Geo.IsConjInvariantH A → ∃ A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, A'.a = (fun k => A.a k + (a k : ℤ) - (b k : ℤ)) ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm A' ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsConjInvariantH A' ∧ ∀ z : ((Σ k, ι k) → ℂ), A'.h z = A.h z * Real.sqrt ((∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2) / (∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j))‖ ^ 2)) := by
  intro K _ _ ι _ A a b n u v hu hv hu0 hv0 hsm hconj
  refine ⟨⟨fun k => A.a k + (a k : ℤ) - (b k : ℤ),
    fun z => A.h z * Real.sqrt ((∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2) /
      (∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j))‖ ^ 2)), ?_, ?_⟩, rfl, ?_, ?_, fun _ => rfl⟩
  · intro z hz
    exact mul_pos (A.pos z hz) (Real.sqrt_pos.mpr (div_pos
      (MultihomogeneousLine.sum_pos u z (hu0 z hz)) (MultihomogeneousLine.sum_pos v z (hv0 z hz))))
  · intro c z hc
    rw [A.smul c z hc, MultihomogeneousLine.sum_scale u a hu, MultihomogeneousLine.sum_scale v b hv,
      MultihomogeneousLine.sqrt_scale _ _ _ _
        (Finset.prod_nonneg fun k _ => pow_nonneg (norm_nonneg _) _)
        (Finset.prod_nonneg fun k _ => pow_nonneg (norm_nonneg _) _)]
    have : ∀ k, ‖c k‖ ^ (A.a k + (a k : ℤ) - (b k : ℤ)) = ‖c k‖ ^ A.a k * ‖c k‖ ^ a k / ‖c k‖ ^ b k := by
      intro k
      have h0 : ‖c k‖ ≠ 0 := norm_ne_zero_iff.mpr (hc k)
      rw [zpow_sub₀ h0, zpow_add₀ h0, zpow_natCast, zpow_natCast]
    simp only [this, Finset.prod_div_distrib, Finset.prod_mul_distrib]
    ring
  · have hN : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ =>
        ∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2) :=
      ContDiff.sum fun j _ => PositivityTheory.Xgn.polynomial_norm_square_smooth _ (u j)
    have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ =>
        ∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j))‖ ^ 2) :=
      ContDiff.sum fun j _ => PositivityTheory.Xgn.polynomial_norm_square_smooth _ (v j)
    exact ContDiffOn.mul hsm (ContDiffOn.sqrt
      (hN.contDiffOn.div hD.contDiffOn fun z hz => (MultihomogeneousLine.sum_pos v z (hv0 z hz)).ne')
      fun z hz => (div_pos (MultihomogeneousLine.sum_pos u z (hu0 z hz))
        (MultihomogeneousLine.sum_pos v z (hv0 z hz))).ne')
  · intro z
    have := hconj z
    simp only [this, PositivityTheory.Xgn.polynomial_eval_complex_conjugate, RCLike.norm_conj]
end
