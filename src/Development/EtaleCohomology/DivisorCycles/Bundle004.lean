module

public import Development.EtaleCohomology.DivisorCycles.Bundle002
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Artinian.Algebra
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.RingTheory.Artinian.Ring

@[expose] public section

section

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div

namespace LateralTheory.DivDb.SemisPf
open LateralTheory.DivDb

variable {C : Type} [Field C] {N : ℕ}

def img {A : Subalgebra C (Mat C N)} (I : Ideal A) : Submodule C (Fin N → C) :=
  Submodule.span C {w | ∃ x ∈ I, ∃ v, w = (x : Mat C N) *ᵥ v}

lemma img_step {A : Subalgebra C (Mat C N)} (J I : Ideal A) {x : A} (hx : x ∈ J) {u : Fin N → C}
    (hu : u ∈ img I) : (x : Mat C N) *ᵥ u ∈ img (J * I) := by
  induction hu using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨y, hy, v, rfl⟩ := hw
    refine Submodule.subset_span ⟨x * y, Submodule.mul_mem_mul hx hy, v, ?_⟩
    simp [Matrix.mulVec_mulVec]
  | zero => simp
  | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact add_mem ha hb
  | smul c a _ ha => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ c ha

lemma img_bot {A : Subalgebra C (Mat C N)} : img (⊥ : Ideal A) = ⊥ := by
  rw [img, Submodule.span_eq_bot]
  rintro w ⟨x, hx, v, rfl⟩
  rw [Submodule.mem_bot] at hx
  simp [hx]

lemma conj_pow (P B Q : Mat C N) (h : Q * P = 1) (n : ℕ) : (P * B * Q) ^ (n + 1) = P * B ^ (n + 1) * Q := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, pow_succ B (n+1)]
    calc P * B ^ (n + 1) * Q * (P * B * Q) = P * B ^ (n + 1) * (Q * P) * B * Q := by noncomm_ring
      _ = _ := by rw [h]; noncomm_ring

lemma nil_conj (P B Q : Mat C N) (h : Q * P = 1) (hB : IsNilpotent B) : IsNilpotent (P * B * Q) := by
  obtain ⟨k, hk⟩ := hB
  refine ⟨k + 1, ?_⟩
  rw [conj_pow P B Q h, pow_succ, hk]; simp

lemma inv_mul_rho {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin N) C) (g : Γ) :
    (ρ g⁻¹ : Mat C N) * (ρ g : Mat C N) = 1 := by
  rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

lemma mul_inv_rho {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin N) C) (g : Γ) :
    (ρ g : Mat C N) * (ρ g⁻¹ : Mat C N) = 1 := by
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem Semis_of : Semis := by
  intro Γ C _ _ N ρ A hss hn hk Y hYA hY

  let S : Set (Mat C N) := {Z | Z ∈ A ∧ ∀ a ∈ A, IsNilpotent (a * Z)}
  let U : Submodule C (Fin N → C) := Submodule.span C {w | ∃ Z ∈ S, ∃ v, w = Z *ᵥ v}
  have hUst : ∀ g, ∀ v ∈ U, (ρ g : Mat C N) *ᵥ v ∈ U := by
    intro g v hv
    induction hv using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨Z, ⟨hZA, hZ⟩, v, rfl⟩ := hw
      refine Submodule.subset_span ⟨(ρ g : Mat C N) * Z * (ρ g⁻¹ : Mat C N), ⟨hn g Z hZA, ?_⟩,
        (ρ g : Mat C N) *ᵥ v, ?_⟩
      · intro a ha
        have ha' : (ρ g⁻¹ : Mat C N) * a * (ρ g⁻¹⁻¹ : Mat C N) ∈ A := hn g⁻¹ a ha
        rw [inv_inv] at ha'
        have := nil_conj (ρ g : Mat C N) ((ρ g⁻¹ : Mat C N) * a * (ρ g : Mat C N) * Z)
          (ρ g⁻¹ : Mat C N) (inv_mul_rho ρ g) (hZ ((ρ g⁻¹ : Mat C N) * a * (ρ g : Mat C N)) ha')
        convert this using 1
        calc a * ((ρ g : Mat C N) * Z * (ρ g⁻¹ : Mat C N))
            = ((ρ g : Mat C N) * (ρ g⁻¹ : Mat C N)) * a * ((ρ g : Mat C N) * Z * (ρ g⁻¹ : Mat C N)) := by
              rw [mul_inv_rho]; simp
          _ = _ := by noncomm_ring
      · rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc ((ρ g : Mat C N) * Z), inv_mul_rho, mul_one]
    | zero => simp
    | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact add_mem ha hb
    | smul c a _ ha => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ c ha
  obtain ⟨W, hcompl, hWst⟩ := hss U hUst
  have hWA := hk W hWst
  have hkill : ∀ Z ∈ S, ∀ w ∈ W, Z *ᵥ w = 0 := by
    intro Z hZ w hw
    have h1 : Z *ᵥ w ∈ U := Submodule.subset_span ⟨Z, hZ, w, rfl⟩
    have h2 : Z *ᵥ w ∈ W := hWA Z hZ.1 w hw
    have := hcompl.inf_eq_bot
    have h3 : Z *ᵥ w ∈ U ⊓ W := ⟨h1, h2⟩
    rw [this] at h3
    exact (Submodule.mem_bot C).1 h3
  have : IsArtinianRing A := IsArtinianRing.of_finite C A
  let J : Ideal A := Ideal.jacobson ⊥
  have hSJ : ∀ Z (hZ : Z ∈ S), (⟨Z, hZ.1⟩ : A) ∈ J := by
    intro Z hZ
    rw [Ideal.mem_jacobson_iff]
    intro y
    have hnil : IsNilpotent (y * (⟨Z, hZ.1⟩ : A)) := by
      obtain ⟨k, hk'⟩ := hZ.2 y y.2
      refine ⟨k, Subtype.ext ?_⟩
      simpa using hk'
    have hu := hnil.isUnit_one_add
    refine ⟨↑hu.unit⁻¹, ?_⟩
    rw [Ideal.mem_bot]
    have h1 : (↑hu.unit⁻¹ : A) * (1 + y * (⟨Z, hZ.1⟩ : A)) = 1 := hu.val_inv_mul
    calc (↑hu.unit⁻¹ : A) * y * (⟨Z, hZ.1⟩ : A) + ↑hu.unit⁻¹ - 1
        = (↑hu.unit⁻¹ : A) * (1 + y * (⟨Z, hZ.1⟩ : A)) - 1 := by noncomm_ring
      _ = 0 := by rw [h1, sub_self]
  obtain ⟨m, hm⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  have key : ∀ k : ℕ, U ≤ img (J ^ (k + 1)) := by
    intro k
    induction k with
    | zero =>
      rw [Submodule.pow_one]
      show Submodule.span C _ ≤ _
      rw [Submodule.span_le]
      rintro w ⟨Z, hZ, v, rfl⟩
      exact Submodule.subset_span ⟨⟨Z, hZ.1⟩, hSJ Z hZ, v, rfl⟩
    | succ k ih =>
      show Submodule.span C _ ≤ _
      rw [Submodule.span_le]
      rintro w ⟨Z, hZ, v, rfl⟩
      have hv : v ∈ U ⊔ W := hcompl.sup_eq_top ▸ Submodule.mem_top
      obtain ⟨u, hu, w', hw', rfl⟩ := Submodule.mem_sup.1 hv
      show Z *ᵥ (u + w') ∈ img (J ^ (k + 1 + 1))
      rw [Matrix.mulVec_add, hkill Z hZ w' hw', add_zero, Ideal.IsTwoSided.pow_succ]
      exact img_step J _ (x := ⟨Z, hZ.1⟩) (hSJ Z hZ) (ih hu)
  have hU : U = ⊥ := by
    have h := key m
    have hb : J ^ (m + 1) = ⊥ := by
      rw [Submodule.pow_succ, hm, Submodule.zero_eq_bot, Submodule.bot_mul]
    rw [hb, img_bot] at h
    exact le_bot_iff.1 h
  ext i j
  have hv : Y *ᵥ Pi.single j 1 ∈ U := Submodule.subset_span ⟨Y, ⟨hYA, hY⟩, Pi.single j 1, rfl⟩
  rw [hU, Submodule.mem_bot] at hv
  simpa using congrFun hv i
end LateralTheory.DivDb.SemisPf
end

section

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.KeyPf
open LateralTheory.DivDb

variable {C : Type} [Field C] {N n : ℕ}

theorem sum_mul_p {p : Fin n → Mat C N} (hS : Sys p) (d : Fin n → C) (k : Fin n) :
    (∑ j, d j • p j) * p k = d k • p k := by
  rw [Finset.sum_mul, Finset.sum_eq_single k]
  · rw [smul_mul_assoc, (hS.1.idem k).eq]
  · intro j _ hj; rw [smul_mul_assoc, hS.1.ortho hj, smul_zero]
  · simp

theorem p_mul_sum {p : Fin n → Mat C N} (hS : Sys p) (d : Fin n → C) (k : Fin n) :
    p k * (∑ j, d j • p j) = d k • p k := by
  rw [Finset.mul_sum, Finset.sum_eq_single k]
  · rw [mul_smul_comm, (hS.1.idem k).eq]
  · intro j _ hj; rw [mul_smul_comm, hS.1.ortho (Ne.symm hj), smul_zero]
  · simp

theorem sum_mul_sum {p : Fin n → Mat C N} (hS : Sys p) (d d' : Fin n → C) :
    (∑ j, d j • p j) * (∑ j, d' j • p j) = ∑ j, (d j * d' j) • p j := by
  rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mul_assoc, p_mul_sum hS, smul_smul]

theorem sum_inv {p : Fin n → Mat C N} (hS : Sys p) (d : Fin n → C) (hd : ∀ j, d j ≠ 0) :
    (∑ j, d j • p j) * (∑ j, (d j)⁻¹ • p j) = 1 ∧ (∑ j, (d j)⁻¹ • p j) * (∑ j, d j • p j) = 1 := by
  rw [sum_mul_sum hS, sum_mul_sum hS]
  simp only [mul_inv_cancel₀ (hd _), inv_mul_cancel₀ (hd _), one_smul, hS.1.complete, and_self]

theorem sum_mem {p : Fin n → Mat C N} (A : Subalgebra C (Mat C N)) (hp : ∀ i, p i ∈ A) (d : Fin n → C) :
    (∑ j, d j • p j) ∈ A :=
  Subalgebra.sum_mem _ fun j _ => Subalgebra.smul_mem _ (hp j) _

theorem inv_in (A : Subalgebra C (Mat C N)) {v : Mat C N} (hvA : v ∈ A) (hv : IsUnit v) :
    ∃ w ∈ A, v * w = 1 := by
  let a : A := ⟨v, hvA⟩
  have hinj : Function.Injective A.val := Subtype.val_injective
  have ha : a ∈ nonZeroDivisors A := comap_nonZeroDivisors_le_of_injective hinj hv.mem_nonZeroDivisors
  haveI : Module.Finite C A := FiniteDimensional.finiteDimensional_submodule (Subalgebra.toSubmodule A)
  have hu : IsUnit a := IsArtinianRing.isUnit_of_nonZeroDivisor_of_isIntegral' (R := C) ha
  obtain ⟨b, hb⟩ := hu
  refine ⟨((b⁻¹ : Aˣ) : A), ((b⁻¹ : Aˣ) : A).2, ?_⟩
  have := congrArg Subtype.val b.mul_inv
  rw [hb] at this; exact this

theorem zcl_sub (S : Set (Mat C N)) : S ⊆ Zcl S := fun x hx _ hf => hf x hx

theorem zcl_mono {S T : Set (Mat C N)} (h : S ⊆ T) : Zcl S ⊆ Zcl T :=
  fun y hy f hf => hy f fun x hx => hf x (h hx)

end LateralTheory.DivDb.KeyPf

namespace LateralTheory.DivDb.KeyPf
open LateralTheory.DivDb
variable {C : Type} [Field C] {N n : ℕ}

theorem sys_conj {p : Fin n → Mat C N} (hS : Sys p) (R Ri : Mat C N) (h1 : ∀ X, R * (Ri * X) = X)
    (h2 : ∀ X, Ri * (R * X) = X) : Sys (fun j => Ri * p j * R) := by
  have h2' : ∀ X, Ri * (R * X) = X := h2
  refine ⟨⟨⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩, fun i h => hS.2 i ?_⟩
  · show Ri * p i * R * (Ri * p i * R) = Ri * p i * R
    simp only [mul_assoc, h1]; rw [← mul_assoc (p i), (hS.1.idem i).eq]
  · show Ri * p i * R * (Ri * p j * R) = 0
    simp only [mul_assoc, h1]; rw [← mul_assoc (p i), hS.1.ortho hij]; simp
  · rw [← Finset.sum_mul, ← Finset.mul_sum, hS.1.complete, mul_one]
    have := h2 1; simpa using this
  · have := congrArg (fun Y => R * Y * Ri) h
    simp only [mul_assoc, h1, mul_zero, zero_mul] at this
    have e' : R * Ri = 1 := by simpa using h1 1
    rwa [e', mul_one] at this

theorem tv_zcl {ρS : Submonoid (Mat C N)} (hZM : ZclMul) (hUn : Unip) [CharZero C]
    (A : Subalgebra C (Mat C N)) (p : Fin n → Mat C N) (hS : Sys p)
    (hT : ∀ a ∈ A, ∀ j k, j ≠ k → p j * a * p k ∈ Tan (ρS : Set (Mat C N))) :
    ∀ u ∈ Tv A p, u ∈ Zcl (ρS : Set (Mat C N)) := by
  intro u hu
  induction hu using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, j, k, hjk, rfl⟩ := hx
    apply hUn C N ρS _ (hT a ha j k hjk)
    have : p k * p j = 0 := hS.1.ortho (Ne.symm hjk)
    calc p j * a * p k * (p j * a * p k) = p j * a * (p k * p j) * a * p k := by simp only [mul_assoc]
      _ = 0 := by rw [this]; simp
  | one => exact zcl_sub _ ρS.one_mem
  | mul x y _ _ hx hy => exact hZM C N ρS x hx y hy

theorem Key_of (hIC : IdemConj) (hMU : MatrixUnits₂) (hUF : UnitFactorization) (hTI : TanIndex) (hUn : Unip)
    (hZM : ZclMul) (hGS : GenSpec) (hTP : TorusPt) (hTD : TanDeg) (hCC : CycleCount) : Key := by
  intro Γ C _ _ _ _ N n ρ e p hDeg hLac hG U hU hUf g
  obtain ⟨hS, hX, hCo, hNN, hNo, _hKe, hOff⟩ := hG
  have hRiR : (ρ g⁻¹ : Mat C N) * (ρ g : Mat C N) = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have hRRi : (ρ g : Mat C N) * (ρ g⁻¹ : Mat C N) = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  set R : Mat C N := (ρ g : Mat C N) with hRdef
  set Ri : Mat C N := (ρ g⁻¹ : Mat C N) with hRidef
  have h1 : ∀ X, R * (Ri * X) = X := fun X => by rw [← mul_assoc, hRRi, one_mul]
  have h2 : ∀ X, Ri * (R * X) = X := fun X => by rw [← mul_assoc, hRiR, one_mul]
  set A := env ρ
  have hSq := sys_conj hS R Ri h1 h2
  have hCq : Corner A (fun j => Ri * p j * R) := by
    refine ⟨fun i => ?_, fun a ha i => ?_⟩
    · have := hNo g⁻¹ (p i) (hCo.1 i); rwa [inv_inv] at this
    · obtain ⟨c, hc⟩ := hCo.2 _ (hNo g a ha) i
      refine ⟨c, ?_⟩
      calc Ri * p i * R * a * (Ri * p i * R) = Ri * (p i * (R * a * Ri) * p i) * R := by
            simp only [mul_assoc]
        _ = c • (Ri * p i * R) := by rw [hc]; simp only [mul_smul_comm, smul_mul_assoc]
  obtain ⟨v, hvA, hvU, π, hvπ, hπ⟩ := hIC C N n A p _ hS hCo hSq hCq hNN
  obtain ⟨E, hE⟩ := hMU C N n A p hS hCo hNN
  obtain ⟨u, huT, d, hd, hvud⟩ := hUF C N n A p E hS hE v hvA hvU
  obtain ⟨hDD', hD'D⟩ := sum_inv hS d hd
  have hu : u = v * ∑ j, (d j)⁻¹ • p j := by rw [hvud, mul_assoc, hDD', mul_one]
  have hup : ∀ j, u * p j = Ri * p (π j) * R * u := by
    intro j
    have e1 : u * p j = v * ((d j)⁻¹ • p j) := by rw [hu, mul_assoc, sum_mul_p hS]
    have e2 : Ri * p (π j) * R * u = v * ((d j)⁻¹ • p j) := by
      rw [hu, ← mul_assoc, ← hvπ j, mul_assoc, p_mul_sum hS]
    rw [e1, e2]
  have hxp : ∀ j, R * u * p j = p (π j) * (R * u) := by
    intro j; rw [mul_assoc, hup]; simp only [mul_assoc, h1]
  have hD'U : IsUnit (∑ j, (d j)⁻¹ • p j) := ⟨⟨_, _, hD'D, hDD'⟩, rfl⟩
  have huU : IsUnit u := by rw [hu]; exact hvU.mul hD'U
  have hxU : IsUnit (R * u) := (Units.isUnit (ρ g)).mul huU
  obtain ⟨B, hBf, hB⟩ := hGS C N n p (R * u) π hS hxU hxp
  have hXT := hTI Γ C N ρ U hU hUf hX
  obtain ⟨τ, hτ, htZ, hτB⟩ := hTP C N n (img ρ U) p e hS hLac hXT B hBf
  have hdisj := hB τ hτ hτB
  obtain ⟨hTT', hT'T⟩ := sum_inv hS τ hτ
  set t := ∑ j, τ j • p j with htdef
  have huZ : u ∈ Zcl (img ρ U : Set (Mat C N)) :=
    tv_zcl hZM hUn A p hS (fun a ha j k hjk => hTI Γ C N ρ U hU hUf (hOff a ha j k hjk)) u huT
  have hmZ := hZM C N (img ρ U) u huZ t htZ
  have htU : IsUnit t := ⟨⟨_, _, hTT', hT'T⟩, rfl⟩
  have hyU : IsUnit (R * u * t) := hxU.mul htU
  have hyp : ∀ j, R * u * t * p j = p (π j) * (R * u * t) := by
    intro j
    rw [mul_assoc, sum_mul_p hS, ← mul_assoc (p _), ← hxp, mul_assoc, mul_assoc, p_mul_sum hS]
    simp only [mul_assoc]
  have himg : ∀ y ∈ img ρ U, y ∈ img ρ ⊤ := fun y hy => by
    obtain ⟨w, -, rfl⟩ := Submonoid.mem_map.mp hy
    exact Submonoid.mem_map.mpr ⟨w, by simp, rfl⟩
  have hdegS : ∀ x ∈ img ρ ⊤, Deg n x := fun x hx => by
    obtain ⟨w, -, rfl⟩ := Submonoid.mem_map.mp hx
    exact hDeg w
  have hRZ : R ∈ Zcl (img ρ ⊤ : Set (Mat C N)) :=
    zcl_sub _ (Submonoid.mem_map.mpr ⟨g, by simp, rfl⟩)
  have hyZ : R * u * t ∈ Zcl (img ρ ⊤ : Set (Mat C N)) := by
    rw [mul_assoc]; exact hZM C N _ R hRZ _ (zcl_mono himg hmZ)
  have hyDeg := (hTD C N n (img ρ ⊤) hdegS).1 _ hyZ
  obtain ⟨hEig, hfix⟩ := hCC C N n p (R * u * t) π hS hyU hyp hyDeg hdisj
  refine ⟨⟨u * t, hmZ, by rw [← mul_assoc]; exact hEig⟩, ?_⟩
  rintro i ⟨a, haA, hne⟩
  have ha' : Ri * a * R ∈ A := by have := hNo g⁻¹ a haA; rwa [inv_inv] at this
  have hπi : π i = i := by
    refine hπ i ⟨Ri * a * R, ha', fun h => hne ?_⟩
    have := congrArg (fun Y => R * Y) h
    simp only [mul_assoc, h1, mul_zero] at this
    simpa [mul_assoc] using this
  obtain ⟨c, hc⟩ := hfix i hπi
  have hpy : p i * (R * u * t) = c • p i := by rw [← hc, hyp i, hπi]
  obtain ⟨vi, hviA, hvvi⟩ := inv_in A hvA hvU
  set D := ∑ j, d j • p j
  set T' := ∑ j, (τ j)⁻¹ • p j
  have hm1 : u * t * (T' * D * vi) = 1 := by
    have ht' : ∀ X, t * (T' * X) = X := fun X => by rw [← mul_assoc, hTT', one_mul]
    have hd' : ∀ X, (∑ j, (d j)⁻¹ • p j) * (D * X) = X := fun X => by rw [← mul_assoc, hD'D, one_mul]
    rw [hu]; simp only [mul_assoc, ht', hd', hvvi]
  refine ⟨c • (T' * D * vi), Subalgebra.smul_mem _ (Subalgebra.mul_mem _ (Subalgebra.mul_mem _
    (sum_mem A hCo.1 _) (sum_mem A hCo.1 _)) hviA) _, ?_⟩
  calc p i * R = p i * R * (u * t * (T' * D * vi)) := by rw [hm1, mul_one]
    _ = p i * (R * u * t) * (T' * D * vi) := by simp only [mul_assoc]
    _ = p i * (c • (T' * D * vi)) := by rw [hpy, smul_mul_assoc, mul_smul_comm]

end LateralTheory.DivDb.KeyPf
end

section

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.DiagScalar₂
open LateralTheory.DivDb

variable {C : Type} [Field C] {N n : ℕ}

theorem mul_p (p : Fin n → Mat C N) (hp : Sys p) (e : Fin n → C) (j : Fin n) :
    (∑ i, e i • p i) * p j = e j • p j := by
  rw [Finset.sum_mul, Finset.sum_eq_single j]
  · rw [smul_mul_assoc, (hp.1.idem j).eq]
  · intro b _ hb; rw [smul_mul_assoc, hp.1.ortho hb, smul_zero]
  · simp

theorem p_mul (p : Fin n → Mat C N) (hp : Sys p) (e : Fin n → C) (j : Fin n) :
    p j * (∑ i, e i • p i) = e j • p j := by
  rw [Finset.mul_sum, Finset.sum_eq_single j]
  · rw [mul_smul_comm, (hp.1.idem j).eq]
  · intro b _ hb; rw [mul_smul_comm, hp.1.ortho (Ne.symm hb), smul_zero]
  · simp

theorem vec_of (p : Fin n → Mat C N) (hp : Sys p) (i : Fin n) (v : Fin N → C)
    (hv : ∀ k, k ≠ i → p k *ᵥ v = 0) : p i *ᵥ v = v := by
  have h1 : (∑ k, p k) *ᵥ v = v := by rw [hp.1.complete]; simp
  rw [Matrix.sum_mulVec, Finset.sum_eq_single i] at h1
  · exact h1
  · intro b _ hb; exact hv b hb
  · simp

theorem X_vec (p : Fin n → Mat C N) (hp : Sys p) (e : Fin n → C) (i : Fin n) (v : Fin N → C)
    (hv : ∀ k, k ≠ i → p k *ᵥ v = 0) : (∑ k, e k • p k) *ᵥ v = e i • v := by
  have h := vec_of p hp i v hv
  conv_lhs => rw [← h]
  rw [Matrix.mulVec_mulVec, mul_p p hp e i, Matrix.smul_mulVec, h]

theorem root_of_eig (Y : Mat C N) (μ : C) (v : Fin N → C) (hv : v ≠ 0) (h : Y *ᵥ v = μ • v) :
    Y.charpoly.IsRoot μ := by
  rw [Polynomial.IsRoot, Matrix.eval_charpoly, ← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨v, hv, ?_⟩
  rw [Matrix.sub_mulVec, h, Matrix.scalar_apply]
  ext k; simp [Matrix.mulVec_diagonal]

theorem deg_shift (x : Mat C N) (c : C) (h : Deg n x) : Deg n (x + algebraMap C (Mat C N) c) := by
  obtain ⟨q, hq, hd, ha⟩ := h
  refine ⟨Polynomial.taylor (-c) q, ?_, ?_, ?_⟩
  · rwa [Ne, Polynomial.taylor_eq_zero]
  · rwa [Polynomial.natDegree_taylor]
  · rw [Polynomial.taylor_apply, Polynomial.aeval_comp]
    simp [ha]

theorem alg_vec (c : C) (v : Fin N → C) : (algebraMap C (Mat C N) c) *ᵥ v = c • v := by
  rw [Matrix.algebraMap_eq_diagonal]; ext k; simp [Matrix.mulVec_diagonal]

end LateralTheory.DivDb.DiagScalar₂

namespace LateralTheory.DivDb
open DiagScalar₂ in
theorem DiagScalar_of (hC : CycleCount) : DiagScalar := by
  intro C _ _ _ N n p e Y hp he hY hD i
  classical
  have : Infinite C := Infinite.of_injective _ Nat.cast_injective
  set X := ∑ i, e i • p i with hX
  set R := Y.charpoly.roots.toFinset with hR
  set B : Finset C := insert 0 ((R ×ˢ R ×ˢ (Finset.univ : Finset (Fin n)) ×ˢ (Finset.univ : Finset (Fin n))).image
    (fun t => (e t.2.2.2 - e t.2.2.1) / (t.1 - t.2.1))) with hB
  obtain ⟨s, hs⟩ := Infinite.exists_notMem_finset B
  have hs0 : s ≠ 0 := fun h => hs (h ▸ Finset.mem_insert_self _ _)
  set M := s • Y + X with hM
  obtain ⟨c', hc'⟩ := Infinite.exists_notMem_finset ((-M).charpoly.roots.toFinset)
  set y := M + algebraMap C (Mat C N) c' with hy
  have hunit : IsUnit y := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    intro h0; apply hc'
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero, Polynomial.IsRoot,
      Matrix.eval_charpoly]
    convert h0 using 2
    rw [hy, Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply, sub_neg_eq_add, add_comm]; rfl
  have hcomm : ∀ j, y * p j = p ((1 : Equiv.Perm (Fin n)) j) * y := by
    intro j
    rw [Equiv.Perm.one_apply, hy, hM, add_mul, add_mul, mul_add, mul_add, smul_mul_assoc, mul_smul_comm, hY j,
      hX, mul_p p hp e j, p_mul p hp e j, Algebra.commutes]
  have hdeg : Deg n y := deg_shift _ c' (hD s)
  have key : ∀ (i : Fin n) (l : C) (v : Fin N → C), v ≠ 0 → y *ᵥ v = l • v →
      (∀ k, ¬ i = k → p k *ᵥ v = 0) → ∃ μ ∈ R, s * μ + e i = l - c' := by
    intro i l v hv hyv hpv
    have hXv := X_vec p hp e i v (fun k hk => hpv k (Ne.symm hk))
    have h1 : y *ᵥ v = s • (Y *ᵥ v) + e i • v + c' • v := by
      rw [hy, hM, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, hX, hXv, alg_vec]
    rw [h1] at hyv
    have h2 : s • (Y *ᵥ v) = (l - c' - e i) • v := by rw [sub_smul, sub_smul, ← hyv]; abel
    refine ⟨s⁻¹ * (l - c' - e i), ?_, by field_simp; ring⟩
    rw [hR, Multiset.mem_toFinset, Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero]
    apply root_of_eig Y _ v hv
    rw [mul_smul, ← h2, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  have hdisj : Disj y 1 p := by
    intro i j hij l v w hv hw hyv hyw hpv hpw
    simp only [Equiv.Perm.sameCycle_one] at hij hpv hpw
    obtain ⟨μ, hμ, h1⟩ := key i l v hv hyv hpv
    obtain ⟨μ', hμ', h2⟩ := key j l w hw hyw hpw
    have hne : e i ≠ e j := he.ne hij
    have hμμ : μ - μ' ≠ 0 := by
      intro h; apply hne
      have : μ = μ' := sub_eq_zero.mp h
      subst this; linear_combination h1 - h2
    apply hs
    apply Finset.mem_insert_of_mem
    rw [Finset.mem_image]
    refine ⟨(μ, μ', i, j), by simp [hμ, hμ'], ?_⟩
    show (e j - e i) / (μ - μ') = s
    rw [div_eq_iff hμμ]; linear_combination h2 - h1
  obtain ⟨_, hfix⟩ := hC C N n p y 1 hp hunit hcomm hdeg hdisj
  obtain ⟨c, hc⟩ := hfix i rfl
  refine ⟨s⁻¹ * (c - e i - c'), ?_⟩
  have h4 : y * p i = s • (Y * p i) + e i • p i + c' • p i := by
    rw [hy, hM, add_mul, add_mul, smul_mul_assoc, hX, mul_p p hp e i, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
      one_mul]
  rw [h4] at hc
  have h3 : s • (Y * p i) = (c - e i - c') • p i := by rw [sub_smul, sub_smul, ← hc]; abel
  rw [mul_smul, ← h3, smul_smul, inv_mul_cancel₀ hs0, one_smul]

end LateralTheory.DivDb
end
