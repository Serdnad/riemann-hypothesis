module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle002
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.LogAbsVpOfNormalised

@[expose] public section

section

noncomputable section

open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat Matrix TensorProduct

namespace GlobalTheory.SelfDualFil

theorem isRegular_of_mul_eq_smul {A : Type} [CommRing A] [IsDomain A] {h : ℕ}
    {M N : Matrix (Fin h) (Fin h) A} {c : A} (hc : c ≠ 0)
    (H : M * N = c • (1 : Matrix (Fin h) (Fin h) A)) : IsRegular M ∧ IsRegular N := by
  have hd : M.det * N.det ≠ 0 := by
    rw [← Matrix.det_mul, H, Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ hc
  exact ⟨Matrix.isRegular_of_isLeftRegular_det (IsRegular.of_ne_zero (left_ne_zero_of_mul hd)).1,
    Matrix.isRegular_of_isLeftRegular_det (IsRegular.of_ne_zero (right_ne_zero_of_mul hd)).1⟩

theorem mul_eq_smul_comm {A : Type} [CommRing A] [IsDomain A] {h : ℕ}
    {M N : Matrix (Fin h) (Fin h) A} {c : A} (hc : c ≠ 0)
    (H : M * N = c • (1 : Matrix (Fin h) (Fin h) A)) :
    N * M = c • (1 : Matrix (Fin h) (Fin h) A) := by
  apply (isRegular_of_mul_eq_smul hc H).1.1
  show M * (N * M) = M * (c • 1)
  rw [← Matrix.mul_assoc, H]
  simp

section

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] {ε : PreTilt O p} {h : ℕ} {Γ : Type} [CommRing Γ]
  [Algebra ℤ_[p] Γ]

theorem G_eq [IsDomain (Ainf p O)] (hμ : mu ε ≠ 0) (hξ : xi ε ≠ 0) (D : Datum ε h Γ) :
    D.G = D.G.map (phiInv p O) * D.Ψ' := by
  apply (isRegular_of_mul_eq_smul hμ D.G_mul_F).2.2
  show D.G * D.F = D.G.map (phiInv p O) * D.Ψ' * D.F
  have e1 : D.G.map (phiInv p O) * D.F.map (phiInv p O) = nu ε • 1 := by
    rw [← Matrix.map_mul, D.G_mul_F]
    ext1 i j
    by_cases hij : i = j <;> simp [hij, phiInv_mu]
  have e2 : D.Ψ' * D.F = xi ε • D.F.map (phiInv p O) := by
    conv_lhs => rw [D.F_eq]
    rw [← Matrix.mul_assoc, mul_eq_smul_comm hξ D.Ψ_mul]
    simp
  rw [Matrix.mul_assoc, e2, Matrix.mul_smul, e1, smul_smul, xi_mul_nu, D.G_mul_F]

def dualDatum [IsDomain (Ainf p O)] (hμ : mu ε ≠ 0) (hξ : xi ε ≠ 0) (D : Datum ε h Γ) :
    Datum ε h ℤ_[p] where
  F := D.Gᵀ
  G := D.Fᵀ
  Ψ := D.Ψ'ᵀ
  Ψ' := D.Ψᵀ
  ρT := (etale ε h).ρT
  ρM := (etale ε h).ρM
  G_mul_F := by rw [← Matrix.transpose_mul, D.G_mul_F]; simp
  F_eq := by
    rw [Matrix.transpose_map, ← Matrix.transpose_mul, ← G_eq hμ hξ D]
  Ψ_mul := by rw [← Matrix.transpose_mul, D.Ψ_mul]; simp
  F_act := by
    intro a
    have e : ((etale ε h).ρT a).map (ofPadic p O) = ofPadic p O a • 1 := by
      ext1 i j
      by_cases hij : i = j <;> simp [etale, Algebra.ofId_apply, Matrix.algebraMap_matrix_apply, hij]
    have e' : (etale ε h).ρM a = ofPadic p O a • 1 := by
      ext1 i j
      by_cases hij : i = j <;> simp [etale, Matrix.algebraMap_matrix_apply, hij]
    rw [e, e']
    simp

variable (C : Type) [Field C] [Algebra O C]

end

end GlobalTheory.SelfDualFil
end
end

section

noncomputable section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv.PsiPhi

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem phiInv_ofPadic (c : ℤ_[p]) : phiInv p O (ofPadic p O c) = ofPadic p O c := by
  have key : ((_root_.frobeniusEquiv (PreTilt O p) p).symm : PreTilt O p →+* PreTilt O p).comp
      (ZMod.castHom (dvd_refl p) (PreTilt O p)) = ZMod.castHom (dvd_refl p) (PreTilt O p) :=
    Subsingleton.elim _ _
  simp only [phiInv, ofPadic, RingHom.comp_apply]
  ext n
  simp only [WittVector.map_coeff]
  exact RingHom.congr_fun key _

end GlobalTheory.DetInv.PsiPhi

namespace GlobalTheory.DetInv

end GlobalTheory.DetInv
end
end

section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory

theorem padicInt_ringHom_ext (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O]
    [IsHausdorff (Ideal.span {(p : O)}) O] (f g : ℤ_[p] →+* O) : f = g := by
  ext x
  rw [← sub_eq_zero]
  apply IsHausdorff.haus (I := Ideal.span {(p : O)}) ‹_›
  intro n
  rw [SModEq.zero]
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp (PadicInt.appr_spec n x)
  have hx : x = (x.appr n : ℤ_[p]) + y * (p : ℤ_[p]) ^ n := by rw [hy]; ring
  have hfx : f x - g x = (f y - g y) * (p : O) ^ n := by
    rw [hx, map_add (f := _), map_add (f := _), map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast,
      map_natCast, map_natCast]
    ring
  rw [hfx, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  exact Ideal.mem_span_singleton'.mpr ⟨f y - g y, rfl⟩

theorem padicToO_unique : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (g : ℤ_[p] →+* O), g = padicToO p O := by
  intro p _ O _ _ _ g
  exact padicInt_ringHom_ext p O g (padicToO p O)

end GlobalTheory
end

section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem _root_.GlobalTheory.ainf_isDomain_and_mu_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (_root_.GlobalTheory.Sandwich.root ε).untilt p → IsDomain (_root_.GlobalTheory.Sandwich.Ainf p O) ∧ _root_.GlobalTheory.Sandwich.mu ε ≠ 0 := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hprim
  haveI : IsDomain (PreTilt O p) := PreTilt.isDomain C v O hv p
  refine ⟨by unfold _root_.GlobalTheory.Sandwich.Ainf; infer_instance, ?_⟩
  intro h
  unfold _root_.GlobalTheory.Sandwich.mu at h
  have h1 : WittVector.teichmuller p ε = 1 := sub_eq_zero.mp h
  have hε : ε = 1 := by
    have := congrArg (fun x => WittVector.coeff x 0) h1
    simpa [WittVector.teichmuller_coeff_zero] using this
  have hroot : _root_.GlobalTheory.Sandwich.root ε = 1 := by
    unfold _root_.GlobalTheory.Sandwich.root
    rw [hε, map_one]
  rw [hroot, map_one] at hprim
  exact (Fact.out : p.Prime).one_lt.ne' (IsPrimitiveRoot.one_left_iff.mp hprim)

end GlobalTheory
end

section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv


open Matrix TensorProduct in
theorem _root_.GlobalTheory.DetInv.mu_coeff_zero_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C]
    [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O →
    ∀ (ε : PreTilt O p), IsPrimitiveRoot (_root_.GlobalTheory.Sandwich.root ε).untilt p →
      (_root_.GlobalTheory.Sandwich.mu ε).coeff 0 ≠ 0 ∧ _root_.GlobalTheory.Sandwich.mu ε ≠ 0 ∧
        _root_.GlobalTheory.Sandwich.nu ε ≠ 0 := by
  intro p _ C _ _ _ v O _ _ _ _ _ ε hζ
  have hε : ε ≠ 1 := by
    rintro rfl
    have h1 : _root_.GlobalTheory.Sandwich.root (1 : PreTilt O p) = 1 := by
      unfold _root_.GlobalTheory.Sandwich.root
      exact map_one _
    have h2 : PreTilt.untilt (1 : PreTilt O p) = 1 := by simp
    rw [h1, h2] at hζ
    have hp : p ∣ 1 := (hζ.pow_eq_one_iff_dvd 1).mp (pow_one 1)
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp hp)
  have hc : (_root_.GlobalTheory.Sandwich.mu ε).coeff 0 ≠ 0 := by
    unfold _root_.GlobalTheory.Sandwich.mu
    rw [← WittVector.constantCoeff_apply, map_sub, map_one, WittVector.constantCoeff_apply,
      WittVector.teichmuller_coeff_zero]
    exact sub_ne_zero.mpr hε
  have hmu : _root_.GlobalTheory.Sandwich.mu ε ≠ 0 := by
    intro h
    apply hc
    rw [h]
    exact WittVector.zero_coeff _ _ _
  refine ⟨hc, hmu, fun h => hmu ?_⟩
  rw [← _root_.GlobalTheory.Sandwich.xi_mul_nu, h, mul_zero]

end GlobalTheory.DetInv
end
