module

public import Formalism.WeaklyAdmissibleFiltrations.Bundle001
public import Mathlib.NumberTheory.Padics.RingHoms
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module TensorProduct GlobalTheory.CompanionTheory.LocDual

namespace PositivityTheory.LocalTateOrthogonality.Bk

theorem le_of_growth {q a b C : ℕ} (hq : 2 ≤ q) (h : ∀ r : ℕ, q ^ (r * a) ≤ C * q ^ (r * b)) :
    a ≤ b := by
  by_contra hab
  have hba : b + 1 ≤ a := by omega
  have hq0 : 0 < q := by omega
  have h1 := h C
  have h2 : q ^ (C * (b + 1)) ≤ q ^ (C * a) :=
    Nat.pow_le_pow_right hq0 (Nat.mul_le_mul_left _ hba)
  have h3 : q ^ (C * b) * q ^ C ≤ q ^ (C * b) * C := by
    calc q ^ (C * b) * q ^ C = q ^ (C * (b + 1)) := by rw [Nat.mul_add, Nat.mul_one, pow_add]
      _ ≤ C * q ^ (C * b) := h2.trans h1
      _ = q ^ (C * b) * C := by ring
  have h4 : q ^ C ≤ C := Nat.le_of_mul_le_mul_left h3 (pow_pos hq0 _)
  have h5 : C < q ^ C := Nat.lt_pow_self (by omega)
  omega

theorem growth_le {q a h h' n m C C' : ℕ} (hq : 2 ≤ q)
    (H : ∀ r : ℕ, ∃ x x' y : ℕ, x ≤ C * q ^ (r * h) ∧ x' ≤ C' * q ^ (r * h') ∧ q ^ (r * a) ≤ y ∧
      y = x * x' * q ^ (r * n * m)) : a ≤ h + h' + n * m := by
  refine le_of_growth (C := C * C') hq fun r => ?_
  obtain ⟨x, x', y, hx, hx', hy, e⟩ := H r
  rw [Nat.mul_assoc r] at e
  calc q ^ (r * a) ≤ y := hy
    _ = x * x' * q ^ (r * (n * m)) := e
    _ ≤ (C * q ^ (r * h)) * (C' * q ^ (r * h')) * q ^ (r * (n * m)) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul hx hx')
    _ = C * C' * q ^ (r * (h + h' + n * m)) := by
        rw [Nat.mul_add, Nat.mul_add, pow_add, pow_add]; ring

theorem stable_pow {G : Type} [Group G] {LL O V : Type} [Field LL] [CommRing O] [Algebra O LL]
    [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    (L : Lattice (O := O) ρ) (ϖ : O) (r : ℕ) :
    StableSub L (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T) := by
  intro g x hx
  have h := Submodule.mem_map_of_mem (f := actT L g) hx
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h


end PositivityTheory.LocalTateOrthogonality.Bk
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

namespace PositivityTheory.LocalTateOrthogonality.Bk.Eul

section Act

variable {G : Type} [Group G] {Qp LL O V : Type} [Field Qp] [Field LL] [Algebra Qp LL] [CommRing O]
  [Algebra O LL] [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [Module O V]
  [IsScalarTower O LL V] {ρ : Representation LL G V}

theorem actQ_one' (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I)
    (m : ↥L.T ⧸ I) : actQ L I hI 1 m = m := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  change Submodule.Quotient.mk (actT L 1 x) = _
  congr 1
  apply Subtype.ext
  change ρ 1 (x : V) = x
  simp

theorem actQ_mul' (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I)
    (g h : G) (m : ↥L.T ⧸ I) : actQ L I hI (g * h) m = actQ L I hI g (actQ L I hI h m) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  change Submodule.Quotient.mk (actT L (g * h) x) = Submodule.Quotient.mk (actT L g (actT L h x))
  congr 1
  apply Subtype.ext
  change ρ (g * h) (x : V) = ρ g (ρ h x)
  simp [Module.End.mul_apply]

end Act

theorem psi_unit {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (ι : ℤ_[l] →+* O) (J : Ideal O)
    (n : ℕ) (hN : ((l ^ n : ℕ) : O) ∈ J) (ψ : (O ⧸ J) →+ ZMod (l ^ n)) (u : ℤ_[l]) (p : O) :
    ψ (Ideal.Quotient.mk J (ι u * p)) = PadicInt.toZModPow n u * ψ (Ideal.Quotient.mk J p) := by
  have hl : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  set m : ℕ := (PadicInt.toZModPow n u : ZMod (l ^ n)).val with hm
  have hmc : ((m : ℕ) : ZMod (l ^ n)) = PadicInt.toZModPow n u := ZMod.natCast_zmod_val _
  have hk : u - (m : ℤ_[l]) ∈ Ideal.span {(l : ℤ_[l]) ^ n} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, hmc, sub_self]
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 hk
  have hu : u = (m : ℤ_[l]) + v * (l : ℤ_[l]) ^ n := by rw [hv]; ring
  have h2 : Ideal.Quotient.mk J (ι u * p) = m • Ideal.Quotient.mk J p := by
    rw [← map_nsmul, Ideal.Quotient.eq]
    have : ι u * p - m • p = (ι v * p) * ((l ^ n : ℕ) : O) := by
      rw [hu]
      simp only [map_add (f := _), map_mul, map_pow, map_natCast, nsmul_eq_mul, Nat.cast_pow]
      ring
    rw [this]
    exact J.mul_mem_left _ hN
  rw [h2, map_nsmul, nsmul_eq_mul, hmc]

theorem exists_pair {O W W' : Type} [CommRing O] [AddCommGroup W] [Module O W] [AddCommGroup W']
    [Module O W'] (J : Ideal O) (N : ℕ) (B : W →ₗ[O] W' →ₗ[O] (O ⧸ J)) (ψ₀ : (O ⧸ J) →+ ZMod N)
    (hψ : ∀ x, (∀ o, ψ₀ (o * x) = 0) → x = 0) (hBl : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hBr : ∀ y, (∀ x, B x y = 0) → y = 0) :
    ∃ Pb : W →+ W' →+ ZMod N, (∀ x y, Pb x y = ψ₀ (B x y)) ∧ (∀ x, (∀ y, Pb x y = 0) → x = 0) ∧
      ∀ y, (∀ x, Pb x y = 0) → y = 0 := by
  have hsm : ∀ (o : O) (b : O ⧸ J), Ideal.Quotient.mk J o * b = o • b := fun o b => by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_mul]
    rfl
  refine ⟨AddMonoidHom.mk' (fun x => ψ₀.comp (B x).toAddMonoidHom) (fun x y => by
    ext z
    simp), fun _ _ => rfl, fun x hx => hBl x fun y => hψ _ fun o => ?_,
    fun y hy => hBr y fun x => hψ _ fun o => ?_⟩
  · obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective o
    rw [hsm, ← map_smul]
    exact hx _
  · obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective o
    rw [hsm, ← LinearMap.smul_apply, ← map_smul]
    exact hy _

theorem quot_killed {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (J : Ideal O) (N : ℕ)
    (hN : (N : O) ∈ J) (m : M ⧸ (J • ⊤ : Submodule O M)) : N • m = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, ← Nat.cast_smul_eq_nsmul O]
  exact Submodule.smul_mem_smul hN trivial

theorem final_count (h1 w z h0 h0' q a d : ℕ) (hw : 0 < w) (hq : w = q ^ a)
    (hC : h1 * w = z * h0) (hZ : z = h0' * w ^ (d + 1)) : h1 = h0 * h0' * q ^ (a * d) := by
  apply Nat.eq_of_mul_eq_mul_right hw
  rw [hC, hZ, pow_succ, pow_mul, ← hq]
  ring


end PositivityTheory.LocalTateOrthogonality.Bk.Eul
end
