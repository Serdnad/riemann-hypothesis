module

public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.Algebra.Group.End
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Tactic.ToDual
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Ring.Defs

@[expose] public section

section

open MvPolynomial

namespace GlobalTheory

theorem mem_polyring_of_integral_closure_range : ∀ {K : Type} [Field K] {D : ℕ} (y : Fin D → K), AlgebraicIndependent ℤ y → ∀ (t : K), t ∈ Subfield.closure (Set.range y) → ∀ {ι : Type} (z : ι → K), (∀ i, ∃ p : MvPolynomial (Fin D) ℤ, aeval y p = z i) → ∀ (f : Polynomial (MvPolynomial ι ℤ)), f.Monic → f.eval₂ (aeval z).toRingHom t = 0 → ∃ T₀ : MvPolynomial (Fin D) ℤ, t = aeval y T₀ := by
  intro K _ D y hy t ht ι z hz f hf hft
  choose p hp using hz
  set F := Subfield.closure (Set.range y) with hF
  have hsub : ∀ u : K, u ∈ Subring.closure (Set.range y) ↔ ∃ q : MvPolynomial (Fin D) ℤ, aeval y q = u := by
    intro u
    have e1 : u ∈ Subring.closure (Set.range y) ↔ u ∈ Algebra.adjoin ℤ (Set.range y) := by
      rw [Algebra.adjoin_int]; rfl
    rw [e1, Algebra.adjoin_range_eq_range_aeval]
    rfl
  have hmem : ∀ q : MvPolynomial (Fin D) ℤ, aeval y q ∈ F := by
    intro q
    exact Subfield.subring_closure_le _ ((hsub _).mpr ⟨q, rfl⟩)
  let φ : MvPolynomial (Fin D) ℤ →+* F := (aeval y).toRingHom.codRestrict F hmem
  letI : Algebra (MvPolynomial (Fin D) ℤ) F := φ.toAlgebra
  have hφ : ∀ q, ((algebraMap (MvPolynomial (Fin D) ℤ) F q : F) : K) = aeval y q := fun q => rfl
  have hinj : Function.Injective (aeval y : MvPolynomial (Fin D) ℤ →ₐ[ℤ] K) :=
    algebraicIndependent_iff_injective_aeval.mp hy
  haveI : FaithfulSMul (MvPolynomial (Fin D) ℤ) F := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b h
    apply hinj
    rw [← hφ a, ← hφ b, h]
  haveI : IsFractionRing (MvPolynomial (Fin D) ℤ) F := by
    refine IsFractionRing.of_field _ _ ?_
    intro w
    obtain ⟨u, hu, v, hv, huv⟩ := Subfield.mem_closure_iff.mp w.2
    obtain ⟨a, ha⟩ := (hsub u).mp hu
    obtain ⟨b, hb⟩ := (hsub v).mp hv
    refine ⟨a, b, ?_⟩
    apply Subtype.ext
    simp only [Subfield.coe_div, hφ, ha, hb, huv]
  haveI : IsIntegrallyClosed (MvPolynomial (Fin D) ℤ) :=
    UniqueFactorizationMonoid.instIsIntegrallyClosed
  have hcomp : (aeval y).toRingHom.comp (bind₁ p).toRingHom = (aeval z).toRingHom := by
    refine RingHom.ext fun q => ?_
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_bind₁]
    have : (fun i => aeval y (p i)) = z := funext hp
    rw [this]
  let t' : F := ⟨t, ht⟩
  have hint : IsIntegral (MvPolynomial (Fin D) ℤ) t' := by
    refine ⟨f.map (bind₁ p).toRingHom, hf.map _, ?_⟩
    apply Subtype.val_injective
    have h1 := Polynomial.hom_eval₂ (f.map (bind₁ p).toRingHom) (algebraMap (MvPolynomial (Fin D) ℤ) F) F.subtype t'
    show F.subtype (Polynomial.eval₂ _ t' _) = F.subtype 0
    rw [h1, map_zero]
    have h2 : F.subtype.comp (algebraMap (MvPolynomial (Fin D) ℤ) F) = (aeval y).toRingHom := by
      exact RingHom.ext fun q => rfl
    rw [h2, Polynomial.eval₂_map, hcomp]
    exact hft
  obtain ⟨T₀, hT⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact ⟨T₀, by rw [← hφ, hT]⟩

end GlobalTheory
end

section

open Equiv

theorem GlobalTheory.perm_invariant_of_cons_swap :
  ∀ (α : Type 1) (n : ℕ) (F : (Fin (n + 2) → α) → ℝ), (∀ (a : α) (L : Fin (n + 1) → α) (e : Equiv.Perm (Fin (n + 1))), F (Fin.cons a fun i => L (e i)) = F (Fin.cons a L)) → (∀ (a b : α) (L : Fin n → α), F (Fin.cons a (Fin.cons b L : Fin (n + 1) → α)) = F (Fin.cons b (Fin.cons a L : Fin (n + 1) → α))) → ∀ (L : Fin (n + 2) → α) (e : Equiv.Perm (Fin (n + 2))), F (fun i => L (e i)) = F L := by
  intro α n F h1 h2
  let S : Subgroup (Equiv.Perm (Fin (n+2))) :=
    { carrier := {σ | ∀ L : Fin (n+2) → α, F (fun i => L (σ i)) = F L}
      mul_mem' := by
        intro σ τ hσ hτ
        have hσ' : ∀ L : Fin (n+2) → α, F (fun i => L (σ i)) = F L := hσ
        have hτ' : ∀ L : Fin (n+2) → α, F (fun i => L (τ i)) = F L := hτ
        show ∀ L : Fin (n+2) → α, F (fun i => L ((σ * τ) i)) = F L
        intro L
        calc F (fun i => L ((σ * τ) i)) = F (fun i => L (σ (τ i))) := rfl
          _ = F (fun j => L (σ j)) := hτ' (fun j => L (σ j))
          _ = F L := hσ' L
      one_mem' := by
        show ∀ L : Fin (n+2) → α, F (fun i => L ((1 : Equiv.Perm (Fin (n+2))) i)) = F L
        intro L; rfl
      inv_mem' := by
        intro σ hσ
        have hσ' : ∀ L : Fin (n+2) → α, F (fun i => L (σ i)) = F L := hσ
        show ∀ L : Fin (n+2) → α, F (fun i => L (σ⁻¹ i)) = F L
        intro L
        calc F (fun i => L (σ⁻¹ i)) = F (fun i => L (σ⁻¹ (σ i))) := (hσ' (fun j => L (σ⁻¹ j))).symm
          _ = F L := by simp }
  have memS : ∀ σ, σ ∈ S ↔ ∀ L : Fin (n+2) → α, F (fun i => L (σ i)) = F L := fun σ => Iff.rfl
  have hfix : ∀ e : Equiv.Perm (Fin (n+1)), Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), e) ∈ S := by
    intro e
    rw [memS]
    intro L
    have hc : (fun i => L (Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), e) i)) = Fin.cons (L 0) (fun i => Fin.tail L (e i)) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp [Equiv.Perm.decomposeFin_symm_apply_succ, Fin.tail]
    rw [hc, h1 (L 0) (Fin.tail L) e, Fin.cons_self_tail]
  have hswap : Equiv.swap (0 : Fin (n+2)) 1 ∈ S := by
    rw [memS]
    intro L
    have e1 : L = Fin.cons (L 0) (Fin.cons (L 1) (fun i => L i.succ.succ) : Fin (n+1) → α) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · refine Fin.cases ?_ (fun k => ?_) j
        · rfl
        · rfl
    have e2 : (fun i => L (Equiv.swap (0 : Fin (n+2)) 1 i)) = Fin.cons (L 1) (Fin.cons (L 0) (fun i => L i.succ.succ) : Fin (n+1) → α) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · refine Fin.cases ?_ (fun k => ?_) j
        · simp
        · have a1 : (k.succ.succ : Fin (n+2)) ≠ 0 := Fin.succ_ne_zero _
          have a2 : (k.succ.succ : Fin (n+2)) ≠ 1 := by
            intro h
            rw [← Fin.succ_zero_eq_one] at h
            exact Fin.succ_ne_zero _ (Fin.succ_injective _ h)
          simp [Equiv.swap_apply_of_ne_of_ne a1 a2]
    rw [e2, ← h2 (L 0) (L 1)]
    exact congrArg F e1.symm
  have hp : ∀ p : Fin (n+2), Equiv.swap (0 : Fin (n+2)) p ∈ S := by
    intro p
    refine Fin.cases ?_ (fun k => ?_) p
    · rw [Equiv.swap_self]; exact S.one_mem
    · have h0 : Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), Equiv.swap (0 : Fin (n+1)) k) 0 = 0 := by simp
      have h1' : Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), Equiv.swap (0 : Fin (n+1)) k) 1 = k.succ := by
        rw [← Fin.succ_zero_eq_one, Equiv.Perm.decomposeFin_symm_apply_succ]
        simp
      have hc := Equiv.swap_apply_apply (Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), Equiv.swap (0 : Fin (n+1)) k)) 0 1
      rw [h0, h1'] at hc
      rw [hc]
      exact S.mul_mem (S.mul_mem (hfix _) hswap) (S.inv_mem (hfix _))
  have hdec : ∀ (p : Fin (n+2)) (e : Equiv.Perm (Fin (n+1))),
      Equiv.Perm.decomposeFin.symm (p, e) = Equiv.swap 0 p * Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), e) := by
    intro p e
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [Equiv.Perm.decomposeFin_symm_apply_succ]
  intro L e
  have he : e ∈ S := by
    rw [← Equiv.Perm.decomposeFin.symm_apply_apply e]
    rcases Equiv.Perm.decomposeFin e with ⟨p, e'⟩
    rw [hdec]
    exact S.mul_mem (hp p) (hfix e')
  exact (memS e).1 he L
end

section

open Matrix Polynomial

namespace GlobalTheory

theorem reducedArtinian_exists_idem {R : Type} [CommRing R] [IsReduced R] [IsArtinianRing R]
    (a : R) : ∃ e b : R, e * e = e ∧ e = a * b ∧ a * e = a := by
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd a (1 : R)
  simp only [smul_eq_mul, mul_one, Nat.succ_eq_add_one] at hy
  have key : ∀ k : ℕ, a ^ n = a ^ (n + k) * y ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => linear_combination ih + (-(a ^ k * y ^ k)) * hy
  have hm : a ^ (n + 1) = a ^ (n + 1 + (n + 1)) * y ^ (n + 1) := by
    linear_combination a * key (n + 1)
  refine ⟨a ^ (n + 1) * y ^ (n + 1), a ^ n * y ^ (n + 1), ?_, by ring, ?_⟩
  · linear_combination (-(y ^ (n + 1))) * hm
  · have h0 : (1 - a ^ (n + 1) * y ^ (n + 1)) * a ^ (n + 1) = 0 := by linear_combination hm
    have hnil : IsNilpotent ((1 - a ^ (n + 1) * y ^ (n + 1)) * a) := by
      refine ⟨n + 1, ?_⟩
      rw [mul_pow, pow_succ (1 - a ^ (n + 1) * y ^ (n + 1)) n, mul_assoc, h0, mul_zero]
    have := hnil.eq_zero
    linear_combination -this

theorem reducedArtinian_involution_split :
    ∀ (R : Type) [CommRing R] [IsReduced R] [IsArtinianRing R] (σ : R →+* R), (∀ x, σ (σ x) = x) →
      ∃ e f : R, IsIdempotentElem e ∧ IsIdempotentElem f ∧ e * σ e = 0 ∧ e + σ e + f = 1 ∧
        ∀ w, w * σ w = 0 → w * f = 0 := by
  intro R _ _ _ σ hσ
  let S : Set (Ideal R) := {I | ∃ e : R, e * e = e ∧ e * σ e = 0 ∧ I = Ideal.span {1 - e - σ e}}
  have hS : S.Nonempty := ⟨_, 0, by simp, by simp, rfl⟩
  obtain ⟨I, ⟨e, he, heσ, rfl⟩, hmin⟩ := WellFounded.has_min wellFounded_lt S hS
  have hσe : σ e * σ e = σ e := by rw [← map_mul, he]
  set f := 1 - e - σ e with hfdef
  have hf : f * f = f := by linear_combination he + hσe + 2 * heσ
  have hσf : σ f = f := by simp only [hfdef, map_sub, map_one, hσ]; ring
  have hef : e * f = 0 := by linear_combination -he - heσ
  have hσef : σ e * f = 0 := by linear_combination -hσe - heσ
  refine ⟨e, f, he, hf, heσ, by ring, ?_⟩
  intro w hw
  by_contra hwf
  set w' := w * f with hw'def
  have hw'σ : w' * σ w' = 0 := by
    rw [hw'def, map_mul, hσf]; linear_combination (f * f) * hw
  obtain ⟨ε, a, hε, hεa, hw'ε⟩ := reducedArtinian_exists_idem w'
  have hεne : ε ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hw'ε; exact hwf hw'ε.symm
  have hεσ : ε * σ ε = 0 := by
    rw [hεa, map_mul]; linear_combination (a * σ a) * hw'σ
  have hw'f : w' * f = w' := by rw [hw'def, mul_assoc, hf]
  have hεf : ε * f = ε := by rw [hεa]; linear_combination a * hw'f
  have hσεf : σ ε * f = σ ε := by
    have := congrArg σ hεf; rw [map_mul, hσf] at this; exact this
  have hσε : σ ε * σ ε = σ ε := by rw [← map_mul, hε]
  have heε : e * ε = 0 := by linear_combination (-e) * hεf + ε * hef
  have heσε : e * σ ε = 0 := by linear_combination (-e) * hσεf + σ ε * hef
  have hσeε : σ e * ε = 0 := by linear_combination (-σ e) * hεf + ε * hσef
  have hmem : Ideal.span {1 - (e + ε) - σ (e + ε)} ∈ S :=
    ⟨e + ε, by linear_combination he + hε + 2 * heε,
      by rw [map_add (f := _)]; linear_combination heσ + heσε + hσeε + hεσ, rfl⟩
  apply hmin _ hmem
  have hff : f * (1 - (e + ε) - σ (e + ε)) = 1 - (e + ε) - σ (e + ε) := by
    rw [map_add (f := _)]; linear_combination hf - hεf - hσεf
  refine lt_of_le_of_ne ?_ ?_
  · rw [Ideal.span_singleton_le_span_singleton]
    exact ⟨_, hff.symm⟩
  · intro hEq
    have : f ∈ Ideal.span {1 - (e + ε) - σ (e + ε)} := by
      rw [hEq]; exact Ideal.mem_span_singleton_self f
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp this
    apply hεne
    have hεg : ε * (1 - (e + ε) - σ (e + ε)) = 0 := by
      rw [map_add (f := _)]; linear_combination -heε - hσeε - hε - hεσ
    linear_combination -hεf - ε * hc + c * hεg

end GlobalTheory
end

section

namespace GlobalTheory

theorem morse_inequality_arith (d : ℕ) (a b : ℤ) (h g : ℕ → ℕ) (C C' m₀ m₁ : ℕ)
    (H1 : ∀ m : ℕ, m₀ ≤ m → |((d + 1).factorial : ℤ) * (h m : ℤ) - a * (m : ℤ) ^ (d + 1)| ≤
      C * (((d + 1 : ℕ) : ℤ) * ((m : ℤ) + 1) ^ (d + 1 - 1)))
    (H2 : ∀ m : ℕ, m₁ ≤ m → |(d.factorial : ℤ) * (g m : ℤ) - b * (m : ℤ) ^ d| ≤
      C' * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)))
    (hab : ((d : ℤ) + 1) * b < a) : ∃ m : ℕ, 1 ≤ m ∧ m * g m < h m := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = C * (d + 1) + (d + 1) * C' * d := ⟨_, rfl⟩
  obtain ⟨m, hm0, hm1, hmK⟩ : ∃ m : ℕ, m₀ ≤ m ∧ m₁ ≤ m ∧ K * 2 ^ d + 1 ≤ m :=
    ⟨m₀ + m₁ + (K * 2 ^ d + 1), by omega, by omega, by omega⟩
  have hm : 1 ≤ m := le_trans (Nat.le_add_left 1 _) hmK
  refine ⟨m, hm, ?_⟩
  by_contra hcon
  have hcon' : (h m : ℤ) ≤ (m : ℤ) * g m := by exact_mod_cast not_lt.mp hcon
  have h1 := (abs_le.mp (H1 m hm0)).1
  have h2 := (abs_le.mp (H2 m hm1)).2
  rw [Nat.add_sub_cancel, Nat.factorial_succ] at h1
  push_cast at h1
  have hM : (1 : ℤ) ≤ m := by exact_mod_cast hm
  have hMK : (K : ℤ) * 2 ^ d + 1 ≤ m := by exact_mod_cast hmK
  have hKz : (K : ℤ) = C * ((d : ℤ) + 1) + (d + 1) * C' * d := by rw [hK]; push_cast; ring
  generalize (m : ℤ) = M at *
  have hF : (0 : ℤ) < d.factorial := by exact_mod_cast d.factorial_pos
  have hd : (0 : ℤ) ≤ d := by positivity
  have hA : M * ((d : ℤ) * (M + 1) ^ (d - 1)) ≤ d * (M + 1) ^ d := by
    rcases d with _ | e
    · simp
    · rw [Nat.add_sub_cancel, pow_succ]
      have : (0 : ℤ) ≤ ((e + 1 : ℕ) : ℤ) * (M + 1) ^ e := by positivity
      nlinarith
  have hP : (M + 1) ^ d ≤ 2 ^ d * M ^ d := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by linarith) d
  have hQ : 0 < M ^ d := by positivity
  have e1 : ((d : ℤ) + 1) * d.factorial * h m ≤ ((d : ℤ) + 1) * d.factorial * (M * g m) :=
    mul_le_mul_of_nonneg_left hcon' (by positivity)
  have e2 : ((d : ℤ) + 1) * M * ((d.factorial : ℤ) * g m - b * M ^ d) ≤
      ((d : ℤ) + 1) * M * (C' * ((d : ℤ) * (M + 1) ^ (d - 1))) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have e3 : ((d : ℤ) + 1) * C' * (M * ((d : ℤ) * (M + 1) ^ (d - 1))) ≤
      ((d : ℤ) + 1) * C' * (d * (M + 1) ^ d) :=
    mul_le_mul_of_nonneg_left hA (by positivity)
  have e4 : (K : ℤ) * (M + 1) ^ d ≤ K * (2 ^ d * M ^ d) :=
    mul_le_mul_of_nonneg_left hP (by positivity)
  have e5 : ((K : ℤ) * 2 ^ d + 1) * M ^ d ≤ M * M ^ d :=
    mul_le_mul_of_nonneg_right hMK hQ.le
  have e6 : (((d : ℤ) + 1) * b + 1) * (M * M ^ d) ≤ a * (M * M ^ d) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have e7 : (K : ℤ) * (M + 1) ^ d =
      C * ((d + 1) * (M + 1) ^ d) + ((d : ℤ) + 1) * C' * (d * (M + 1) ^ d) := by
    rw [hKz]; ring
  rw [pow_succ' M d] at h1
  linarith

end GlobalTheory
end

section

namespace GlobalTheory.VSubArith

theorem sq_le_two_pow_add_one (v : ℕ) : v * v ≤ 2 ^ v + 1 := by
  have key : ∀ k : ℕ, (k + 4) * (k + 4) ≤ 2 ^ (k + 4) ∧ 2 * (k + 4) + 1 ≤ 2 ^ (k + 4) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      obtain ⟨h1, h2⟩ := ih
      rw [show k + 1 + 4 = (k + 4) + 1 by ring, pow_succ]
      constructor <;> nlinarith
  rcases Nat.lt_or_ge v 4 with h | h
  · interval_cases v <;> norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, v = k + 4 := ⟨v - 4, by omega⟩
    exact le_trans (key k).1 (Nat.le_succ _)

theorem two_mul_le_sq_add_sq (v L : ℕ) : 2 * (v * L) ≤ v * v + L * L := by
  have h : (2 * (v * L) : ℤ) ≤ v * v + L * L := by nlinarith [sq_nonneg ((v : ℤ) - L)]
  exact_mod_cast h

theorem add_mul_le_of_pow_le : ∀ (p L m : ℕ), 2 ≤ p → ∃ M0 : ℕ, ∀ n v : ℕ, M0 ≤ n → p ^ v ≤ n → (v + m) * L ≤ n := by
  intro p L m hp
  refine ⟨L * L + 2 * m * L + 1, ?_⟩
  intro n v hn hpv
  have h2 : 2 ^ v ≤ p ^ v := Nat.pow_le_pow_left hp v
  have hsq := sq_le_two_pow_add_one v
  have hag := two_mul_le_sq_add_sq v L
  have hx : 2 * ((v + m) * L) ≤ n + n := by nlinarith
  linarith

end GlobalTheory.VSubArith
end

section

namespace GlobalTheory

theorem sum_bound_of_step_diff :
    ∀ (a : ℕ → ℕ) (d p C : ℕ), 1 ≤ p →
      (∀ m : ℕ, a (m + p) ≤ a m + C * (d * (m + p + 1) ^ (d - 1))) →
      ∃ C' : ℕ, ∀ m : ℕ, a m ≤ C' * ((d + 1) * (m + 1) ^ d) := by
  intro a d p C hp h
  have key : ∀ m : ℕ, a m ≤ (∑ j ∈ Finset.range p, a j) + C * (d * (m + 1) ^ (d - 1)) * m := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      by_cases hm : m < p
      · exact le_trans (Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.2 hm)) (Nat.le_add_right _ _)
      · obtain ⟨n, rfl⟩ : ∃ n, m = n + p := ⟨m - p, by omega⟩
        have h1 := ih n (by omega)
        have h2 := h n
        have h3 : C * (d * (n + 1) ^ (d - 1)) * n ≤ C * (d * (n + p + 1) ^ (d - 1)) * n := by
          gcongr
          omega
        have h4 : C * (d * (n + p + 1) ^ (d - 1)) * (n + 1)
            ≤ C * (d * (n + p + 1) ^ (d - 1)) * (n + p) := by
          gcongr
        rw [Nat.mul_succ] at h4
        omega
  refine ⟨(∑ j ∈ Finset.range p, a j) + C, fun m => (key m).trans ?_⟩
  have h1 : 1 ≤ (d + 1) * (m + 1) ^ d := Nat.succ_le_of_lt (by positivity)
  have h2 : d * (m + 1) ^ (d - 1) * m ≤ (d + 1) * (m + 1) ^ d := by
    cases d with
    | zero => simp
    | succ k =>
      rw [Nat.add_sub_cancel, pow_succ, mul_assoc]
      gcongr <;> omega
  rw [add_mul, mul_assoc C]
  exact add_le_add (Nat.le_mul_of_pos_right _ h1) (Nat.mul_le_mul_left _ h2)

end GlobalTheory
end

section

namespace GlobalTheory.NonzeroSmulMembership

theorem exists_ne_zero_smul_mem {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (hL : Submodule.IsFullLattice E L)
    (x : Fin n → E) :
    ∃ (d : NumberField.RingOfIntegers E), d ≠ (0 : NumberField.RingOfIntegers E) ∧ d • x ∈ L := by
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := by
    rw [hL.span_eq_top]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h1 : (a * b) • y = b • a • y := by rw [mul_comm, mul_smul]
    rw [smul_add, h1, mul_smul]
    exact L.add_mem (L.smul_mem b hay) (L.smul_mem a hbz)
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := NumberField.RingOfIntegers E) c
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hq1 : algebraMap (NumberField.RingOfIntegers E) E q ≠ 0 := by
      intro h
      exact hq0 (IsFractionRing.injective (NumberField.RingOfIntegers E) E (by simpa using h))
    refine ⟨q * a, mul_ne_zero hq0 ha, ?_⟩
    have key : (q * a) • ((algebraMap (NumberField.RingOfIntegers E) E p /
        algebraMap (NumberField.RingOfIntegers E) E q) • y) = p • a • y := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      simp only [Algebra.smul_def, map_mul]
      field_simp
    rw [key]
    exact L.smul_mem p hay

end GlobalTheory.NonzeroSmulMembership
end
