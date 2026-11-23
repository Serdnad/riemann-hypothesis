module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle037
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
public import Formalism.PairingDivisors.StatementN
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle038
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.Galois.Infinite

@[expose] public section

section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

theorem _root_.GlobalTheory.T.exists_dual_oddFrame_cuspForms : ∀ (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ), (-1 : SL(2, ℤ)) ∉ Γ → IsReps Γ s → (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) → (∀ τ, (evM s w F τ).det ≠ 0) → Tendsto (fun τ => ModularForm.discriminant τ • (evM s w F τ)⁻¹) atImInfty (𝓝 0) → ∃ G : Fin r → ℍ → ℂ, (∀ j, IsCF Γ (12 - w j) (G j)) ∧ ∀ τ, (evM s (fun j => 12 - w j) G τ).det ≠ 0 := by
  first | exact @GlobalTheory.OddFrame.DualFrame.exists_dual_cuspForms | exact GlobalTheory.OddFrame.DualFrame.exists_dual_cuspForms | (intros; apply GlobalTheory.OddFrame.DualFrame.exists_dual_cuspForms <;> assumption)
end

section

open GlobalTheory.K5 GlobalTheory.KumDlog

noncomputable section

namespace GlobalTheory.FixFrac

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

def fracField (T : Tower p Ω) : Subfield Ω where
  carrier := {x | ∃ m : ℕ, ∃ a ∈ Lev T m, ∃ b ∈ Lev T m, b ≠ 0 ∧ x = a / b}
  zero_mem' := ⟨0, 0, zero_mem _, 1, one_mem _, one_ne_zero, by simp⟩
  one_mem' := ⟨0, 1, one_mem _, 1, one_mem _, one_ne_zero, by simp⟩
  add_mem' := by
    rintro _ _ ⟨m, a, ha, b, hb, hb0, rfl⟩ ⟨m', c, hc, d, hd, hd0, rfl⟩
    have h1 := Lev_mono T (le_max_left m m')
    have h2 := Lev_mono T (le_max_right m m')
    refine ⟨max m m', a * d + b * c, add_mem (mul_mem (h1 ha) (h2 hd)) (mul_mem (h1 hb) (h2 hc)),
      b * d, mul_mem (h1 hb) (h2 hd), mul_ne_zero hb0 hd0, ?_⟩
    rw [div_add_div _ _ hb0 hd0]
  mul_mem' := by
    rintro _ _ ⟨m, a, ha, b, hb, hb0, rfl⟩ ⟨m', c, hc, d, hd, hd0, rfl⟩
    have h1 := Lev_mono T (le_max_left m m')
    have h2 := Lev_mono T (le_max_right m m')
    exact ⟨max m m', a * c, mul_mem (h1 ha) (h2 hc), b * d, mul_mem (h1 hb) (h2 hd),
      mul_ne_zero hb0 hd0, div_mul_div_comm a b c d⟩
  neg_mem' := by
    rintro _ ⟨m, a, ha, b, hb, hb0, rfl⟩
    exact ⟨m, -a, neg_mem ha, b, hb, hb0, (neg_div b a).symm⟩
  inv_mem' := by
    rintro _ ⟨m, a, ha, b, hb, hb0, rfl⟩
    by_cases ha0 : a = 0
    · exact ⟨0, 0, zero_mem _, 1, one_mem _, one_ne_zero, by simp [ha0]⟩
    · exact ⟨m, b, hb, a, ha, ha0, inv_div a b⟩

theorem mem_fracField_of_mem (T : Tower p Ω) {m : ℕ} {a : Ω} (ha : a ∈ Lev T m) :
    a ∈ fracField T :=
  ⟨m, a, ha, 1, one_mem _, one_ne_zero, (div_one a).symm⟩

theorem fixed_eq_div : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (x : Ω), (∀ h ∈ Hinf T, h x = x) →
    ∃ m : ℕ, ∃ a ∈ Lev T m, ∃ b ∈ Lev T m, b ≠ 0 ∧ x = a / b := by
  intro p _ Ω _ _ hC T x hx
  haveI : FaithfulSMul (O0 p) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 hC.inj
  letI : Algebra (FractionRing (O0 p)) Ω := FractionRing.liftAlgebra (O0 p) Ω
  haveI : IsScalarTower (O0 p) (FractionRing (O0 p)) Ω :=
    FractionRing.isScalarTower_liftAlgebra _ _
  haveI : Algebra.IsAlgebraic (O0 p) Ω := hC.alg
  haveI : Algebra.IsAlgebraic (FractionRing (O0 p)) Ω :=
    Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective (O0 p) (FractionRing (O0 p)))
  haveI : IsAlgClosed Ω := hC.clo
  haveI : IsAlgClosure (FractionRing (O0 p)) Ω := ⟨hC.clo, inferInstance⟩
  haveI : CharZero Ω := Basic.charZero_of_isClo hC
  haveI : CharZero (FractionRing (O0 p)) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective (O0 p) (FractionRing (O0 p)))
  haveI : IsGalois (FractionRing (O0 p)) Ω := IsAlgClosure.isGalois _ _
  let E := IntermediateField.adjoin (FractionRing (O0 p)) (Set.range T.ζ ∪ Set.range T.qq)
  have hxE : x ∈ E := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have hfix : ∀ y ∈ E, σ y = y := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ
    have hmem : σ.restrictScalars (O0 p) ∈ Hinf T := by
      rw [mem_Hinf]
      intro n
      exact ⟨hfix _ (IntermediateField.subset_adjoin _ _ (Or.inl ⟨n, rfl⟩)),
        hfix _ (IntermediateField.subset_adjoin _ _ (Or.inr ⟨n, rfl⟩))⟩
    exact hx _ hmem
  have halg : ∀ c : FractionRing (O0 p), algebraMap (FractionRing (O0 p)) Ω c ∈ fracField T := by
    intro c
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (O0 p)) c
    dsimp only
    rw [IsFractionRing.mk'_eq_div, map_div₀, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
    exact ⟨0, _, Subalgebra.algebraMap_mem _ a, _, Subalgebra.algebraMap_mem _ (s : O0 p),
      (map_ne_zero_iff _ hC.inj).2 (nonZeroDivisors.ne_zero s.2), rfl⟩
  have hle : E ≤ (fracField T).toIntermediateField halg := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ (⟨n, rfl⟩ | ⟨n, rfl⟩)
    · exact mem_fracField_of_mem T (zeta_mem_Lev T n)
    · exact mem_fracField_of_mem T (qq_mem_Lev T n)
  exact hle hxE

end GlobalTheory.FixFrac
end
end

section

noncomputable section

namespace GlobalTheory.DerExt

open GlobalTheory.K5 GlobalTheory.KumDlog

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]
variable {ι : Type} [Fintype ι]

def D0 (u v : ι → Ω) (tr d : Ω → Ω) (x : Ω) : Ω := ∑ k, u k * d (tr (v k * x))

def phi (D : Ω → Ω) (x y : Ω) : Ω := D (x * y) - x * D y - y * D x

def psi (u v : ι → Ω) (D : Ω → Ω) (x : Ω) : Ω := ∑ k, u k * phi D (v k) x

theorem phi_comm (D : Ω → Ω) (x y : Ω) : phi D x y = phi D y x := by
  unfold phi; rw [mul_comm x y]; ring

theorem phi_one (D : Ω → Ω) (y : Ω) : phi D 1 y = -(y * D 1) := by
  unfold phi; simp

theorem phi_ident (D : Ω → Ω) (w x y : Ω) :
    w * phi D x y - phi D (w * x) y + phi D w (x * y) - y * phi D w x = 0 := by
  unfold phi; rw [show w * x * y = w * (x * y) by ring]; ring

variable {B C : Subalgebra (O0 p) Ω} {u v : ι → Ω} {tr : Ω → Ω} {d : Ω → Ω}

private theorem isInt_congr {x y : Ω} (hx : IsInt (p := p) x) (h : y = x) :
    IsInt (p := p) y := h ▸ hx

theorem traceDerivationFirstApprox_add_isInt (h : DualData B C u v tr) (hd : IsDer B d) {x y : Ω} (hx : x ∈ C) (hy : y ∈ C) :
    IsInt (p := p) (D0 u v tr d (x + y) - D0 u v tr d x - D0 u v tr d y) := by
  obtain ⟨_, hCi, hu, hv, htr, hadd, -⟩ := h
  refine isInt_congr (IsIntegral.sum (s := Finset.univ) _ fun k _ => IsIntegral.mul (hCi _ (hu k))
    (hd.1 _ (htr _ (C.mul_mem (hv k) hx)) _ (htr _ (C.mul_mem (hv k) hy)))) ?_
  simp only [D0, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_add, hadd _ (C.mul_mem (hv k) hx) _ (C.mul_mem (hv k) hy)]; ring

theorem traceDerivationFirstApprox_mul_left_isInt (h : DualData B C u v tr) (hd : IsDer B d) {b x : Ω} (hb : b ∈ B) (hx : x ∈ C) :
    IsInt (p := p) (D0 u v tr d (b * x) - b * D0 u v tr d x - p * x * d b) := by
  obtain ⟨_, hCi, hu, hv, htr, -, hlin, hdual, -⟩ := h
  refine isInt_congr (IsIntegral.sum (s := Finset.univ) _ fun k _ => IsIntegral.mul (hCi _ (hu k))
    (hd.2.1 b hb _ (htr _ (C.mul_mem (hv k) hx)))) ?_
  rw [← hdual x hx]
  simp only [D0, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show v k * (b * x) = b * (v k * x) by ring, hlin b hb _ (C.mul_mem (hv k) hx)]; ring

theorem phi_add (h : DualData B C u v tr) (hd : IsDer B d) {x x' y : Ω} (hx : x ∈ C) (hx' : x' ∈ C)
    (hy : y ∈ C) :
    IsInt (p := p) (phi (D0 u v tr d) (x + x') y - phi (D0 u v tr d) x y - phi (D0 u v tr d) x' y) := by
  refine isInt_congr (IsIntegral.sub (traceDerivationFirstApprox_add_isInt h hd (C.mul_mem hx hy) (C.mul_mem hx' hy))
    (IsIntegral.mul (h.2.1 y hy) (traceDerivationFirstApprox_add_isInt h hd hx hx'))) ?_
  simp only [phi, add_mul]; ring

theorem phi_bmul (h : DualData B C u v tr) (hd : IsDer B d) {b x y : Ω} (hb : b ∈ B) (hx : x ∈ C)
    (hy : y ∈ C) :
    IsInt (p := p) (phi (D0 u v tr d) (b * x) y - b * phi (D0 u v tr d) x y) := by
  refine isInt_congr (IsIntegral.sub (traceDerivationFirstApprox_mul_left_isInt h hd hb (C.mul_mem hx hy))
    (IsIntegral.mul (h.2.1 y hy) (traceDerivationFirstApprox_mul_left_isInt h hd hb hx))) ?_
  simp only [phi]; rw [show b * x * y = b * (x * y) by ring]; ring

theorem lin_sum (h : DualData B C u v tr) (f : Ω → Ω)
    (hadd : ∀ x ∈ C, ∀ y ∈ C, IsInt (p := p) (f (x + y) - f x - f y))
    (hlin : ∀ b ∈ B, ∀ x ∈ C, IsInt (p := p) (f (b * x) - b * f x))
    {κ : Type} (s : Finset κ) (w b : κ → Ω) (hw : ∀ i, w i ∈ C) (hb : ∀ i, b i ∈ B) :
    IsInt (p := p) (f (∑ i ∈ s, w i * b i) - ∑ i ∈ s, b i * f (w i)) := by
  classical
  have hBC := h.1
  induction s using Finset.induction_on with
  | empty =>
    simpa using hlin 0 B.zero_mem 0 C.zero_mem
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hS : ∑ i ∈ s, w i * b i ∈ C := C.sum_mem fun i _ => C.mul_mem (hw i) (hBC (hb i))
    have h1 := hadd _ (C.mul_mem (hw a) (hBC (hb a))) _ hS
    have h2 := hlin (b a) (hb a) (w a) (hw a)
    rw [mul_comm (b a) (w a)] at h2
    exact isInt_congr (IsIntegral.add h1 (IsIntegral.add h2 ih)) (by ring)

theorem sum_swap_eq (h : DualData B C u v tr) (D : Ω → Ω) {x : Ω} (hx : x ∈ C) (y : Ω) :
    ∑ k, u k * ∑ l, tr (u l * (v k * x)) * phi D (v l) y = p * x * psi u v D y := by
  obtain ⟨_, -, hu, -, -, -, -, hdual, -⟩ := h
  calc ∑ k, u k * ∑ l, tr (u l * (v k * x)) * phi D (v l) y
      = ∑ k, ∑ l, u k * tr (v k * (x * u l)) * phi D (v l) y := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [show u l * (v k * x) = v k * (x * u l) by ring]; ring
    _ = ∑ l, ∑ k, u k * tr (v k * (x * u l)) * phi D (v l) y := Finset.sum_comm
    _ = ∑ l, (∑ k, u k * tr (v k * (x * u l))) * phi D (v l) y := by
        simp only [Finset.sum_mul]
    _ = ∑ l, p * (x * u l) * phi D (v l) y := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hdual _ (C.mul_mem hx (hu l))]
    _ = p * x * psi u v D y := by
        simp only [psi, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        ring

theorem S_congr (h : DualData B C u v tr) (hd : IsDer B d) {x y : Ω} (hx : x ∈ C) (hy : y ∈ C) :
    IsInt (p := p) (p * ∑ k, u k * phi (D0 u v tr d) (v k * x) y - p * x * psi u v (D0 u v tr d) y) := by
  have hBC := h.1
  have hCi := h.2.1
  have hu := h.2.2.1
  have hv := h.2.2.2.1
  have htr := h.2.2.2.2.1
  have hdual2 := h.2.2.2.2.2.2.2.2.1
  have hpB : (p : Ω) ∈ B := natCast_mem B p
  have key : ∀ k, IsInt (p := p) (u k * (p * phi (D0 u v tr d) (v k * x) y -
      ∑ l, tr (u l * (v k * x)) * phi (D0 u v tr d) (v l) y)) := by
    intro k
    have hz : v k * x ∈ C := C.mul_mem (hv k) hx
    have ha := phi_bmul h hd hpB hz hy
    have hb := lin_sum h (fun z => phi (D0 u v tr d) z y)
      (fun a ha b hb => phi_add h hd ha hb hy) (fun b hb a ha => phi_bmul h hd hb ha hy)
      Finset.univ v (fun l => tr (u l * (v k * x))) hv
      (fun l => htr _ (C.mul_mem (hu l) hz))
    rw [hdual2 _ hz] at hb
    exact IsIntegral.mul (hCi _ (hu k)) (isInt_congr (IsIntegral.sub hb ha) (by ring))
  refine isInt_congr (IsIntegral.sum (s := Finset.univ) _ fun k _ => key k) ?_
  rw [← sum_swap_eq h (D0 u v tr d) hx y, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

def Dext (p : ℕ) (u v : ι → Ω) (tr d : Ω → Ω) (x : Ω) : Ω :=
  (p : Ω) ^ 2 * D0 u v tr d x + p * psi u v (D0 u v tr d) x

theorem Dext_mul (h : DualData B C u v tr) (hd : IsDer B d) {x y : Ω} (hx : x ∈ C) (hy : y ∈ C) :
    IsInt (p := p) (Dext p u v tr d (x * y) - x * Dext p u v tr d y - y * Dext p u v tr d x) := by
  have hsum := h.2.2.2.2.2.2.2.2.2
  have hid : (p : Ω) * phi (D0 u v tr d) x y - ∑ k, u k * phi (D0 u v tr d) (v k * x) y +
      psi u v (D0 u v tr d) (x * y) - y * psi u v (D0 u v tr d) x = 0 := by
    calc (p : Ω) * phi (D0 u v tr d) x y - ∑ k, u k * phi (D0 u v tr d) (v k * x) y +
          psi u v (D0 u v tr d) (x * y) - y * psi u v (D0 u v tr d) x
        = ∑ k, u k * (v k * phi (D0 u v tr d) x y - phi (D0 u v tr d) (v k * x) y +
            phi (D0 u v tr d) (v k) (x * y) - y * phi (D0 u v tr d) (v k) x) := by
          rw [← hsum]
          simp only [psi, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
            ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
      _ = 0 := by simp [phi_ident]
  refine isInt_congr (S_congr h hd hx hy) ?_
  simp only [Dext, phi, psi] at hid ⊢
  linear_combination (p : Ω) * hid

theorem Dext_add (h : DualData B C u v tr) (hd : IsDer B d) {x y : Ω} (hx : x ∈ C) (hy : y ∈ C) :
    IsInt (p := p) (Dext p u v tr d (x + y) - Dext p u v tr d x - Dext p u v tr d y) := by
  have hCi := h.2.1
  have hu := h.2.2.1
  have hv := h.2.2.2.1
  have h1 := traceDerivationFirstApprox_add_isInt h hd hx hy
  have h2 : IsInt (p := p) (∑ k, u k * (phi (D0 u v tr d) (x + y) (v k) - phi (D0 u v tr d) x (v k) -
      phi (D0 u v tr d) y (v k))) :=
    IsIntegral.sum (s := Finset.univ) _ fun k _ => IsIntegral.mul (hCi _ (hu k)) (phi_add h hd hx hy (hv k))
  have hp : IsIntegral (O0 p) (p : Ω) := isIntegral_natCast p
  refine isInt_congr (IsIntegral.add ((hp.pow 2).mul h1) (hp.mul h2)) ?_
  have e : psi u v (D0 u v tr d) (x + y) - psi u v (D0 u v tr d) x - psi u v (D0 u v tr d) y =
      ∑ k, u k * (phi (D0 u v tr d) (x + y) (v k) - phi (D0 u v tr d) x (v k) -
        phi (D0 u v tr d) y (v k)) := by
    simp only [psi, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [phi_comm _ (v k) (x + y), phi_comm _ (v k) x, phi_comm _ (v k) y]; ring
  simp only [Dext]
  linear_combination (p : Ω) * e

theorem Dext_B (h : DualData B C u v tr) (hd : IsDer B d) {b : Ω} (hb : b ∈ B) :
    IsInt (p := p) (Dext p u v tr d b - (p : Ω) ^ 3 * d b) := by
  have hCi := h.2.1
  have hu := h.2.2.1
  have hv := h.2.2.2.1
  have hsum := h.2.2.2.2.2.2.2.2.2
  have h1 := traceDerivationFirstApprox_mul_left_isInt h hd hb C.one_mem
  rw [mul_one, mul_one] at h1
  have h2 : IsInt (p := p) (psi u v (D0 u v tr d) b + p * b * D0 u v tr d 1) := by
    refine isInt_congr (IsIntegral.sum (s := Finset.univ) _ fun k _ => IsIntegral.mul (hCi _ (hu k))
      (phi_bmul h hd hb C.one_mem (hv k))) ?_
    rw [← hsum]
    simp only [psi, phi_one, mul_one, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [phi_comm _ (v k) b]; ring
  have hp : IsIntegral (O0 p) (p : Ω) := isIntegral_natCast p
  refine isInt_congr (IsIntegral.add ((hp.pow 2).mul h1) (hp.mul h2)) ?_
  simp only [Dext]; ring

theorem Dext_isDer (h : DualData B C u v tr) (hd : IsDer B d) : IsDer C (Dext p u v tr d) :=
  ⟨fun x hx y hy => Dext_add h hd hx hy, fun x hx y hy => Dext_mul h hd hx hy,
   fun c => isInt_congr (IsIntegral.add (Dext_B h hd (B.algebraMap_mem c))
     (((isIntegral_natCast (R := O0 p) (B := Ω) p).pow 3).mul (hd.2.2 c))) (by ring)⟩

theorem exists_ext : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    ∀ (B C : Subalgebra (O0 p) Ω) (ι : Type) [Fintype ι] (u v : ι → Ω) (tr : Ω → Ω),
    DualData B C u v tr →
    ∀ d : Ω → Ω, IsDer B d → ∃ D : Ω → Ω, IsDer C D ∧ ∀ b ∈ B, IsInt (p := p) (D b - (p : Ω) ^ 3 * d b) := by
  intro p _ Ω _ _ B C ι _ u v tr h d hd
  exact ⟨Dext p u v tr d, Dext_isDer h hd, fun b hb => Dext_B h hd hb⟩

end GlobalTheory.DerExt
end
end

section

noncomputable section

namespace GlobalTheory.LevGlue

open GlobalTheory.K5 GlobalTheory.KumDlog

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem der_pow_val {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (hD : GlobalTheory.KumDlog.IsDer S D)
    (hS : ∀ x ∈ S, IsInt (p := p) x) (hp : (p : Ω) ≠ 0) {x c : Ω} {m j : ℕ} (hx : x ∈ S)
    (h : IsInt (p := p) (D x - c * x / (p : Ω) ^ (m + j))) :
    IsInt (p := p) (D (x ^ (p ^ j)) - c * x ^ (p ^ j) / (p : Ω) ^ m) := by
  obtain ⟨k, hk⟩ : ∃ k, p ^ j = k + 1 := ⟨p ^ j - 1, (Nat.succ_pred_eq_of_pos (ppow_pos j)).symm⟩
  have h1 := hD.pow hS hx k
  rw [← hk] at h1
  have e : c * x ^ (p ^ j) / (p : Ω) ^ m =
      ((p ^ j : ℕ) : Ω) * x ^ k * (c * x / (p : Ω) ^ (m + j)) := by
    have e1 : x ^ (p ^ j) = x ^ k * x := by rw [hk, pow_succ]
    have e2 : ((p ^ j : ℕ) : Ω) = (p : Ω) ^ j := by push_cast; ring
    rw [e1, e2, pow_add]
    field_simp
  refine int_congr (int_add h1 (int_mul (int_mul (int_nat (p ^ j)) (int_pow (hS x hx) k)) h)) ?_
  linear_combination (-1 : Ω) * e

theorem compat_gen (T : Tower p Ω) {m n : ℕ} (hmn : m ≤ n) {D D' : Ω → Ω}
    (hD : GlobalTheory.KumDlog.IsDer (Lev T n) D) (hD' : GlobalTheory.KumDlog.IsDer (Lev T m) D')
    (hz : IsInt (p := p) (D (T.ζ m) - D' (T.ζ m))) (hq : IsInt (p := p) (D (T.qq m) - D' (T.qq m))) :
    ∀ x ∈ Lev T m, IsInt (p := p) (D x - D' x) :=
  GlobalTheory.KumDlog.IsDer.adjoin (t := {T.ζ m, T.qq m}) (GlobalTheory.KumDlog.IsDer.sub (hD.mono (Lev_mono T hmn)) hD') (Lev_int T m)
    (by rintro x (rfl | rfl); exacts [zeta_mem_Lev T m, qq_mem_Lev T m])
    (by rintro x (rfl | rfl); exacts [hz, hq])

theorem vals_down (T : Tower p Ω) (hp : (p : Ω) ≠ 0) {m n : ℕ} (hmn : m ≤ n) {dz dq : Ω → Ω}
    (hz : GlobalTheory.KumDlog.IsDer (Lev T n) dz) (hq : GlobalTheory.KumDlog.IsDer (Lev T n) dq) (hv : GlobalTheory.KumDlog.Vals T n dz dq) : GlobalTheory.KumDlog.Vals T m dz dq := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have hS := Lev_int T (m + j)
  have zm := zeta_mem_Lev T (m + j)
  have qm := qq_mem_Lev T (m + j)
  have z0 : ∀ {D : Ω → Ω} {x : Ω}, IsInt (p := p) (D x) → IsInt (p := p) (D x - 0 * x / (p : Ω) ^ (m + j)) :=
    fun h => int_congr h (by ring)
  have z1 : ∀ {D : Ω → Ω} {y : Ω}, IsInt (p := p) (D y - 0 * y / (p : Ω) ^ m) → IsInt (p := p) (D y) :=
    fun h => int_congr h (by ring)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := der_pow_val hz hS hp zm hv.1
    rwa [zeta_pow] at this
  · have := z1 (der_pow_val hz hS hp qm (z0 hv.2.1))
    rwa [qq_pow] at this
  · have := z1 (der_pow_val hq hS hp zm (z0 hv.2.2.1))
    rwa [zeta_pow] at this
  · have := der_pow_val hq hS hp qm hv.2.2.2
    rwa [qq_pow] at this

theorem glue_fam (T : Tower p Ω) (F : ℕ → Ω → Ω) (hF : ∀ m, GlobalTheory.KumDlog.IsDer (Lev T (m + 1)) (F m))
    (hc : ∀ m n, m ≤ n → ∀ x ∈ Lev T (m + 1), IsInt (p := p) (F n x - F m x)) :
    ∃ G : Ω → Ω, (∀ m, ∀ x ∈ Lev T (m + 1), IsInt (p := p) (G x - F m x)) ∧
      ∀ S : Subalgebra (O0 p) Ω, (∀ x ∈ S, ∃ m, x ∈ Lev T m) → GlobalTheory.KumDlog.IsDer S G := by
  classical
  let M : Ω → ℕ := fun x => if h : ∃ m, x ∈ Lev T (m + 1) then Classical.choose h else 0
  have hG : ∀ m, ∀ x ∈ Lev T (m + 1), IsInt (p := p) (F (M x) x - F m x) := by
    intro m x hx
    have h : ∃ m, x ∈ Lev T (m + 1) := ⟨m, hx⟩
    have hM : M x = Classical.choose h := dif_pos h
    have ha := Classical.choose_spec h
    rw [hM]
    have h1 := hc _ (max m (Classical.choose h)) (le_max_right _ _) x ha
    have h2 := hc _ (max m (Classical.choose h)) (le_max_left _ _) x hx
    exact int_congr (int_sub h2 h1) (by ring)
  refine ⟨fun x => F (M x) x, hG, fun S hS => ?_⟩
  have two : ∀ x ∈ S, ∀ y ∈ S, ∃ n, x ∈ Lev T (n + 1) ∧ y ∈ Lev T (n + 1) := by
    intro x hx y hy
    obtain ⟨a, ha⟩ := hS x hx
    obtain ⟨b, hb⟩ := hS y hy
    exact ⟨a + b, Lev_mono T (by omega) ha, Lev_mono T (by omega) hb⟩
  refine ⟨fun x hx y hy => ?_, fun x hx y hy => ?_, fun c => ?_⟩
  · obtain ⟨n, hxn, hyn⟩ := two x hx y hy
    refine int_congr (int_add (int_add (int_sub (int_sub ((hF n).1 x hxn y hyn)
      (hG n x hxn)) (hG n y hyn)) (hG n _ (add_mem hxn hyn))) int_zero) ?_
    ring
  · obtain ⟨n, hxn, hyn⟩ := two x hx y hy
    have ix := Lev_int T _ x hxn
    have iy := Lev_int T _ y hyn
    refine int_congr (int_sub (int_sub (int_add ((hF n).2.1 x hxn y hyn)
      (hG n _ (mul_mem hxn hyn))) (int_mul ix (hG n y hyn))) (int_mul iy (hG n x hxn))) ?_
    ring
  · have hm := (Lev T (0 + 1)).algebraMap_mem c
    exact int_congr (int_add (hG 0 _ hm) ((hF 0).2.2 c)) (by ring)

theorem glue : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (B : Subalgebra (O0 p) Ω), (∀ x ∈ B, ∃ m : ℕ, x ∈ Lev T m) →
    (∀ m : ℕ, 1 ≤ m → ∃ dz dq : Ω → Ω, GlobalTheory.KumDlog.IsDer (Lev T m) dz ∧ GlobalTheory.KumDlog.IsDer (Lev T m) dq ∧ GlobalTheory.KumDlog.Vals T m dz dq) →
    ∃ dz dq : Ω → Ω, GlobalTheory.KumDlog.IsDer B dz ∧ GlobalTheory.KumDlog.IsDer B dq ∧ ∀ m : ℕ, 1 ≤ m → GlobalTheory.KumDlog.Vals T m dz dq := by
  intro p _ Ω _ _ hclo T B hB hlev
  haveI : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo hclo
  have hp : (p : Ω) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have h' : ∀ m : ℕ, ∃ dz dq : Ω → Ω, GlobalTheory.KumDlog.IsDer (Lev T (m + 1)) dz ∧ GlobalTheory.KumDlog.IsDer (Lev T (m + 1)) dq ∧
      GlobalTheory.KumDlog.Vals T (m + 1) dz dq := fun m => hlev (m + 1) (by omega)
  choose Z Q hZ hQ hV using h'
  have cZ : ∀ m n, m ≤ n → ∀ x ∈ Lev T (m + 1), IsInt (p := p) (Z n x - Z m x) := by
    intro m n hmn
    have v := vals_down T hp (by omega : m + 1 ≤ n + 1) (hZ n) (hQ n) (hV n)
    exact compat_gen T (by omega : m + 1 ≤ n + 1) (hZ n) (hZ m)
      (int_congr (int_sub v.1 (hV m).1) (by ring)) (int_congr (int_sub v.2.1 (hV m).2.1) (by ring))
  have cQ : ∀ m n, m ≤ n → ∀ x ∈ Lev T (m + 1), IsInt (p := p) (Q n x - Q m x) := by
    intro m n hmn
    have v := vals_down T hp (by omega : m + 1 ≤ n + 1) (hZ n) (hQ n) (hV n)
    exact compat_gen T (by omega : m + 1 ≤ n + 1) (hQ n) (hQ m)
      (int_congr (int_sub v.2.2.1 (hV m).2.2.1) (by ring))
      (int_congr (int_sub v.2.2.2 (hV m).2.2.2) (by ring))
  obtain ⟨dz, hdz, hdzB⟩ := glue_fam T Z hZ cZ
  obtain ⟨dq, hdq, hdqB⟩ := glue_fam T Q hQ cQ
  refine ⟨dz, dq, hdzB B hB, hdqB B hB, fun m hm => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have v := hV k
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact int_congr (int_add (hdz k _ (zeta_mem_Lev T _)) v.1) (by ring)
  · exact int_congr (int_add (hdz k _ (qq_mem_Lev T _)) v.2.1) (by ring)
  · exact int_congr (int_add (hdq k _ (zeta_mem_Lev T _)) v.2.2.1) (by ring)
  · exact int_congr (int_add (hdq k _ (qq_mem_Lev T _)) v.2.2.2) (by ring)

end GlobalTheory.LevGlue
end
end

section


theorem _root_.GlobalTheory.T.dividedPowerValuations_minVal : Formalism.PairingDivisionLocalBalance.MinVal := by
  first | exact @GlobalTheory.cmValues_minPadicVal_bound | exact GlobalTheory.cmValues_minPadicVal_bound | (intros; apply GlobalTheory.cmValues_minPadicVal_bound <;> assumption)
end
