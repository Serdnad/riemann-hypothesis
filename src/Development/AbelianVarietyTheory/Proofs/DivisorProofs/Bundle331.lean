module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle256
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle251
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle252
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle254
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle255
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001

@[expose] public section

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

namespace GlobalTheory.MonoCech

variable {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E]

def cone (i : ι) (c : Finset ι → E) : Finset ι → E := fun t =>
  if i ∈ t then 0 else cubeSign (insert i t) i • c (insert i t)

theorem delta_cone_add (i : ι) (c : Finset ι → E) :
    GlobalTheory.DI.delta (cone i c) + cone i (GlobalTheory.DI.delta c) = c := by
  funext t
  simp only [Pi.add_apply, GlobalTheory.DI.delta, cone]
  by_cases hi : i ∈ t
  · rw [if_pos hi, add_zero, Finset.sum_eq_single i]
    · rw [if_neg (by simp), Finset.insert_erase hi, smul_smul, cubeSign_mul_self, one_smul]
    · intro j _ hji
      rw [if_pos (Finset.mem_erase.2 ⟨Ne.symm hji, hi⟩), smul_zero]
    · intro h; exact absurd hi h
  · rw [if_neg hi, Finset.sum_insert hi, Finset.erase_insert hi, smul_add, smul_smul, cubeSign_mul_self,
      one_smul, Finset.smul_sum]
    have key : ∀ j ∈ t, cubeSign t j • (if i ∈ t.erase j then (0 : E) else
        cubeSign (insert i (t.erase j)) i • c (insert i (t.erase j))) +
        cubeSign (insert i t) i • cubeSign (insert i t) j • c ((insert i t).erase j) = 0 := by
      intro j hj
      have hij : i ≠ j := fun h => hi (h ▸ hj)
      rw [if_neg (fun h => hi (Finset.mem_of_mem_erase h)), ← Finset.erase_insert_of_ne hij, smul_smul,
        smul_smul, ← add_smul]
      have h1 := cubeSign_mul_erase (t := insert i t) (i := i) (j := j) (Finset.mem_insert_self _ _)
        (Finset.mem_insert_of_mem hj) hij
      rw [Finset.erase_insert hi] at h1
      have ha := cubeSign_mul_self (insert i t) i
      have he := cubeSign_mul_self ((insert i t).erase j) i
      have : cubeSign t j * cubeSign ((insert i t).erase j) i + cubeSign (insert i t) i * cubeSign (insert i t) j = 0 := by
        linear_combination (cubeSign (insert i t) i * cubeSign ((insert i t).erase j) i) * h1
          - (cubeSign t j * cubeSign ((insert i t).erase j) i) * ha
          - (cubeSign (insert i t) i * cubeSign (insert i t) j) * he
      rw [this, zero_smul]
    rw [add_left_comm, ← Finset.sum_add_distrib, Finset.sum_eq_zero key, add_zero]

theorem cone_zero (i : ι) : cone i (0 : Finset ι → E) = 0 := by
  funext t; simp [cone]

end GlobalTheory.MonoCech

namespace GlobalTheory.MonoCech

end GlobalTheory.MonoCech
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.exists_tensorInduction_char' : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (∀ t : Γ, t ∈ Subgroup.zpowers s) → ∀ χ : G → ℂ, IsChar ℂ ℂ χ → ∃ X : G ⋊[φ] Γ → ℂ, IsChar ℂ ℂ X ∧ (∀ g, X (inl g) = ∏ t : Γ, χ (φ t g)) ∧ ∀ δ, X (inl δ * inr s) = χ (nrmG φ s (Nat.card Γ) δ) := by
  first | (exact @GlobalTheory.Shin.TensorInd.exists_tensorInduction_char) | (exact GlobalTheory.Shin.TensorInd.exists_tensorInduction_char) | (intros; apply GlobalTheory.Shin.TensorInd.exists_tensorInduction_char <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.isInCharacterIsotypicPart_twistedInduction : ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (τ : G → G) (φ Y : H → ℂ), Kills φ Y → Kills (fun x => (Nat.card H : ℂ)⁻¹ * ∑ᶠ y : G, ext0 H φ (y⁻¹ * x * τ y)) (ind H Y) := by
  first | (exact @GlobalTheory.Shin.IndIso.kills_ind) | (exact GlobalTheory.Shin.IndIso.kills_ind) | (intros; apply GlobalTheory.Shin.IndIso.kills_ind  <;> assumption)
end

section

open GlobalTheory GlobalTheory.DI

theorem _root_.GlobalTheory.T.cartierPropertyAt_sign_mul_factorial_scaling : ∀ {E : Type} [AddCommGroup E] (p : ℕ) [Fact p.Prime] (d γ : E →+ E) (γ' : E → E) (N T : ℕ → AddSubgroup E), (∀ x : E, p • x = 0) → (∀ a, p ≤ a → N a = ⊥) → (∀ a, ∀ x ∈ N a, γ' x = ((-1 : ℤ) ^ a * (a.factorial : ℤ)) • γ x) → CartierAt d γ N T → CartierAt d γ' N T := by
  first | exact @GlobalTheory.DI.cartierAt_signFactorial | exact GlobalTheory.DI.cartierAt_signFactorial | (intros; apply GlobalTheory.DI.cartierAt_signFactorial <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

theorem _root_.GlobalTheory.T.torsionPointOfLatticeTau_lattice_membership : ∀ (N : ℕ) [NeZero N] (τ : ℍ), (∀ x y : Fin 2 → ZMod N, tors N τ x - tors N τ y ∈ (tauPair τ).lattice ↔ x = y) ∧ (∀ x y : Fin 2 → ZMod N, tors N τ (x + y) - (tors N τ x + tors N τ y) ∈ (tauPair τ).lattice) ∧ (∀ x : Fin 2 → ZMod N, tors N τ x ∈ (tauPair τ).lattice ↔ x = 0) ∧ (∀ x : Fin 2 → ZMod N, (N : ℂ) * tors N τ x ∈ (tauPair τ).lattice) ∧ (∀ z : ℂ, (N : ℂ) * z ∈ (tauPair τ).lattice → ∃ x : Fin 2 → ZMod N, z - tors N τ x ∈ (tauPair τ).lattice) := by
  first | exact @GlobalTheory.WpFam.TorsMem.main | exact GlobalTheory.WpFam.TorsMem.main | (intros; apply GlobalTheory.WpFam.TorsMem.main <;> assumption)
end

section

open GlobalTheory GlobalTheory.DI

theorem _root_.GlobalTheory.T.cechAntisymmetrizedCupProduct_leading_term : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) (f : ι → V →+ V) (h : ι → ι → V →+ K), (∀ (a : ℕ) (v : Fin a → V) (j : ι), alt f h a v {j} = ((-1 : ℤ) ^ a * (a.factorial : ℤ)) • ExteriorAlgebra.ιMulti K a (fun k => f j (v k))) ∧ ∀ (Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V)) (j : ι) (γ : ExteriorAlgebra K V →+* ExteriorAlgebra K V), IsPhi p f h Φ → IsGamma p (f j) γ → ∀ a, ∀ x ∈ forms (Set.univ : Set K) (Set.univ : Set V) a, Φ x {j} = ((-1 : ℤ) ^ a * (a.factorial : ℤ)) • γ x := by
  first | exact @GlobalTheory.DI.PhiLead.leading_term | exact GlobalTheory.DI.PhiLead.leading_term | (intros; apply GlobalTheory.DI.PhiLead.leading_term <;> assumption)
end

section

open GlobalTheory GlobalTheory.DI

theorem _root_.GlobalTheory.T.cechAntisymmetrizedCupProduct_vanish_above_degree : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) (f : ι → V →+ V) (h : ι → ι → V →+ K), (∀ (a : ℕ) (v : Fin a → V) (t : Finset ι), a + 1 < t.card → alt f h a v t = 0) ∧ ∀ (Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V)), IsPhi p f h Φ → ∀ a, ∀ x ∈ forms (Set.univ : Set K) (Set.univ : Set V) a, ∀ t : Finset ι, a + 1 < t.card → Φ x t = 0 := by
  first | exact @GlobalTheory.DI.alt_and_phi_vanish_above_degree | exact GlobalTheory.DI.alt_and_phi_vanish_above_degree | (intros; apply GlobalTheory.DI.alt_and_phi_vanish_above_degree <;> assumption)
end

section

open GlobalTheory GlobalTheory.DI

theorem _root_.GlobalTheory.T.isTotalCochainOfDegree_succ_of_differentials : ∀ {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] (d : E →+ E) (T : ℕ → Finset ι → AddSubgroup E), (∀ q s t, s.Nonempty → s ⊆ t → T q s ≤ T q t) → ∀ m c, InTot T m c → InTot T (m + 1) (delta c) ∧ ((∀ q s x, x ∈ T q s → d x ∈ T (q + 1) s) → InTot T (m + 1) (Dtot d c)) := by
  first | exact @GlobalTheory.DI.inTot_delta_Dtot | exact GlobalTheory.DI.inTot_delta_Dtot | (intros; apply GlobalTheory.DI.inTot_delta_Dtot <;> assumption)
end

section

open GlobalTheory GlobalTheory.DI

theorem _root_.GlobalTheory.T.cech_and_total_differential_additive_square_zero : ∀ {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] (d : E →+ E), (∀ c c' : Finset ι → E, delta (c + c') = delta c + delta c') ∧ (∀ c c' : Finset ι → E, delta (c - c') = delta c - delta c') ∧ (∀ c c' : Finset ι → E, Dtot d (c + c') = Dtot d c + Dtot d c') ∧ (∀ c c' : Finset ι → E, Dtot d (c - c') = Dtot d c - Dtot d c') ∧ (∀ c : Finset ι → E, delta (delta c) = 0) ∧ ((∀ x, d (d x) = 0) → ∀ c : Finset ι → E, Dtot d (Dtot d c) = 0) := by
  first | exact @GlobalTheory.DI.delta_Dtot_props | exact GlobalTheory.DI.delta_Dtot_props | (intros; apply GlobalTheory.DI.delta_Dtot_props <;> assumption)
end

section

open GlobalTheory GlobalTheory.DI

theorem _root_.GlobalTheory.T.exteriorFormsSpanOfSets_mul_smul_mono : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] (A : Subring K) (L : Set V), (1 : ExteriorAlgebra K V) ∈ forms (A : Set K) L 0 ∧ (∀ q x y, x ∈ forms (A : Set K) L 1 → y ∈ forms (A : Set K) L q → x * y ∈ forms (A : Set K) L (q + 1)) ∧ (∀ q (c : K) y, c ∈ A → y ∈ forms (A : Set K) L q → c • y ∈ forms (A : Set K) L q) ∧ (∀ (B : Set K) q (c : K) y, y ∈ forms B L q → c • y ∈ forms ((fun b => c * b) '' B) L q) ∧ ∀ (B B' : Set K) (L' : Set V) q, B ⊆ B' → L ⊆ L' → forms B L q ≤ forms B' L' q := by
  first | exact @GlobalTheory.DI.forms_mul_smul_mono | exact GlobalTheory.DI.forms_mul_smul_mono | (intros; apply GlobalTheory.DI.forms_mul_smul_mono <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD
open scoped TensorProduct

theorem _root_.GlobalTheory.T.lattice_congruence_iff_completion : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)) (M : ℕ) (β : GL (Fin n) E), 1 ≤ M → (∀ v, fv F v ∈ hat F (Λ : Set (Fin n → E)) ↔ v ∈ Λ) → (((∀ x, x ∈ Λ ↔ (β : Matrix (Fin n) (Fin n) E) *ᵥ x ∈ Λ) ∧ ∀ x ∈ Λ, ∃ y ∈ Λ, (β : Matrix (Fin n) (Fin n) E) *ᵥ x - x = M • y) ↔ ((∀ x ∈ hat F (Λ : Set (Fin n → E)), ∃ y ∈ hat F (Λ : Set (Fin n → E)), ratM F (β : Matrix (Fin n) (Fin n) E) *ᵥ x - x = M • y) ∧ ∀ x ∈ hat F (Λ : Set (Fin n → E)), ∃ y ∈ hat F (Λ : Set (Fin n → E)), ratM F (β : Matrix (Fin n) (Fin n) E) *ᵥ y = x)) := by
  first | exact @GlobalTheory.LocGlob.stab_cong_iff_hat | exact GlobalTheory.LocGlob.stab_cong_iff_hat | (intros; apply GlobalTheory.LocGlob.stab_cong_iff_hat <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

theorem _root_.GlobalTheory.T.weierstrass_constant_q_expansion : ∀ (N : ℕ) [NeZero N], HasQ N gN (cG N) := by
  first | exact @GlobalTheory.WpFam.hasQ_gN | exact GlobalTheory.WpFam.hasQ_gN | (intros; apply GlobalTheory.WpFam.hasQ_gN <;> assumption)
end
