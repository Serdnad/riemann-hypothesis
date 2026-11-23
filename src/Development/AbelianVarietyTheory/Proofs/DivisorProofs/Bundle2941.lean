module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2650
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudTorusWeightZeroInvariantFieldCoeffs
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsResEqOfUnitInChart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle019
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2812
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeG
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatLoc

variable {F : Type} [Field F]

theorem der_bracket (d : Derivation ℤ F F) (x y β : F) (M : ℕ) :
    x * β ^ M * d (y * β ^ M) - y * β ^ M * d (x * β ^ M) = β ^ (2 * M) * (x * d y - y * d x) := by
  simp only [Derivation.leibniz, smul_eq_mul]
  ring

theorem der_mul_pow (d : Derivation ℤ F F) (x β : F) (hβ : β ≠ 0) (m : ℕ) :
    d (x * β ^ (m + 1)) = β ^ (m + 1) * (d x + ((m + 1 : ℕ) : F) * x * (d β / β)) := by
  simp only [Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
  field_simp
  ring

theorem symb_eq {n : ℕ} (δ : Fin n → Derivation ℤ F F) (δ₀ : Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F)
    (x y β : F) (hβ : β ≠ 0) (k m : ℕ) :
    ((k * (m + 1) : ℕ) : F) * (x * β ^ (m + 1)) * (x * β ^ (m + 1) * δ₀ (y * β ^ (m + 1)) - y * β ^ (m + 1) * δ₀ (x * β ^ (m + 1))) -
      ∑ a, ∑ e, Λ a e * δ a (x * β ^ (m + 1)) *
        (x * β ^ (m + 1) * δ e (y * β ^ (m + 1)) - y * β ^ (m + 1) * δ e (x * β ^ (m + 1))) =
    β ^ (3 * (m + 1)) * (((k * (m + 1) : ℕ) : F) * x * (x * δ₀ y - y * δ₀ x) -
      ∑ a, ∑ e, Λ a e * (δ a x + ((m + 1 : ℕ) : F) * x * (δ a β / β)) * (x * δ e y - y * δ e x)) := by
  rw [mul_sub (β ^ (3 * (m + 1))), Finset.mul_sum]
  simp only [Finset.mul_sum]
  congr 1
  · rw [der_bracket]; ring
  · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    rw [der_bracket, der_mul_pow _ _ _ hβ]; ring

theorem symb_one {n : ℕ} (δ : Fin n → Derivation ℤ F F) (δ₀ : Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F)
    (y β : F) (k m : ℕ) :
    ((k * (m + 1) : ℕ) : F) * 1 * (1 * δ₀ y - y * δ₀ 1) -
      ∑ a, ∑ e, Λ a e * (δ a 1 + ((m + 1 : ℕ) : F) * 1 * (δ a β / β)) * (1 * δ e y - y * δ e 1) =
    ((m + 1 : ℕ) : F) * ((k : F) * δ₀ y - ∑ a, ∑ e, Λ a e * (δ a β / β) * δ e y) := by
  simp only [Derivation.map_one_eq_zero, mul_zero, sub_zero, zero_add, one_mul, mul_one]
  rw [mul_sub, Finset.mul_sum]
  simp only [Finset.mul_sum]
  congr 1
  · push_cast; ring
  · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    ring

def derivationBracketSum {n : ℕ} (δ : Fin n → Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F) (x y : F) : F :=
  ∑ a, ∑ e, Λ a e * δ a x * (x * δ e y - y * δ e x)

theorem symb_two {n : ℕ} (δ : Fin n → Derivation ℤ F F) (δ₀ : Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F)
    (x y β : F) (k m : ℕ) :
    ((k * (m + 1) : ℕ) : F) * x * (x * δ₀ y - y * δ₀ x) -
      ∑ a, ∑ e, Λ a e * (δ a x + ((m + 1 : ℕ) : F) * x * (δ a β / β)) * (x * δ e y - y * δ e x) =
    ((m + 1 : ℕ) : F) * x * (x * ((k : F) * δ₀ y - ∑ a, ∑ e, Λ a e * (δ a β / β) * δ e y) -
      y * ((k : F) * δ₀ x - ∑ a, ∑ e, Λ a e * (δ a β / β) * δ e x)) - derivationBracketSum δ Λ x y := by
  have hs : ∑ a, ∑ e, Λ a e * (δ a x + ((m + 1 : ℕ) : F) * x * (δ a β / β)) * (x * δ e y - y * δ e x) =
      derivationBracketSum δ Λ x y + ((m + 1 : ℕ) : F) * x * (x * ∑ a, ∑ e, Λ a e * (δ a β / β) * δ e y -
        y * ∑ a, ∑ e, Λ a e * (δ a β / β) * δ e x) := by
    unfold derivationBracketSum
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    ring
  rw [hs]; push_cast; ring

theorem tsum_add_one {n : ℕ} (δ : Fin n → Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F) (x y : F) :
    derivationBracketSum δ Λ (x + 1) y - derivationBracketSum δ Λ x y = ∑ a, ∑ e, Λ a e * δ a x * δ e y := by
  unfold derivationBracketSum
  simp only [map_add (f := _), Derivation.map_one_eq_zero, add_zero, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
  ring

end GlobalTheory.HeatLoc

namespace GlobalTheory.HeatLoc

theorem valR_ne_zero_sec {X : Scheme.{0}} (L : LB X) {F : Type} [Field F] (ξ : Sp F ⟶ X) (j₀ : L.ι)
    (h : ⊤ ≤ ξ ⁻¹ᵁ L.U j₀) (k : ℕ) (s : SecM (𝟙 X) L k) (hs : ⊤ ≤ ξ ⁻¹ᵁ nonzeroLocus s) :
    valR ξ _ (s.f fun _ => j₀) ≠ 0 := by
  have hk : ⊤ ≤ ξ ⁻¹ᵁ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) fun _ => (k : ℤ)).U (fun _ => j₀) :=
    fun p hp => Set.mem_iInter.2 fun _ => h hp
  have h₁ := (GlobalTheory.AmpleSpan.isUnit_gs_iff ξ (IsLocalRing.closedPoint F) _ (hk trivial) _).1
    ((GlobalTheory.AmpleSpan.mem_nonzeroLocus_iff_gs s ξ _ (hk trivial)).1 (hs trivial))
  exact ((GlobalTheory.Points.le_preimage_basicOpen_iff ξ hk _).1
    (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of F) ξ h₁).ge).ne_zero

theorem symb_regular : ∀ (K : Type) [Field K] [CharZero K] (P₀ : Out.PolAV (Sp K)) (n : ℕ) (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left), (∀ a, IsInv P₀.A (v a) (dd a)) → ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ (δ : Fin n → Derivation ℤ F F), (∀ a O f, ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O (dd a O f) = δ a (valR ξ O f)) → ∀ (j₀ : P₀.L.ι), ⊤ ≤ ξ ⁻¹ᵁ P₀.L.U j₀ → ∀ (δ₀ : Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F), (∀ (k : ℕ), 1 ≤ k → ∀ σ τ : SecM (𝟙 P₀.A.left) P₀.L k, ∃ ρ : SecM (𝟙 P₀.A.left) P₀.L (3 * k), ∀ b c : F, b = valR ξ _ (σ.f fun _ => j₀) → c = valR ξ _ (τ.f fun _ => j₀) → (k : F) * b * (b * δ₀ c - c * δ₀ b) - ∑ a, ∑ e, Λ a e * δ a b * (b * δ e c - c * δ e b) = valR ξ _ (ρ.f fun _ => j₀)) → ∀ (k : ℕ), 1 ≤ k → ∀ s : SecM (𝟙 P₀.A.left) P₀.L k, ⊤ ≤ ξ ⁻¹ᵁ (Out.nonzeroLocus s) → (∀ f f' : Γ(P₀.A.left, (Out.nonzeroLocus s)), ∃ h : Γ(P₀.A.left, (Out.nonzeroLocus s)), valR ξ _ h = ∑ a, ∑ e, Λ a e * δ a (valR ξ _ f) * δ e (valR ξ _ f')) ∧ (∀ f : Γ(P₀.A.left, (Out.nonzeroLocus s)), ∃ f' : Γ(P₀.A.left, (Out.nonzeroLocus s)), valR ξ _ f' = (k : F) * δ₀ (valR ξ _ f) - ∑ a, ∑ e, Λ a e * (δ a (valR ξ _ (s.f fun _ => j₀)) / valR ξ _ (s.f fun _ => j₀)) * δ e (valR ξ _ f)) := by
  intro K _ _ P₀ n v dd hdd F _ ψ ξ hξ hinj δ hδ j₀ hj₀ δ₀ Λ hyp k hk s hs
  haveI := P₀.isAb.proper
  haveI : CompactSpace P₀.A.left := QuasiCompact.compactSpace_of_compactSpace P₀.A.hom
  haveI : QuasiSeparatedSpace P₀.A.left := quasiSeparatedSpace_of_quasiSeparated P₀.A.hom
  obtain ⟨G₁, G₂⟩ := GlobalTheory.T.pointValue_eq_quotient_section_by_power_at_field P₀.A.left P₀.L P₀.isLB F ξ j₀ hj₀ k s hs
  have hβ := valR_ne_zero_sec P₀.L ξ j₀ hj₀ k s hs
  set β := valR ξ _ (s.f fun _ => j₀) with hβdef
  have v1 : valR ξ (nonzeroLocus s) 1 = 1 := by rw [WtAlg.valR_eq' ξ _ hs, map_one, map_one]
  have hM : ∀ m : ℕ, ((m + 1 : ℕ) : F) ≠ 0 := fun m h => by
    have : ψ ((m + 1 : ℕ) : K) = 0 := by rw [map_natCast]; exact h
    exact (Nat.cast_ne_zero.2 (Nat.succ_ne_zero m)) ((map_eq_zero ψ).1 this)

  have partD : ∀ f : Γ(P₀.A.left, nonzeroLocus s), ∃ f' : Γ(P₀.A.left, nonzeroLocus s),
      valR ξ _ f' = (k : F) * δ₀ (valR ξ _ f) - ∑ a, ∑ e, Λ a e * (δ a β / β) * δ e (valR ξ _ f) := by
    intro f
    obtain ⟨m₁, h₁⟩ := G₁ 1
    obtain ⟨m₂, h₂⟩ := G₁ f
    set m := max m₁ m₂
    obtain ⟨σ, hσ⟩ := h₁ (m + 1) (k * (m + 1)) (by omega) rfl
    obtain ⟨τ, hτ⟩ := h₂ (m + 1) (k * (m + 1)) (by omega) rfl
    obtain ⟨ρ, hρ⟩ := hyp (k * (m + 1)) (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))) σ τ
    obtain ⟨g, hg⟩ := G₂ (3 * (m + 1)) (3 * (k * (m + 1))) (by ring) ρ
    have e := hρ _ _ rfl rfl
    rw [hσ, hτ, hg, v1, symb_eq δ δ₀ Λ _ _ β hβ k m, symb_one] at e
    have e' : valR ξ _ g = ((m + 1 : ℕ) : F) * ((k : F) * δ₀ (valR ξ _ f) -
        ∑ a, ∑ e, Λ a e * (δ a β / β) * δ e (valR ξ _ f)) := by
      have h3 : β ^ (3 * (m + 1)) ≠ 0 := pow_ne_zero _ hβ
      rw [mul_comm (valR ξ _ g)] at e
      exact (mul_left_cancel₀ h3 e).symm
    refine ⟨constFn P₀.A.hom _ (((m + 1 : ℕ) : K)⁻¹) * g, ?_⟩
    rw [WtAlg.valR_mul'' ξ _ hs, GlobalTheory.LogKSBal.valR_constFn P₀.A.hom ξ hs hξ, e', map_inv₀, map_natCast,
      ← _root_.mul_assoc, inv_mul_cancel₀ (hM m), _root_.one_mul]

  have partT : ∀ f f' : Γ(P₀.A.left, nonzeroLocus s), ∃ h : Γ(P₀.A.left, nonzeroLocus s),
      valR ξ _ h = derivationBracketSum δ Λ (valR ξ _ f) (valR ξ _ f') := by
    intro f f'
    obtain ⟨m₁, h₁⟩ := G₁ f
    obtain ⟨m₂, h₂⟩ := G₁ f'
    obtain ⟨d, hd⟩ := partD f
    obtain ⟨d', hd'⟩ := partD f'
    set m := max m₁ m₂
    obtain ⟨σ, hσ⟩ := h₁ (m + 1) (k * (m + 1)) (by omega) rfl
    obtain ⟨τ, hτ⟩ := h₂ (m + 1) (k * (m + 1)) (by omega) rfl
    obtain ⟨ρ, hρ⟩ := hyp (k * (m + 1)) (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))) σ τ
    obtain ⟨g, hg⟩ := G₂ (3 * (m + 1)) (3 * (k * (m + 1))) (by ring) ρ
    have e := hρ _ _ rfl rfl
    rw [hσ, hτ, hg, symb_eq δ δ₀ Λ _ _ β hβ k m, symb_two, ← hd, ← hd'] at e
    have e' : valR ξ _ g = ((m + 1 : ℕ) : F) * valR ξ _ f * (valR ξ _ f * valR ξ _ d' - valR ξ _ f' * valR ξ _ d) -
        derivationBracketSum δ Λ (valR ξ _ f) (valR ξ _ f') := by
      have h3 : β ^ (3 * (m + 1)) ≠ 0 := pow_ne_zero _ hβ
      rw [mul_comm (valR ξ _ g)] at e
      exact (mul_left_cancel₀ h3 e).symm
    refine ⟨((m + 1 : ℕ) : Γ(P₀.A.left, nonzeroLocus s)) * f * (f * d' - f' * d) - g, ?_⟩
    rw [WtAlg.valR_sub' ξ _ hs, WtAlg.valR_mul'' ξ _ hs, WtAlg.valR_mul'' ξ _ hs, WtAlg.valR_sub' ξ _ hs,
      WtAlg.valR_mul'' ξ _ hs, WtAlg.valR_mul'' ξ _ hs, WtAlg.valR_natCast' ξ _ hs, e']
    ring
  refine ⟨fun f f' => ?_, partD⟩
  obtain ⟨h₁, e₁⟩ := partT (f + 1) f'
  obtain ⟨h₂, e₂⟩ := partT f f'
  refine ⟨h₁ - h₂, ?_⟩
  rw [WtAlg.valR_sub' ξ _ hs, e₁, e₂, WtAlg.valR_add' ξ _ hs, v1, tsum_add_one]

end GlobalTheory.HeatLoc
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.InvComb

open TrivSqZeroExt (inl inr)

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem tv_finsum {κ : Type} (s : Finset κ) (f : κ → TanM (𝟙 (Sp R)) G) :
    tv (∑ i ∈ s, f i) = ∏ i ∈ s, tv (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.prod_empty]; rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, PullbackSections.tv_add, ih]

theorem isField_comb (g : ℕ) (e : Fin g → Fld G.left) (he : ∀ c, IsField ⊤ (e c)) (a : Fin g → R) :
    IsField ⊤ (fun O f => ∑ c, constFn G.hom O (a c) * e c O f) := by
  refine ⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' h hW f => ?_⟩
  · have h1 := fun c => (he c).1 W hW f f'
    simp only [h1, mul_add, Finset.sum_add_distrib]
  · have h1 := fun c => (he c).2.1 W hW f f'
    simp only [h1, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun c _ => by ring
  · have h1 := fun c => (he c).2.2 W W' h hW f

    simp only [h1, map_sum, map_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← GlobalTheory.ArcPts.SecValue.res_constFn G.hom h (a c)]

theorem isInv_comb : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g : ℕ)
    (w : Fin g → TanM (𝟙 (Sp R)) G) (e : Fin g → Fld G.left), (∀ c, IsInv G (w c) (e c)) →
    ∀ a : Fin g → R, IsInv G (∑ c, a c • w c) (fun O f => ∑ c, constFn G.hom O (a c) * e c O f) := by
  intro R _ G _ _ g w e hw a
  refine ⟨isField_comb g e (fun c => (hw c).1) a, ?_⟩
  intro S _ φ x w' O f hx hO htr
  letI : Algebra R S := φ.toAlgebra
  have hG := GlobalTheory.Heat.CoeffWt.isGrpPullback_self G
  choose u hu using fun c => PullbackSections.push_surj hG (tv (w c))
  have hul : ∀ c, (u c).left = (tv (w c)).left := fun c =>
    (Category.comp_id _).symm.trans (congrArg (fun q => q.left) (hu c))
  have ht : ∀ c, IsTangent (u c) := fun c => (PullbackSections.isTangent_iff hG _).2 (by rw [hu c]; exact PullbackSections.tv_mem _)
  let z0 : Chart.sp (R₀ := R) S ⟶ G := Over.homMk x hx
  let z : Chart.sp (R₀ := R) (DualNumber S) ⟶ G := Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z0
  let ee : Fin g → DualNumber S := fun c => inr (φ (a c))
  have hee : ∀ i j, ee i * ee j = 0 := fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _
  obtain ⟨a₁, a₂⟩ := GlobalTheory.ZH.CrdCalc.valR_spMap (GlobalTheory.SqZero.inlS R S).toRingHom x O hO
  obtain ⟨b₁, b₂⟩ := GlobalTheory.Heat.CoeffWt.valR_prod hul ht hw ee hee z O a₁ Finset.univ

  choose U hU using PullbackSections.push_surj hG (tv (∑ c, a c • w c))
  have hU' : U = ∏ c, PullbackSections.scK (a c) (u c) := by
    refine PullbackSections.push_inj hG ?_
    rw [hU, map_prod, tv_finsum]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [PullbackSections.push_scK, hu c, PullbackSections.tv_smul]
  have hUl : U.left = (tv (∑ c, a c • w c)).left :=
    (Category.comp_id _).symm.trans (congrArg (fun q => q.left) hU)
  obtain ⟨g', v', hg', hv', rfl⟩ := htr
  let ρ : Chart.sp (R₀ := R) (DualNumber S) ⟶ tEpsG (x ≫ G.hom) := Over.homMk (𝟙 _) (by
    rw [hx]
    refine (Category.id_comp _).trans ?_
    exact (Spec.map_comp (CommRingCat.ofHom (algebraMap R S)) (CommRingCat.ofHom (algebraMap S (DualNumber S)))).symm)
  have k₁ : ρ ≫ g' = z := Over.OverMorphism.ext ((Category.id_comp _).trans hg')
  have k₂ : ρ ≫ v' = ∏ c, (Chart.spMap (GlobalTheory.SqZero.epsTo R (ee c) (hee c c)) ≫ u c :
      Chart.sp (R₀ := R) (DualNumber S) ⟶ G) := by
    have k₃ : ρ ≫ v' = Chart.spMap (GlobalTheory.SqZero.dualMap (Algebra.ofId R S)) ≫ U := by
      refine Over.OverMorphism.ext ((Category.id_comp _).trans (hv'.trans ?_))
      show _ = _ ≫ U.left
      rw [hUl]
      refine congrArg (fun q : DualNumber R →+* DualNumber S => spMap q ≫ _) (RingHom.ext fun r => ?_)
      ext <;> simp [dualMap, Algebra.smul_def, TrivSqZeroExt.algebraMap_eq_inl] <;> rfl
    rw [k₃, hU', comp_prodT]
    refine Finset.prod_congr rfl fun c _ => Over.OverMorphism.ext ?_
    show _ ≫ spMap (epsScaleR (a c)) ≫ (u c).left = _ ≫ (u c).left
    rw [← Category.assoc]
    refine congrArg (· ≫ (u c).left) ?_
    simp only [Chart.spMap_left, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r <;> simp [epsScaleR, GlobalTheory.SqZero.epsTo, GlobalTheory.SqZero.dualTo_apply, ee, Algebra.smul_def] <;> rfl
  have key : (g' * v').left = ((∏ c, (Chart.spMap (GlobalTheory.SqZero.epsTo R (ee c) (hee c c)) ≫ u c :
      Chart.sp (R₀ := R) (DualNumber S) ⟶ G)) * z).left := by
    rw [← k₂, ← k₁, _root_.mul_comm, ← MonObj.comp_mul]
    exact (Category.id_comp _).symm
  rw [key, b₂ f]
  have a₃ : ∀ h, valR z.left O h = inl (valR x O h) := a₂
  simp only [a₃]
  show _ = valR x O (∑ c, constFn G.hom O (a c) * e c O f)

  conv_rhs => rw [GlobalTheory.ZH.CrdCalc.valR_eq x O hO, map_sum]
  simp only [map_mul, ← GlobalTheory.ZH.CrdCalc.valR_eq x O hO]
  rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, zero_add, TrivSqZeroExt.snd_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [GlobalTheory.ZH.CrdCalc.valR_mul x O hO, GlobalTheory.ArcPts.SecValue.valR_constFn G.hom φ x hx O hO]
  simp [ee, mul_comm]

end GlobalTheory.Heat.InvComb
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.FormalDer

open TrivSqZeroExt (inl inr)
open ReciprocityTheory.ChartRestriction.G.Chart (sp)

theorem isLocalRing_dual (Ω : Type) [CommRing Ω] [IsLocalRing Ω] : IsLocalRing (DualNumber Ω) := by
  have : Nontrivial (DualNumber Ω) := (TrivSqZeroExt.inl_injective (R := Ω) (M := Ω)).nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun y => ?_
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]
  simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self y.fst

theorem mem_pow_map {Ω : Type} [CommRing Ω] (K : Ideal Ω) (n : ℕ) (y : DualNumber Ω)
    (hy : y ∈ (K.map (algebraMap Ω (DualNumber Ω))) ^ n) : y.fst ∈ K ^ n ∧ y.snd ∈ K ^ n := by
  rw [← Ideal.map_pow] at hy
  let S : Ideal (DualNumber Ω) :=
    { carrier := {y | y.fst ∈ K ^ n ∧ y.snd ∈ K ^ n}
      add_mem' := fun ha hb => ⟨by simpa using add_mem ha.1 hb.1, by simpa using add_mem ha.2 hb.2⟩
      zero_mem' := ⟨by simp, by simp⟩
      smul_mem' := fun c y hy => ⟨by simpa using Ideal.mul_mem_left _ c.fst hy.1, by
        simpa [TrivSqZeroExt.snd_mul, smul_eq_mul, _root_.mul_comm] using
          add_mem (Ideal.mul_mem_left _ c.fst hy.2) (Ideal.mul_mem_left _ c.snd hy.1)⟩ }
  have : (K ^ n).map (algebraMap Ω (DualNumber Ω)) ≤ S :=
    Ideal.map_le_iff_le_comap.2 fun r hr => ⟨by simpa [TrivSqZeroExt.algebraMap_eq_inl] using hr, by
      simp [TrivSqZeroExt.algebraMap_eq_inl]⟩
  exact this hy

theorem isHausdorff_dual {R Ω : Type} [CommRing R] [CommRing Ω] (φ : R →+* Ω) (I : Ideal R)
    [h : IsHausdorff (I.map φ) Ω] :
    IsHausdorff (I.map ((algebraMap Ω (DualNumber Ω)).comp φ)) (DualNumber Ω) := by
  rw [← Ideal.map_map]
  refine ⟨fun y hy => ?_⟩
  have h' : ∀ n, y.fst ∈ (I.map φ) ^ n ∧ y.snd ∈ (I.map φ) ^ n := fun n => mem_pow_map _ n y (by
    have := hy n
    rwa [SModEq.zero, smul_eq_mul, Ideal.mul_top] at this)
  ext
  · exact h.haus y.fst fun n => by rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]; exact (h' n).1
  · exact h.haus y.snd fun n => by rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]; exact (h' n).2

theorem exists_tangent_lift {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (v : TanM (𝟙 (Sp R)) G) : ∃ u : epsR R ⟶ G, u.left = (tv v).left ∧ IsTangent u := by
  have h := CoeffWt.isGrpPullback_self G
  obtain ⟨u, e⟩ := PullbackSections.push_surj h (tv v)
  exact ⟨u, (Category.comp_id _).symm.trans (congrArg (fun q => q.left) e),
    (PullbackSections.isTangent_iff h _).2 (by rw [e]; exact PullbackSections.tv_mem _)⟩

theorem epsHom_comp {R Ω : Type} [CommRing R] [CommRing Ω] (φ : R →+* Ω) (δ : Derivation ℤ Ω Ω)
    (hδφ : ∀ r, δ (φ r) = 0) :
    letI : Algebra R Ω := φ.toAlgebra
    (epsHom δ).comp φ = algebraMap R (DualNumber Ω) := by
  letI : Algebra R Ω := φ.toAlgebra
  refine RingHom.ext fun r => TrivSqZeroExt.ext ?_ ?_
  · show (epsHom δ (φ r)).fst = (algebraMap R (DualNumber Ω) r).fst
    simp [epsHom, TrivSqZeroExt.algebraMap_eq_inl']
    rfl
  · show (epsHom δ (φ r)).snd = (algebraMap R (DualNumber Ω) r).snd
    simp [epsHom, TrivSqZeroExt.algebraMap_eq_inl', hδφ]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Fin n → TanM (𝟙 (Sp R)) Y.H) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vH a) (dd a)) → ∀ (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∀ (dd' : Fin n → Fld t.G.left), (∀ a, IsInv t.G (v' a) (dd' a)) → ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x : Sp Ω ⟶ Y.H.left) (δ : Fin n → Derivation ℤ Ω Ω), IsAdicComplete ((maximalIdeal R).map φ) Ω → ∀ (hx : x ≫ Y.H.hom = spMap φ), (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) → ∀ (x' : Sp Ω ⟶ t.G.left) (hx' : x' ≫ t.G.hom = spMap φ), GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx)) (Over.homMk x' hx') → ∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f) := by
  intro E _ _ _ H R _ _ _ _ _ _ t P
  letI := H.starRing
  intro Y n vH dd hdd v' hv' dd' hdd' Ω _ _ _ φ x δ hcomp hx hδφ hδ x' hx' hxx' a O f hO
  letI : Algebra R Ω := φ.toAlgebra
  have hε : (inr 1 : DualNumber Ω) * inr 1 = 0 := TrivSqZeroExt.inr_mul_inr _ _ _
  haveI := isLocalRing_dual Ω
  haveI : IsHausdorff ((maximalIdeal R).map (algebraMap R (DualNumber Ω))) (DualNumber Ω) :=
    isHausdorff_dual φ (maximalIdeal R)
  let jη : epsR R ⟶ overAt (𝟙 (Sp R)) (DualNumber R) := Over.homMk (𝟙 _) (by simp)
  obtain ⟨u₀, hu₀, hut₀⟩ := exists_tangent_lift Y.H (vH a)
  obtain ⟨u₁, hu₁, hut₁⟩ := exists_tangent_lift t.G (v' a)
  have eu₀ : u₀ = jη ≫ tv (vH a) := Over.OverMorphism.ext (hu₀.trans (Category.id_comp _).symm)
  have eu₁ : u₁ = jη ≫ tv (v' a) := Over.OverMorphism.ext (hu₁.trans (Category.id_comp _).symm)
  let T : Over (Sp R) := Over.mk (spMap φ)
  let xt : T ⟶ Y.H := Over.homMk x hx
  let xt' : T ⟶ t.G := Over.homMk x' hx'
  let kz : sp (R₀ := R) (DualNumber Ω) ⟶ T := Over.homMk (spMap (algebraMap Ω (DualNumber Ω))) (by
    show spMap _ ≫ spMap φ = Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber Ω)))
    rw [spMap, spMap, ← Spec.map_comp]
    rfl)
  let kε : sp (R₀ := R) (DualNumber Ω) ⟶ T := Over.homMk (spMap (epsHom (δ a))) (by
    show spMap _ ≫ spMap φ = Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber Ω)))
    rw [spMap, spMap, ← Spec.map_comp]
    exact congrArg (fun q => Spec.map (CommRingCat.ofHom q)) (epsHom_comp φ (δ a) (hδφ a)))
  let kk := Chart.spMap (GlobalTheory.SqZero.epsTo R (inr 1 : DualNumber Ω) hε) ≫ jη
  let z : sp (R₀ := R) (DualNumber Ω) ⟶ Y.H := kz ≫ xt
  let z' : sp (R₀ := R) (DualNumber Ω) ⟶ t.G := kz ≫ xt'
  let yH := (Chart.spMap (GlobalTheory.SqZero.epsTo R (inr 1 : DualNumber Ω) hε) ≫ u₀) * z
  let yG := (Chart.spMap (GlobalTheory.SqZero.epsTo R (inr 1 : DualNumber Ω) hε) ≫ u₁) * z'

  have e₁ : yH = kε ≫ xt := by
    refine CoeffWt.eq_of_valR Y yH (kε ≫ xt) ⊤ (x (closedPoint Ω)) trivial fun V' _ hp => ?_
    have m : ⊤ ≤ x ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V') := (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of Ω) x hp).ge
    obtain ⟨a₁, a₂⟩ := GlobalTheory.ZH.CrdCalc.valR_spMap (algebraMap Ω (DualNumber Ω)) x _ m
    obtain ⟨b₁, b₂⟩ := GlobalTheory.ZH.CrdCalc.valR_spMap (epsHom (δ a)) x _ m
    obtain ⟨c₁, c₂⟩ := CoeffWt.valR_translate hu₀ hut₀ (hdd a) (inr 1 : DualNumber Ω) hε z _ a₁
    refine ⟨c₁, b₁, fun α g _ => ?_⟩
    refine (c₂ g).trans (Eq.trans ?_ (b₂ g).symm)
    show valR (spMap (algebraMap Ω (DualNumber Ω)) ≫ x) _ g +
      inr 1 * valR (spMap (algebraMap Ω (DualNumber Ω)) ≫ x) _ (dd a _ g) = _
    rw [a₂, a₂, hδ a _ g m]
    ext <;> simp [epsHom, TrivSqZeroExt.algebraMap_eq_inl']
  have hG : GlobalFnsSt := GlobalTheory.allSixLaws.1.globalFns
  have pz := hxx'.pull kz (Y.rep.1 _ _ kz xt)
  have pu := (hv' a).pull (Chart.spMap (GlobalTheory.SqZero.epsTo R (inr 1 : DualNumber Ω) hε) ≫ jη)
    (Y.rep.1 _ _ (Chart.spMap (GlobalTheory.SqZero.epsTo R (inr 1 : DualNumber Ω) hε) ≫ jη) (tv (vH a)))
  rw [Category.assoc, Category.assoc, ← eu₀, ← eu₁] at pu
  have pm := FormalPoint.IsPointOf.mul hG pu pz (Y.rep.2 _ _ _)
  have pε := hxx'.pull kε (Y.rep.1 _ _ kε xt)
  have e₂ : yG = kε ≫ xt' := by
    have pm' : FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (kε ≫ xt)) yG := by
      rw [← e₁]; exact pm
    exact FormalPoint.IsPointOf.unique pm' pε
  obtain ⟨a₁, a₂⟩ := GlobalTheory.ZH.CrdCalc.valR_spMap (algebraMap Ω (DualNumber Ω)) x' O hO
  obtain ⟨b₁, b₂⟩ := GlobalTheory.ZH.CrdCalc.valR_spMap (epsHom (δ a)) x' O hO
  obtain ⟨c₁, c₂⟩ := CoeffWt.valR_translate hu₁ hut₁ (hdd' a) (inr 1 : DualNumber Ω) hε z' O a₁
  have hz : ∀ g, valR z'.left O g = algebraMap Ω (DualNumber Ω) (valR x' O g) := a₂
  have k : valR yG.left O f = valR (spMap (epsHom (δ a)) ≫ x') O f := by
    rw [e₂]
    rfl
  have k2 : algebraMap Ω (DualNumber Ω) (valR x' O f) +
      inr 1 * algebraMap Ω (DualNumber Ω) (valR x' O (dd' a O f)) = epsHom (δ a) (valR x' O f) := by
    rw [← hz, ← hz, ← c₂, k, b₂]
  have k3 := congrArg TrivSqZeroExt.snd k2
  simpa [epsHom, TrivSqZeroExt.algebraMap_eq_inl'] using k3

end GlobalTheory.Heat.FormalDer
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.raynaudExtension_invariantField_coeffs_unique : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (W : Y.H.left.Opens) (c : Fin n → Γ(Y.H.left, W)), (∀ Wo : Y.H.left.Opens, Wo ≤ W → ∀ f, ∑ a, rsT (c a) Wo * dd a Wo f = 0) → ∀ a, c a = 0 := by
  first | exact @GlobalTheory.HxUniq.raynaud_coeff_eq_zero | exact GlobalTheory.HxUniq.raynaud_coeff_eq_zero | (intros; apply GlobalTheory.HxUniq.raynaud_coeff_eq_zero <;> assumption)
end
