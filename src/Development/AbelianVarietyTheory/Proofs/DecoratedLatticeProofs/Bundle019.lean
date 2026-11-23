module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle043
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOfMemSB
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharEqOneOfOpENeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle031
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle016
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

theorem _root_.GlobalTheory.T.exists_weilSourceAction_and_smooth : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)), (∃ ρ' : Representation ℂ (GL a k) (SB (Matrix b a k)), IsSrc μ ρ') ∧ ∀ ρ' : Representation ℂ (GL a k) (SB (Matrix b a k)), IsSrc μ ρ' → IsSmoothRep ρ' := by
  first | exact @GlobalTheory.PosOne.isSrc_exists_isSmoothRep | exact GlobalTheory.PosOne.isSrc_exists_isSmoothRep | (intros; apply GlobalTheory.PosOne.isSrc_exists_isSmoothRep <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

noncomputable section
namespace GlobalTheory.PosOne.ToOnePos

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem toOne_lin (ψ : AddChar k Circle) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure]
    {A : Type} [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (hσ : IsSmoothRep σ) :
    ∀ m : ℕ, m + 1 ≤ c → ∀ l : A →ₗ[ℂ] ℂ, IsNEquiv ψ (m + 1) σ l →
      ∃ l₁ : A →ₗ[ℂ] ℂ, (∀ v, l₁ v = toOne ν σ (m + 1) l v) ∧ IsNEquiv ψ 1 σ l₁ := by
  intro m
  induction m with
  | zero => intro _ l hl; exact ⟨l, fun v => rfl, hl⟩
  | succ m ih =>
    intro hm l hl
    obtain ⟨l', hl'v, hl'⟩ := (GlobalTheory.RootEx.Exchange.exchange_isPos k n c (m + 1) (by omega) (by omega) ψ hψ hψ1
      ν A σ hσ).2.1 l hl
    obtain ⟨l₁, hl₁v, hl₁⟩ := ih (by omega) l' hl'
    refine ⟨l₁, fun v => ?_, hl₁⟩
    rw [hl₁v, toOne_succ]
    congr 1
    funext w
    exact hl'v w

theorem toOne_bil (ψ : AddChar k Circle) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure]
    {A : Type} [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (hσ : IsSmoothRep σ)
    {P : Type} [AddCommGroup P] [Module ℂ P] (π : Representation ℂ (GL n k) P) :
    ∀ m : ℕ, m + 1 ≤ c → ∀ b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ, IsPos ψ (m + 1) π σ b →
      ∃ b₁ : P →ₗ[ℂ] A →ₗ[ℂ] ℂ, (∀ φ v, b₁ φ v = toOne ν σ (m + 1) (b φ) v) ∧ IsPos ψ 1 π σ b₁ := by
  intro m
  induction m with
  | zero => intro _ b hb; exact ⟨b, fun φ v => rfl, hb⟩
  | succ m ih =>
    intro hm b hb
    obtain ⟨b', hb'v, hb'⟩ := ((GlobalTheory.RootEx.Exchange.exchange_isPos k n c (m + 1) (by omega) (by omega) ψ hψ hψ1
      ν A σ hσ).2.2 P π b).2 hb
    obtain ⟨b₁, hb₁v, hb₁⟩ := ih (by omega) b' hb'
    refine ⟨b₁, fun φ v => ?_, hb₁⟩
    rw [hb₁v, toOne_succ]
    congr 1
    funext w
    exact hb'v φ w

variable {n' : Type} [Fintype n'] [DecidableEq n']

def omRep (μ : kˣ →* ℂˣ) (hμ : IsOpen (μ.ker : Set kˣ)) : Representation ℂ (GL n k) (SB (Matrix n n' k)) where
  toFun g :=
    { toFun := fun Ψ => ⟨om μ 1 g Ψ.1,
        (GlobalTheory.SplitWeil.om_isSmoothRepresentation k n' n μ hμ).2.2.2.1 1 g Ψ.1 Ψ.2⟩
      map_add' := fun Ψ Ψ' => by
        apply Subtype.ext
        have := (GlobalTheory.SplitWeil.om_isSmoothRepresentation k n' n μ hμ).2.2.1 1 g 1 Ψ.1 Ψ'.1
        simpa using this
      map_smul' := fun z Ψ => by
        apply Subtype.ext
        have := (GlobalTheory.SplitWeil.om_isSmoothRepresentation k n' n μ hμ).2.2.1 1 g z Ψ.1 0
        have h0 : om μ 1 g (0 : Matrix n n' k → ℂ) = 0 := by
          funext x
          simp [om]
        simpa [h0] using this }
  map_one' := by
    ext Ψ : 2
    exact (GlobalTheory.SplitWeil.om_isSmoothRepresentation k n' n μ hμ).1 Ψ.1
  map_mul' g h := by
    ext Ψ : 2
    have := (GlobalTheory.SplitWeil.om_isSmoothRepresentation k n' n μ hμ).2.1 1 1 g h Ψ.1
    simpa using this

theorem bilPos_iff (ψ : AddChar k Circle) (μ : kˣ →* ℂˣ) (hμ : IsOpen (μ.ker : Set kˣ)) (p : ℕ)
    {A : Type} [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)
    (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) : BilPos ψ μ p σ B ↔ IsPos ψ p (omRep μ hμ) σ B := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun g Ψ v => h2 g Ψ _ v rfl⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun g Ψ Ψ₁ v hΨ => ?_⟩
    have : Ψ₁ = omRep μ hμ g Ψ := Subtype.ext hΨ
    subst this
    exact h2 g Ψ v

end GlobalTheory.PosOne.ToOnePos


open GlobalTheory.PosOne.ToOnePos in
theorem GlobalTheory.PosOne.toOne_isPosOne : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c P : ℕ) (_ : 1 ≤ P) (_ : P ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ), (∀ l : A →ₗ[ℂ] ℂ, IsNEquiv ψ P σ l → ∃ l₁ : A →ₗ[ℂ] ℂ, (∀ v, l₁ v = toOne ν σ P l v) ∧ IsNEquiv ψ 1 σ l₁) ∧ ∀ (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ), BilPos ψ μ P σ B → ∃ B₁ : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ, (∀ Ψ v, B₁ Ψ v = toOne ν σ P (B Ψ) v) ∧ BilPos ψ μ 1 σ B₁ := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c P hP hPc ψ hψ hψ1 ν _ A _ _ σ hσ
  obtain ⟨m, rfl⟩ : ∃ m, P = m + 1 := ⟨P - 1, by omega⟩
  refine ⟨toOne_lin ψ hψ hψ1 ν σ hσ m hPc, fun μ hμ B hB => ?_⟩
  obtain ⟨B₁, hB₁v, hB₁⟩ := toOne_bil ψ hψ hψ1 ν σ hσ (omRep μ hμ) m hPc B ((bilPos_iff ψ μ hμ _ σ B).1 hB)
  exact ⟨B₁, hB₁v, (bilPos_iff ψ μ hμ 1 σ B₁).2 hB₁⟩
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

namespace GlobalTheory.PosOne

theorem covers_opE_finite : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (J : Subgroup (GL (n ⊕ Fin c) k)) (_ : IsOpen (J : Set (GL (n ⊕ Fin c) k))) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), ∃ T, Covers p J T fun h => opE ψ ν p (om μ 1 h Φ.1) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p hp1 hpc ψ hψc hψ ν _ μ _ J hJ Φ
  classical
  obtain ⟨Λ, hΛ, hper⟩ := exists_isOpen_addSubgroup_add_eq Φ.2.1 Φ.2.2
  obtain ⟨Ω, hΩ, hcov⟩ := opE_support_compact_mod_R k n n' c p hp1 hpc ψ hψc hψ ν (tsupport Φ.1) Φ.2.2 Λ hΛ
  obtain ⟨F, hF⟩ := hΩ.elim_finite_subcover (fun w : GL (n ⊕ Fin c) k => (fun g => w⁻¹ * g) ⁻¹' (J : Set _))
    (fun w => hJ.preimage (continuous_const.mul continuous_id))
    (fun w _ => Set.mem_iUnion.2 ⟨w, by simp [J.one_mem]⟩)
  let rep : GL (n ⊕ Fin c) k → GL (n ⊕ Fin c) k := fun w => Quotient.out (DoubleCoset.mk (R k n c p) J w)
  have hrep : ∀ w, DoubleCoset.mk (R k n c p) J (rep w) = DoubleCoset.mk (R k n c p) J w :=
    fun w => DoubleCoset.out_eq' _
  refine ⟨F.image rep, ?_, ?_⟩
  · intro a ha b hb hab
    simp only [Finset.coe_image, Set.mem_image] at ha hb
    obtain ⟨w₁, -, rfl⟩ := ha
    obtain ⟨w₂, -, rfl⟩ := hb
    rw [hrep, hrep] at hab
    simp only [rep, hab]
  · intro h hh
    obtain ⟨x₀, hx₀⟩ := Function.ne_iff.1 hh
    obtain ⟨r, hr, w, hw, rfl⟩ := hcov μ Φ.1 (subset_tsupport _) (fun x y hy => hper x y hy) (fun _ => 1)
      (IsLocallyConstant.const 1) h x₀ (by simpa using hx₀)
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hF hw)
    obtain ⟨hiF, hiw⟩ := Set.mem_iUnion.1 hi
    refine ⟨rep i, Finset.mem_image_of_mem _ hiF, ?_⟩
    rw [hrep, eq_comm, DoubleCoset.eq]
    exact ⟨r, hr, i⁻¹ * w, hiw, by group⟩

end GlobalTheory.PosOne
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

theorem _root_.GlobalTheory.T.exists_finset_integralScaledBoxPi_coset_reps : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (r R : kˣ), valuation k (r : k) ≤ valuation k (R : k) → ∃ S : Finset (n → k), (∀ b ∈ S, b ∈ box n R) ∧ ∀ a ∈ box n R, ∃! b, b ∈ S ∧ a - b ∈ box n r := by
  first | exact @GlobalTheory.BoxReps.exists_finset_box_reps | exact GlobalTheory.BoxReps.exists_finset_box_reps | (intros; apply GlobalTheory.BoxReps.exists_finset_box_reps <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

theorem _root_.GlobalTheory.T.exists_integralScaledBoxPi_superset_of_isCompact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (K : Set (n → k)), IsCompact K → ∀ r : kˣ, ∃ R : kˣ, valuation k (r : k) ≤ valuation k (R : k) ∧ K ⊆ box n R := by
  first | exact @GlobalTheory.exists_box_superset_of_isCompact | exact GlobalTheory.exists_box_superset_of_isCompact | (intros; apply GlobalTheory.exists_box_superset_of_isCompact <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

theorem _root_.GlobalTheory.T.integral_box_invariant_eq_measureReal_mul_sum_reps : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (n : Type) [Fintype n] (r R : kˣ) (S : Finset (n → k)), (∀ b ∈ S, b ∈ box n R) → (∀ a ∈ box n R, ∃! b, b ∈ S ∧ a - b ∈ box n r) → ∀ F : (n → k) → ℂ, (∀ t ∈ box n r, ∀ y, F (y + t) = F y) → (∀ y ∉ box n R, F y = 0) → ∫ y, F y ∂(Measure.pi fun _ => ν) = ((Measure.pi fun _ : n => ν).real (box n r) : ℂ) * ∑ b ∈ S, F b := by
  first | exact @GlobalTheory.SplitWeil.FourierPi.integral_eq_measureReal_box_mul_sum | exact GlobalTheory.SplitWeil.FourierPi.integral_eq_measureReal_box_mul_sum | (intros; apply GlobalTheory.SplitWeil.FourierPi.integral_eq_measureReal_box_mul_sum <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

theorem _root_.GlobalTheory.T.sum_integralScaledBoxPi_coset_reps_shift_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (r R : kˣ) (S : Finset (n → k)), (∀ b ∈ S, b ∈ box n R) → (∀ a ∈ box n R, ∃! b, b ∈ S ∧ a - b ∈ box n r) → ∀ F : (n → k) → ℂ, (∀ t ∈ box n r, ∀ y, F (y + t) = F y) → ∀ a ∈ box n R, ∑ b ∈ S, F (a + b) = ∑ b ∈ S, F b := by
  first | exact @GlobalTheory.CosetSumShift.sum_shift | exact GlobalTheory.CosetSumShift.sum_shift | (intros; apply GlobalTheory.CosetSumShift.sum_shift <;> assumption)
end
