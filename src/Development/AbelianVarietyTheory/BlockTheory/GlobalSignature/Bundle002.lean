module

public import Formalism.LocalRingCardinality.DataCD
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding

open MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped ENNReal

abbrev Sp (P Q : ℕ) : Type := Fin P ⊕ Fin Q → ℂ

def herm {P Q : ℕ} (x y : Sp P Q) : ℂ :=
  ∑ i : Fin P, x (Sum.inl i) * star (y (Sum.inl i)) -
    ∑ j : Fin Q, x (Sum.inr j) * star (y (Sum.inr j))

def qf {P Q : ℕ} (x : Sp P Q) : ℝ :=
  ∑ i : Fin P, Complex.normSq (x (Sum.inl i)) - ∑ j : Fin Q, Complex.normSq (x (Sum.inr j))

open MeasureTheory Matrix in
open scoped ENNReal in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.herm_self {P Q : ℕ} (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.herm x x = (_root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.qf x : ℂ) := by
  simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.herm, _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.qf, Complex.star_def,
    Complex.mul_conj]

open MeasureTheory Matrix in
open scoped ENNReal in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.herm_eq_hform {P Q : ℕ} (x y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.herm x y = _root_.Formalism.UG.hform (starRingEnd ℂ) (_root_.Formalism.UG.Jpq P Q) y x := by
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.herm, _root_.Formalism.UG.hform, _root_.Formalism.UG.Jpq, Fintype.sum_sum_type,
    fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
    Matrix.one_apply, Matrix.neg_apply, Matrix.zero_apply, Complex.star_def]
  simp [mul_comm, sub_eq_add_neg, Finset.sum_neg_distrib]

def dx (P Q : ℕ) : Measure (Sp P Q) := ((2 : ℝ≥0∞) ^ (P + Q)) • (volume : Measure (Sp P Q))

def cM (M : ℕ) : ℝ := (2 * Real.pi) ^ M / ((M - 1).factorial : ℝ)

open MeasureTheory Matrix in
open scoped ENNReal in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.cM_pos (M : ℕ) : 0 < _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.cM M := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.cM
  positivity

def IsDxDq {P Q : ℕ} (fib : ℝ → Measure (Sp P Q)) : Prop :=
  IsFibreFamily (dx P Q) (qf : Sp P Q → ℝ) id {x | x ≠ 0} (volume : Measure ℝ) Set.univ fib

def act {P Q : ℕ} (g : UpqT P Q) (x : Sp P Q) : Sp P Q := UpqT.mat g *ᵥ x

def IsPerpEmb {P Q P' Q' : ℕ} (x₀ : Sp P Q)
    (A : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ) (j : UpqT P' Q' → UpqT P Q) : Prop :=
  (∀ u v : Sp P' Q', herm (A *ᵥ u) (A *ᵥ v) = herm u v) ∧
  (∀ y : Sp P Q, herm y x₀ = 0 ↔ ∃ u : Sp P' Q', A *ᵥ u = y) ∧
  (∀ g : UpqT P' Q', act (j g) x₀ = x₀ ∧ ∀ u : Sp P' Q', act (j g) (A *ᵥ u) = A *ᵥ act g u)

def IsSection {P Q : ℕ} (β : ℝ) (x₀ : Sp P Q) (s : Sp P Q → UpqT P Q) : Prop :=
  Measurable s ∧ ∀ y : Sp P Q, qf y = β → act (s y) x₀ = y

def QuotFormula (c : CDHaar) (P Q P' Q' : ℕ) (β : ℝ) : Prop :=
  ∀ x₀ : Sp P Q, qf x₀ = β →
    AllSome
      (fun Aj : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ × (UpqT P' Q' → UpqT P Q) =>
        IsPerpEmb x₀ Aj.1 Aj.2)
      (fun Aj =>
        Set.range Aj.2 = {g | act g x₀ = x₀} ∧
        AllSome (fun fib : ℝ → Measure (Sp P Q) => IsDxDq fib) (fun fib =>
          AllSome (fun s : Sp P Q → UpqT P Q => IsSection β x₀ s) (fun s =>
            ∀ f : UpqT P Q → ℝ≥0∞, Measurable f →
              ∫⁻ g, f g ∂(c.cd P Q) =
                (ENNReal.ofReal (cM (P + Q)))⁻¹ *
                  ∫⁻ y, (∫⁻ g', f (s y * Aj.2 g') ∂(c.cd P' Q')) ∂(fib β))))

def CompactDualQuotient : Prop :=
  ∀ (c : CDHaar) (P Q : ℕ),
    QuotFormula c (P + 1) Q P Q 1 ∧ QuotFormula c P (Q + 1) P Q (-1)

def SelfDualReal : Prop :=
  ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
    (∀ P Q : ℕ, SelfDual (dx P Q) (fun x y : Sp P Q =>
      Complex.exp (2 * Real.pi * Complex.I * ((ε * (2 * (herm x y).re) : ℝ) : ℂ)))) ∧
    SelfDual (volume : Measure ℝ)
      (fun t s : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((ε * (t * s) : ℝ) : ℂ)))

def SphereMass : Prop :=
  ∀ M : ℕ, 1 ≤ M → AllSome (fun fib : ℝ → Measure (Sp M 0) => IsDxDq fib)
    (fun fib => fib 1 Set.univ = ENNReal.ofReal (cM M))

end GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding
end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ActionCoordinates

open MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped ENNReal

abbrev Wsp (P Q : ℕ) : Type := Fin P ⊕ Fin Q → ℂ

def sgn {P Q : ℕ} : Fin P ⊕ Fin Q → ℂ := Sum.elim (fun _ => 1) (fun _ => -1)

def herm {P Q : ℕ} (x y : Wsp P Q) : ℂ := ∑ j, sgn j * x j * (starRingEnd ℂ) (y j)

def qf {P Q : ℕ} (x : Wsp P Q) : ℝ := (herm x x).re

def bil {P Q : ℕ} (x y : Wsp P Q) : ℝ := Algebra.trace ℝ ℂ (herm x y)

theorem herm_self {P Q : ℕ} (x : Wsp P Q) : herm x x = (qf x : ℂ) := by
  have term : ∀ j, sgn j * x j * (starRingEnd ℂ) (x j) =
      (((sgn j).re * Complex.normSq (x j) : ℝ) : ℂ) := by
    intro j
    rw [mul_assoc, Complex.mul_conj]
    rcases j with j | j <;> simp [sgn]
  unfold qf herm
  simp_rw [term]
  rw [← Complex.ofReal_sum, Complex.ofReal_re]

def fourierT {V : Type} [MeasurableSpace V] (e : ℝ) (β : V → V → ℝ) (μ : Measure V)
    (Φ : V → ℂ) (y : V) : ℂ :=
  ∫ x, Φ x * Complex.exp (2 * Real.pi * Complex.I * ((e * β x y : ℝ) : ℂ)) ∂μ

def IsSelfDualFor {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
    (e : ℝ) (β : V → V → ℝ) (μ : Measure V) : Prop :=
  ∀ Φ : SchwartzMap V ℂ, Integrable (⇑Φ) μ ∧ Integrable (fourierT e β μ Φ) μ ∧
    ∀ x, fourierT e β μ (fourierT e β μ Φ) x = Φ (-x)

def dx (P Q : ℕ) : Measure (Wsp P Q) := (2 : ℝ≥0∞) ^ (P + Q) • volume

def cM (M : ℕ) : ℝ≥0∞ := ENNReal.ofReal ((2 * Real.pi) ^ M / (Nat.factorial (M - 1) : ℝ))

def IsDxDq {P Q : ℕ} (β : ℝ) (fib : ℝ → Measure (Wsp P Q)) : Prop :=
  ∃ (U : Set (Wsp P Q)) (B : Set ℝ), {x | x ≠ 0} ⊆ U ∧ IsOpen B ∧ β ∈ B ∧
    IsFibreFamily (dx P Q) qf id U (volume : Measure ℝ) B fib

def act {P Q : ℕ} (g : UpqT P Q) (x : Wsp P Q) : Wsp P Q := (UpqT.mat g).mulVec x

def IsPerpFrame {P Q P' Q' : ℕ} (x₀ : Wsp P Q) (j : Wsp P' Q' →ₗ[ℂ] Wsp P Q)
    (ι : UpqT P' Q' → UpqT P Q) : Prop :=
  (∀ v w, herm (j v) (j w) = herm v w) ∧
  (∀ y, herm y x₀ = 0 ↔ ∃ v, j v = y) ∧
  (∀ g', act (ι g') x₀ = x₀ ∧ ∀ v, act (ι g') (j v) = j (act g' v))

def SelfDualMeasures : Prop :=
  ∀ e : ℝ, (e = 1 ∨ e = -1) →
    (∀ (P Q : ℕ) (μ : Measure (Wsp P Q)), μ.IsAddHaarMeasure →
      (IsSelfDualFor e bil μ ↔ μ = dx P Q)) ∧
    (∀ ν : Measure ℝ, ν.IsAddHaarMeasure →
      (IsSelfDualFor e (fun t s : ℝ => t * s) ν ↔ ν = volume))

def SphereVolume : Prop :=
  ∀ M : ℕ, 1 ≤ M → ∀ fib : ℝ → Measure (Wsp M 0), IsDxDq 1 fib →
    fib 1 {x | qf x = 1} = cM M

def QuotientMeasure : Prop :=
  ∀ (P Q : ℕ) (β : ℝ), (β = 1 ∨ β = -1) → ∀ x₀ : Wsp P Q, qf x₀ = β →
    (∀ y : Wsp P Q, qf y = β → ∃ g : UpqT P Q, act g⁻¹ x₀ = y) ∧
    (∃ (P' Q' : ℕ) (j : Wsp P' Q' →ₗ[ℂ] Wsp P Q) (ι : UpqT P' Q' → UpqT P Q),
      (β = 1 → P' + 1 = P ∧ Q' = Q) ∧ (β = -1 → P' = P ∧ Q' + 1 = Q) ∧ IsPerpFrame x₀ j ι) ∧
    ∀ (P' Q' : ℕ) (j : Wsp P' Q' →ₗ[ℂ] Wsp P Q) (ι : UpqT P' Q' → UpqT P Q),
      IsPerpFrame x₀ j ι →
        Set.range ι = {g | act g x₀ = x₀} ∧
        ∀ (c : CDHaar) (fib : ℝ → Measure (Wsp P Q)), IsDxDq β fib →
          ∀ s : Wsp P Q → UpqT P Q, (∀ y, qf y = β → act (s y)⁻¹ x₀ = y) →
            ∀ f : UpqT P Q → ℝ≥0∞, Measurable f →
              ∫⁻ g, f g ∂(c.cd P Q) =
                (cM (P + Q))⁻¹ *
                  ∫⁻ y in {y | qf y = β}, (∫⁻ g', f (ι g' * s y) ∂(c.cd P' Q')) ∂(fib β)

def RealPlaceMeasures : Prop := SelfDualMeasures ∧ SphereVolume ∧ QuotientMeasure

end GlobalTheory.IndefiniteRowSideFullHecke.ActionCoordinates
end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def UnramAt (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal.LiesOver v.asIdeal →
    w.asIdeal.ramificationIdx (𝓞 F) = 1

abbrev Ev (v : HeightOneSpectrum (𝓞 F)) : Type := Fv F v ⊗[F] E

def OEv (v : HeightOneSpectrum (𝓞 F)) : Subalgebra (v.adicCompletionIntegers F) (Ev F E v) :=
  integralClosure (v.adicCompletionIntegers F) (Ev F E v)

variable {F E} (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
  (v : HeightOneSpectrum (𝓞 F))

def act (g : HA (Fv F v) σ J) (x : Fin M → Ev F E v) : Fin M → Ev F E v :=
  ((HA.mat (Fv F v) σ J g : GL (Fin M) (Ev F E v)) : Matrix (Fin M) (Fin M) (Ev F E v)).mulVec x

def IsSDLatIn (P : Submodule (Ev F E v) (Fin M → Ev F E v))
    (L : Submodule (OEv F E v) (Fin M → Ev F E v)) : Prop :=
  L.FG ∧ Submodule.span (Ev F E v) (L : Set (Fin M → Ev F E v)) = P ∧
    ∀ y : Fin M → Ev F E v, y ∈ L ↔ (y ∈ P ∧ ∀ z ∈ L, hR (Fv F v) σ J z y ∈ OEv F E v)

def IsSDLat (L : Submodule (OEv F E v) (Fin M → Ev F E v)) : Prop := IsSDLatIn σ J v ⊤ L

def perp (x : Fin M → Ev F E v) : Submodule (Ev F E v) (Fin M → Ev F E v) where
  carrier := {y | hR (Fv F v) σ J x y = 0}
  zero_mem' := by simp [hR, Formalism.UG.hform]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, hR, Formalism.UG.hform] at *
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, ha, hb, add_zero]
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq, hR, Formalism.UG.hform] at *
    have : ∑ i, ∑ j, sigR (Fv F v) σ (x i) * JR (Fv F v) J i j * (c • a) j =
        c * ∑ i, ∑ j, sigR (Fv F v) σ (x i) * JR (Fv F v) J i j * a j := by
      simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [this, ha, mul_zero]

def perpLat (L : Submodule (OEv F E v) (Fin M → Ev F E v)) (x : Fin M → Ev F E v) :
    Submodule (OEv F E v) (Fin M → Ev F E v) :=
  (perp σ J v x).restrictScalars (OEv F E v) ⊓ L

def stabLat (L : Submodule (OEv F E v) (Fin M → Ev F E v)) : Subgroup (HA (Fv F v) σ J) :=
  (Formalism.UG.stabGL L).subgroupOf (HR (Fv F v) σ J)

def stabVec (x : Fin M → Ev F E v) : Subgroup (HA (Fv F v) σ J) :=
  MulAction.stabilizer (HA (Fv F v) σ J) (fun _ : Fin 1 => x)

def unitaryLatIn (P : Submodule (Ev F E v) (Fin M → Ev F E v))
    (L' : Submodule (OEv F E v) (Fin M → Ev F E v)) : Subgroup (P ≃ₗ[Ev F E v] P) where
  carrier := {u | (∀ y z : P, hR (Fv F v) σ J (u y) (u z) = hR (Fv F v) σ J y z) ∧
    ∀ y : P, (y : Fin M → Ev F E v) ∈ L' ↔ ((u y : P) : Fin M → Ev F E v) ∈ L'}
  one_mem' := ⟨fun _ _ => rfl, fun _ => Iff.rfl⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨fun y z => (ha (b y) (b z)).trans (hb y z), fun y => (hb' y).trans (ha' (b y))⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨fun y z => ?_, fun y => ?_⟩
    · have := ha (a.symm y) (a.symm z)
      rw [a.apply_symm_apply, a.apply_symm_apply] at this
      exact this.symm
    · have := ha' (a.symm y)
      rw [a.apply_symm_apply] at this
      exact this.symm

def Xb (β : Fv F v) : Set (Fin M → Ev F E v) := {x | x ≠ 0 ∧ qR (Fv F v) σ J x = β}

def SL (L : Submodule (OEv F E v) (Fin M → Ev F E v)) (β : Fv F v) : Set (Fin M → Ev F E v) :=
  {x | x ∈ L ∧ qR (Fv F v) σ J x = β}

def HasONB (L : Submodule (OEv F E v) (Fin M → Ev F E v)) : Prop :=
  ∃ b : Module.Basis (Fin M) (OEv F E v) L,
    ∀ i j, hR (Fv F v) σ J (b i) (b j) = if i = j then 1 else 0

def UnitVectors (L : Submodule (OEv F E v) (Fin M → Ev F E v)) (β : Fv F v) : Prop :=

  (SL σ J v L β).Nonempty ∧

  (∀ x ∈ SL σ J v L β,
    L = Submodule.span (OEv F E v) {x} ⊔ perpLat σ J v L x ∧
      IsSDLatIn σ J v (perp σ J v x) (perpLat σ J v L x)) ∧

  (∀ x ∈ SL σ J v L β, ∀ x' ∈ SL σ J v L β, ∃ g ∈ stabLat σ J v L, act σ J v g x = x') ∧

  (∀ x ∈ SL σ J v L β,
    stabLat σ J v L ⊓ stabVec σ J v x = stabLat σ J v (perpLat σ J v L x) ⊓ stabVec σ J v x ∧
    ∃ φ : (stabLat σ J v L ⊓ stabVec σ J v x : Subgroup (HA (Fv F v) σ J)) ≃*
        unitaryLatIn σ J v (perp σ J v x) (perpLat σ J v L x),
      ∀ g (y : perp σ J v x),
        (((φ g : perp σ J v x ≃ₗ[Ev F E v] perp σ J v x) y : perp σ J v x) : Fin M → Ev F E v) =
          act σ J v (g : HA (Fv F v) σ J) y) ∧

  (∀ x ∈ Xb σ J v β, ∀ x' ∈ Xb σ J v β, ∃ g : HA (Fv F v) σ J, act σ J v g x = x') ∧

  (∀ x ∈ Xb σ J v β, (∃ L₁, IsSDLat σ J v L₁ ∧ x ∈ L₁) ∧
    ∃ L', IsSDLatIn σ J v (perp σ J v x) L')

end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

def SelfDualLattices : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 1 ≤ M →
    ∀ v : HeightOneSpectrum (𝓞 F), UnramAt F E v →
    ∀ L : Submodule (OEv F E v) (Fin M → Ev F E v), IsSDLat σ J v L →
      HasONB σ J v L ∧
      (∀ L₁ : Submodule (OEv F E v) (Fin M → Ev F E v), IsSDLat σ J v L₁ →
        ∃ g : HA (Fv F v) σ J, ∀ y, y ∈ L ↔ act σ J v g y ∈ L₁) ∧
      ∀ β : (v.adicCompletionIntegers F)ˣ,
        UnitVectors σ J v L ((β : v.adicCompletionIntegers F) : Fv F v)

section Basic₂

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))

open scoped TensorProduct in
open NumberField IsDedekindDomain in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) in
private lemma involution_apply_eq_tensorProductMap_restrictScalars (a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.Ev F E v) :
    _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ a =
      ((Algebra.TensorProduct.map (AlgHom.id (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) σ).restrictScalars
        (v.adicCompletionIntegers F)) a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => unfold _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR; simp
  | add x y hx hy => simp [map_add (f := _), hx, hy]


open scoped TensorProduct in
open NumberField IsDedekindDomain in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.sigR_mem {a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.Ev F E v}
    (ha : a ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.OEv F E v) :
    _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ a ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.OEv F E v := by
  rw [involution_apply_eq_tensorProductMap_restrictScalars]
  exact IsIntegral.map _ ha

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal
end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

def IsUnimodularLC (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] : Prop :=
  IsTopologicalGroup G ∧ T2Space G ∧ LocallyCompactSpace G ∧ SecondCountableTopology G ∧
    BorelSpace G ∧ (∃ μ : Measure G, μ.IsHaarMeasure) ∧
    ∀ μ : Measure G, μ.IsHaarMeasure → μ.IsMulRightInvariant

def IsDiscreteWithDomains {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    (Γ : Subgroup G) : Prop :=
  Countable Γ ∧ DiscreteTopology Γ ∧
    ∀ μ : Measure G, μ.IsHaarMeasure →
      ∃ 𝓕 : Set G, MeasurableSet 𝓕 ∧ IsFundamentalDomain Γ 𝓕 μ

section Points

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def ratPts (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) : Subgroup (HA R σ J) := HFinIn R σ J

def UnimodularOver (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] (σ : E →ₐ[F] E)
    {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Prop :=
  IsUnimodularLC (HA R σ J) ∧
    ∀ x : Fin 1 → Fin M → E, hE σ J (x 0) (x 0) ≠ 0 → IsUnimodularLC (Hstab R σ J x)

end Points

def AdelicUnitaryHaar : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
      UnimodularOver (AF F) σ J ∧ UnimodularOver (Ainf F) σ J ∧ UnimodularOver (Af F) σ J ∧
      (∀ v : HeightOneSpectrum (𝓞 F), UnimodularOver (Fv F v) σ J) ∧
      IsDiscreteWithDomains (ratPts (AF F) σ J) ∧
      ∀ x : Fin 1 → Fin M → E, hE σ J (x 0) (x 0) ≠ 0 →
        IsDiscreteWithDomains (HstabFin (AF F) σ J x)

theorem isUnimodularLC_of_commGroup (G : Type) [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] : IsUnimodularLC G :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨Measure.haar, inferInstance⟩, fun _ _ => inferInstance⟩

end GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure
end
end
