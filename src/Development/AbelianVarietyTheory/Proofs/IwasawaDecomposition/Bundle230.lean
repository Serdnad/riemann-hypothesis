module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle014
public import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.Bundle001
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Divisors.ChartMeasApplyOfSubset
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle225
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle025
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle077
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle070
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle192
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle193
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockActionsIsHolomorphicProductKRepFamily
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle220
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle204
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle221
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle218
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar
open scoped Pointwise

namespace GlobalTheory.TrueGeo.SmallSec

variable {F : Type} [Field F] [NumberField F]

section Local

variable {Z : Scheme.{0}} [IsIntegral Z] {D : CartierDiv Z} {x : Z} {u g : Z.functionFieldˣ}
  {f : Z.functionField} {k τ : ℕ}

end Local

variable {C : CxSt F} {Y : Var F} (A : Adl C Y) {k τ : ℕ} {f : Y.Fn}

theorem isRatSec_pow {Z : Scheme.{0}} [IsIntegral Z] {L : LB Z} {r : L.ι → Z.functionFieldˣ}
    (hr : IsRatSec L r) (τ : ℕ) : IsRatSec (lbPow L τ) fun c => r (c PUnit.unit) ^ τ :=
  fun c c' h => by
  have l : (lbPow L τ).U c ⊓ (lbPow L τ).U c' ≤ L.U (c PUnit.unit) ⊓ L.U (c' PUnit.unit) :=
    fun _ hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  have e : (lbPow L τ).g c c' = res l (L.g (c PUnit.unit) (c' PUnit.unit)) ^ τ := by
    change ∏ _k : PUnit, _ = _
    refine (Fintype.prod_unique _).trans ((zpow_natCast _ _).trans ?_)
    rfl
  rw [e, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow,
    ← mul_pow, hr _ _ (l h)]
  exact congrArg (fun a => (a * _) ^ τ) (fnOf_resG l h _).symm


end GlobalTheory.TrueGeo.SmallSec
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.DefLift

theorem holShape_fixed : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_order → ∀ i, HolShape (R.MW i (sg0 D A)) ∧ ∃ w, WtIs (R.MW i (sg0 D A)) w := by
  intro D G _ _ Pl0 T A Ks _ _ _ R ho i
  have hs : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have hpq : ∀ τ, ((Wc D i).sig (tauE D τ)).1 + ((Wc D i).sig (tauE D τ)).2 = (Wc D i).rank :=
    fun τ => GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW_add_qW i τ
  have hc : ∀ ρ, Formalism.QuantumDeterminants.IsHCParam ((R.MW i (sg0 D A)).lam ρ) := fun ρ => by
    have he := (R.MW i (sg0 D A)).enum ρ
    refine ⟨he.1, fun a => ?_⟩
    obtain ⟨-, f, hf, hS⟩ := he
    have hp : Links.parAt (Wc D i) (sg0 D A) ρ = Formalism.L2.NTheta.holPar _ _ (Formalism.L2.NTheta.wtOf D (Wc D i) ρ) := by
      rw [hs]; exact GlobalTheory.ThetaFiresProbe.parAt_fixed _ ρ
    rw [hp] at hS
    have hm : (f a, (R.MW i (sg0 D A)).ε ρ a) ∈ Formalism.L2.NTheta.holPar _ _ (Formalism.L2.NTheta.wtOf D (Wc D i) ρ) := by
      rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    obtain ⟨x, -, hx⟩ := Finset.mem_image.1 hm
    have hx1 := congrArg Prod.fst hx
    have hn : (((Wc D i).rank : ℕ) : ℝ) = (((Wc D i).sig (tauE D ρ)).1 : ℝ) + ((Wc D i).sig (tauE D ρ)).2 := by
      rw [← hpq ρ]; push_cast; rfl
    dsimp only at hx1
    rw [hf a, ← hx1, hn]
    rcases x with c | c
    · refine ⟨Formalism.L2.NTheta.wtOf D (Wc D i) ρ (Sum.inl c) - ((Wc D i).sig (tauE D ρ)).2 - (c : ℕ), ?_⟩
      simp only [Formalism.L2.NTheta.holEnt, Sum.elim_inl]
      push_cast
      ring
    · refine ⟨Formalism.L2.NTheta.wtOf D (Wc D i) ρ (Sum.inr c) - (c : ℕ), ?_⟩
      simp only [Formalism.L2.NTheta.holEnt, Sum.elim_inr]
      push_cast
      ring
  refine ⟨fun ρ => ⟨hc ρ, _, (Nat.le_add_right _ _).trans (hpq ρ).le, fun a => ho i ρ a⟩, ?_⟩
  choose w hw using fun ρ a => Formalism.QuantumDeterminants.low_k_integrable_holds _ ((R.MW i (sg0 D A)).ε ρ) _ (hc ρ).2 a
  exact ⟨fun ρ c => w ρ (revNeg ((R.MW i (sg0 D A)).ε ρ) (arr (nNeg ((R.MW i (sg0 D A)).ε ρ)) c)),
    fun ρ c => (hw ρ _).symm⟩

end GlobalTheory.DefLift
end

section

open MeasureTheory GlobalTheory.ChartGlue
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChartGlue

theorem glueMeas_add_of_compat_on : ∀ {Y : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y] {n : ℕ} {κ : Type} (e : κ → OpenPartialHomeomorph Y (V n)),
    (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) →
    (∀ y, ∃ i, y ∈ (e i).source) → ∀ {S : Set Y}, MeasurableSet S → ∀ (ρ ρ' : κ → Y → ℝ≥0∞),
    (∀ i j y, y ∈ S → y ∈ (e i).source → y ∈ (e j).source →
      ρ i y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ρ j y) →
    (∀ i j y, y ∈ S → y ∈ (e i).source → y ∈ (e j).source →
      ρ' i y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ρ' j y) →
    (∀ i, AEMeasurable (fun v => ρ i ((e i).symm v)) (volume.restrict ((e i).target ∩ (e i).symm ⁻¹' S))) →
    glueMeas e (fun i y => ρ i y + ρ' i y) S = glueMeas e ρ S + glueMeas e ρ' S := by
  intro Y _ _ _ _ n κ e hd hcov S hS ρ ρ' hρ hρ' hAE

  have same : ∀ (τ τ' : κ → Y → ℝ≥0∞), (∀ i y, y ∈ S → τ i y = τ' i y) →
      glueMeas e τ S = glueMeas e τ' S := by
    intro τ τ' h
    have hm := GlobalTheory.ChernScale.glueMeas_restrict_eq e (ρ := τ) (ρ' := τ') (c := 1) ENNReal.one_ne_top hS
      (fun i y _ hy => by rw [one_mul]; exact h i y hy)
    have := congrArg (fun μ : Measure Y => μ S) hm
    simpa only [Measure.smul_apply, smul_eq_mul, one_mul, Measure.restrict_apply_self] using this

  have compat : ∀ (τ : κ → Y → ℝ≥0∞), (∀ i j y, y ∈ S → y ∈ (e i).source → y ∈ (e j).source →
      τ i y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * τ j y) →
      ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      S.indicator (τ i) y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * S.indicator (τ j) y := by
    intro τ hτ i j y hi hj
    by_cases hy : y ∈ S
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]; exact hτ i j y hy hi hj
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]
  have cσ := compat ρ hρ
  have cσ' := compat ρ' hρ'
  have cs : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      S.indicator (ρ i) y + S.indicator (ρ' i) y =
        ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * (S.indicator (ρ j) y + S.indicator (ρ' j) y) := by
    intro i j y hi hj
    rw [mul_add, cσ i j y hi hj, cσ' i j y hi hj]

  have aem : ∀ i (A : Set Y), MeasurableSet A → A ⊆ (e i).source →
      AEMeasurable (fun v => S.indicator (ρ i) ((e i).symm v)) (volume.restrict ((e i) '' A)) := by
    intro i A hAm hA
    have hT : MeasurableSet ((e i).target ∩ (e i).symm ⁻¹' S) := by
      rw [← (e i).image_source_inter_eq']
      exact measurableSet_image (e i) ((e i).open_source.measurableSet.inter hS) Set.inter_subset_left
    have hg := ((aemeasurable_indicator_iff hT).2 (hAE i)).mono_measure
      (Measure.restrict_le_self (s := (e i) '' A))
    refine hg.congr ((ae_restrict_iff' (measurableSet_image (e i) hAm hA)).2
      (Filter.Eventually.of_forall ?_))
    rintro _ ⟨y, hy, rfl⟩
    have ht : (e i) y ∈ (e i).target := (e i).map_source (hA hy)
    show _ = S.indicator (ρ i) ((e i).symm ((e i) y))
    by_cases hs : (e i).symm ((e i) y) ∈ S
    · rw [Set.indicator_of_mem (show (e i) y ∈ (e i).target ∩ (e i).symm ⁻¹' S from ⟨ht, hs⟩),
        Set.indicator_of_mem hs]
    · rw [Set.indicator_of_notMem (show (e i) y ∉ (e i).target ∩ (e i).symm ⁻¹' S from fun h => hs h.2),
        Set.indicator_of_notMem hs]
  have key : glueMeas e (fun i y => S.indicator (ρ i) y + S.indicator (ρ' i) y) =
      glueMeas e (fun i => S.indicator (ρ i)) + glueMeas e (fun i => S.indicator (ρ' i)) := by
    refine ext_of_cover (fun i => (e i).source) (fun i => (e i).open_source) hcov fun i A hA hAi => ?_
    rw [Measure.add_apply, glueMeas_apply e _ hd cs i hA hAi,
      glueMeas_apply e (fun i => S.indicator (ρ i)) hd cσ i hA hAi,
      glueMeas_apply e (fun i => S.indicator (ρ' i)) hd cσ' i hA hAi,
      chartMeas_apply_of_subset _ _ hA hAi, chartMeas_apply_of_subset _ _ hA hAi,
      chartMeas_apply_of_subset _ _ hA hAi]
    exact lintegral_add_left' (aem i A hA hAi) _
  rw [same (fun i y => ρ i y + ρ' i y) (fun i y => S.indicator (ρ i) y + S.indicator (ρ' i) y)
      (fun i y hy => by simp only [Set.indicator_of_mem hy]),
    same ρ (fun i => S.indicator (ρ i)) (fun i y hy => by simp only [Set.indicator_of_mem hy]),
    same ρ' (fun i => S.indicator (ρ' i)) (fun i y hy => by simp only [Set.indicator_of_mem hy]),
    key, Measure.add_apply]

end GlobalTheory.ChartGlue
end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.Datum
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdjMove

section Ring

variable {A R k : Type} [CommRing A] [CommRing R] [CommRing k] {m n : ℕ}

def adj (φ : A →+* R) (C : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin n) (Fin n) R) (Z : Fin m → Fin n → A) :
    Matrix (Fin m) (Fin n) R := C * (Matrix.of Z).map φ * B

theorem adj_move (φ : A →+* R) (C : Matrix (Fin m) (Fin m) R) (B Y : Matrix (Fin n) (Fin n) R)
    (u : Matrix (Fin n) (Fin n) A) (h : (u.map φ)ᵀ * B * Y = B) (M : ℕ) (Z Z' w : Fin m → Fin n → A)
    (hZ : ∀ b, u *ᵥ Z' b = Z b + M • w b) : adj φ C B Z' = (adj φ C B Z + M • adj φ C B w) * Y := by
  have e : (Matrix.of Z).map φ + M • (Matrix.of w).map φ = (Matrix.of Z').map φ * (u.map φ)ᵀ := by
    ext b a
    have := congrArg φ (congrFun (hZ b) a)

    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.add_apply, Pi.smul_apply, map_add (f := _), map_nsmul] at this
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply,
      Matrix.transpose_apply, ← this, mul_comm]
  unfold adj
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.add_mul, ← Matrix.mul_add, e]
  conv_lhs => rw [← h]
  simp only [Matrix.mul_assoc]

theorem adj_apply (φ : A →+* R) (C : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin n) (Fin n) R) (Z : Fin m → Fin n → A)
    (b' : Fin m) (a : Fin n) : adj φ C B Z b' a = ∑ b, C b' b * ∑ j, φ (Z b j) * B j a := by
  unfold adj
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply]

theorem red_eq (S : Subring R) (ρ : S →+* k) (M : ℕ) (hM : (M : k) = 0) (X X' W : Matrix (Fin m) (Fin n) R)
    (y : Matrix (Fin n) (Fin n) S) (hX : ∀ i j, X i j ∈ S) (hX' : ∀ i j, X' i j ∈ S) (hW : ∀ i j, W i j ∈ S)
    (h : X' = (X + M • W) * y.map S.subtype) (i : Fin m) (j : Fin n) :
    ρ ⟨X' i j, hX' i j⟩ = ∑ a, ρ ⟨X i a, hX i a⟩ * ρ (y a j) := by
  have e : (⟨X' i j, hX' i j⟩ : S) = ∑ a, (⟨X i a, hX i a⟩ + M • ⟨W i a, hW i a⟩) * y a j := by
    apply Subtype.ext
    simp [h, Matrix.mul_apply]

  rw [e, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, map_add (f := _), map_nsmul, nsmul_eq_mul, hM, zero_mul, add_zero]

def lft (c : R) (P Q : Matrix (Fin m) (Fin m) R) : Matrix (Fin m) (Fin m) R := c • (P * Q)

theorem entry_eq {E : Type} [CommRing E] (f : E →+* R) (φ : A →+* R) (c : R) (P : Matrix (Fin m) (Fin m) R)
    (Q : Matrix (Fin m) (Fin m) E) (X : Matrix (Fin m) (Fin n) E) (G : Matrix (Fin n) (Fin n) E)
    (β : Matrix (Fin n) (Fin n) R) (Z : Fin m → Fin n → A) (h : ∀ b a, f (X b a) = φ (Z b a)) :
    (fun b a => c * (P * (Q * X * G).map f * β) b a) = adj φ (lft c P (Q.map f)) (G.map f * β) Z := by
  have e1 : X.map f = (Matrix.of Z).map φ := Matrix.ext h
  unfold adj lft
  rw [Matrix.smul_mul, Matrix.smul_mul, ← e1, Matrix.map_mul, Matrix.map_mul]
  ext b a
  simp only [Matrix.mul_assoc, Matrix.smul_apply, smul_eq_mul]

theorem unit_rel_ring (S : Subring R) (σ : A →+* A) (s : A →+* R) (J : Matrix (Fin n) (Fin n) A) (u : GL (Fin n) A)
    (β : GL (Fin n) R) (y : GL (Fin n) S) (hu : u ∈ Formalism.UG.UJ σ J)
    (hy : β * Formalism.UG.bc S.subtype y * β⁻¹ = Formalism.UG.bc s u) :
    (u.1.map (s.comp σ))ᵀ * (J.map s * β.1) * y.1.map S.subtype = J.map s * β.1 := by
  have h1 : β * Formalism.UG.bc S.subtype y = Formalism.UG.bc s u * β := by rw [← hy, inv_mul_cancel_right]
  have h2 : β.1 * y.1.map S.subtype = u.1.map s * β.1 := congrArg Units.val h1
  have h4 : (u.1.map σ)ᵀ * J * u.1 = J := hu
  have h5 := congrArg (fun N => Matrix.map N s) h4
  simp only [Matrix.map_mul] at h5
  have h6 : (u.1.map (s.comp σ))ᵀ * J.map s * u.1.map s = J.map s := h5
  rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h6]

theorem adj_int_ring (S : Subring R) (φ : A →+* R) (C : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin n) (Fin n) R)
    (s : Set (Fin n → A)) (La : Type) [Zero La] (v : La → Fin n → A) (v0 : ∀ j, v 0 j = 0)
    (h : ∀ x : Fin m → La, ∀ i j, adj φ C B (fun b => v (x b)) i j ∈ S)
    (hs : ∀ z ∈ s, ∃ t ∈ S, ∃ l, ∀ j, φ (z j) = t * φ (v l j))
    (w : Fin m → Fin n → A) (hw : ∀ b, w b ∈ AddSubgroup.closure s) (b' : Fin m) (a : Fin n) : adj φ C B w b' a ∈ S := by
  rw [adj_apply]
  refine sum_mem fun b _ => ?_
  have key : ∀ z ∈ AddSubgroup.closure s, C b' b * ∑ j, φ (z j) * B j a ∈ S := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨t, ht, l, hl⟩ := hs z hz
      have h1 := h (Pi.single b l) b' a
      rw [adj_apply, Finset.sum_eq_single b] at h1
      · have h2 := mul_mem ht h1
        rw [Pi.single_eq_same, mul_left_comm, Finset.mul_sum] at h2
        simpa only [hl, mul_assoc] using h2
      · intro c _ hc
        rw [Pi.single_eq_of_ne hc]
        simp [v0]
      · simp
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib, mul_add]
      exact add_mem hx hy
    | neg x _ hx =>
      simp only [Pi.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib, mul_neg]
      exact neg_mem hx
  exact key _ (hw b)

end Ring

variable {D : D7}

noncomputable def barSwap (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →+* EAf D :=
  (Lev.swapAE D).comp (sigR (Af D.host.F) D.sp.cm.sig)

theorem barSwap_tmul (a : Af D.host.F) (x : D.host.E) :
    barSwap D (a ⊗ₜ[D.host.F] x) = ((1 : D.host.E) ⊗ₜ[D.host.F] a) * barSwap D ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) := by
  change D.sp.cm.sig x ⊗ₜ[D.host.F] a = ((1 : D.host.E) ⊗ₜ[D.host.F] a) * (D.sp.cm.sig x ⊗ₜ[D.host.F] 1)
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

theorem uMat_eq (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D)
    (X : Fin S.rank → Fin T.rank → D.host.E) :
    uMat S T βS βT e X = adj (barSwap D) (lft (toEAf D e) (βS⁻¹).1 (S.gram⁻¹.map (eToEAf D)))
      (T.gram.map (eToEAf D) * βT.1) fun b => finVec T (X b) :=
  entry_eq (eToEAf D) (barSwap D) _ _ _ _ _ _ _ fun _ _ => rfl

theorem unit_rel (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (u : GA D T)
    (y : GL (Fin T.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)) (hy : frGL βT y = Lev.finE T u) :
    ((finHom T u).1.map (barSwap D))ᵀ * (T.gram.map (eToEAf D) * βT.1) * y.1.map (Subring.subtype _) =
      T.gram.map (eToEAf D) * βT.1 :=
  unit_rel_ring _ (sigR (Af D.host.F) D.sp.cm.sig) (Lev.swapAE D) (JR (Af D.host.F) T.gram) (finHom T u) βT y
    (GlobalTheory.UnitarySplit.finHom_mem T u) hy

theorem adj_int {m : ℕ} (T : HSp D) (C : Matrix (Fin m) (Fin m) (EAf D)) (B : Matrix (Fin T.rank) (Fin T.rank) (EAf D))
    (La : Type) [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin T.rank → D.host.E))
    (h : ∀ x : Fin m → La, IsIntM (adj (barSwap D) C B fun b => finVec T (ι (x b))))
    (w : Fin m → Fin T.rank → Af D.host.F ⊗[D.host.F] D.host.E)
    (hw : ∀ b, w b ∈ GlobalTheory.AdLat.hat D.host.F (Set.range ι)) : IsIntM (adj (barSwap D) C B w) := by
  refine adj_int_ring _ (barSwap D) C B _ La (fun l => finVec T (ι l)) (fun j => ?_) h ?_ w hw
  · show (1 : Af D.host.F) ⊗ₜ[D.host.F] (ι 0 j) = 0
    rw [LinearMap.map_zero]
    exact TensorProduct.tmul_zero _ _
  · rintro z ⟨α, hα, _, ⟨l, rfl⟩, rfl⟩
    exact ⟨(1 : D.host.E) ⊗ₜ[D.host.F] α, Subring.subset_closure (Or.inr ⟨⟨α, hα⟩, rfl⟩), l,
      fun j => barSwap_tmul α (ι l j)⟩



theorem redM_uMat_move : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D) (La : Type) [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin T.rank → D.host.E)), (∀ x : Fin S.rank → La, IsIntM (uMat S T βS βT e fun b => ι (x b))) → ∀ (u : GA D T) (y : GL (Fin T.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)), frGL βT y = Lev.finE T u → ∀ (M : ℕ) (PP : Pl D.host.E), (M : 𝓞 D.host.E) ∈ PP.asIdeal → ∀ x x' : Fin S.rank → La, (∀ b, ∃ w ∈ GlobalTheory.AdLat.hat D.host.F (Set.range ι), (finHom T u).1.mulVec (finVec T (ι (x' b))) = finVec T (ι (x b)) + M • w) → redM PP (uMat S T βS βT e fun b => ι (x' b)) = redM PP (uMat S T βS βT e fun b => ι (x b)) * y.1.map (resS D.host.F PP) := by
  intro D S T βS βT e La _ _ ι hint u y hy M PP hM x x' hx
  choose w hw hx using hx
  have hW := adj_int T _ _ La ι (fun x => by rw [← uMat_eq S T βS βT e]; exact hint x) w hw
  have hmv := adj_move (barSwap D) (lft (toEAf D e) (βS⁻¹).1 (S.gram⁻¹.map (eToEAf D))) _ _ _ (unit_rel T βT u y hy) M
    (fun b => finVec T (ι (x b))) (fun b => finVec T (ι (x' b))) w hx
  rw [← uMat_eq S T βS βT e, ← uMat_eq S T βS βT e] at hmv
  have hM' : (M : kP PP) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hM
  ext i j
  have := red_eq _ (resS D.host.F PP) M hM' _ _ _ y.1 (hint x) (hint x') hW hmv i j
  rw [Matrix.mul_apply]
  unfold redM
  rw [dite_eq_left (hint x' i j), this]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [dite_eq_left (hint x i a)]
  rfl

end GlobalTheory.AdjMove
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.weilPairing_expModelFiber_eq_alternatingForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (σ₀ : KA l →+* ℂ) (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X) (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p), IsPeriod (Fu.Di i) ty P → ∀ (k : ℕ) (a b : (Fu.Di i).La) (ζ : ℂˣ), 0 < k → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((Fu.Di i).EF a b : ℂ) / k) → GlobalTheory.UU.CubWeil Z.t.cub k (pushEx Z Fu y i P p hu hp ((k : ℂ)⁻¹ • P a)) (pushEx Z Fu y i P p hu hp ((k : ℂ)⁻¹ • P b)) (unitOn ζ) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.pushEx_cubWeil | exact GlobalTheory.ShFam.Hor.LogCh.pushEx_cubWeil | (intros; apply GlobalTheory.ShFam.Hor.LogCh.pushEx_cubWeil <;> assumption)
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.GrassTop

theorem ren_rel {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (τ : GlobalTheory.AllWt.Psi H) (k : ℕ) :
    ren τ (rel k) = GlobalTheory.PointChern.relPoly τ k := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [ren, rel, GlobalTheory.PointChern.relPoly, map_sum, renVar]

theorem admissibleChernForm_kills_grassmannianRelationCopies : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ), GlobalTheory.Schubert.admitted H Dw Θ →
    ∀ (τ : GlobalTheory.AllWt.Psi H) (j : MvPolynomial (Bool × ℕ) ℝ), j ∈ GlobalTheory.GrassTop.J Dw.p Dw.q →
    ∀ r : MvPolynomial ((E →+* ℂ) × ℕ) ℝ, Θ (r * GlobalTheory.GrassTop.ren τ j) = 0 := by
  intro E _ _ _ H Dw Θ hA τ j hj
  obtain ⟨h1, h2, h3, -⟩ := hA
  unfold J at hj
  induction hj using Submodule.span_induction with
  | mem x hx =>
    intro r
    rcases hx with ⟨k, hk, rfl⟩ | ⟨b, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
    · rw [ren_rel, mul_comm]; exact h1 τ k hk r
    · rw [mul_comm]
      simp only [ren, map_sub, rename_X, map_one]
      exact h2 _ r
    · rw [mul_comm]
      simp only [ren, rename_X]
      have hm : Dw.mult τ.1 = Dw.p := GlobalTheory.PointChern.mult_of_mem Dw τ.2
      exact h3 _ _ (by simp only [renVar, if_true]; omega) r
    · rw [mul_comm]
      simp only [ren, rename_X]
      have hm : Dw.mult (conjEmb τ.1) = Dw.q := GlobalTheory.PointChern.mult_of_not_mem Dw (GlobalTheory.AllWt.conj_not_mem τ)
      exact h3 _ _ (by simp only [renVar]; simp only [Bool.false_eq_true, if_false]; omega) r
  | zero => intro r; simp
  | add x y _ _ hx hy => intro r; rw [map_add (f := _), mul_add, map_add (f := _), hx, hy, add_zero]
  | smul a x _ hx => intro r; rw [smul_eq_mul, map_mul (ren τ) a x, ← mul_assoc]; exact hx _

end GlobalTheory.GrassTop
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_operator_lowestWeight_holomorphic_KType : ∀ (n : ℕ) (ε : Fin n → Bool) (abelian₂ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H), IsURepOn (Formalism.REAL.Kset ε) σ → IsKTypeOf ε σ abelian₂ S → ∀ (P : Type) [AddCommGroup P] [Module ℂ P] (B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ) (π : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P), IsHolRep ε B π → ∃ (w : S) (T : S →ₗ[ℂ] Module.End ℂ P), w ≠ 0 ∧ (∀ s, T s ∈ Submodule.span ℂ (π '' Formalism.REAL.Kset ε)) ∧ ∀ y, IsBottom ε π (-abelian₂) y → T w y = y ∧ ∀ k ∈ Formalism.REAL.Kset ε, ∀ s s' : S, (s' : H) = σ k s → T s' y = π (k.map star) (T s y) := by
  first | exact @GlobalTheory.JointHarm.KTypeOp.exists_op | exact GlobalTheory.JointHarm.KTypeOp.exists_op | (intros; apply GlobalTheory.JointHarm.KTypeOp.exists_op <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fockActions_isHolomorphicProductKRepFamily : ∀ (D : D7) (m n : ℕ) (ε : D.what₂.Tau → Fin m → Bool) (x₁ x₂ x₃ : D.what₂.Tau → ℤ), IsHolFam ε fockL (factK n ε x₁ x₂ x₃) ∧ IsHolFam (fun _ => allPos n) fockL (factU (n := n) ε x₁ x₂ x₃) := by
  first | exact @GlobalTheory.FockHol.main | exact GlobalTheory.FockHol.main | (intros; apply GlobalTheory.FockHol.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lowestKType_coefficientWeight_eq_minorWeights : ∀ (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), σ = D.what₂.embLL → ∀ M : DSModel (Wc D i) (parAt (Wc D i) σ), (∀ τ a, M.ε τ a = decide ((a : ℕ) < ((Wc D i).sig (tauE D τ)).1)) → ∃ x₁ x₂ x₃ : D.what₂.Tau → ℤ, ∀ τ, (x₁ τ : ℚ) = -(D.hc τ).e i + ((Vc D i).rank : ℚ) / 2 ∧ (x₂ τ : ℚ) = -(D.hc τ).e i - ((Vc D i).rank : ℚ) / 2 ∧ (x₃ τ : ℚ) = -(((((Wc D i).sig (tauE D τ)).1 : ℚ) - ((Wc D i).sig (tauE D τ)).2) / 2 + (-(D.hc τ).e i - 1 / 2)) ∧ (∀ a, Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ) a = (wtK ((Wc D i).sig (tauE D τ)).1 (aPl D i ((Wc D i).sig (tauE D τ)).1 τ) (aMi D i ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 τ) (x₁ τ) (x₂ τ) a : ℝ)) ∧ ∀ j : Fin (Vc D i).rank, wtU ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 (aPl D i ((Wc D i).sig (tauE D τ)).1 τ) (aMi D i ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 τ) (x₃ τ) j = -(Bridge.lamLdef (D := D) (Vc D i).rank ((i : ℕ) + 1) τ).w j := by
  first | exact @GlobalTheory.JointHarm.weights_of_minors | exact GlobalTheory.JointHarm.weights_of_minors | (intros; apply GlobalTheory.JointHarm.weights_of_minors <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.columnHighest_rowIntertwiners_proportional : ∀ (ι : Type) [Fintype ι] (m n : ℕ), n ≤ m → ∀ (X : Type) [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X] (π : ι → Matrix.unitaryGroup (Fin m) ℂ → Module.End ℂ X), IrrFam π → ∀ (Φ Ψ : X →ₗ[ℂ] Pol ι m n) (μ μ' : ι → Fin n → ℤ), Φ ≠ 0 → (∀ τ u x, Φ (π τ u x) = rowSub n τ u (Φ x) ∧ Ψ (π τ u x) = rowSub n τ u (Ψ x)) → (∀ τ k l, k < l → colLie m τ k l ∘ₗ Φ = 0 ∧ colLie m τ k l ∘ₗ Ψ = 0) → (∀ τ k, colLie m τ k k ∘ₗ Φ = (μ τ k : ℂ) • Φ ∧ colLie m τ k k ∘ₗ Ψ = (μ' τ k : ℂ) • Ψ) → ∃ r : ℂ, Ψ = r • Φ := by
  first | exact @GlobalTheory.DefLift.colHighest_intertwiner_proportional | exact GlobalTheory.DefLift.colHighest_intertwiner_proportional | (intros; apply GlobalTheory.DefLift.colHighest_intertwiner_proportional <;> assumption)
end
