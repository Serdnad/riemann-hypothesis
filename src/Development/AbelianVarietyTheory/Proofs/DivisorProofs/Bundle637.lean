module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle545
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle590
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.SemidirectProduct
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle591
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle592
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Mathlib.FieldTheory.KrullTopology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisDescentFreeSheafCechLevelSepClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle506
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle609
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Lemma
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle589
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003

@[expose] public section

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem iterD_eventuallyEq (I : Type) [Fintype I] [DecidableEq I] (u : List I)
    (f g : (I → ℂ) → ℂ) (z : I → ℂ) (h : f =ᶠ[nhds z] g) :
    iterD u f =ᶠ[nhds z] iterD u g := by
  induction u with
  | nil => exact h
  | cons i u ih =>
    have h2 := ih.eventuallyEq_nhds
    filter_upwards [h2] with w hw
    exact Filter.EventuallyEq.lineDeriv_eq hw

theorem iterD_eq_of_eventuallyEq : ∀ (I : Type) [Fintype I] [DecidableEq I] (u : List I)
    (f g : (I → ℂ) → ℂ) (z : I → ℂ), f =ᶠ[nhds z] g → iterD u f z = iterD u g z :=
  fun I _ _ u f g z h => (iterD_eventuallyEq I u f g z h).eq_of_nhds

end GlobalTheory.HilbFam
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

open Set Filter Topology in
open NumberField IsDedekindDomain in
open scoped ContDiff nonZeroDivisors in
private lemma partialD_eqOn_fderiv_single {I : Type} [Fintype I] [DecidableEq I] {U : Set (I → ℂ)}
    {h : (I → ℂ) → ℂ} (hU : IsOpen U) (hh : DifferentiableOn ℂ h U) (i : I) :
    EqOn (_root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.partialD i h) (fun z ↦ fderiv ℂ h z (Pi.single i 1)) U := by
  intro z hz
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.partialD
  exact (hh.differentiableAt (hU.mem_nhds hz)).lineDeriv_eq_fderiv

open Set Filter Topology in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma iterD_eqOn_iteratedFDeriv_single {I : Type} [Fintype I] [DecidableEq I]
    {U : Set (I → ℂ)} {h : (I → ℂ) → ℂ} (hU : IsOpen U) (hh : DifferentiableOn ℂ h U) :
    ∀ l : List I, EqOn (_root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD l h)
      (fun z ↦ iteratedFDeriv ℂ l.length h z (fun k ↦ Pi.single (l.get k) 1)) U
  | [] => by
    intro z _
    simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD]
  | i :: l => by
    intro z hz
    have ih := iterD_eqOn_iteratedFDeriv_single hU hh l
    have hG : DifferentiableOn ℂ
        (fun z ↦ iteratedFDeriv ℂ l.length h z (fun k ↦ Pi.single (l.get k) 1)) U :=
      (_root_.GlobalTheory.SCV.differentiableOn_iteratedFDeriv hU hh l.length).continuousMultilinear_apply_const _
    have hd : DifferentiableOn ℂ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD l h) U := hG.congr ih
    have hstep : _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD (i :: l) h z =
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.partialD i (_root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD l h) z := by
      simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD]
    have hev : _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD l h =ᶠ[𝓝 z]
        fun z ↦ iteratedFDeriv ℂ l.length h z (fun k ↦ Pi.single (l.get k) 1) :=
      Filter.eventuallyEq_of_mem (hU.mem_nhds hz) ih
    rw [hstep, partialD_eqOn_fderiv_single hU hd i hz]
    simp only
    rw [hev.fderiv_eq, fderiv_continuousMultilinear_apply_const_apply
      ((_root_.GlobalTheory.SCV.differentiableOn_iteratedFDeriv hU hh l.length).differentiableAt (hU.mem_nhds hz))]
    exact (iteratedFDeriv_succ_apply_left (f := h) (x := z) (n := l.length)
      (fun k ↦ Pi.single ((i :: l).get k) 1)).symm


open Set Filter Topology in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
theorem _root_.GlobalTheory.HilbFam.hasSum_iterD_termwise : ∀ (I : Type) [Fintype I] [DecidableEq I] (Ξ : Type) (u : List I) (r : ℝ)
    (f : Ξ → (I → ℂ) → ℂ) (g : (I → ℂ) → ℂ) (M : Ξ → ℝ), 0 < r → Summable M →
    (∀ ξ, DifferentiableOn ℂ (f ξ) (Metric.ball 0 r)) →
    (∀ ξ, ∀ z ∈ Metric.ball (0 : I → ℂ) r, ‖f ξ z‖ ≤ M ξ) →
    (∀ z ∈ Metric.ball (0 : I → ℂ) r, HasSum (fun ξ ↦ f ξ z) (g z)) →
    HasSum (fun ξ ↦ _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u (f ξ) 0) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u g 0) := by
  intro I _ _ Ξ u r f g M hr hM hf hbound hsum
  have hU : IsOpen (Metric.ball (0 : I → ℂ) r) := Metric.isOpen_ball
  have h0 : (0 : I → ℂ) ∈ Metric.ball (0 : I → ℂ) r := Metric.mem_ball_self hr
  have hloc : ∀ x ∈ Metric.ball (0 : I → ℂ) r, ∃ t ∈ 𝓝 x, ∃ v : Ξ → ℝ, Summable v ∧
      ∀ ξ, ∀ z ∈ t, ‖f ξ z‖ ≤ v ξ :=
    fun x hx ↦ ⟨_, hU.mem_nhds hx, M, hM, hbound⟩
  have hg_eq : EqOn g (fun w ↦ ∑' ξ, f ξ w) (Metric.ball 0 r) :=
    fun z hz ↦ (hsum z hz).tsum_eq.symm
  have hg : DifferentiableOn ℂ g (Metric.ball 0 r) :=
    (_root_.GlobalTheory.SCV.differentiableOn_tsum_of_locally_normal hU hf hloc).congr hg_eq
  have hev : g =ᶠ[𝓝 0] fun w ↦ ∑' ξ, f ξ w := Filter.eventuallyEq_of_mem (hU.mem_nhds h0) hg_eq
  have hS := _root_.GlobalTheory.SCV.hasSum_iteratedFDeriv_of_locally_normal hU hf hloc u.length h0
  rw [← (hev.iteratedFDeriv ℂ u.length).eq_of_nhds] at hS
  rw [iterD_eqOn_iteratedFDeriv_single hU hg u h0]
  simp only [iterD_eqOn_iteratedFDeriv_single hU (hf _) u h0]
  exact ContinuousMultilinearMap.hasSum_eval hS _

end GlobalTheory.HilbFam
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum

namespace GlobalTheory.HomothetyLatSum

variable {E : Type} [Field E] [NumberField E]

def mulQ (α : E) : Quotient (unitRel (E := E)) → Quotient (unitRel (E := E)) :=
  Quotient.map (fun x => α * x) (by rintro x x' ⟨u, h⟩; exact ⟨u, by rw [h]; ring⟩)

theorem mulQ_mk (α x : E) : mulQ α (Quotient.mk _ x) = Quotient.mk (unitRel (E := E)) (α * x) := rfl

theorem mulQ_mulQ (a b : E) (q : Quotient (unitRel (E := E))) : mulQ a (mulQ b q) = mulQ (a * b) q := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  rw [mulQ_mk, mulQ_mk, mulQ_mk, mul_assoc]

theorem mulQ_one (q : Quotient (unitRel (E := E))) : mulQ 1 q = q := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  rw [mulQ_mk, one_mul]

theorem mulQ_mem {α : E} (hα : α ≠ 0) {L : Set E} {q : Quotient (unitRel (E := E))} (hq : q ∈ modUnits L) :
    mulQ α q ∈ modUnits ((fun x => α * x) '' L) := by
  obtain ⟨x, hx, h0, rfl⟩ := hq
  exact ⟨α * x, ⟨x, hx, rfl⟩, mul_ne_zero hα h0, rfl⟩

theorem mulQ_inv_mem {α : E} (hα : α ≠ 0) {L : Set E} {q : Quotient (unitRel (E := E))}
    (hq : q ∈ modUnits ((fun x => α * x) '' L)) : mulQ α⁻¹ q ∈ modUnits L := by
  obtain ⟨_, ⟨x, hx, rfl⟩, h0, rfl⟩ := hq
  refine ⟨x, hx, fun h => h0 (by simp [h]), ?_⟩
  rw [mulQ_mk, inv_mul_cancel_left₀ hα]

def mulEquiv {α : E} (hα : α ≠ 0) (L : Set E) : modUnits L ≃ modUnits ((fun x => α * x) '' L) where
  toFun q := ⟨mulQ α q.1, mulQ_mem hα q.2⟩
  invFun q := ⟨mulQ α⁻¹ q.1, mulQ_inv_mem hα q.2⟩
  left_inv q := Subtype.ext (by simp only; rw [mulQ_mulQ, inv_mul_cancel₀ hα, mulQ_one])
  right_inv q := Subtype.ext (by simp only; rw [mulQ_mulQ, mul_inv_cancel₀ hα, mulQ_one])

variable {I : Type} [Fintype I]

theorem term_out_mulQ [IsCMField E] {φ : I → E →+* ℂ} (hφ : IsCMType φ) (s : ℕ) (κ : I → ℕ) (σ : ℂ) (α : E)
    (q : Quotient (unitRel (E := E))) :
    term φ (2 * s) κ σ (mulQ α q).out = term φ (2 * s) κ σ α * term φ (2 * s) κ σ q.out := by
  have h1 : mulQ α q = Quotient.mk _ (α * q.out) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  obtain ⟨u, hu⟩ := Quotient.exact ((Quotient.out_eq _).trans h1)
  rw [← term_mul, hu, (TermUnit.term_unit_and_norm E I φ hφ s κ σ _).1 u]

theorem term_eq_lamInf [IsCMField E] {φ : I → E →+* ℂ} (hφ : IsCMType φ) (s : ℕ) (κ : I → ℕ) (σ : ℂ) (α : Eˣ) :
    term φ (2 * s) κ σ α =
      (lamInf φ (2 * s) κ α)⁻¹ * ((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-σ) := by
  have key : ∀ i, ((‖φ i α‖ : ℝ) : ℂ) ^ (-2 * σ) = (((‖φ i α‖ ^ 2 : ℝ)) : ℂ) ^ (-σ) := fun i => by
    have hp : 0 < ‖φ i α‖ := by simp
    have : (((‖φ i α‖ ^ 2 : ℝ)) : ℂ) = ((‖φ i α‖ : ℝ) : ℂ) * ((‖φ i α‖ : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.mul_cpow_ofReal_nonneg hp.le hp.le,
      ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 hp.ne')]
    congr 1; ring
  rw [← TermUnit.prod_norm_sq hφ, ← TermUnit.prod_cpow _ _ (fun i => by positivity)]
  unfold term lamInf
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [key]
  have gen : ∀ (a c N : ℂ) (m n : ℕ), a⁻¹ ^ m * c ^ n * N = (a ^ m * c⁻¹ ^ n)⁻¹ * N := by
    intro a c N m n
    rw [mul_inv, inv_pow, inv_pow, inv_inv]
  exact gen _ _ _ _ _

theorem homothety (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I]
    (φ : I → E →+* ℂ) (hφ : IsCMType φ) (s : ℕ) (L : Set E) : Homothety φ (2 * s) L := by
  intro κ α S hS
  have hα : (α : E) ≠ 0 := α.ne_zero
  have hN : ((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, abs_ne_zero, Rat.cast_ne_zero, Algebra.norm_ne_zero_iff]; exact hα
  have key : IsLatSum φ (2 * s) κ ((fun x => (α : E) * x) '' L)
      (fun σ => (lamInf φ (2 * s) κ α)⁻¹ * ((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-σ) * S σ) := by
    refine ⟨?_, fun σ hσ => ?_⟩
    · exact ((differentiable_neg.const_cpow (Or.inl hN)).const_mul _).mul hS.1
    · have h1 := (hS.2 σ hσ).mul_left
        ((lamInf φ (2 * s) κ α)⁻¹ * ((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-σ))
      have hf : ((fun q' : modUnits ((fun x => (α : E) * x) '' L) => term φ (2 * s) κ σ q'.1.out) ∘ mulEquiv hα L) =
          fun q : modUnits L => (lamInf φ (2 * s) κ α)⁻¹ * ((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-σ) *
            term φ (2 * s) κ σ q.1.out := funext fun q => by
        show term φ (2 * s) κ σ (mulQ (α : E) q.1).out = _
        rw [term_out_mulQ hφ, term_eq_lamInf hφ]
      rw [← (mulEquiv hα L).hasSum_iff, hf]
      exact h1
  refine ⟨key, fun S' hS' => ?_⟩
  rw [hS'.unique key]
  simp

end GlobalTheory.HomothetyLatSum
end
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.HeckeGal
open GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols (IsTwistedSum IsSymbol conjChar classOf)
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (IsConjWt IsConjChar lamF upIdele)

namespace GlobalTheory.ToricTransport

def coordIn (E : Type) [Field E] [NumberField E] {I : Type} [Fintype I] (d s : ℕ) (κ : I → ℕ) (Ω T : ℂ) : ℂ :=
  (C0 E d (2 * s) κ : ℂ) * T / Ω ^ (2 * s * Fintype.card I + 2 * ∑ i, κ i)

def IsDatum {K E : Type} [Field K] [Field E] [NumberField E] [Algebra K E] {I : Type} [Fintype I] (ι : K →+* ℂ)
    (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) : Prop :=
  UnramFin E ∧ IsCMType φ ∧ (∀ i, (φ i).comp (algebraMap K E) = ι) ∧ 1 ≤ s ∧ (∀ i, 1 ≤ κ i) ∧ IsBaseCond 𝔣 ∧ IsFinSetSplitPlacesCoprimeConductor 𝔣 Q ∧
    IsValChar φ s κ 𝔣 ∅ χ

def TwistedTransport : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ),
    Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∃ Ω₀ : ℂ, Ω₀ ≠ 0 ∧
      (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (s : ℕ)
        (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E), IsDatum ι φ s κ 𝔣 Q χ →
        ∀ (ψ : PicO (condQ 𝔣 Q) →* ℂˣ) (T : ℂ), IsTwistedSum φ s κ (condQ 𝔣 Q) χ ψ T → IsAlgebraic ℚ (coordIn E d s κ Ω₀ T)) ∧
      ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (j : Ω →+* ℂ) (art : Ideles K →* Gab K Ω),
        j.comp (algebraMap K Ω) = ι → IsGlobalArtin art →
        ∀ (g : ℂ ≃+* ℂ) (σ : Formalism.ConjugateSelfDual.G K Ω) (t : (Af K)ˣ), (∀ x, j (σ x) = g (j x)) → IsSymbol art t σ →
        ∃ Ω₁ : ℂ, Ω₁ ≠ 0 ∧
          ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (s : ℕ)
            (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E), IsDatum ι φ s κ 𝔣 Q χ →
            ∀ (κ' : I → ℕ) (χ' : HChar E), IsConjWt φ g κ κ' → IsConjChar φ s κ' g χ χ' →
            ∀ (ψ : PicO (condQ 𝔣 Q) →* ℂˣ) (T T' : ℂ), IsTwistedSum φ s κ (condQ 𝔣 Q) χ ψ T →
              IsTwistedSum φ s κ' (condQ 𝔣 Q) χ' (conjChar g ψ) T' →
              g (coordIn E d s κ Ω₀ T) =
                coordIn E d s κ Ω₁ ((((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ *
                  (lamF s χ' (upIdele K E t) * ((conjChar g ψ (classOf K (condQ 𝔣 Q) t) : ℂˣ) : ℂ))⁻¹ * T')

theorem coordIn_div (E : Type) [Field E] [NumberField E] {I : Type} [Fintype I] {d s : ℕ} (hd : 0 < d) (hs : 1 ≤ s) (κ : I → ℕ)
    {Ω : ℂ} (hΩ : Ω ≠ 0) (T T₀ : ℂ) : coordIn E d s κ Ω T / coordIn E d s κ Ω T₀ = T / T₀ := by
  have hC : (C0 E d (2 * s) κ : ℂ) ≠ 0 := by exact_mod_cast (cmValueConst_pos E hd (by omega) κ).ne'
  rw [coordIn, coordIn, div_div_div_cancel_right₀ (pow_ne_zero _ hΩ), mul_div_mul_left _ _ hC]

end GlobalTheory.ToricTransport
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw

theorem _root_.GlobalTheory.T.lineBundle_trivial_of_generator_fpqc_descent : ∀ {X X' Z : Scheme.{0}} (M : LB X), M.IsLB → ∀ (f : X' ⟶ X), Flat f → Surjective f → QuasiCompact f → ∀ (g₁ g₂ : Z ⟶ X'), IsPullback g₁ g₂ f f → ∀ t : LB.Gen (M.pull f), t.IsGen → (∀ (z : Z) (J : (Z ⟶ X) → M.ι), Geo.Tor.Good M z J → val t g₁ z J = val t g₂ z J) → Triv M := by
  first | exact @GlobalTheory.FlatDescent.triv_of_gen_descent | exact GlobalTheory.FlatDescent.triv_of_gen_descent | (intros; apply GlobalTheory.FlatDescent.triv_of_gen_descent <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.exists_semidirect_character_ext_of_stable : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (∀ t : Γ, t ∈ Subgroup.zpowers s) → ∀ Y : G → ℂ, IsChar ℂ ℂ Y → (∀ g, Y (φ s g) = Y g) → ∃ Z : G ⋊[φ] Γ → ℂ, IsChar ℂ ℂ Z ∧ ∀ g, Z (inl g) = Y g := by
  first | (exact @GlobalTheory.StableExt.exists_ext) | (exact GlobalTheory.StableExt.exists_ext) | (intros; apply GlobalTheory.StableExt.exists_ext <;> assumption)
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.functionField_finite_support_sum_order_eq_zero : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ x : F, x ≠ 0 → {v : Place k F | v.1 x ≠ 1}.Finite ∧ ∑ᶠ v : Place k F, ord v x = 0 := by
  first | exact @GlobalTheory.Nef.finite_support_and_sum_ord_eq_zero | exact GlobalTheory.Nef.finite_support_and_sum_ord_eq_zero | (intros; apply GlobalTheory.Nef.finite_support_and_sum_ord_eq_zero <;> assumption)
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.functionFieldPlace_localIndex_scaled_uniformiser : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (v : Place k F) (n : ℕ) (M : Matrix (Fin n) (Fin n) F) (d : ℕ), M.det ≠ 0 →
    (∀ i j, v.1 (M⁻¹ i j) ≤ WithZero.exp (d : ℤ)) →
    ∃ (N : ℕ) (φ : (Fin n → F) →ₗ[k] (Fin N → k)), (N : ℤ) = n * d - ord v M.det ∧
      ∀ p : Fin n → F, (∀ i, v.1 (p i) ≤ WithZero.exp (d : ℤ)) → φ p = 0 →
        ∀ i, v.1 (M.mulVec p i) ≤ 1 := by
  first | exact @GlobalTheory.Nef.local_index_scaled | exact GlobalTheory.Nef.local_index_scaled | (intros; apply GlobalTheory.Nef.local_index_scaled <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.galoisDescent_freeSheaf_cechLevel_sepClosure : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (k : ℕ), Function.Injective (fun (s : (free R).obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op (SimplexCategory.mk (k)))) ⟶ F) (σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω)) => val s (Spec (CommRingCat.of Ω)) (cechPt (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) k (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (fun i => Spec.map (CommRingCat.ofHom ((σ i : Ω ≃ₐ[K] Ω) : Ω →+* Ω))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext fun x => (σ i).commutes x))) ∧ (∀ s : (free R).obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op (SimplexCategory.mk (k)))) ⟶ F, IsLocallyConstant (fun σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω) => val s (Spec (CommRingCat.of Ω)) (cechPt (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) k (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (fun i => Spec.map (CommRingCat.ofHom ((σ i : Ω ≃ₐ[K] Ω) : Ω →+* Ω))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext fun x => (σ i).commutes x)))) ∧ ∀ φ : (Fin (k + 1) → (Ω ≃ₐ[K] Ω)) → Sec F (Spec (CommRingCat.of Ω)), IsLocallyConstant φ → (∀ (τ : Ω ≃ₐ[K] Ω) (σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω)), φ (fun i => τ * σ i) = Sec.res (Spec.map (CommRingCat.ofHom (τ : Ω →+* Ω))) (φ σ)) → ∃ s : (free R).obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op (SimplexCategory.mk (k)))) ⟶ F, ∀ σ, val s (Spec (CommRingCat.of Ω)) (cechPt (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) k (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (fun i => Spec.map (CommRingCat.ofHom ((σ i : Ω ≃ₐ[K] Ω) : Ω →+* Ω))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext fun x => (σ i).commutes x)) = φ σ := by
  first | (exact @GlobalTheory.EtC.GalSec.gal_sec) | (exact GlobalTheory.EtC.GalSec.gal_sec) | (intros; apply GlobalTheory.EtC.GalSec.gal_sec  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.BcCoprod

theorem bc_map_fst {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) {V U : Over S} (g : V ⟶ U) :
    (bc p).map g ≫ (pullback.fst p (sch.map U.hom) : (bc p).obj U ⟶ E) = pullback.fst p (sch.map V.hom) := by
  simp only [bc, pullback.map]
  set_option synthInstance.maxHeartbeats 200000 in
    simpa only [Category.comp_id] using pullback.lift_fst _ _ _

theorem bc_map_snd {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) {V U : Over S} (g : V ⟶ U) :
    (bc p).map g ≫ (pullback.snd p (sch.map U.hom) : (bc p).obj U ⟶ _) = pullback.snd p (sch.map V.hom) ≫ sch.map g.left := by
  set_option synthInstance.maxHeartbeats 200000 in
    simp only [bc, pullback.map]
  set_option synthInstance.maxHeartbeats 200000 in
    exact pullback.lift_snd _ _ _

theorem isPullback_bc {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) {V U : Over S} (g : V ⟶ U) :
    IsPullback ((bc p).map g) (pullback.snd p (sch.map V.hom)) (pullback.snd p (sch.map U.hom)) (sch.map g.left) := by
  have h2 : sch.map g.left ≫ sch.map U.hom = sch.map V.hom := by
    rw [← sch.map_comp, Over.w g]
  have outer : IsPullback ((bc p).map g ≫ (pullback.fst p (sch.map U.hom) : (bc p).obj U ⟶ E))
      (pullback.snd p (sch.map V.hom)) p (sch.map g.left ≫ sch.map U.hom) := by
    rw [bc_map_fst p g, h2]
    exact IsPullback.of_hasPullback p (sch.map V.hom)
  exact IsPullback.of_right outer (bc_map_snd p g) (IsPullback.of_hasPullback p (sch.map U.hom))

theorem main : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (E : Spc) (p : E ⟶ sch.obj S) (U : Over S) (ι : Type) (V : ι → Over S) (j : ∀ i, V i ⟶ U), IsColimit (Cofan.mk U.left (fun i => (j i).left)) → ∀ n : ℤ, Function.Bijective (fun (x : H R ((bc p).obj U) F n) (i : ι) => pull R ((bc p).map (j i)) F n x) := by
  intro R _ F S E p U ι V j hc n
  refine GlobalTheory.T.etaleSpaceCohomology_levelwise_coproduct_bijective R F ((bc p).obj U) ι (fun i => (bc p).obj (V i)) (fun i => (bc p).map (j i)) (fun k => ?_) n
  refine GlobalTheory.T.freeEtaleSheaf_presheaf_over_coproduct_eq_sum R U.left ι (fun i => (V i).left) (fun i => (j i).left) hc (((bc p).obj U).obj k)
    ((pullback.snd p (sch.map U.hom)).app k) (fun i => ((bc p).obj (V i)).obj k)
    (fun i => ((bc p).map (j i)).app k) (fun i => (pullback.snd p (sch.map (V i).hom)).app k) (fun i => ?_)
  exact (isPullback_bc p (j i)).map ((evaluation _ _).obj k)

end GlobalTheory.EtC.BcCoprod
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.coalternatingExact_of_finiteType_iso_filteredColimits : ∀ (N M : CommRingCat.{0} ⥤ AddCommGrpCat.{1}) (ε : N ⟶ M), PreservesFilteredColimitsOfSize.{0, 0} N → (∀ A : CommRingCat.{0}, Algebra.FiniteType ℤ A → IsIso (ε.app A)) → (∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → WExact M (coAug g)) → ∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → WExact N (coAug g) := by
  first | (exact @GlobalTheory.EtC.wExact_of_finiteType_iso) | (exact GlobalTheory.EtC.wExact_of_finiteType_iso) | (intros; apply GlobalTheory.EtC.wExact_of_finiteType_iso  <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem holo_etale_iff_holo_chart : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → ∀ (Ω : Set Y) (u : Y → ℂ), IsOpen Ω → ((∀ e : OpenPartialHomeomorph U (V n), IsChart n (fun y : U => z y) e → DifferentiableOn ℂ ((fun y : U => u y) ∘ e.symm) (e.target ∩ e.symm ⁻¹' (Subtype.val ⁻¹' Ω))) ↔ ∀ i, DifferentiableOn ℂ (u ∘ (A.chart i).symm) ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ Ω))) := by
  intro n Y _ _ _ _ _ ι La _ A U z hE Ω u hΩ
  have hloc := GlobalTheory.T.etale_isLocalHomeomorph' n Y ι La A U z hE
  constructor
  · intro h i v hv
    obtain ⟨hvt, hvU, hvΩ⟩ := hv
    obtain ⟨e, hes, hez⟩ := hloc ⟨(A.chart i).symm v, hvU⟩
    have he : IsChart n (fun y : U => z y) e := fun w _ => by rw [hez]
    have hev : ∀ w : U, e w = z w := fun w => by rw [← hez]
    obtain ⟨W, hW, hWe⟩ := isOpen_induced_iff.1 e.open_source
    have hO : IsOpen (e.target ∩ e.symm ⁻¹' (Subtype.val ⁻¹' Ω)) :=
      e.isOpen_inter_preimage_symm (hΩ.preimage continuous_subtype_val)
    have hmem : z ((A.chart i).symm v) ∈ e.target ∩ e.symm ⁻¹' (Subtype.val ⁻¹' Ω) := by
      have h1 := hev ⟨(A.chart i).symm v, hvU⟩
      simp only at h1
      rw [← h1]
      refine ⟨e.map_source hes, ?_⟩
      simp only [Set.mem_preimage]
      rw [e.left_inv hes]
      exact hvΩ
    have h1 : DifferentiableAt ℂ ((fun y : U => u y) ∘ e.symm) (z ((A.chart i).symm v)) :=
      (h e he _ hmem).differentiableAt (hO.mem_nhds hmem)
    have h2 : DifferentiableAt ℂ (z ∘ (A.chart i).symm) v :=
      (hE.holo i v ⟨hvt, hvU⟩).differentiableAt
        (((A.chart i).isOpen_inter_preimage_symm hE.isOpen).mem_nhds ⟨hvt, hvU⟩)
    have h3 := DifferentiableAt.comp v (g := (fun y : U => u y) ∘ e.symm)
      (f := z ∘ (A.chart i).symm) h1 h2
    refine (h3.congr_of_eventuallyEq ?_).differentiableWithinAt
    have hvW : (A.chart i).symm v ∈ W := by
      rw [← hWe] at hes
      exact hes
    filter_upwards [((A.chart i).isOpen_inter_preimage_symm (hE.isOpen.inter hW)).mem_nhds
      ⟨hvt, hvU, hvW⟩] with v' hv'
    have hs : (⟨(A.chart i).symm v', hv'.2.1⟩ : U) ∈ e.source := by
      rw [← hWe]
      exact hv'.2.2
    have h4 := hev ⟨(A.chart i).symm v', hv'.2.1⟩
    simp only at h4
    simp only [Function.comp]
    rw [← h4, e.left_inv hs]
  · intro h e he v hv
    obtain ⟨hvt, hvΩ⟩ := hv
    have hs := A.mem_pick (e.symm v : U)
    set i := A.pick (e.symm v : U)
    obtain ⟨hc, hev, -⟩ := GlobalTheory.T.contDiffAt_chart_inverse_of_etale n Y ι La A U z hE e he v hvt i hs
    have hmem : A.chart i (e.symm v : U) ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ Ω) := by
      refine ⟨(A.chart i).map_source hs, ?_⟩
      simp only [Set.mem_preimage]
      rw [(A.chart i).left_inv hs]
      exact ⟨(e.symm v).2, hvΩ⟩
    have h1 : DifferentiableAt ℂ (u ∘ (A.chart i).symm) (A.chart i (e.symm v : U)) :=
      (h i _ hmem).differentiableAt
        (((A.chart i).isOpen_inter_preimage_symm (hE.isOpen.inter hΩ)).mem_nhds hmem)
    have h3 := DifferentiableAt.comp v (g := u ∘ (A.chart i).symm)
      (f := fun v' => A.chart i (e.symm v' : U)) h1 (hc.differentiableAt (by simp))
    refine (h3.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hev] with v' hv'
    simp only [Function.comp]
    rw [(A.chart i).left_inv hv']

end GlobalTheory.OTY
end
