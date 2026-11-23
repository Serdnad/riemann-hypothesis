module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle694
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle029
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle040
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle696
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle658
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle701
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle667
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle685
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle697
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle192
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle253
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle221
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle233
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle235
public import Formalism.DegreeFormula.PointDegree.PowSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle699
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle668

@[expose] public section

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical


theorem _root_.GlobalTheory.T.exists_variety_connectedComponent_genericFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F), SmoothOfRelativeDimension Dw.dim (genStr Z) → ∀ (Y : Var F) (π : Y.X ⟶ gen Z), π ≫ genStr Z ≫ spMap e.toRingHom = Y.str → ∃ (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j ∧ j ≫ genStr Z ≫ spMap e.toRingHom = X.str ∧ Set.range π ⊆ Set.range j := by
  first | exact @GlobalTheory.CompOfVar.exists_var_comp | exact GlobalTheory.CompOfVar.exists_var_comp | (intros; apply GlobalTheory.CompOfVar.exists_var_comp <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx
open scoped Matrix
open Filter Topology


theorem _root_.GlobalTheory.T.exists_analytic_flagDomain_section_flatCoordinates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (p q n : ℕ) (Xd : ReciprocityTheory.ChartRestriction.G.FD.Data E (p + q)), Xd.p0 = p + q - p → ∀ (h : Fintype.card (Xd.Ψ × Fin p × Fin (p + q - p)) = n) (v : ReciprocityTheory.L2DbarEstimates.V n), GlobalTheory.UnifDens.flatL h v ∈ DomFlat Xd.Ψ p (p + q - p) → ∃ s : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.ChartRestriction.G.FD.Frame Xd.Ψ (p + q), AnalyticAt ℂ s v ∧ (∀ (τ : Xd.Ψ) (a b : Fin p), AnalyticAt ℂ (fun w => coW Xd (Nat.le_add_right p q) (s w) τ a b) v) ∧ ∀ᶠ w in nhds v, ∃ hs : s w ∈ Xd.dom, flat (domPt Xd (Nat.le_add_right p q) (Equiv.refl Xd.Ψ) (s w)) = GlobalTheory.UnifDens.flatL h w := by
  first | exact @GlobalTheory.FrameLift.exists_analytic_section | exact GlobalTheory.FrameLift.exists_analytic_section | (intros; apply GlobalTheory.FrameLift.exists_analytic_section <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.punctPolydiscCover_latticeBasis_real_holomorphic : ∀ (n a g r : ℕ) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ), IsLatFam (Metric.ball 0 1) K → ContinuousOn lam (logDom n a) → (∀ s ∈ logDom n a, LinearIndependent ℤ (lam s) ∧ Submodule.span ℝ (Set.range (lam s)) = ⊤ ∧ ∀ w, w ∈ K (logExp a s) ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) → r = 2 * g ∧ (∀ s ∈ logDom n a, LinearIndependent ℝ (lam s)) ∧ ∀ (j : Fin r) (k : Fin g), DifferentiableOn ℂ (fun s => lam s j k) (logDom n a) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.latBasis_logCover_real_holo | exact GlobalTheory.ShFam.Hor.LogCh.latBasis_logCover_real_holo | (intros; apply GlobalTheory.ShFam.Hor.LogCh.latBasis_logCover_real_holo <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.not_periodMatrix_intVec_continuous_boundary : ∀ (n a g r₀ r : ℕ) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℤ) (c : Matrix (Fin r₀) (Fin r) ℤ) (α : Matrix (Fin g) (Fin r₀) ℚ) (φ : Matrix (Fin g) (Fin r) ℚ) (rk D : ℕ), IsLatFam (Metric.ball 0 1) K → AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ i, ζ z i ∈ K z) → IsLatBasis (K 0) (ζ 0) → (∀ s ∈ logDom n a, LinearIndependent ℝ (lam s) ∧ ∀ w, w ∈ K (logExp a s) ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) → (∀ s ∈ logDom n a, ∀ i, ζ (logExp a s) i = ∑ j, c i j • lam s j) → Mᵀ = -M → φ * M.map (Int.cast : ℤ → ℚ) * (α * c.map (Int.cast : ℤ → ℚ))ᵀ = 1 → (∀ i : Fin g, i.val < rk → ∀ m, ((α * c.map (Int.cast : ℤ → ℚ)) * M.map (Int.cast : ℤ → ℚ) * (c.map (Int.cast : ℤ → ℚ))ᵀ) i m = 0) → 0 < D → (∀ s ∈ logDom n a, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α).det) → ∀ v : Fin g → ℤ, v ≠ 0 → (∀ j : Fin g, rk ≤ j.val → v j = 0) → ∀ F : (Fin n → ℂ) → Fin g → ℂ, ContinuousOn F (Metric.ball 0 1) → ¬ ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1 → (GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s).mulVec (fun j => (v j : ℂ)) = F (logExp a s) := by
  first | exact @GlobalTheory.PeriodFrame.not_perTau_mulVec_eq_continuous | exact GlobalTheory.PeriodFrame.not_perTau_mulVec_eq_continuous | (intros; apply GlobalTheory.PeriodFrame.not_perTau_mulVec_eq_continuous <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

theorem _root_.GlobalTheory.T.exists_common_denominator_strictness_smooth_fan : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (φ : InvFun ℤ), IsPolFanOn (id : ℤ → ℤ) φ X → ∃ N : ℕ, 0 < N ∧ ∀ B ∈ psdCone (bar := (id : ℤ → ℤ)) (X := X), ∃ (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (w : (X × X) →₀ ℤ), IsCone (id : ℤ → ℤ) φ u ∧ StrictWith (id : ℤ → ℤ) φ N (linW w) u ∧ B ∈ rcone u := by
  first | exact @GlobalTheory.PolCell.exists_common_den | exact GlobalTheory.PolCell.exists_common_den | (intros; apply GlobalTheory.PolCell.exists_common_den <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.balancedFormCellMultiplicity_pos : ∀ {O : Type} [CommRing O] [Module.Finite ℤ O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    {m : ℕ} (δ : Fin m → balForms bar X), 0 < cellMult bar δ := by
  first | exact @GlobalTheory.PolFan.cellMult_pos | exact GlobalTheory.PolFan.cellMult_pos | (intros; apply GlobalTheory.PolFan.cellMult_pos <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.isPrimitiveBalancedForm_primitive_among_intForms : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] (β : LinearMap.BilinForm ℤ X) (hβ : β ∈ balForms bar X), IsPrim bar (⟨β, hβ⟩ : balForms bar X) →
  ∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β → k = 1 := by
  first | exact @GlobalTheory.PolFan.isPrim_eq_one_of_smul_eq | exact GlobalTheory.PolFan.isPrim_eq_one_of_smul_eq | (intros; apply GlobalTheory.PolFan.isPrim_eq_one_of_smul_eq <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.primitiveBalancedForm_eq_of_same_ray : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X]
    (β β' : balForms bar X) (p r : ℕ), IsPrim bar β → IsPrim bar β' → 0 < p → 0 < r → p • β = r • β' → β = β' := by
  first | exact @GlobalTheory.PolFan.isPrim_ray_eq | exact GlobalTheory.PolFan.isPrim_ray_eq | (intros; apply GlobalTheory.PolFan.isPrim_ray_eq <;> assumption)
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

namespace GlobalTheory.GrassTopDim

attribute [-instance] GlobalTheory.CompHt.fintypePsi

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem relIdeal_isHomogeneous (H : Host E) (Dw : Datum H) :
    (relIdeal H Dw).IsHomogeneous
      (weightedHomogeneousSubmodule ℝ (Prod.snd : (E →+* ℂ) × ℕ → ℕ)) := by
  apply Ideal.homogeneous_span
  rintro x ((⟨τ, rfl⟩ | ⟨τ, k, -, rfl⟩) | ⟨τ, k, -, rfl⟩)
  · refine ⟨0, ?_⟩
    refine sub_mem ?_ ?_
    · rw [mem_weightedHomogeneousSubmodule]
      exact isWeightedHomogeneous_X ℝ Prod.snd (τ, 0)
    · rw [mem_weightedHomogeneousSubmodule]
      exact isWeightedHomogeneous_one ℝ Prod.snd
  · refine ⟨k, ?_⟩
    rw [mem_weightedHomogeneousSubmodule]
    exact isWeightedHomogeneous_X ℝ Prod.snd (τ, k)
  · refine ⟨k, Submodule.sum_mem _ fun a ha => ?_⟩
    rw [mem_weightedHomogeneousSubmodule]
    have ha' : a ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)
    have h := ((isWeightedHomogeneous_C Prod.snd ((-1 : ℝ) ^ (k - a))).mul
      (isWeightedHomogeneous_X ℝ Prod.snd (τ.1, a))).mul
      (isWeightedHomogeneous_X ℝ Prod.snd (conjEmb τ.1, k - a))
    convert h using 1
    simp only [zero_add]
    omega

theorem pointPoly_isWeightedHomogeneous (H : Host E) (Dw : Datum H) :
    IsWeightedHomogeneous Prod.snd (pointPoly H Dw) (Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q)) := by
  have h : ∀ τ ∈ (Finset.univ : Finset (GlobalTheory.AllWt.Psi H)), IsWeightedHomogeneous Prod.snd
      ((C ((-1 : ℝ) ^ Dw.mult τ.1) * X (τ.1, Dw.mult τ.1)) ^ (Dw.p + Dw.q - Dw.mult τ.1)) (Dw.p * Dw.q) := by
    intro τ _
    have hm : Dw.mult τ.1 = Dw.p := GlobalTheory.PointChern.mult_of_mem Dw τ.2
    have h1 := ((isWeightedHomogeneous_C Prod.snd ((-1 : ℝ) ^ Dw.mult τ.1)).mul
      (isWeightedHomogeneous_X ℝ Prod.snd (τ.1, Dw.mult τ.1))).pow (Dw.p + Dw.q - Dw.mult τ.1)
    convert h1 using 1
    simp only [hm, zero_add, Nat.add_sub_cancel_left]
    ring
  have h2 := IsWeightedHomogeneous.prod Finset.univ _ _ h
  rw [pointPoly]
  convert h2 using 1
  simp [Finset.sum_const, Finset.card_univ, smul_eq_mul]

theorem mem_of_forall_dual {V : Type} [AddCommGroup V] [Module ℝ V] (S : Submodule ℝ V) (v : V)
    (h : ∀ f : Module.Dual ℝ (V ⧸ S), f (S.mkQ v) = 0) : v ∈ S := by
  have := (Module.forall_dual_apply_eq_zero_iff ℝ (S.mkQ v)).1 h
  simpa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using this

theorem top_eq_smul_point : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ),
    IsWeightedHomogeneous Prod.snd Q (Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q)) →
      ∃ c : ℝ, Q - C c * pointPoly H Dw ∈ relIdeal H Dw := by
  intro E _ _ _ H Dw Q hQ
  obtain ⟨β, hβ⟩ := GlobalTheory.T.admissible_form_eq_mul_point_class_value E H Dw Q
  set D := Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q) with hD
  let N : Submodule ℝ (MvPolynomial ((E →+* ℂ) × ℕ) ℝ) := Submodule.span ℝ
    {f | ∃ d : (E →+* ℂ) × ℕ →₀ ℕ, (d.sum fun x i => x.2 * i) ≠ D ∧ f = monomial d 1}
  let S := (relIdeal H Dw).restrictScalars ℝ ⊔ N
  have hS : Q - C β * pointPoly H Dw ∈ S := by
    apply mem_of_forall_dual
    intro f
    let Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ := f ∘ₗ S.mkQ
    have hker : ∀ x ∈ S, Θ x = 0 := fun x hx => by
      simp [Θ, (Submodule.Quotient.mk_eq_zero _).2 hx]
    have hrel : ∀ x ∈ relIdeal H Dw, Θ x = 0 := fun x hx =>
      hker x (Submodule.mem_sup_left (by simpa using hx))
    have hadm : GlobalTheory.Schubert.admitted H Dw Θ := by
      refine ⟨fun τ k hk P => hrel _ ?_, fun τ P => hrel _ ?_, fun τ k hk P => hrel _ ?_,
        fun d hd => hker _ (Submodule.mem_sup_right (Submodule.subset_span ⟨d, hd, rfl⟩))⟩
      · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Or.inr ⟨τ, k, hk, rfl⟩))
      · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Or.inl (Or.inl ⟨τ, rfl⟩)))
      · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Or.inl (Or.inr ⟨τ, k, hk, rfl⟩)))
    show Θ (Q - C β * pointPoly H Dw) = 0
    rw [map_sub, hβ Θ hadm, C_mul', map_smul, smul_eq_mul, sub_self]
  obtain ⟨r, hr, n, hn, hrn⟩ := Submodule.mem_sup.1 hS
  have hn0 : ∀ n ∈ N, weightedHomogeneousComponent Prod.snd D n = 0 := by
    intro n hn
    induction hn using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨d, hd, rfl⟩ := hx
      refine weightedHomogeneousComponent_eq_zero' _ _ fun d' hd' => ?_
      rw [support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hd'
      subst hd'
      rw [Finsupp.weight_apply]
      intro h
      apply hd
      rw [← h]
      exact Finsupp.sum_congr fun x _ => by rw [smul_eq_mul, mul_comm]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, hx, smul_zero]
  have hhom : IsWeightedHomogeneous Prod.snd (Q - C β * pointPoly H Dw) D := by
    have h1 : Q ∈ weightedHomogeneousSubmodule ℝ Prod.snd D := (mem_weightedHomogeneousSubmodule _ _ _ _).2 hQ
    have h2 : pointPoly H Dw ∈ weightedHomogeneousSubmodule ℝ Prod.snd D :=
      (mem_weightedHomogeneousSubmodule _ _ _ _).2 (pointPoly_isWeightedHomogeneous H Dw)
    rw [← mem_weightedHomogeneousSubmodule, C_mul']
    exact sub_mem h1 (Submodule.smul_mem _ β h2)
  refine ⟨β, ?_⟩
  rw [← hhom.weightedHomogeneousComponent_same, ← hrn, map_add (f := _), hn0 n hn, add_zero]
  exact weightedHomogeneousComponent_mem_of_mem ℝ Prod.snd (relIdeal_isHomogeneous H Dw) (by simpa using hr) D

end GlobalTheory.GrassTopDim
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

namespace GlobalTheory.GrassTop

attribute [-instance] GlobalTheory.CompHt.fintypePsi

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem rho_eq_flagMap (H : Host E) (Dw : Datum H) : rho H Dw = GlobalTheory.Schubert.flagMap Dw := rfl

theorem degFl_rho_antisymm (H : Host E) (Dw : Datum H) (Q : MvPolynomial (Root Dw.mult) ℝ) :
    Formalism.DegreeFormula.degFl (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q)
      (rho H Dw (GlobalTheory.GoodMetric.antisymm Q)) =
      (∏ τ, ((Dw.mult τ).factorial : ℝ)) * Formalism.DegreeFormula.degFl (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (rho H Dw Q) := by
  rw [rho_eq_flagMap]
  unfold GlobalTheory.GoodMetric.antisymm

  rw [map_sum, ← GlobalTheory.Schubert.flagLin_apply, map_sum]
  have hterm : ∀ w : ∀ τ, Equiv.Perm (Fin (Dw.mult τ)),
      GlobalTheory.Schubert.flagLin (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (GlobalTheory.Schubert.flagMap Dw
        ((((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ)) • rename (fun x : Root Dw.mult =>
          (⟨x.1, w x.1 x.2⟩ : Root Dw.mult)) Q)) =
        Formalism.DegreeFormula.degFl (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (GlobalTheory.Schubert.flagMap Dw Q) := by
    intro w
    rw [map_zsmul, map_zsmul, GlobalTheory.Schubert.flagLin_apply,
      GlobalTheory.Schubert.degFl_flagMap_rename_perm, zsmul_eq_mul, ← mul_assoc]
    have hs : ((((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : ℝ)) *
        (((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : ℝ) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp
    rw [hs, one_mul]
  rw [Finset.sum_congr rfl fun w _ => hterm w, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_pi]
  push_cast
  simp only [Fintype.card_perm, Fintype.card_fin]

theorem prod_factorial_mult (H : Host E) (Dw : Datum H) :
    (∏ τ, ((Dw.mult τ).factorial : ℝ)) =
      ((Dw.p.factorial * Dw.q.factorial : ℝ)) ^ Fintype.card (GlobalTheory.AllWt.Psi H) := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)]
  have e1 : ∀ τ : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0}, ((Dw.mult τ.1).factorial : ℝ) = Dw.p.factorial := by
    intro τ; simp [Datum.mult, τ.2]
  have e2 : ∀ τ : {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0}, ((Dw.mult τ.1).factorial : ℝ) = Dw.q.factorial := by
    intro τ; simp [Datum.mult, τ.2]
  simp only [e1, e2, Finset.prod_const, Finset.card_univ, mul_pow]
  congr 2
  exact Fintype.card_congr
    { toFun := fun τ => (⟨conjEmb τ.1, GlobalTheory.AllWt.conj_mem τ.2⟩ : GlobalTheory.AllWt.Psi H)
      invFun := fun τ => ⟨conjEmb τ.1, GlobalTheory.AllWt.conj_not_mem τ⟩
      left_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb τ.1)
      right_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb τ.1) }

theorem intGr_eq_flagDeg : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (la : GlobalTheory.AllWt.Weight Dw) (R : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) (D : ℕ),
    D = Fintype.card (GlobalTheory.AllWt.Psi H) * ((Dw.p + Dw.q) * (Dw.p + Dw.q - 1) / 2) →
    GlobalTheory.GoodMetric.antisymm
      ((∑ x : Root Dw.mult, MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) * MvPolynomial.X x) ^ D) =
      chernRoots Dw.mult R * rootDiscr Dw.mult →
    intGr H Dw R = Formalism.DegreeFormula.flagDeg (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (fun τ i => (la τ i : ℝ)) := by
  intro E _ _ _ H Dw la R D hD hA
  have hPsi : GlobalTheory.CompHt.fintypePsi (H := H) =
      (inferInstance : Fintype (GlobalTheory.AllWt.Psi H)) := Subsingleton.elim _ _
  unfold intGr
  rw [hPsi]
  rw [← hA, degFl_rho_antisymm, prod_factorial_mult, map_pow, rho_eq_flagMap,
    GlobalTheory.Schubert.chernRootSubstitution_weightLineBundle_eq_linRoot, hD]
  have hpos : ((Dw.p.factorial * Dw.q.factorial : ℝ)) ^ Fintype.card (GlobalTheory.AllWt.Psi H) ≠ 0 := by
    apply pow_ne_zero; exact_mod_cast (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)).ne'
  rw [mul_div_cancel_left₀ _ hpos]
  rfl

end GlobalTheory.GrassTop
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

namespace GlobalTheory.GrassTop.RelVanish

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem rho_eq_flagMap (H : Host E) (Dw : Datum H) : rho H Dw = GlobalTheory.Schubert.flagMap Dw := by
  unfold rho GlobalTheory.Schubert.flagMap
  congr 1

noncomputable def numLin (H : Host E) (Dw : Datum H) : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ :=
  GlobalTheory.Schubert.flagLin (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) ∘ₗ (GlobalTheory.Schubert.flagMap Dw).toLinearMap ∘ₗ
    LinearMap.mulRight ℝ (rootDiscr Dw.mult) ∘ₗ (chernRoots Dw.mult).toLinearMap

theorem numLin_apply (H : Host E) (Dw : Datum H) (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) :
    numLin H Dw Q = Formalism.DegreeFormula.degFl (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q)
      (GlobalTheory.Schubert.flagMap Dw (chernRoots Dw.mult Q * rootDiscr Dw.mult)) := by
  simp [numLin, GlobalTheory.Schubert.flagLin_apply]

theorem numLin_of_chernRoots_eq_zero (H : Host E) (Dw : Datum H) (g : MvPolynomial ((E →+* ℂ) × ℕ) ℝ)
    (hg : chernRoots Dw.mult g = 0) (a : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) : numLin H Dw (g * a) = 0 := by
  rw [numLin_apply, map_mul (chernRoots Dw.mult), hg, zero_mul, zero_mul, map_zero, ← GlobalTheory.Schubert.flagLin_apply, map_zero]

theorem chernRoots_X_zero_sub_one (H : Host E) (Dw : Datum H) (τ : E →+* ℂ) :
    chernRoots Dw.mult (X (τ, 0) - 1 : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) = 0 := by
  simp [chernRoots, esymm_zero]

theorem chernRoots_X_of_lt (H : Host E) (Dw : Datum H) (τ : E →+* ℂ) (k : ℕ) (hk : Dw.mult τ < k) :
    chernRoots Dw.mult (X (τ, k) : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) = 0 := by
  have h0 : esymm (Fin (Dw.mult τ)) ℝ k = 0 := by
    unfold esymm
    rw [Finset.powersetCard_eq_empty.mpr (by simpa using hk)]
    simp
  simp [chernRoots, h0]

theorem numLin_relPoly (H : Host E) (Dw : Datum H) (τ : GlobalTheory.AllWt.Psi H) (k : ℕ) (hk : 1 ≤ k)
    (a : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) : numLin H Dw (GlobalTheory.PointChern.relPoly τ k * a) = 0 := by
  rw [numLin_apply, map_mul (chernRoots Dw.mult), mul_assoc, map_mul, GlobalTheory.Schubert.RelKill.flagMap_relPoly]
  exact Formalism.DegreeFormula.degreeEsymmMulEqZero _ _ τ k _ hk

theorem numLin_mul_eq_zero (H : Host E) (Dw : Datum H) (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ)
    (hQ : Q ∈ relIdeal H Dw) : ∀ a, numLin H Dw (Q * a) = 0 := by
  unfold relIdeal at hQ
  induction hQ using Submodule.span_induction with
  | mem x hx =>
    intro a
    rcases hx with (⟨τ, rfl⟩ | ⟨τ, k, hk, rfl⟩) | ⟨τ, k, hk, rfl⟩
    · exact numLin_of_chernRoots_eq_zero H Dw _ (chernRoots_X_zero_sub_one H Dw τ) a
    · exact numLin_of_chernRoots_eq_zero H Dw _ (chernRoots_X_of_lt H Dw τ k hk) a
    · exact numLin_relPoly H Dw τ k hk a
  | zero => intro a; simp
  | add x y _ _ hx hy => intro a; rw [add_mul, map_add (f := _), hx, hy, add_zero]
  | smul r x _ hx => intro a; rw [smul_eq_mul, mul_assoc, mul_comm r, mul_assoc]; exact hx _

end GlobalTheory.GrassTop.RelVanish

namespace GlobalTheory.GrassTop

theorem intGr_eq_zero_of_mem_relIdeal : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), Q ∈ relIdeal H Dw → intGr H Dw Q = 0 := by
  intro E _ _ _ H Dw Q hQ
  have h := RelVanish.numLin_mul_eq_zero H Dw Q hQ 1
  rw [mul_one, RelVanish.numLin_apply, ← RelVanish.rho_eq_flagMap] at h
  rw [intGr, h, zero_div]

end GlobalTheory.GrassTop
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

namespace GlobalTheory.PolFan.Mark

theorem finite_bilinForm_abs_le (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (B : X → X → ℤ) :
    {x : LinearMap.BilinForm ℤ X | ∀ a b, |x a b| ≤ B a b}.Finite := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := X)
  let f : LinearMap.BilinForm ℤ X → (s × s → ℤ) := fun x p => x p.1 p.2
  have hf : Function.Injective f := fun x y h =>
    LinearMap.ext_on hs fun a ha => LinearMap.ext_on hs fun b hb => congrFun h (⟨a, ha⟩, ⟨b, hb⟩)
  have hfin : (Set.pi Set.univ fun p : s × s => Set.Icc (-B p.1 p.2) (B p.1 p.2)).Finite :=
    Set.Finite.pi' (fun p : s × s => Set.finite_Icc (-B p.1 p.2) (B p.1 p.2)) |>.subset fun g hg p => hg p trivial
  exact (hfin.preimage hf.injOn).subset fun x hx p _ => abs_le.1 (hx p.1 p.2)

theorem abs_le_of_indec {X : Type} [AddCommGroup X] {m : ℕ} (τ : Fin m → LinearMap.BilinForm ℤ X)
    {x : LinearMap.BilinForm ℤ X} (hx : InRCone τ x)
    (hind : ∀ y z, InRCone τ y → InRCone τ z → y ≠ 0 → z ≠ 0 → y + z ≠ x) (a b : X) :
    |x a b| ≤ ∑ j, |τ j a b| := by
  classical
  obtain ⟨c, hc, h⟩ := hx
  have hv : ∀ a b, ((x a b : ℤ) : ℝ) = ∑ i, c i * (τ i a b : ℝ) := fun a b => by
    have := LinearMap.congr_fun₂ h a b
    simpa [toReal, LinearMap.sum_apply] using this
  by_cases hex : ∃ j, τ j ≠ 0 ∧ 1 ≤ c j
  · obtain ⟨j, hj, hcj⟩ := hex
    have hin : InRCone τ (x - τ j) := by
      refine ⟨c - Pi.single j 1, fun i => ?_, LinearMap.ext₂ fun a b => ?_⟩
      · by_cases hi : i = j
        · subst hi; simpa using hcj
        · simpa [Pi.single_apply, hi] using hc i
      · simp [toReal, LinearMap.sum_apply, sub_mul, Finset.sum_sub_distrib, Pi.single_apply, hv]
    have hx0 : x - τ j = 0 := by
      by_contra h0
      exact hind _ _ hin (inRCone_self τ j) h0 hj (by simp)
    rw [sub_eq_zero.1 hx0]
    exact Finset.single_le_sum (f := fun j => |τ j a b|) (fun i _ => abs_nonneg _) (Finset.mem_univ j)
  · push Not at hex
    have : ((|x a b| : ℤ) : ℝ) ≤ ((∑ j, |τ j a b| : ℤ) : ℝ) := by
      push_cast
      rw [hv]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      by_cases hi : τ i = 0
      · simp [hi]
      · rw [abs_mul, abs_of_nonneg (hc i)]
        exact mul_le_of_le_one_left (abs_nonneg _) (hex i hi).le
    exact_mod_cast this

theorem finite_indec_inRCone (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (m : ℕ)
    (τ : Fin m → LinearMap.BilinForm ℤ X) :
    {x : LinearMap.BilinForm ℤ X | InRCone τ x ∧ x ≠ 0 ∧
      ∀ y z, InRCone τ y → InRCone τ z → y ≠ 0 → z ≠ 0 → y + z ≠ x}.Finite :=
  (finite_bilinForm_abs_le X fun a b => ∑ j, |τ j a b|).subset fun _ hx => abs_le_of_indec τ hx.1 hx.2.2

end GlobalTheory.PolFan.Mark
end
