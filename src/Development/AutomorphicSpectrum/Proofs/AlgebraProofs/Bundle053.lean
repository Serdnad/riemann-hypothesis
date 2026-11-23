module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle048
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle049
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle003
public import Development.WeilBound.CoreStatements.HodgeTatePoints.ReBase
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle031
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle050
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle012
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle015
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle031
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle019
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle015
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle018
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateNormComparison
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
import Mathlib.Tactic.ReduceModChar
import Development.WeilBound.CoreStatements.HodgeTatePoints.ProdIccFin
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusMatrix
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle020
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle015
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle029
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle006
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle032

@[expose] public section

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem _root_.GlobalTheory.T.formal_hermitian_action_pairing : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), (∃ ρH : O →+* Module.End R ((Fin d → R) × (Fin d → R)), ∀ a, ρH a = rhoH B a) ∧ (bil B.sy 1 1).transpose = - bil B.sy 1 1 ∧ ∀ a y y', pairH B (rhoH B a y) y' = pairH B y (rhoH B (star a) y') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.rhoH_hom_adjoint | exact GlobalTheory.CompanionTheory.Ar.Conj.rhoH_hom_adjoint | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.rhoH_hom_adjoint <;> assumption)
end

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem _root_.GlobalTheory.T.formal_isomorphism_transport : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (B₂ : FB R d O) (φ ψ : Pt R 1 d) (lam : PS R 2 d), IsIso B B₂ φ ψ lam → lin φ 1 * lin ψ 1 = 1 ∧ lin ψ 1 * lin φ 1 = 1 ∧ Function.Bijective (transH φ ψ lam) ∧ (∀ a, rho B a * lin φ 1 = lin φ 1 * rho B₂ a) ∧ (∀ a, rhoH B a ∘ₗ transH φ ψ lam = transH φ ψ lam ∘ₗ rhoH B₂ a) ∧ ∀ y y', pairH B (transH φ ψ lam y) (transH φ ψ lam y') = pairH B₂ y y' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.Iso.rho_pairing | exact GlobalTheory.CompanionTheory.Ar.Conj.Iso.rho_pairing | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.Iso.rho_pairing <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem subDeg_dotDual_orth : ∀ (K : Type) [Field K] (C : ACurve K) (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)) (W X : Submodule K (Fin d → K)), IsBun C L → (∀ u, u ∈ W ↔ ∀ φ ∈ X, u ⬝ᵥ φ = 0) → subDeg C (dotDual C L) X = deg C (dotDual C L) + subDeg C L W :=
  PositivityTheory.HtPt.Ch.subdeg_orth

end GlobalTheory.CompanionTheory.Ar.Crv
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.CompanionTheory.Relay.tensor_product_tight_hopf_orders : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N₁ : Type) [AddCommGroup N₁] [Fintype N₁] [DecidableEq N₁], ∀ (N₂ : Type) [AddCommGroup N₂] [Fintype N₂] [DecidableEq N₂], ∀ (A₁ : HopfOrder (C := C) R N₁) (A₂ : HopfOrder (C := C) R N₂), (∀ x : N₁, p • x = 0) → (∀ x : N₂, p • x = 0) → IsTight v p A₁.carrier → IsTight v p A₂.carrier → IsTight v p (tens A₁.carrier A₂.carrier) := by
  intro p _ C _ _ _ v R _ _ hv hp N₁ _ _ _ N₂ _ _ _ A₁ A₂ _ _ h1 h2
  unfold IsTight at h1 h2 ⊢
  obtain ⟨a1, c1, o1, hA1, hC1, hO1, e1, f1⟩ := h1
  obtain ⟨a2, c2, o2, hA2, hC2, hO2, e2, f2⟩ := h2
  obtain ⟨AA, hAA, hl, hr, s1, s2, hcol⟩ := PositivityTheory.HtPt.Re.tens_hopf p C v R hv hp N₁ N₂ A₁ A₂
  rw [← hAA]
  have st1 : ∀ g ∈ AA.carrier, (fun x : N₁ × N₂ =>
      g ((AddMonoidHom.inl N₁ N₂) ((AddMonoidHom.fst N₁ N₂) x))) ∈ AA.carrier := by
    intro g hg
    simpa using s1 g hg
  have st2 : ∀ g ∈ AA.carrier, (fun x : N₁ × N₂ =>
      g ((AddMonoidHom.inr N₁ N₂) ((AddMonoidHom.snd N₁ N₂) x))) ∈ AA.carrier := by
    intro g hg
    simpa using s2 g hg
  have hAF := PositivityTheory.HtPt.Re.ret_af p C v R hv hp (N₁ × N₂) AA N₁ N₂ (AddMonoidHom.inl N₁ N₂)
    (AddMonoidHom.fst N₁ N₂) (AddMonoidHom.inr N₁ N₂) (AddMonoidHom.snd N₁ N₂)
    (fun y => by simp) (fun y => by simp) (fun x => by simp) (fun y => by simp) (fun y => by simp)
    st1 st2 a1 a2 (by rw [hl]; exact hA1) (by rw [hr]; exact hA2)
  have hOm := PositivityTheory.HtPt.Re.ret_om hv AA (AddMonoidHom.inl N₁ N₂)
    (AddMonoidHom.fst N₁ N₂) (AddMonoidHom.inr N₁ N₂) (AddMonoidHom.snd N₁ N₂)
    (fun y => by simp) (fun y => by simp) (fun x => by simp) (fun y => by simp) (fun y => by simp)
    st1 st2 o1 o2 (by rw [hl]; exact hO1) (by rw [hr]; exact hO2)
  refine ⟨a1 * a2, c1 ^ Fintype.card N₂ * c2 ^ Fintype.card N₁, o1 * o2, hAF, hcol c1 c2 hC1 hC2, hOm, ?_, ?_⟩
  · rw [Fintype.card_prod, mul_pow]
    have k1 : a1 ^ (Fintype.card N₁ * Fintype.card N₂ * (p - 1)) =
        (a1 ^ (Fintype.card N₁ * (p - 1))) ^ Fintype.card N₂ := by
      rw [← pow_mul]
      congr 1
      ring
    have k2 : a2 ^ (Fintype.card N₁ * Fintype.card N₂ * (p - 1)) =
        (a2 ^ (Fintype.card N₂ * (p - 1))) ^ Fintype.card N₁ := by
      rw [← pow_mul]
      congr 1
      ring
    rw [k1, k2, e1, e2]
    ring
  · rw [Fintype.card_prod, mul_pow]
    have k1 : o1 ^ (Fintype.card N₁ * Fintype.card N₂) = (o1 ^ Fintype.card N₁) ^ Fintype.card N₂ :=
      pow_mul _ _ _
    have k2 : o2 ^ (Fintype.card N₁ * Fintype.card N₂) = (o2 ^ Fintype.card N₂) ^ Fintype.card N₁ := by
      rw [← pow_mul, _root_.mul_comm (Fintype.card N₂)]
    rw [k1, k2, f1, f2]
    ring
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

theorem _root_.GlobalTheory.CompanionTheory.Relay.hopf_order_retract_elementary : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → ∀ AA : HopfOrder (C := C) R N, ∀ (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'], ∀ (ι : N' →+ N) (π : N →+ N'), (∀ y, π (ι y) = y) → (∀ g ∈ AA.carrier, (fun x => g (ι (π x))) ∈ AA.carrier) → IsTight v p AA.carrier → IsTight v p (AA.carrier.map (LinearMap.funLeft R C (ι : N' → N))) := by
  first | exact @PositivityTheory.HtPt.Re.ret_tight | exact PositivityTheory.HtPt.Re.ret_tight
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

theorem _root_.GlobalTheory.T.stable_hopf_order_fundamental_ideal : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ σ : MulChar F R, IsFund p σ → (∀ χ : MulChar F R, ∃ r : NNReal, r ≠ 0 ∧ HasLen v R (OmType AA.carrier χ) r) ∧ ∀ r : ℕ → NNReal, (∀ m ∈ Finset.Icc 1 (p ^ f - 1), HasLen v R (OmType AA.carrier (σ ^ m)) (r m)) → HasLen v R (OmAA AA.carrier) (∏ m ∈ Finset.Icc 1 (p ^ f - 1), r m) :=
  @_root_.PositivityTheory.HtPt.Rc.om_split
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.sesq_unimodular_dual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), (∀ y, (∀ x, sesq D x y = 0) → y = 0) ∧ ∀ f : D.La →ₗ[𝓞 E] E, (∀ δ ∈ differentIdeal ℤ (𝓞 E), ∀ x, ∃ b : 𝓞 E, (δ : E) * f x = b) → ∃ y, ∀ x, f x = sesq D x y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.unimodularity_sesq | exact GlobalTheory.CompanionTheory.Ar.Fl.unimodularity_sesq | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.unimodularity_sesq <;> assumption)
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

theorem _root_.GlobalTheory.T.cm_field_small_integral_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ a : Fin (Module.finrank ℚ E) → 𝓞 E, LinearIndependent ℚ (fun i => (a i : E)) ∧ ∀ i (σ : E →+* ℂ), ‖σ (a i)‖ ≤ Module.finrank ℚ E * hostRd E := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.exists_full_family_conjugates_le | exact GlobalTheory.CompanionTheory.Ar.Cusp.exists_full_family_conjugates_le | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.exists_full_family_conjugates_le <;> assumption)
end

section

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem rootOnFund_mul_fundOnRoot_inverse : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (r r' : Ψ × Fin N), (∑ a, rootOnFund r a * fundOnRoot a r' = if r = r' then 1 else 0) ∧ (∀ π : Ψ ≃ Ψ, rootOnFund (π r.1, r.2) (π r'.1, r'.2) = rootOnFund r r' ∧ fundOnRoot (π r.1, r.2) (π r'.1, r'.2) = fundOnRoot r r') :=
  @PositivityTheory.UnitarySelfGeneration.h_fundinv

end GlobalTheory.CompanionTheory.Ar.Cmp
end

section

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal


theorem _root_.GlobalTheory.CompanionTheory.Relay.ball_average_fibre_count : ∀ (n e : ℕ) (S : Set (EuclideanSpace ℂ (Fin n))), IsScaleStable S → IsSigmaCompact S →
  ∀ T : ℝ≥0∞ → ℝ≥0∞, Measurable T →
    ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π *
        ∫⁻ w in (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1), T (cntOver S π w) =
      volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) *
        ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π * T (cntOver S π (firstCoordVec (e + 1))) := by
  first | exact @PositivityTheory.Xgn.t_xgz_chow_mahler_e0reduce | exact PositivityTheory.Xgn.t_xgz_chow_mahler_e0reduce
end

section

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal


theorem _root_.GlobalTheory.CompanionTheory.Relay.chow_form_fibre_specialization : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (g : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (π : Fin (e + 1) → Fin n → ℂ) (u₀ : Fin n → ℂ),
  IsProjPrime W → IsChowForm W (e + 1) g → IsMultiHomog δ g →
  (fibrePts (coneSet h W) π).encard = δ →
  eval (consGroup u₀ (nrmGroups h e (coefRows h π))) g ≠ 0 →
    ∃ c : ℂ, c ≠ 0 ∧ ∀ u : Fin n → ℂ, eval (consGroup u (nrmGroups h e (coefRows h π))) g =
      c * ∏ᶠ y ∈ fibrePts (coneSet h W) π, ∑ j, u j * h.pointOf y j := by
  first | exact @PositivityTheory.Xgn.t_xgz_chow_mahler_fibrefactor | exact PositivityTheory.Xgn.t_xgz_chow_mahler_fibrefactor
end

section

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

theorem _root_.GlobalTheory.T.chart_sequence_holds : ChartSequence :=
  @_root_.PositivityTheory.HtPt.Ge.chart_sequence
end
