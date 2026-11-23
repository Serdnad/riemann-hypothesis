module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SplitHermitianGeneratorsExist
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle003
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle054
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle012
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle031
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle015
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle053
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle044
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XSBlowupfibre
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle038
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle022
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XPluckerFrame
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwistedDualGensExist
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
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle002

@[expose] public section

section

open NumberField GlobalTheory.CompanionTheory.Ar.Crv

theorem _root_.GlobalTheory.T.split_hermitian_generators_exist : ∀ (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (d r : ℕ) (D : ConjData C p (𝓞 E) d) (χ : 𝓞 E →+* K), (∀ a : 𝓞 E, ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom K)).Splits) → (∀ i, ∃ x : Fin r → (Fin d → K) × (Fin d → K), LinearIndependent K (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => D.ρH (RingOfIntegers.basis E q.2) (x q.1)) ∧ ∀ y, y ∈ D.H i ↔ ∃ c : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) → K, (∀ q, C.v i (c q) ≤ 1) ∧ y = ∑ q, c q • D.ρH (RingOfIntegers.basis E q.2) (x q.1)) → deg C (quot C D.H (⨆ a : 𝓞 E, LinearMap.range (D.ρH a - χ a • LinearMap.id))) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.deg_quot_eq_zero | exact GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.deg_quot_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.deg_quot_eq_zero <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar.Crv

theorem _root_.GlobalTheory.T.dot_dual_sub_degree_annihilator : ∀ (K : Type) [Field K] (C : ACurve K) (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)) (W X : Submodule K (Fin d → K)), IsBun C L → (∀ u, u ∈ W ↔ ∀ φ ∈ X, u ⬝ᵥ φ = 0) → subDeg C (dotDual C L) X = deg C (dotDual C L) + subDeg C L W := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.subDeg_dotDual_orth | exact GlobalTheory.CompanionTheory.Ar.Crv.subDeg_dotDual_orth | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.subDeg_dotDual_orth <;> assumption)
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.tensor_product_tight_hopf_orders : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N₁ : Type) [AddCommGroup N₁] [Fintype N₁] [DecidableEq N₁], ∀ (N₂ : Type) [AddCommGroup N₂] [Fintype N₂] [DecidableEq N₂], ∀ (A₁ : HopfOrder (C := C) R N₁) (A₂ : HopfOrder (C := C) R N₂), (∀ x : N₁, p • x = 0) → (∀ x : N₂, p • x = 0) → IsTight v p A₁.carrier → IsTight v p A₂.carrier → IsTight v p (tens A₁.carrier A₂.carrier) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.tensor_product_tight_hopf_orders | exact GlobalTheory.CompanionTheory.Relay.tensor_product_tight_hopf_orders | (intros; apply GlobalTheory.CompanionTheory.Relay.tensor_product_tight_hopf_orders <;> assumption)
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

theorem _root_.GlobalTheory.T.hopf_order_retract_elementary : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → ∀ AA : HopfOrder (C := C) R N, ∀ (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'], ∀ (ι : N' →+ N) (π : N →+ N'), (∀ y, π (ι y) = y) → (∀ g ∈ AA.carrier, (fun x => g (ι (π x))) ∈ AA.carrier) → IsTight v p AA.carrier → IsTight v p (AA.carrier.map (LinearMap.funLeft R C (ι : N' → N))) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.hopf_order_retract_elementary | exact GlobalTheory.CompanionTheory.Relay.hopf_order_retract_elementary | (intros; apply GlobalTheory.CompanionTheory.Relay.hopf_order_retract_elementary <;> assumption)
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

theorem _root_.GlobalTheory.T.stable_hopf_order_subgroup_characters : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (χ : MulChar F R) (a b c : NNReal), HasLen v R (OmType (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : K → N))) χ) a → HasLen v R (OmType (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))) χ) b → HasLen v R (OmType AA.carrier χ) c → a * b ≤ c := by
  first | exact @GlobalTheory.CompanionTheory.Relay.stable_hopf_order_subgroup_characters | exact GlobalTheory.CompanionTheory.Relay.stable_hopf_order_subgroup_characters | (intros; apply GlobalTheory.CompanionTheory.Relay.stable_hopf_order_subgroup_characters <;> assumption)
end

section

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

theorem _root_.GlobalTheory.T.root_fundamental_weight_duality : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (r r' : Ψ × Fin N), (∑ a, rootOnFund r a * fundOnRoot a r' = if r = r' then 1 else 0) ∧ (∀ π : Ψ ≃ Ψ, rootOnFund (π r.1, r.2) (π r'.1, r'.2) = rootOnFund r r' ∧ fundOnRoot (π r.1, r.2) (π r'.1, r'.2) = fundOnRoot r r') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.rootOnFund_mul_fundOnRoot_inverse | exact GlobalTheory.CompanionTheory.Ar.Cmp.rootOnFund_mul_fundOnRoot_inverse | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.rootOnFund_mul_fundOnRoot_inverse <;> assumption)
end

section

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal


theorem _root_.GlobalTheory.T.ball_average_fibre_count : ∀ (n e : ℕ) (S : Set (EuclideanSpace ℂ (Fin n))), IsScaleStable S → IsSigmaCompact S →
  ∀ T : ℝ≥0∞ → ℝ≥0∞, Measurable T →
    ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π *
        ∫⁻ w in (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1), T (cntOver S π w) =
      volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) *
        ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π * T (cntOver S π (firstCoordVec (e + 1))) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.ball_average_fibre_count | exact GlobalTheory.CompanionTheory.Relay.ball_average_fibre_count | (intros; apply GlobalTheory.CompanionTheory.Relay.ball_average_fibre_count <;> assumption)
end

section

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal


theorem _root_.GlobalTheory.T.chow_form_fibre_specialization : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (g : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (π : Fin (e + 1) → Fin n → ℂ) (u₀ : Fin n → ℂ),
  IsProjPrime W → IsChowForm W (e + 1) g → IsMultiHomog δ g →
  (fibrePts (coneSet h W) π).encard = δ →
  eval (consGroup u₀ (nrmGroups h e (coefRows h π))) g ≠ 0 →
    ∃ c : ℂ, c ≠ 0 ∧ ∀ u : Fin n → ℂ, eval (consGroup u (nrmGroups h e (coefRows h π))) g =
      c * ∏ᶠ y ∈ fibrePts (coneSet h W) π, ∑ j, u j * h.pointOf y j := by
  first | exact @GlobalTheory.CompanionTheory.Relay.chow_form_fibre_specialization | exact GlobalTheory.CompanionTheory.Relay.chow_form_fibre_specialization | (intros; apply GlobalTheory.CompanionTheory.Relay.chow_form_fibre_specialization <;> assumption)
end

section

namespace GlobalTheory.CompanionTheory.CommAlg.BlowUpFibre

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpFibreSemilocal.Statement.{0} :=
  PositivityTheory.Xgn.t_s_blowupfibre

end GlobalTheory.CompanionTheory.CommAlg.BlowUpFibre
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.CommonFlag

theorem exists_basis_mem {O Ω τ V : Type} [CommRing O] [Field Ω] [Algebra O Ω] [AddCommGroup V]
    [Module Ω V] {N : ℕ} {y : τ → Ω} (B : ChartBundle O y N V) {c : τ} (hc : y c ≠ 0) :
    ∃ w : Module.Basis (Fin N) Ω V, ∀ i, w i ∈ B.lat c := by
  classical
  obtain ⟨k, f, cc, hf, hcc, hsum, hb⟩ := B.frame c hc
  obtain ⟨l, hl⟩ : ∃ l, f l ≠ 0 := by
    by_contra h
    push Not at h
    simp [h] at hsum
  obtain ⟨b, hli, hsp, hiff⟩ := hb l
  have hbl : ∀ q, ∃ n : ℕ, f l ^ n • b q ∈ B.lat c := fun q =>
    (hiff (b q)).2 ⟨Pi.single q 1, fun q' => ⟨0, by by_cases h : q' = q <;> simp [h]⟩,
      by simp [Pi.single_apply]⟩
  choose n hn using hbl
  refine ⟨(Module.Basis.mk hli hsp.ge).unitsSMul fun q => Units.mk0 (f l ^ n q) (pow_ne_zero _ hl),
    fun q => ?_⟩
  rw [Module.Basis.unitsSMul_apply, Module.Basis.mk_apply]
  exact hn q

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ (N n : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E : Fin (n + 1) → ChartBundle O (mseg x) N V), (∀ j, SameGeneric O x (E 0) (E j)) → ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (z : (Σ k, ι' k) → Ω) (EB : Fin (n + 1) → ChartBundle O (mseg (joinCoord x z)) N V) (w : Module.Basis (Fin N) Ω V) (b : Fin (n + 1) → Fin N → K ⊕ K' → ℤ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d ∧ fnField O (joinCoord x z) = fnField O x ∧ ∀ j, IsPull O x z (E j) (EB j) ∧ IsFlagFrame (joinCoord x z) (EB j) w (b j) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d hx N n V _ _ E hE
  obtain ⟨hK, hx0, hinj, hT⟩ := (PositivityTheory.Xgn.A_join_model.isModelOver_iff x d).1 hx
  choose s₀ hs₀ using hx0
  have hs : mseg x s₀ ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hs₀ k
  obtain ⟨w, hw⟩ := exists_basis_mem (E 0) hs
  have hgen : ∀ j, ∃ (a : K → ℤ) (M : ℕ) (φ : Fin M → Module.Dual Ω V),
      IsTwistedDualGens x (E j) a φ := fun j => by
    obtain ⟨a, ha⟩ := TwistedDualGensExist.proof O Ω K ι x N V (E j)
    exact ⟨a, ha a le_rfl⟩
  choose a M φ hφ using hgen
  obtain ⟨hz, hfn⟩ := GlobalTheory.CompanionTheory.Ar.Num.plucker_birat O Ω K ι x N V (Fin (n + 1)) E M a φ hφ w s₀ hs
  have hfn' := hfn fun j i => by
    obtain ⟨c, hc, hcw⟩ := (hE j s₀ hs).1 (w i) (hw i)
    exact ⟨c, (map_ne_zero_iff _ hinj).2 hc, hcw⟩
  have hpull : ∀ j, ∃ EB : ChartBundle O (mseg (joinCoord x (pluckerCoord φ w))) N V,
      IsPull O x (pluckerCoord φ w) (E j) EB := fun j =>
    (GlobalTheory.CompanionTheory.Ar.Num.PullExists.main O Ω K ι x N V (E j)).1 _ _ (pluckerCoord φ w)
  choose EB hEB using hpull
  refine ⟨Fin (n + 1) × Fin (N + 1), inferInstance, inferInstance, pluckerIdx N M, inferInstance,
    pluckerCoord φ w, EB, w, fun j => pluckerDeg (a j) j, ?_, hfn', fun j => ⟨hEB j,
      PositivityTheory.Xgn.t_plucker_frame O Ω K ι x N V (Fin (n + 1)) E M a φ hφ w j (EB j) (hEB j)⟩⟩
  refine (PositivityTheory.Xgn.A_join_model.isModelOver_iff _ d).2 ⟨inferInstance, ?_, hinj, ?_⟩
  · rintro (k | k)
    · exact ⟨s₀ k, hs₀ k⟩
    · exact hz k
  · rw [hfn', hT]

end GlobalTheory.CompanionTheory.Ar.CommonFlag
end
