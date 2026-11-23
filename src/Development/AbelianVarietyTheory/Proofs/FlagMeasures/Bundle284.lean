module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmallFundamentalSetRealUnipotent
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeEqAmpJAndBesselEqDoubleIntegral
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFunctionalTwoSided
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle278
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableBesselCoefficientSmulEquivariant
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle016
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle005
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle279
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle231
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle200
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle001
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle148
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle280
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle281
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle104
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle176
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle131
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff

@[expose] public section

section

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.small_fundamental_set_real_unipotent : ∀ (I : AutInst) (x : I.GA) (g : ℕ) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (lo hi rho : ℝ), 1 ≤ g → IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) R → R ≠ ⊥ → R ≤ perpIn I x R → 0 < hi → largestSize (bas I) (frm I x) R ≤ hi → (∀ N, R < N → N ≤ lamX I x → lo ≤ sizeQ (bas I) (frm I x) N R) → hi ≤ rho * lo → hi ^ 2 ≤ rho / 4 → ∀ ν : I.Ginf, ((ν, 1) : I.GA) ∈ I.NA (Submodule.span I.E (R : Set (Fin I.n → I.E))) → ∃ γ ∈ I.GFset ∩ I.NA (Submodule.span I.E (R : Set (Fin I.n → I.E))), (x⁻¹ * γ * x).2 ∈ I.Kg g ∧ ∃ A Z : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ, (∀ v, inG (I.ε v) (A v) ∧ inG (I.ε v) (Z v)) ∧ (∀ v, uMat (ν v) * uMat (x.1 v) = uMat (γ.1 v) * uMat (x.1 v) * NormedSpace.exp (A v) * NormedSpace.exp (Z v)) ∧ Real.sqrt (∑ v, hs (A v)) + Real.sqrt (∑ v, hs (Z v)) ≤ (I.n : ℝ) ^ 2 * Real.sqrt I.f * g * I.rd * rho / 4 ∧ ∀ s t : ℝ, ∃ m : I.Ginf, ((m, 1) : I.GA) ∈ I.NA (Submodule.span I.E (R : Set (Fin I.n → I.E))) ∧ ∀ v, uMat (m v) * uMat (x.1 v) = uMat (x.1 v) * NormedSpace.exp ((s : ℂ) • A v) * NormedSpace.exp ((t : ℂ) • Z v) := by
  first | exact @GlobalTheory.SmallFund.small_fundamental_set | exact GlobalTheory.SmallFund.small_fundamental_set | (intros; apply GlobalTheory.SmallFund.small_fundamental_set <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.amplitude_eq_ampJ_and_bessel_eq_doubleIntegral : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] , (∀ (μG : Measure (Mt k r)) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq), IsHaarOn (GG k r) μG → ∀ γ ∈ GG k r, OO μG Φ Φ' γ = ampJ μG 1 Φ Φ' γ) ∧ ∀ (σ : Mat k r → (H →L[ℂ] H)) (z z' : Fin (2 * r + k + 1) → ℂ) (c₀ : ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (π' : Mat k r → (Wq →L[ℂ] Wq)) (μW μW' μN : Measure (Mt k r)) (x y : H) (ξ : Wp) (ξ' : Wq), inWb k r z → 0 < Tz k r z → inWb k r z' → 0 < Tz k r z' → IsURepOn (GG k r) σ → IsURepOn (UWset k r z) π → IsURepOn (UWset k r z') π' → IsHaarOn (UWset k r z) μW → IsHaarOn (UWset k r z') μW' → IsHaarOn (Nset k r) μN → ∀ γ ∈ GG k r, besselJ k r z z' c₀ π π' μW μN μW' (fun g => coef σ x y g • rk1 ξ ξ') γ = Iint (psi k r z c₀) (psi k r z' c₀) π π' ((μW.prod μN).map fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2) ((μW'.prod μN).map fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2) σ x y ξ ξ' γ := by
  first | exact @GlobalTheory.SgInf.AmpJ.oo_eq_ampJ_and_besselJ_eq_Iint | exact GlobalTheory.SgInf.AmpJ.oo_eq_ampJ_and_besselJ_eq_Iint | (intros; apply GlobalTheory.SgInf.AmpJ.oo_eq_ampJ_and_besselJ_eq_Iint <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.bessel_functional_two_sided : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) (z' : Fin (2 * r + k + 1) → ℂ) (c' : Fin r → ℂ) (π' : Mat k r → (Wq →L[ℂ] Wq)) (μS' : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → Side z' π' μS' → ∀ (x y : H) (ξ : Wp) (ξ' : Wq) (Om Om' : Set (Mt k r)), MeasurableSet Om → MeasurableSet Om' → μS Om < ⊤ → μS' Om' < ⊤ → Integrable (fun p : Mt k r => coef σ y y (Matrix.of p)) μS → Integrable (fun p : Mt k r => coef σ x x (Matrix.of p)) μS' → ContinuousOn (Iint (psiGen k r z c) (psiGen k r z' c') π π' (μS.restrict Om) (μS'.restrict Om') σ x y ξ ξ') (GG k r) ∧ Integrable (fun g : Mt k r => hsNormSq (Iint (psiGen k r z c) (psiGen k r z' c') π π' (μS.restrict Om) (μS'.restrict Om') σ x y ξ ξ' (Matrix.of g))) μG ∧ ((∫ g, hsNormSq (Iint (psiGen k r z c) (psiGen k r z' c') π π' (μS.restrict Om) (μS'.restrict Om') σ x y ξ ξ' (Matrix.of g)) ∂μG : ℝ) : ℂ) = (d : ℂ)⁻¹ * (∫ p, ((μS {s | s ∈ Om ∧ lmulM (Matrix.of p) s ∈ Om}).toReal : ℂ) * (coef σ y y (Matrix.of p) * ⟪ξ, PiS (psiGen k r z c) π (Matrix.of p)⁻¹ ξ⟫_ℂ) ∂μS) * (∫ p, ((μS' {s | s ∈ Om' ∧ lmulM (Matrix.of p) s ∈ Om'}).toReal : ℂ) * (coef σ x x (Matrix.of p) * ⟪ξ', PiS (psiGen k r z' c') π' (Matrix.of p)⁻¹ ξ'⟫_ℂ) ∂μS') := by
  first | exact @GlobalTheory.SgInf.TruncNorm.truncated_norm_sq | exact GlobalTheory.SgInf.TruncNorm.truncated_norm_sq | (intros; apply GlobalTheory.SgInf.TruncNorm.truncated_norm_sq <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.smooth_functional_orbit_smoothVector : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] (σ : Mat k r → (H →L[ℂ] H)) (Λ : H →L[ℂ] B), IsURepOn (GG k r) σ → ∀ v : H, IsSmoothVec (k := k) (r := r) σ v → SmoothOnH (Hpk k r) (fun g : Mat k r => Λ (σ g v)) ∧ ∀ ws : List (Mat k r), (∀ X ∈ ws, InLieHpk k r X) → ∀ x ∈ GG k r, rdWord ws (fun g : Mat k r => Λ (σ g v)) x = Λ (σ x (dsigW σ ws v)) := by
  first | exact @GlobalTheory.SgInfOrb.smooth_rdWord_functional | exact GlobalTheory.SgInfOrb.smooth_rdWord_functional | (intros; apply GlobalTheory.SgInfOrb.smooth_rdWord_functional <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.Iint_equivariant_alt : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) (z' : Fin (2 * r + k + 1) → ℂ) (c' : Fin r → ℂ) (π' : Mat k r → (Wq →L[ℂ] Wq)) (μS' : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → Side z' π' μS' → ∀ (x y : H) (ξ : Wp) (ξ' : Wq) (Om Om' : Set (Mt k r)), MeasurableSet Om → MeasurableSet Om' → ∀ γ ∈ GG k r, ∀ t ∈ Sset k r z, ∀ t' ∈ Sset k r z', Iint (psiGen k r z c) (psiGen k r z' c') π π' (μS.restrict Om) (μS'.restrict Om') σ x y ξ ξ' (t * γ * t'⁻¹) = (PiS (psiGen k r z c) π t).comp ((Iint (psiGen k r z c) (psiGen k r z' c') π π' (μS.restrict (rmulM t '' Om)) (μS'.restrict (rmulM t' '' Om')) σ x y ξ ξ' γ).comp (PiS (psiGen k r z' c') π' t'⁻¹)) := by
  first | exact @GlobalTheory.SgInf.Equivar.Iint_equivariant | exact GlobalTheory.SgInf.Equivar.Iint_equivariant | (intros; apply GlobalTheory.SgInf.Equivar.Iint_equivariant <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.hcTypeW_irreducible_and_schur_average : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mat k r → (Wp →L[ℂ] Wp)), inWb k r z → 0 < Tz k r z → (∀ u, IsHCTypeW k r z u π → Nontrivial Wp ∧ IsURepOn (UWset k r z) π ∧ IsIrredOn (UWset k r z) π) ∧ ∀ μW : Measure (Mt k r), IsURepOn (UWset k r z) π → IsIrredOn (UWset k r z) π → IsHaarOn (UWset k r z) μW → μW Set.univ = 1 → ∀ w ξ : Wp, ∫⁻ h, (‖⟪w, π (Matrix.of h) ξ⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 ∂μW = ENNReal.ofReal (‖w‖ ^ 2 * ‖ξ‖ ^ 2 / Module.finrank ℂ Wp) := by
  first | exact @GlobalTheory.Amp.Schur.type_irred_and_avg | exact GlobalTheory.Amp.Schur.type_irred_and_avg | (intros; apply GlobalTheory.Amp.Schur.type_irred_and_avg <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.integrable_besselCoefficient_smul_equivariant : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ ν : Measure (Mt k r), IsQuotMeas μG μS ν → ∀ W : Mat k r → Wp, AEStronglyMeasurable (fun x : Mt k r => W (Matrix.of x)) μG → AEStronglyMeasurable (fun x : Mt k r => W (Matrix.of x)) ν → IsSPsiEquiv z (psiGen k r z c) π W → l2SG ν W < ⊤ → ∀ y ∈ GG k r, Integrable (fun g : Mt k r => star (coef σ w w (y⁻¹ * Matrix.of g)) • W (Matrix.of g)) μG := by
  first | exact @GlobalTheory.SgInf.AbsConv.integrable_coef_smul | exact GlobalTheory.SgInf.AbsConv.integrable_coef_smul | (intros; apply GlobalTheory.SgInf.AbsConv.integrable_coef_smul <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitian_lattice_datum_equivariant_flag_isometries : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∀ d Λ, S.IsTerm d Λ → d = S.datOf Λ) ∧ (∀ h ∈ S.H0, ∀ Λ, S.datOf (h • Λ) = h • S.datOf Λ) ∧ (∀ n ∈ S.N, ∀ Λ, (S.datOf (n • Λ)).1 = (S.datOf Λ).1) ∧ (∀ n ∈ S.N', ∀ Λ, (S.datOf (n • Λ)).2.1 = (S.datOf Λ).2.1) ∧ ∀ φ ∈ isomG L S.Hm, (∀ b : Fin (r + 1), φ (S.f b) - S.f b ∈ S.spanTo S.f b) → (∀ b : Fin (r + 1), φ (S.f' b) - S.f' b ∈ S.spanTo S.f' b) → ∃ s ∈ S.St, ∃ h ∈ S.H0, φ = s * h := by
  first | exact @GlobalTheory.HL.DatumOf.main | exact GlobalTheory.HL.DatumOf.main | (intros; apply GlobalTheory.HL.DatumOf.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

noncomputable section

namespace GlobalTheory.DegStepG

theorem vandLine (hH : GlobalTheory.GapIn.Hyp) (Cn m₀ : ℝ)
    (hnear : ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), GlobalTheory.Amp.HypZ D large₂ C' Cl Cg cb Cu cT CT C0 →
      1000 ≤ Cl → m₀ ≤ D.R.m → ∀ (τ : D.what₂.Tau) (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ),
        l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 + D.R.r →
        Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) lam' ((D.R.r : ℝ) ^ 19 / 2) ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS ((D.R.r : ℝ) ^ 19 / 2))
    (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 C1 : ℝ) (hCl : 1000 ≤ Cl) (hm : m₀ ≤ D.R.m) :
    Formalism.MainNotions.BridgeLemma₂.deg_VandLine D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 := by
  intro hH0 τ w w' _ θ _ W _ lam' hl A hA I s hs A' hA'
  have hZ : GlobalTheory.Amp.HypZ D large₂ C' Cl Cg cb Cu cT CT C0 := hH0
  have hcard : (I.card : ℝ) ≤ D.R.r := by
    rw [← Formalism.MainNotions.BridgeLemma₂.deg_cast_r]
    have : I.card ≤ 2 * D.R.rS + D.R.k + 1 := by
      have := Finset.card_le_univ I
      rwa [Fintype.card_fin] at this
    exact_mod_cast this
  have hr0 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
  have h1 : l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 + D.R.r := by linarith
  have h2 : l1dist (lam' + s • epsI I) (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 + D.R.r :=
    le_trans (Formalism.MainNotions.BridgeLemma.l1_distance_sign_step _ _ s hs I) (by linarith)
  obtain ⟨g1, gok⟩ := hnear D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl hm τ lam' h1
  obtain ⟨g2, _⟩ := hnear D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl hm τ _ h2
  exact GlobalTheory.T.formalDegree_ratio_eq_harishChandra_ratio_largeGap hH D W lam' (lam' + s • epsI I) A A' _ hA hA' g1 g2 gok

theorem degI_along_family : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS →
    ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ C thr : ℝ, 0 ≤ C ∧ ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm →
      PX.RanksF Fm C0 Cg cb Cu cT CT → ∀ Cn : ℝ,
        OwnEv Fm fun C' Cl x i => Formalism.MainNotions.BridgeLemma.DegreeRatioUnitShiftBound (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C := by
  intro _ hH _ Cg cb Cu cT CT C0 C1
  refine ⟨1, 1000, zero_le_one, fun eps Fm _ hCl _ Cn => ?_⟩
  obtain ⟨m₀, hnear⟩ := GlobalTheory.T.gap_near_placeParameter_half_noncompactGap Cn
  obtain ⟨x0, hx0⟩ := GlobalTheory.family_sizes_eventually_large eps Fm m₀
  refine ⟨x0, fun x hx i => ?_⟩
  exact Formalism.MainNotions.BridgeLemma₂.degree_ratio_one_of_vandermonde _ _ _ _ _ _ _ _ _ _ _ _
    (vandLine hH Cn m₀ hnear (Fm.D x i) (Fm.L x i) _ _ _ _ _ _ _ _ _ hCl (hx0 x hx i).2.1)

end GlobalTheory.DegStepG
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

theorem _root_.GlobalTheory.T.localisedIwasawaIntegral_smallBall_asymptotics : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ (dN dM dK dL : ℕ) (EN : Fin dN → Matrix (Fin n) (Fin n) ℂ) (EM : Fin dM → Matrix (Fin n) (Fin n) ℂ) (EK : Fin dK → Matrix (Fin n) (Fin n) ℂ) (EL : Fin dL → Matrix (Fin n) (Fin n) ℂ), IsCut ε (flagN ε W) EN → IsCut ε (flagM ε W) EM → IsCut ε (maxK ε) EK → IsON EL → (∀ v, gau EN EM EK EL v = 0 → v = 0) → volume {v | gau EN EM EK EL v ≤ 1} ≠ ⊤ → ∀ μN μM μK : Measure (Formalism.REAL.UJ ε), IsGaugeSub (flagN ε W) dN μN → IsGaugeSub (flagM ε W) dM μM → IsGaugeSub (maxK ε) dK μK → ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → Filter.Tendsto (fun r : ℝ => (∫⁻ u, ∫⁻ m, dlt j W m * ∫⁻ k, (hsBall ε r).indicator 1 (u * m * k) * (slab ε EL ρ r).indicator 1 k ∂μK ∂μM ∂μN) / ENNReal.ofReal (r ^ (dN + (dM + dK)))) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (volume {v | gau EN EM EK EL v ≤ 1})) := by
  first | exact @GlobalTheory.IwConst.localised_iwasawa_asymptotics | exact GlobalTheory.IwConst.localised_iwasawa_asymptotics | (intros; apply GlobalTheory.IwConst.localised_iwasawa_asymptotics <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.KernelContRep

theorem continuous_integral_kernel {X Z : Type} [TopologicalSpace X] [LocallyCompactSpace X]
    [FirstCountableTopology X] [TopologicalSpace Z] [T2Space Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    (ν : Measure Z) [IsFiniteMeasureOnCompacts ν] (K : X → Z → ℂ)
    (hK : Continuous fun p : X × Z => K p.1 p.2) (y : Z → ℂ) (hy : MemLp y 2 ν) (C : Set Z)
    (hC : IsCompact C) (h0 : ∀ᵐ z ∂ν, z ∉ C → y z = 0) :
    Continuous fun x => ∫ z, K x z * y z ∂ν := by
  have : IsFiniteMeasure (ν.restrict C) := ⟨by simpa using hC.measure_lt_top⟩
  have hi : Integrable y ν :=
    IntegrableOn.integrable_of_ae_notMem_eq_zero (s := C) ((hy.restrict C).integrable one_le_two) h0
  have hc : ∀ x, Continuous fun z => K x z := fun x => hK.comp (Continuous.prodMk_right x)
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  obtain ⟨U, hU, hx⟩ := exists_compact_mem_nhds x₀
  obtain ⟨M, hM⟩ := (hU.prod hC).exists_bound_of_continuousOn hK.continuousOn
  refine continuousAt_of_dominated (bound := fun z => M * ‖y z‖) ?_ ?_ (hi.norm.const_mul M) ?_
  · exact Filter.Eventually.of_forall fun x => (hc x).aestronglyMeasurable.mul hi.1
  · filter_upwards [hx] with x hxU
    filter_upwards [h0] with z hz
    by_cases hzC : z ∈ C
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hM (x, z) ⟨hxU, hzC⟩) (norm_nonneg _)
    · simp [hz hzC]
  · exact Filter.Eventually.of_forall fun z =>
      ((hK.comp (Continuous.prodMk_left z)).mul continuous_const).continuousAt

theorem ext_ae_eq_on_fund (B : RowsAut) (y : B.I.L2 B.μf B.fund) :
    B.I.ext y =ᵐ[(B.I.muA B.μf).restrict B.fund] (y : B.I.GA → ℂ) := by
  have h2 : ∀ᵐ z ∂(B.I.muA B.μf), ∀ γ ∈ B.I.GFset, γ ≠ 1 →
      γ * z ∉ (fun y => γ * y) '' B.fund ∩ B.fund := by
    refine (ae_ball_iff (GlobalTheory.RatDiscrete.countable_GFset B.I)).2 fun γ hγ => ?_
    by_cases h1 : γ = 1
    · exact Filter.Eventually.of_forall fun z h => absurd h1 h
    · filter_upwards [(GlobalTheory.AdelicUnfold.measurePreserving_left B.I B.μf γ).quasiMeasurePreserving.ae
        (measure_eq_zero_iff_ae_notMem.1 (B.fund_spec.2.2 γ hγ h1))] with z hz _
      exact hz
  filter_upwards [ae_restrict_of_ae h2, ae_restrict_mem B.fund_spec.1] with z hz hzf
  have h := B.fund_spec.2.1 z
  have e : B.I.rep B.fund z = h.choose * z := by
    unfold AutInst.rep; exact dif_pos h
  have e1 : h.choose = 1 := by
    by_contra hne
    exact hz _ h.choose_spec.1 hne ⟨⟨z, hzf, rfl⟩, h.choose_spec.2⟩
  show (y : B.I.GA → ℂ) (B.I.rep B.fund z) = _
  rw [e, e1, one_mul]

theorem isContRep_of_kernel (hA : KernelA) : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.I.n → LocDec B h → HBig B 32 h → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → ∀ (y : B.I.L2 B.μf B.fund) (C : Set B.I.GA), IsCompact C → (∀ᵐ z ∂((B.I.muA B.μf).restrict B.fund), z ∉ C → (y : B.I.GA → ℂ) z = 0) → IsContRep B (T y) (fun x => ∫ z in B.fund, kern B.I (phe B d) x z * (y : B.I.GA → ℂ) z ∂(B.I.muA B.μf)) := by
  intro B d h hd hn hl hb T hT y C hC h0
  obtain ⟨-, hK, hinv, -⟩ := hA B d h hd hn hl hb
  obtain ⟨hT2, hL, hS, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  have : BorelSpace B.I.GA := inferInstance
  have : IsFiniteMeasureOnCompacts (B.I.muA B.μf) := by
    unfold AutInst.muA; infer_instance
  refine ⟨?_, fun γ hγ x => ?_, ?_⟩
  · exact continuous_integral_kernel _ (kern B.I (phe B d)) hK _ (Lp.memLp y) C hC h0
  · simp only [(hinv γ hγ _ _).1]
  · obtain ⟨h1, h2⟩ := GlobalTheory.ConvKernel.rconv_eq_integral B _ T hT y
    have h3 := ((GlobalTheory.RightRegFund.rightReg_unitary_continuous B).2.2.2.2 y).1
    filter_upwards [h1, h2] with x hx1 hx2
    rw [hx2, (GlobalTheory.AdelicUnfold.integral_unfold_kernel B _ _ x h3 hx1).2]
    refine integral_congr_ae ?_
    filter_upwards [ext_ae_eq_on_fund B y] with z hz
    rw [hz]

theorem isContRep_integral_kernel : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.I.n → LocDec B h → HBig B 32 h → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → ∀ (y : B.I.L2 B.μf B.fund) (C : Set B.I.GA), IsCompact C → (∀ᵐ z ∂((B.I.muA B.μf).restrict B.fund), z ∉ C → (y : B.I.GA → ℂ) z = 0) → IsContRep B (T y) (fun x => ∫ z in B.fund, kern B.I (phe B d) x z * (y : B.I.GA → ℂ) z ∂(B.I.muA B.μf)) :=
  isContRep_of_kernel GlobalTheory.T.automorphicKernel_convergence_properties

end GlobalTheory.KernelContRep
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.EvalBound

theorem tens_mem_VP (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (hB : IsDSData B d) :
    B.tens B.w ∈ VP B 0 :=
  (tens_w_mem B hB 0).1

noncomputable def realRep (B : RowsAut) : B.I.Ginf →* (B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund) where
  toFun x := B.R (x, 1)
  map_one' := (GlobalTheory.RightRegFund.rightReg_unitary_continuous B).1
  map_mul' x y := by
    rw [← (GlobalTheory.RightRegFund.rightReg_unitary_continuous B).2.1, Prod.mk_mul_mk, mul_one]

theorem exists_contRep_bound : GlobalTheory.DSId.StrictLow → ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → 1 ≤ B.I.n → 1 ≤ B.g → ∃ C : ℝ, ∀ A ∈ B.I.HomS B.σs B.μf B.fund B.R, (∀ k ∈ B.I.Kg B.g, B.R (1, k) (A (B.tens B.w)) = A (B.tens B.w)) → ∃ f : B.I.GA → ℂ, IsContRep B (A (B.tens B.w)) f ∧ ∀ x, ‖f x‖ ≤ C * (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) * ‖A (B.tens B.w)‖ := by
  intro hSL B d hB hn hg
  obtain ⟨hU, -, -, hw1, -⟩ := GlobalTheory.Dec.tensorRep B d hB
  obtain ⟨F, hF, hFc, hFeq⟩ :=
    GlobalTheory.StepAverage.exists_smooth_average hSL B d hB 0 _ (tens_mem_VP B d hB)
  set a : B.I.Ginf → ℂ := fun g => F (fun v i j => uMat (g v) i j) with ha
  have hemb := GlobalTheory.StepAverage.isClosedEmbedding_entries_inf B.I
  have hac : Continuous a := hF.continuous.comp hemb.continuous
  have haS : HasCompactSupport a := hFc.comp_isClosedEmbedding hemb
  have hsm : SmoothInf B.I a := fun x =>
    ⟨F, hF.contDiffAt, Filter.Eventually.of_forall fun _ => rfl⟩
  have hvi : Integrable (fun g => a g • B.σs g (B.tens B.w)) (muInf B.I) := by
    by_contra hni
    have h0 : B.tens B.w = 0 := by rw [hFeq]; exact integral_undef hni
    rw [h0, norm_zero] at hw1
    exact zero_ne_one hw1
  have hai : Integrable a (muInf B.I) := by
    refine hvi.norm.mono' hac.aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
    rw [norm_smul, hU.2.2.1, hw1, mul_one]
  obtain ⟨C, hC⟩ := GlobalTheory.T.convolutionSmoothL2_of_def B B.g hn hg a hsm haS
  refine ⟨C, fun A hA hK => ?_⟩
  have hRU := GlobalTheory.RightRegFund.rightReg_unitary_continuous B
  obtain ⟨P, hP1, hP2⟩ := GlobalTheory.absOpInt B.I.Ginf (muInf B.I) (B.I.L2 B.μf B.fund) (realRep B)
    (fun g x => hRU.2.2.1 (g, 1) x)
    (fun x => (hRU.2.2.2.1 x).comp (continuous_id.prodMk continuous_const)) a hai
  have hA' : ∀ g, A.comp (B.σs g) = (B.R (g, 1)).comp A := hA
  have hPy : P (A (B.tens B.w)) = A (B.tens B.w) := by
    rw [hP1]
    symm
    calc A (B.tens B.w) = A (∫ g, a g • B.σs g (B.tens B.w) ∂(muInf B.I)) := congrArg A hFeq
      _ = ∫ g, A (a g • B.σs g (B.tens B.w)) ∂(muInf B.I) := (A.integral_comp_comm hvi).symm
      _ = ∫ g, a g • realRep B g (A (B.tens B.w)) ∂(muInf B.I) := by
        congr 1
        funext g
        rw [map_smul]
        congr 1
        exact congrArg (fun T => T (B.tens B.w)) (hA' g)
  obtain ⟨f, hsmg, hfc, hfb, hfae⟩ := hC (A (B.tens B.w)) hK P ⟨hai, fun x y => hP2 x y⟩
  refine ⟨f, ?_, hfb⟩
  rw [hPy] at hfae
  unfold IsSmoothMG at hsmg
  unfold IsContRep
  exact ⟨hfc, hsmg.1, hfae⟩

end GlobalTheory.EvalBound
end
