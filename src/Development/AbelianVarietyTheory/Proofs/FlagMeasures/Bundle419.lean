module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle017
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle401
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle382
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantLengthTwoSidedMomentsLargeGap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle203
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellDataSupport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaContOn
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.ZhatNormLinearBound
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle339
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle351
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle385
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle355
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle068
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle370
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle411
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle047
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle413
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle414
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle387
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle412
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle404
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle013
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf

@[expose] public section

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.InnerDict

theorem inner_of_term : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (r : ℕ) (P : LocNG.FPair H r) (d : LocNG.Datum P) (τ : Loc.Term V M r), LocNG.IsTermOver P d τ → (d.L : Set (H.Wb P.A.f)) = H.Lset τ.abelian₂ P.A.f ∧ (d.L' : Set (H.Wb P.B.f)) = H.Lset τ.abelian₂ P.B.f := GlobalTheory.T.nonGenericDatum_lattice_eq_perpQuotientImage_term

theorem lset_eq_of_lsub_eq : ∀ (D : D7) (Z : LocDat D) (p : PlF D) {T : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T) (Fr : LocNG.FrameD (locH Z p) D.R.rS), Fr.f = (fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ Λ₁ Λ₂ : LV D, Submodule.IsLattice D.host.E Λ₁ → Submodule.IsLattice D.host.E Λ₂ → Lsub Λ₁ G = Lsub Λ₂ G → (locH Z p).Lset (lattice₂ D Z.M p Λ₁) Fr.f = (locH Z p).Lset (lattice₂ D Z.M p Λ₂) Fr.f := GlobalTheory.T.localInnerLattice_eq_of_innerPreimage_eq

theorem lsub_eq_of_lset_eq : ∀ (D : D7) (Z : LocDat D) {T : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T) (Fr : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (Fr p).f = (fun a => frFac Z.δ p a • baseChange₂ D p (frame G a))) → ∀ Λ₁ Λ₂ : LV D, Submodule.IsLattice D.host.E Λ₁ → Submodule.IsLattice D.host.E Λ₂ → (∀ p, (locH Z p).Lset (lattice₂ D Z.M p Λ₁) (Fr p).f = (locH Z p).Lset (lattice₂ D Z.M p Λ₂) (Fr p).f) → Lsub Λ₁ G = Lsub Λ₂ G := GlobalTheory.T.innerPreimage_eq_of_local_innerLattice_eq

theorem iota_eq_of_graph_eq : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ) (F : LFlag (D.sp.Y 0) D.R.rS (Tn : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (T'n : D.host.E)), Based Z FP Tn T'n F F' → ∀ Λ₁ Λ₂ : LV D, Submodule.IsLattice D.host.E Λ₁ → Submodule.IsLattice D.host.E Λ₂ → Lsub Λ₁ F = Lsub Λ₂ F → Lsub Λ₁ F' = Lsub Λ₂ F' → (gdat F F' Λ₁).2.2 = (gdat F F' Λ₂).2.2 → ∀ (p : PlF D) (g : Loc.SplitG (Z.M p).L), (Z.M p).split = some g → (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₁, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩ = (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₂, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩ := GlobalTheory.T.local_identification_eq_of_global_lattices_eq

theorem graph_eq_of_iota_eq : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ) (F : LFlag (D.sp.Y 0) D.R.rS (Tn : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (T'n : D.host.E)), Based Z FP Tn T'n F F' → ∀ Λ₁ Λ₂ : LV D, Submodule.IsLattice D.host.E Λ₁ → Submodule.IsLattice D.host.E Λ₂ → Lsub Λ₁ F = Lsub Λ₂ F → Lsub Λ₁ F' = Lsub Λ₂ F' → (∀ (p : PlF D) (g : Loc.SplitG (Z.M p).L), (Z.M p).split = some g → (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₁, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩ = (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₂, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩) → (gdat F F' Λ₁).2.2 = (gdat F F' Λ₂).2.2 := GlobalTheory.T.global_graph_eq_of_local_iota_agree

theorem datum_ext {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : Loc.HermSp M V} {r : ℕ} {P : LocNG.FPair H r} (d d' : LocNG.Datum P) (h1 : d.L = d'.L) (h2 : d.L' = d'.L') (h3 : d.io = d'.io) : d = d' := by
  cases d; cases d'; simp only at h1 h2 h3; subst h1 h2 h3; rfl

theorem gdat_eq_iff : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ₁ Λ₂ : LV D) (y₁ y₂ : Dat Z FP), LocOver Λ₁ y₁ → LocOver Λ₂ y₂ → (gdat F F' Λ₁ = gdat F F' Λ₂ ↔ y₁ = y₂) := by
  intro D X Y u u' F F' w _ _ Z FP hB _ Λ₁ Λ₂ y₁ y₂ h₁ h₂
  have hL : ∀ (Λ : LV D) (y : Dat Z FP), LocOver Λ y → ∀ p,
      ((y p).L : Set _) = (locH Z p).Lset (lattice₂ D Z.M p Λ) (FP p).A.f ∧
      ((y p).L' : Set _) = (locH Z p).Lset (lattice₂ D Z.M p Λ) (FP p).B.f ∧
      ∀ g, (Z.M p).split = some g → (y p).io = (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩ := by
    intro Λ y hy p
    obtain ⟨τ, hτ, hlam⟩ := hy.2 p
    have h1 := inner_of_term (locH Z p) D.R.rS (FP p) (y p) τ hτ
    refine ⟨h1.1.trans (congrArg (fun L => (locH Z p).Lset L (FP p).A.f) hlam),
      h1.2.trans (congrArg (fun L => (locH Z p).Lset L (FP p).B.f) hlam), fun g hg => ?_⟩
    have h2 := (hτ.2.2.2.2 g hg).2
    have e4 : ∀ (L : Submodule (Z.M p).L.O (Vp D p)) (a b c e : (D.s.atP p).Fp), L = lattice₂ D Z.M p Λ →
        (locH Z p).iotaGraph g ⟨L, (FP p).A.f, (FP p).B.f, a, b⟩ =
          (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ, (FP p).A.f, (FP p).B.f, c, e⟩ := by
      intro L a b c e hL; subst hL; rfl
    exact h2.symm.trans (e4 _ _ _ _ _ hlam)
  constructor
  · intro hg
    have hF : Lsub Λ₁ F = Lsub Λ₂ F := congrArg (fun t => t.1) hg
    have hF' : Lsub Λ₁ F' = Lsub Λ₂ F' := congrArg (fun t => t.2.1) hg
    have hΓ := congrArg (fun t => t.2.2) hg
    funext p
    apply datum_ext
    · apply SetLike.coe_injective
      exact (hL Λ₁ y₁ h₁ p).1.trans ((lset_eq_of_lsub_eq D Z p F (FP p).A (hB p).1 Λ₁ Λ₂ h₁.1 h₂.1 hF).trans (hL Λ₂ y₂ h₂ p).1.symm)
    · apply SetLike.coe_injective
      exact (hL Λ₁ y₁ h₁ p).2.1.trans ((lset_eq_of_lsub_eq D Z p F' (FP p).B (hB p).2.1 Λ₁ Λ₂ h₁.1 h₂.1 hF').trans (hL Λ₂ y₂ h₂ p).2.1.symm)
    · cases hs : (Z.M p).split with
      | none => exact ((y₁ p).io_L hs).trans ((y₂ p).io_L hs).symm
      | some g =>
        exact ((hL Λ₁ y₁ h₁ p).2.2 g hs).trans ((iota_eq_of_graph_eq D Z FP _ _ F F' hB Λ₁ Λ₂ h₁.1 h₂.1 hF hF' hΓ p g hs).trans
          ((hL Λ₂ y₂ h₂ p).2.2 g hs).symm)
  · intro hy
    subst hy
    have hF : Lsub Λ₁ F = Lsub Λ₂ F :=
      lsub_eq_of_lset_eq D Z F (fun p => (FP p).A) (fun p => (hB p).1) Λ₁ Λ₂ h₁.1 h₂.1
        (fun p => (hL Λ₁ y₁ h₁ p).1.symm.trans (hL Λ₂ y₁ h₂ p).1)
    have hF' : Lsub Λ₁ F' = Lsub Λ₂ F' :=
      lsub_eq_of_lset_eq D Z F' (fun p => (FP p).B) (fun p => (hB p).2.1) Λ₁ Λ₂ h₁.1 h₂.1
        (fun p => (hL Λ₁ y₁ h₁ p).2.1.symm.trans (hL Λ₂ y₁ h₂ p).2.1)
    have hΓ := graph_eq_of_iota_eq D Z FP _ _ F F' hB Λ₁ Λ₂ h₁.1 h₂.1 hF hF'
      (fun p g hs => ((hL Λ₁ y₁ h₁ p).2.2 g hs).symm.trans ((hL Λ₂ y₁ h₂ p).2.2 g hs))
    exact Prod.ext hF (Prod.ext hF' hΓ)

end GlobalTheory.Unfold.InnerDict
end

section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.majorantLength_twoSidedMoments_largeGap : GlobalTheory.GapIn.Hyp → ∀ Cg cb Cu cT CT C0 : ℝ, ∃ CH : ℝ, 0 ≤ CH ∧ ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), 1000 ≤ Cl → HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ τ w (W : LocW D.R.k D.R.rS), GoodW D τ w w 1 W → ∀ A : LocS W, GoodS D (lamD D τ) A → ∀ q : ℕ, q ≤ D.R.k * D.R.m ^ 3 → MomBd W.z W.νS A.Φ q (large₂.sc.b ^ (CH * (D.R.m : ℝ))) ∧ ∀ a : Fin (D.R.rS + 1), ∫⁻ x, ENNReal.ofReal ((lA D.R.k D.R.rS W.z (Matrix.of x) a)⁻¹ ^ (2 * q)) * (‖A.Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂W.νS ≤ ENNReal.ofReal ((large₂.sc.b ^ (CH * (D.R.m : ℝ))) ^ (2 * q)) * l2SG W.νS A.Φ := by
  first | exact @GlobalTheory.TwoSidedMomentsGap.two_sided_moments_gap | exact GlobalTheory.TwoSidedMomentsGap.two_sided_moments_gap | (intros; apply GlobalTheory.TwoSidedMomentsGap.two_sided_moments_gap <;> assumption)
end

section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.majorantLength_moments_amplitudes_largeGap : GlobalTheory.GapIn.Hyp → ∀ Cg cb Cu cT CT C0 C1 Cq : ℝ, ∃ C : ℝ, ∀ Cn : ℝ, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), 1000 ≤ Cl → Big D large₂ Cl m₀ → MomIn D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 Cq C := by
  first | exact @GlobalTheory.AmpMomentsGap.amplitude_moments_gap | exact GlobalTheory.AmpMomentsGap.amplitude_moments_gap | (intros; apply GlobalTheory.AmpMomentsGap.amplitude_moments_gap <;> assumption)
end

section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

theorem _root_.GlobalTheory.T.exists_besselMaps_largeGap_periodIdentities : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (h : ℝ), Formalism.QuantumDeterminants.GapAtLeast L.ε L.lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → L.c ≠ 0 → 0 < L.κN → L.κN ≠ ⊤ → ∃ (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq), GlobalTheory.AmpTK.BeTK L l l' ∧ GlobalTheory.AmpTK.SmCW L l ∧ GlobalTheory.AmpTK.SmCW L l' := by
  first | exact @GlobalTheory.AmpTKGap.exists_besselTK | exact GlobalTheory.AmpTKGap.exists_besselTK | (intros; apply GlobalTheory.AmpTKGap.exists_besselTK <;> assumption)
end

section

open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.lintegral_amplitudeNormSq_bigCell_gap : GlobalTheory.GapIn.Hyp → GlobalTheory.GapIn.AmpKF0 → CellConv → ∀ (k r : ℕ) (L : LocBessel k r) (μG : Measure (Mt k r)) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), 2 ≤ k → L.c ≠ 0 → L.κN ≠ 0 → L.κN ≠ ⊤ → IsHaarOn (UH (Hpk k r)) μG → IsSection k r L.z L.z' μsec → ∃ c : ℝ, 0 < c ∧ ∀ (R : Rep k r) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (l : R.H → L.Wp) (l' : R.H → L.Wq) (w : R.H), haveI := FiniteDimensional.complete ℂ L.Wp; haveI := FiniteDimensional.complete ℂ L.Wq; R.IsDS L.ε mu → GapAtLeast L.ε mu h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → GapCell k r h → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π R.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x)) → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' R.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x)) → (∃ v, R.KFin v ∧ l v ≠ 0) → (∃ v, R.KFin v ∧ l' v ≠ 0) → PI.UpqRep.IsLowUnitH k r L.ε mu R.σ w → ∫⁻ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (bcWeight k r (Tz k r L.z) (Tz k r L.z') q * hsNormSq (amp R l l' w μG (bigCell k r q.1 (μsec q.2)))) = ENNReal.ofReal (c / PI.BesselPeriodGGP.fdegH μG R.σ w ^ 3) := by
  first | exact @GlobalTheory.AmpNormGap.lintegral_hsNormSq_amp_gap | exact GlobalTheory.AmpNormGap.lintegral_hsNormSq_amp_gap | (intros; apply GlobalTheory.AmpNormGap.lintegral_hsNormSq_amp_gap <;> assumption)
end

section

open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CellOrbIntG

open GlobalTheory.CellOrbInt

theorem orbInt_integrable : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (L : LocBessel k r) (h : ℝ) (μG : Measure (Mt k r)) (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r)) (ν : Measure (PairSp k r)), GapAtLeast L.ε L.lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → L.κN ≠ ⊤ → CellData L μG γ μR νR ν → (∀ᵐ p ∂ν, Matrix.of p.1.1 ∈ UWset k r L.z ∧ Matrix.of p.1.2 ∈ Nset k r ∧ Matrix.of p.2.1 ∈ UWset k r L.z' ∧ Matrix.of p.2.2 ∈ Nset k r) ∧ ∀ b : ℝ, 0 ≤ b → b ≤ Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 → Integrable (pairMaj γ b) ν → ∀ v v' : L.Hs, PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v → PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v' → ∀ (ξ : L.Wp) (ξ' : L.Wq), Integrable (besselIntg L (coefF L v v' ξ ξ') γ) ν := by
  intro H k r L h μG γ μR νR ν hgap hok _ hC
  obtain ⟨hγ, -, -, -, hR, hQ, -⟩ := hC
  have hae := ae_quot L hR hQ
  refine ⟨hae, fun b _ hb hint v v' hv hv' ξ ξ' => ?_⟩
  have hσ : PI.UpqRep.IsDSHpk k r L.ε L.lam L.σ := L.hσ
  have hsm := H.1.1.2.2.1 k r L.ε L.lam L.Hs L.σ L.hlam hσ v' hv'
  obtain ⟨C, Ws, -, hdec⟩ := H.1.1.2.1 k r L.ε L.lam h L.Hs L.σ L.hlam hσ hgap hok v hv
  have hd := hdec v' hsm
  generalize C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) L.σ W v'‖).sum = A at hd
  have hF : ContinuousOn (coefF L v v' ξ ξ') (UH (Hpk k r)) := by
    have e : coefF L v v' ξ ξ' = fun g => ⟪v, L.σ g v'⟫_ℂ • (innerSL ℂ ξ').smulRight ξ :=
      funext (coefF_eq L v v' ξ ξ')
    rw [e]
    exact (ContinuousOn.inner (𝕜 := ℂ) continuousOn_const (Formalism.FourierDecayAlt.P.S3dx4.sigma_contOn hσ v')).smul continuousOn_const
  haveI : BorelSpace (PairSp k r) := Prod.borelSpace
  have hm : AEStronglyMeasurable (besselIntg L (coefF L v v' ξ ξ') γ) ν := by
    have := (contOn_intg L hγ hF).aestronglyMeasurable (μ := ν) (meas_pairSet L)
    rwa [Measure.restrict_eq_self_of_ae_mem hae] at this
  refine (hint.const_mul (|A| * ‖(innerSL ℂ ξ').smulRight ξ‖)).mono' hm ?_
  filter_upwards [hae] with p hp
  refine (norm_intg_le L γ _ hp).trans ?_
  have hx := point_mem L hγ hp
  unfold pairMaj
  set x := (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ * Matrix.of p.2.2 * Matrix.of p.2.1
  have h1 : 1 ≤ Formalism.FourierDecayAlt.B.gN x := PI.PolynomialProperness.GN.gN_ge_one hx
  have h2 : Formalism.FourierDecayAlt.B.gN x ^ (1 - Formalism.FourierDecayAlt.ThreeDimData.aOf r h) ≤ Formalism.FourierDecayAlt.B.gN x ^ (-b) :=
    Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  have h3 : ‖⟪v, L.σ x v'⟫_ℂ‖ ≤ |A| * Formalism.FourierDecayAlt.B.gN x ^ (-b) :=
    (hd x hx).trans ((mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)).trans
      (mul_le_mul_of_nonneg_left h2 (abs_nonneg A)))
  rw [coefF_eq, norm_smul, mul_right_comm]
  exact mul_le_mul_of_nonneg_right h3 (norm_nonneg _)

end GlobalTheory.CellOrbIntG
end

section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.amplitude_eq_smul_normalisedAmplitude_largeGap : GlobalTheory.GapIn.Hyp → ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W) (h : ℝ) (l : A.H → W.Wp) (l' : A.H → W.Wq), haveI := FiniteDimensional.complete ℂ W.Wp; haveI := FiniteDimensional.complete ℂ W.Wq; 0 < θ → 0 < D.host.ka / gg D → 0 < Tr D w → 0 < Tr D w' → GoodW D τ w w' θ W → GoodS D lam A → GapAtLeast (epsSH D.R) lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z (psiS D W.z) A.σ W.π l → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z' (psiS D W.z') A.σ W.π' l' → (∀ x ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).sm, ∀ v ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).TK, Formalism.FourierDecayAlt.ThreeDimData.be W.z ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) W.π A.σ W.μW W.μN x v = (innerSL ℂ (l v)).smulRight (l x)) → (∀ x ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).sm, ∀ v ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).TK, Formalism.FourierDecayAlt.ThreeDimData.be W.z' ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) W.π' A.σ W.μW' W.μN x v = (innerSL ℂ (l' v)).smulRight (l' x)) → (∃ v, (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).KFin v ∧ l v ≠ 0) ∧ (∃ v, (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).KFin v ∧ l' v ≠ 0) ∧ ∃ (w0 : A.H) (η : ℂ), PI.UpqRep.IsLowUnitH D.R.k D.R.rS (epsSH D.R) lam A.σ w0 ∧ ‖η‖ = PI.BesselPeriodGGP.fdegH W.μG A.σ w0 * Real.sqrt ((Module.finrank ℂ W.Wp : ℝ) * (Module.finrank ℂ W.Wq : ℝ)) ∧ ∀ (ν : Measure (Mt D.R.k D.R.rS)) (γ : MatKR D.R.k D.R.rS), γ ∈ UH (Hpk D.R.k D.R.rS) → ν {x | Matrix.of x ∉ UH (Hpk D.R.k D.R.rS)} = 0 → A.J ν γ = η • amp (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS) l l' w0 ν γ := by
  first | exact @GlobalTheory.AmpNormalGap.amp_eq_smul_normalised_gap | exact GlobalTheory.AmpNormalGap.amp_eq_smul_normalised_gap | (intros; apply GlobalTheory.AmpNormalGap.amp_eq_smul_normalised_gap <;> assumption)
end

section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm GlobalTheory.TypeAsm.PerRow
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.sum_pairs_definiteIsometry_le_frameClasses : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ → ∀ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W), GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype → ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) (h : GTu Y u → (W ≃ₗ[D.host.E] W)), (∀ t ∈ relSet Y u, GlobalTheory.DegAsm.IsH (F0 X u) (Ft t) W.subtype t.lin (h t)) → ∀ (Sf : Finset (GTu Y u × GTu Y u)), (∀ p ∈ Sf, p ∈ (Y.tO u u).allPairs (relSet Y u) ∧ p.1.lam = Λ) → (∀ p ∈ Sf, ∀ q ∈ Sf, h p.1 * (h p.2)⁻¹ = h q.1 * (h q.2)⁻¹) → ∑ p ∈ Sf, wRow D (X.Fu u) p.1.lam' * (omT p.1 * omT p.2) ≤ (∑ b ∈ Sf.image (fun p => frCls Λ p.1), clsOm Y u Λ b) * ∑ b ∈ Sf.image (fun p => frCls Λ p.2), clsOm Y u Λ b := by
  first | exact @GlobalTheory.TypeAsm.PerRow.sum_pairs_le_classes_pf | exact GlobalTheory.TypeAsm.PerRow.sum_pairs_le_classes_pf | (intros; apply GlobalTheory.TypeAsm.PerRow.sum_pairs_le_classes_pf <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Unfold.FixFin

section Img

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem img_mul (g g' : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) :
    LocNG.img (g * g') Λ = LocNG.img g (LocNG.img g' Λ) := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨g' x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, rfl⟩

theorem img_one (Λ : Submodule M.L.O V) : LocNG.img (1 : V ≃ₗ[E] V) Λ = Λ := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩; exact hx
  · intro hv; exact ⟨v, hv, rfl⟩

theorem img_inv {g : V ≃ₗ[E] V} {Λ Λ' : Submodule M.L.O V} (h : LocNG.img g Λ = Λ') :
    LocNG.img g⁻¹ Λ' = Λ := by
  rw [← h, ← img_mul, inv_mul_cancel, img_one]

theorem mem_Aut {g : V ≃ₗ[E] V} {Λ : Submodule M.L.O V} : g ∈ LocNG.Aut Λ ↔ LocNG.img g Λ = Λ := by
  constructor
  · intro hg
    unfold LocNG.Aut at hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one => exact img_one Λ
    | mul x y _ _ hx hy => rw [img_mul, hy, hx]
    | inv x _ hx => exact img_inv hx
  · intro h; exact Subgroup.subset_closure h

theorem img_fg_span (g : V ≃ₗ[E] V) (L : Submodule M.L.O V)
    (h : L.FG ∧ Submodule.span E (L : Set V) = ⊤) :
    (LocNG.img g L).FG ∧ Submodule.span E (LocNG.img g L : Set V) = ⊤ := by
  refine ⟨h.1.map _, ?_⟩
  have e : (LocNG.img g L : Set V) = (g : V →ₗ[E] V) '' (L : Set V) := rfl
  rw [e, Submodule.span_image, h.2, Submodule.map_top, LinearMap.range_eq_top]
  exact g.surjective

end Img

variable {D : D7}

theorem localLattice_fg_span (Z : LocDat D) (Λ : LV D) (h : Submodule.IsFullLattice D.host.E Λ) (p : PlF D) :
    (lattice₂ D Z.M p Λ).FG ∧ Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ : Set (Vp D p)) = ⊤ := by
  have hc : Submodule.IsFullLattice D.host.E (LatLoc.cL Λ) := by
    refine { toIsLattice := LatLoc.isLattice_map _ _ h.toIsLattice, span_eq_top := ?_ }
    change Submodule.span D.host.E ((LatLoc.cE D).toLinearMap '' (Λ : Set (VS D).V)) = ⊤
    rw [Submodule.span_image, h.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact (LatLoc.cE D).surjective
  have := (GlobalTheory.T.numberField_lattice_determined_by_local_lattices (GlobalTheory.HL.placesOf Z) (nV D) (LatLoc.cL Λ) hc).2.1 p
  rw [LatLoc.localLattice_eq]
  exact this

private theorem isFullLattice_of_local_span {D : D7} (Z : LocDat D) (p : PlF D) (Λ : LV D)
    (hΛ : Submodule.IsLattice D.host.E Λ)
    (hspan : Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ : Set (Vp D p)) = ⊤) :
    Submodule.IsFullLattice D.host.E Λ := by
  let U := Submodule.span D.host.E (Λ : Set (VS D).V)
  let b := Module.finBasis D.host.E U
  let W := Submodule.span (D.s.atP p).Ep
    (Set.range fun i => baseChange₂ D p (b i : (VS D).V))
  have hW (x : U) : baseChange₂ D p (x : (VS D).V) ∈ W := by
    have hx := congrArg (fun y : U => baseChange₂ D p (y : (VS D).V)) (b.sum_repr x)
    change baseChange₂ D p (U.subtype (∑ i, b.repr x i • b i)) = _ at hx
    rw [map_sum, map_sum] at hx
    rw [← hx]
    exact W.sum_mem fun i _ => by
      rw [map_smul, baseChange_smul₂]
      exact W.smul_mem _ (Submodule.subset_span (Set.mem_range_self i))
  have htop : W = ⊤ := by
    apply top_le_iff.mp
    rw [← hspan, lattice₂, Submodule.span_span_of_tower]
    refine Submodule.span_le.2 ?_
    rintro y ⟨x, hx, heq⟩
    rw [← heq]
    exact hW ⟨x, Submodule.subset_span hx⟩
  refine { toIsLattice := hΛ, span_eq_top := Submodule.eq_of_le_of_finrank_le le_top ?_ }
  rw [finrank_top, Module.finrank_eq_card_basis (VS D).frame, Fintype.card_fin]
  simpa only [Module.finrank_fin_fun, Fintype.card_fin] using
    finrank_le_of_span_eq_top (show Submodule.span (D.s.atP p).Ep _ = ⊤ from htop)


end GlobalTheory.Unfold.FixFin



open GlobalTheory.Unfold.FixFin in
theorem GlobalTheory.Unfold.FixFin.conj_aut_finite : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0)), (∀ (h : ↥(FlagPairStabilizer F F')) p, Ext p (h : GV D) ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)) → ∀ Λ₀ : LV D, Submodule.IsFullLattice D.host.E Λ₀ → ∀ a : ∀ p, ↥(FP p).UW0, {p | ((a p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∉ LocNG.Aut (lattice₂ D Z.M p Λ₀)}.Finite → {h : ↥(FlagPairStabilizer F F') | ∀ p, (((a p)⁻¹ * φ h p * a p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∈ LocNG.Aut (lattice₂ D Z.M p Λ₀)}.Finite := by
  intro D X Y u u' F F' w hw hG Z FP hB hR φ hφ Λ₀ hΛ₀ a ha
  have hLG := LatLoc.lattices_local_global D Z
  obtain ⟨Λa, hΛa, hΛap⟩ := hLG.2 Λ₀ hΛ₀
    (fun p => LocNG.img ((a p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (lattice₂ D Z.M p Λ₀))
    (fun p => img_fg_span _ _ (localLattice_fg_span Z Λ₀ hΛ₀ p))
    (ha.subset fun p hp hA => hp (mem_Aut.1 hA))
  obtain ⟨p⟩ := GlobalTheory.PhiEmbed.exists_place D
  have hΛaFull : Submodule.IsFullLattice D.host.E Λa := by
    apply isFullLattice_of_local_span Z p Λa hΛa
    rw [hΛap p]
    exact (img_fg_span _ _ (localLattice_fg_span Z Λ₀ hΛ₀ p)).2
  have H128 := GlobalTheory.T.rationalAutomorphism_local_extension_moves_lattices D X Y u u' F F' w hw hG Z FP hB hR
  have H133 := (GlobalTheory.T.rationalLatticeClasses_finite_localOrbits D X Y u u' F F' w hw hG Z FP hB hR Λa hΛaFull).1
  refine (H133.preimage Subtype.val_injective.injOn).subset ?_
  intro h hh
  refine ⟨h.2, ?_⟩
  have hgl : Submodule.IsFullLattice D.host.E (Formalism.HermitianLatticesTheory.gmap (h : GV D) Λa) := by
    refine { toIsLattice := LatLoc.isLattice_map (h : GV D) Λa hΛa, span_eq_top := ?_ }
    change Submodule.span D.host.E (((h : GV D) : (VS D).V →ₗ[D.host.E] (VS D).V) '' (Λa : Set (VS D).V)) = ⊤
    rw [Submodule.span_image, hΛaFull.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact (h : GV D).surjective
  apply (hLG.1 _ _ hgl hΛaFull).2
  intro p
  rw [H128.2.2.1 (h : GV D) p _ Λa (hφ h p), hΛap p]
  have e := mem_Aut.1 (hh p)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, img_mul, img_mul] at e
  have e2 := congrArg (LocNG.img ((a p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)) e
  rwa [← img_mul, mul_inv_cancel, img_one] at e2
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.splitTrivialTranslate_localComponent_disjoint_or_le : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))) (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (T : τ.V →ₗ[ℂ] (GAf L n → ℂ)), Function.Injective T → (∀ x : GAf L n, TrivOutside {s.v} x → ∀ a, T (τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) a) = NG.rt L n x (T a)) → ∀ y : GAf L n, TrivOutside {s.v}ᶜ y → ∀ P : Submodule ℂ (GAf L n → ℂ), (∀ x : GAf L n, TrivOutside {s.v} x → ∀ f ∈ P, NG.rt L n x f ∈ P) → Disjoint (LinearMap.range ((NG.rt L n y).comp T)) P ∨ LinearMap.range ((NG.rt L n y).comp T) ≤ P := by
  first | exact @GlobalTheory.SlocDich.translate_dichotomy | exact GlobalTheory.SlocDich.translate_dichotomy | (intros; apply GlobalTheory.SlocDich.translate_dichotomy <;> assumption)
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SnFamGenAll

theorem famGen : GlobalTheory.SnFam.FamGen := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, ?_⟩
  intro C' Cl _ _ D large₂ X Y u u' _
  have hG : ∀ t : TauC Y u u', t ∈ (Y.tO u u').genSet → t.G ≠ 0 := by
    intro t ht h0
    have h1 : (Y.tO u u').G t ≠ 0 := ht.1
    apply h1
    show Gt t = 0
    simp [Gt, h0]
  exact GlobalTheory.T.genericTerms_scalarClasses_form_family D X Y u u'
    (fun t ht t' ht' _ hs hc => GlobalTheory.T.corank_one_scalar_pair_symmetric D X Y u u' t t' (hG t ht) (hG t' ht') hs hc)
    (fun t ht t' ht' t'' ht'' _ _ hs hc hs' hc' =>
      GlobalTheory.T.scalarCorankOnePairs_trans D X Y u u' t t' t'' (hG t ht) (hG t' ht') (hG t'' ht'') hs hc hs' hc')

end GlobalTheory.SnFamGenAll
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.non_generic_corank_one_terms_family_cut_by_defect : GlobalTheory.SnFam.FamNG := by
  first | exact @GlobalTheory.SnFam.famNG_holds | exact GlobalTheory.SnFam.famNG_holds | (intros; apply GlobalTheory.SnFam.famNG_holds <;> assumption)
end
