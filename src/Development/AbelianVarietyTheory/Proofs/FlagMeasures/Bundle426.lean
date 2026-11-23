module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitalIntegralsTermsOneDoubleCoset
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle004
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle005
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle421
public import Formalism.UnipotentAdelicQuotients.Bundle003
public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle420
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle403
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle138
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplifierOfHypotheses
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle203

@[expose] public section

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.orbital_integrals_terms_one_doubleCoset : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → ∀ ν, Formalism.L2.SG.RealObj.NuQPin X u u' ν → ∀ t₀ : TauC Y u u', t₀.relevant → t₀.G ≠ 0 → ∀ w, w = Formalism.L2.SG.PairVal.ptOf t₀.toTerm → (∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) ∧ ∃ T : X.Vpi u' →L[ℂ] X.Vpi u, ‖Formalism.L2.SG.PackageTie.hsEmb T‖ = ‖Formalism.L2.SG.PackageTie.hsEmb (haveI := FiniteDimensional.complete ℂ (X.Vpi u); OO (ν (Formalism.L2.SG.RealObj.gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (Formalism.L2.SG.RealObj.gamW X u u' w))‖ ∧ ∀ (t : TauC Y u u') (n m : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (xn xm : X.B.I.GA), n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → RatLink X xn n → RatLink X xm m → ∃ (μR : Measure X.B.I.Ginf) (K : Set X.B.I.Ginf), Formalism.L2.SG.VolPin.IsPinnedR t w μR ∧ (MeasurableSet K ∧ ∀ y ∈ Formalism.L2.SG.TermOp.Vanish.Rset t, ∃! s, s ∈ ROinf t ∧ s * y ∈ K) ∧ OOt t = (((μR K).toReal : ℂ) * ((X.psiInfU u xn.1)⁻¹ * X.psiInfU u' xm.1)) • T := by
  first | exact @GlobalTheory.CosetOrbital.coset_orbital_form | exact GlobalTheory.CosetOrbital.coset_orbital_form | (intros; apply GlobalTheory.CosetOrbital.coset_orbital_form <;> assumption)
end

section

namespace GlobalTheory

theorem stepFamC_of_globalLeaves :
    Formalism.L2.SG.FamDefs.OrbitFamilyIdentityNonGeneric → Formalism.L2.SG.FamDefs.WeightsNG → Formalism.L2.SG.FamDefs.ProductStructureNonGeneric →
      Formalism.L2.SG.FamDefs.ExistNG → Formalism.L2.SG.NGLocModel.StepFamC :=
  fun hG5 hW hG4 hE =>
    Formalism.L2.SG.FamDefs.stepFamC_of (fun D h => GlobalTheory.T.localMass_le_genericMass_const_nine _ _ h) GlobalTheory.T.differentLocalIdentity_familiesLemmaH hG5 hW hG4 hE

end GlobalTheory
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.columnDictionary_bijective_of_levelMatch : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter), (∀ a, Tr.ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Tr.ιA a)) → LevelMatch X Tr hK → ColDictBij X Tr hK := by
  first | exact @GlobalTheory.St.colDict_bij_of_levelMatch | exact GlobalTheory.St.colDict_bij_of_levelMatch | (intros; apply GlobalTheory.St.colDict_bij_of_levelMatch <;> assumption)
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.columnDictionary_isometric_of_representatives : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter), (∀ a, Tr.ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Tr.ιA a)) → LevelMatch X Tr hK → Formalism.L2.SG.ColsDim.StabTriv (iotaF X u) (Ku X u hK) → ∀ (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (cs : Formalism.L2.SG.TermOp.ColSys X u what₂) (hinj : Function.Injective (Formalism.L2.SG.TermOp.sharp hK cs)), Formalism.L2.SG.TermOp.ColReps hK cs → ColDictIsom X Tr hK cs hinj := by
  first | exact @GlobalTheory.St.colDict_isometric_of_reps | exact GlobalTheory.St.colDict_isometric_of_reps | (intros; apply GlobalTheory.St.colDict_isometric_of_reps <;> assumption)
end

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.relevant_term_has_real_relative_point : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (θ : ℝ) (C : Choice X θ) (u u' : D.what₂.Word) (t : D.s.Term u u') (s : TT Y u u'), s.toTerm = tc hI t → D.s.Gterm t ≠ 0 → D.s.relevant t → ∀ τ, ∃ p, RelPt D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (s.pt.1 (vOf X τ))) p := by
  first | exact @GlobalTheory.RelPtLift.relPt_lift | exact GlobalTheory.RelPtLift.relPt_lift | (intros; apply GlobalTheory.RelPtLift.relPt_lift <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.exists_haar_frameStabiliser_compatible_fibre : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∀ (hT : ∀ i j, σ (gramE σ J (F0 P) j i) = gramE σ J (F0 P) i j), ∀ (μ : Measure (Fin (r + 1) → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ (r + 1))), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ fib : HermR (Fv F v) σ (r + 1) → Measure (Fin (r + 1) → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib → ∀ μG : Measure (HA (Fv F v) σ J), μG.IsHaarMeasure → ∃ μ0 : Measure (S0 (Fv F v) σ J P), μ0.IsHaarMeasure ∧ ((fib (hermOf (Fv F v) σ (gramE σ J (F0 P)) hT)) {y | ¬ ∃ g : HA (Fv F v) σ J, g • ratTup (Fv F v) (F0 P) = y} = 0 ∧ ∀ f : HA (Fv F v) σ J → ℝ≥0∞, Measurable f → ∀ s : (Fin (r + 1) → Fin n → Fv F v ⊗[F] E) → HA (Fv F v) σ J, (∀ y, (∃ g : HA (Fv F v) σ J, g • ratTup (Fv F v) (F0 P) = y) → s y • ratTup (Fv F v) (F0 P) = y) → ∫⁻ g, f g ∂μG = ∫⁻ y, ∫⁻ h', f (s y * (h' : HA (Fv F v) σ J)) ∂μ0 ∂(fib (hermOf (Fv F v) σ (gramE σ J (F0 P)) hT))) := by
  first | exact @GlobalTheory.LocalStabiliserHaar.exists_haar_stabiliser | exact GlobalTheory.LocalStabiliserHaar.exists_haar_stabiliser | (intros; apply GlobalTheory.LocalStabiliserHaar.exists_haar_stabiliser <;> assumption)
end

section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp
noncomputable section

namespace GlobalTheory.AmpTKOne

open GlobalTheory.AmpOrb GlobalTheory.CellOrbInt GlobalTheory.AmpTK

variable {k r : ℕ}

theorem besselIntg_sum (L : LocBessel k r) {ι : Type} (s : Finset ι)
    (F : ι → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp))
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (p : PairSp k r) :
    besselIntg L (fun q => ∑ a ∈ s, F a q) g p = ∑ a ∈ s, besselIntg L (F a) g p := by
  ext η

  simp [besselIntg, ContinuousLinearMap.sum_apply, map_sum, Finset.smul_sum]

end GlobalTheory.AmpTKOne
end
end

section

open Formalism.MainNotions.PlaceDegreeData

namespace GlobalTheory.CountBridge

theorem count_typed_of_volumeStep :
    GlobalTheory.FlagMeas.VolumeStep → ∀ A : ℝ, ∃ (n₀ : ℕ) (C₀ : ℝ), 0 ≤ C₀ ∧ ∀ n₁ ≥ n₀, ∀ C ≥ C₀,
      ∀ D : Formalism.BasicNotions.D7, Formalism.MainNotions.PlaceDegreeData.PointsLemma D n₁ A C (1 / 16) (1 / 16) := by
  intro hV A
  obtain ⟨n₀, C₀, hC₀, hcount⟩ := GlobalTheory.T.unitaryAutomorphicCounting_unbundled (GlobalTheory.T.unitaryAutomorphicCounting_of_compactDualVolumeRatio hV) A
  refine ⟨n₀, C₀, hC₀, fun n₁ hn₁ C hC _D => ?_⟩
  intro I b lam g g₀ e H _ _ _ σ w Hs _ _ _ σs tens μf _ fund R Re h hSet hData
  exact hcount n₁ hn₁ C hC I b lam g g₀ e H σ w Hs σs tens μf fund R Re h hSet hData

end GlobalTheory.CountBridge
end

section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.amplitude_one_side_of_good_local_data : ∀ (D : D7) (τ : D.what₂.Tau) (w w' : D.what₂.Word) (θ : ℝ) (W : LocW D.R.k D.R.rS) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W), 0 < D.host.v → 0 < θ → 0 < Tr D w → 0 < Tr D w' → GoodW D τ w w' θ W → GoodS D lam A → OneSide W.z W.π (psiS D W.z) W.μG W.μW (ENNReal.ofReal ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ * 2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) • lebN D.R.k D.R.rS) W.νS A.Φ A.cN ∧ OneSide W.z' W.π' (psiS D W.z') W.μG W.μW' (ENNReal.ofReal ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ * 2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) • lebN D.R.k D.R.rS) W.νS' A.Φ' A.cN := by
  first | exact @GlobalTheory.AmpSides.oneSide_of_good | exact GlobalTheory.AmpSides.oneSide_of_good | (intros; apply GlobalTheory.AmpSides.oneSide_of_good <;> assumption)
end

section


theorem _root_.GlobalTheory.T.unitary_hyperplane_volumeRatio_siegelWeil : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ D : Formalism.BasicNotions.D7, Formalism.MainNotions.RT.MassRatioUnderVolume D := by
  first | exact @GlobalTheory.VolRatioFromSiegelWeil.volumeRatio | exact GlobalTheory.VolRatioFromSiegelWeil.volumeRatio | (intros; apply GlobalTheory.VolRatioFromSiegelWeil.volumeRatio <;> assumption)
end
