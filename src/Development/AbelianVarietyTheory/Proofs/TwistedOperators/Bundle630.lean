module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle182
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOverBoth
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle624
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle059
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle621
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle620
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle622
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle626
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle611
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsPointedOfIsHkIsog
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle410

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix


theorem _root_.GlobalTheory.T.mem_congruenceSubgroup_of_stabilises_and_congruent : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ →
    ∀ (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ 𝔪 : Ideal (𝓞 D.host.E),
    (∀ PP : Pl D.host.E, 𝔪 ≤ PP.asIdeal → PP ∈ Z) → ∀ g : GA D V,
    (∀ v, (∀ PP ∈ Z, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) →
      GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v) →
    (∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ,
      toEAf D e • ((Lev.finE V g).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ∧
      toEAf D e • (((Lev.finE V g)⁻¹).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ∧
      toEAf D e • ((Lev.finE V g).1 *ᵥ x - x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ)) →
    Lev.finE V g ∈ congLev D.sp.cm V.gram Λ 𝔪 := by
  first | exact @GlobalTheory.CongAssemble.cong_assemble | exact GlobalTheory.CongAssemble.cong_assemble | (intros; apply GlobalTheory.CongAssemble.cong_assemble <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv GlobalTheory.LastVertexMove

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw




namespace GlobalTheory.FinEmbLat

open Matrix
open scoped nonZeroDivisors TensorProduct

variable {D : D7}

theorem mulVec_mem_hatL_of_mapsTo {m n : ℕ} (N : Matrix (Fin m) (Fin n) D.host.E)
    (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E))
    (hN : ∀ x ∈ Λ, N *ᵥ x ∈ Λ') :
    ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ, N.map (eToEAf D) *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ' := by
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    have e : N.map (eToEAf D) *ᵥ (fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (x i)) =
        fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) ((N *ᵥ x) i) := by
      funext i
      exact (RingHom.map_mulVec (eToEAf D) N x i).symm
    rw [e]
    exact Submodule.subset_span ⟨_, hN x hx, rfl⟩
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [mulVec_add]; exact add_mem ha hb
  | smul r a _ ha => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ r ha

variable {A B : HSp D} {c : ℕ} {ε : D.host.E}

theorem mapsTo_hatL_lat (d : HermitianOrthogonalExtensionData A B c ε) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
    (M : Matrix (Fin B.rank) (Fin B.rank) (Lev.EAf D)) (K : Matrix (Fin A.rank) (Fin A.rank) (Lev.EAf D))
    (h1 : M * (frameMat B A d.ι).map (eToEAf D) = (frameMat B A d.ι).map (eToEAf D) * K)
    (h2 : M * d.a.map (eToEAf D) = d.a.map (eToEAf D))
    (hK : ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ, K *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    ∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (d.lat Λ fun _ => 1),
      M *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (d.lat Λ fun _ => 1) := by
  have hP : ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ,
      (frameMat B A d.ι).map (eToEAf D) *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) (d.lat Λ fun _ => 1) :=
    mulVec_mem_hatL_of_mapsTo _ Λ _ fun x hx =>
      ⟨x, hx, 0, fun _ => (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E).zero_mem, by rw [mulVec_zero, add_zero]⟩
  intro v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨x, ⟨y0, hy0, u, hu, rfl⟩, rfl⟩ := hv
    have e : (fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)
        (((frameMat B A d.ι) *ᵥ y0 + d.a *ᵥ u) i)) =
        (frameMat B A d.ι).map (eToEAf D) *ᵥ (fun i => eToEAf D (y0 i)) + d.a.map (eToEAf D) *ᵥ (fun p => eToEAf D (u p)) := by
      funext i
      rw [Pi.add_apply, Pi.add_apply, map_add (f := _)]
      exact congrArg₂ (· + ·) (RingHom.map_mulVec (eToEAf D) _ y0 i) (RingHom.map_mulVec (eToEAf D) d.a u i)
    show M *ᵥ (fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)
        (((frameMat B A d.ι) *ᵥ y0 + d.a *ᵥ u) i)) ∈ _
    rw [e, mulVec_add, mulVec_mulVec, mulVec_mulVec, h1, h2, ← mulVec_mulVec]
    refine add_mem (hP _ (hK _ (Submodule.subset_span ⟨y0, hy0, rfl⟩))) ?_
    have e2 : d.a.map (eToEAf D) *ᵥ (fun p => eToEAf D (u p)) =
        fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) ((d.a *ᵥ u) i) := by
      funext i
      exact (RingHom.map_mulVec (eToEAf D) d.a u i).symm
    rw [e2]
    exact Submodule.subset_span ⟨_, ⟨0, zero_mem _, u, hu, by rw [mulVec_zero, zero_add]⟩, rfl⟩
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [mulVec_add]; exact add_mem ha hb
  | smul r a _ ha => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ r ha

end GlobalTheory.FinEmbLat

namespace GlobalTheory.FinEmbLat

open Matrix

theorem finEmb_mem_stabGL : ∀ {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (y : GfC A), Lev.finE A y.1 ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) Λ) → Lev.finE B (finEmb d y).1 ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) (d.lat Λ fun _ => 1)) := by
  intro D A B c ε d Λ y hy
  have hrel := finEmb_rel d y
  set G' := Lev.finE B (finEmb d y).1 with hG'
  set Y := Lev.finE A y.1 with hY
  have h1 : G'.1 * (frameMat B A d.ι).map (eToEAf D) = (frameMat B A d.ι).map (eToEAf D) * Y.1 := by
    have := congrArg (fun X => X.map (toEAf D)) hrel.1
    simp only [Matrix.map_mul] at this
    exact this
  have h2 : G'.1 * d.a.map (eToEAf D) = d.a.map (eToEAf D) := by
    ext i p
    have hx := hrel.2 (fun k => d.a k p) (by
      funext k
      exact congrFun (congrFun d.perp k) p)
    have := congrArg (toEAf D) (congrFun hx i)
    rw [RingHom.map_mulVec] at this
    exact this
  have hK : ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ, Y.1 *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ :=
    fun z hz => (hy z).1 hz
  have hKi : ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ, (Y⁻¹).1 *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ :=
    fun z hz => ((Subgroup.inv_mem _ hy) z).1 hz
  have h1i : (G'⁻¹).1 * (frameMat B A d.ι).map (eToEAf D) = (frameMat B A d.ι).map (eToEAf D) * (Y⁻¹).1 := by
    calc (G'⁻¹).1 * (frameMat B A d.ι).map (eToEAf D)
        = (G'⁻¹).1 * (frameMat B A d.ι).map (eToEAf D) * (Y.1 * (Y⁻¹).1) := by
          rw [Units.mul_inv, Matrix.mul_one]
      _ = (G'⁻¹).1 * ((frameMat B A d.ι).map (eToEAf D) * Y.1) * (Y⁻¹).1 := by
          simp only [Matrix.mul_assoc]
      _ = (G'⁻¹).1 * (G'.1 * (frameMat B A d.ι).map (eToEAf D)) * (Y⁻¹).1 := by rw [h1]
      _ = (frameMat B A d.ι).map (eToEAf D) * (Y⁻¹).1 := by
          rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  have h2i : (G'⁻¹).1 * d.a.map (eToEAf D) = d.a.map (eToEAf D) := by
    conv_lhs => rw [← h2]
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  intro v
  constructor
  · exact mapsTo_hatL_lat d Λ G'.1 Y.1 h1 h2 hK v
  · intro hv
    have := mapsTo_hatL_lat d Λ (G'⁻¹).1 (Y⁻¹).1 h1i h2i hKi _ hv
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

end GlobalTheory.FinEmbLat
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaProjection_intertwines_levelLifts : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ i t g κ, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) κ → ∀ y y' : (R.HV i t).H, (∀ h, (R.HV i t).e y' h = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • (R.HV i t).e y (h * (finHom _).rangeRestrict κ)) → R.thG i t y' = R.gW i (sg0 D A) g (R.thG i t y) := by
  first | exact @GlobalTheory.ThetaProjEquiv.thG_intertwines_core | exact GlobalTheory.ThetaProjEquiv.thG_intertwines_core | (intros; apply GlobalTheory.ThetaProjEquiv.thG_intertwines_core <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.fractionalIdealCompletion_div_conjModulus_off_badPlaces : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D}, v ∉ P.S0 → ∀ (𝔞 : GlobalTheory.SeeSaw.FI D) (s : AE D), s ∈ GlobalTheory.SeeSaw.idV (𝔞 * ((P.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) v ↔ s ∈ GlobalTheory.SeeSaw.idV 𝔞 v := by
  first | exact @GlobalTheory.ModBarOff.idV_mul_modulBar_inv | exact GlobalTheory.ModBarOff.idV_mul_modulBar_inv | (intros; apply GlobalTheory.ModBarOff.idV_mul_modulBar_inv <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainInv

variable {D : D7}

theorem conjP_eq_conjPl (P : HeightOneSpectrum (𝓞 D.host.E)) : Formalism.L2.Col.conjPrime₂ P = Formalism.DivisionValues.conjPl P := by
  apply HeightOneSpectrum.ext
  ext x
  show Formalism.L2.Col.cO _ x ∈ P.asIdeal ↔ x ∈ Ideal.map (Formalism.DivisionValues.cO D.host.E) P.asIdeal
  rw [← Ideal.comap_symm, Ideal.mem_comap]
  have : (Formalism.DivisionValues.cO D.host.E).symm x = Formalism.L2.Col.cO _ x := by
    apply RingOfIntegers.ext
    simp [Formalism.DivisionValues.cO, Formalism.L2.Col.cO]
    rfl
  rw [this]

theorem under_conjPl (w : HeightOneSpectrum (𝓞 D.host.E)) :
    (Formalism.DivisionValues.conjPl w).under (𝓞 D.host.F) = w.under (𝓞 D.host.F) := by
  rw [← conjP_eq_conjPl]
  exact GlobalTheory.GridPlaces.under_conjP w

theorem absNorm_conjPl (w : HeightOneSpectrum (𝓞 D.host.E)) :
    Ideal.absNorm (Formalism.DivisionValues.conjPl w).asIdeal = Ideal.absNorm w.asIdeal := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr
    (Ideal.quotientEquiv w.asIdeal (Formalism.DivisionValues.conjPl w).asIdeal (Formalism.DivisionValues.cO D.host.E) rfl).toEquiv).symm

theorem not_isSplit_of_conjPl_eq {w : HeightOneSpectrum (𝓞 D.host.E)} (hc : Formalism.DivisionValues.conjPl w = w) :
    ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) := by
  intro hs
  obtain ⟨P, Q, hPQ, hP, hQ⟩ := GlobalTheory.LFun.isSplit_iff.1 hs
  have key : ∀ R : HeightOneSpectrum (𝓞 D.host.E), R.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) → R = w :=
    fun R hR => (GlobalTheory.GridPlaces.eq_or_eq_conjP hR).elim id fun h => h.trans ((conjP_eq_conjPl w).trans hc)
  exact hPQ ((key P hP).trans (key Q hQ).symm)

theorem val_conjPl_of_resEta (χ : (AE D)ˣ →* Circle) (n : ℕ) (hr : Formalism.L2.Theta.ResEta D χ n)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hu : GlobalTheory.LFun.UnrAt χ w) (hu' : GlobalTheory.LFun.UnrAt χ (Formalism.DivisionValues.conjPl w)) :
    GlobalTheory.LFun.val (F := D.host.F) χ (Formalism.DivisionValues.conjPl w) = (GlobalTheory.LFun.val (F := D.host.F) χ w)⁻¹ := by
  have h2 := (GlobalTheory.AdelicU.isCMExt_host D).2.2.1
  by_cases hc : Formalism.DivisionValues.conjPl w = w
  · have hns := not_isSplit_of_conjPl_eq hc
    rcases GlobalTheory.LFun.InertChart.isSplit_or_isInertAt (GlobalTheory.VacCoef.isUnram_host D (w.under (𝓞 D.host.F))) with hs | ⟨w0, hw0⟩
    · exact absurd hs hns
    · obtain rfl : w0 = w := GlobalTheory.LFun.eq_of_not_isSplit hns (GlobalTheory.LFun.under_eq_of_isInertAt hw0) rfl
      have hv := GlobalTheory.LFun.ResEta.val_of_isInertAt h2 hr hw0 hu
      rw [hc, hv, ← inv_pow, inv_neg_one]
  · exact eq_inv_of_mul_eq_one_right (GlobalTheory.LFun.ResEta.val_mul_val h2 hr (Ne.symm hc) rfl (under_conjPl w) hu hu')

theorem val_step_conjPl (c : Com D) (hc : c.Is) (k : ℕ) (hk : k < D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) :
    GlobalTheory.LFun.val (F := D.host.F) (c.chS (k + 1)) (Formalism.DivisionValues.conjPl w) =
                 (GlobalTheory.LFun.val (F := D.host.F) (c.chS (k + 1)) w)⁻¹ ∧
      GlobalTheory.LFun.val (F := D.host.F) (c.chT (k + 1)) (Formalism.DivisionValues.conjPl w) =
        (GlobalTheory.LFun.val (F := D.host.F) (c.chT (k + 1)) w)⁻¹ := by
  have hw' : Formalism.DivisionValues.conjPl w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) := by
    intro h
    apply hw
    rw [GlobalTheory.LFun.above, Set.mem_setOf_eq] at h ⊢
    rwa [under_conjPl] at h
  have hμ : GlobalTheory.LFun.val (F := D.host.F) (c.μ (k + 1)) (Formalism.DivisionValues.conjPl w) =
      (GlobalTheory.LFun.val (F := D.host.F) (c.μ (k + 1)) w)⁻¹ :=
    val_conjPl_of_resEta _ 0 (hc.chars.2.2.2.2 (k + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)).2 w
      (hc.unr ⟨k, hk⟩ w hw) (hc.unr ⟨k, hk⟩ _ hw')
  have hη : GlobalTheory.LFun.val (F := D.host.F) c.η (Formalism.DivisionValues.conjPl w) = (GlobalTheory.LFun.val (F := D.host.F) c.η w)⁻¹ :=
    val_conjPl_of_resEta _ 1 hc.chars.2.2.1 w (GlobalTheory.LFun.unrAt_of_unramEverywhere hc.chars.2.1 w)
      (GlobalTheory.LFun.unrAt_of_unramEverywhere hc.chars.2.1 _)
  unfold Com.chS Com.chT Lift.chrStep
  split_ifs <;> simp only [GlobalTheory.LFun.val_mul, GlobalTheory.LFun.val_inv, hμ, hη, mul_inv, inv_inv, and_self]

theorem range_reflect (t : ℕ) : (Multiset.range t).map (fun i => t - 1 - i) = Multiset.range t := by
  refine (Multiset.Nodup.ext ?_ (Multiset.nodup_range t)).2 fun a => ?_
  · refine (Multiset.nodup_range t).map_on fun x hx y hy h => ?_
    rw [Multiset.mem_range] at hx hy
    omega
  · simp only [Multiset.mem_map, Multiset.mem_range]
    constructor
    · rintro ⟨b, hb, rfl⟩; omega
    · intro ha; exact ⟨t - 1 - a, by omega, by omega⟩

theorem seg_conjPl (w : HeightOneSpectrum (𝓞 D.host.E)) (z : ℂˣ) (t : ℕ) :
    GlobalTheory.LFun.seg (Formalism.DivisionValues.conjPl w) z⁻¹ t = (GlobalTheory.LFun.seg w z t).map (·⁻¹) := by
  have hN : ∀ y, GlobalTheory.LFun.npowU (Formalism.DivisionValues.conjPl w) y = GlobalTheory.LFun.npowU w y := fun y =>
    Units.ext (by simp only [GlobalTheory.LFun.coe_npowU, GlobalTheory.LFun.npow, absNorm_conjPl])
  simp only [GlobalTheory.LFun.seg, hN, Multiset.map_map, Finset.range_val]
  conv_rhs => rw [← range_reflect t, Multiset.map_map]
  refine Multiset.map_congr rfl fun i hi => ?_
  rw [Multiset.mem_range] at hi
  simp only [Function.comp_apply, mul_inv]
  congr 1
  refine Units.ext ?_
  simp only [GlobalTheory.LFun.coe_npowU, Units.val_inv_eq_inv_val, GlobalTheory.LFun.npow]
  rw [← Complex.cpow_neg]
  congr 1
  push_cast [Nat.cast_sub (show i ≤ t - 1 by omega), Nat.cast_sub (show 1 ≤ t by omega)]
  ring

theorem chainPar_conjPl (c : Com D) (hc : c.Is) (B B' : GlobalTheory.LFun.Fam D.host.E) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))))
    (hB : B' (Formalism.DivisionValues.conjPl w) = (B w).map (·⁻¹)) :
    ∀ k ≤ D.R.m, chainPar c B' k (Formalism.DivisionValues.conjPl w) = (chainPar c B k w).map (·⁻¹) := by
  intro k hk
  induction k with
  | zero => exact hB
  | succ k ih =>
    obtain ⟨hS, hT⟩ := val_step_conjPl c hc k (by omega) w hw
    rw [chainPar_succ, chainPar_succ]
    simp only [stepPar]
    rw [ih (by omega), hS, hT, seg_conjPl, Multiset.map_add (f := _), Multiset.map_map, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun b _ => ?_
    simp only [Function.comp_apply, mul_inv, inv_inv]

theorem conjPl_inv_of_chainPar : ∀ (D : D7) (c : Com D), c.Is → ∀ j ≤ D.R.m, ∀ (B : GlobalTheory.LFun.Fam D.host.E),
    ∀ w ∉ (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))),
    chainPar c B j (Formalism.DivisionValues.conjPl w) = (chainPar c B j w).map (·⁻¹) →
      B (Formalism.DivisionValues.conjPl w) = (B w).map (·⁻¹) := by
  intro D c hc j hj B w hw h
  classical
  let B' : GlobalTheory.LFun.Fam D.host.E := Function.update B (Formalism.DivisionValues.conjPl w) ((B w).map (·⁻¹))
  have hB : B' (Formalism.DivisionValues.conjPl w) = (B w).map (·⁻¹) := by simp [B']
  have h1 := chainPar_conjPl c hc B B' w hw hB j hj
  have h2 := chainPar_inj_at D c j B B' (Formalism.DivisionValues.conjPl w) (h.trans h1.symm)
  rw [h2, hB]

end GlobalTheory.ChainInv

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.GoodBaseChange

theorem good_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T T' : CDVR) (io : c.F →+* T.Fr) (io' : c.F →+* T'.Fr) (y : IntFr Xo c T io) (y' : IntFr Xo c T' io') (i : T.Fr →+* T'.Fr) (r : ℕ), 0 < r → (∀ a : T.Fr, vV T'.V (i a) = (r : ℤ) * vV T.V a) → xOf y' = spMap i ≫ xOf y → GlobalTheory.GoodPts.Good y → GlobalTheory.GoodPts.Good y' := by
  intro E _ _ _ H Dw l Xo c T T' io io' y y' i r _ hv hx hy
  obtain ⟨G, t, m1, m2, hp⟩ := hy
  obtain ⟨φ, hφ⟩ := GlobalTheory.IntFrBaseChange.exists_restrict T T' i r hv
  obtain ⟨G', mG⟩ : ∃ G' : SAB H (Sp T'.V), Nonempty (SABMap G' G (spMap φ)) := by
    obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.CubePf.cubePull (spMap φ) G
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨t', mt⟩ : ∃ t' : SAB H (Sp T'.Fr), Nonempty (SABMap t' t (spMap i)) := by
    obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.CubePf.cubePull (spMap i) t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨mG⟩ := mG
  obtain ⟨mt⟩ := mt
  obtain ⟨n1, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m1 mt
  obtain ⟨n2, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m2 mt
  have hsq : spMap i ≫ spMap (algebraMap T.V T.Fr) = spMap (algebraMap T'.V T'.Fr) ≫ spMap φ := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => (hφ a).symm))
  rw [hsq] at n2
  obtain ⟨n3, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ mG n2
  have n4 : SABMap t' Xo.univ.t (xOf y') := by
    rw [hx]
    exact n1
  exact ⟨G', t', n4, n3, MorphismProperty.of_isPullback (P := @IsProper) mG.cart.1 hp⟩

end GlobalTheory.GoodBaseChange
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical


theorem _root_.GlobalTheory.T.normSq_productDatumTheta_conjugateHalf : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → ∀ i t σ s P cμ cη m ω BW f₀ f c io, GlobalTheory.LiftRows.IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io →
  ∀ e : AE D, IsIdemSum e (R.Pg ∪ R.Q t) →
  ∀ (Gd : (∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) → ℂ)
    (h : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP) → ℝ),
    (∀ y, ‖Gd y‖ = ∏ PP ∈ R.Pg ∪ R.Q t, h PP (y PP)) →
  ∀ f' : WO (Vc D i) (Wc D i) → ℂ,
    IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D e)
      (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 f₀
      (fun x => if IsHalf (cA D e) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then
        Gd (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) f' →
  ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 →
    nrm2 μ 𝓧 f' = ∏ PP ∈ R.Pg ∪ R.Q t, (∑ᶠ z, h PP z ^ 2) / (Nat.card (kP PP) : ℝ) ^ ((Vc D i).rank * (Wc D i).rank) := by
  first | exact @GlobalTheory.PlancherelHalf.normSq_thetaAt_halfProd | exact GlobalTheory.PlancherelHalf.normSq_thetaAt_halfProd | (intros; apply GlobalTheory.PlancherelHalf.normSq_thetaAt_halfProd <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_realIntertwiners_upwardThetaPair : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (t : ℕ) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (aS aT : D.what₂.Tau → ℚ) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ → (∀ τ, UpPair t (S τ) (S' τ) (aS τ) (aT τ)) → (∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, ∀ ω f, GlobalTheory.PairLift.IsWeilExp ψ V W aS aT ω → GlobalTheory.Chain.IsVacVec ψ θ M M' f → IsItW θ M M' ω (GlobalTheory.Chain.ptOf ψ θ M M' f) It) ∧ ∃ It : PolF D V.rank W.rank →ₗ[ℂ] SmT M →ₗ[ℂ] SmT M', ∀ ω f, GlobalTheory.PairLift.IsWeilExp ψ W V aT aS ω → GlobalTheory.Chain.IsVacVec ψ θ M' M f → IsItW θ M' M ω (GlobalTheory.Chain.ptOf ψ θ M' M f) It := by
  first | exact @GlobalTheory.EvenOnto.upPair_itW | exact GlobalTheory.EvenOnto.upPair_itW | (intros; apply GlobalTheory.EvenOnto.upPair_itW <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_common_denominator_selfDual_level : ∀ (D : D7) (V : HSp D) (Λ : Lat V), IsSelfDualC V Λ → ∃ b : ℕ, 0 < b ∧ ∀ k ∈ congLev D.sp.cm V.gram Λ ⊤, ∀ i j, (b : Lev.EAf D) * k.1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  first | exact @GlobalTheory.LevelDenom.exists_denom_congLev | exact GlobalTheory.LevelDenom.exists_denom_congLev | (intros; apply GlobalTheory.LevelDenom.exists_denom_congLev <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unipotentPeriod_value_lipschitz_realOneParameter : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (S S' : D.what₂.Tau → SPar) (M₀ : DSModel Y S') (M : DSModel V S) (p : Pack M₀ M) (Q : ℝ), p.Is θ d Q → ∀ (J : Set (GA D Y)) (χ : GA D Y → ℂ), ∀ t ∈ MultT θ M₀ J χ, ∀ b : ℝ, (∀ x, ‖t (PiTensorProduct.tprod ℂ p.w) x‖ ≤ b) → Lip θ p.A (t (PiTensorProduct.tprod ℂ p.w)) (Real.exp Q * b) := by
  first | exact @GlobalTheory.SepPer.LipValue.lip_value | exact GlobalTheory.SepPer.LipValue.lip_value | (intros; apply GlobalTheory.SepPer.LipValue.lip_value <;> assumption)
end
