module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle014
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdSubConjEqNeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeTrivialBoundOfBoundedZonalSphericalUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle277
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle278
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.InducedCmType
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralTwistedPlaceEigenvecto
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle010
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle112
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RecHeightWith
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2
attribute [local instance] GlobalTheory.Mem.Col2.starE

noncomputable section

namespace GlobalTheory.Core.Ht2

theorem analyticTies_trueCols : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (hX : B.fields.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)), ColIn.JetsIn I → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice (I.rec7 l Z) ⊤ I.J.δ ∧ TaylorLogMetric.IsChi (I.rec7 l Z) I.chi ∧ IsDgen (I.rec7 l Z) I.J.cD ∧ ∀ u a, GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.FieldOfDefinition (Pr := B.primes X) B.wts I.sel (I.tup a) (I.cst a) u I.A := by
  intro B X I h _ l Z hJ
  have hA := (I.J.ok_iff B (I.cols l) Z.W Z.V Z.S Z.N Z.G).1 h.amb_ok
  exact ⟨hA.1, GlobalTheory.Mem.ChiIdeal.isChi_chiId (I.rec7 l Z) I.C.chiPsi I.C.isChi, hA.2, fun u a i hi => hJ a u i hi⟩

end GlobalTheory.Core.Ht2

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.CoreHt

theorem charTie_trueCols : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)), GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.CharTie (numDatumOfParameters (I.rec7 l Z) L) (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (Pr := B.primes X) B.wts I.Ch I.glob I.sel := by
  intro B X I h l Z L
  exact ⟨h.ch_ok, rfl, rfl, ⟨I.C.eta, h.ch_tied⟩, h.weil, h.sel_ok⟩

end GlobalTheory.CoreHt
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)


theorem _root_.GlobalTheory.T.satakeTrivialBound_of_bounded_zonal_spherical_unitary : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.UnramDoublingInert → ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : Lˣ) (σ : L →+* L) (q n : ℕ), IsUnramInv (ϖ : L) σ q → ∀ (α : Fin (n / 2) → ℂˣ) (w : GU σ n → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsZonal (ϖ : L) q α w → (∃ C : ℝ, ∀ g, ‖w g‖ ≤ C) → GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q n α := by
  first | exact @GlobalTheory.ZonalBound.trivialBound_of_bounded | exact GlobalTheory.ZonalBound.trivialBound_of_bounded | (intros; apply GlobalTheory.ZonalBound.trivialBound_of_bounded <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.Core.Ht2

theorem host_fields_primes_ties : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (hX : B.fields.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)), (I.rec7 l Z).host.ccK = ⊤ ∧ GL3Theta.InducedCMType (I.rec7 l Z) ∧ GL3Theta.HostFieldConditions (I.rec7 l Z) ∧ B.fields.AbelianUnramifiedExtensionConditions ∧ (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G).Ok ∧ (∀ x : B.fields.K, B.embLL (star x) = starRingEnd ℂ (B.embLL x)) ∧ (B.primes X).Ok ∧ (B.primes X).PiGCong ∧ (B.primes X).cond = B.host.QS * B.host.q * B.host.d ∧ (∀ i, (B.primes X).g i = B.host.g i) ∧ B.wts.Ok := by
  intro B X I _ _ l Z
  exact ⟨B.toPre.ccK_top, GlobalTheory.InducedType.restrict_K _, Formalism.MainNotions.GL3Theta.cm_field_facts_hold _, (GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).1,
    seamOf_ok B (I.cols l) Z.W Z.V Z.S Z.N Z.G, B.starLL_cx, (GlobalTheory.BasePrimes.primes_ok B X).1, (GlobalTheory.BasePrimes.primes_ok B X).2,
    rfl, fun _ => rfl, B.wts_isOk⟩

end GlobalTheory.Core.Ht2
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.BaseCosetPt

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem lat_eq_of_carries {g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {N₁ N₂ : Submodule (𝓞 E) (Fin n → E)}
    (h₁ : Submodule.IsFullLattice E N₁) (h₂ : Submodule.IsFullLattice E N₂)
    (c₁ : Formalism.L2.Herm.Carries g (Formalism.L2.Col.stdLat E n) N₁) (c₂ : Formalism.L2.Herm.Carries g (Formalism.L2.Col.stdLat E n) N₂) :
    N₁ = N₂ := by
  have key : ∀ N : Submodule (𝓞 E) (Fin n → E), Submodule.IsFullLattice E N → ∀ x : Fin n → E,
      (x ∈ N ↔ (fun j => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x j)) ∈ Formalism.L2.Herm.hatL (F := F) N) := by
    intro N hN x
    let : Submodule.IsFullLattice E N := hN
    have hone := Formalism.UG.P.global_lattice_one_holds F E (Fin n) N (Module.Finite.iff_fg.mpr hN.fg) (Submodule.IsFullLattice.span_eq_top (A := E) (M := N))
    conv_lhs => rw [← hone]
    show (((1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) ∈ Formalism.L2.Herm.hatL (F := F) N ↔ _
    rw [inv_one, Units.val_one, Matrix.one_mulVec]
  ext x
  rw [key N₁ h₁, key N₂ h₂, c₁, c₂]

end Gen

section Pt

open _root_.Formalism.L2.Col Formalism.MainNotions Formalism.L2.DIV

variable {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)}

theorem frsF_symm_mem {u : Pr.Word} {j : ℕ} (p : ChPt (R := R) sel mu u j) (P : rowSG Pr sel mu) {w : Sp X.E (R.N j)}
    (hw : w ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.deco.1.N) : (frsF sel mu p P).symm w ∈ stdAt X.E (R.N j) P.1 := by
  have hfr := isFr_ptFr p P.1
  rw [← frsF_eq_ptFr sel mu p P] at hfr
  exact (hfr _).1 (by simpa using hw)

theorem frsF_mem {u : Pr.Word} {j : ℕ} (p : ChPt (R := R) sel mu u j) (P : rowSG Pr sel mu) {x : Sp X.E (R.N j)}
    (hx : x ∈ stdAt X.E (R.N j) P.1) : frsF sel mu p P x ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.deco.1.N := by
  have hfr := isFr_ptFr p P.1
  rw [← frsF_eq_ptFr sel mu p P] at hfr
  exact (hfr _).2 hx

theorem cosetIn_eq_of {u : Pr.Word} {j : ℕ} (r : PtAt R sel mu cst u j) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs)
    (y : Sp X.E (R.N j)) (e : rowSG Pr sel mu → ℤ) (he : e P = 0)
    (hY : r.1.2 = {z | z - y ∈ locLat (rowSG Pr sel mu) r.1.1.deco.1.N e}) :
    cosetIn r P = {z | z - (frsF sel mu r.1.1 P).symm y ∈ stdAt X.E (R.N j) P.1} := by
  classical
  apply Set.ext
  intro z
  simp only [cosetIn, if_pos hP, pow_zero, inv_one, one_smul, Set.mem_setOf_eq, hY]
  constructor
  · rintro ⟨y', hy', hz⟩
    have h1 : y' - y ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal r.1.1.deco.1.N := by
      have := (Submodule.mem_iInf _).1 hy' P
      simpa [Submodule.mem_comap, he] using this
    have := add_mem hz (frsF_symm_mem r.1.1 P h1)
    rwa [map_sub, sub_add_sub_cancel] at this
  · intro hz
    exact ⟨y, by simp, hz⟩

end Pt

end GlobalTheory.BaseCosetPt

namespace GlobalTheory.BaseCosetPt

open _root_.Formalism.L2.Col Formalism.MainNotions Formalism.L2.DIV

end GlobalTheory.BaseCosetPt
end
end

section

noncomputable section

namespace GlobalTheory.KerDia

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC

attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : Base} {X : PreX B.toPre}

def ent (I : TC B X) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) {b : (I.stp u a i).β} {b' : (I.stp u a (i + 1)).β}
    (p : (I.stp u a i).D b) (p' : (I.stp u a (i + 1)).D b') :
    (Fr B.fields.emb B.embLL (B.R.N i) → ℂ) →ₗ[ℂ] (Fr B.fields.emb B.embLL (B.R.N (i + 1)) → ℂ) :=
  (I.rho u a i b p * I.rho' u a i b' p') • (((I.chain l u a).divDe i).comp
    ((fnOf (Gr B.fields.emb B.embLL (B.R.N (i + 1))) 0 1 ∘ₗ jetMap (jetC I.J.cD (I.th u a i b b' p p')) 0 ∘ₗ
      polOf (Gr B.fields.emb B.embLL (B.R.N i)) 0 (fr0 B.fields.emb B.embLL (B.R.N i))).comp ((I.chain l u a).sharp i)))

theorem Kmap_eq (I : TC B X) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) (c : (I.stp u a i).Cl) (c' : (I.stp u a (i + 1)).Cl) :
    (I.chain l u a).Kmap i c c' = ent I l u a i ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c') := rfl

end GlobalTheory.KerDia
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Transport

def CongAt (B : Base) {a b : ℕ} (P : HeightOneSpectrum (𝓞 B.host.E)) (M₀ : ℕ) (y : TC.GA B a) (y' : TC.GA B b)
    (x x₀ : Formalism.L2.Col.HomE B.fields.E a b) : Prop :=
  ∀ r s, Valued.v (adAt B.host.F P
    ((HMul.hMul (HMul.hMul ((y'⁻¹ : TC.GA B b).1 : Matrix (Fin b) (Fin b) (Formalism.L2.DIV.AfE B.host.F B.host.E))
      ((LinearMap.toMatrix' x).map (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) : Matrix (Fin b) (Fin a) (Formalism.L2.DIV.AfE B.host.F B.host.E)))
      (y.1 : Matrix (Fin a) (Fin a) (Formalism.L2.DIV.AfE B.host.F B.host.E)) -
      ((LinearMap.toMatrix' x₀).map (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) : Matrix (Fin b) (Fin a) (Formalism.L2.DIV.AfE B.host.F B.host.E))) r s)) ≤
    Valued.v ((M₀ : ℕ) : P.adicCompletion B.host.E)

end GlobalTheory.Transport
end
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.isPointOfDecoratedLattice_unique : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))} (g : GL (Fin n) (Formalism.L2.DIV.AfE F E)) (p p' : Formalism.L2.Col.DecoF E n ST SG Q), GlobalTheory.Mem.Col2.IsPtOf hc g p → GlobalTheory.Mem.Col2.IsPtOf hc g p' → p = p' := by
  first | exact @GlobalTheory.Mem.Col2.PtUniq.isPtOf_unique | exact GlobalTheory.Mem.Col2.PtUniq.isPtOf_unique | (intros; apply GlobalTheory.Mem.Col2.PtUniq.isPtOf_unique <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexOrder

namespace GlobalTheory.KJReal

variable {D : D7}

theorem detPlus_one_one {m n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) (b : Matrix (Fin m) (Fin m) ℂ) :
    GlobalTheory.WeilParts.detPlus 1 1 a b = b.det ^ n * a.det ^ m := by
  unfold GlobalTheory.WeilParts.detPlus
  have e2 : (1 + 1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) = (2 : ℂ) • 1 := by
    rw [two_smul]
  rw [Matrix.transpose_one, Matrix.one_kronecker_one, sub_self, smul_zero, add_zero, e2, Matrix.smul_mul,
    Matrix.one_mul, smul_smul, show (1 / 2 * 2 : ℂ) = 1 by norm_num, one_smul, Matrix.det_kronecker,
    Matrix.det_transpose, Fintype.card_fin, Fintype.card_fin]

theorem exp_identity (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (e mS mT : ℤ) (nS nT : ℕ) (hS : (nS : ℤ) = mS + mS)
    (hT : (nT : ℤ) = mT + mT) :
    (a ^ (e - mT))⁻¹ * b ^ (e - mS) * (b ^ nS * a⁻¹ ^ nT) = a ^ (-e - mT) * b ^ (e + mS) := by
  rw [inv_pow, ← zpow_natCast b, ← zpow_natCast a, ← zpow_neg a, ← zpow_neg a]
  calc (a ^ (-(e - mT)) * b ^ (e - mS) * (b ^ (nS : ℤ) * a ^ (-(nT : ℤ))))
      = a ^ (-(e - mT)) * a ^ (-(nT : ℤ)) * (b ^ (e - mS) * b ^ (nS : ℤ)) := by ring
    _ = a ^ (-(e - mT) + -(nT : ℤ)) * b ^ (e - mS + (nS : ℤ)) := by rw [← zpow_add₀ ha, ← zpow_add₀ hb]
    _ = a ^ (-e - mT) * b ^ (e + mS) := by
      congr 2
      · rw [hT]; ring
      · rw [hS]; ring

end GlobalTheory.KJReal

namespace GlobalTheory.KJReal

end GlobalTheory.KJReal
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

theorem _root_.GlobalTheory.T.unramifiedDoublingIntegral_twisted_place_eigenvector : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (r t l : ℕ) (ξ μ₀ : kˣ →* ℂˣ), IsUnitaryChar ξ → IsTame ξ → ¬ IsUnram ξ → IsUnram μ₀ → IsUnitaryChar μ₀ → ∀ (B : Multiset ℂˣ) (α : Fin (l * t) → ℂˣ) (ρ : ℝ), Finset.univ.val.map α = B.map (· * ((μ₀ * ξ) ϖ)⁻¹) → (∀ x, ‖(α x : ℂ)‖ ≤ (resCard k : ℝ) ^ ρ ∧ ‖(α x : ℂ)‖⁻¹ ≤ (resCard k : ℝ) ^ ρ) → ∀ H : GL (Fin r ⊕ Blocks l t) k → ℝ, IsHgt ϖ H → ∀ [MeasurableSpace (GL (Fin r ⊕ Blocks l t) k)] [BorelSpace (GL (Fin r ⊕ Blocks l t) k)] (m : Measure (GL (Fin r ⊕ Blocks l t) k)) [m.IsHaarMeasure], m (parahoric k (Fin r) (Blocks l t)) = 1 → ∀ c : GL (Fin r ⊕ Blocks l t) k → ℂ, (∀ g, c g = ip ν (om (μ₀ * ξ) g (1 : GL (Fin r ⊕ Blocks (l + 1) t) k) (datum ξ)) (datum ξ)) → c 1 ≠ 0 ∧ ∃ ζ : GL (Fin r ⊕ Blocks l t) k → ℂ, (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin r ⊕ Blocks l t) k) V) (x : V) (ℓ : V →ₗ[ℂ] ℂ), IsGen π ξ ϖ B x → IsCoType π ξ ℓ → ∀ g, starRingEnd ℂ (c g) * ℓ (π g x) = starRingEnd ℂ (c 1) * ζ g * ℓ x) ∧ (∀ g ∈ parahoric k (Fin r) (Blocks l t), ζ g = 1) ∧ ∀ s : ℂ, ρ - 1 / 2 < s.re → Integrable (fun g => ζ g * (H g : ℂ) ^ (s - (t : ℂ) / 2)) m ∧ ∫ g, ζ g * (H g : ℂ) ^ (s - (t : ℂ) / 2) ∂m = lFactor (resCard k) α (s + 1 / 2) * lFactor (resCard k) α⁻¹ (s + 1 / 2) * invNormFactor (resCard k) (l * t) s := by
  first | exact @GlobalTheory.TwistedZeta.local_zeta_twisted | exact GlobalTheory.TwistedZeta.local_zeta_twisted | (intros; apply GlobalTheory.TwistedZeta.local_zeta_twisted <;> assumption)
end

section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.collisionAbsSum_bound_of_two_rowBounds : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ CT C : ℝ, 408 * (Real.exp 1 * Real.pi) ≤ C → CT ≤ C → ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (u : D.what₂.Word) (T : TermTie D) (Z : LoopTie D large₂ T u u 1) (C' Cl Cg cb Cu cT C0 : ℝ), thr ≤ C' → thr ≤ Cl → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → ConcTie X Y → (Y.tO u u).AbsConv → TieAt hF hI large₂ u T Z → UnitaryVolumeMass.FormAt D u → BridgeLemma.RowsND T Z C → BridgeLemma.RowsDeg T Z C → CollS Y u := by
  first | exact @GlobalTheory.Core.Deg.collS_of_rowBounds | exact GlobalTheory.Core.Deg.collS_of_rowBounds | (intros; apply GlobalTheory.Core.Deg.collS_of_rowBounds <;> assumption)
end

section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.nondegenerateCollision_rowBound_at_parameters : ∀ CT cH cV Ca C2 Ch c C : ℝ, 1 ≤ c → |cH| + 2 ≤ c → |cV| + 2 ≤ c → 0 ≤ Ch → c ≤ C → 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C → ∀ (D : D7) (large₂ : SizeData₂ D) (u : D.what₂.Word) (T : TermTie D) (Z : LoopTie D large₂ T u u 1) (C' Cl Cg cb Cu cT C0 : ℝ), |C2| ≤ C' → Cnt.Hyp D large₂ u u C' Cl Cg cb Cu cT CT C0 1 → UnitaryVolumeMass.MeanFlagPairCount D large₂ u u C' Cl Cg cb Cu cT CT C0 1 3 c → UnitaryVolumeMass.stHH D large₂ u u C' Cl Cg cb Cu cT CT C0 1 cH → UnitaryVolumeMass.stVol D large₂ T u u 1 Z C' Cl Cg cb Cu cT CT C0 1 cV → AmpAt D large₂ C' Cl Cg cb Cu cT CT C0 (9 * c + 3) Ca C2 Ch 1 → SmallAt D large₂ C' Cl Cg cb Cu cT CT C0 1 → BridgeLemma.TermPtsTie T Z → @BridgeLemma.LatticeDeterminantFactorization D T u u → BridgeLemma₂.wordPairEntriesInLattice T u u → BridgeLemma.RowsND T Z C := by
  first | exact @GlobalTheory.Core.Deg.rowsND_one_record | exact GlobalTheory.Core.Deg.rowsND_one_record | (intros; apply GlobalTheory.Core.Deg.rowsND_one_record <;> assumption)
end
