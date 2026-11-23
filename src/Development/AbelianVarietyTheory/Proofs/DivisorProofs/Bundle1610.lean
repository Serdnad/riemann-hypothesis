module

public import Aesop.BuiltinRules
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1582
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle016
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle013
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
public import Formalism.FockGram.StatementFock
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1556
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIntertwinerUniqueScalar
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle304
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle098
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle181
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1559
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.ConstantTerm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1560
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
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle876
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle005
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle266
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.AutomorphicForms.Bundle003
import GroundTheory.GlobalFields.KummerTheory.LocalIndex

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaGAGA

variable {A : Over (Sp ℂ)} [GrpObj A] {M : LB A.left} {g : ℕ}

theorem top_le_of_lbPow (u : HolUnif A M g) (k : ℕ) (j : (lbPow M k).ι) {z : Fin g → ℂ}
    (hz : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow M k).U j) : ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U (j PUnit.unit) :=
  GlobalTheory.top_le_preimage_mono _ (GlobalTheory.Cartier.lbPow_U M k j).le hz

def powFrame (u : HolUnif A M g) (k : ℕ) : HolUnif A (lbPow M k) g where
  ex := u.ex
  ex_add := u.ex_add
  ex_onto := u.ex_onto
  Λ := u.Λ
  ker := u.ker
  discrete := u.discrete
  full := u.full
  hol := u.hol
  fr j z := u.fr (j PUnit.unit) z ^ k
  fr_hol j := ((u.fr_hol (j PUnit.unit)).mono fun _ hz => top_le_of_lbPow u k j hz).pow k
  fr_ne j z hz := pow_ne_zero _ (u.fr_ne _ z (top_le_of_lbPow u k j hz))
  fr_compat i j z hz := GlobalTheory.ThetaBundleSec.fr_pow_compat u z k i j
    ((GlobalTheory.top_le_preimage_inf _ _ _).1 hz).1 ((GlobalTheory.top_le_preimage_inf _ _ _).1 hz).2

theorem exists_isFnPow : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ),
    M.IsLB → u.IsAH Hm χ → ∀ (k : ℕ) (θ : (Fin g → ℂ) → ℂ), u.IsThetaFn Hm χ k θ → ∃ s, u.IsFnPow k s θ := by
  intro g A _ hA M u Hm χ hM hAH k θ hθ
  have := hA.comm
  have hp : IsProjOver A.hom := (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver A.hom).1
    (GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme ℂ A hA)
  obtain ⟨s, hs⟩ := GlobalTheory.HolUnifSec.exists_isFn (powFrame u k) hA hp (GlobalTheory.isLB_lbPow hM k) hθ.1 (by
    intro l hl j z hz
    have hz' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U (j PUnit.unit) := top_le_of_lbPow u k j hz
    have h1 := hθ.2 ⟨l, hl⟩ z
    have h2 := hAH.2.2.2 ⟨l, hl⟩ _ z hz'
    change θ (z + l) * u.fr (j PUnit.unit) (z + l) ^ k = θ z * u.fr (j PUnit.unit) z ^ k
    simp only [hermForm] at h1
    change θ (z + l) = _ at h1
    change u.fr (j PUnit.unit) z = _ * u.fr (j PUnit.unit) (z + l) at h2
    rw [h1, h2, mul_pow]
    ring)
  exact ⟨s, hs⟩

end GlobalTheory.ThetaGAGA
end
end

section

open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.exists_kFiniteModule_irreducible_unitary : CompanionTheory.D.LK.KModExists := by
  first | exact @GlobalTheory.CompanionTheory.KModExistsStep.kModExists_holds | exact GlobalTheory.CompanionTheory.KModExistsStep.kModExists_holds | (intros; apply GlobalTheory.CompanionTheory.KModExistsStep.kModExists_holds <;> assumption)
end

section

open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.kStab_iff_isKStableOn_finite_vectors : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D), CompleteSpace H → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → IsKMod ε σ D E → ∀ U : Submodule ℂ D, FiniteDimensional ℂ U → (KStab ε E U ↔ IsKStableOn ε σ (U.map D.subtype)) := by
  first | exact @GlobalTheory.KFinStab.kStab_iff_kStableOn | exact GlobalTheory.KFinStab.kStab_iff_kStableOn | (intros; apply GlobalTheory.KFinStab.kStab_iff_kStableOn <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

namespace GlobalTheory.AdelicScalar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev l2 {X : Type} [MeasurableSpace X] (μ : Measure X) (𝓕 : Set X) (φ₁ φ₂ : X → ℂ) : ℂ := Lift.pet μ 𝓕 φ₁ φ₂

abbrev Upq (W : HSp D) (ρ : D.what₂.Tau) : Type := UpqT (W.sig (tauE D ρ)).1 (W.sig (tauE D ρ)).2

abbrev Frames (W : HSp D) : Type :=
  ∀ ρ : D.what₂.Tau, Matrix (Fin (W.sig (tauE D ρ)).1 ⊕ Fin (W.sig (tauE D ρ)).2) (Fin W.rank) ℂ

def IsFrames (W : HSp D) (A : Frames W) : Prop :=
  ∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq (W.sig (tauE D ρ)).1 (W.sig (tauE D ρ)).2 * A ρ = gramAt D W ρ

def conjFrame {p q n : ℕ} (Gm : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ)
    (b : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Gm⁻¹ * (Aᴴ * Formalism.UG.Jpq p q * b * A : Matrix (Fin n) (Fin n) ℂ)

def realMat (W : HSp D) (A : Frames W) (ρ : D.what₂.Tau) (b : Upq W ρ) : Matrix (Fin W.rank) (Fin W.rank) ℂ :=
  conjFrame (gramAt D W ρ) (A ρ) (UpqT.mat b)

def realElt (θ : Datum.InfFam D) (W : HSp D) (g : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) : GA D W :=
  ((Finset.univ : Finset D.what₂.Tau).toList.map fun ρ => atTau θ W ρ (g ρ)).prod

abbrev FinCos (W : HSp D) (K : Subgroup (GA D W)) : Type := GfC W ⧸ K.subgroupOf (GfC W)

def FinCos.rep {W : HSp D} {K : Subgroup (GA D W)} (c : FinCos W K) : GA D W := (c.out : GfC W)


open Classical in
def quadSign (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : ℝ :=
  if (Ideal.primesOver v.asIdeal (𝓞 D.host.E)).ncard = 2 then 1 else -1

def quadTerm (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (i : ℕ) : ℝ :=
  quadSign D v ^ i / (Ideal.absNorm v.asIdeal : ℝ) ^ i

def dLoc (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : ℝ := ∏ i ∈ Finset.Ioc D.R.t D.R.nV, (1 - quadTerm D v i)⁻¹

def dOff (D : D7) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : ℝ :=
  ∏' p : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ S} × Finset.Ioc D.R.t D.R.nV, (1 - quadTerm D p.1.1 p.2.1)⁻¹

def eulerOff (D : D7) (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (x : HeightOneSpectrum (𝓞 D.host.E) → Fin D.R.r → ℂ) : ℂ :=
  ∏' p : {w : HeightOneSpectrum (𝓞 D.host.E) // OffS D S w} × Fin D.R.r, (1 - x p.1.1 p.2)⁻¹


variable (D) in
def degAt (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) : ℕ :=
  ∑ n ∈ Finset.range (pW D i ρ), aPlAt D i σ ρ n + ∑ n ∈ Finset.range (qW D i ρ), aMiAt D i σ ρ n

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

abbrev levW (i : Fin D.R.m) : Subgroup (GA D (Wc D i)) := Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv)

abbrev levV (i : Fin D.R.m) (t : T) (P : LevelP R.Pg D.R.r ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) :
    Subgroup (GL (Fin (Vc D i).rank) (Lev.EAf D)) := lev D.sp.cm (Vc D i).gram (R.βV i) (datV i R.Pg (R.Q t) P m)

abbrev petW (i : Fin D.R.m) (F₁ F₂ : GA D (Wc D i) → ℂ) : ℂ := l2 (R.νW i) (R.fdW i) F₁ F₂

def upLift (i : Fin D.R.m) (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ))
    (φ : Datum.WO (Vc D i) (Wc D i) → ℂ) (F : GA D (Wc D i) → ℂ) (h : GA D (Vc D i)) : ℂ :=
  petW R i (fun g => Datum.thetaKO ω h g φ) F

def IsLiftData (F : Face D A) (i : Fin D.R.m) (t : T) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (P : LevelP R.Pg D.R.r ℂ)
    (cμ cη : (AE D)ˣ →* Circle) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ))
    (BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : Datum.WO (Vc D i) (Wc D i) → ℂ)
    (c : CoefA (Vc D i)) (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) : Prop :=
  R.Char F ∧ PrimeToHost R t ∧ IsEmbOverK D σ s ∧ IsLocalLevel P ∧ IsConjChars R i t s cμ cη m ∧
    Datum.IsWeilDatumO R.ψ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) ω ∧
    (∀ ρ, Datum.IsONBasis (gramAt D (Wc D i) ρ) (cart (R.MW i σ) ρ) (BW ρ) (pW D i ρ)) ∧
    IsLevelVec R.ψ R.θ (Vc D i) (Wc D i) (cart (R.MW i σ)) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) (R.datWp i P) (R.Q t) m f₀ f ∧
    Lift.PtTheta R.ψ (Vc D i) (Wc D i) (ptAt R i σ BW f) ∧ c.Is ∧
    IsIoW R.θ (R.MW i σ) c ω (ptAt R i σ BW f) (deltaAtEmb D i σ) io




variable (D) in
def DeltaNorm : Prop :=
  ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), Formalism.E.fock (deltaAtEmb D i σ) (deltaAtEmb D i σ) =
    ∏ ρ : D.what₂.Tau, ((hookOf (pW D i ρ) (aPlAt D i σ ρ) : ℂ) * (hookOf (qW D i ρ) (aMiAt D i σ ρ) : ℂ))




variable (D) in
def MassLower : Prop :=
  ∀ i : Fin D.R.m, (Vc D i).IsPosDef → 1 / ((NumberField.Units.torsionOrder D.host.E : ℝ) ^ D.R.nV * (D.R.nV.factorial : ℝ)) ≤
    GlobalTheory.Mass.unitaryMass D.sp.cm.sig (Vc D i).gram (GlobalTheory.Mass.Levels.latStab (Vc D i))

end GlobalTheory.AdelicScalar

end
end

section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

theorem _root_.GlobalTheory.T.exists_archimedean_adele_CM_prescribed_embedding_values : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (z : InfinitePlace F → ℂ), ∃ a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evI F) a ∧ ∀ w, piInf (τ w) a = z w := by
  first | exact @GlobalTheory.PolRangeInf.exists_at_inf_values | exact GlobalTheory.PolRangeInf.exists_at_inf_values | (intros; apply GlobalTheory.PolRangeInf.exists_at_inf_values <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

theorem _root_.GlobalTheory.T.schrodinger_intertwiner_l2_constant : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : mixedEmbedding.mixedSpace F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (mixedEmbedding.mixedSpace F) ℂ),
    (∀ a, ψ a = Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) a : ℝ))) →
    ∀ (T : SInf F κ →L[ℂ] SInf F κ)
      (A : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) →
        (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      (∀ w (f g : SInf F κ), (g : (κ → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ w f →
        (T g : (κ → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ (A w) (T f)) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (κ → mixedEmbedding.mixedSpace F) (borel _),
        @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ f f' : SInf F κ,
          @integral _ ℂ _ _ (borel _) μ (fun x => T f x * starRingEnd ℂ (T f' x)) =
            (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => f x * starRingEnd ℂ (f' x)) := by
  first | exact @GlobalTheory.SvNForm.schrodinger_intertwiner_l2_const | exact GlobalTheory.SvNForm.schrodinger_intertwiner_l2_const | (intros; apply GlobalTheory.SvNForm.schrodinger_intertwiner_l2_const <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal


theorem _root_.GlobalTheory.T.local_intertwiner_unique_scalar : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) [Invertible (2 : Fv F v)] (κ : Type) [Fintype κ]
    (ψv : AddChar (Fv F v) ℂ), Continuous ψv → ψv ≠ 1 →
    ∀ (T : ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ) (A : (κ → Fv F v) × (κ → Fv F v) → (κ → Fv F v) × (κ → Fv F v)),
      (∀ φ ∈ SB (κ → Fv F v), T φ ∈ SB (κ → Fv F v)) →
      (∀ w, ∀ φ ∈ SB (κ → Fv F v), T (schr ψv w φ) = schr ψv (A w) (T φ)) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (κ → Fv F v) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∀ φ ∈ SB (κ → Fv F v), ∀ φ' ∈ SB (κ → Fv F v),
          @integral _ ℂ _ _ (borel _) μ (fun x => T φ x * starRingEnd ℂ (T φ' x)) =
            (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => φ x * starRingEnd ℂ (φ' x)) := by
  first | exact @GlobalTheory.CompactOpenLattice.inner_eq_const_mul | exact GlobalTheory.CompactOpenLattice.inner_eq_const_mul | (intros; apply GlobalTheory.CompactOpenLattice.inner_eq_const_mul <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertChars

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem eq_mul_of_at {v : Pl (F := F)} {y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)} (hy : At (evFin F v) y) :
    y = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.EmbChart.atPlace v 1) * y := by
  have h0 : evFin F v (1 - GlobalTheory.EmbChart.atPlace v 1) = 0 := by
    rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self]
  have h1 : (1 - GlobalTheory.EmbChart.atPlace v 1) • y = 0 := hy _ h0
  rw [Algebra.smul_def, map_sub, map_one, sub_mul, one_mul, sub_eq_zero] at h1
  exact h1

private lemma tensorProduct_map_eq_zero_of_at_of_atPlace_eq_zero {R : Type} [CommRing R] [Algebra F R] {v : Pl (F := F)} (φ : AF F →ₐ[F] R)
    (hφ : φ (GlobalTheory.EmbChart.atPlace v 1) = 0) {y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)} (hy : At (evFin F v) y) :
    Algebra.TensorProduct.map φ (AlgHom.id F E) y = 0 := by
  rw [eq_mul_of_at hy, map_mul, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul,
    Algebra.algebraMap_self_apply, hφ, TensorProduct.zero_tmul, zero_mul]

theorem eq_ideleAt_of_at {v : Pl (F := F)} (z : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ) (hz : At (evFin F v) ((z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) - 1)) :
    z = GlobalTheory.Doubling.ideleAt F E v (GlobalTheory.Doubling.unitFin F E v z) := by
  have hev : ∀ {R : Type} [CommRing R] [Algebra F R] (φ : AF F →ₐ[F] R), φ (GlobalTheory.EmbChart.atPlace v 1) = 0 →
      Algebra.TensorProduct.map φ (AlgHom.id F E) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = 1 := by
    intro R _ _ φ hφ
    have h := tensorProduct_map_eq_zero_of_at_of_atPlace_eq_zero φ hφ hz
    rwa [map_sub, map_one, sub_eq_zero] at h
  apply GlobalTheory.Doubling.idele_ext
  · intro w
    rw [GlobalTheory.Doubling.unitInf_ideleAt]
    ext
    refine hev (evInf F w) ?_
    rw [GlobalTheory.EmbChart.atPlace_apply]
    show GlobalTheory.AutFunCompare.evW w (fstA F (pairA F 0 (singleFin v 1))) = 0
    exact map_zero _
  · intro u
    by_cases huv : u = v
    · subst huv
      rw [GlobalTheory.Doubling.unitFin_ideleAt_self]
    · rw [GlobalTheory.Doubling.unitFin_ideleAt_ne huv]
      ext
      refine hev (evFin F u) ?_
      rw [GlobalTheory.EmbChart.atPlace_apply]
      exact evalV_singleFin_ne huv 1

end GlobalTheory.InertChars

namespace GlobalTheory.InertChars

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem locIdele_eq_of_inert {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w)
    (α β : Chr F E) (hres : ∀ b : (AF F)ˣ, α (ideleMap F E b) = β (ideleMap F E b))
    (hα : UnrAt α w) (hβ : UnrAt β w) (y : (w.adicCompletion E)ˣ) :
    α (locIdele F w y) = β (locIdele F w y) := by
  unfold UnrAt at hα hβ
  have h := GlobalTheory.LFun.under_eq_of_isInertAt hw
  obtain ⟨a, ha⟩ := GlobalTheory.LFun.InertValue.exists_isUnifAt hw h
  have hπ : α (locIdele F w (Units.map (complMap h).toMonoidHom a)) =
      β (locIdele F w (Units.map (complMap h).toMonoidHom a)) := by
    rw [GlobalTheory.LFun.InertValue.locIdele_complMap hw h a]
    exact hres _
  generalize Units.map (complMap h).toMonoidHom a = π at ha hπ
  have hunit : ∀ u : (w.adicCompletion E)ˣ, Valued.v (u : w.adicCompletion E) = 1 →
      α (locIdele F w u) = β (locIdele F w u) := by
    intro u hu
    have h1 : locChar α w u = 1 := hα u hu
    have h2 : locChar β w u = 1 := hβ u hu
    rw [← h2] at h1
    have h3 := congrArg (fun x : ℂˣ => (x : ℂ)) h1
    simp only [locChar, MonoidHom.comp_apply, Circle.toUnits_apply, Units.val_mk0] at h3
    exact Circle.ext h3
  have key : ∀ (u : (w.adicCompletion E)ˣ) (n : ℤ), Valued.v (u : w.adicCompletion E) = 1 →
      α (locIdele F w (u * π ^ n)) = β (locIdele F w (u * π ^ n)) := by
    intro u n hu'
    rw [map_mul, map_mul, map_mul, map_zpow, map_zpow, map_zpow, hunit u hu', hπ]
  have hy0 : Valued.v (y : w.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).mpr y.ne_zero
  obtain ⟨k, hk⟩ : ∃ k : ℤ, Valued.v (y : w.adicCompletion E) = WithZero.exp k :=
    ⟨_, (WithZero.exp_log hy0).symm⟩
  have hu : Valued.v ((y * π ^ k : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := by
    have hπv : Valued.v (π : w.adicCompletion E) = WithZero.exp (-1 : ℤ) := ha
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hπv, hk, ← WithZero.exp_zsmul,
      ← WithZero.exp_add, smul_neg, smul_eq_mul, mul_one, add_neg_cancel, WithZero.exp_zero]
  have hy : y = (y * π ^ k) * π ^ (-k) := by
    rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  rw [hy]
  exact key _ _ hu

theorem beta_eq_alpha_of_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
      ∀ z : (AE F E)ˣ, At (evFin F v) ((z : AE F E) - 1) → X.β z = X.α z := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hw hv z hz
  have h := GlobalTheory.LFun.under_eq_of_isInertAt hw
  have hpow : ((-1 : ℂ)) ^ a = (-1) ^ a' := by
    have he := hT.geo.even
    rw [Nat.even_add] at he
    rcases Nat.even_or_odd a with ha | ha
    · rw [ha.neg_one_pow, (he.mp ha).neg_one_pow]
    · have ha' : Odd a' := Nat.not_even_iff_odd.mp (fun h' => Nat.not_even_iff_odd.mpr ha (he.mpr h'))
      rw [ha.neg_one_pow, ha'.neg_one_pow]
  have hres : ∀ b : (AF F)ˣ, X.β (ideleMap F E b) = X.α (ideleMap F E b) := by
    intro b
    have e1 : ((X.α (ideleMap F E b) : Circle) : ℂ) = _ := hT.chars.resα b
    have e2 : ((X.β (ideleMap F E b) : Circle) : ℂ) = _ := hT.chars.resβ b
    apply Circle.ext
    rw [e1, e2, hpow]
  have hnot : ¬ (w.under (𝓞 F) ∈ (X.T : Set (Pl (F := F)))) := by
    rw [h]
    exact hv
  rw [eq_ideleAt_of_at z hz, GlobalTheory.LFun.ideleAt_eq_locIdele_of_isInertAt h hw]
  exact locIdele_eq_of_inert hw X.β X.α hres (hT.chars.unrβ w hnot) (hT.chars.unrα w hnot) _

end GlobalTheory.InertChars
end
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

theorem _root_.GlobalTheory.T.rational_boundedInfinite_compactFinite_polyCount : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], ∃ m : ℕ, ∀ Kf : Set (Af E), IsCompact Kf → ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → {ξ : E | ‖pInf E (algebraMap E (Ad E) ξ)‖ ≤ T ∧ pFin E (algebraMap E (Ad E) ξ) ∈ Kf}.Finite ∧ ({ξ : E | ‖pInf E (algebraMap E (Ad E) ξ)‖ ≤ T ∧ pFin E (algebraMap E (Ad E) ξ) ∈ Kf}.ncard : ℝ) ≤ C * T ^ m := by
  first | exact @GlobalTheory.rat_bounded_compact_polynomial | exact GlobalTheory.rat_bounded_compact_polynomial | (intros; apply GlobalTheory.rat_bounded_compact_polynomial <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

theorem _root_.GlobalTheory.T.exists_compact_coneDiagonal_conj_upperTriangular : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ω : Set (GL (Fin a) (Cinf E))), IsCompact ω → (∀ b ∈ ω, b.val.BlockTriangular id) → ∀ t : ℝ, 0 < t → ∃ Ω : Set (GL (Fin a) (Cinf E)), IsCompact Ω ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∀ b ∈ ω, d⁻¹ * b * d ∈ Ω := by
  first | exact @GlobalTheory.upperCone_conj_compact | exact GlobalTheory.upperCone_conj_compact | (intros; apply GlobalTheory.upperCone_conj_compact <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

theorem _root_.GlobalTheory.T.exists_height_mul_le_of_isCompact : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ω : Set (GL (Fin a) (Cinf E))), IsCompact Ω → ∃ B : ℝ, 1 ≤ B ∧ ∀ c ∈ Ω, ∀ y : GL (Fin a) (Cinf E), height (y * c) ≤ B * height y := by
  first | exact @GlobalTheory.AutGrowth.height_mul_le_of_isCompact | exact GlobalTheory.AutGrowth.height_mul_le_of_isCompact | (intros; apply GlobalTheory.AutGrowth.height_mul_le_of_isCompact <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix

theorem _root_.GlobalTheory.T.isCuspidal_of_isCuspForm' : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsCuspForm φ → GroundTheory.Automorphic.AutomorphicForm.IsCuspidal (K := E) (n := a) φ.1 := by
  first | exact @GlobalTheory.CuspRep.IsCuspForm.constantTerm_eq_zero | exact GlobalTheory.CuspRep.IsCuspForm.constantTerm_eq_zero | (intros; apply GlobalTheory.CuspRep.IsCuspForm.constantTerm_eq_zero <;> assumption)
end
