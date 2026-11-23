module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDarbouxComplexStructureTwoInvolutions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1347
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1588
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle246
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle028
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqClassSumOfHom
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle247
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle317
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle306
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle249
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle250
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle252
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1449
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle170
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010

@[expose] public section

section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix


theorem _root_.GlobalTheory.T.exists_normClass_of_rationalIsometry_traceForm : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (P : PPol σ n) (J : Matrix (Fin n) (Fin n) E) (φ : Fld P ≃ₗ[E] (Fin n → E)) (x : Fld P), x ≠ 0 → star' P x = x → (∀ y y', Formalism.UG.hform (σ : E →+* E) J (φ y') (φ y) = Algebra.trace E (Fld P) (x * y * star' P y')) → ∀ γ : GRat σ J, (∀ y, γ.1.1 *ᵥ φ y = φ (alpha P * y)) → ∃ q, HasCls P F J (diagH σ J F γ) q := by
  first | exact @GlobalTheory.RatCls.hasCls_of_ratIsom | exact GlobalTheory.RatCls.hasCls_of_ratIsom | (intros; apply GlobalTheory.RatCls.hasCls_of_ratIsom <;> assumption)
end

section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

theorem _root_.GlobalTheory.T.rationalNormClasses_eq_local_unramifiedCM : ∀ (E : Type) [Field E] [NumberField E] (F : Subfield E) [NumberField F] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → (∀ q q' : Cls P F, q ∈ XSet P F J → q' ∈ XSet P F J → (∀ v : HeightOneSpectrum (𝓞 F), ∃ a : Cls P (Fv F v), MapsCls P (k := F) (Algebra.ofId F (Fv F v)) q a ∧ MapsCls P (k := F) (Algebra.ofId F (Fv F v)) q' a) → (∀ w : InfinitePlace F, ∃ a : Cls P w.Completion, MapsCls P (k := F) (Algebra.ofId F w.Completion) q a ∧ MapsCls P (k := F) (Algebra.ofId F w.Completion) q' a) → q = q') ∧ ∀ (qf : ∀ v : HeightOneSpectrum (𝓞 F), Cls P (Fv F v)) (qa : ∀ w : InfinitePlace F, Cls P w.Completion), (∀ v, qf v ∈ XSet P (Fv F v) J) → (∀ w, qa w ∈ XSet P w.Completion J) → (∀ᶠ v in cofinite, qf v = 1) → ∃ q : Cls P F, q ∈ XSet P F J ∧ (∀ v : HeightOneSpectrum (𝓞 F), MapsCls P (k := F) (Algebra.ofId F (Fv F v)) q (qf v)) ∧ ∀ w : InfinitePlace F, MapsCls P (k := F) (Algebra.ofId F w.Completion) q (qa w) := by
  first | exact @GlobalTheory.TrEll.Hasse.rational_eq_local | exact GlobalTheory.TrEll.Hasse.rational_eq_local | (intros; apply GlobalTheory.TrEll.Hasse.rational_eq_local <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

theorem _root_.GlobalTheory.T.scalarHypotheses_of_topRows : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → HostHyp D → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → D.host.ccK = ⊤ → FWT.QGuard R.toRealDat → GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R.toRealDat → Given R.toRealDat F.lv2 := by
  first | exact @GlobalTheory.GivenOfTop.given_of_top | exact GlobalTheory.GivenOfTop.given_of_top | (intros; apply GlobalTheory.GivenOfTop.given_of_top <;> assumption)
end

section

open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacLn

theorem _root_.GlobalTheory.T.exists_darboux_complex_structure_two_involutions : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (θA : InfinitePlace F → Matrix α α ℂ)
    (θB : InfinitePlace F → Matrix β β ℂ) (ε ε' : InfinitePlace F → ℤˣ), IsCMExt F E σ →
    (∀ w, θA w * θA w = 1) → (∀ w, θB w * θB w = 1) →
    ∃ (J e : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
        ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))
      (e' : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F)),
      (∀ y, J (J y) = -y) ∧ (∀ y, e (e y) = e y) ∧ (∀ y, J (e y) = e (J y)) ∧ (∀ y, (e y).1 = e' y.1) ∧
      (∀ y x, trPair F κ x (e y).2 = trPair F κ (e' x) y.2) ∧
      ∀ y, ∃ u u' u₁ : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
        At (evI F) u ∧ At (evI F) u' ∧ At (evI F) u₁ ∧
        (∀ w, u'.map (piInf (τ w)) = (((ε' w : ℤ) : ℂ) * Complex.I) • (θA w * u.map (piInf (τ w)) * (θB w)ᵀ)) ∧
        (∀ w, u₁.map (piInf (τ w)) = (((ε w : ℤ) : ℂ) * Complex.I) • (θA w * u.map (piInf (τ w)) * (θB w)ᵀ)) ∧
        coord d u = y ∧ coord d u' = J (y - (2 : ℝ) • e y) ∧ coord d u₁ = J y := by
  first | exact @GlobalTheory.SignInvolDarboux.exists_bridge | exact GlobalTheory.SignInvolDarboux.exists_bridge | (intros; apply GlobalTheory.SignInvolDarboux.exists_bridge <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVac

theorem gen_diag_anti_split_herm : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (V : Spc F E d) (r s : ℕ), B.IsGood σ → V.IsHerm σ B r s →
    ∀ (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ H : Subgroup (GlobalTheory.DblVac.UD σ V),
      (∀ p ∈ GlobalTheory.DblVac.KD σ V v, p ∈ GlobalTheory.DblVac.PDiag σ V → p ∈ H) →
      (∀ p ∈ GlobalTheory.DblVac.KD σ V v, p ∈ GlobalTheory.DblVac.PAnti σ V → p ∈ H) → ∀ g ∈ GlobalTheory.DblVac.KD σ V v, g ∈ H := by
  intro F E _ _ _ _ _ σ B d V r s hB hV v hv hψ h2 H hD hA g hg
  obtain ⟨Y, hYat, hYlat, hYadm, M, hM, hMlat⟩ := GlobalTheory.T.exists_admissible_unipotent_at_split_place GlobalTheory.T.exists_isUnit_det_add_mul_of_fromBlocks_localRing σ B V r s hB hV v hv hψ h2 g hg
  obtain ⟨p, hpK, hpD, hp⟩ := GlobalTheory.T.exists_unipotent_doubledStabilizer_adds_diagonalBlock σ V v h2 Y hYat hYlat hYadm
  obtain ⟨hpgK, hpg⟩ := hp g hg
  have hbig : GlobalTheory.DblVac.BigCell V v (p * g) := ⟨M, by rw [hpg]; exact hM, hMlat⟩
  obtain ⟨q, hqK, hqA, p', hp'K, hp'D, he⟩ := GlobalTheory.T.doubledVacuumStabilizer_gaussDecomposition_bigCell σ V v h2 (p * g) hpgK hbig
  have hg' : g = p⁻¹ * (q * p') := by rw [← he]; group
  rw [hg']
  exact H.mul_mem (H.inv_mem (hD p hpK hpD)) (H.mul_mem (hA q hqK hqA) (hD p' hp'K hp'D))

end GlobalTheory.DblVac
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.adelicLiftDatum_of_conjugate_liftDatum : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ gramR c0R c0L, GlobalTheory.GalLift.Comparison₂ R gramR c0R c0L → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjForms R i σ (c0L i) c c₁ H j → ∀ μ' η', ChiAt R i σ μ' → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ R.eta η' → ∀ ω f₀ f B io thP, GlobalTheory.GalLift.LiftData R i σ μ' η' c H ω f₀ f B io thP → ∃ s m, GlobalTheory.LiftRows.IsLiftDataC R F i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io ∧ IsMeasDef (Vc D i) (GlobalTheory.AdelicScalar.levV R i A.μ0 R.triv m) (R.νV i A.μ0) (R.fdV i A.μ0) ∧ Bridge.IsReps (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y ∧ H.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.chrOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m))) (Bridge.adInner (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y) := by
  first | exact @GlobalTheory.ConjLiftData.isLiftDataC_of_liftData | exact GlobalTheory.ConjLiftData.isLiftDataC_of_liftData | (intros; apply GlobalTheory.ConjLiftData.isLiftDataC_of_liftData <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.extend_restriction_finitePoints_eq : ∀ {D : D7} {V : HSp D} (c : CoefA V), c.Is → ∀ (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (Ψ : GA D V → c.W), (∀ γ ∈ GQ V, ∀ k, Lev.finE V k ∈ lev D.sp.cm V.gram β L → ∀ h, Ψ (γ * h * k) = Lev.levChi V β L k • c.ρ k⁻¹ (Ψ h)) → ∀ h : GA D V, c.ext (fun u => Ψ (GlobalTheory.AdelicScalar.finLift V u)) h = Ψ h := by
  first | exact @GlobalTheory.AdelicRestrict.ext_restrict | exact GlobalTheory.AdelicRestrict.ext_restrict | (intros; apply GlobalTheory.AdelicRestrict.ext_restrict <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TameSplitChar

open GlobalTheory.CharLocProd

theorem locK_eq_of_congr {L : Type} [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L)
    (P : HeightOneSpectrum (𝓞 L)) (ht : χ.TameAt P) (k b : Lˣ) (hb : P.valuation L (b : L) = 1)
    (h : Valued.v (algebraMap L (P.adicCompletion L) (k : L) - algebraMap L (P.adicCompletion L) (b : L)) ≤
      WithZero.exp (-1 : ℤ)) : χ.locK P k = χ.locK P b := by
  have hlt : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have e : ((Formalism.L2.Host.atFin P (k * b⁻¹) : (P.adicCompletion L)ˣ) : P.adicCompletion L) - 1 =
      (algebraMap L (P.adicCompletion L) (k : L) - algebraMap L (P.adicCompletion L) (b : L)) *
        algebraMap L (P.adicCompletion L) ((b : L)⁻¹) := by
    show algebraMap L (P.adicCompletion L) ((k * b⁻¹ : Lˣ) : L) - 1 = _
    rw [sub_mul, ← map_mul, ← map_mul, mul_inv_cancel₀ b.ne_zero, map_one, Units.val_mul, Units.val_inv_eq_inv_val]
  have h1 : Valued.v (((Formalism.L2.Host.atFin P (k * b⁻¹) : (P.adicCompletion L)ˣ) : P.adicCompletion L) - 1) ≤
      WithZero.exp (-1 : ℤ) := by
    rw [e, map_mul, val_algebraMap, map_inv₀, hb, inv_one, mul_one]
    exact h
  have h2 : χ.locK P (k * b⁻¹) = 1 := by
    refine ht _ ?_ h1
    show Valued.v _ = 1
    rw [← map_one (Valued.v : Valuation (P.adicCompletion L) _)]
    refine Valuation.map_eq_of_sub_lt _ ?_
    rw [map_one]
    exact h1.trans_lt hlt
  rwa [map_mul, map_inv, mul_inv_eq_one] at h2

theorem idem_apply {L : Type} [Field L] [NumberField L] (ε : FiniteAdeleRing (𝓞 L) L) (hε : ε * ε = ε)
    (Q : HeightOneSpectrum (𝓞 L))
    (h : ∀ x : 𝓞 L, x ≠ 0 → (x ∈ Q.asIdeal ↔
      ¬ ∀ R, Valued.v (CharLocProd.evalAt R (ε * algebraMap L (FiniteAdeleRing (𝓞 L) L) ((x : L)⁻¹))) ≤ 1)) :
    CharLocProd.evalAt Q ε = 1 ∧ ∀ R, R ≠ Q → CharLocProd.evalAt R ε = 0 := by
  have h01 : ∀ R, CharLocProd.evalAt R ε ≠ 0 → CharLocProd.evalAt R ε = 1 := fun R hR =>
    mul_left_cancel₀ hR (by rw [← map_mul, hε, mul_one])
  have h0 : ∀ R, R ≠ Q → CharLocProd.evalAt R ε = 0 := by
    intro R hR
    by_contra hne
    have hnle : ¬ R.asIdeal ≤ Q.asIdeal := fun hle =>
      hR (HeightOneSpectrum.ext (R.isMaximal.eq_of_le Q.isPrime.ne_top hle))
    obtain ⟨y, hyR, hyQ⟩ := Set.not_subset.1 hnle
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact hyQ Q.asIdeal.zero_mem
    have h2 := not_not.1 (mt (h y hy0).2 hyQ) R
    rw [map_mul, h01 R hne, one_mul] at h2
    exact (GlobalTheory.PlaceIdem.val_inv_le_one R hy0).1 h2 hyR
  refine ⟨h01 Q fun hQ => ?_, h0⟩
  obtain ⟨y, hyQ, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot Q.ne_bot
  refine (h y hy0).1 hyQ fun R => ?_
  have : CharLocProd.evalAt R ε = 0 := by
    by_cases hR : R = Q
    · rw [hR, hQ]
    · exact h0 R hR
  rw [map_mul, this, zero_mul, map_zero]
  exact zero_le

theorem val_sub_le_of_resS {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : Pl E) (φ : Formalism.L2.Herm.intAf F E →+* P.adicCompletion E) (h1 : ∀ z, Valued.v (φ z) ≤ 1)
    (h2 : ∀ t : 𝓞 E, φ (oToS F E t) = algebraMap E _ (t : E)) (a : Formalism.L2.Herm.intAf F E) (b : 𝓞 E)
    (hab : resS F P a = Ideal.Quotient.mk P.asIdeal b) :
    Valued.v (φ a - algebraMap E _ (b : E)) ≤ WithZero.exp (-1 : ℤ) := by
  have h0 : resS F P (a - oToS F E b) = 0 := by rw [map_sub, resS_oToS, hab, sub_self]
  have hm : a - oToS F E b ∈ idS F P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact (map_eq_zero_iff _ (RingEquiv.ofBijective (cmpS F P.asIdeal)
      (cmpS_bij (F := F) P.asIdeal P.ne_bot)).symm.injective).1 h0
  rw [← h2, ← map_sub]
  generalize a - oToS F E b = z at hm
  induction hm using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨t, ht, rfl⟩ := hy
    rw [h2, val_algebraMap]
    have := (P.intValuation_le_pow_iff_mem t 1).2 (by simpa using ht)
    rw [show P.valuation E (t : E) = P.intValuation t from HeightOneSpectrum.valuation_of_algebraMap P t]
    simpa using this
  | zero => rw [map_zero, map_zero]; exact zero_le
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Valuation.map_add_le _ hx hy
  | smul r x _ hx =>
    rw [smul_eq_mul, map_mul, map_mul]
    exact (mul_le_mul' (h1 r) hx).trans (one_mul _).le

theorem map_mix {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (e a : A) :
    f (e * a + (1 - e)) = f e * f a + (1 - f e) := by
  rw [map_add (f := _), map_mul, map_sub, map_one]

theorem map_finset_sum {A B ι : Type} [CommRing A] [CommRing B] (f : A →+* B) (s : Finset ι) (g : ι → A) :
    f (∑ i ∈ s, g i) = ∑ i ∈ s, f (g i) := map_sum f g s



theorem char_eq_prod_res : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (P : Finset (Pl D.host.E)) (e : AE D) (ρ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), ChrEq c χ → IsIdemSum e P → (∀ PP ∈ P, χ.TameAt PP ∧ IsRes χ PP (ρ PP)) → ∀ (x : (AE D)ˣ) (a : AE D) (a' : Formalism.L2.Herm.intAf D.host.F D.host.E) (u : ∀ PP : Pl D.host.E, (kP PP)ˣ), (x : AE D) = e * a + (1 - e) → (a' : Lev.EAf D) = toEAf D a → (∀ PP ∈ P, (u PP : kP PP) = resS D.host.F PP a') → ((c x : Circle) : ℂ) = ∏ PP ∈ P, ((ρ PP (u PP) : ℂˣ) : ℂ) := by
  classical
  intro D c χ P e ρ hc he ht x a a' u hx ha hu
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2
    (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc
  have hinf : infPart D (x : AE D) = 1 := by
    rw [hx, map_mix, GlobalTheory.PlaceVec.idemSum_infPart he, zero_mul, zero_add, sub_zero]
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := he
  obtain ⟨ev, hev⟩ : ∃ ev : ∀ R : Pl D.host.E, AE D →+* R.adicCompletion D.host.E,
      ∀ R z, ev R z = CharLocProd.evalAt R (ι (finPart D z)) :=
    ⟨fun R => (CharLocProd.evalAt R).comp ((ι : _ →+* _).comp (finPart D)), fun _ _ => rfl⟩
  have hidem : ∀ Q ∈ P, ev Q (es Q) = 1 ∧ ∀ R, R ≠ Q → ev R (es Q) = 0 := by
    intro Q hQ
    simp only [hev]
    refine idem_apply _ (by rw [← RingEquiv.map_mul, ← RingHom.map_mul, (hes Q hQ).1.1]) Q fun y hy => ?_
    refine ((hes Q hQ).2 y hy).trans (not_congr ((h2 _).trans ?_))
    rw [RingHom.map_mul, RingEquiv.map_mul, show finPart D (incA D ((y : D.host.E)⁻¹)) =
      (1 : GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] ((y : D.host.E)⁻¹) from rfl, h1]
    rfl
  have hxP : ∀ R ∈ P, ev R x = ev R a := by
    intro R hR
    have : ev R e = 1 := by
      rw [hsum, map_finset_sum, Finset.sum_eq_single R, (hidem R hR).1]
      · intro Q hQ hne; exact (hidem Q hQ).2 R hne.symm
      · intro h; exact absurd hR h
    rw [hx, map_mix, this, one_mul, sub_self, add_zero]
  have hxP' : ∀ R, R ∉ P → ev R x = 1 := by
    intro R hR
    have : ev R e = 0 := by
      rw [hsum, map_finset_sum]
      exact Finset.sum_eq_zero fun Q hQ => (hidem Q hQ).2 R fun h => hR (h ▸ hQ)
    rw [hx, map_mix, this, zero_mul, zero_add, sub_zero]
  have hx0 : ∀ R, ev R x ≠ 0 := fun R => (RingHom.isUnit_map (ev R) x.isUnit).ne_zero
  choose k hk using fun R => GlobalTheory.adicCompletion_exists_unit_approx D.host.E N hN R _ (hx0 R)
  have hfin : {R : Pl D.host.E | R.asIdeal ∣ Ideal.span {(N : 𝓞 D.host.E)}}.Finite :=
    Ideal.finite_factors (by simpa [Ideal.span_singleton_eq_bot] using hN.ne')
  have key := hprod x hinf (P ∪ hfin.toFinset) (fun R => if R ∈ P then k R else 1) ?_ ?_
  rotate_left
  · intro R _
    change Valued.v (CharLocProd.evalAt R (ι (finPart D x))) = _ ∧
      Valued.v (CharLocProd.evalAt R (ι (finPart D x)) - _) ≤ _
    rw [← hev]
    by_cases hR : R ∈ P
    · simp only [if_pos hR]
      exact ⟨(hk R).1, (hk R).2.1⟩
    · simp only [if_neg hR]
      rw [hxP' R hR, Units.val_one, map_one, map_one, map_one, sub_self, map_zero]
      exact ⟨rfl, zero_le⟩
  · intro R hR
    rw [Finset.mem_union, not_or] at hR
    change Valued.v (CharLocProd.evalAt R (ι (finPart D x))) = _ ∧ _
    rw [← hev, hxP' R hR.1, map_one]
    exact ⟨rfl, fun h => hR.2 (hfin.mem_toFinset.2 (Ideal.dvd_span_singleton.2 h))⟩
  rw [key, ← Finset.prod_subset Finset.subset_union_left
    (fun R _ hR => by rw [if_neg hR, map_one, Units.val_one])]
  refine Finset.prod_congr rfl fun R hR => ?_
  rw [if_pos hR]
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (u R : kP R)
  have := R.isPrime
  have hbR : b ∉ R.asIdeal := fun h => (u R).ne_zero (hb ▸ Ideal.Quotient.eq_zero_iff_mem.2 h)
  have hb0 : (b : D.host.E) ≠ 0 := fun h => hbR (RingOfIntegers.coe_eq_zero_iff.1 h ▸ R.asIdeal.zero_mem)
  have hbv : R.valuation D.host.E (b : D.host.E) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := D.host.E) R (r := b)).2 hbR
  let cm := (Algebra.TensorProduct.comm D.host.F (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E)
  let φ : Formalism.L2.Herm.intAf D.host.F D.host.E →+* R.adicCompletion D.host.E :=
    (CharLocProd.evalAt R).comp ((ι : _ →+* _).comp (cm.symm.toRingEquiv.toRingHom.comp
      (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype))
  have hφ : ∀ z, φ z = CharLocProd.evalAt R (ι (cm.symm (z : Lev.EAf D))) := fun _ => rfl
  have hv := val_sub_le_of_resS R φ (fun z => (h2 _).1 ((GlobalTheory.HostAdeleIso.mem_intAE_iff_comm D _).2
      (by change cm (cm.symm (z : Lev.EAf D)) ∈ _; rw [AlgEquiv.apply_symm_apply]; exact z.2)) R)
    (fun t => by
      rw [hφ, show cm.symm ((oToS D.host.F D.host.E t : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) =
        (1 : GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (t : D.host.E) from rfl, h1]
      rfl) a' b ((hu R hR).symm.trans hb.symm)
  have hφa : φ a' = ev R x := by
    rw [hxP R hR, hev, hφ, ha]
    exact congrArg (fun z => CharLocProd.evalAt R (ι z)) (cm.symm_apply_apply (finPart D a))
  rw [hφa] at hv
  have hlt : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hxv : Valued.v (ev R x) = 1 := by
    rw [← hbv, ← val_algebraMap]
    refine Valuation.map_eq_of_sub_lt _ ?_
    rw [val_algebraMap, hbv]
    exact hv.trans_lt hlt
  have hk3 := (hk R).2.2
  rw [← (hk R).1, hxv, mul_one] at hk3
  rw [(ht R hR).2 b (Units.mk0 _ hb0) (u R) rfl hb.symm,
    locK_eq_of_congr χ R (ht R hR).1 (k R) (Units.mk0 _ hb0) hbv ?_]
  have e4 : algebraMap D.host.E (R.adicCompletion D.host.E) (k R : D.host.E) -
      algebraMap D.host.E (R.adicCompletion D.host.E) (b : D.host.E) =
      (ev R x - algebraMap D.host.E _ (b : D.host.E)) - (ev R x - algebraMap D.host.E _ (k R : D.host.E)) := by
    ring
  rw [Units.val_mk0, e4]
  exact Valuation.map_sub_le _ hv hk3

end GlobalTheory.TameSplitChar
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_integer_conj_prescribed_residues_places : ∀ (D : D7) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (b : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Formalism.L2.DIV.kP PP), ∃ c : 𝓞 D.host.E, ∀ PP ∈ P, Ideal.Quotient.mk PP.asIdeal (GlobalTheory.SW.Lev.bar c) = b PP := by
  first | exact @GlobalTheory.SW.Lev.exists_bar_mk_eq_at_places | exact GlobalTheory.SW.Lev.exists_bar_mk_eq_at_places | (intros; apply GlobalTheory.SW.Lev.exists_bar_mk_eq_at_places <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.levelVector_finiteDatum_isTheta_vacuum_off : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → IsThetaFunO R.ψ (Vc D i) (Wc D i) f ∧ ∀ v ∉ finS R t, VacFin R.ψ (Vc D i) (Wc D i) v f := by
  first | exact @GlobalTheory.FinZeta.levVec_vacFin | exact GlobalTheory.FinZeta.levVec_vacFin | (intros; apply GlobalTheory.FinZeta.levVec_vacFin <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel

def vmvBil (E : Type) [Field E] [NumberField E] (n r : ℕ) :
    (Fin n → E) →ₗ[𝓞 E] (Fin r → E) →ₗ[𝓞 E] Matrix (Fin n) (Fin r) E :=
  LinearMap.mk₂ (𝓞 E) (fun v u => vecMulVec v u)
    (fun v v' u => by ext i j; simp [vecMulVec, add_mul])
    (fun a v u => by ext i j; simp [vecMulVec, smul_mul_assoc])
    (fun v u u' => by ext i j; simp [vecMulVec, mul_add])
    (fun a v u => by ext i j; simp [vecMulVec, mul_smul_comm])

theorem tens_quot_finite {E : Type} [Field E] [NumberField E] {n r : ℕ} (Λ : Lt E n) (L : Lt E r)
    (hΛ : Λ.FG) (hL : L.FG) (𝔞 𝔪 : Ideal (𝓞 E)) (hm : 𝔪 ≠ ⊥) :
    Finite (tens Λ (𝔞 • L) ⧸ (tens Λ ((𝔞 * 𝔪) • L)).addSubgroupOf (tens Λ (𝔞 • L))) := by
  set A := tens Λ (𝔞 • L) with hA
  set B := tens Λ ((𝔞 * 𝔪) • L) with hB
  have hM : (Submodule.map₂ (vmvBil E n r) Λ L).FG := hΛ.map₂ _ hL
  have hMZ : ((Submodule.map₂ (vmvBil E n r) Λ L).restrictScalars ℤ).FG := hM.restrictScalars
  have hle : A.toIntSubmodule ≤ (Submodule.map₂ (vmvBil E n r) Λ L).restrictScalars ℤ := by
    intro x hx
    have hsub : A ≤ ((Submodule.map₂ (vmvBil E n r) Λ L).restrictScalars ℤ).toAddSubgroup := by
      rw [hA, tens, AddSubgroup.closure_le]
      rintro y ⟨v, hv, u, hu, rfl⟩
      exact Submodule.apply_mem_map₂ (vmvBil E n r) hv (Submodule.smul_le_right hu)
    exact hsub hx
  have hAfg : A.toIntSubmodule.FG :=
    (isNoetherian_submodule.mp (isNoetherian_of_fg_of_noetherian _ hMZ)) _ hle
  haveI : AddGroup.FG A := by
    have : Module.Finite ℤ A.toIntSubmodule := Module.Finite.iff_fg.mpr hAfg
    exact (Module.Finite.iff_addGroup_fg).mp this
  set N := Ideal.absNorm 𝔪 with hN
  have hNpos : 0 < N := Nat.pos_of_ne_zero (fun h => hm (Ideal.absNorm_eq_zero_iff.mp h))
  have hNA : ∀ x ∈ A, N • x ∈ B := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨v, hv, u, hu, rfl⟩ := hy
      apply AddSubgroup.subset_closure
      refine ⟨v, hv, N • u, ?_, ?_⟩
      · have h1 : ((N : 𝓞 E)) • u ∈ 𝔪 • (𝔞 • L) := Submodule.smul_mem_smul (Ideal.absNorm_mem 𝔪) hu
        rw [← Submodule.mul_smul, mul_comm] at h1
        rwa [← Nat.cast_smul_eq_nsmul (𝓞 E)]
      · ext i j; simp [vecMulVec]; ring
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx
  haveI : AddGroup.FG (A ⧸ B.addSubgroupOf A) := AddGroup.fg_of_surjective (QuotientAddGroup.mk'_surjective _)
  apply AddCommGroup.finite_of_fg_torsion
  intro q
  induction q using QuotientAddGroup.induction_on with
  | H x =>
    refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨N, hNpos, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    simpa using hNA x x.2

theorem lvCls_finite : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Lv : GlobalTheory.SW.Level C.X), Finite (GlobalTheory.LiftLevel.LvCls C Lv) := by
  intro D S T C Lv
  exact tens_quot_finite _ _ (Submodule.fg_span (Set.finite_range _)) C.X.Λ_fg _ _ Lv.ne_bot

end GlobalTheory.LiftLevel

end
end
