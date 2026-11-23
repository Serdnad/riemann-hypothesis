module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle034
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle003
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle020
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle081
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCcIsEquivAtSerOfOneMapRowOfFive
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PureTensorOSmul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseEmbeddingReadingEvalAdelicFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle548
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSpanAndGoodRange
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle854
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.BaseIntSet
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFormsThetaShortSeriesIdentity
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle031
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1546
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle978
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnfoldingConstantTermsAgreeAtGoodEmbeddings
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle033
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle057
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeSupReal

open Formalism.L2.Pj Formalism.IndefR.FWT GlobalTheory.HeckeSup



theorem hkSupAt_realSide : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → ∀ (D : D7) (X : RealSide D) j, GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.HkSupAt X.core X.R.toRealDat j := by
  intro hDec hI hT hRT D X i
  have hC := X.char
  have ht : TieIn X.core X.R.toRealDat X.geo.κ X.geo.v₀ :=
    ⟨X.geo.fw.laws, X.geo.fw.alg_eq, X.geo.fw.kap, X.geo.fw.hv₀, X.geo.fw.chiR, X.geo.fw.x0⟩
  have h5 : GlobalTheory.Core5 X.R.toRealDat X.F.lv2 := ⟨hC.lev, hC.grp, hC.fam, hC.models, hC.thP⟩
  have hio := GlobalTheory.IoExtremal.ioExt D _ _ _ _ _ X.R.toRealDat hC.lev hC.fam hC.models hC.thP
  have hr := GlobalTheory.OneMapTies.oneMapRow0_of_ties_ofFive GlobalTheory.ChartFree.chartIndep D _ _ _ _ X.core X.R.toRealDat X.F.lv2
    X.geo.κ X.geo.v₀ h5 ht hio X.geo.O i (X.geo.pins i)
  have hc := GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.constPinned_of X.core X.R.toRealDat X.geo.κ X.geo.v₀ X.geo.O i (X.geo.pins i) hr (X.geo.cTie i)
  have h0 := GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.readAt0_of X.core X.R.toRealDat X.geo.κ X.geo.v₀ X.inGeo.jEvExists X.geo.fw X.unif i hc
  have hsp := GlobalTheory.AdSpan.spanAt X.R.toRealDat hDec X.size hC.lev hC.fam hC.models hC.thP i X.A3.A.μ0
  refine hkSupAt_of_clauses hI hT GlobalTheory.HeckePointLaw.heckePointLaws (hC.lev.βW i) hC.fam.Sb hC.models.inf hC.models.HW
    hC.models.gW hC.models.HV hC.models.jV hC.thP.thF_mem X.geo.fw h0 hsp (fun O hO => ?_) fun c' hL hV => ?_
  · obtain ⟨cc, h1, u, h2, h3, h4, -⟩ := GlobalTheory.AdTh.ioExt_oneMap_ofFive.2.1 GlobalTheory.ChartFree.chartIndep D _ _ _ _ X.core
      X.R.toRealDat X.F.lv2 X.geo.κ X.geo.v₀ h5 ht hio i _ _ O hO
    exact ⟨cc, h1, u, h2, h3, h4⟩
  · exact @hRT D X.Γ _ _ X.Pl0 _ X.A3.A (withConst X.core c') X.alg X.R.toRealDat X.F.lv2 X.geo.κ X.geo.v₀ hC.lev hC.grp
      hC.fam hC.models hC.thP
      (@TieIn.mk D X.Γ _ _ X.Pl0 _ X.A3.A (withConst X.core c') X.alg X.R.toRealDat X.geo.κ X.geo.v₀ hL X.geo.fw.alg_eq
        X.geo.fw.kap X.geo.fw.hv₀ X.geo.fw.chiR X.geo.fw.x0) i _ rfl hV

end GlobalTheory.HeckeSupReal
end
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.exists_forms_theta_short_series_identity : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (σ : c.F →+* ℂ), (∀ τ, relab c σ τ = τ) → GoodEmb c σ → ∀ (U : Unf Xo c σ r), l.A = 1 → Odd r → ∀ (hr : W.rank = r) (dict : GA D W → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (mu : GA D W → ℂ) (cc : U.Comp → ℂ), IsDict U W hr dict ι x₀ → FrameTie U W hr x₀ sW BW → CcIs θ V W hr U dict mu x₀ om f₀ cc → ∀ e : AE D, IsHalfIdem l e → ∀ (bad N : ℕ) (h : GA D V) (Λ : GenLat D.host.E V.rank) (e' : AE D) (Ps : Finset (Formalism.L2.DIV.Pl D.host.E)) (y : (AE D)ˣ), l.M ∣ bad → IsIdemSum e' Ps → (∀ PP ∈ Ps, ((bad : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → h ∈ GfC V → SuppAt e' V h → IsDetAt e' V h y → (∀ v, v ∈ Λ.La ↔ (fun j => star (v j)) ∈ Bridge.hLat V (GlobalTheory.ExportSeries.finPt V h)) → Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ (lt : LtN Dw V.rank ≃ FVar D W.rank V.rank) (wa : (D.host.E →+* ℂ) × ℕ → ℕ), IsLetters Dw lt → Dom wa V.rank → LastPos Dw wa → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ), p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → l.GoodAt p → ∀ O : Subring ℂ, ValRing σ la O → ∀ u : (Fin V.rank → LevQ Dw l) → ℂ, (∀ q, u q ∈ O) → ∀ Q ∈ HHa Dw.mult V.rank ℂ ComplexEmbedding.conjugate (InPsi H) (fun τ i => wa (τ, i)), (∀ mo, Q.coeff mo ∈ O) → ∃ (m : ℕ) (β : Fin m → ℂ) (f : Fin m → Rul Xo c), (∀ k, β k ∈ O ∧ f k ∈ sec Xo c wa V.rank ∧ rdU U (f k) ∈ Formalism.L2.Pj.holSub0 U.X (laU U wa V.rank) ∧ GlobalTheory.GoodPts.BddAll Xo c la (((Λ.mIdx N (Dw.p + Dw.q) * Nat.card (Fin V.rank → LevQ Dw l) : ℕ) : c.F) * ((2 * NumberField.discr D.host.E * N : ℤ) : c.F) ^ degA Dw wa) (f k)) ∧ ∀ g : GA D W, thetaKO om h g (stdF ψ θ V W sW BW (transSum ψ V W l ι e f₀ u) (MvPolynomial.rename lt Q)) = (-1) ^ degA Dw wa * clsScal χW y Λ r * ∑ k, β k * ((lieFac Dw (xiR D) wa : ℂ) * (cc (dict g).1 * mu g * rdU U (f k) (dict g).1 (dict g).2)) := by
  first | exact @GlobalTheory.LevelSeries.SerId.exists_forms_of_transSum | exact GlobalTheory.LevelSeries.SerId.exists_forms_of_transSum | (intros; apply GlobalTheory.LevelSeries.SerId.exists_forms_of_transSum <;> assumption)
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.exists_centralFlip_thetaTranslate_halfLevel : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → Odd W.rank → ∀ (χ : Formalism.L2.Host.HChar D.host.E) (M₀ l : ℕ), ChiData χW χ M₀ → l.Prime → M₀ ≠ 0 → ∃ (Z : Finset (GA D V)) (c : ℕ), (∀ z ∈ Z, z ∈ GfC V) ∧ ∀ (H : Geo.Tor.Host D.host.E) (l₂ : Geo.Tor.Level H) (pd : ℕ), l₂.M = M₀ * pd → Nat.Coprime pd M₀ → Nat.Coprime pd l → Nat.Coprime l₂.M (GlobalTheory.Tow.badN D) → ∀ (k : Type) [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) (O : Subring ℂ), ((l : ℕ) : 𝓞 k) ∈ la.asIdeal → ValRing σ la O → ConjIn D σ → χ.ValuesIn (-1 / 2) σ → zeta l₂.M ∈ O → ∀ (e e₂ : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P → (∀ PP ∈ P, ((l₂.M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → IsHalfIdem l₂ e₂ → ∃ z₂ ∈ Z, ∃ z₁ ∈ GfC V, OneAt V l z₁ ∧ ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e l₂.M O, ∃ f' ∈ trSp ψ V W ΛV ΛW f₀ e₂ l₂.M O, ∀ (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (Q : MvPolynomial (FVar D W.rank V.rank) ℂ) (s : GA D V) (g : GA D W), (l : ℂ) ^ c * thetaKO om s g (stdF ψ θ V W sW BW f Q) = thetaKO om (s * z₂ * z₁) g (stdF ψ θ V W sW BW f' Q) := by
  first | exact @GlobalTheory.LevelSeries.exists_flip_theta | exact GlobalTheory.LevelSeries.exists_flip_theta | (intros; apply GlobalTheory.LevelSeries.exists_flip_theta <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SpanFamily



theorem holSub0_le_span_cuspA_of_lastPos : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ →
    ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → LastPos (T.Q.Dw j) a →
    4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ n →
    Formalism.L2.Pj.holSub0 (T.U j σ).X (laU (T.U j σ) a n) ≤
      Submodule.span ℂ (rdU (T.U j σ) '' (T.cuspA j a n : Set (T.R j))) := by
  intro D T h j hj σ hσ a n hdom hlast hn
  have hr : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
  obtain ⟨hrk, hM⟩ := h.modelW j hj σ hσ
  have key := GlobalTheory.Dict.holSub0_le_span_cusp GlobalTheory.chartIndependence_unconditional D.host.E T.Q.H (T.Q.Dw j) T.Q.l
    (T.Q.Xo j) T.Q.c D.R.r (fun s => Formalism.L2.PjFree.Unf.ofPj (T.U j s)) hr h.pins.2.1.2
    (fun s hs => (Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf j hj s hs)) σ hσ
    (fun k k' => ⟨(hM k).1.trans (hM k').1.symm, (hM k).2.trans (hM k').2.symm⟩)
    (fun k => GlobalTheory.PrincCore.mem_group_of_congruent D T.toCore h.toLawsM j hj σ hσ k)
    a n hdom hlast hn
    (fun k => h.chiTriv j hj σ hσ a n hdom k)
  intro P hP
  exact key ⟨hP.1, hP.2⟩

theorem exists_complex_point {K A : Type} [Field K] [CommRing A] [Algebra K A] [Algebra.FiniteType K A]
    (σ : K →+* ℂ) (I : Ideal A) (hI : I ≠ ⊤) : ∃ ψ : A →ₐ[K] CAt σ, ∀ x ∈ I, ψ x = 0 := by
  obtain ⟨M, hMmax, hle⟩ := Ideal.exists_le_maximal _ hI
  let _ : Field (A ⧸ M) := Ideal.Quotient.field M
  have : Module.Finite K (A ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ M)
  let _ : Algebra K ℂ := σ.toAlgebra
  let κ : (A ⧸ M) →ₐ[K] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨κ.comp (Ideal.Quotient.mkₐ K M), fun x hx => ?_⟩
  show κ (Ideal.Quotient.mk M x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.2 (hle hx), map_zero]

theorem evR_of_frMap {D : D7} (T : CoreJ D) (h : LawsJ T) {j : ℕ} (hj : Formalism.L2.Pj.InR D j) (f : T.R j)
    (hf : IsNatural (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) f)
    {S : Type} [CommRing S] [Algebra T.Q.c.F S] (p : TRing T.Q.c.F) (ψ : p.R →ₐ[T.Q.c.F] S)
    (y : FrPt (T.Q.Xo j) T.Q.c p.R) (z : FrPt (T.Q.Xo j) T.Q.c S) (hz : FrMap ψ y z) :
    evR (T.Q.Xo j) T.Q.c f z = ψ (f p y) := by
  have hT : FromTest (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) z :=
    ⟨p, ψ, y, hz⟩
  unfold evR evalAt
  rw [dif_pos hT]
  exact h.evalWD j hj f hf S _ p _ ψ _ y z hT.choose_spec.choose_spec.choose_spec hz


set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
theorem exists_family : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∃ (b : (D.host.E →+* ℂ) × ℕ → ℕ) (m N : ℕ) (t : Fin N → Rul (T.Q.Xo j) T.Q.c), Dom b m ∧ (∀ i, t i ∈ sec (T.Q.Xo j) T.Q.c b m) ∧ (∀ (p : TRing T.Q.c.F) (y : FrPt (T.Q.Xo j) T.Q.c p.R), Ideal.span (Set.range fun i => t i p y) = ⊤) ∧ ∀ P ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n), ∀ i, P * rdU (T.U j σ) (t i) ∈ Submodule.span ℂ (rdU (T.U j σ) '' (sec (T.Q.Xo j) T.Q.c (a + b) (n + m) : Set (Rul (T.Q.Xo j) T.Q.c))) := by
  intro D T h j hj σ hσ a n hdom
  obtain ⟨b, m, hbm, hlast, hm, hnz⟩ := GlobalTheory.T.exists_dominantWeight_cuspSections_noCommonZero D T h j hj σ hσ
  haveI : FiniteDimensional T.Q.c.F (T.cuspA j b m) := h.cuspFD j hj b m hbm
  haveI : Module.Free T.Q.c.F (T.cuspA j b m) := Module.Free.of_divisionRing _ _
  let B := Module.finBasis T.Q.c.F (T.cuspA j b m)
  have hsec : ∀ i, (B i : T.R j) ∈ sec (T.Q.Xo j) T.Q.c b m := fun i => cusp_le_sec _ _ _ _ _ (B i).2
  refine ⟨b, m, _, fun i => (B i : T.R j), hbm, hsec, ?_, ?_⟩
  · intro p y
    by_contra hne
    have hL := (GlobalTheory.Reg.evLaws_genFr_atlas _ _ _ _ (T.Q.Xo j) T.Q.c).1
    obtain ⟨ψ, hψ⟩ := exists_complex_point σ _ hne
    obtain ⟨z, hz⟩ := hL.bc p.R (CAt σ) ψ y
    have hz0 : ∀ i, evR (T.Q.Xo j) T.Q.c (B i : T.R j) z = 0 := fun i => by
      rw [evR_of_frMap T h hj _ (hsec i).1 p ψ y z hz]
      exact hψ _ (Ideal.subset_span ⟨i, rfl⟩)
    haveI : IsDomain (CAt σ) := inferInstanceAs (IsDomain ℂ)
    obtain ⟨k, x, t, ht⟩ := (h.unf j hj σ hσ).2.2.1 z
    have hx0 : ∀ i, rdU (T.U j σ) (B i : T.R j) k x.1 = 0 := fun i => by
      have hw := GlobalTheory.ArcQ.evR_frBor_of_isDomain hL (hsec i) t _ z ht
      rw [hz0 i] at hw
      have hu : wchar (ex (T.Q.Dw j) b m) t ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun c _ => pow_ne_zero _ (t c).ne_zero
      have h0 := (mul_eq_zero.1 hw.symm).resolve_left hu
      simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_pos x.2]
      exact congrArg toC h0
    let ev : FDSec (T.U j σ).X →ₗ[ℂ] ℂ :=
      { toFun := fun P => P k x.1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hall : ∀ f ∈ T.cuspA j b m, rdU (T.U j σ) f k x.1 = 0 := by
      intro f hf
      have key : ∀ g : T.cuspA j b m, g ∈ Submodule.span T.Q.c.F (Set.range B) →
          rdU (T.U j σ) (g : T.R j) k x.1 = 0 := by
        intro g0 hg0
        induction hg0 using Submodule.span_induction with
        | mem g hg =>
          obtain ⟨i, rfl⟩ := hg
          exact hx0 i
        | zero => rw [Submodule.coe_zero, map_zero]; rfl
        | add g g' _ _ hg hg' =>
          rw [Submodule.coe_add, map_add (f := _), Pi.add_apply, Pi.add_apply, hg, hg', add_zero]
        | smul c g _ hg =>
          rw [Submodule.coe_smul, map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, hg, smul_zero]
      exact key ⟨f, hf⟩ (B.mem_span _)
    have hle : Submodule.span ℂ (rdU (T.U j σ) '' (T.cuspA j b m : Set (T.R j))) ≤ LinearMap.ker ev := by
      rw [Submodule.span_le]
      rintro _ ⟨f, hf, rfl⟩
      exact hall f hf
    obtain ⟨P, hP, hPx⟩ := hnz k x.1 x.2
    exact hPx (hle (holSub0_le_span_cuspA_of_lastPos D T h j hj σ hσ b m hbm hlast hm hP))
  · intro P hP i
    have hrd : rdU (T.U j σ) (B i : T.R j) ∈ holSub (T.U j σ).X (laU (T.U j σ) b m) :=
      ((mem_cusp _ _ _ _ _ _).1 (B i).2).2 σ hσ
    have hdab : Dom (a + b) (n + m) := ⟨fun τ => (hdom.1 τ).add (hbm.1 τ), hdom.2.add hbm.2⟩
    have hprod : P * rdU (T.U j σ) (B i : T.R j) ∈
        Formalism.L2.Pj.holSub0 (T.U j σ).X (laU (T.U j σ) (a + b) (n + m)) := by
      refine ⟨?_, fun k x hx => by simp [hP.2 k x hx]⟩
      have hP1 := (GlobalTheory.CuspProduct.mem_holSub_iff _ _ _).1 hP.1
      have hr1 := (GlobalTheory.CuspProduct.mem_holSub_iff _ _ _).1 hrd
      refine (GlobalTheory.CuspProduct.mem_holSub_iff _ _ _).2 fun k => ?_
      rw [show laU (T.U j σ) (a + b) (n + m) k = laU (T.U j σ) a n k + laU (T.U j σ) b m k from
        GlobalTheory.CuspProduct.laU_add (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) a b n m hdom.2 hbm.2 k]
      exact (siegelSpaceAlgebra_holds (E := D.host.E) D.R.r _ _ _ 0).2.1 _ (hP1 k) _ (hr1 k).1
    have hlast' : LastPos (T.Q.Dw j) (a + b) := fun τ hτ hm0 =>
      lt_of_lt_of_le (hlast τ hτ hm0) (by simp)
    have hs := holSub0_le_span_cuspA_of_lastPos D T h j hj σ hσ (a + b) (n + m) hdab hlast' (by omega) hprod
    exact Submodule.span_mono (Set.image_mono (cusp_le_sec _ _ _ _ _)) hs

end GlobalTheory.SpanFamily
end
