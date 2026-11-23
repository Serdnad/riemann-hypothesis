module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle443
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle476
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle478
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle491
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1587
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1191
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1230
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle005
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle014
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle004
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle365
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle186
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle021
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle004
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle531
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle539
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle554
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle022
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKFiniteIteratedCompactAverageApprox
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle006
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle008
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle010
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle658
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle525
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
noncomputable section
namespace GlobalTheory.SplitDblPar
theorem parabolic_derivative_fixes_split_vector : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.V'.J) (dbl (incM F G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (cA σ) (dbl (incM F G.W.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co dd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (dbl (incM F G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, R 0 ≠ 0 → Rest (evFin F v) (G.M'.vac v) R →
    ∀ p ∈ GlobalTheory.InertDbl.ParD σ G.W v, omd p (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hTr v hsp hT hψ h2 hvac dd omd hdc hws R hR0 hRv p hp
  set Ψ := tens (evFin F v) (G.M'.vac v) R with hΨdef
  have hΨ : Ψ ∈ schA F _ := hRv.2
  have hΦ : GlobalTheory.InertDbl.dblFun Ψ ∈ schA F _ :=
    GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Ψ hΨ _ (GlobalTheory.SchAConj.star_mem_schA F _ Ψ hΨ)
  have hV := hTr.geo.hM'.vac v
  obtain ⟨y, hy⟩ : ∃ y, G.M'.vac v y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hV.2.1 (funext h)
  have hΨne : Ψ ≠ 0 := by
    intro h0
    let x : Fin a' × Fin (a + a') → AF F := fun i => GlobalTheory.LatVac.liftV v (y i)
    have hRx : R x = R 0 := by
      have := hRv.1 0 x (fun u hu => by funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu)
      simpa using this
    have h1 := congrFun h0 x
    simp only [hΨdef, tens, x, GlobalTheory.LatVac.evFin_liftV, hRx, Pi.zero_apply] at h1
    exact mul_ne_zero hy hR0 h1
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.SplitDblLine.doubleLine_eigenfunction_split hP F E σ B a a' G X om om' hTr v hsp hT hψ h2 hvac dd omd hdc hws R hRv p hp.1
  obtain ⟨l, hl, hinv, hl0⟩ := GlobalTheory.T.exists_translationInvariant_doubledForm_conjProduct_ne_zero F _ Ψ hΨ hΨne
  obtain ⟨t, ht⟩ := hp.2
  have hS := hws.2.2 l hl (fun z φ hφ => hinv φ hφ _ _ (GlobalTheory.WeilM.SiegelModel.rho_diag B.ψ hdc z φ)) p t ht _ hΦ
  have htp := GlobalTheory.T.doubledSiegelParabolic_diagonal_action_integral F E σ G.W v p hp t ht
  have ha := _root_.GlobalTheory.T.split_det_character_trivial hP F E σ B a a' G X om om' hTr v hsp hT hψ h2 hvac t htp
  have hb := _root_.GlobalTheory.SplitDetModule.split_det_modulus_eq_norm_det hP F E σ B a a' G X om om' hTr v hsp hT hψ h2 hvac t htp
  rw [ha, hb] at hS
  rw [hc, map_smul, smul_eq_mul] at hS
  simp only [Circle.coe_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, one_mul] at hS
  have h1 : c = 1 := (mul_eq_right₀ hl0).mp hS
  rw [hc, h1, one_smul]
end GlobalTheory.SplitDblPar
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.split_double_parabolic_derivative_fixed : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.V'.J) (dbl (incM F G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (cA σ) (dbl (incM F G.W.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co dd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (dbl (incM F G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, R 0 ≠ 0 → Rest (evFin F v) (G.M'.vac v) R →
    ∀ p ∈ GlobalTheory.InertDbl.ParD σ G.W v, omd p (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  first | exact @_root_.GlobalTheory.SplitDblPar.parabolic_derivative_fixes_split_vector | exact _root_.GlobalTheory.SplitDblPar.parabolic_derivative_fixes_split_vector | (intros; apply _root_.GlobalTheory.SplitDblPar.parabolic_derivative_fixes_split_vector <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
namespace GlobalTheory.MovedDict
theorem moved_vacuum_isVacuumIntegral : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    IsVacO ch.W.ψ ch.W.θ _ _ (ch.G.cartS ch.W.cart p) (ch.G.onT ch.W.cart p) (inV (frS ch.S.N p) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y)) (inV (frT ch.S.N p) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y))
      (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p)) := by
  intro hPr hInp D Γ _ _ Pl0 T A Ks _ _ _ R ch hIs p hp x y
  have hn := DefPair.nodes hp
  have hom := ch.W.om_is p (by cases p <;> simp only [DefPair, DefNode] at hp hn <;> simp only [Pair.InRange, Node.InRange] <;> omega)
  have negMem : ∀ (V : HSp D) {g : Formalism.L2.Theta.GA D V}, g ∈ GfC V → negGA V g ∈ GfC (negSp V) := by
    intro V g hg
    have e : matHom (negSp V) (negGA V g) = matHom V g := Units.ext (mt_negGA V g)
    simp only [GfC, MonoidHom.mem_ker, infHom, MonoidHom.comp_apply] at hg ⊢
    rw [e]
    exact hg
  set gh := ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small))
    ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big)) with hgh
  have mem : gh.1 ∈ GfC (ch.G.pS p) ∧ gh.2 ∈ GfC (ch.G.pT p) := by
    rw [hgh]
    cases p with
    | chi i j => exact ⟨negMem _ (y * ch.S.N.u _).2, (x * ch.S.N.u _).2⟩
    | mu t i j => exact ⟨(x * ch.S.N.u _).2, (y * ch.S.N.u _).2⟩
    | core i => exact ⟨negMem _ (y * ch.S.N.u _).2, (x * ch.S.N.u _).2⟩
    | top t j => exact ⟨(x * ch.S.N.u _).2, (y * ch.S.N.u _).2⟩
  obtain ⟨hstd, hv⟩ := ch.S.Z.vac_is p hp
  have hact := (_root_.GlobalTheory.T.twisted_moved_lattice_action hPr hInp ch hIs p hp x y).2
  have hth' := hom.om_pres gh _ hv.theta
  have hgh' : gh = (gh.1, gh.2) := rfl
  refine ⟨hstd, { inf := hv.inf, theta := hth', lat := ⟨fun u' hu' => ?_, fun e he u' hu' hhalf => ?_⟩, fock := fun τ z => ?_, norm := ⟨hv.norm.1, fun q hq => ?_⟩ }⟩
  · obtain ⟨u, hu, rfl⟩ := hact u' hu'
    have h2 : actO _ _ gh.1 gh.2 u + actO _ _ gh.1 gh.2 u = actO _ _ gh.1 gh.2 (u + u) := by
      simp only [actO, Matrix.mul_add, Matrix.add_mul]
    have h3 := hv.lat.1 u hu
    rw [two_nsmul] at h3 ⊢
    rw [h2, hgh', ← hom.om_heis gh.1 gh.2 _ _ hv.theta, h3]
  · obtain ⟨u, hu, rfl⟩ := hact u' hu'
    rw [hgh', ← hom.om_heis gh.1 gh.2 u _ hv.theta, hv.lat.2 e he u hu (GlobalTheory.MovedVac.halfBack D _ _ gh.1 gh.2 e u hhalf)]
  · have hθ := ch.W.θ_is
    have e : ∀ z', Formalism.IndefR.Datum.dRho (heisO ch.W.ψ _ _) ch.W.θ τ z' (ch.W.om p gh (ch.S.Z.vac p)) =
        ch.W.om p gh (Formalism.IndefR.Datum.dRho (heisO ch.W.ψ _ _) ch.W.θ τ z' (ch.S.Z.vac p)) := by
      intro z'
      rw [hgh', GlobalTheory.OrientedHeis.om_dRho hom hθ gh.1 gh.2 τ z' hv.theta, GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC ch.W.θ _ mem.2,
        GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC ch.W.θ _ (inv_mem mem.1), Matrix.one_mul, Matrix.mul_one]
    have h0 := hv.fock τ z
    unfold annih at h0 ⊢
    rw [e, e, ← map_smul, ← map_add (f := _), h0, map_zero]
  · show nrm2 q.1 q.2 (ch.W.om p gh (ch.S.Z.vac p)) = 1
    have hU := hom.om_unit q.1 q.2 hq.1 hq.2.1 gh _ hv.theta
    haveI : OpensMeasurableSpace (WO (ch.G.pS p) (ch.G.pT p)) := ⟨le_rfl⟩
    have key : ∀ F : WO (ch.G.pS p) (ch.G.pT p) → ℂ, Continuous F → nrm2 q.1 q.2 F = (∫⁻ w in q.2, ‖F w‖ₑ ^ 2 ∂q.1).toReal := by
      intro F hF
      unfold nrm2
      have hc : Continuous fun w => ‖F w‖ ^ 2 := by fun_prop
      rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae (f := fun w => ‖F w‖ ^ 2)
        (Filter.Eventually.of_forall fun w => sq_nonneg ‖F w‖) hc.aestronglyMeasurable]
      congr 1
      refine MeasureTheory.lintegral_congr fun w => ?_
      rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [key _ hth'.cont, hU, ← key _ hv.theta.cont]
    exact hv.norm.2 q hq
end GlobalTheory.MovedDict
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

theorem _root_.GlobalTheory.T.twisted_moved_vacuum_integral : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    IsVacO ch.W.ψ ch.W.θ _ _ (ch.G.cartS ch.W.cart p) (ch.G.onT ch.W.cart p) (inV (frS ch.S.N p) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y)) (inV (frT ch.S.N p) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y))
      (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p)) := by
  first | exact @_root_.GlobalTheory.MovedDict.moved_vacuum_isVacuumIntegral | exact _root_.GlobalTheory.MovedDict.moved_vacuum_isVacuumIntegral | (intros; apply _root_.GlobalTheory.MovedDict.moved_vacuum_isVacuumIntegral <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
noncomputable section
namespace GlobalTheory.KTypeProj
theorem kType_projection_mem : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ → IsCuspFun V ψ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ f ∈ W, rTr V (atTau θ V τ g) f ∈ W) →
    ∀ b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ,
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, x ≠ 0 → 0 < (b x x).re) →
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ, star (b x y) = b y x) →
      (∀ τ g, GlobalTheory.CuspGK.InK M τ g → ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ,
        b x (rTr V (atTau θ V τ g) y) = b (rTr V (atTau θ V τ g⁻¹) x) y) →
      (∀ τ, ∀ X ∈ lieAt V τ, ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ,
        b x (Rder θ V τ X y) = -b (Rder θ V τ X x) y) →
    ∃ e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ), e ψ = ψ ∧
      (∀ A : Submodule ℂ (GA D V → ℂ), A ≤ GlobalTheory.CuspGK.gkGen θ M ψ → GlobalTheory.CuspGK.IsGKSub θ M A → ∀ x ∈ A, e x ∈ A) ∧
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, e (e x) = e x) ∧
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ, b (e x) y = b x (e y)) ∧
      FiniteDimensional ℂ ((GlobalTheory.CuspGK.gkGen θ M ψ).map e) := by
  intro hP D θ V S M hθ ψ hψ hcusp hWex b hpos hherm hKadj hLie
  obtain ⟨W, hWfd, hψW, hWK⟩ := hWex
  have hWK' : KStable θ M W := fun τ g hg f hf => hWK τ g hg.1 hg.2 f hf
  set G := GlobalTheory.CuspGK.gkGen θ M ψ with hGdef
  set F := typeSpan (rhoK θ M) (W ⊓ G) G with hFdef
  haveI hFfd : FiniteDimensional ℂ F := _root_.GlobalTheory.T.admissible_KType_span_finiteDimensional hP θ V S M hθ ψ hψ hcusp W hWfd hψW hWK' b hpos hherm hKadj hLie
  have hFG : F ≤ G := typeSpan_le _ _ _
  have hprojG : ∀ F' : Submodule ℂ (GA D V → ℂ), F' ≤ G → FiniteDimensional ℂ F' →
      ∃ π : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ), (∀ x, π x ∈ F') ∧ ∀ x, ∀ f ∈ F', b (π x) f = b x f :=
    fun F' hF' hfd => GlobalTheory.T.exists_orthogonalProjection_posDef_sesquilinear_finiteDim b F' hfd (fun x hx => hpos x (hF' hx)) (fun x hx y hy => hherm x (hF' hx) y (hF' hy))
  obtain ⟨e, heF, hechar⟩ := hprojG F hFG hFfd
  have hfix : ∀ f ∈ F, e f = f := by
    intro f hf
    by_contra hne
    have hd : e f - f ∈ F := F.sub_mem (heF f) hf
    have h0 : b (e f - f) (e f - f) = 0 := by
      rw [show b (e f - f) = b (e f) - b f from map_sub b _ _, LinearMap.sub_apply, hechar f _ hd, sub_self]
    have := hpos _ (hFG hd) (sub_ne_zero.2 hne)
    rw [h0] at this
    simp at this
  have hψF : ψ ∈ F := le_typeSpan _ inf_le_right ⟨hψW, GlobalTheory.CuspGK.mem_gkGen θ M ψ⟩
  have hinvK : ∀ i : KIdx M, GlobalTheory.CuspGK.InK M i.1.1 i.1.2⁻¹ ∧ i.1.2⁻¹⁻¹ = i.1.2 := fun i => GlobalTheory.T.inMaxCompactOfModelFrame_inv M i.1.1 i.1.2 i.2
  let inv : KIdx M → KIdx M := fun i => ⟨(i.1.1, i.1.2⁻¹), (hinvK i).1⟩
  have hρG : ∀ i, ∀ x ∈ G, rhoK θ M i x ∈ G := (kStable_iff θ M G).1 (kStable_gkGen θ M ψ)
  have hadj : ∀ i, ∀ x ∈ G, ∀ y ∈ G, b (rhoK θ M i x) y = b x (rhoK θ M (inv i) y) := by
    intro i x hx y hy
    have h := hKadj i.1.1 i.1.2⁻¹ (hinvK i).1 x hx y hy
    rw [(hinvK i).2] at h
    exact h.symm
  refine ⟨e, hfix ψ hψF, ?_, fun x _ => hfix _ (heF x), ?_, ?_⟩
  · intro A hAG hA x hx
    obtain ⟨Y, hYfd, hxY, hYK⟩ := GlobalTheory.T.kFinite_of_mem_gKModuleGeneratedBy θ M hθ ψ hψ ⟨W, hWfd, hψW, hWK'⟩ x (hAG hx)
    haveI := hYfd
    have hst := (kStable_iff θ M (Y ⊓ A)).1 (kStable_inf θ M hYK (kStable_of_isGKSub θ M hA))
    have := GlobalTheory.T.typeSpanProjection_preserves_finiteDim_invariant_subspace b G (rhoK θ M) inv hpos hherm hρG hadj hprojG (W ⊓ G) e heF hechar (Y ⊓ A)
      inferInstance (inf_le_right.trans hAG) hst x ⟨hxY, hx⟩
    exact this.2
  · intro x hx y hy
    have h1 : b (e x) (y - e y) = 0 := by
      rw [← hherm _ (G.sub_mem hy (hFG (heF y))) _ (hFG (heF x)), map_sub, LinearMap.sub_apply,
        hechar y _ (heF x), sub_self, star_zero]
    have h2 : b (e x) y = b (e x) (e y) := by
      rw [map_sub] at h1
      exact sub_eq_zero.1 h1
    rw [h2, hechar x _ (heF y)]
  · refine Submodule.finiteDimensional_of_le (S₂ := F) ?_
    rintro _ ⟨x, -, rfl⟩
    exact heF x
end GlobalTheory.KTypeProj
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

theorem _root_.GlobalTheory.T.kType_projection_of_kFinite : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ → IsCuspFun V ψ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ f ∈ W, rTr V (atTau θ V τ g) f ∈ W) →
    ∀ b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ,
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, x ≠ 0 → 0 < (b x x).re) →
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ, star (b x y) = b y x) →
      (∀ τ g, GlobalTheory.CuspGK.InK M τ g → ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ,
        b x (rTr V (atTau θ V τ g) y) = b (rTr V (atTau θ V τ g⁻¹) x) y) →
      (∀ τ, ∀ X ∈ lieAt V τ, ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ,
        b x (Rder θ V τ X y) = -b (Rder θ V τ X x) y) →
    ∃ e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ), e ψ = ψ ∧
      (∀ A : Submodule ℂ (GA D V → ℂ), A ≤ GlobalTheory.CuspGK.gkGen θ M ψ → GlobalTheory.CuspGK.IsGKSub θ M A → ∀ x ∈ A, e x ∈ A) ∧
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, e (e x) = e x) ∧
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ, b (e x) y = b x (e y)) ∧
      FiniteDimensional ℂ ((GlobalTheory.CuspGK.gkGen θ M ψ).map e) := by
  first | exact @_root_.GlobalTheory.KTypeProj.kType_projection_mem | exact _root_.GlobalTheory.KTypeProj.kType_projection_mem | (intros; apply _root_.GlobalTheory.KTypeProj.kType_projection_mem <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace
noncomputable section
namespace GlobalTheory.KFinDecomp
theorem kFiniteDecomp_class_add : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (f f' : GA D N.V → ℂ), f ∈ Cls θ N U → f' ∈ Cls θ N U → f + f' ∈ Cls θ N U := by
  intro D θ hθ hPr N U f f' hf hf'
  obtain ⟨⟨a1, a2, a3⟩, a4⟩ := hf
  obtain ⟨⟨b1, b2, b3⟩, b4⟩ := hf'
  refine ⟨⟨GlobalTheory.Mem.AutSpace.isAutFunSm_add a1 b1, GlobalTheory.MultMem.isCuspFun_add a1.toIsAutFun b1.toIsAutFun a2 b2,
    fun τ => _root_.GlobalTheory.CuspGKForms.isTypeAt_add_cuspForm hPr hθ a1 b1 (a3 τ) (b3 τ)⟩, fun k hk hkf g => ?_⟩
  simp only [Pi.add_apply, a4 k hk hkf g, b4 k hk hkf g]
end GlobalTheory.KFinDecomp
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.kFinite_isotypic_decomposition_additive : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (f f' : GA D N.V → ℂ), f ∈ Cls θ N U → f' ∈ Cls θ N U → f + f' ∈ Cls θ N U := by
  first | exact @_root_.GlobalTheory.KFinDecomp.kFiniteDecomp_class_add | exact _root_.GlobalTheory.KFinDecomp.kFiniteDecomp_class_add | (intros; apply _root_.GlobalTheory.KFinDecomp.kFiniteDecomp_class_add <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open MeasureTheory GlobalTheory.Grow GlobalTheory.Size
open scoped ENNReal
namespace GlobalTheory.KFinCuspApprox
theorem kFinite_cusp_approx_at_one_place : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (φ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → ∀ (τ : D.what₂.Tau) (a : ℕ) (δ : ℝ), 0 < δ → ∃ e : Formalism.REAL.KG (N.M.ε τ) → ℂ, Continuous e ∧ GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e ∧ ∀ g, ‖φ g - GlobalTheory.KFinCuspApprox.avgN θ N τ e φ g‖ * GlobalTheory.Grow.quotHeight N.V g ^ a ≤ δ := by
  intro hP D θ hθ N φ hφ τ a δ hδ
  obtain ⟨hA, hc, -⟩ := id hφ
  obtain ⟨U, hU, hlev⟩ := hA.level
  obtain ⟨d, C, hC⟩ := hP.cuspDecaySobolev D θ hθ N.V U hU 0 a
  have hr := rapidDecSm_of_cuspForm hP.cuspRapidDecay hθ hA hc
  have hη : 0 < δ / ((C : ℝ) + 1) := div_pos hδ (by positivity)
  obtain ⟨e, he, hgrow⟩ := GlobalTheory.KAvgApprox.one_place D θ hθ N.V τ (N.M.ε τ) (N.M.fr τ) (N.M.fr_unit τ) (N.M.fr_gram τ) φ hr d _ hη
  have hec : Continuous e := by obtain ⟨F, -, h1, h2, -⟩ := he; exact h2 _ h1
  have hav := GlobalTheory.KAvgApprox.avg_rapid D θ hθ N.V τ (N.M.ε τ) (N.M.fr τ) (N.M.fr_unit τ) (N.M.fr_gram τ) e hec φ hr
  set ψ : GA D N.V → ℂ := φ - avgN θ N τ e φ with hψ
  have hψr : RapidDecSm θ N.V ψ := by
    have := hr.add (hav.smul (-1))
    rwa [neg_one_smul, ← sub_eq_add_neg] at this
  have hψc : IsCuspFun N.V ψ := by
    have h2 := _root_.GlobalTheory.T.kFinite_cuspForm_average_approx θ hθ hP N τ e hec φ hA hc
    have := GlobalTheory.MultMem.isCuspFun_add hr.toIsAutFun (hav.smul (-1)).toIsAutFun hc (GlobalTheory.MultMem.isCuspFun_smul (-1) h2)
    rwa [neg_one_smul, ← sub_eq_add_neg] at this
  have hψlev : ∀ k ∈ U, k ∈ GfC N.V → ∀ x, ψ (x * k) = ψ x := by
    intro k hk hk' x
    simp only [hψ, Pi.sub_apply, hlev k hk hk' x]
    congr 1
    show (∫ k', e k' * φ (x * k * _) ∂_) = ∫ k', e k' * φ (x * _) ∂_
    congr 1; funext k'
    rw [mul_assoc, ← Formalism.IndefR.Eqv.Act.comm_inf_fin (Formalism.IndefR.Eqv.Act.atTau_mem θ τ _) hk', ← mul_assoc, hlev k hk hk']
  refine ⟨e, hec, he, fun g => ?_⟩
  have h1 := hC ψ hψr.toIsAutFun hψlev hψr.smooth (GlobalTheory.CuspApproxAll.growthSob_zero_ne_top hψr) hψc
  have h2 : decaySize N.V a ψ ≤ ENNReal.ofReal δ := by
    have h4 : (C : ℝ≥0∞) * growthSob θ N.V d 0 ψ ≤ C * ENNReal.ofReal (δ / ((C : ℝ) + 1)) := by gcongr
    refine h1.trans (h4.trans ?_)
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [NNReal.coe_nonneg C]
  have h3 : ENNReal.ofReal (‖ψ g‖ * quotHeight N.V g ^ a) ≤ ENNReal.ofReal δ :=
    (le_iSup (fun x => ENNReal.ofReal (‖ψ x‖ * quotHeight N.V x ^ a)) g).trans h2
  rw [ENNReal.ofReal_le_ofReal_iff hδ.le] at h3
  simpa [hψ] using h3
end GlobalTheory.KFinCuspApprox
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.cuspForm_approximation_single_place : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (φ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → ∀ (τ : D.what₂.Tau) (a : ℕ) (δ : ℝ), 0 < δ → ∃ e : Formalism.REAL.KG (N.M.ε τ) → ℂ, Continuous e ∧ GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e ∧ ∀ g, ‖φ g - GlobalTheory.KFinCuspApprox.avgN θ N τ e φ g‖ * GlobalTheory.Grow.quotHeight N.V g ^ a ≤ δ := by
  first | exact @_root_.GlobalTheory.KFinCuspApprox.kFinite_cusp_approx_at_one_place | exact _root_.GlobalTheory.KFinCuspApprox.kFinite_cusp_approx_at_one_place | (intros; apply _root_.GlobalTheory.KFinCuspApprox.kFinite_cusp_approx_at_one_place <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.CuspValueTypeAt
theorem cusp_value_hasTypeAt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau),
    IsInfFam θ → N.V.SigOK → GoodPar N.V.rank (N.V.sig (tauE D τ)).1 (N.V.sig (tauE D τ)).2 (N.S τ) →
    ∀ F ∈ N.Cusp θ, ∀ w, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt θ N.V τ (N.S τ) (F w) := by
  intro hP D θ N τ hθ hN _ F hF w
  exact _root_.GlobalTheory.CuspValueType.hasTypeAt_cusp_of_cusp_value_type hP θ hθ N hN F hF w τ
end GlobalTheory.CuspValueTypeAt
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.twist_cusp_value_hasTypeAt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau), IsInfFam θ → N.V.SigOK → GoodPar N.V.rank (N.V.sig (tauE D τ)).1 (N.V.sig (tauE D τ)).2 (N.S τ) → ∀ F ∈ N.Cusp θ, ∀ w, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt θ N.V τ (N.S τ) (F w) := by
  first | exact @_root_.GlobalTheory.CuspValueTypeAt.cusp_value_hasTypeAt | exact _root_.GlobalTheory.CuspValueTypeAt.cusp_value_hasTypeAt | (intros; apply _root_.GlobalTheory.CuspValueTypeAt.cusp_value_hasTypeAt <;> assumption)
end
end

section

section
namespace GlobalTheory.PairLift
theorem thetaPairLift_cuspidal_of_hypotheses : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal := fun h =>
  liftsCuspidal_of_functoriality h.discreteSeriesCover h.harishChandraModules h.cuspRapidDecay h.casselmanWallach
end GlobalTheory.PairLift
end

section

theorem _root_.GlobalTheory.T.twisted_thetaLift_cuspidal : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal := by
  first | exact @_root_.GlobalTheory.PairLift.thetaPairLift_cuspidal_of_hypotheses | exact _root_.GlobalTheory.PairLift.thetaPairLift_cuspidal_of_hypotheses | (intros; apply _root_.GlobalTheory.PairLift.thetaPairLift_cuspidal_of_hypotheses <;> assumption)
end
end
