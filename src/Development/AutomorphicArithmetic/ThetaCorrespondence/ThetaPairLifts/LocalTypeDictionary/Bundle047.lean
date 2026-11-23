module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1368
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1720
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1609
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1758
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle190
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle018
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle678
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle503
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle524
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle626
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle633
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle402
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle670
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle514
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle528
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1846
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle527
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle022
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle042
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle037
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle547
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle040
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero

@[expose] public section

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Filter Topology
open GlobalTheory.AdelicU
noncomputable section
open scoped Classical
namespace GlobalTheory.ThetaLineDerFirst
theorem hasDerivAt_thetaSum_along_line : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Y, ∀ (m : ℕ) (f f₁ : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
    (∀ i, (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = M.vac v) →
    (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) (f i) (f₁ i)) →
    ∀ u, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (om (γ (Multiplicative.ofAdd t), 1) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)))))
      (GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i)))) 0 := by
  intro hP F E _ _ _ _ _ σ n d Y Wd M ψ χX χW om hψ hG hW γ hγ m f f₁ φ hφ hD u
  have hstd : ∀ i, ∀ᶠ v in Filter.cofinite, φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1 :=
    fun i => ((hφ i).2.and hG.std).mono fun v h => h.1.trans h.2
  have hmem : ∀ i (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (φ i) ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) :=
    fun i g => GlobalTheory.TensUniq.pure_mem_schA g (φ i) (hφ i).1 (hstd i)
  have hpres := (GlobalTheory.WeilM.IsUWeilPair.isUSplitting hW).pres
  have hcurve : (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (om (γ (Multiplicative.ofAdd t), 1) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)))))
      = fun t => ∑ i, GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (om (γ (Multiplicative.ofAdd t), 1)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (f i) (fun x => ∏ᶠ v, φ i v fun j => evFin F v (x j))))) := by
    funext t

    rw [map_sum]
    exact GlobalTheory.ThetaLineDer.rho_sum M ψ hψ u _ (fun i => hpres _ _ (hmem i (f i)))
  have hend : GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i))) =
      ∑ i, GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (f₁ i) (fun x => ∏ᶠ v, φ i v fun j => evFin F v (x j)))) :=
    GlobalTheory.ThetaLineDer.rho_sum M ψ hψ u _ (fun i => hmem i (f₁ i))
  have hi : ∀ i, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (om (γ (Multiplicative.ofAdd t), 1)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (f i) (fun x => ∏ᶠ v, φ i v fun j => evFin F v (x j))))))
      (GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u
                   (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (f₁ i) (fun x => ∏ᶠ v, φ i v fun j => evFin F v (x j))))) 0 :=
    fun i => _root_.GlobalTheory.T.thetaSum_differentiable_along_line hP M ψ χX χW om hψ hG hW γ hγ (f i) (f₁ i) _
      (GlobalTheory.ThK.EvUniqInf.rest_pure (f i) (φ i) (hφ i).1 (hstd i)) (hD i) u
  rw [hcurve, hend]
  have := HasDerivAt.sum (u := Finset.univ) fun i _ => hi i
  simpa [Finset.sum_fn] using this
end GlobalTheory.ThetaLineDerFirst
end
end
end

section

section
noncomputable section
open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
namespace GlobalTheory.RealLift.FockFirst
section SlopeTestRemainingChoices
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end SlopeTestRemainingChoices
theorem exists_fockMap_first_order_of_real_lift (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W)
    (om' : Rep σ G.V' G.W) (h : IsTriple B G X om om') :
    ∃ (A : InfinitePlace F → Matrix (Fin a) (Ix (a - G.p) G.p) ℂ)
      (Φ : Tens F (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')))
      (c : InfinitePlace F → ℂ),
      (∀ w, IsFrame ((1 : ℂ) • (incM F G.V.J).map (piInf (B.emb w))) (A w)) ∧
      (∀ w, G.V.θ w * A w = A w * Jm (a - G.p) G.p) ∧
      LinearMap.range Φ = G.M.Pol B.ψ B.emb ∧
      ActsBy B.emb A (om.comp (MonoidHom.inl _ _)) Φ
        (fockAct1 (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q)) c := by
  obtain ⟨hb, hg, hc, hw, -⟩ := h
  choose A hA hAθ using fun w => GlobalTheory.RealLift.frameEx_holds _ _ _ _ _ (hg.hV.sig w) (hg.hV.cartan w)
  choose C hC hCθ using fun w => GlobalTheory.RealLift.frameEx_holds _ _ _ _ _ (hg.hW.sig w) (hg.hW.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F G.V.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_piInf, one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F G.W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [incM_map_piInf]; exact hC w
  have fr : Framed B.emb (incM F G.V.J) (incM F G.W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  have hder : DerEx := GlobalTheory.T.archHeisenbergDerivatives_exist
  have hvl : VacLine := GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hder
  have hfe : FockEx := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives hder
  have hsec : LieSecond := _root_.GlobalTheory.T.real_lift_lie_second_order hP hder hfe hvl (_root_.GlobalTheory.T.weil_lie_algebra_scalar_action hP hder hvl)
  have hfst : LieFirst := GlobalTheory.RealLift.LieFirstPf.lieFirst_of_lieSecond hsec
  have hpr : PolRange := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws GlobalTheory.RealLift.actsLaws hder hvl
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := hpr F E σ _ _ _ _ _ _ G.V G.W G.M B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := hw
  obtain ⟨d, hd, hB1⟩ := hwp.2.1
  have hW1 := hfst F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co d 1 Complex.I A C Φ _ _ _ hb.cm hb.std fr hΦ hd hB1
    (hasExp_div B.emb hc.expβ hc.expα)
  exact ⟨A, Φ, _, hA1, hAθ, hr, hW1⟩
end GlobalTheory.RealLift.FockFirst
end
end

section

theorem _root_.GlobalTheory.T.real_lift_exists_fock_map : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∃ (A : NumberField.InfinitePlace F → Matrix (Fin a) (Formalism.BasicNotions.TH.Ix (a - Γ.p) Γ.p) ℂ)
      (Φ : GlobalTheory.RealLift.Tens F (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q) →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')))
      (c : NumberField.InfinitePlace F → ℂ),
      (∀ w, GlobalTheory.RealLift.IsFrame ((1 : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Γ.V.J).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w))) (A w)) ∧
      (∀ w, Γ.V.θ w * A w = A w * Formalism.BasicNotions.TH.Jm (a - Γ.p) Γ.p) ∧
      LinearMap.range Φ = Γ.M.Pol Bs.ψ Bs.emb ∧
      GlobalTheory.RealLift.ActsBy Bs.emb A (om.comp (MonoidHom.inl _ _)) Φ
        (Formalism.BasicNotions.TH.fockAct1 (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q)) c := by
  first | exact @_root_.GlobalTheory.RealLift.FockFirst.exists_fockMap_first_order_of_real_lift | exact _root_.GlobalTheory.RealLift.FockFirst.exists_fockMap_first_order_of_real_lift | (intros; apply _root_.GlobalTheory.RealLift.FockFirst.exists_fockMap_first_order_of_real_lift <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.FlipRun
theorem cuspStep_down_of_large_flipRun : (∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidalSmoothAt D) → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch =>
  ∀ (t : T) (M : Vol ch.G), M.Is t → ∀ a : Arrow T, IsGridArrow D.R.m t a → (∃ i j, a = Arrow.down t i j) →
    ∀ e, IsIdemSum e (locPl ch.G t) → ∀ φ f, IsLocVec ch.W a.pair e (vacOf ch.rm a) φ f →
    ∀ (Q : PolF D (ch.G.pT a.pair).rank (ch.G.pS a.pair).rank) (F : Fn ch.G a.src), IsCuspListed ch.W.θ a.src F →
      LiftConv ch.W M a (ch.W.fock a.pair f Q) F ∧ IsCuspListed ch.W.θ a.tgt (liftA ch.W M a (ch.W.fock a.pair f Q) F) := by
  intro hS hP
  refine ⟨0, fun ε CF _ => ⟨0, ?_⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hset ch hch hsc t M hMt a ha hdown e he φ f hf Q Fn hFn
  obtain ⟨i, j, rfl⟩ := hdown
  have hgap : ch.sc.cGap = 1 := by rw [hsc]
  obtain ⟨hi, hj⟩ : i ≤ D.R.m ∧ j < D.R.m := by
    rcases ha with ⟨_, _, _, _, h⟩ | ⟨i', j', h1, h2, h⟩
    · cases h
    · cases h; exact ⟨h1, h2⟩
  obtain ⟨G, hG, hMa⟩ := GlobalTheory.GridJoin.exists_gridPre hP.discreteSeriesUpqExists hP.discreteSeriesCover
    hP.harishChandraModules hset.host hset.size hset.core hgap ch.W hch.weil
  have hRB : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R :=
    ⟨hset.core.lev, hset.core.models.inf, hset.core.models.νY, hset.core.models.νY', hset.core.models.νX⟩
  have hCS := hS D (GlobalTheory.RowSizes.sizes_of_sizeRows large₂ hset.size) Γ Pl0 T A Ks R G hRB hG
  have eA := ga_eq_of_match hMa hi (Nat.succ_le_of_lt hj)
  have eB := ga_eq_of_match hMa hi hj.le
  have hΨ := GlobalTheory.T.isThetaFunction_fock_vector_downward_arrow ch.rm t i j hi hj he hf Q
  obtain ⟨Φ, hΦ, hK⟩ := GlobalTheory.T.thetaKernel_downward_testGrid_eq_sender_grid ch.W hch.weil G hG hMa t i j hi hj eA eB _ hΨ
  have hF' := (GlobalTheory.T.isCuspTyped_testGrid_iff_sender_grid_conj hset hgap ch.W hch.weil G hG hMa i (j + 1) hi (Nat.succ_le_of_lt hj) eA Fn).1 hFn
  obtain ⟨hint, hcusp⟩ := hCS.th t i j hi hj Φ hΦ _ hF'
  have hθ : ch.W.θ = R.θ := hch.weil.θ
  have hinv : ∀ h, ∀ γ ∈ GQ (ch.G.V (.grid i (j + 1))), ∀ g,
      (fun g => ch.W.kerA (.down t i j) (ch.W.fock (.mu t i j) f Q) g h * Fn g) (γ * g) =
      (fun g => ch.W.kerA (.down t i j) (ch.W.fock (.mu t i j) f Q) g h * Fn g) g := fun h γ hγ g => by
    simp only [GlobalTheory.T.thetaKernel_downward_arrow_left_invariant ch.W t i j hi hj _ hΨ h γ hγ g, hFn.1.toIsAutFun.left γ hγ g]
  have key := fun h => GlobalTheory.T.testGrid_measure_domain_downward_eq_sender hset hgap ch.W hch.weil G hG hMa M t hMt i j hi hj eA
    (fun g => ch.W.kerA (.down t i j) (ch.W.fock (.mu t i j) f Q) g h * Fn g) (hinv h)
  have hcb : ∀ h : GA D (ch.G.V (.grid i j)), cast eB (cast eB.symm h) = h := fun h => cast_cast _ _ h
  refine ⟨fun h => ?_, ?_⟩
  · rw [← hcb h]
    refine (key _).1.1 ?_
    simpa only [hK] using hint (cast eB.symm h)
  · refine (GlobalTheory.T.isCuspTyped_testGrid_iff_sender_grid_conj hset hgap ch.W hch.weil G hG hMa i j hi hj.le eB _).2 ?_
    convert hcusp using 2 with h
    rw [liftA_apply, ← (key _).2]
    simp only [hK]
end GlobalTheory.FlipRun
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.flipRun_descending_cusp_transition : (∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidalSmoothAt D) → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch =>
  ∀ (t : T) (M : Vol ch.G), M.Is t → ∀ a : Arrow T, IsGridArrow D.R.m t a → (∃ i j, a = Arrow.down t i j) →
    ∀ e, IsIdemSum e (locPl ch.G t) → ∀ φ f, IsLocVec ch.W a.pair e (vacOf ch.rm a) φ f →
    ∀ (Q : PolF D (ch.G.pT a.pair).rank (ch.G.pS a.pair).rank) (F : Fn ch.G a.src), IsCuspListed ch.W.θ a.src F →
      LiftConv ch.W M a (ch.W.fock a.pair f Q) F ∧ IsCuspListed ch.W.θ a.tgt (liftA ch.W M a (ch.W.fock a.pair f Q) F) := by
  first | exact @_root_.GlobalTheory.FlipRun.cuspStep_down_of_large_flipRun | exact _root_.GlobalTheory.FlipRun.cuspStep_down_of_large_flipRun | (intros; apply _root_.GlobalTheory.FlipRun.cuspStep_down_of_large_flipRun <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.RightArrowCusp
theorem cuspStep_rightward : (∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidalSmoothAt D) → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch =>
  ∀ (t : T) (M : Vol ch.G), M.Is t → ∀ a : Arrow T, IsGridArrow D.R.m t a → (∃ i j, a = Arrow.right i j) →
    ∀ e, IsIdemSum e (locPl ch.G t) → ∀ φ f, IsLocVec ch.W a.pair e (vacOf ch.rm a) φ f →
    ∀ (Q : PolF D (ch.G.pT a.pair).rank (ch.G.pS a.pair).rank) (F : Fn ch.G a.src), IsCuspListed ch.W.θ a.src F →
      LiftConv ch.W M a (ch.W.fock a.pair f Q) F ∧ IsCuspListed ch.W.θ a.tgt (liftA ch.W M a (ch.W.fock a.pair f Q) F) := by
  intro hLS hP
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hSet ch hch hsc => ?_⟩⟩
  intro t M hM a ha hr e he φ f hf Q F' hF
  obtain ⟨i, j, rfl⟩ := hr
  obtain ⟨i', j', hi, hj, h'⟩ | ⟨_, _, _, _, _, h'⟩ := ha
  · cases h'
    have hcg : ch.sc.cGap = 1 := by rw [hsc]
    obtain ⟨G, hG, hMa⟩ := GlobalTheory.GridJoin.exists_gridPre hP.discreteSeriesUpqExists hP.discreteSeriesCover
      hP.harishChandraModules hSet.host hSet.size hSet.core hcg ch.W hch.weil
    have hRB : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R :=
      ⟨hSet.core.lev, hSet.core.models.inf, hSet.core.models.νY, hSet.core.models.νY', hSet.core.models.νX⟩
    have hSm := (hLS D (GlobalTheory.RowSizes.sizes_of_sizeRows large₂ hSet.size) Γ Pl0 T A Ks R G hRB hG).X t i j hi hj
    have hgm := meas_haar_fund hSet.core G hG t i j hi.le hj
    exact lift_right_of_smooth hcg ch.W hch.weil ch.rm hch.vac M t hM i j hi hj (G.V i j) (G.V (i + 1) j)
      (hMa.1.vert i j hi.le hj).sp (hMa.1.vert (i + 1) j hi hj).sp (vert_par hSet.core G hG i j hi.le hj)
      (vert_par hSet.core G hG (i + 1) j hi hj) (G.meas t i j) hgm.1 hgm.2 (G.X i j).ω (hMa.2.omX i j hi hj) hSm
      e he φ f hf Q F' hF
end GlobalTheory.RightArrowCusp
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.cusp_transition_rightward : (∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidalSmoothAt D) → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch =>
  ∀ (t : T) (M : Vol ch.G), M.Is t → ∀ a : Arrow T, IsGridArrow D.R.m t a → (∃ i j, a = Arrow.right i j) →
    ∀ e, IsIdemSum e (locPl ch.G t) → ∀ φ f, IsLocVec ch.W a.pair e (vacOf ch.rm a) φ f →
    ∀ (Q : PolF D (ch.G.pT a.pair).rank (ch.G.pS a.pair).rank) (F : Fn ch.G a.src), IsCuspListed ch.W.θ a.src F →
      LiftConv ch.W M a (ch.W.fock a.pair f Q) F ∧ IsCuspListed ch.W.θ a.tgt (liftA ch.W M a (ch.W.fock a.pair f Q) F) := by
  first | exact @_root_.GlobalTheory.RightArrowCusp.cuspStep_rightward | exact _root_.GlobalTheory.RightArrowCusp.cuspStep_rightward | (intros; apply _root_.GlobalTheory.RightArrowCusp.cuspStep_rightward <;> assumption)
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
noncomputable section
namespace GlobalTheory.SplitMoveKappa
theorem movedKappa_split : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (κ : ℂ), GlobalTheory.MovedKappaEx.JetKap ch p x y κ →
    ∀ (e : Formalism.L2.Theta.AE D), IsSplitIdem D e → ∀ (s : FinPt ch.G p.small) (s' : FinPt ch.G p.big),
    SuppAt e _ (s : GA D (ch.G.V p.small)) → SuppAt e _ (s' : GA D (ch.G.V p.big)) →
    ∃ c : ℂ, Mod1All c ∧ (∀ (q : ℕ) [Fact q.Prime], GlobalTheory.MovedKappaEx.OffPrime e q → GlobalTheory.MovedKappaEx.UnitAt q c) ∧
      GlobalTheory.MovedKappaEx.JetKap ch p (s * x) (s' * y) (c * κ) := by
  intro hP hI D Γ _ _ Pl0 T A Ks _ _ _ R ch hch p hp x y κ hJ e he s s' hs hs'
  obtain ⟨x₀, y₀, hx₀, hy₀, ζ, ⟨n, hn, hζ⟩, r, hr, hJ'⟩ := _root_.GlobalTheory.T.twist_jetKappa_split_move hP hI ch hch p hp x y κ hJ e he s s' hs hs'
  have h1 := _root_.GlobalTheory.T.twist_norm_kappa_moved_place hP hI ch hch p hp x y κ hJ
  have h2 := _root_.GlobalTheory.T.twist_norm_kappa_moved_place hP hI ch hch p hp _ _ _ hJ'
  have hζn : ‖ζ‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 (by rw [← norm_pow, hζ, norm_one])
  have hχn : ‖((((ch.G.chrT p x₀)⁻¹ * ch.G.chrS p y₀ : Circle)) : ℂ)‖ = 1 := Circle.norm_coe _
  have hr1 : (r : ℂ) = 1 := by
    rw [norm_mul, norm_mul, norm_mul, hζn, hχn, h1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at h2
    simp only [mul_one] at h2
    rw [h2]; simp
  rw [hr1, one_mul] at hJ'
  have hA := _root_.GlobalTheory.T.twist_split_character_values hP hI ch hch p hp e he x₀ hx₀
  have hB := _root_.GlobalTheory.T.twist_split_character_values hP hI ch hch p hp e he y₀ hy₀
  have hco : ((((ch.G.chrT p x₀)⁻¹ * ch.G.chrS p y₀ : Circle)) : ℂ) =
      ((ch.G.chrT p x₀ : Circle) : ℂ)⁻¹ * ((ch.G.chrS p y₀ : Circle) : ℂ) := by
    rw [Circle.coe_mul, Circle.coe_inv]
  have hm : Mod1All ((((ch.G.chrT p x₀)⁻¹ * ch.G.chrS p y₀ : Circle)) : ℂ) := by
    rw [hco]
    exact GlobalTheory.FamilyTieProof.mod1All_mul' (GlobalTheory.FamilyTieProof.mod1All_inv hA.1.2) hB.1.1
  refine ⟨ζ * ((((ch.G.chrT p x₀)⁻¹ * ch.G.chrS p y₀ : Circle)) : ℂ), GlobalTheory.FamilyTieProof.mod1All_mul' (mod1All_root hn hζ) hm,
    fun q _ hq => ?_, hJ'⟩
  refine unitAt_mul (qbar_of_root hn hζ) hm.1 (unitAt_root q hn hζ) ?_
  rw [hco]
  exact unitAt_mul (inv_mem hA.1.2.1) hB.1.1.1 (unitAt_inv hA.1.2.1 ((hA.2 q hq).2)) ((hB.2 q hq).1)
end GlobalTheory.SplitMoveKappa
end
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

theorem _root_.GlobalTheory.T.splitting_of_moved_kappa_twist : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (κ : ℂ), GlobalTheory.MovedKappaEx.JetKap ch p x y κ →
    ∀ (e : Formalism.L2.Theta.AE D), IsSplitIdem D e → ∀ (s : FinPt ch.G p.small) (s' : FinPt ch.G p.big),
    SuppAt e _ (s : GA D (ch.G.V p.small)) → SuppAt e _ (s' : GA D (ch.G.V p.big)) →
    ∃ c : ℂ, Mod1All c ∧ (∀ (q : ℕ) [Fact q.Prime], GlobalTheory.MovedKappaEx.OffPrime e q → GlobalTheory.MovedKappaEx.UnitAt q c) ∧
      GlobalTheory.MovedKappaEx.JetKap ch p (s * x) (s' * y) (c * κ) := by
  first | exact @_root_.GlobalTheory.SplitMoveKappa.movedKappa_split | exact _root_.GlobalTheory.SplitMoveKappa.movedKappa_split | (intros; apply _root_.GlobalTheory.SplitMoveKappa.movedKappa_split <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Filter Topology
open GlobalTheory.AdelicU
open scoped Classical
theorem GlobalTheory.Twist.twist_smoothLine_isPure : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Wd, ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
    ∃ (c : ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
      (∀ t : ℝ, om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c t) φ) ∧
      Tendsto (fun t : ℝ => t⁻¹ • (c t - c 0)) (𝓝[≠] 0) (𝓝 g) := by
  intro hP F E _ _ _ _ _ σ n d Y Wd M ψ χX χW om hCM hψ hM hW γ hγ f φ hφ hv
  have h1 := fun t : ℝ => GlobalTheory.T.archimedeanPoint_pureTensor_keeps_finiteFactor M ψ χX χW om hψ hM hW (γ (Multiplicative.ofAdd t)) (hγ.2 _) f φ hφ hv
  choose c hc using h1
  by_cases h : ∃ y : Fin n × Fin d → AF F, ∏ᶠ v, φ v (fun i => evFin F v (y i)) ≠ 0
  · obtain ⟨g, hg⟩ := _root_.GlobalTheory.T.pure_tensor_theta_smooth_along_line hP M ψ χX χW om hCM hψ hM hW γ hγ f φ hφ hv h c hc
    exact ⟨c, g, hc, hg⟩
  · push_neg at h
    have h0 : ∀ c' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure c' φ = 0 := fun c' => by
      funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, h x]
    refine ⟨fun _ => 0, 0, fun t => ?_, ?_⟩
    · rw [h0 f, h0 0, map_zero]
    · simp
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Filter Topology
open GlobalTheory.AdelicU
open scoped Classical

theorem _root_.GlobalTheory.T.twisted_smoothLine_pure_weight : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Wd, ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
    ∃ (c : ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
      (∀ t : ℝ, om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c t) φ) ∧
      Tendsto (fun t : ℝ => t⁻¹ • (c t - c 0)) (𝓝[≠] 0) (𝓝 g) := by
  first | exact @_root_.GlobalTheory.Twist.twist_smoothLine_isPure | exact _root_.GlobalTheory.Twist.twist_smoothLine_isPure | (intros; apply _root_.GlobalTheory.Twist.twist_smoothLine_isPure <;> assumption)
end
end
