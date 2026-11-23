module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle006
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle020
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeScalingAtS0
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle148
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle733
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle008
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle005
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsFinCombSingleZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle481
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle536
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle483
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle712
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle732
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle506
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle730
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle638
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianAdjointLawsStandardCharacter
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle599
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle507
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle724
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle187
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle726
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SingleCosetOffTwistPlacesLargeDepth
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
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle410
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

theorem _root_.GlobalTheory.T.heckeKernel_complex_point_matches_cosets : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i σ hV →
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
    ∀ (h : GA D (Wc D i))
      (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).dom),
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
      ∃ e : hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) ≃ Rc,
        ∀ C z, hkRelFr P.asIdeal p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p) (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) C z →
          ∃ (hx' : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * (e C : GA D (Wc D i)))).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * (e C : GA D (Wc D i)))).1).dom) (t : Ix (T.Q.Dw ((i : ℕ) + 1)) → (CAt σ)ˣ),
            (∀ j, j ≠ none → t j = 1) ∧ FrBor t ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * (e C : GA D (Wc D i)))).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * (e C : GA D (Wc D i)))).2, hx'⟩) z := by
  first | exact @GlobalTheory.HeckeTermIdent.heckeKernelCoset | exact GlobalTheory.HeckeTermIdent.heckeKernelCoset | (intros; apply GlobalTheory.HeckeTermIdent.heckeKernelCoset <;> assumption)
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.CharXFB

theorem _root_.GlobalTheory.T.lattice_scaling_at_S0 : All fun {D} _ _ {sc} {G} _ _ => ∀ i, i < D.R.m → ∀ u ∈ latRow G i, ∀ v ∈ G.pl.S0, ∀ y ∈ latV (G.V (.grid (i + 1) 0)) (G.Λ (.grid (i + 1) 0)) (· = v), ∀ s ∈ GlobalTheory.SeeSaw.idV (D.host.AA⁻¹ * ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) v, s • (u *ᵥ y) ∈ latV (G.V (.grid i 0)) (G.Λ (.grid i 0)) (· = v) := by
  first | exact @GlobalTheory.DepthMap.smul_mulVec_mem_latV | exact GlobalTheory.DepthMap.smul_mulVec_mem_latV | (intros; apply GlobalTheory.DepthMap.smul_mulVec_mem_latV <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.AnnOpen

theorem latRow_ann_open : All fun {D} _ _ {sc} {G} W _ => ∀ i, i < D.R.m → ∃ U : Set (WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0))),
    IsOpen U ∧ (0 : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0))) ∈ U ∧
    ∀ u' ∈ U, MxAt (fun _ => True) u' → ∀ u ∈ latRow G i, W.ψ (symplO _ _ u u') = 1 := by
  intro D hq T L μ0 hL sc G W M hM i hi
  have sdG : ∀ i, i ≤ D.R.m → IsSelfDualC (G.V (.grid i 0)) (G.Λ (.grid i 0)) := by
    intro i hi
    cases i with
    | zero =>
      obtain ⟨c, hc⟩ := (hL.βY 0 (by have := D.R.two_le_m; omega) : ∃ c, _)
      exact Formalism.IndefR.Eqv.KerDiag.isSelfDualC_of_base hc
    | succ i => exact (G.sp.V_is (i + 1) 0 (by omega) hi (by omega)).sd
  have hS : IsSelfDualC (G.pS (.chi i 0)) (G.latS (.chi i 0)) := isSelfDualC_neg (sdG (i + 1) hi)
  have hT : IsSelfDualC (G.pT (.chi i 0)) (G.latT (.chi i 0)) := sdG i hi.le
  have hfin := GlobalTheory.T.isFiniteAdelicMatrixLattice_depthLatticeOfPair G (.chi i 0) hS hT
  obtain ⟨U, hU, h0, hUA⟩ := hfin.opn
  refine ⟨U, hU, h0, fun u' hu' hfu' u hu => ?_⟩
  have hu'R : u' ∈ latRow G i := hUA u' hu' hfu'
  have key := (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ W.ψ_std _ _ _ _ hS hT (fun _ => True) u (hfin.fin u hu)).1 hu.1 u' hu'R.1
  have e : symplO (G.pS (.chi i 0)) (G.pT (.chi i 0)) u u' = -symplO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) u u' := by
    have hinv : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) D.host.E), (-A)⁻¹ = -A⁻¹ := by
      intro n A
      by_cases h : IsUnit A.det
      · exact Matrix.inv_eq_left_inv (by rw [neg_mul_neg, Matrix.nonsing_inv_mul A h])
      · have h' : ¬ IsUnit (-A).det := by
          rw [Matrix.det_neg]
          intro hu
          exact h (isUnit_of_mul_isUnit_right hu)
        rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h', neg_zero]
    simp only [symplO, hO, negSp_gram, hinv, Matrix.neg_apply, map_neg, neg_mul, mul_neg, Finset.sum_neg_distrib]
  rw [e, AddChar.map_neg_eq_inv] at key
  exact inv_eq_one.mp key

end GlobalTheory.AscFin.AnnOpen

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain (IsVacVec ptOf)
open GlobalTheory.PairLift (adjO)
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.CosDatum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cA_cA₀ {D : D7} (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => show a ⊗ₜ[D.host.F] star (star x) = _; rw [star_star]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem latO_le_true {D : D7} (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO S T LS LT P ≤ latO S T LS LT fun _ => True := by
  apply AddSubgroup.closure_mono
  rintro w ⟨α, hα, -, rest⟩
  exact ⟨α, hα, fun v h => (h trivial).elim, rest⟩

theorem isLatVac_mono {D : D7} {m n : ℕ} {hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)} {Λ Λ' : AddSubgroup (Mx D m n)}
    (h : Λ' ≤ Λ) {f : Mx D m n → ℂ} (hf : IsLatVac hs Λ f) : IsLatVac hs Λ' f :=
  ⟨fun u hu => hf.1 u (h hu), fun e he u hu hh => hf.2 e he u (h hu) hh⟩

theorem addChar_ne_zero {A : Type} [AddGroup A] (ψ : AddChar A ℂ) (a : A) : ψ a ≠ 0 := fun h => by
  have := ψ.map_add_eq_mul a (-a)
  rw [add_neg_cancel, ψ.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

end GlobalTheory.CosDatum

namespace GlobalTheory.CoreOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.CosDatum in
theorem datumEx : DatumEx := by
  intro D hq T L μ0 hL sc G W M hM i hi r r' hr hr' S S' MM MM' x₀ hx₀
  have hψ : IsStdChar D W.ψ (-1) := W.ψ_std
  have hθ : IsInfFam W.θ := W.θ_is
  have hEx : ExchLaw D := GlobalTheory.T.adjointExchange_laws_thetaHeisenberg D
  have hLE : LatExch := GlobalTheory.T.coreChain_adjoint_latticeExchange
  have hadj := GlobalTheory.AdjLawPf.adjLaw D W.ψ hψ (G.V (.core i)) (G.V (.core (i + 1)))
  obtain ⟨e, he, -⟩ := W.cosVec_is
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.T.thetaChain_unitVacuum_otherLattices_exists D hq T L μ0 hL sc G W M hM i hi r r' S S' MM MM'
  obtain ⟨R, hR1, hR2, hR3, hR4⟩ := GlobalTheory.T.exists_representatives_half_quotient_pairing_trivial_depthLattice D hq T L μ0 hL sc G W M hM i hi e he
  have hxi := GlobalTheory.T.corePair_integralPoint_pairs_trivially_half D hq T L μ0 hL sc G W M hM i hi e he x₀ hx₀
  have hhalf : ∀ z ∈ R, IsHalf e (adjO (G.V (.core i)) (G.V (.core (i + 1))) z) := fun z hz => by
    have := hadj.half _ z (hR1 z hz).1
    rwa [cA_cA₀] at this
  have hfin : ∀ z ∈ R, (adjO (G.V (.core i)) (G.V (.core (i + 1))) z).map (infPart D) = 0 := fun z hz =>
    GlobalTheory.T.infinitePart_eq_zero_of_isHalf_idempotentSum _ e he _ (Or.inl (hhalf z hz))
  let c : WO (G.pS (.core i)) (G.pT (.core i)) → ℂ :=
    fun z => W.ψ (-symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) z)
  let f : WO r.sp r'.sp → ℂ :=
    ∑ z ∈ R, c z • heisO W.ψ r.sp r'.sp (adjO (G.V (.core i)) (G.V (.core (i + 1))) z) f₀
  have hexs : ∀ g : WO r.sp r'.sp → ℂ,
      exch (G.V (.core i)) (G.V (.core (i + 1)))
        (∑ z ∈ R, c z • heisO W.ψ r.sp r'.sp (adjO (G.V (.core i)) (G.V (.core (i + 1))) z) g) =
      ∑ z ∈ R, c z • heisO W.ψ (G.pS (.core i)) (G.pT (.core i)) z (exch (G.V (.core i)) (G.V (.core (i + 1))) g) := by
    intro g
    funext x
    have h2 := fun z : WO (G.pS (.core i)) (G.pT (.core i)) =>
      congrFun ((hEx W.ψ (G.V (.core i)) (G.V (.core (i + 1))) hψ).2.1 z g) x
    show (∑ z ∈ R, c z • heisO W.ψ r.sp r'.sp (adjO (G.V (.core i)) (G.V (.core (i + 1))) z) g)
      (adjO (G.V (.core i)) (G.V (.core (i + 1))) x) = _
    rw [Finset.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Pi.smul_apply, Pi.smul_apply, h2 z]
    rfl
  have hf₀th : IsThetaFunO W.ψ r.sp r'.sp f₀ := hf₀.2.theta
  have hcomb := GlobalTheory.T.isThetaFunction_finiteHeisenbergCombination W.ψ W.θ r.sp r'.sp hψ hθ f₀ hf₀th R c _ hfin
  have hex0 : exch (G.V (.core i)) (G.V (.core (i + 1))) f₀ ≠ 0 := by
    intro h0
    apply GlobalTheory.SeeSaw.Inh.vac_ne_zero hf₀
    funext y
    obtain ⟨x, rfl⟩ := (hEx W.ψ _ _ hψ).2.2.2.1.2 y
    exact congrFun h0 x
  have hRne : ∃ z ∈ R, c z ≠ 0 := by
    obtain ⟨y', hy', -⟩ := hR2 0 (fun _ _ => mul_zero _) (fun u _ => by
      have h00 : symplO (G.pS (.core i)) (G.pT (.core i)) u 0 = 0 := by unfold symplO hO; simp
      rw [h00, AddChar.map_zero_eq_one])
    exact ⟨y', hy', addChar_ne_zero _ _⟩
  refine ⟨f, ⟨hcomb.1, ?_, fun τ => GlobalTheory.T.isFockVacuumAt_finiteHeisenbergCombination W.ψ W.θ r.sp r'.sp hψ hθ _ τ f₀ hf₀th (hf₀.2.fock τ) R c _ hfin⟩,
    ?_, fun φ => ?_⟩
  · intro h0
    have h2 : exch (G.V (.core i)) (G.V (.core (i + 1))) f = 0 := by rw [h0]; rfl
    refine GlobalTheory.T.sum_heisenbergTranslates_latticeVacuum_ne_zero W.ψ (G.pS (.core i)) (G.pT (.core i)) (G.latS (.core i)) (G.latT (.core i)) G.pl.W0 e he R hR4
      _ (GlobalTheory.T.adjointExchange_isLatticeVacuum_coreChain D hq T L μ0 hL sc G W M hM hEx hLE i hi r r' hr hr' f₀ hf₀.2.lat) hex0 c hRne ?_
    rw [← hexs f₀]
    exact h2
  · show IsLatVac _ _ _
    refine GlobalTheory.T.isLatticeVacuum_sum_heisenbergTranslates W.ψ r.sp r'.sp _ f₀ (isLatVac_mono (latO_le_true _ _ _ _ _) hf₀.2.lat) R c _ ?_
    intro z hz u hu
    rw [GlobalTheory.T.half_vector_symplectic_orthogonal D hq T L μ0 hL sc G W M hM e he r.sp r'.sp _ _ u hu _ (hhalf z hz), AddChar.map_zero_eq_one]
  · have hpt : ptOf W.ψ W.θ MM MM' f φ = ∑ z ∈ R, c z • heisO W.ψ r.sp r'.sp
        (adjO (G.V (.core i)) (G.V (.core (i + 1))) z) (ptOf W.ψ W.θ MM MM' f₀ φ) :=
      hcomb.2 (cart MM) (onb MM) (cart MM') (onb MM') φ
    have hfl := GlobalTheory.T.isTheta_isLatticeVacuum_fockPureTensor W.ψ W.θ r.sp r'.sp hψ hθ _ _ _ f₀ hf₀th hf₀.2.lat (cart MM) (onb MM) (cart MM') (onb MM') φ
    have hgl := GlobalTheory.T.adjointExchange_isLatticeVacuum_coreChain D hq T L μ0 hL sc G W M hM hEx hLE i hi r r' hr hr' _ hfl.2
    have hth : IsThetaFunO W.ψ r.sp r'.sp (ptOf W.ψ W.θ MM MM' f φ) := by
      rw [hpt]; exact (GlobalTheory.T.isThetaFunction_finiteHeisenbergCombination W.ψ W.θ r.sp r'.sp hψ hθ _ hfl.1 R c _ hfin).1
    have hth' := (((GlobalTheory.T.selfDualLattice_changeOfLattice_laws D).2.2 W.ψ (G.V (.core i)) (G.V (.core (i + 1))) r r').1 _).1 hth
    have hΦth := ((hEx W.ψ (G.V (.core i)) (G.V (.core (i + 1))) hψ).1 _).1 hth'
    have hΦ := hexs (ptOf W.ψ W.θ MM MM' f₀ φ)
    rw [← hpt] at hΦ
    rw [hΦ] at hΦth ⊢
    refine ⟨⟨hΦth, GlobalTheory.T.isLatticeVacuum_sum_heisenbergTranslates W.ψ _ _ _ _ (isLatVac_mono (Λ' := depLat G (.core i)) (fun u hu => hu.1) hgl) R c (fun z => z)
      (fun z hz => (hR1 z hz).2)⟩, ?_⟩
    intro e' he' y hy hyd
    obtain rfl := GlobalTheory.T.idempotentSum_over_finite_places_unique _ _ _ he he'
    exact GlobalTheory.T.cosetSum_heisenberg_isEigenvector W.ψ _ _ (G.latS (.core i)) (G.latT (.core i)) G.pl.W0 e he (depLat G (.core i)) R _ hR1 hR2 hR3 hxi
      _ hgl y hy hyd

end GlobalTheory.CoreOnto

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowInv

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

def mvD (t : T) (j : ℕ) (k : GA D (ch.G.V (.grid D.R.m j))) (Φ : SchDown ch.G t) : SchDown ch.G t := fun i =>
  ch.W.om (.mu t D.R.m i) ((Pi.mulSingle j k : Pts ch.G) i, (Pi.mulSingle j k : Pts ch.G) (i + 1)) (Φ i)

theorem mulSingle_fin {j : ℕ} {k : GA D (ch.G.V (.grid D.R.m j))} (hk : k ∈ GfC _) (i : ℕ) :
    (Pi.mulSingle j k : Pts ch.G) i ∈ GfC _ := by
  rcases eq_or_ne i j with rfl | hi
  · rwa [Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne hi]
    exact one_mem _

theorem om_move (t : T) {j : ℕ} {k : GA D (ch.G.V (.grid D.R.m j))} (hk : k ∈ GfC _) {Φ : SchDown ch.G t}
    (hΦ : ∀ i, IsThetaFunO ch.W.ψ _ _ (Φ i)) (P : PolDown ch.G) (i : ℕ) (hi : i < D.R.m)
    (g : GA D (ch.G.V (.grid D.R.m i))) (g' : GA D (ch.G.V (.grid D.R.m (i + 1)))) :
    ch.W.om (.mu t D.R.m i) (g * (Pi.mulSingle j k : Pts ch.G) i, g' * (Pi.mulSingle j k : Pts ch.G) (i + 1))
        (fockD ch.W t Φ P ⟨i, hi⟩) =
      ch.W.om (.mu t D.R.m i) (g, g') (fockD ch.W t (mvD ch t j k Φ) P ⟨i, hi⟩) := by
  have hom := ch.W.om_is (.mu t D.R.m i) ⟨le_rfl, hi⟩
  have hb := mulSingle_fin ch hk i
  have hb' := mulSingle_fin ch hk (i + 1)
  have key := GlobalTheory.OrientedHeis.om_pureTensorO D ch.W.ψ ch.W.θ (ch.G.pS (.mu t D.R.m i)) (ch.G.pT (.mu t D.R.m i))
    (ch.G.chrS (.mu t D.R.m i)) (ch.G.chrT (.mu t D.R.m i)) (ch.W.om (.mu t D.R.m i)) hom ch.W.θ_is
    (ch.G.cartS ch.W.cart (.mu t D.R.m i)) (ch.G.cartS ch.W.cart (.mu t D.R.m i))
    (ch.G.onS ch.W.onb (.mu t D.R.m i)) (ch.G.onS ch.W.onb (.mu t D.R.m i))
    (ch.G.onT ch.W.cart (.mu t D.R.m i)) (ch.G.onT ch.W.cart (.mu t D.R.m i))
    (ch.G.onT ch.W.onb (.mu t D.R.m i)) (ch.G.onT ch.W.onb (.mu t D.R.m i)) _ _
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb', Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb', Matrix.one_mul]) (Φ ⟨i, hi⟩) (hΦ ⟨i, hi⟩) (P ⟨i, hi⟩)
  have e1 : ((g * (Pi.mulSingle j k : Pts ch.G) i, g' * (Pi.mulSingle j k : Pts ch.G) (i + 1)) :
      GA D (ch.G.V (.grid D.R.m i)) × GA D (ch.G.V (.grid D.R.m (i + 1)))) =
      (g, g') * ((Pi.mulSingle j k : Pts ch.G) i, (Pi.mulSingle j k : Pts ch.G) (i + 1)) := rfl
  rw [e1, map_mul, Module.End.mul_apply]
  exact congrArg (ch.W.om (.mu t D.R.m i) (g, g')) key.2

theorem lastDat_congr {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (Wl : G.Weil) {t : T} {M : Vol G}
    (hM : M.Is t) (j : ℕ) (hj : j + 2 * 0 + 2 = D.R.m) (vN : GlobalTheory.Unf.VolN (besDecAt G j 0 hj)) (g g' : GA D (G.V (.grid D.R.m j)))
    (Φ₁ Φ₁' : WO (G.V (.grid D.R.m j)) (G.V (.grid D.R.m (j + 1))) → ℂ)
    (Φ₂ : WO (G.V (.grid D.R.m (j + 1))) (G.V (.grid D.R.m D.R.m)) → ℂ)
    (e : Wl.om (.mu t D.R.m j) (g, 1) Φ₁ = Wl.om (.mu t D.R.m j) (g', 1) Φ₁') :
    lastDat Wl hM j hj vN g Φ₁ Φ₂ = lastDat Wl hM j hj vN g' Φ₁' Φ₂ := by
  have e' : (lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁ = (lastAt G Wl t hM j hj vN).s.om (g', 1) Φ₁' := e
  unfold lastDat
  rw [e']

theorem down_theta {t : T} {Φ : ch.G.Datum} {τ : SchRow ch.G × SchDown ch.G t →₀ ℂ} (hτ : IsFlipFin t ch.S.B ch.rm Φ τ)
    {d : SchRow ch.G × SchDown ch.G t} (hd : d ∈ τ.support) (j : Fin D.R.m) : IsThetaFunO ch.W.ψ _ _ (d.2 j) := by
  obtain ⟨e, _he, φ, hφ, _⟩ := hτ
  have hv := ch.rm.vT_is t D.R.m j le_rfl j.2
  exact GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt ch.W.ψ_std ch.W.θ_is ((hφ d hd).2 j).2 hv.2.theta

theorem fockD_theta (t : T) {Φ : SchDown ch.G t} (hΦ : ∀ j, IsThetaFunO ch.W.ψ _ _ (Φ j)) (P : PolDown ch.G) (j : Fin D.R.m) :
    IsThetaFunO ch.W.ψ _ _ (fockD ch.W t Φ P j) := by
  have hom := ch.W.om_is (.mu t D.R.m j) ⟨le_rfl, j.2⟩
  have key := GlobalTheory.OrientedHeis.om_pureTensorO D ch.W.ψ ch.W.θ (ch.G.pS (.mu t D.R.m j)) (ch.G.pT (.mu t D.R.m j))
    (ch.G.chrS (.mu t D.R.m j)) (ch.G.chrT (.mu t D.R.m j)) (ch.W.om (.mu t D.R.m j)) hom ch.W.θ_is
    (ch.G.cartS ch.W.cart (.mu t D.R.m j)) (ch.G.cartS ch.W.cart (.mu t D.R.m j))
    (ch.G.onS ch.W.onb (.mu t D.R.m j)) (ch.G.onS ch.W.onb (.mu t D.R.m j))
    (ch.G.onT ch.W.cart (.mu t D.R.m j)) (ch.G.onT ch.W.cart (.mu t D.R.m j))
    (ch.G.onT ch.W.onb (.mu t D.R.m j)) (ch.G.onT ch.W.onb (.mu t D.R.m j)) 1 1
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ (one_mem _), Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ (one_mem _), Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ (one_mem _), Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ (one_mem _), Matrix.one_mul]) (Φ j) (hΦ j) (P j)
  exact key.1

theorem mvD_theta (t : T) {j : ℕ} {k : GA D (ch.G.V (.grid D.R.m j))} {Φ : SchDown ch.G t}
    (hΦ : ∀ i, IsThetaFunO ch.W.ψ _ _ (Φ i)) (i : Fin D.R.m) : IsThetaFunO ch.W.ψ _ _ (mvD ch t j k Φ i) :=
  (ch.W.om_is (.mu t D.R.m i) ⟨le_rfl, i.2⟩).om_pres _ _ (hΦ i)

theorem update_eq_mul (h : Pts ch.G) (j : ℕ) (k : GA D (ch.G.V (.grid D.R.m j))) :
    Function.update h j (h j * k) = h * Pi.mulSingle j k := by
  funext i
  by_cases hi : i = j
  · subst hi
    simp
  · simp [hi]

theorem conAt_move (t : T) {M : Vol ch.G} (hM : M.Is t) {j : ℕ} (hj : j ∈ idx D) {k : GA D (ch.G.V (.grid D.R.m j))}
    (hk : k ∈ GfC _) {Φ : SchDown ch.G t} (hΦ : ∀ i, IsThetaFunO ch.W.ψ _ _ (Φ i)) (P : PolDown ch.G) (h : Pts ch.G) :
    conAt ch.W hM (fockD ch.W t Φ P) (h * Pi.mulSingle j k) = conAt ch.W hM (fockD ch.W t (mvD ch t j k Φ) P) h := by
  have hjm : j ≤ D.R.m - 2 := by
    simp only [idx, List.mem_range'_1] at hj
    omega
  funext j'
  unfold conAt
  by_cases h0 : j' + 2 * 0 + 2 = D.R.m
  · rw [dite_eq_left h0, dite_eq_left h0]
    have hne1 : j' + 1 ≠ j := by omega
    have hne2 : j' + 1 + 1 ≠ j := by omega
    have hmv : mvD ch t j k Φ ⟨j' + 1, by omega⟩ = Φ ⟨j' + 1, by omega⟩ := by
      simp only [mvD, Fin.val_mk, Pi.mulSingle_eq_of_ne hne1, Pi.mulSingle_eq_of_ne hne2, Prod.mk_one_one, map_one,
        Module.End.one_apply]
    have hf : fockD ch.W t (mvD ch t j k Φ) P ⟨j' + 1, by omega⟩ = fockD ch.W t Φ P ⟨j' + 1, by omega⟩ := by
      unfold fockD
      rw [hmv]
    rw [hf]
    refine lastDat_congr ch.W hM j' h0 _ _ _ _ _ _ ?_
    have e := om_move ch t hk hΦ P j' (by omega) (h j') 1
    rw [Pi.mulSingle_eq_of_ne hne1, one_mul] at e
    exact e
  rw [dite_eq_right h0, dite_eq_right h0]
  by_cases h1 : j' + 2 * ((D.R.m - 4 - j') / 2 + 1) + 2 = D.R.m
  · refine dite_congr rfl (fun h1' => ?_) (fun _ => rfl)
    have e1 := om_move ch t hk hΦ P j' (by omega) (h j') (h (j' + 1))
    have e2 := om_move ch t hk hΦ P (j' + 1) (by omega) (h (j' + 1)) (h (j' + 1 + 1))
    simp only [Pi.mul_apply]
    rw [e1, e2]
  · refine dite_congr rfl (fun h1' => absurd h1' h1) (fun _ => rfl)

theorem inv_of (hB : BasicAt ch) (hC : ConLin ch) (hK : KFix ch) (hR : RInv ch) (hT : TensAt ch) : InvAt ch := by
  intro t a τ hτ M hM P y j hj h
  refine ⟨fun r hr => ?_, fun k hk => ?_⟩
  · unfold tot
    refine Finsupp.sum_congr fun d hd => ?_
    rw [hR t M hM _ d.1 (fockD_theta ch t (down_theta ch hτ hd) P.2)
      (fun i => (hB.2.2.2.2.1 t _ τ hτ M hM d hd P.2 h).2 i) P.1 _ _ (hB.1 a) (hB.2.1 t y) j hj r hr h]
  · have hk' : k ∈ GfC _ := (Subgroup.mem_inf.1 hk).1
    have hmv : ∀ d ∈ τ.support, conAt ch.W hM (fockD ch.W t d.2 P.2) (h * Pi.mulSingle j k) =
        conAt ch.W hM (fockD ch.W t (mvD ch t j k d.2) P.2) h := fun d hd =>
      conAt_move ch t hM hj hk' (down_theta ch hτ hd) P.2 h
    rw [update_eq_mul]
    unfold tot
    simp only [Finsupp.sum]
    refine Eq.trans (Finset.sum_congr rfl fun d hd =>
      congrArg (fun C => τ d * per ch.W M t C d.1 P.1 (colFn ch a) (formTop ch t y)) (hmv d hd)) ?_
    let Φs : (SchRow ch.G × SchDown ch.G t) ⊕ (SchRow ch.G × SchDown ch.G t) → SchDown ch.G t :=
      Sum.elim (fun d => mvD ch t j k d.2) (fun d => d.2)
    let fs : (SchRow ch.G × SchDown ch.G t) ⊕ (SchRow ch.G × SchDown ch.G t) → SchRow ch.G := Sum.elim (·.1) (·.1)
    let xs : (SchRow ch.G × SchDown ch.G t) ⊕ (SchRow ch.G × SchDown ch.G t) → ℂ := Sum.elim (fun d => τ d) (fun d => -τ d)
    have hth : ∀ i ∈ τ.support.disjSum τ.support, ∀ n, IsThetaFunO ch.W.ψ _ _ (Φs i n) := by
      rintro (d | d) hd n
      · exact mvD_theta ch t (down_theta ch hτ (Finset.inl_mem_disjSum.1 hd)) n
      · exact down_theta ch hτ (Finset.inr_mem_disjSum.1 hd) n
    have hvan : ∀ (yr : RowPt ch.G) (v : ∀ j : Fin D.R.m, WO (ch.G.V (.grid D.R.m j)) (ch.G.V (.grid D.R.m (j + 1)))),
        ∑ i ∈ τ.support.disjSum τ.support, xs i * ((∏ n, fs i n (yr n)) * ∏ n, Φs i n (v n)) = 0 := by
      intro yr v
      have hk2 := hK t _ τ hτ j hj k hk yr v
      simp only [Finsupp.sum] at hk2
      rw [Finset.sum_disjSum]
      simp only [xs, fs, Φs, Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib]
      rw [← sub_eq_add_neg, sub_eq_zero]
      exact hk2
    have hgood : ∀ i ∈ τ.support.disjSum τ.support, Good ch.W (conAt ch.W hM (fockD ch.W t (Φs i) P.2) h) (fs i) := by
      rintro (d | d) hd
      · have hd' := Finset.inl_mem_disjSum.1 hd
        show Good ch.W (conAt ch.W hM (fockD ch.W t (mvD ch t j k d.2) P.2) h) d.1
        rw [← hmv d hd']
        exact hB.2.2.2.2.1 t _ τ hτ M hM d hd' P.2 _
      · exact hB.2.2.2.2.1 t _ τ hτ M hM d (Finset.inr_mem_disjSum.1 hd) P.2 h
    have key := hT t M (hB.2.2.1 t M hM) _ _ (hB.1 a) (hB.2.1 t y) _ (τ.support.disjSum τ.support) xs
      (fun i => conAt ch.W hM (fockD ch.W t (Φs i) P.2) h) fs hgood (hC t M hM P.2 h _ _ xs fs Φs hth hvan) P.1
    rw [Finset.sum_disjSum] at key
    simp only [xs, fs, Φs, Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib] at key
    rw [← sub_eq_zero, sub_eq_add_neg]
    exact key

theorem main : Big fun ch => InvAt ch :=
  big_mono (fun ch h => inv_of ch h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)
    (Big.and GlobalTheory.T.lastRow_unfolding_basicHypotheses (Big.and GlobalTheory.T.unfoldedProduct_depends_on_dataProduct (Big.and GlobalTheory.T.flippedFiniteTensorLatticeFixed_largeDepth (Big.and GlobalTheory.T.innermostIntegrand_leftPeriodInvariant_largeDepth GlobalTheory.T.definitePeriod_depends_on_productFunction))))

end GlobalTheory.RowInv
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.singleCosetOffTwistPlaces_largeDepth : Big fun ch => OffAt ch := by
  first | exact @GlobalTheory.RowOneCos.offAt_big | exact GlobalTheory.RowOneCos.offAt_big | (intros; apply GlobalTheory.RowOneCos.offAt_big <;> assumption)
end
