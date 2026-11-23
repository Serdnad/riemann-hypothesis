module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle543
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle423
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle537
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle542
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle534
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle515
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle065
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle063
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle064
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaAtEqSumHeisOfFourierSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle589
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelAlgebraicExpansion
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle231
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle594
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle357
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodRightTranslateSobolevSepContinuous
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)
noncomputable section
namespace GlobalTheory.SepRows.SepProof
section
open Classical
end

open Classical in
theorem theta_lifts_separate_of_separating_data : _root_.GlobalTheory.FunPr.ThetaLocalInputs → TopSep := by
  intro _
  unfold TopSep All
  intro D _ T L μ0 _ sc G W M hM S MB F' hF' Ψ hΨ
  have hθ : IsInfFam W.θ := W.θ_is
  set T' : MMap MB := PiTensorProduct.lift.symm F' with hT'
  have hT'm : T' ∈ Mult W.θ MB ∅ 1 := (mem_multT W.θ MB ∅ 1 F').1 hF'
  obtain ⟨Ω, hΩc, hΩ⟩ := GlobalTheory.T.exists_compact_meets_besselTopRationalOrbits W M hM
  have hφ : ∀ ξ, pairVec (coefPlus G W.θ) ξ Ψ ∈ contLeft (G.V (.top 0)) := fun ξ =>
    ⟨GlobalTheory.RowBplus.pairVec_cont G W.θ hθ ξ hΨ, fun γ hγ g => GlobalTheory.RowBplus.pairVec_left G W.θ ξ hΨ hγ g⟩
  have H := fun ξ => GlobalTheory.T.besselPeriodCorankOne_additive_bounded_compact W M hM Ω hΩc hΩ _ (hφ ξ)
  choose C hC using H
  have hadd := fun ξ => (hC ξ).1
  have hadd' := fun ξ => (hC ξ).2.1
  have hbd := fun ξ => (hC ξ).2.2
  have hTt : ∀ u : MB.Vec, F' (PiTensorProduct.tprod ℂ u) = T' u := by
    intro u
    have : F' = PiTensorProduct.lift T' := by rw [hT']; exact (PiTensorProduct.lift.apply_symm_apply F').symm
    rw [this, PiTensorProduct.lift.tprod]
  have hmem : ∀ x : SmT MB, F' x ∈ contLeft (G.V (.grid D.R.m 0)) := by
    intro x
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r u =>
      rw [map_smul, hTt]
      exact (contLeft _).smul_mem r (GlobalTheory.Core.Mi.SepPer.mult_mem_contLeft W.θ MB ∅ 1 hT'm u)
    | add x y hx hy =>
      rw [map_add (f := _)]
      exact (contLeft _).add_mem hx hy
  have pv_add : ∀ ξ ξ', pairVec (coefPlus G W.θ) (ξ + ξ') Ψ = pairVec (coefPlus G W.θ) ξ Ψ + pairVec (coefPlus G W.θ) ξ' Ψ := by
    intro ξ ξ'; funext h; simp [pairVec_apply]
  have pv_smul : ∀ (a : ℂ) ξ, pairVec (coefPlus G W.θ) (a • ξ) Ψ = a • pairVec (coefPlus G W.θ) ξ Ψ := by
    intro a ξ; funext h; simp [pairVec_apply]
  have hBadd : ∀ ξ ξ' F, F ∈ contLeft (G.V (.grid D.R.m 0)) → Bplus W M (pairVec (coefPlus G W.θ) (ξ + ξ') Ψ) F =
      Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ) F + Bplus W M (pairVec (coefPlus G W.θ) ξ' Ψ) F := by
    intro ξ ξ' F hF; rw [pv_add]; exact hadd' ξ _ (hφ ξ') F hF
  have hBsmul : ∀ (a : ℂ) ξ F, Bplus W M (pairVec (coefPlus G W.θ) (a • ξ) Ψ) F = a * Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ) F := by
    intro a ξ F
    rw [pv_smul]; exact Bplus_smul_left W M a _ F
  have hBsmulR : ∀ (a : ℂ) φ F, Bplus W M φ (a • F) = a * Bplus W M φ F := by
    intro a φ F
    exact Bplus_smul_right W M a φ F
  refine ⟨⟨LinearMap.mk₂ ℂ (fun ξ v => Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ) (F' v))
      (fun ξ ξ' v => hBadd ξ ξ' _ (hmem v)) (fun a ξ v => hBsmul a ξ _)
      (fun ξ v v' => (congrArg (Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ)) (F'.map_add v v')).trans (hadd ξ _ (hmem v) _ (hmem v')))
      (fun a ξ v => (congrArg (Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ)) (F'.map_smul a v)).trans (hBsmulR a _ _)), fun ξ v => rfl⟩, ?_⟩
  intro Wt _ _ π e he τ x v
  have hE : ∀ (y y' : Wt τ), e (PiTensorProduct.tprod ℂ (Function.update x τ (y + y'))) =
      e (PiTensorProduct.tprod ℂ (Function.update x τ y)) + e (PiTensorProduct.tprod ℂ (Function.update x τ y')) := by
    intro y y'; rw [MultilinearMap.map_update_add, map_add (f := _)]
  have hEs : ∀ (a : ℂ) (y : Wt τ), e (PiTensorProduct.tprod ℂ (Function.update x τ (a • y))) =
      a • e (PiTensorProduct.tprod ℂ (Function.update x τ y)) := by
    intro a y; rw [MultilinearMap.map_update_smul, map_smul]; simp
  have hV : ∀ (u u' : MB.sm τ), F' (PiTensorProduct.tprod ℂ (Function.update v τ (u + u'))) =
      F' (PiTensorProduct.tprod ℂ (Function.update v τ u)) + F' (PiTensorProduct.tprod ℂ (Function.update v τ u')) := by
    intro u u'; rw [MultilinearMap.map_update_add, map_add (f := _)]
  have hVs : ∀ (a : ℂ) (u : MB.sm τ), F' (PiTensorProduct.tprod ℂ (Function.update v τ (a • u))) =
      a • F' (PiTensorProduct.tprod ℂ (Function.update v τ u)) := by
    intro a u; rw [MultilinearMap.map_update_smul, map_smul]; simp
  have hF1 : ∀ (g : Matrix (Fin (G.V (.grid D.R.m 0)).rank) (Fin (G.V (.grid D.R.m 0)).rank) ℂ),
      g ∈ Formalism.QuantumDeterminants.UH (gramAt D (G.V (.grid D.R.m 0)) τ) → ∀ (x₁ y₁ : MB.sm τ), (y₁ : MB.H τ) = MB.rep τ g x₁ →
      F' (PiTensorProduct.tprod ℂ (Function.update v τ y₁)) =
        rTr _ (atTau W.θ _ τ g) (F' (PiTensorProduct.tprod ℂ (Function.update v τ x₁))) := by
    intro g hg x₁ y₁ hy
    rw [hTt, hTt]
    have := mult_equiv W.θ MB ∅ 1 hT'm τ hg (Function.update v τ x₁) y₁ (by simpa using hy)
    simpa using this
  obtain ⟨Lw, Cu, hL, hb⟩ := GlobalTheory.Core.Mi.SepPer.mult_bound (θ := W.θ) hθ MB (∅ : Set (GA D (G.V (.grid D.R.m 0)))) 1 hT'm Ω hΩc τ v
  refine ⟨LinearMap.mk₂ ℂ (fun y u => Bplus W M (pairVec (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ (Function.update x τ y))) Ψ)
      (F' (PiTensorProduct.tprod ℂ (Function.update v τ u))))
      (fun y y' u => (congrArg (fun ξ => Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ) _) (hE y y')).trans (hBadd _ _ _ (hmem _)))
      (fun a y u => (congrArg (fun ξ => Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ) _) (hEs a y)).trans (hBsmul _ _ _))
      (fun y u u' => (congrArg (Bplus W M _) (hV u u')).trans (hadd _ _ (hmem _) _ (hmem _)))
      (fun a y u => (congrArg (Bplus W M _) (hVs a u)).trans (hBsmulR _ _ _)), ⟨?_, ?_, ?_⟩, fun y u => rfl⟩
  · intro y
    have hℓ0 := fun (u u' : MB.sm τ) =>
      (congrArg (Bplus W M (pairVec (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ (Function.update x τ y))) Ψ)) (hV u u')).trans
        (hadd _ _ (hmem _) _ (hmem _))
    have hℓ1 := fun (a : ℂ) (u : MB.sm τ) =>
      (congrArg (Bplus W M (pairVec (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ (Function.update x τ y))) Ψ)) (hVs a u)).trans
        (hBsmulR a _ _)
    let ℓ₀ : MB.sm τ →ₗ[ℂ] ℂ :=
      { toFun := fun u => Bplus W M (pairVec (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ (Function.update x τ y))) Ψ)
          (F' (PiTensorProduct.tprod ℂ (Function.update v τ u)))
        map_add' := hℓ0
        map_smul' := hℓ1 }
    obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ℓ₀
    have hℓw : ∀ u : MB.sm τ, ℓ u = Bplus W M (pairVec (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ (Function.update x τ y))) Ψ)
        (F' (PiTensorProduct.tprod ℂ (Function.update v τ u))) := fun u => congrArg (fun m => m u) hℓ
    refine ⟨ℓ, ⟨Lw, C (e (PiTensorProduct.tprod ℂ (Function.update x τ y))) * Cu, hL, fun w hw => ?_⟩, fun u => hℓw u⟩
    have hw' : w ∈ MB.sm τ := Submodule.subset_span hw
    have e1 : ℓ w = ℓ ((⟨w, hw'⟩ : MB.sm τ) : MB.H τ) := rfl
    rw [e1, hℓw]
    have := hbd (e (PiTensorProduct.tprod ℂ (Function.update x τ y))) _ (hmem _) _
      (fun z hz => by rw [hTt]; exact hb ⟨w, hw'⟩ z hz)
    calc _ ≤ _ := this
      _ = _ := by ring
  · intro h hh g hg hEm w x₁ y₁ hy
    have he1 := he τ h hh (Function.update x τ w) (Function.update x τ (π τ h w)) (by simp) (fun τ' hτ' => by simp [hτ'])
    have hp := pairVec_comp_rho (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ (Function.update x τ w))) Ψ
      (atTau_mem_GinfC' W.θ _ τ h)
    have hemb : atTau W.θ (G.V (.grid D.R.m 0)) τ g = embTop G (atTau W.θ (G.V (.top 0)) τ h) :=
      (embRel_iff _ _ _).1 (GlobalTheory.T.embRel_atRealPlace_of_unitaryEmbedding D W.θ hθ _ _ _ τ h g hh hg hEm)
    show Bplus W M (pairVec (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ (Function.update x τ (π τ h w)))) Ψ)
      (F' (PiTensorProduct.tprod ℂ (Function.update v τ y₁))) =
      Bplus W M (pairVec (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ (Function.update x τ w))) Ψ)
      (F' (PiTensorProduct.tprod ℂ (Function.update v τ x₁)))
    rw [he1, hp, hF1 g hg x₁ y₁ hy, hemb]
    exact GlobalTheory.T.besselPeriodCorankOne_simultaneous_rightTranslate W M hM _ (hφ _) _ (hmem _) _
  · intro u hu w x₁ y₁ hy
    show Bplus W M _ (F' (PiTensorProduct.tprod ℂ (Function.update v τ y₁))) = _ * Bplus W M _ (F' (PiTensorProduct.tprod ℂ (Function.update v τ x₁)))
    rw [hF1 u hu.1 x₁ y₁ hy]
    exact GlobalTheory.T.besselPeriodCorankOne_rightTranslate_unipotent W M hM _ _ (hmem _) _ (GlobalTheory.T.atRealPlace_mem_unipotentFlag_adelic D W.θ hθ _ G.besTop.e τ u hu)
end GlobalTheory.SepRows.SepProof
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.theta_lifts_separate_points : _root_.GlobalTheory.FunPr.ThetaLocalInputs → TopSep := by
  first | exact @_root_.GlobalTheory.SepRows.SepProof.theta_lifts_separate_of_separating_data | exact _root_.GlobalTheory.SepRows.SepProof.theta_lifts_separate_of_separating_data | (intros; apply _root_.GlobalTheory.SepRows.SepProof.theta_lifts_separate_of_separating_data <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
namespace GlobalTheory.AlgWave
open GlobalTheory.PlaceModel
variable {G : Type} [AddCommGroup G]
variable {χ : G → G → ℂ} {X Y L L' : AddSubgroup G}
end GlobalTheory.AlgWave
namespace GlobalTheory.AlgWave
open GlobalTheory.PlaceModel
variable {G : Type} [AddCommGroup G] {χ : G → G → ℂ} {X Y L L' : AddSubgroup G}
end GlobalTheory.AlgWave
namespace GlobalTheory.BotFourier
open GlobalTheory.PlaceModel GlobalTheory.AlgWave GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle
variable {D : D7}
end GlobalTheory.BotFourier
namespace GlobalTheory.BotFourier
open GlobalTheory.PlaceModel GlobalTheory.AlgWave

theorem finite_datum_eq_sum_heisenberg : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc}
    {W : G.Weil} {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) →
    L.Is μ₀ → IsBottomTri W i j X →
    ∀ t : T, ∃ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → WO (GlobalTheory.Grid.neg A) WW), (∀ p, IsAlgebraic ℚ (c p)) ∧
      (∀ p, (w p).map (infPart D) = 0) ∧ X.f t = ∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ _ hX t
  classical
  have hI := hX.is
  have hψ : IsStdChar D W.ψ (-1) := hI.isVac.1
  have hν := (hI.weil' t).hecT
  have hSd : IsSelfDualC (GlobalTheory.Grid.neg A) X.rA.Λ := by
    refine ⟨hI.rigA.1.1, fun y => (hI.rigA.1.2 y).trans (forall₂_congr fun x _ => ⟨fun ⟨c, hc⟩ => ⟨-c, ?_⟩,
      fun ⟨c, hc⟩ => ⟨-c, ?_⟩⟩)⟩
    · simp [GlobalTheory.Grid.neg_gram, hc]
    · simp [GlobalTheory.Grid.neg_gram] at hc ⊢
      exact neg_eq_iff_eq_neg.2 hc
  have hWd : IsSelfDualC WW X.rW.Λ := hI.rigW.1
  have he := hI.idem t
  have hee := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  have hinf' := GlobalTheory.PlaceDatum.infPart_cA hinf
  set S := GlobalTheory.Grid.neg A with hSdef
  set e := X.e t with hedef
  set Λ : AddSubgroup (WO S WW) := latO S WW X.rA.Λ X.rW.Λ fun _ => True with hΛ
  obtain ⟨K, hK, hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO (S := S)
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hSd)
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hWd) X.rA.β X.rW.β
  have hSB := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.stdFst_isSB hν.1 he (GlobalTheory.ConstRatio.ideal_ne_bot X (locPl G) t) A WW X.rA.β X.rW.β Λ
    (GlobalTheory.PlaceDatum.exists_den_frMapO (S := S) hSd.1.fg hWd.1.fg X.rA.β X.rW.β)
    ⟨K, hK, fun t ht => hC t (GlobalTheory.PlaceDatum.infPart_of_half hinf ht)⟩
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hI.fst t
  rw [hall Tm hTm]
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D W.ψ S WW X.rA.Λ X.rW.Λ hψ hSd hWd).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S WW _ _ hSd.1.fg hWd.1.fg fun _ => True
  have he' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, hee]
  have hsm : ∀ a : AE D, a * a = a → ∀ u ∈ Λ, a • u ∈ Λ ⊓ half S WW a := fun a ha u hu =>
    AddSubgroup.mem_inf.2 ⟨GlobalTheory.LatticeStable.smul_mem_latO D S WW _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu, by rw [mem_half, smul_smul, ha]⟩
  have finX : ∀ x ∈ half S WW e, x.map (infPart D) = 0 := fun x hx =>
    GlobalTheory.PlaceDatum.infPart_of_half hinf ((isHalf_iff S WW).2 hx)
  have finY : ∀ y ∈ half S WW (cA D e), y.map (infPart D) = 0 := fun y hy =>
    GlobalTheory.PlaceDatum.infPart_of_half hinf' ((isHalf_iff S WW).2 hy)
  have tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S WW => k • t := fun k hk a b hab => by
    rw [← inv_smul_nsmul S WW hk a, ← inv_smul_nsmul S WW hk b]
    exact congrArg _ hab
  have hb := isBichar_symplO S WW W.ψ
  obtain ⟨h1, k, hk, h2, h3⟩ := hSB
  have hmem := mem_algSpan (χ := fun x y : WO S WW => W.ψ (symplO S WW x y)) (X := half S WW e)
    (Y := half S WW (cA D e)) (L := Λ ⊓ half S WW e) (L' := Λ ⊓ half S WW (cA D e)) hb
    (fun x hx y hy => psi_mem hψ hSd hWd (finX x hx) (finY y hy)) inf_le_right inf_le_right
    (fun u hu y hy => (hdual u (finX u hu.2)).1 hu.1 y hy.1)
    (fun x hx h => ⟨(hdual x (finX x hx)).2 fun u hu => by
      have := h _ (hsm _ he' u hu)
      rwa [← symplO_smul, (mem_half S WW).1 hx] at this, hx⟩)
    (half_div S WW e) (half_div S WW _) tf
    (fun k hk => by
      obtain ⟨R, hR, h⟩ := hfin k hk
      refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
      obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
      refine ⟨_, ⟨r, hr, rfl⟩, e • u, hsm e hee u hu, ?_⟩
      have := (mem_half S WW).1 ht.2
      rw [← this, htr, smul_add, smul_comm e k u])
    _ (fun x => stdFst_mem hν.1 he _ A WW X.rA.β X.rW.β x) (fun t ht => (isHalf_iff S WW).1 (h1 t ht)) k hk
    (fun u hu => h2 u hu.1 ((isHalf_iff S WW).2 hu.2))
    (fun t ht => ⟨h3 t ht, (half S WW e).nsmul_mem ((isHalf_iff S WW).1 (h1 t ht)) _⟩)
  set V : Submodule Qb (WO S WW → ℂ) := Submodule.span Qb
    {F | ∃ w : WO S WW, w.map (infPart D) = 0 ∧ F = heisO W.ψ S WW w X.vac} with hV
  have hvac : Tm (halfInd e Λ) = X.vac := by simpa using hTm.vac
  have s0 := GlobalTheory.isSBHalf_halfInd e Λ
  have hT : ∀ Ψ ∈ algSpan (fun x y : WO S WW => W.ψ (symplO S WW x y)) (half S WW e) (half S WW (cA D e))
      (Λ ⊓ half S WW e), Tm Ψ ∈ V := by
    intro Ψ hΨ
    induction hΨ using Submodule.span_induction with
    | mem _ hh =>
      obtain ⟨x, hx, y, hy, rfl⟩ := hh
      have s1 : IsSBHalf e Λ fun t => W.ψ (symplO S WW t y) * halfInd e Λ t := by
        obtain ⟨k, hk, hk'⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO' (S := S) (T := WW)
          (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hSd)
          (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hWd) y (finY y hy)
        obtain ⟨a1, k', hk1, a2, a3⟩ := s0
        refine ⟨fun t ht => a1 t (right_ne_zero_of_mul ht), k * k', Nat.mul_pos hk hk1, fun u hu hh t => ?_,
          fun t ht => ?_⟩
        · have e1 : halfInd e Λ (t + (k * k') • u) = halfInd e Λ t := by
            rw [mul_nsmul]
            exact a2 _ (nsmul_mem hu k) ((isHalf_iff S WW).2 (nsmul_mem ((isHalf_iff S WW).1 hh) k)) t
          have e2 : W.ψ (symplO S WW ((k * k') • u) y) = 1 := by
            rw [mul_nsmul']
            refine (hb.nsmul k _ y).trans ((hdual _ (finX _ (nsmul_mem ((isHalf_iff S WW).1 hh) k'))).1
              (nsmul_mem hu k') _ hk')
          simp only [e1, symplO_add_left, AddChar.map_add_eq_mul, e2, mul_one]
        · rw [mul_nsmul']
          exact nsmul_mem (a3 t (right_ne_zero_of_mul ht)) k
      have e1 : wave (fun x y : WO S WW => W.ψ (symplO S WW x y)) (Λ ⊓ half S WW e) x y =
          fun t => (fun t => W.ψ (symplO S WW t y) * halfInd e Λ t) (t + x) := by
        rw [halfInd_eq_ind]; rfl
      rw [e1, hTm.trans _ s1 x ((isHalf_iff S WW).2 hx), hTm.modul _ s0 y ((isHalf_iff S WW).2 hy), hvac]
      have e2 : heisO W.ψ S WW x (heisO W.ψ S WW y X.vac) =
          W.ψ (symplOH S WW x y) • heisO W.ψ S WW (x + y) X.vac := heisL_heisL S WW W.ψ x y X.vac
      rw [e2]
      refine smul_mem_of_mem (psiH_mem hψ hSd hWd (finX x hx) (finY y hy)) (Submodule.subset_span ⟨x + y, ?_, rfl⟩)
      refine Matrix.ext fun a b => ?_
      have q1 : infPart D (x a b) = 0 := congrFun (congrFun (finX x hx) a) b
      have q2 : infPart D (y a b) = 0 := congrFun (congrFun (finY y hy) a) b
      change infPart D (x a b + y a b) = 0
      rw [RingHom.map_add (f := _), q1, q2, add_zero]
    | zero => rw [map_zero]; exact zero_mem _
    | add f g _ _ hf hg => rw [map_add]; exact add_mem hf hg
    | smul c f _ hf =>
      change Tm ((c : ℂ) • f) ∈ V
      rw [map_smul]
      exact V.smul_mem c hf
  obtain ⟨n, f, g, hfg⟩ := (Submodule.mem_span_set').1 (hT _ hmem)
  choose w hw hgw using fun p => (g p).2
  refine ⟨n, fun p => (f p : ℂ), w, fun p => mem_algebraicClosure_iff.1 (f p).2, hw, ?_⟩
  rw [← hfg]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← hgw p]
  rfl
end GlobalTheory.BotFourier
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.bottom_fourier_coeff_heisenberg_expansion : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∀ t : T, ∃ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → WO (GlobalTheory.Grid.neg A) WW), (∀ p, IsAlgebraic ℚ (c p)) ∧
      (∀ p, (w p).map (infPart D) = 0) ∧ X.f t = ∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac := by
  first | exact @_root_.GlobalTheory.BotFourier.finite_datum_eq_sum_heisenberg | exact _root_.GlobalTheory.BotFourier.finite_datum_eq_sum_heisenberg | (intros; apply _root_.GlobalTheory.BotFourier.finite_datum_eq_sum_heisenberg <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
open scoped ComplexOrder
namespace GlobalTheory.BottomDeg
open GlobalTheory.Grid (neg sgn ofSgn)
variable {D : D7}
theorem bottomClassSum_eq_zero_off_finite : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ K : Finset (FVar D WW.rank A.rank →₀ ℕ), ∀ t, ∀ h ∈ GfC WW, ∀ k ∉ K,
      X.I W.ψ W.θ t (MvPolynomial.monomial k 1) h = 0 := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ _ hX
  classical
  let Good : T → Set (FVar D WW.rank A.rank →₀ ℕ) := fun t =>
    {k | ∃ h ∈ GfC WW, X.I W.ψ W.θ t (MvPolynomial.monomial k 1) h ≠ 0}
  have one_of : ∀ {c I : ℂ}, I = c * I → I ≠ 0 → c = 1 := fun {c I} e hI => by
    have h0 : (c - 1) * I = 0 := by rw [sub_mul, one_mul, ← e, sub_self]
    exact sub_eq_zero.1 ((mul_eq_zero.1 h0).resolve_right hI)
  have hfin : ∀ t, (Good t).Finite := by
    intro t
    by_cases hne : (Good t).Nonempty
    · obtain ⟨k₀, h₀, -, hk₀⟩ := hne
      refine (GlobalTheory.finite_monomials_of_placeDegree D WW.rank A.rank
        (fun τ => ∑ v ∈ k₀.support with v.1 = τ, k₀ v)).subset fun k hk τ => ?_
      obtain ⟨h, -, hk⟩ := hk
      obtain ⟨C, w, hw, hI⟩ := scalar_exists hX t τ
      have e1 := one_of (hI k h) hk
      have e0 := one_of (hI k₀ h₀) hk₀
      have hC : C ≠ 0 := fun h0 => by rw [h0, zero_mul] at e1; exact zero_ne_one e1
      exact GlobalTheory.ExpPow.pow_exp_I_or_inv_injective _ _ w hw (mul_left_cancel₀ hC (e1.trans e0.symm))
    · rw [Set.not_nonempty_iff_eq_empty.1 hne]
      exact Set.finite_empty
  have hU : (⋃ t, Good t).Finite := Set.finite_iUnion hfin
  refine ⟨hU.toFinset, fun t h hh k hk => ?_⟩
  by_contra hne
  exact hk (hU.mem_toFinset.2 (Set.mem_iUnion.2 ⟨t, h, hh, hne⟩))
end GlobalTheory.BottomDeg
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.bottomClassSum_finite_support : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ K : Finset (FVar D WW.rank A.rank →₀ ℕ), ∀ t, ∀ h ∈ GfC WW, ∀ k ∉ K,
      X.I W.ψ W.θ t (MvPolynomial.monomial k 1) h = 0 := by
  first | exact @_root_.GlobalTheory.BottomDeg.bottomClassSum_eq_zero_off_finite | exact _root_.GlobalTheory.BottomDeg.bottomClassSum_eq_zero_off_finite | (intros; apply _root_.GlobalTheory.BottomDeg.bottomClassSum_eq_zero_off_finite <;> assumption)
end
end

section

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SignedHC
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SepRows
theorem separating_family_has_models : _root_.GlobalTheory.FunPr.ThetaLocalInputs → CoreModels := fun h => coreModels_of_upq h.discreteSeriesUpqExists
end GlobalTheory.SepRows
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_separating_models : _root_.GlobalTheory.FunPr.ThetaLocalInputs → CoreModels := by
  first | exact @_root_.GlobalTheory.SepRows.separating_family_has_models | exact _root_.GlobalTheory.SepRows.separating_family_has_models | (intros; apply _root_.GlobalTheory.SepRows.separating_family_has_models <;> assumption)
end
end
