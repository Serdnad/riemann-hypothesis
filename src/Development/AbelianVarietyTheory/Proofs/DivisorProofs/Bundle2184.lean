module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle065
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2151
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanePairRestrictionFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1294
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2148
import Formalism.LocalToGlobal.IndefiniteReal.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1347
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2136
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2150
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle584
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1588
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle369
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1529
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1368
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1720
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle032

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

theorem _root_.GlobalTheory.T.heckePolynomials_of_carried_eigensystem : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ p, ∀ w ∈ R.EEp3 p, LinearMap.adjoint (R.Th A3.A.μ0) w = 0 → w = 0) → ∀ p c, R.Carries p c → ∀ P ∈ A3.A.ok A3.A.μ0, RealDat.polE (A := A3.A) p.1.1 P = Formalism.L2.Col.heckePolyOf D.R.r (A3.A.q P) (fun k => c (R.pl P) (dualLab (splitLab D.R.r k))) ∧ RealDat.polW (A := A3.A) p.1.1 P = Formalism.L2.Col.heckePolyOf D.R.r (A3.A.q P) (fun k => c (R.pl P) (splitLab D.R.r k)) := by
  first | exact @GlobalTheory.CarriedHecke.hecke_polys_of_carries | exact GlobalTheory.CarriedHecke.hecke_polys_of_carries | (intros; apply GlobalTheory.CarriedHecke.hecke_polys_of_carries <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolRoot

def Root {S T : Scheme.{0}} (A : Over S) [GrpObj A] (P : LB (G2 A).left) (t : T ⟶ S) : Prop :=
  ∃ (B : Over T) (_ : GrpObj B) (_ : IsCommMonObj B) (β : B.left ⟶ A.left) (β₂ : (G2 B).left ⟶ (G2 A).left),
    IsGrpPullback B A t β ∧ IsSquare β β₂ ∧ ∃ L : LB B.left, L.IsLB ∧ LBIso (abelian₂ B L) (P.pull β₂)

theorem Root.comp {S T T' : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A) {P : LB (G2 A).left}
    {t : T ⟶ S} (h : Root A P t) (σ : T' ⟶ T) : Root A P (σ ≫ t) := by
  obtain ⟨A', _, _, β, β₂, hβ, hsq, L, hL, H⟩ := h
  obtain ⟨B', _, φ, hφ⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A' σ
  haveI : IsCommMonObj B' := by
    rw [isCommMonObj_iff_isMulCommutative]
    intro T
    refine ⟨⟨fun x y => Over.OverMorphism.ext (hφ.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
    rw [← hφ.2 T x y (pushPt hφ.1.w x) (pushPt hφ.1.w y) rfl rfl,
      ← hφ.2 T y x (pushPt hφ.1.w y) (pushPt hφ.1.w x) rfl rfl, _root_.mul_comm]
  let V := lift (pushPt hφ.1.w (fst B' B')) (pushPt hφ.1.w (snd B' B'))
  have hV : IsSquare φ V.left := GlobalTheory.LamPull.exists_isSquare hφ.1.w
  refine ⟨B', inferInstance, inferInstance, φ ≫ β, V.left ≫ β₂, hφ.comp hβ,
    GlobalTheory.ZM.SiegPull.isSquare_comp hV hsq, L.pull φ, pull_isLB hL φ, ?_⟩
  refine LBIso.chartPull
    (chartPullLinComb L φ _ _ _ V.left fun I => psum_push hφ _ _ V (fun i => ?_) I.down)
    (chartPullSame P (fun _ : PUnit => V.left ≫ β₂) (fun _ => β₂) (fun _ => 1) V.left fun _ => rfl) H
  fin_cases i <;> simp [V, x2]

def tri {X Y T : Scheme.{0}} (f : X ⟶ Y) (a b c : T ⟶ X) (h₁ : a ≫ f = b ≫ f) (h₂ : b ≫ f = c ≫ f) :
    T ⟶ GlobalTheory.LBDescent.Triple f :=
  pullback.lift (pullback.lift a b h₁) (pullback.lift b c h₂) (by rw [pullback.lift_snd, pullback.lift_fst])

def TriCocycle {X Y : Scheme.{0}} (f : X ⟶ Y) (D : Γ(GlobalTheory.LBDescent.Triple f, ⊤)ˣ) : Prop :=
  ∀ (T : Scheme.{0}) (a b c d : T ⟶ X) (h₁ : a ≫ f = b ≫ f) (h₂ : b ≫ f = c ≫ f) (h₃ : c ≫ f = d ≫ f),
    GlobalTheory.CharKer.pullTop (tri f a b c h₁ h₂) D * GlobalTheory.CharKer.pullTop (tri f a c d (h₁.trans h₂) h₃) D =
      GlobalTheory.CharKer.pullTop (tri f b c d h₂ h₃) D * GlobalTheory.CharKer.pullTop (tri f a b d h₁ (h₂.trans h₃)) D

def KillsSq {X Y : Scheme.{0}} (f : X ⟶ Y) (D : Γ(GlobalTheory.LBDescent.Triple f, ⊤)ˣ) (u : Γ(pullback f f, ⊤)ˣ) : Prop :=
  D ^ 2 * GlobalTheory.CharKer.pullTop (pullback.fst (pullback.snd f f) (pullback.fst f f)) u *
      GlobalTheory.CharKer.pullTop (pullback.snd (pullback.snd f f) (pullback.fst f f)) u =
    GlobalTheory.CharKer.pullTop (GlobalTheory.LBDescent.pr13 f) u

end GlobalTheory.PolRoot
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.heisenbergIntertwiner_eq_twisted_weilOperator : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' →
    ∀ (K : GL (Fin a') (Fv F Bs.v₁) →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.V'.J),
    (∀ g, K g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.V' (evFin F Bs.v₁) ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = g.val ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp σ)) =
        (Γ.V'.J.map Bs.τ₁)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * Γ.V'.J.map Bs.τ₁) →
    ∀ (S : GL (Fin a') (Fv F Bs.v₁) → ((Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ) → (Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _, ∀ c : ℂ, S g (c • φ + φ') = c • S g φ + S g φ') →
    (∀ g g', ∀ φ ∈ GlobalTheory.WeilM.SB _, S (g * g') φ = S g (S g' φ)) →
    (∀ φ ∈ GlobalTheory.WeilM.SB _, S 1 φ = φ) →
    (∀ g (γ : Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F Bs.v₁) γ →
      ∀ φ ∈ GlobalTheory.WeilM.SB _,
        S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ) =
          GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁)
            (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (K g, (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.W.J)) γ)) (S g φ)) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ μ : @Measure (Fin a' × Fin (a + a') → Fv F Bs.v₁) (borel _),
      @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∃ ν α : (Fv F Bs.v₁)ˣ →* ℂˣ, (∀ x, ‖(ν x : ℂ)‖ = 1) ∧
      ∀ ι, Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι → ∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g φ) = omB ν α g 1 (ι φ) := by
  first | exact @GlobalTheory.LinModelLocal.exists_omB_of_linBar | exact GlobalTheory.LinModelLocal.exists_omB_of_linBar | (intros; apply GlobalTheory.LinModelLocal.exists_omB_of_linBar <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

noncomputable section

namespace GlobalTheory.DblEval

theorem lintegral_partL_eq : ∀ {F : Type} [Field F] [NumberField F] {κ κ' : Type} [Fintype κ] [Fintype κ']
    (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)),
    (∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ C : ℝ≥0∞, ∀ φ ∈ schA F κ, ∫⁻ x, ‖T φ x‖ₑ ^ 2 ∂μ = C * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    (∀ Φ ∈ schA F (κ ⊕ κ'), partL T Φ ∈ schA F (κ ⊕ κ')) →
    ∀ μ : @Measure (κ ⊕ κ' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ C : ℝ≥0∞, ∀ Φ ∈ schA F (κ ⊕ κ'), ∫⁻ x, ‖partL T Φ x‖ₑ ^ 2 ∂μ = C * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  intro F _ _ κ κ' _ _ T hT hmem μ hμ
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  letI mX : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  letI mY : MeasurableSpace (κ' → AF F) := borel _
  haveI : BorelSpace (κ' → AF F) := ⟨rfl⟩
  letI mZ : MeasurableSpace (κ ⊕ κ' → AF F) := borel _
  haveI : BorelSpace (κ ⊕ κ' → AF F) := ⟨rfl⟩
  let μ₁ : Measure (κ → AF F) := Measure.addHaar
  let μ₂ : Measure (κ' → AF F) := Measure.addHaar
  obtain ⟨C₁, hC₁⟩ := hT μ₁ inferInstance
  refine ⟨C₁, fun Φ hΦ => ?_⟩
  let e : (κ ⊕ κ' → AF F) ≃ₜ (κ → AF F) × (κ' → AF F) := Homeomorph.sumArrowHomeomorphProdArrow
  let eA : ((κ → AF F) × (κ' → AF F)) ≃ₜ+ (κ ⊕ κ' → AF F) :=
    { e.symm with map_add' := fun a b => by funext i; cases i <;> rfl }
  let ν : Measure (κ ⊕ κ' → AF F) := (μ₁.prod μ₂).map eA
  haveI : ν.IsAddHaarMeasure := eA.isAddHaarMeasure_map _
  obtain ⟨c, hμν⟩ : ∃ c : ℝ≥0, μ = c • ν := ⟨_, Measure.isAddLeftInvariant_eq_smul μ ν⟩
  have key : ∀ f : (κ ⊕ κ' → AF F) → ℝ≥0∞, Measurable f →
      ∫⁻ z, f z ∂μ = c * ∫⁻ y, ∫⁻ x, f (Sum.elim x y) ∂μ₁ ∂μ₂ := by
    intro f hf
    have hmeas : Measurable (⇑eA) := eA.continuous.measurable
    rw [hμν, lintegral_smul_measure]
    simp only [ν]
    rw [lintegral_map hf hmeas, lintegral_prod_symm (fun p => f (eA p)) (hf.comp hmeas).aemeasurable]
    rfl
  have hc1 := GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F (hmem Φ hΦ)
  have hc2 := GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hΦ
  rw [key _ (hc1.measurable.enorm.pow_const 2), key _ (hc2.measurable.enorm.pow_const 2)]
  have inner : ∀ y, ∫⁻ x, ‖partL T Φ (Sum.elim x y)‖ₑ ^ 2 ∂μ₁ = C₁ * ∫⁻ x, ‖Φ (Sum.elim x y)‖ₑ ^ 2 ∂μ₁ :=
    fun y => hC₁ _ (sliceL_mem hΦ y)
  have hm : Measurable fun y => ∫⁻ x, ‖Φ (Sum.elim x y)‖ₑ ^ 2 ∂μ₁ :=
    Measurable.lintegral_prod_left' (f := fun p : (κ → AF F) × (κ' → AF F) => ‖Φ (eA p)‖ₑ ^ 2)
      ((hc2.comp eA.continuous).measurable.enorm.pow_const 2)
  simp_rw [inner]
  rw [lintegral_const_mul _ hm]
  ring

end GlobalTheory.DblEval

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertDblGen

theorem inlD_mem_closure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, GlobalTheory.InertDbl.inlD σ G.W k ∈ Subgroup.closure (GlobalTheory.InertDbl.ParD σ G.W v ∪ GlobalTheory.InertDbl.NabD σ G.W v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hv k hk
  obtain ⟨k₁, hk₁, k₂, hk₂, h₁, h₂, rfl⟩ := GlobalTheory.T.inertPlace_stabilizer_two_factor_decomposition F E σ B a a' G X om om' hT v w hv k hk
  rw [map_mul]
  obtain ⟨n₁, hn₁, p₁, hp₁, e₁⟩ := GlobalTheory.T.unitaryToDoubledFirstFactor_bigCell_inertPlace F E σ B a a' G X om om' hT v w hv k₁ hk₁ h₁
  obtain ⟨n₂, hn₂, p₂, hp₂, e₂⟩ := GlobalTheory.T.unitaryToDoubledFirstFactor_bigCell_inertPlace F E σ B a a' G X om om' hT v w hv k₂ hk₂ h₂
  rw [e₁, e₂]
  have s : ∀ x, x ∈ GlobalTheory.InertDbl.ParD σ G.W v ∪ GlobalTheory.InertDbl.NabD σ G.W v →
      x ∈ Subgroup.closure (GlobalTheory.InertDbl.ParD σ G.W v ∪ GlobalTheory.InertDbl.NabD σ G.W v) :=
    fun x hx => Subgroup.subset_closure hx
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (s _ (Or.inr hn₁)) (s _ (Or.inl hp₁)))
    (Subgroup.mul_mem _ (s _ (Or.inr hn₂)) (s _ (Or.inl hp₂)))

end GlobalTheory.InertDblGen
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

theorem GlobalTheory.InertBridgeLine.locVac_line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L)
      (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L) (ψL : AddChar L ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') L →+ Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT →
    ∀ ρ : Matrix (Fin (a + a')) (Fin a') L → Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v)),
      (∀ x (m : SB (Fin a' × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M'.co.rho B.ψ (κ x))
        (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) ((ρ x m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ)) →
    ∀ s m : SB (Fin a' × Fin (a + a') → Fv F v), (s : (Fin a' × Fin (a + a') → Fv F v) → ℂ) = G.M'.vac v →
      GlobalTheory.Hk3.LocVac ρ m → ∃ c : ℂ, m = c • s := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hin hvT L _ _ ϖ σL q δ JS JT ψL κ ιS ιT hC ρ hρ s m hs hm
  obtain ⟨unr, odd, intS, intT, hermS, hermT, hδ, psiInt, psiNe, hAt, hSurj, hLat, hPsi, hEq, hιS, hιT, hKS, hKT⟩ := hC
  obtain ⟨-, -, θ, hθ, hvac⟩ := hTr.geo.hM'.vac v
  have h2 : evFin F v (⅟(2 : AF F)) ∈ v.adicCompletionIntegers F := by
    have h2e : evFin F v (⅟(2 : AF F)) = algebraMap F (Fv F v) (2 : F)⁻¹ := by
      show evFin F v (algebraMap F (AF F) 2⁻¹) = _
      exact AlgHom.commutes _ _
    rw [h2e]
    exact GlobalTheory.LatVac.half_mem_adicCompletionIntegers F v (hTr.base.inert v w hin).1
  have hone : ∀ γ ∈ latAtV G.V' G.W v, B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E))
      ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) = 1 := fun γ hγ =>
    GlobalTheory.LatVacArith.psi_symp_latAtV σ B G.V' G.W _ _ _ _ hTr.base hTr.geo.hV' hTr.geo.hW v θ _ h2 γ hγ γ hγ
  have hm' : ∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ)
      (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) •
        (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ)) := by
    intro γ hγ
    rw [hone γ hγ, one_smul]
    obtain ⟨x, rfl⟩ := hSurj γ ((GlobalTheory.LatVac.latAtV_at_stable G.V' G.W v).1 γ hγ)
    have hx := (hLat x).2 hγ
    have h := hρ x m
    rwa [hm x hx] at h
  obtain ⟨c, hc⟩ := GlobalTheory.T.inertPlace_schwartzBruhat_vacuumCondition_eq_smul F E σ B a a' G X om om' hTr v w hin θ hθ hvac m m.2 hm'
  refine ⟨c, Subtype.ext ?_⟩
  rw [Submodule.coe_smul, hs]
  exact hc

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertTransv

theorem exists_unip_corner_isUnit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n r s : ℕ) (X : Spc F E n), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ g ∈ GlobalTheory.DblVac.KD σ X v,
    ∃ u ∈ GlobalTheory.DblVac.KD σ X v, u ∈ GlobalTheory.DblVac.PDiag σ X ∧
      IsUnit ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD (g * u) * GlobalTheory.DblVac.antiCols n).det ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt X v,
        ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD (g * u) * GlobalTheory.DblVac.antiCols n)⁻¹ *ᵥ z ∈
          GlobalTheory.InertSph.latAt X v := by
  intro F E _ _ _ _ _ σ B n r s X hB hX v w hvw g hg
  obtain ⟨Z, hZs, hZl, hZn, hdet, hinv⟩ := GlobalTheory.T.exists_inertPlace_transversal_of_localCore GlobalTheory.T.exists_isotropic_graph_unitary_isUnit_lowerBlock F E σ B n r s X hB hX v w hvw g hg
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := (hB.inert v w hvw).1
  obtain ⟨u, huK, huP, hu⟩ := GlobalTheory.T.halfSkewUnipotent_mem_doubledLatticeStabilizer F E σ n X v h2 Z hZs hZl hZn
  set N : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E) := GlobalTheory.DblVac.antiCols (F := F) (E := E) n with hN
  set Δ : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E) := diagCols (Fin n) with hΔ
  have hNN : Nᵀ * N = (2 : AF F) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    rw [hN, GlobalTheory.DblVac.antiCols, Matrix.transpose_fromRows, Matrix.transpose_one, Matrix.transpose_neg,
      Matrix.transpose_one, Matrix.fromCols_mul_fromRows]
    simp [two_smul]
  have hmul : GlobalTheory.DblVac.matD (g * u) = GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.matD u := rfl
  have key : Nᵀ * GlobalTheory.DblVac.matD (g * u) * N = Nᵀ * GlobalTheory.DblVac.matD g * N + Nᵀ * GlobalTheory.DblVac.matD g * Δ * Z := by
    rw [hmul, hu]
    have : Nᵀ * (GlobalTheory.DblVac.matD g * (1 + (⅟(2 : AF F)) • (Δ * Z * Nᵀ))) * N =
        Nᵀ * GlobalTheory.DblVac.matD g * N + (⅟(2 : AF F)) • (Nᵀ * GlobalTheory.DblVac.matD g * Δ * Z * (Nᵀ * N)) := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    rw [this, hNN, Matrix.mul_smul, smul_smul, invOf_mul_self, one_smul, Matrix.mul_one]
  refine ⟨u, huK, huP, ?_, ?_⟩
  · convert hdet using 2
    exact congrArg Matrix.det key
  · intro z hz; convert hinv z hz using 3
    exact key

end GlobalTheory.InertTransv
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.doubledVacuum_eigenvalue_eq_one_inertPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) (Fin a × Fin (a + a'))),
    (∀ x : Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = G.M.co.e x) →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.V →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) d' dd →
    IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) dd (X.β / X.α) (diagCols (Fin a)) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r → tens (evFin F v) (G.M.vac v) r ≠ 0 →
    ∀ p ∈ GlobalTheory.DblVac.KD σ G.V v, p ∈ GlobalTheory.DblVac.PDiag σ G.V → ∀ μ : ℂ,
      omd p (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) → μ = 1 := by
  first | exact @GlobalTheory.DblVacSiegelV.eigen_eq_one_of_diag | exact GlobalTheory.DblVacSiegelV.eigen_eq_one_of_diag | (intros; apply GlobalTheory.DblVacSiegelV.eigen_eq_one_of_diag <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

theorem _root_.GlobalTheory.T.diagonalLagrangian_invariantForm_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : Darboux (symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)) κ),
        (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
          co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ l ∈ (adeleClass F).adm κ,
        (∀ z : Matrix (Fin nS) (Fin nT) (AF F ⊗[F] E), ∀ φ ∈ schA F κ,
          l ((GlobalTheory.WeilSchrodinger.transD (cA σ) co).rho B.ψ (z * ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id)ᵀ) φ) = l φ) →
        ∃ c : ℂ, ∀ Φ ∈ schA F κ, l Φ = c * GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) := by
  first | exact @GlobalTheory.LagrUniq.lagr_invariant_unique | exact GlobalTheory.LagrUniq.lagr_invariant_unique | (intros; apply GlobalTheory.LagrUniq.lagr_invariant_unique <;> assumption)
end

section

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU
open scoped Matrix

noncomputable section

namespace GlobalTheory.FockKFin.VacFin

open GlobalTheory.ThK.EvAt0.PolD Formalism.BasicNotions.TH

theorem incM_map_piInf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n m : Type}
    (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

theorem Jm_transpose (p q : ℕ) : (Jm p q)ᵀ = Jm p q := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_transpose]

theorem vac_mem_line {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ) (h : GlobalTheory.ThK.IsPair B M χX χW om r s r' s') :
    ∃ v : SInf F (Fin n × Fin d), ∀ g, GaussD M B.emb g → ∃ z : ℂ, g = z • v := by
  have hb := h.base
  choose A hA hAθ using fun w => GlobalTheory.RealLift.frameEx_holds _ _ _ _ _ (h.herm.sig w) (h.herm.cartan w)
  choose C hC hCθ using fun w => GlobalTheory.RealLift.frameEx_holds _ _ _ _ _ (h.skew.sig w) (h.skew.cartan w)
  have hA1 : ∀ w, GlobalTheory.RealLift.IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_piInf, one_smul]; exact hA w
  have hC1 : ∀ w, GlobalTheory.RealLift.IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [incM_map_piInf]; exact hC w
  have fr : GlobalTheory.RealLift.Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.FockMapEx.fockEx_of_derEx GlobalTheory.HeisDer.derEx F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I
    A C hb.cm hb.std fr
  obtain ⟨D, hD⟩ := GlobalTheory.HeisDer.derEx F E σ (Fin n) (Fin d) (Fin n × Fin d) B.ψ (incM F X.J) (incM F W.J) M.co hb.std
  have hDd : ∀ u, At (evI F) u → ∀ f : SInf F (Fin n × Fin d), D u f = dOp (arc (M.co.e u).1) (arc (M.co.e u).2) f := by
    intro u hu f
    refine DFunLike.ext _ _ fun x => ?_
    rw [(hD u hu f).2 x, dOp_apply]
    try rfl
  have tw : ∀ w (c : Matrix (Ix r s) (Ix r' s') ℂ) (e : ℂ),
      A w * (e • (Jm r s * c * Jm r' s')) * (C w)ᵀ = e • (X.θ w * (A w * c * (C w)ᵀ) * (W.θ w)ᵀ) := by
    intro w c e
    have h2 : (C w)ᵀ * (W.θ w)ᵀ = Jm r' s' * (C w)ᵀ := by
      rw [← Matrix.transpose_mul, hCθ w, Matrix.transpose_mul, Jm_transpose]
    calc A w * (e • (Jm r s * c * Jm r' s')) * (C w)ᵀ = e • ((A w * Jm r s) * c * (Jm r' s' * (C w)ᵀ)) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = _ := by rw [← hAθ w, ← h2]; simp only [Matrix.mul_assoc]
  refine ⟨Φ (PiTensorProduct.tprod ℂ fun _ => 1), fun g ⟨ε, hε⟩ => ?_⟩
  refine GlobalTheory.VacLn.vacLine_of_derEx GlobalTheory.HeisDer.derEx F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C Φ
    hb.cm hb.std fr hΦ g ε ?_
  intro u u' hu hu' c hc hc' f f' hf hf'
  have e1 : f = D u g := (GlobalTheory.RealLift.actsLaws F _ g f (D u g)).2.2.2.2 _ hf (hD u hu g).1
  have e2 : f' = D u' g := (GlobalTheory.RealLift.actsLaws F _ g f' (D u' g)).2.2.2.2 _ hf' (hD u' hu' g).1
  rw [e1, e2, hDd u hu, hDd u' hu']
  exact hε u u' hu hu' (fun w => by rw [hc' w, tw, ← hc w])

end GlobalTheory.FockKFin.VacFin

theorem GlobalTheory.FockKFin.vacSp_finiteDimensional : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → FiniteDimensional ℂ (GlobalTheory.FockKFin.vacSp M B.emb) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' h
  obtain ⟨v, hv⟩ := GlobalTheory.FockKFin.VacFin.vac_mem_line σ B n d X W M χX χW om r s r' s' h
  have hle : GlobalTheory.FockKFin.vacSp M B.emb ≤ Submodule.span ℂ {v} := by
    refine Submodule.span_le.2 fun g hg => ?_
    obtain ⟨z, rfl⟩ := hv g hg
    exact Submodule.smul_mem _ z (Submodule.subset_span rfl)
  exact Submodule.finiteDimensional_of_le hle

end
end
