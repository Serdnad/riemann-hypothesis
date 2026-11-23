module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle302
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1268
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1245
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle159
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle311
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.Bundle001
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefIntegralEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle346
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle300
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle303
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiActionTargetFlagUnipotentHomEquivariant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle307
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
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.classSum_inner_eq_sum_vectorThetaLifts : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), (∀ χ ∈ A.X, IsAbsIrrChar χ) → GlobalTheory.LiftRows.SourceLevelLawC R F → GlobalTheory.LiftRows.InnerProductFormulaC R F → GlobalTheory.LiftRows.FockCoefficientC R F → GlobalTheory.LiftRows.FiniteZetaL R F → GlobalTheory.LiftRows.RealLowestKTypeCoeffSquareIntegrable R →
  ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (μ' η' : (AE D)ˣ →* Circle)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
    (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (c : CoefA (Vc D i))
    (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (H : HMod (Bridge.Gf (Vc D i) → c.W)),
  GlobalTheory.LiftRows.IsLiftDataC R F i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io →
  IsMeasDef (Vc D i) (GlobalTheory.AdelicScalar.levV R i A.μ0 R.triv m) (R.νV i A.μ0) (R.fdV i A.μ0) →
  Bridge.IsReps (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y →
  H.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.chrOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m))) (Bridge.adInner (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y) →
  ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, (∀ ρ, ‖((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1) →
  ∀ U₁ ∈ R.Wall i σ, ∀ U₂ ∈ R.Wall i σ, ∀ z₁ z₂ : H.H,
    (∀ h w, inner ℂ (c.ext (H.e z₁) h) w = GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) (U₁ fun ρ => v ρ) h) →
    (∀ h w, inner ℂ (c.ext (H.e z₂) h) w = GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) (U₂ fun ρ => v ρ) h) →
    ∀ {ι : Type} [Fintype ι] (b : OrthonormalBasis ι ℂ c.W),
      inner ℂ z₁ z₂ = ∑ k, GlobalTheory.AdelicScalar.l2 (R.νV i A.μ0) (R.fdV i A.μ0) (GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) (b k))) (U₁ fun ρ => v ρ)) (GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) (b k))) (U₂ fun ρ => v ρ)) := by
  first | exact @GlobalTheory.LiftGram.inner_eq_sum_upLift | exact GlobalTheory.LiftGram.inner_eq_sum_upLift | (intros; apply GlobalTheory.LiftGram.inner_eq_sum_upLift <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.RowsPosRed

theorem exists_unitary_rep {K G V H E : Type} [Field K] [StarRing K] [Group G] [AddCommGroup V] [Module K V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [AddCommGroup E] [Module ℂ E] {σ : K →+* ℂ} (j : V →ₛₗ[σ] H)
    {ι : Type} (b : Module.Basis ι K V) (hli : LinearIndependent ℂ fun k => j (b k))
    (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤) (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hiso : ∀ x y, ⟪j x, j y⟫_ℂ = σ (h x y)) (r : Representation K G V) (hr : ∀ g x y, h (r g x) (r g y) = h x y)
    (Θ : H →ₗ[ℂ] E) (π : Representation ℂ G E) (hΘ : ∀ g z, Θ (j (r g z)) = π g (Θ (j z))) :
    ∃ ρ : Representation ℂ G H, (∀ g z, j (r g z) = ρ g (j z)) ∧ (∀ g y, ‖ρ g y‖ = ‖y‖) ∧
      ∀ g y, Θ (ρ g y) = π g (Θ y) := by
  let B : Module.Basis ι ℂ H := Module.Basis.mk hli hsp.ge
  have hB : ∀ k, B k = j (b k) := fun k => Module.Basis.mk_apply hli hsp.ge k
  let f : G → Module.End ℂ H := fun g => B.constr ℂ fun k => j (r g (b k))
  have hf : ∀ g z, f g (j z) = j (r g z) := by
    intro g z
    have : (f g).comp j = j.comp (r g) := b.ext fun k => by
      show f g (j (b k)) = j (r g (b k))
      rw [← hB]
      exact B.constr_basis ℂ _ k
    exact LinearMap.congr_fun this z
  let ρ : Representation ℂ G H :=
    { toFun := f
      map_one' := B.ext fun k => by
        show f 1 (B k) = B k
        rw [hB, hf, map_one, Module.End.one_apply]
      map_mul' := fun g g' => B.ext fun k => by
        show f (g * g') (B k) = f g (f g' (B k))
        rw [hB, hf, hf, hf, map_mul, Module.End.mul_apply] }
  have hρ : ∀ g z, ρ g (j z) = j (r g z) := hf
  have hin : ∀ g y y', ⟪ρ g y, ρ g y'⟫_ℂ = ⟪y, y'⟫_ℂ := by
    intro g
    have h1 : ∀ k y', ⟪ρ g (B k), ρ g y'⟫_ℂ = ⟪B k, y'⟫_ℂ := by
      intro k
      have : (innerₛₗ ℂ (ρ g (B k))).comp (ρ g) = innerₛₗ ℂ (B k) := B.ext fun l => by
        show ⟪ρ g (B k), ρ g (B l)⟫_ℂ = ⟪B k, B l⟫_ℂ
        rw [hB, hB, hρ, hρ, hiso, hiso, hr]
      exact fun y' => LinearMap.congr_fun this y'
    intro y y'
    have : (innerₛₗ ℂ (ρ g y)).comp (ρ g) = innerₛₗ ℂ y := B.ext fun l => by
      show ⟪ρ g y, ρ g (B l)⟫_ℂ = ⟪y, B l⟫_ℂ
      rw [← inner_conj_symm, h1, inner_conj_symm]
    exact LinearMap.congr_fun this y'
  refine ⟨ρ, fun g z => (hρ g z).symm, fun g y => ?_, fun g => ?_⟩
  · rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, hin]
  · have : Θ.comp (ρ g) = (π g).comp Θ := B.ext fun k => by
      show Θ (ρ g (B k)) = π g (Θ (B k))
      rw [hB, hρ, hΘ]
    exact fun y => LinearMap.congr_fun this y

end GlobalTheory.RowsPosRed

namespace GlobalTheory.RowsPosRed

open Formalism.IndefR.Cx.CxData

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem sum_idem_gEx (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : GlobalTheory.Hk3.Core R.toRealDat F.lv2) (x : (R.toCx3 F).EE) :
    ∑ g, A3.A.fam.v0.embedding ((idemOf A3.A.X).coeff g) • R.gEx F g x = x := by
  have h := GlobalTheory.AdjGood.proj_rows_core hC (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) x)
  have e : ∀ g, Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H)
      (A3.A.fam.v0.embedding ((idemOf A3.A.X).coeff g) • R.gEx F g x) =
      D.what₂.embLL ((idemOf A3.A.X).coeff g) • R.gE g (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) x) := by
    intro g
    have hc : cj (twAt D.what₂.embLL A3.A.v0) (A3.A.v0.embedding ((idemOf A3.A.X).coeff g)) =
        D.what₂.embLL ((idemOf A3.A.X).coeff g) := by
      rw [R.emb0, cj_cj]
    exact congrArg (fun z : ℂ => z • R.gE g (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) x)) hc
  exact (Finset.sum_congr rfl fun g _ => e g).trans h

theorem range_le_span_rat {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}
    (X : CxData A) (cv : CrdV A) (hK : X.KFormR) (hJ : X.JIsoR cv) (hT : Formalism.IndefR.Rat.RowTest X) (t : Bs.Tup) :
    LinearMap.range (LinearMap.adjoint (X.Θ t)) ≤
      Submodule.span ℂ (X.jR t '' {z | X.jR t z ∈ LinearMap.range (LinearMap.adjoint (X.Θ t))}) := by
  obtain ⟨N, ψ, hψ, hr⟩ := hT
  exact (Formalism.IndefR.Rat.range_adjoint_rat _ (X.jR t) (cv.hR t) (bR t) (hK t).1 (hK t).2 (hJ t) (X.Θ t) ψ hψ
    (fun i x => hr t i x)).ge

theorem exists_rho (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ} (hOk : A3.fam3.Ok3 s) (hM : R.toRealDat.IsModels)
    (hGE : R.PGEquiv F) :
    ∃ ρ : Representation ℂ G ((R.toCx3 F).FC A3.A.fam.μ0),
      (∀ g z, (R.toCx3 F).jR A3.A.fam.μ0 ((A3.A.fam.R A3.A.fam.μ0).r g z) = ρ g ((R.toCx3 F).jR A3.A.fam.μ0 z)) ∧
      (∀ g y, ‖ρ g y‖ = ‖y‖) ∧
      ∀ g y, (R.toCx3 F).Θ A3.A.fam.μ0 (ρ g y) = R.gEx F g ((R.toCx3 F).Θ A3.A.fam.μ0 y) := by
  have hKR : (R.toCx3 F).KFormR := RealDat3.kFormR_of hM
  have hJR : (R.toCx3 F).JIsoR F.cv := RealDat3.jIsoR_of hM
  exact exists_unitary_rep (V := (A3.A.fam.R A3.A.fam.μ0).S.Forms) (H := (R.toCx3 F).FC A3.A.fam.μ0)
    ((R.toCx3 F).jR A3.A.fam.μ0) (Formalism.IndefR.Cx.CxData.bR (A := A3.fam3.amb3) A3.A.fam.μ0) (hKR A3.A.fam.μ0).1
    (hKR A3.A.fam.μ0).2 (F.cv.hR A3.A.fam.μ0) (hJR A3.A.fam.μ0) (A3.A.fam.R A3.A.fam.μ0).r
    (fun g x y => (hOk.ok2.what₂ A3.A.fam.μ0).act.unitary g x y) ((R.toCx3 F).Θ A3.A.fam.μ0) (R.gEx F)
    (fun g z => hGE.1 A3.A.fam.μ0 g z)

theorem exists_row (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hM : R.toRealDat.IsModels) (hN : RowsNe R.toRealDat F.lv2)
    (b : Bool) : ∃ u : (R.toCx3 F).EE, u ≠ 0 ∧ u ∈ (R.toCx3 F).EEl b := by
  obtain ⟨U, hU, hU0⟩ := (Submodule.ne_bot_iff _).1 (hN b)
  have hT : U ∈ R.EEat R.triv := GlobalTheory.GoodRowsLevel.eeat_le_triv R.toRealDat _ hU
  obtain ⟨y, rfl⟩ : U ∈ LinearMap.range R.HE.e := hM.HE.2.1 ▸ hT
  refine ⟨Tw.mk (twAt D.what₂.embLL A3.A.v0) y, fun h0 => hU0 ?_, hU⟩
  have : y = 0 := h0
  rw [this, map_zero]


omit [Fintype G] in
theorem tw_eq_zero {s : Bool} {E E' : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [FiniteDimensional ℂ E'] (f : E →ₗ[ℂ] E')
    (hf : Function.Injective (LinearMap.adjoint f)) (v : Tw s E') (h1 : ∀ y : Tw s E, ⟪Tw.map s f y, v⟫_ℂ = 0) : v = 0 := by
  have h5 : LinearMap.adjoint f (Tw.out v) = 0 := by
    refine ext_inner_left ℂ fun y => ?_
    rw [LinearMap.adjoint_inner_right, inner_zero_right]
    have h3 : cj s ⟪f y, Tw.out v⟫_ℂ = 0 := h1 (Tw.mk s y)
    have h4 := congrArg (cj s) h3
    rwa [cj_cj, map_zero] at h4
  exact hf (h5.trans (map_zero _).symm)

theorem surj_of_upInj (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hUp : UpInj R.toRealDat) (x : (R.toCx3 F).EE) :
    ∃ u, (R.toCx3 F).Θ A3.A.fam.μ0 (LinearMap.adjoint ((R.toCx3 F).Θ A3.A.fam.μ0) u) = x := by
  have hinj : ∀ v, LinearMap.adjoint ((R.toCx3 F).Θ A3.A.fam.μ0) v = 0 → v = 0 := by
    intro v hv
    have h1 : ∀ y : (R.toCx3 F).FC A3.A.fam.μ0, ⟪(R.toCx3 F).Θ A3.A.fam.μ0 y, v⟫_ℂ = 0 := fun y => by
      rw [← LinearMap.adjoint_inner_right, hv, inner_zero_right]
    exact tw_eq_zero (s := twAt D.what₂.embLL A3.A.v0) (R.Th A3.A.fam.μ0) (hUp A3.A.fam.μ0) v h1
  have h2 : Function.Injective ((R.toCx3 F).Θ A3.A.fam.μ0 ∘ₗ LinearMap.adjoint ((R.toCx3 F).Θ A3.A.fam.μ0)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h3 : ⟪LinearMap.adjoint ((R.toCx3 F).Θ A3.A.fam.μ0) v, LinearMap.adjoint ((R.toCx3 F).Θ A3.A.fam.μ0) v⟫_ℂ = 0 := by
      rw [LinearMap.adjoint_inner_left]
      rw [LinearMap.comp_apply] at hv
      rw [hv, inner_zero_right]
    exact hinj v (inner_self_eq_zero.1 h3)
  exact LinearMap.injective_iff_surjective.1 h2 x

theorem dZ_pos_of_row (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ} (hOk : A3.fam3.Ok3 s) (hC : R.WeakCharacterisation F)
    (hEx : R.toRealDat.ExAt) (hUp : UpInj R.toRealDat) (hGE : R.PGEquiv F) (hRT : Formalism.IndefR.Rat.RowTest (R.toCx3 F))
    (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (u : (R.toCx3 F).EE) (hu0 : u ≠ 0)
    (hu : u ∈ typeSp3 A3 (R.toCx3 F) (R.gEx F) P ψ) :
    0 < (A3.A.fam.R A3.A.fam.μ0).dZ (A3.A.fam.lvl P ψ) ((R.toCx3 F).Z A3.A.fam.μ0) := by
  have hM : R.toRealDat.IsModels := hC.base.models
  have hrat := range_le_span_rat (R.toCx3 F) F.cv (RealDat3.kFormR_of hM) (RealDat3.jIsoR_of hM) hRT A3.A.fam.μ0
  obtain ⟨ρ, hj, hρ, hΘ⟩ := exists_rho R F hOk hM hGE
  have hCore := (GlobalTheory.CoreOfWeak.core_of_weak R F hC hEx).1
  have htype : ∀ h : P, R.gEx F (h : G) u = A3.A.fam.v0.embedding ((ψ h : D.what₂.LLˣ) : D.what₂.LL) • u := by
    intro h
    have := (Submodule.mem_iInf _).1 hu h
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
    exact this
  obtain ⟨w, hw⟩ := surj_of_upInj R F hUp u
  obtain ⟨z, hz0, hz⟩ := GlobalTheory.RowsNonzero.exists_rational ((R.toCx3 F).jR A3.A.fam.μ0) (A3.A.fam.R A3.A.fam.μ0).r ρ
    (R.gEx F) ((R.toCx3 F).Θ A3.A.fam.μ0) hj hρ hΘ hrat (fun g => (idemOf A3.A.X).coeff g)
    (fun g => (lvlIdem P ψ).coeff g) hu0 hw (sum_idem_gEx R F hCore u)
    (GlobalTheory.RowsNonzero.sum_lvlIdem (R.gEx F) P ψ htype)
  exact GlobalTheory.RowsNonzero.dZ_pos (A3.A.fam.R A3.A.fam.μ0) (A3.A.fam.lvl P ψ) ((R.toCx3 F).Z A3.A.fam.μ0) hz0 hz

end GlobalTheory.RowsPosRed

theorem GlobalTheory.RowsPosRed.pos_of_rows : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → UpInj R.toRealDat → RowsNe R.toRealDat F.lv2 → R.PGEquiv F → (R.toCx3 F).zs.InBlock → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hC hEx hUp hNe hGE _ hRT b
  have hel := GlobalTheory.LevelRows3.eel_eq_typeSp3 R F hC
  obtain ⟨u, hu0, hu⟩ := GlobalTheory.RowsPosRed.exists_row R F hC.base.models hNe b
  cases b
  · rw [hel.1] at hu
    exact GlobalTheory.RowsPosRed.dZ_pos_of_row R F hOk hC hEx hUp hGE hRT F.P0 F.ψ0 u hu0 hu
  · rw [hel.2] at hu
    exact GlobalTheory.RowsPosRed.dZ_pos_of_row R F hOk hC hEx hUp hGE hRT F.P1 F.ψ1 u hu0 hu
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoMeanSmear

theorem exists_bound {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V W : HSp D}
    {G : WO V W → ℂ} (hG : IsThetaFunO ψ V W G) : ∃ C, ∀ u, ‖G u‖ ≤ C := by
  obtain ⟨-, -, -, -, -, K, hK, hcov⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V.rank
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hG.cont.continuousOn
  refine ⟨C, fun u => ?_⟩
  obtain ⟨γ, hγm, hγ⟩ := hcov u
  obtain ⟨γ0, rfl⟩ := hγm
  have e : ((incA D).toAddMonoidHom.mapMatrix (m := Fin W.rank) (n := Fin V.rank)) γ0 = ratW W V γ0 := rfl
  have h1 := hC _ hγ
  rw [e, hG.quasi, norm_mul, hψ.1.2.1, one_mul] at h1
  exact h1

theorem continuous_emb {D : D7} (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) : Continuous (GlobalTheory.IsoMean.emb V W P Q) := by
  unfold GlobalTheory.IsoMean.emb
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

end GlobalTheory.IsoMeanSmear

namespace GlobalTheory.IsoMeanSmear

theorem smear : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne (GlobalTheory.MixModel.ratMx D a b) μ 𝓨 → ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' → Continuous (fun u => ∫ ξ in 𝓨, heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q ξ) G u * star (G' u) ∂μ) ∧ (∀ γ ∈ ratL W V, ∀ u, ∫ ξ in 𝓨, heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q ξ) G (γ + u) * star (G' (γ + u)) ∂μ = ∫ ξ in 𝓨, heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q ξ) G u * star (G' u) ∂μ) ∧ ∀ φ : WO V W → ℂ, Continuous φ → (∀ u, ‖φ u‖ ≤ 1) → ∫ ξ in 𝓨, (∫ u in 𝓕, φ u * (heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q ξ) G u * star (G' u)) ∂ν) ∂μ = ∫ u in 𝓕, φ u * (∫ ξ in 𝓨, heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q ξ) G u * star (G' u) ∂μ) ∂ν := by
  intro D V W a b P Q ψ hψ μ 𝓨 hμ ν 𝓕 hν h𝓕 G G' hG hG'
  obtain ⟨hHaar, -, h1⟩ := hμ
  obtain ⟨-, -, s1, -, -, -⟩ := GlobalTheory.MixModel.lattice_Mx D a b
  obtain ⟨-, -, s2, -, -, K, hK, hcov⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V.rank
  haveI := s1
  haveI := s2
  haveI : FirstCountableTopology (WO V W) := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology (WO V W)
  haveI : BorelSpace (Mx D a b) := ⟨rfl⟩
  haveI : BorelSpace (WO V W) := ⟨rfl⟩
  haveI hfμ : IsFiniteMeasure (μ.restrict 𝓨) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  haveI : Countable D.host.E := by
    haveI : FiniteDimensional ℚ D.host.E := inferInstance
    exact (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin W.rank) (Fin V.rank) D.host.E) :=
    inferInstanceAs (Countable (Fin W.rank → Fin V.rank → D.host.E))
  haveI : Countable (ratL W V) := (Set.countable_range _).to_subtype
  have hνF : ν 𝓕 < ⊤ := by
    have hcov' : ∀ x : WO V W, ∃ γ ∈ ratL W V, γ + x ∈ K := hcov
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (ratL W V) hK hcov' ν h𝓕
  haveI hfν : IsFiniteMeasure (ν.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hνF⟩
  haveI : SFinite (ν.restrict 𝓕) := @instSFiniteOfSigmaFinite _ _ _ (@IsFiniteMeasure.toSigmaFinite _ _ _ hfν)
  haveI : SFinite (μ.restrict 𝓨) := @instSFiniteOfSigmaFinite _ _ _ (@IsFiniteMeasure.toSigmaFinite _ _ _ hfμ)
  obtain ⟨C, hC⟩ := exists_bound hψ hG
  obtain ⟨C', hC'⟩ := exists_bound hψ hG'
  set Φ : Mx D a b × WO V W → ℂ := fun p => heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q p.1) G p.2 * star (G' p.2) with hΦ
  have he := continuous_emb V W P Q
  have hcont : Continuous Φ := by
    simp only [hΦ, heisO]
    exact ((hψ.1.1.comp (GlobalTheory.OrientedHeis.continuous_symplOH continuous_snd (he.comp continuous_fst))).mul
      (hG.cont.comp (continuous_snd.add (he.comp continuous_fst)))).mul (hG'.cont.comp continuous_snd).star
  have hbd : ∀ p, ‖Φ p‖ ≤ C * C' := by
    intro p
    simp only [hΦ, heisO, norm_mul, norm_star, hψ.1.2.1, one_mul]
    exact mul_le_mul (hC _) (hC' _) (norm_nonneg _) ((norm_nonneg _).trans (hC 0))
  refine ⟨?_, ?_, ?_⟩
  · refine continuous_of_dominated (bound := fun _ => C * C') (fun u => ?_) (fun u => ?_) (integrable_const _) ?_
    · have hu : Continuous fun ξ => Φ (ξ, u) := hcont.comp (continuous_id.prodMk continuous_const)
      exact hu.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun ξ => hbd (ξ, u)
    · refine Filter.Eventually.of_forall fun ξ => ?_
      have hξ : Continuous fun u => Φ (ξ, u) := hcont.comp (continuous_const.prodMk continuous_id)
      exact hξ
  · intro γ hγ u
    obtain ⟨γ0, rfl⟩ := hγ
    have er : ((incA D).toAddMonoidHom.mapMatrix (m := Fin W.rank) (n := Fin V.rank)) γ0 = ratW W V γ0 := rfl
    rw [er]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    have hH := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hG (GlobalTheory.IsoMean.emb V W P Q ξ)
    simp only
    rw [hH.quasi, hG'.quasi, star_mul]
    have hn : ψ (-(symplOH V W (ratW W V γ0) u)) * star (ψ (-(symplOH V W (ratW W V γ0) u))) = 1 := by
      have h1 := hψ.1.2.1 (-(symplOH V W (ratW W V γ0) u))
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]
      norm_num
    linear_combination (heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q ξ) G u * star (G' u)) * hn
  · intro φ hφ hφ1
    have hint : Integrable (Function.uncurry fun ξ u => φ u * Φ (ξ, u)) ((μ.restrict 𝓨).prod (ν.restrict 𝓕)) := by
      refine Integrable.of_bound ?_ (C * C') (Filter.Eventually.of_forall fun p => ?_)
      · exact ((hφ.comp continuous_snd).mul hcont).aestronglyMeasurable
      · simp only [Function.uncurry, norm_mul]
        calc ‖φ p.2‖ * ‖Φ (p.1, p.2)‖ ≤ 1 * (C * C') :=
              mul_le_mul (hφ1 _) (hbd _) (norm_nonneg _) zero_le_one
          _ = C * C' := one_mul _
    refine (integral_integral_swap hint).trans ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    exact integral_const_mul _ _

end GlobalTheory.IsoMeanSmear
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ENNReal

noncomputable section

namespace GlobalTheory.ThetaLiftBound

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_rat_height_le {D : D7} (W : HSp D) (h : GA D W) :
    ∃ γ ∈ GQ W, GlobalTheory.Grow.height W (γ * h) ≤ 2 * GlobalTheory.Grow.quotHeight W h := by
  have hq := GlobalTheory.Grow.one_le_quotHeight W h
  by_contra hne
  push_neg at hne
  have : 2 * GlobalTheory.Grow.quotHeight W h ≤ GlobalTheory.Grow.quotHeight W h :=
    (GlobalTheory.Grow.le_quotHeight_iff W).2 fun γ hγ => (hne γ hγ).le
  linarith

theorem bound_pow (c a b M q : ℝ) (A : ℕ) (ha : 1 ≤ a) (haM : a ≤ M) (hb : 1 ≤ b) (hbq : b ≤ 2 * q) :
    c * (a * b) ^ A ≤ max c 0 * (M * (2 * q)) ^ A := by
  have hX : a * b ≤ M * (2 * q) := mul_le_mul haM hbq (by linarith) (by linarith)
  have hXp : (a * b) ^ A ≤ (M * (2 * q)) ^ A := pow_le_pow_left₀ (mul_nonneg (by linarith) (by linarith)) hX A
  exact (mul_le_mul_of_nonneg_right (le_max_left c 0) (pow_nonneg (mul_nonneg (by linarith) (by linarith)) A)).trans
    (mul_le_mul_of_nonneg_left hXp (le_max_right c 0))

theorem bound_mul (c M q f C' : ℝ) (A : ℕ) (hM : 0 ≤ M) (hq : 0 ≤ q) (hf : 0 ≤ f) (hF : f * q ^ A ≤ C') :
    max c 0 * (M * (2 * q)) ^ A * f ≤ max c 0 * (2 * M) ^ A * max C' 0 := by
  have e : max c 0 * (M * (2 * q)) ^ A * f = max c 0 * (2 * M) ^ A * (f * q ^ A) := by
    rw [mul_pow, mul_pow, mul_pow]; ring
  rw [e]
  exact mul_le_mul_of_nonneg_left (hF.trans (le_max_left _ _))
    (mul_nonneg (le_max_right c 0) (pow_nonneg (by linarith) A))

theorem lintegral_ne_top : ∀ (D : D7) (V W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C → ∀ (κ : Measure (NI V C)) (𝓝 : Set (NI V C)), κ.IsHaarMeasure → IsFundamentalDomain (NIQ V C) 𝓝 κ → ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν → ∀ F : GA D W → ℂ, GlobalTheory.Grow.RapidDec W F → ∀ (Sg : GA D V × GA D W → ℝ≥0∞), (∀ n ∈ NI V C, n ∈ GQ V → ∀ a b, Sg (n * a, b) = Sg (a, b)) → (∀ γ ∈ GQ W, ∀ a b, Sg (a, γ * b) = Sg (a, b)) → ∀ (A : ℕ) (c : ℝ), (∀ a b, Sg (a, b) ≤ ENNReal.ofReal (c * (GlobalTheory.Grow.height V a * GlobalTheory.Grow.height W b) ^ A)) → ∀ g : GA D V, ∫⁻ n in 𝓝, ∫⁻ h in 𝓕, Sg ((n : GA D V) * g, h) * ‖F h‖ₑ ∂ν ∂κ ≠ ⊤ := by
  intro D V W r C hC κ 𝓝 hκ h𝓝 ν 𝓕 hν h𝓕 F hF Sg h1 h2 A c hc g
  obtain ⟨K, hK, hcov⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D V r C ⟨hC.2.1, hC.2.2⟩).2
  obtain ⟨M, hM⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact V
    (hK.image (f := fun k : NI V C => (k : GA D V) * g) (by fun_prop))
  obtain ⟨C', hC'⟩ := hF.2.2 A
  have hbound : ∀ n : NI V C, ∀ h, Sg ((n : GA D V) * g, h) * ‖F h‖ₑ ≤
      ENNReal.ofReal (max c 0 * (2 * M) ^ A * max C' 0) := by
    intro n h
    obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov n
    obtain ⟨γ', hγ', hh⟩ := exists_rat_height_le W h
    have e1 : Sg (((γ * k : NI V C) : GA D V) * g, h) = Sg ((k : GA D V) * g, γ' * h) := by
      rw [Subgroup.coe_mul, mul_assoc, h1 _ γ.2 (Subgroup.mem_subgroupOf.1 hγ), h2 _ hγ']
    rw [e1]
    have hkM : GlobalTheory.Grow.height V ((k : GA D V) * g) ≤ M := hM _ ⟨k, hk, rfl⟩
    have hV1 := GlobalTheory.Grow.one_le_height V ((k : GA D V) * g)
    have hW1 := GlobalTheory.Grow.one_le_height W (γ' * h)
    have hq1 := GlobalTheory.Grow.one_le_quotHeight W h
    have hc1 := bound_pow c _ _ M (GlobalTheory.Grow.quotHeight W h) A hV1 hkM hW1 hh
    have hb := bound_mul c M (GlobalTheory.Grow.quotHeight W h) ‖F h‖ C' A (by linarith) (by linarith) (norm_nonneg _) (hC' h)
    calc Sg ((k : GA D V) * g, γ' * h) * ‖F h‖ₑ
        ≤ ENNReal.ofReal (max c 0 * (M * (2 * GlobalTheory.Grow.quotHeight W h)) ^ A) * ENNReal.ofReal ‖F h‖ := by
          rw [ofReal_norm_eq_enorm]
          exact mul_le_mul' ((hc _ _).trans (ENNReal.ofReal_le_ofReal hc1)) le_rfl
      _ = ENNReal.ofReal (max c 0 * (M * (2 * GlobalTheory.Grow.quotHeight W h)) ^ A * ‖F h‖) :=
          (ENNReal.ofReal_mul (mul_nonneg (le_max_right c 0)
            (pow_nonneg (mul_nonneg (by linarith) (by linarith)) A))).symm
      _ ≤ ENNReal.ofReal (max c 0 * (2 * M) ^ A * max C' 0) := ENNReal.ofReal_le_ofReal hb
  have hν𝓕 := (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol W ν 𝓕 hν h𝓕).ne
  have hκ𝓝 := GlobalTheory.TowerCT.vol D V r C hC κ 𝓝 hκ h𝓝
  refine ne_top_of_le_ne_top ?_ (lintegral_mono fun n => lintegral_mono fun h => hbound n h)
  rw [setLIntegral_const, setLIntegral_const]
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hν𝓕) hκ𝓝

end GlobalTheory.ThetaLiftBound

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isCuspFun_of_tendsto_moderateGrowthSize : ∀ (D : D7) (V : HSp D) (N : ℕ) (ψ : ℕ → GA D V → ℂ) (f : GA D V → ℂ), (∀ n, Continuous (ψ n) ∧ (∀ γ ∈ GQ V, ∀ g, ψ n (γ * g) = ψ n g) ∧ IsCuspFun V (ψ n)) → Continuous f → (∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) → Filter.Tendsto (fun n => GlobalTheory.Size.growthSize V N (ψ n - f)) Filter.atTop (nhds 0) → IsCuspFun V f := by
  first | exact @GlobalTheory.CuspLimit.isCuspFun_of_tendsto | exact GlobalTheory.CuspLimit.isCuspFun_of_tendsto | (intros; apply GlobalTheory.CuspLimit.isCuspFun_of_tendsto <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.flag_unipotent_bessel_character_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (S S₀ A L : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) (θ : D.host.E), (∀ z, Continuous (psiBes ψ d θ z)) ∧ (∀ z, ∀ γ ∈ GQ S, psiBes ψ d θ z γ = 1) ∧ (∀ n h, psiBes ψ d θ (vecB o ζ) (embA d o h * n * (embA d o h)⁻¹) = psiBes ψ d θ (vecB o ζ) n) ∧ (∀ n h, psiFlag ψ d (d.emb0 h * n * (d.emb0 h)⁻¹) = psiFlag ψ d n) ∧ (∀ g, g ∈ besGrp d o ↔ ∃ n ∈ flagN d, ∃ h, g = n * embA d o h) ∧ ∀ ι : A.V →ₗ[D.host.E] S.V, frameMat S A ι = d.i₀ * o.iA → ∀ h, EmbRel S A ι (embA d o h) h := by
  first | exact @GlobalTheory.MixPer.charLaws | exact GlobalTheory.MixPer.charLaws | (intros; apply GlobalTheory.MixPer.charLaws <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.flag_unipotent_fourier_jacobi_group_structure : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), (∀ n, n ∈ flagN d ↔ ∃ u ∈ UX D ρ, ∃ b c, n = d.levi u * (d.nB b * d.nC c)) ∧ (∀ n, n ∈ radX d ↔ ∃ b c, n = d.nB b * d.nC c) ∧ (∀ g, g ∈ stabX d ↔ ∃ n ∈ radX d, ∃ h, g = n * d.emb0 h) ∧ (∀ g, g ∈ jacGrp d ↔ ∃ n ∈ flagN d, ∃ h, g = n * d.emb0 h) ∧ (∀ n ∈ flagN d, ∀ h, d.emb0 h * n * (d.emb0 h)⁻¹ ∈ flagN d) ∧ (∀ n ∈ flagN d, ∀ n' ∈ flagN d, ∀ h h', n * d.emb0 h = n' * d.emb0 h' → n = n' ∧ h = h') ∧ ∀ u b c u' b' c', d.levi u * (d.nB b * d.nC c) = d.levi u' * (d.nB b' * d.nC c') → u = u' ∧ b = b' ∧ c = c' := by
  first | exact @GlobalTheory.MixPer.flag_jacobi_structure | exact GlobalTheory.MixPer.flag_jacobi_structure | (intros; apply GlobalTheory.MixPer.flag_jacobi_structure <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.jacobi_action_target_flag_unipotent_hom_equivariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (T T₀ S : HSp D) (ρ : ℕ) (d : HypDec T T₀ ρ) (y : Mx D S.rank ρ), (∀ u ∈ UX D ρ, y ⬝ u.1 = y) → (∀ b c, cenT d S y (d.nB b * d.nC c) = d.qT S c y) ∧ (∀ n ∈ flagN d, ∀ n' ∈ flagN d, ptT d S y (n * n') = ptT d S y n + ptT d S y n' ∧ cenT d S y (n * n') = cenT d S y n + cenT d S y n' + symplOH S T₀ (ptT d S y n) (ptT d S y n') ∧ ∀ f, jacT ψ d S y (n * n') f = jacT ψ d S y n (jacT ψ d S y n' f)) ∧ (∀ n ∈ flagN d, ∀ u ∈ UX D ρ, jacT ψ d S y (n * d.levi u) = jacT ψ d S y n) ∧ ∀ n g, ptT d S y (d.emb0 g * n * (d.emb0 g)⁻¹) = actO S T₀ 1 g (ptT d S y n) ∧ cenT d S y (d.emb0 g * n * (d.emb0 g)⁻¹) = cenT d S y n := by
  first | exact @GlobalTheory.MixPer.jacT_hom | exact GlobalTheory.MixPer.jacT_hom | (intros; apply GlobalTheory.MixPer.jacT_hom <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.complexDerivative_rightDerivative_commutator : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (τ τ' : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ), ∀ X ∈ lieAt V τ, ∀ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V, (RderC θ V τ Z (Rder θ V τ X φ) = Rder θ V τ X (RderC θ V τ Z φ) + RderC θ V τ (Z * X - X * Z) φ) ∧ (τ' ≠ τ → RderC θ V τ' Z (Rder θ V τ X φ) = Rder θ V τ X (RderC θ V τ' Z φ)) := by
  first | exact @GlobalTheory.DerBracket.RderC_Rder | exact GlobalTheory.DerBracket.RderC_Rder | (intros; apply GlobalTheory.DerBracket.RderC_Rder <;> assumption)
end
