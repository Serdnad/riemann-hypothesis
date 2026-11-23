module

public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle356
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle396
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle398
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim

noncomputable section

namespace GlobalTheory.BrRat

open MvPolynomial _root_.Formalism.L2.Col Formalism.L2.Ker

section General

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem projVV_of_mem {K : Type} [Field K] [CharZero K] (sg : ι → DomWeight n) (x : VV K sg) :
    Br.projVV sg x.1 = x := by
  have h := GlobalTheory.Proof.TensorMapDescent.eq_zero_of_fockB sg (Br.projVV sg x.1 - x) fun i => by
    rw [← fockBL_apply, Submodule.coe_sub, map_sub, fockBL_apply, fockBL_apply,
      GlobalTheory.Proof.TensorMapDescent.fockB_projVV_basis, sub_self]
  exact sub_eq_zero.mp h

theorem exists_map_eq {K : Type} [Field K] (φ : K →+* ℂ) {σ : Type} (P : MvPolynomial σ ℂ)
    (h : ∀ m, AddMonoidAlgebra.coeff P m ∈ Set.range φ) : ∃ P₀ : MvPolynomial σ K, map φ P₀ = P := by
  classical
  choose c hc using h
  refine ⟨∑ m ∈ P.support, monomial m (c m), ?_⟩
  conv_rhs => rw [P.as_sum]

  simp [map_sum, map_monomial, hc]

theorem descend {K : Type} [Field K] [CharZero K] (φ : K →+* ℂ) (sg : ι → DomWeight n) (x : VV ℂ sg)
    (h : ∀ m, AddMonoidAlgebra.coeff x.1 m ∈ Set.range φ) : ∃ y : VV K sg, map φ y.1 = x.1 := by
  obtain ⟨P₀, hP⟩ := exists_map_eq φ x.1 h
  refine ⟨Br.projVV sg P₀, ?_⟩
  rw [← GlobalTheory.Proof.TensorMapDescent.projVV_map φ sg P₀, hP, projVV_of_mem]

theorem map_frDet {K : Type} [Field K] (φ : K →+* ℂ) (τ : ι) : map φ (frDet K n τ) = frDet ℂ n τ := by
  unfold frDet
  rw [RingHom.map_det]
  congr 1
  ext a s
  simp

theorem map_dualSubst {K : Type} [Field K] (φ : K →+* ℂ) (P : Pol K ι n) :
    map φ (dualSubst K ι n P) = dualSubst ℂ ι n (map φ P) := by
  have e : (map φ : Pol K ι n →+* Pol ℂ ι n).comp (dualSubst K ι n).toRingHom =
      (dualSubst ℂ ι n).toRingHom.comp (map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [dualSubst]
    · intro v
      have hm : (Matrix.of fun a s : Fin n => (X (v.1, a, s) : Pol ℂ ι n)) =
          (map φ : Pol K ι n →+* Pol ℂ ι n).mapMatrix (Matrix.of fun a s : Fin n => (X (v.1, a, s) : Pol K ι n)) := by
        ext a s
        simp
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, dualSubst, aeval_X, map_X]
      rw [hm, ← RingHom.map_adjugate]
      rfl
  exact DFunLike.congr_fun e P

theorem isFunForm_map {K : Type} [Field K] (φ : K →+* ℂ) (σ : ι → DomWeight n) {F : VV K σ}
    {f : VV K fun τ => (σ τ).dual} (h : IsFunForm σ F f) :
    IsFunForm σ ⟨map φ F.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV φ σ _ F.2⟩
      ⟨map φ f.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV φ _ _ f.2⟩ := by
  unfold IsFunForm at h ⊢
  have h1 := congrArg (map φ) h
  simp only [map_mul, map_prod, map_pow, map_frDet, map_dualSubst] at h1
  exact h1

theorem covOf_eq (σ : ι → DomWeight n) (f : VV ℂ fun τ => (σ τ).dual) : covOf σ f = (funEquiv σ).symm f := by
  have hex : ∃ φ : (VV ℂ fun τ => (σ τ).dual) →ₗ[ℂ] VV ℂ σ, ∀ f, IsFunForm σ (φ f) f :=
    ⟨(funEquiv σ).symm.toLinearMap, fun f => (isFunForm_iff_eq σ _ f).2 (by simp)⟩
  have e : covOf σ f = hex.choose f := by rw [covOf, dite_eq_left hex]
  rw [e]
  apply (funEquiv σ).injective
  rw [LinearEquiv.apply_symm_apply]
  exact ((isFunForm_iff_eq σ _ f).1 (hex.choose_spec f)).symm

theorem covOf_desc {K : Type} [Field K] [CharZero K] (φ : K →+* ℂ) (σ : ι → DomWeight n)
    (f : VV ℂ fun τ => (σ τ).dual) (hf : ∀ m, AddMonoidAlgebra.coeff f.1 m ∈ Set.range φ) :
    ∃ F₀ : VV K σ, map φ F₀.1 = (covOf σ f).1 := by
  obtain ⟨f₀, hf₀⟩ := descend φ _ f hf
  refine ⟨(funEquiv σ).symm f₀, ?_⟩
  have h1 : IsFunForm σ ((funEquiv σ).symm f₀) f₀ := by
    have := isFunForm_funEquiv σ ((funEquiv σ).symm f₀)
    rwa [LinearEquiv.apply_symm_apply] at this
  have h2 := isFunForm_map φ σ h1
  have h4 : f = funEquiv σ ⟨map φ ((funEquiv σ).symm f₀).1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV φ σ _ ((funEquiv σ).symm f₀).2⟩ := by
    rw [← (isFunForm_iff_eq σ _ _).1 h2]
    exact Subtype.ext hf₀.symm
  rw [covOf_eq, h4, LinearEquiv.symm_apply_apply]

theorem brPair_mem_range {K : Type} [Field K] [CharZero K] (φ : K →+* ℂ) (σ : ι → DomWeight n) {N : ℕ}
    (hN : N = n + 1) (Λ : ι → DomWeight N) (U : VV ℂ Λ) (V : VV ℂ fun τ => (σ τ).dual)
    (hU : ∀ m, AddMonoidAlgebra.coeff U.1 m ∈ Set.range φ) (hV : ∀ m, AddMonoidAlgebra.coeff V.1 m ∈ Set.range φ) :
    brPair σ hN Λ U V ∈ Set.range φ := by
  obtain ⟨U₀, hU₀⟩ := exists_map_eq φ U.1 hU
  obtain ⟨F₀, hF₀⟩ := covOf_desc φ σ V hV
  refine ⟨(extNormB K σ)⁻¹ * fockB (Br.brStdP hN Λ σ U₀ : Pol K ι n) F₀.1, ?_⟩
  rw [brPair, LinearMap.compl₁₂_apply, pairBK_apply, pairB_apply, ← hF₀, Br.brStd, LinearMap.comp_apply,
    Submodule.subtype_apply, ← hU₀, GlobalTheory.Proof.TensorMapDescent.branchingProjection_map, GlobalTheory.Proof.TensorMapDescent.fockB_map, map_mul, map_inv₀]
  congr 2
  unfold extNormB
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← GlobalTheory.Proof.TensorMapDescent.fockB_map, Formalism.L2.DIV.map_extremal]

end General

end GlobalTheory.BrRat

namespace GlobalTheory.RowClaim

theorem brPair_mem_coefField : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ch.Is → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ (U : VV ℂ (wt ch.G (.top D.R.m))) (V : VV ℂ (wt ch.G (.grid D.R.m D.R.m))), (∀ m, AddMonoidAlgebra.coeff U.1 m ∈ Set.range D.what₂.embLL) → (∀ m, AddMonoidAlgebra.coeff V.1 m ∈ Set.range D.what₂.embLL) → brPair (listedWt ch.G (.grid D.R.m D.R.m)) ch.G.sp.topDec.rank.symm (wt ch.G (.top D.R.m)) U V ∈ Set.range D.what₂.embLL := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F _ _ _ t Φ _ U V hU hV
  haveI : CharZero D.what₂.LL := (RingHom.charZero_iff D.what₂.embLL.injective).mpr inferInstance
  exact GlobalTheory.BrRat.brPair_mem_range D.what₂.embLL _ _ _ U V hU hV

end GlobalTheory.RowClaim
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols Separates rowForm)

namespace GlobalTheory.RowTest

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Period

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G)

theorem bplusConv_add {φ φ' : Fn G (.top 0)} {F : Fn G (.grid D.R.m 0)} (h : BplusConv W M φ F)
    (h' : BplusConv W M φ' F) :
    BplusConv W M (φ + φ') F ∧ Bplus W M (φ + φ') F = Bplus W M φ F + Bplus W M φ' F := by
  have e : ∀ x, besInt W (φ + φ') F x = fun n => besInt W φ F x n + besInt W φ' F x n := fun x => funext fun n => by
    simp only [besInt, Pi.add_apply]; ring
  have ei : ∀ x, ∫ n in M.fdN, besInt W (φ + φ') F x n ∂M.νN =
      (∫ n in M.fdN, besInt W φ F x n ∂M.νN) + ∫ n in M.fdN, besInt W φ' F x n ∂M.νN := fun x => by
    rw [e x]; exact integral_add (h.1 x) (h'.1 x)
  refine ⟨⟨fun x => ?_, ?_⟩, ?_⟩
  · rw [e x]; exact (h.1 x).add (h'.1 x)
  · simp only [ei]; exact h.2.add h'.2
  · simp only [Bplus, ei]; exact integral_add h.2 h'.2

theorem bplusConv_smul (c : ℂ) {φ : Fn G (.top 0)} {F : Fn G (.grid D.R.m 0)} (h : BplusConv W M φ F) :
    BplusConv W M (c • φ) F ∧ Bplus W M (c • φ) F = c * Bplus W M φ F := by
  have e : ∀ x, besInt W (c • φ) F x = fun n => c * besInt W φ F x n := fun x => funext fun n => by
    simp only [besInt, Pi.smul_apply, smul_eq_mul]; ring
  have ei : ∀ x, ∫ n in M.fdN, besInt W (c • φ) F x n ∂M.νN = c * ∫ n in M.fdN, besInt W φ F x n ∂M.νN := fun x => by
    rw [e x]; exact integral_const_mul _ _
  refine ⟨⟨fun x => ?_, ?_⟩, ?_⟩
  · rw [e x]; exact (h.1 x).const_mul c
  · simp only [ei]; exact h.2.const_mul c
  · simp only [Bplus, ei]; exact integral_const_mul _ _

theorem bplusConv_zero (F : Fn G (.grid D.R.m 0)) : BplusConv W M 0 F ∧ Bplus W M 0 F = 0 := by
  have e : ∀ x, besInt W (0 : Fn G (.top 0)) F x = fun _ => 0 := fun x => funext fun n => by simp [besInt]
  refine ⟨⟨fun x => by rw [e x]; exact integrableOn_zero, ?_⟩, ?_⟩
  · simp only [e, integral_zero]; exact integrableOn_zero
  · simp only [Bplus, e, integral_zero]

end Period

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}



theorem inj_of_separates {ch : Choice R} (hIs : ch.Is) (hM : R.IsModels) {ρ : ch.G.RealVec}
    {ξ : Module.Dual ℂ (coefPlus ch.G ch.W.θ).W} (hsep : Separates R ch.W ch.M ch.w ρ ξ)
    (hconv : ∀ a u, ConvK (ch.withReal ρ ξ) a u) (u : R.HE.H) (hu : ∀ a, psiK ch a u = 0) : u = 0 := by
  have hu' : ∀ a, psiK (ch.withReal ρ ξ) a u = 0 := fun a => hIs.real u hu ρ ξ a
  by_contra h0
  have hmem : R.HE.e u ∈ R.EEat R.triv := hM.HE.2.1 ▸ LinearMap.mem_range_self _ u
  have hne : R.HE.e u ≠ 0 := fun h => h0 (hM.HE.1 (h.trans (map_zero _).symm))
  obtain ⟨Ψ, hΨ, Φ, -, hf⟩ := hsep _ hmem hne
  apply hf
  rw [← span_col_eq_cols ch Φ] at hΨ
  have key : ∀ x ∈ Submodule.span ℂ (ch.col '' {a | ch.Phi a = Φ}),
      BplusConv ch.W ch.M (pairVec (coefPlus ch.G ch.W.θ) ξ x) (thetaChi ch.W ch.M ρ Φ (rowForm R ch.w (R.HE.e u))) ∧
        Bplus ch.W ch.M (pairVec (coefPlus ch.G ch.W.θ) ξ x) (thetaChi ch.W ch.M ρ Φ (rowForm R ch.w (R.HE.e u))) = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      have ha' : ch.Phi a = Φ := ha
      have h1 : FConv ch.W ch.M ρ ξ (ch.col a) (ch.Phi a) (ch.form u) := hconv a u
      have h2 : fPsiPhi ch.W ch.M ρ ξ (ch.col a) (ch.Phi a) (ch.form u) = 0 := hu' a
      rw [ha'] at h1 h2
      exact ⟨h1.2, h2⟩
    | zero =>
      rw [LinearMap.map_zero (pairVec (coefPlus ch.G ch.W.θ) ξ)]; exact bplusConv_zero ch.W ch.M _
    | add x y _ _ hx hy =>
      rw [LinearMap.map_add (pairVec (coefPlus ch.G ch.W.θ) ξ) x y]
      obtain ⟨hc, he⟩ := bplusConv_add ch.W ch.M hx.1 hy.1
      exact ⟨hc, by rw [he, hx.2, hy.2, add_zero]⟩
    | smul c x _ hx =>
      rw [LinearMap.map_smul (pairVec (coefPlus ch.G ch.W.θ) ξ) c x]
      obtain ⟨hc, he⟩ := bplusConv_smul ch.W ch.M c hx.1
      exact ⟨hc, by rw [he, hx.2, mul_zero]⟩
  exact (key Ψ hΨ).2

theorem injK_of_separates (hS : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate)
    (hL : GlobalTheory.RowClaim.Big fun ch => ∀ ρ ξ a u, ConvK (ch.withReal ρ ξ) a u) : GlobalTheory.RowClaim.InjK := by
  obtain ⟨C1, hL⟩ := hL
  refine ⟨max 6510 C1, fun ε CF hCF => ?_⟩
  obtain ⟨x1, hS⟩ := hS ε CF (le_of_max_le_left hCF)
  obtain ⟨x2, hL⟩ := hL ε CF (le_of_max_le_right hCF)
  refine ⟨max x1 x2, fun D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F hset ch hch hsc u hu => ?_⟩
  have hconv := hL D large₂ hε (le_of_max_le_right hx) Γ Pl0 T A Ks R F hset ch hch hsc
  obtain ⟨sc, G, W, M, ρ0, ξ0, cv, rm, S, rp, n, e, c⟩ := ch
  change sc = _ at hsc
  subst hsc
  obtain ⟨ρ, ξ, hsep⟩ := hS D large₂ hε (le_of_max_le_left hx) hset.size hset.eser Γ Pl0 T A Ks R hset.core.lev hset.grp G W
    hch.weil M hch.vol _ hch.w_ne
  exact inj_of_separates hch hset.core.models hsep (hconv ρ ξ) u hu

end GlobalTheory.RowTest

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_rational_image_rationalPoint_mulVec : ∀ (D : D7) (V : HSp D) (γ : GA D V), γ ∈ GQ V → ∀ y : Fin V.rank → D.host.E, ∃ z : Fin V.rank → D.host.E, mt V γ *ᵥ ratV y = ratV z := by
  first | exact @GlobalTheory.SepPer.ratPt_mulVec_ratV | exact GlobalTheory.SepPer.ratPt_mulVec_ratV | (intros; apply GlobalTheory.SepPer.ratPt_mulVec_ratV <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.principalCongruence_mem_latticeCongruenceLevel : ∀ (D : D7) (V : HSp D) (fr : Formalism.IndefR.Eqv.UI.Frames D V) (g : ℕ), 1 ≤ g → ∀ k ∈ (Formalism.IndefR.Eqv.UI.instV fr).Kg g, Formalism.IndefR.Eqv.UI.brg fr (1, k) ∈ Formalism.IndefR.Lev.levA V (congLev D.sp.cm V.gram fr.Λ (Ideal.span {((g : ℕ) : 𝓞 D.host.E)})) := by
  first | exact @GlobalTheory.CongLevelInst.kg_mem_levA | exact GlobalTheory.CongLevelInst.kg_mem_levA | (intros; apply GlobalTheory.CongLevelInst.kg_mem_levA <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SwapWeil

variable {D : D7}

theorem symplOH_of {A B C E : HSp D} (e : WO A B → WO C E) (h : ∀ x y, symplO C E (e x) (e y) = symplO A B x y)
    (x y : WO A B) : symplOH C E (e x) (e y) = symplOH A B x y := by
  simp only [symplOH, h]

theorem theta_pull {ψ : AddChar (AF D.host.F) ℂ} {A B C E : HSp D} (e : WO A B ≃ₗ[AE D] WO C E) (hc : Continuous e)
    (hrat : ∀ x, x ∈ ratL B A → e x ∈ ratL E C) (hs : ∀ x y, symplO C E (e x) (e y) = symplO A B x y)
    (hinf : ∀ x : WO A B, x.map (infPart D) = 0 → (e x).map (infPart D) = 0)
    (hfin : ∀ x : WO A B, x.map (finPart D) = 0 → (e x).map (finPart D) = 0)
    {f : WO C E → ℂ} (hf : IsThetaFunO ψ C E f) : IsThetaFunO ψ A B (fun w => f (e w)) := {
  quasi γ w := by
    obtain ⟨γ', hγ'⟩ := hrat (ratW B A γ) ⟨γ, rfl⟩
    have e1 : e (ratW B A γ) = ratW E C γ' := hγ'.symm
    show f (e (ratW B A γ + w)) = _
    rw [map_add (f := _), e1, hf.quasi, ← e1, symplOH_of (⇑e) hs]
  level := by
    obtain ⟨U, hU, k⟩ := hf.level
    refine ⟨U.comap (e : WO A B →+ WO C E), hU.preimage hc, fun u hu h0 => ?_⟩
    funext w
    have := congrFun (k (e u) hu (hinf u h0)) (e w)
    simp only [heisO] at this ⊢
    rw [map_add (f := _), ← symplOH_of (⇑e) hs]
    exact this
  cont := hf.cont.comp hc
  smooth k L hL h0 w := by
    have := hf.smooth k ((e : WO A B →+ WO C E).comp L) (hc.comp hL) (fun t => hfin _ (h0 t)) (e w)
    simpa only [AddMonoidHom.comp_apply, AddMonoidHom.coe_coe, map_add (f := _)] using this }

theorem isDetAt_inv {e : AE D} (he : e * e = e) {V V₂ : HSp D} {g : GA D V} {k : GA D V₂} {x : (AE D)ˣ}
    (hx : IsDetAt e V g x) (hk : (mt V₂ k).det = (mt V g⁻¹).det) : IsDetAt e V₂ k x⁻¹ := by
  unfold IsDetAt at hx
  have hd : (mt V g⁻¹).det * (mt V g).det = 1 := by
    have hm : mt V g⁻¹ * mt V g = 1 := by simp [Formalism.L2.Theta.mt]
    rw [← Matrix.det_mul, hm, Matrix.det_one]
  show ((x⁻¹ : (AE D)ˣ) : AE D) = e * (mt V₂ k).det + (1 - e)
  rw [hk]
  apply Units.inv_eq_of_mul_eq_one_left
  rw [hx]
  linear_combination e * hd + ((mt V g⁻¹).det * (mt V g).det - (mt V g⁻¹).det - (mt V g).det + 1) * he

def swapOm {S T S' T' : HSp D} (L : WO S' T' ≃ₗ[AE D] WO S T) (φ : GA D S' →* GA D T) (φ' : GA D T' →* GA D S)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : GA D S' × GA D T' →* Module.End ℂ (WO S' T' → ℂ) where
  toFun p :=
    { toFun := fun F w => om (φ' p.2, φ p.1) (fun x => F (L.symm x)) (L w)
      map_add' := fun F G => by
        funext w
        have e : (fun x => (F + G) (L.symm x)) = (fun x => F (L.symm x)) + fun x => G (L.symm x) := rfl
        show om _ (fun x => (F + G) _) _ = om _ (fun x => F _) _ + om _ (fun x => G _) _
        rw [e, map_add (f := _)]; rfl
      map_smul' := fun c F => by
        funext w
        have e : (fun x => (c • F) (L.symm x)) = c • fun x => F (L.symm x) := rfl
        show om _ (fun x => (c • F) _) _ = c • om _ (fun x => F _) _
        rw [e, map_smul]; rfl }
  map_one' := by
    refine LinearMap.ext fun F => funext fun w => ?_
    have e : ((φ' (1 : GA D S' × GA D T').2, φ (1 : GA D S' × GA D T').1) : GA D S × GA D T) = 1 := by
      simp
    simp only [LinearMap.coe_mk, AddHom.coe_mk, e, map_one, Module.End.one_apply, LinearEquiv.symm_apply_apply]
  map_mul' p q := by
    refine LinearMap.ext fun F => funext fun w => ?_
    have e : ((φ' (p * q).2, φ (p * q).1) : GA D S × GA D T) = (φ' p.2, φ p.1) * (φ' q.2, φ q.1) := by
      simp
    simp only [LinearMap.coe_mk, AddHom.coe_mk, e, map_mul, Module.End.mul_apply, LinearEquiv.apply_symm_apply]

theorem swapOm_apply {S T S' T' : HSp D} (L : WO S' T' ≃ₗ[AE D] WO S T) (φ : GA D S' →* GA D T)
    (φ' : GA D T' →* GA D S) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (g : GA D S') (h : GA D T')
    (F : WO S' T' → ℂ) : swapOm L φ φ' om (g, h) F = fun w => om (φ' h, φ g) (fun x => F (L.symm x)) (L w) :=
  rfl

end GlobalTheory.SwapWeil



open GlobalTheory.SwapWeil in
theorem GlobalTheory.SwapWeil.isWeilDatumO_swap : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T S' T' : HSp D), S'.rank = T.rank → T'.rank = S.rank →
    ∀ (L : WO S' T' ≃ₗ[AE D] WO S T) (φ : GA D S' →* GA D T) (φ' : GA D T' →* GA D S),
    Continuous L → Continuous L.symm → (∀ x, L x ∈ ratL T S ↔ x ∈ ratL T' S') →
    (∀ x y, symplO S T (L x) (L y) = symplO S' T' x y) →
    (∀ x, (L x).map (infPart D) = 0 ↔ x.map (infPart D) = 0) → (∀ x, (L x).map (finPart D) = 0 ↔ x.map (finPart D) = 0) →
    Continuous φ → Continuous φ' → (∀ γ ∈ GQ S', φ γ ∈ GQ T) → (∀ γ ∈ GQ T', φ' γ ∈ GQ S) →
    (∀ g h x, L (actO S' T' g h x) = actO S T (φ' h) (φ g) (L x)) →
    (∀ e g, SuppAt e S' g → SuppAt e T (φ g)) → (∀ e h, SuppAt e T' h → SuppAt e S (φ' h)) →
    (∀ g, (Formalism.L2.Theta.mt T (φ g)).det = (Formalism.L2.Theta.mt S' g⁻¹).det) → (∀ h, (Formalism.L2.Theta.mt S (φ' h)).det = (Formalism.L2.Theta.mt T' h⁻¹).det) →
    ∀ (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT ω →
      ∃ ω' : GA D S' × GA D T' →* Module.End ℂ (WO S' T' → ℂ), IsWeilDatumO ψ S' T' χT χS ω' ∧
        ∀ g h (f : WO S T → ℂ), ω' (g, h) (fun u => f (L u)) = fun u => ω (φ' h, φ g) f (L u) := by
  intro D ψ S T S' T' hST hTS L φ φ' hLc hLsc hrat hs hinf hfin hφ hφ' hGQ hGQ' hact hsupp hsupp' hdet hdet' χS χT om H
  have hs' : ∀ x y, symplO S' T' (L.symm x) (L.symm y) = symplO S T x y := fun x y => by
    rw [← hs, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have thL : ∀ G : WO S T → ℂ, IsThetaFunO ψ S T G → IsThetaFunO ψ S' T' (fun w => G (L w)) := fun G hG =>
    theta_pull L hLc (fun x hx => (hrat x).2 hx) hs (fun x hx => (hinf x).2 hx) (fun x hx => (hfin x).2 hx) hG
  have thLs : ∀ F : WO S' T' → ℂ, IsThetaFunO ψ S' T' F → IsThetaFunO ψ S T (fun x => F (L.symm x)) := fun F hF =>
    theta_pull L.symm hLsc (fun x hx => (hrat (L.symm x)).1 (by rwa [LinearEquiv.apply_symm_apply])) hs'
      (fun x hx => (hinf (L.symm x)).1 (by rwa [LinearEquiv.apply_symm_apply]))
      (fun x hx => (hfin (L.symm x)).1 (by rwa [LinearEquiv.apply_symm_apply])) hF
  have hratS : ∀ x, L.symm.toAddEquiv x ∈ ratL T' S' ↔ x ∈ ratL T S := fun x => by
    show L.symm x ∈ ratL T' S' ↔ x ∈ ratL T S
    rw [← hrat, LinearEquiv.apply_symm_apply]
  refine ⟨swapOm L φ φ' om, ⟨H.std, H.hecT, H.hecS, by rw [hST]; exact H.resT, by rw [hTS]; exact H.resS,
    fun p F hF => ?_, fun g h w₀ F hF => ?_, fun γ hγ γ' hγ' F hF => ?_, fun F hF w => ?_,
    fun μ 𝓕 hμ h𝓕 p F hF => ?_, fun e he g h hg hh x y hx hy => ?_⟩, fun g h f => ?_⟩
  · obtain ⟨g, h⟩ := p
    exact thL _ (H.om_pres _ _ (thLs F hF))
  · have e1 : (fun x => heisO ψ S' T' w₀ F (L.symm x)) = heisO ψ S T (L w₀) (fun x => F (L.symm x)) := by
      funext x
      simp only [heisO]
      rw [← symplOH_of (⇑L) hs (L.symm x) w₀, LinearEquiv.apply_symm_apply, map_add (f := _), LinearEquiv.symm_apply_apply]
    funext w
    show om (φ' h, φ g) (fun x => heisO ψ S' T' w₀ F (L.symm x)) (L w) =
      heisO ψ S' T' (actO S' T' g h w₀) (swapOm L φ φ' om (g, h) F) w
    rw [e1, H.om_heis _ _ _ _ (thLs F hF), ← hact]
    simp only [heisO, swapOm_apply, map_add (f := _), symplOH_of (⇑L) hs]
  · show om (φ' γ', φ γ) (fun x => F (L.symm x)) (L 0) = F 0
    rw [L.map_zero, H.om_aut _ (hGQ' γ' hγ') _ (hGQ γ hγ) _ (thLs F hF)]
    exact congrArg F L.symm.map_zero
  · exact (H.om_cont _ (thLs F hF) (L w)).comp ((hφ'.comp continuous_snd).prodMk (hφ.comp continuous_fst))
  · haveI : BorelSpace (WO S T) := ⟨rfl⟩
    haveI : BorelSpace (WO S' T') := ⟨rfl⟩
    obtain ⟨ν, hν, h𝓖, hu⟩ := GlobalTheory.WeilSrc.haar_pull L.symm.toAddEquiv hLsc hLc (ratL T S) (ratL T' S') hratS μ 𝓕 hμ h𝓕
    have e1 := hu fun w => ‖swapOm L φ φ' om p F w‖ₑ ^ 2
    have e2 := hu fun w => ‖F w‖ₑ ^ 2
    have e3 : ∀ x, swapOm L φ φ' om p F (L.symm.toAddEquiv x) = om (φ' p.2, φ p.1) (fun x => F (L.symm x)) x :=
      fun x => by
        show om _ _ (L (L.symm x)) = _
        rw [LinearEquiv.apply_symm_apply]
    simp only [e3] at e1
    rw [← e1, ← e2]
    exact H.om_unit ν _ hν h𝓖 _ _ (thLs F hF)
  · obtain ⟨r, hr, Hs⟩ := H.om_split e he (φ' h) (φ g) (hsupp' e h hh) (hsupp e g hg) y⁻¹ x⁻¹
      (isDetAt_inv he.1 hy (hdet' h)) (isDetAt_inv he.1 hx (hdet g))
    refine ⟨r, hr, fun ℓ hℓ F hF => ?_⟩
    let ℓ' : (WO S T → ℂ) →ₗ[ℂ] ℂ := ℓ ∘ₗ LinearMap.funLeft ℂ ℂ L
    have hinv : ∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ G, IsThetaFunO ψ S T G →
        ℓ' (heisO ψ S T u G) = ℓ' G := by
      intro u hu G hG
      show ℓ (fun w => heisO ψ S T u G (L w)) = ℓ (fun w => G (L w))
      have e1 : (fun w => heisO ψ S T u G (L w)) = heisO ψ S' T' (L.symm u) (fun w => G (L w)) := by
        funext w
        simp only [heisO]
        rw [← symplOH_of (⇑L) hs w (L.symm u), map_add (f := _), LinearEquiv.apply_symm_apply]
      rw [e1]
      refine hℓ _ ?_ _ (thL G hG)
      have hu' : cA D e • u = u := by
        ext i j
        exact hu i j
      intro i j
      have k := congrArg (fun M : WO S' T' => M i j) (congrArg L.symm hu')
      simpa only [LinearEquiv.map_smul, Matrix.smul_apply, smul_eq_mul] using k
    have main := Hs ℓ' hinv _ (thLs F hF)
    have e1 : ℓ' (fun x => F (L.symm x)) = ℓ F := by
      show ℓ (fun w => F (L.symm (L w))) = ℓ F
      simp only [LinearEquiv.symm_apply_apply]
    have hfac : splitFacO χS χT y⁻¹ x⁻¹ = splitFacO χT χS x y := by
      unfold splitFacO
      rw [map_inv, map_inv, inv_inv, mul_comm]
    rw [e1, hfac] at main
    exact main
  · funext u
    show om _ (fun x => f (L (L.symm x))) _ = _
    simp only [LinearEquiv.apply_symm_apply]
end
end
