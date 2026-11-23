module

public import Formalism.LocalToGlobal.IndefiniteReal.Bundle008
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.Divisibility.ClassSumLemmas
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
public import Formalism.LocalToGlobal.Divisibility.InertPartitionLePartF
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.BridgeLemmas
import Formalism.LocalToGlobal.IndefiniteReal.CxCutPO
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle011
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.CommutingTwist
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.RatHerm
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle025
public import Mathlib.Topology.Sheaves.Presheaf
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle019
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle003
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle007
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
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
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

noncomputable section

namespace GlobalTheory.Div

open scoped ComplexOrder


open Formalism.IndefR.Cx.GroupActionMatrices Formalism.IndefR.Cx.EigenprojectionMatrices Formalism.IndefR.Cx.OrthogonalPartDecomposition Formalism.L2.DIV.CyclotomicLifting in
theorem csum_eigSum_orth {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I : Type}
    {B : BlockDat K G Pl0} {ℓ : Lvl K G} {v : InfinitePlace K} {s : ℕ} {op : I → Module.End K B.S.Forms}
    (h : BlockHyp B ℓ v s) (hO : OkOp B op) {C C' : (I → K) → Prop} (hCC : ∀ x, C' x → ¬ C x) {f g : B.S.Forms}
    (hf : f ∈ Formalism.L2.Col.eigSum op C) (hg : g ∈ Formalism.L2.Col.eigSum op C') :
    B.S.csum (f : B.S.Cl → B.S.V) (g : B.S.Cl → B.S.V) = 0 := by
  classical
  have hA : (B.S.H.map v.embedding).PosDef := h.ok.hpos v
  have hHh : B.S.Hᴴ = B.S.H := FinitelyNonzeroLinear.herm_of_pos h.conj (h.ok.hpos v)
  have hadj : ∀ i, ∃ i', B.S.H.map v.embedding * (oM B op i).map v.embedding =
      ((oM B op i').map v.embedding)ᴴ * B.S.H.map v.embedding := by
    intro i
    obtain ⟨i', hi'⟩ := oM_adj hO i
    have h2 : B.S.H * oM B op i = (oM B op i')ᴴ * B.S.H := by
      have := congrArg Matrix.conjTranspose hi'
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hHh] at this
      exact this
    refine ⟨i', ?_⟩
    rw [← Matrix.map_mul, h2, Matrix.map_mul, map_conjTranspose_of_mem_cmMax v.embedding _ (hO.rat i')]
  have hc : Formalism.L2.Col.PairComm (linF fun i => (oM B op i).map v.embedding) := fun i j =>
    linF_commute (by rw [← Matrix.map_mul, ← Matrix.map_mul, oM_comm hO.comm])
  have hs : Formalism.L2.Col.SplitOver (linF fun i => (oM B op i).map v.embedding) := fun i =>
    Module.End.iSup_maxGenEigenspace_eq_top _
  have hmem : ∀ {S : (I → K) → Prop} {z : B.S.Forms}, z ∈ Formalism.L2.Col.eigSum op S →
      (fun a => v.embedding (B.S.basis.equivFun z a)) ∈ Formalism.L2.Col.eigSum (linF fun i => (oM B op i).map v.embedding)
        (fun w => ∃ x, S x ∧ w = fun i => v.embedding (x i)) := by
    intro S z hz
    have h1 : B.S.basis.equivFun z ∈ Formalism.L2.Col.eigSum (fun i => Matrix.toLin' (oM B op i)) S := by
      have := eigSum_le_comap_of (B.S.basis.equivFun : B.S.Forms →ₗ[K] (Fin B.S.dim → K)) op
        (fun i => Matrix.toLin' (oM B op i)) (fun i f => by rw [Matrix.toLin'_apply]; exact equivFun_oM i f) _ hz
      simpa [Submodule.mem_comap] using this
    exact emb_mem_eigSum v.embedding (oM B op) S h1
  have hCC' : ∀ w, (fun w => ∃ x, C' x ∧ w = fun i => v.embedding (x i)) w →
      ¬ (fun w => ∃ x, C x ∧ w = fun i => v.embedding (x i)) w := by
    rintro w ⟨x', hx', rfl⟩ ⟨x, hx, e⟩
    have : x' = x := funext fun i => v.embedding.injective (by simpa using congrFun e i)
    subst this
    exact hCC x' hx' hx
  have key := cx_eig_orth (fun i => (oM B op i).map v.embedding) (B.S.H.map v.embedding) hA hadj hc hs hCC' (hmem hf) (hmem hg)
  have hform0 : hform B.S.H (B.S.basis.equivFun f) (B.S.basis.equivFun g) = 0 := by
    apply v.embedding.injective
    rw [map_zero, ← key, RationalHermitianForm.hform_eq_dot, ← emb_mulVec v.embedding B.S.H]

    simp only [dotProduct, map_sum, map_mul, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h.conj]
    rfl
  rw [hform_eq_csum, CSD.I_apply, CSD.I_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply] at hform0
  exact hform0

end GlobalTheory.Div

namespace GlobalTheory.Div



theorem inner_jX_csum {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hM : R.IsModels) (t : A.fam.base.Tup)
    (x y : (A.fam.R t).S.Forms) :
    Formalism.IndefR.Links.cj (twAt D.what₂.embLL A.v0) (inner ℂ (R.jX t x) (R.jX t y)) =
      A.v0.embedding ((A.fam.R t).S.csum ((x : (A.fam.R t).S.Forms) : (A.fam.R t).S.Cl → (A.fam.R t).S.V)
        ((y : (A.fam.R t).S.Forms) : (A.fam.R t).S.Cl → (A.fam.R t).S.V)) := by
  rw [(hM.HX t).2.2, hM.jX, hM.jX, R.emb0]
  congr 1
  exact Formalism.IndefR.Bridge.ClassPres.isom_holds (R.B.R t).pres x y

theorem inner_jX_zero {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hM : R.IsModels) (t : A.fam.base.Tup)
    (x y : (A.fam.R t).S.Forms)
    (h : (A.fam.R t).S.csum ((x : (A.fam.R t).S.Forms) : (A.fam.R t).S.Cl → (A.fam.R t).S.V)
        ((y : (A.fam.R t).S.Forms) : (A.fam.R t).S.Cl → (A.fam.R t).S.V) = 0) :
    inner ℂ (R.jX t x) (R.jX t y) = 0 := by
  have key := inner_jX_csum R hM t x y
  have h1 : Formalism.IndefR.Links.cj (twAt D.what₂.embLL A.v0) (inner ℂ (R.jX t x) (R.jX t y)) = 0 :=
    key.trans ((congrArg (⇑A.v0.embedding) h).trans (map_zero A.v0.embedding))
  exact (map_eq_zero (Formalism.IndefR.Links.cj (twAt D.what₂.embLL A.v0))).1 h1

end GlobalTheory.Div


theorem GlobalTheory.Div.parts_orth_complex : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → ∀ p q : A3.fam3.base3.Ix, p ≠ q → ∀ x ∈ Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms)), ∀ y ∈ Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum q.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms)), ⟪x, y⟫_ℂ = 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hC hH p q hpq x hx y hy
  have hok := hOk.ok2.what₂ A3.A.μ0
  have hO := okOp_opAll hok (hOk.what₂ A3.A.μ0) (hH A3.A.μ0).1 (hH A3.A.μ0).2
  have hSS : ∀ z, (A3.rowI A3.A.μ0).HasRes3 q.1 z → ¬ (A3.rowI A3.A.μ0).HasRes3 p.1 z := fun z hq =>
    (A3.rowI A3.A.μ0).excl3 ((A3.rowI A3.A.μ0).diffAt_of_mem_ixFin3 q.2 p.2 fun e => hpq (Subtype.ext e).symm) z hq
  have hblk : BlockHyp (A3.A.fam.R A3.A.μ0) (A3.A.fam.lvl F.P0 F.ψ0) A3.A.fam.v0 s := ⟨hOk.ok2.conj, hOk.ok2.irr, hok⟩
  have hgen : ∀ f ∈ (A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1, ∀ g ∈ (A3.rowI A3.A.μ0).inertTypeEigenspaceSum q.1,
      ⟪R.jX A3.A.μ0 f, R.jX A3.A.μ0 g⟫_ℂ = 0 := by
    intro f hf g hg
    have h0 := GlobalTheory.Div.csum_eigSum_orth hblk hO hSS hf hg
    exact GlobalTheory.Div.inner_jX_zero R.toRealDat hC.base.models A3.A.μ0 f g h0
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨f, hf, rfl⟩ := ha
    induction hy using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨g, hg, rfl⟩ := hb
      exact hgen f hf g hg
    | zero => simp
    | add u w _ _ hu hw => rw [inner_add_right, hu, hw, add_zero]
    | smul c u _ hu => rw [inner_smul_right, hu, mul_zero]
  | zero => simp
  | add u w _ _ hu hw => rw [inner_add_left, hu, hw, add_zero]
  | smul c u _ hu => rw [inner_smul_left, hu, mul_zero]
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem lift_mem_levVP : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (i : Fin D.R.m) (t : T) (P : LevelP R.Pg D.R.r ℂ) (g0 : P.H) (κ : GA D (Vc D i)), IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0.1 κ → κ ∈ levG (Vc D i) (R.βV i) (RecTie.datVP R i t P) ∧ levChi (Vc D i) (R.βV i) (RecTie.datVP R i t P) κ = ((P.chi g0 : ℂˣ) : ℂ)⁻¹ * levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i t P g0 κ hκ
  obtain ⟨hG, hpar, hr⟩ := hκ
  have hrt : Formalism.L2.DIV.rTup (R.βV i) (RecTie.datVP R i t P) (finE (Vc D i) κ) = g0.1 := hr
  have hmem : finE (Vc D i) κ ∈ Formalism.L2.DIV.lev D.sp.cm (Vc D i).gram (R.βV i) (RecTie.datVP R i t P) := by
    refine ⟨hpar, ?_⟩
    rw [hrt]; exact g0.2
  refine ⟨⟨hG, hmem⟩, ?_⟩
  have e1 : Formalism.L2.DIV.ext1 (RecTie.datVP R i t P).P.H (RecTie.datVP R i t P).P.chi
      (Formalism.L2.DIV.rTup (R.βV i) (RecTie.datVP R i t P) (finE (Vc D i) κ)) = (P.chi g0)⁻¹ := by
    rw [Formalism.L2.DIV.extendOne_of_mem _ hmem.2]
    simp only [hrt]
    rfl
  have e2 : Formalism.L2.DIV.ext1 (flagL (R.datVt i t)).P.H (flagL (R.datVt i t)).P.chi
      (Formalism.L2.DIV.rTup (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) κ)) = 1 := by
    rw [Formalism.L2.DIV.extendOne_of_mem _ (show Formalism.L2.DIV.rTup (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) κ) ∈ (flagL (R.datVt i t)).P.H from Subgroup.mem_top _)]
    rfl
  have key : Formalism.L2.DIV.levFn (R.βV i) (RecTie.datVP R i t P) (finE (Vc D i) κ) =
      (P.chi g0)⁻¹ * Formalism.L2.DIV.levFn (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) κ) := by
    unfold Formalism.L2.DIV.levFn
    rw [e1, e2, one_mul, mul_assoc]
    rfl
  show ((Formalism.L2.DIV.levFn (R.βV i) (RecTie.datVP R i t P) (finE (Vc D i) κ) : ℂˣ) : ℂ) = _
  rw [key, Units.val_mul, Units.val_inv_eq_inv_val]
  rfl

end GlobalTheory
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.ThetaPRead

theorem isThetaP_restrict {G' H' S' Si Tau Y ι : Type} [MeasurableSpace H'] [AddCommGroup Si] [Module ℂ Si]
    [AddCommGroup Tau] [Module ℂ Tau] [AddCommGroup Y] [Module ℂ Y]
    {M : ι → Type} [∀ ρ, AddCommGroup (M ρ)] [∀ ρ, Module ℂ (M ρ)] (low : ∀ ρ, Submodule ℂ (M ρ))
    {ν : Measure H'} {𝓕 : Set H'} {th : G' → H' → S' → ℂ} {pt : Si → S'}
    {io : (⨂[ℂ] ρ, low ρ) →ₗ[ℂ] Tau →ₗ[ℂ] Si} (L : Y →ₗ[ℂ] (H' → Tau)) (hL : Function.Injective L)
    (S : Submodule ℂ (H' → Tau)) (U : Y →ₗ[ℂ] ((∀ ρ, M ρ) →ₘₗ[ℂ] (G' → ℂ)))
    (h : ∃ thP, Lift.IsThetaP ν 𝓕 th pt io (LinearMap.range L) thP ∧
      ∀ x (v : ∀ ρ, low ρ), U x (fun ρ => v ρ) = thP (L.rangeRestrict x) (PiTensorProduct.tprod ℂ v)) :
    Lift.IsThetaP ν 𝓕 th pt io (LinearMap.range L ⊓ S)
      (LinearMap.lcomp ℂ (G' → ℂ) (PiTensorProduct.map fun ρ => (low ρ).subtype) ∘ₗ
        (PiTensorProduct.lift : ((∀ ρ, M ρ) →ₘₗ[ℂ] (G' → ℂ)) ≃ₗ[ℂ] _).toLinearMap ∘ₗ U ∘ₗ
        (LinearEquiv.ofInjective L hL).symm.toLinearMap ∘ₗ Submodule.inclusion inf_le_left) := by
  obtain ⟨thP, hP, hv⟩ := h
  have key : ∀ f : ↥(LinearMap.range L ⊓ S),
      (LinearMap.lcomp ℂ (G' → ℂ) (PiTensorProduct.map fun ρ => (low ρ).subtype) ∘ₗ
        (PiTensorProduct.lift : ((∀ ρ, M ρ) →ₘₗ[ℂ] (G' → ℂ)) ≃ₗ[ℂ] _).toLinearMap ∘ₗ U ∘ₗ
        (LinearEquiv.ofInjective L hL).symm.toLinearMap ∘ₗ Submodule.inclusion inf_le_left) f =
        thP (Submodule.inclusion inf_le_left f) := by
    intro f
    set x := (LinearEquiv.ofInjective L hL).symm (Submodule.inclusion inf_le_left f) with hx
    have h1 : L.rangeRestrict x = Submodule.inclusion inf_le_left f := by
      have := LinearEquiv.apply_symm_apply (LinearEquiv.ofInjective L hL) (Submodule.inclusion inf_le_left f)
      rw [← hx] at this
      rw [← this]
      rfl
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.lcomp_apply, LinearEquiv.coe_coe, PiTensorProduct.map_tprod, Submodule.coe_subtype,
      PiTensorProduct.lift.tprod]
    rw [← hx, hv x v, h1]
  refine ⟨fun f e g => ?_, fun f e g => ?_⟩
  · exact hP.integ (Submodule.inclusion inf_le_left f) e g
  · rw [key f]
    exact hP.eq _ e g

theorem isThetaP_toLiftReal : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : RecTie.TopMultH R) (hinj : ∀ i t, Function.Injective (R.extV i t)), R.thP_thF → ∀ μ i, Lift.IsThetaP ((RecTie.toLiftReal R F tupT hm hTop hinj).measV μ i) ((RecTie.toLiftReal R F tupT hm hTop hinj).fdV μ i) ((RecTie.toLiftReal R F tupT hm hTop hinj).thW μ i) ((RecTie.toLiftReal R F tupT hm hTop hinj).ptW μ i) ((RecTie.toLiftReal R F tupT hm hTop hinj).ioK i) ((RecTie.toLiftReal R F tupT hm hTop hinj).Amt μ i) ((RecTie.toLiftReal R F tupT hm hTop hinj).thC μ i) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F tupT hm hTop hinj h μ i
  exact isThetaP_restrict _ _ _ _ _ (h i (tupT μ))

end GlobalTheory.ThetaPRead
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.SymplSkew

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem herm_inv {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) (a b : Fin n) :
    σ (J⁻¹ b a) = J⁻¹ a b := by
  have hmap : J.map σ = Jᵀ := by ext i j; simp [Matrix.transpose_apply, hJ.1 j i]
  have hu : IsUnit J.det := isUnit_iff_ne_zero.mpr hJ.2
  have h1 : (J⁻¹).map σ * J.map σ = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu]; simp
  have h2 : (J⁻¹).map σ = (J⁻¹)ᵀ := by
    rw [Matrix.transpose_nonsing_inv, ← hmap]; exact (Matrix.inv_eq_left_inv h1).symm
  have := congrFun (congrFun h2 b) a
  rw [Matrix.map_apply] at this
  rw [this, Matrix.transpose_apply]

noncomputable def cEquiv (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) : AEF F E ≃ₐ[AF F] AEF F E :=
  Algebra.TensorProduct.congr (AlgEquiv.refl) (AlgEquiv.ofAlgHom σ σ (AlgHom.ext fun e => hσ e) (AlgHom.ext fun e => hσ e))

theorem cEquiv_apply (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (z : AEF F E) : cEquiv σ hσ z = cAF σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem cAF_cAF (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (z : AEF F E) : cAF σ (cAF σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    show (Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ) ((Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ) (a ⊗ₜ e)) = a ⊗ₜ e
    simp [hσ]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem cAF_incAF (σ : E →ₐ[F] E) (e : E) : cAF σ (incAF F E e) = incAF F E (σ e) := by
  show (Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ) ((1 : AF F) ⊗ₜ e) = (1 : AF F) ⊗ₜ σ e
  simp

theorem cAF_hOF (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E}
    {JT : Matrix (Fin nT) (Fin nT) E} (hS : IsHermND σ JS) (hT : IsHermND σ JT) (x y : WOF F E nS nT) :
    cAF σ (hOF σ JS JT x y) = hOF σ JS JT y x := by
  unfold hOF

  simp only [map_sum, map_mul, cAF_incAF, cAF_cAF σ hσ, herm_inv hS, hT.1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  ring

theorem symplOF_swap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    (∀ e, σ (σ e) = e) → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
    IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, σ ξ₀ = -ξ₀ → ∀ x y : WOF F E nS nT,
      symplOF σ JS JT ξ₀ y x = -symplOF σ JS JT ξ₀ x y := by
  intro F E _ _ _ _ _ σ hσ nS nT JS JT hS hT ξ₀ hξ x y
  unfold symplOF
  have hx : incAF F E ξ₀ = cAF σ (incAF F E (-ξ₀)) := by rw [cAF_incAF, ← hξ, hσ]
  rw [← cAF_hOF σ hσ hS hT x y]
  have key : incAF F E ξ₀ * cAF σ (hOF σ JS JT x y) = cEquiv σ hσ (incAF F E (-ξ₀) * hOF σ JS JT x y) := by
    rw [cEquiv_apply, map_mul, ← hx]
  rw [key, Algebra.trace_eq_of_algEquiv, map_neg, neg_mul, map_neg]

end GlobalTheory.SymplSkew
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.AdelicMatrixLatticeF

theorem lattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT : ℕ),
    IsTopologicalAddGroup (WOF F E nS nT) ∧ LocallyCompactSpace (WOF F E nS nT) ∧
    SecondCountableTopology (WOF F E nS nT) ∧ T2Space (WOF F E nS nT) ∧ DiscreteTopology (ratLF F E nS nT) ∧
    ∃ K : Set (WOF F E nS nT), IsCompact K ∧ ∀ x : WOF F E nS nT, ∃ γ ∈ ratLF F E nS nT, γ + x ∈ K := by
  intro F E _ _ _ _ _ nS nT
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele _
  have : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele _
  have : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField _
  have : IsModuleTopology (AF F) (AEF F E) := ⟨rfl⟩
  have : IsTopologicalRing (AEF F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  have : LocallyCompactSpace (AEF F E) := e.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology (AEF F E) := e.secondCountableTopology
  have : T2Space (AEF F E) := e.isEmbedding.t2Space
  have hg : IsTopologicalAddGroup (WOF F E nS nT) :=
    inferInstanceAs (IsTopologicalAddGroup (Fin nT → Fin nS → AEF F E))
  refine ⟨hg, inferInstanceAs (LocallyCompactSpace (Fin nT → Fin nS → AEF F E)),
    inferInstanceAs (SecondCountableTopology (Fin nT → Fin nS → AEF F E)),
    inferInstanceAs (T2Space (Fin nT → Fin nS → AEF F E)), ?_, ?_⟩
  · obtain ⟨U, hU, hx⟩ := GlobalTheory.AdelicMatrixLattice.discrete_tensor (F := F) (E := E) (AF F)
      (GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F)
    have hN : (Set.univ.pi fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => U) ∈
        nhds (0 : WOF F E nS nT) :=
      set_pi_mem_nhds Set.finite_univ fun _ _ => set_pi_mem_nhds Set.finite_univ fun _ _ => hU
    refine discreteTopology_of_isOpen_singleton_zero ?_
    rw [isOpen_singleton_iff_nhds_eq_pure]
    refine le_antisymm (Filter.le_pure_iff.2 ?_) (pure_le_nhds _)
    have hc : ContinuousAt (fun x : ratLF F E nS nT => (x : WOF F E nS nT)) 0 :=
      continuous_subtype_val.continuousAt
    refine Filter.mem_of_superset (hc.preimage_mem_nhds hN) ?_
    rintro ⟨_, y, rfl⟩ hy
    have hy0 : y = 0 := by
      funext i j
      exact hx _ (hy i (Set.mem_univ i) j (Set.mem_univ j))
    subst hy0
    exact Subtype.ext (map_zero _)
  · obtain ⟨K, hK, hx⟩ := GlobalTheory.AdelicMatrixLattice.cocompact_tensor (F := F) (E := E) (AF F)
      (GlobalTheory.AdeleCocompact.exists_compact_adele F)
    choose c hc using hx
    refine ⟨Set.univ.pi fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => K,
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK, fun x => ?_⟩
    exact ⟨_, ⟨Matrix.of fun i j => c (x i j), rfl⟩, fun i _ j _ => hc (x i j)⟩

end GlobalTheory.AdelicMatrixLatticeF
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.TowerFD

theorem exists_fd_any : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT : ℕ),
    ∃ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure ∧
      IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν := by
  intro F E _ _ _ _ _ nS nT
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  have : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  have : LocallyCompactSpace (AF F ⊗[F] E) := e.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology (AF F ⊗[F] E) := e.secondCountableTopology
  have : T2Space (AF F ⊗[F] E) := e.isEmbedding.t2Space
  have : LocallyCompactSpace (WOF F E nS nT) :=
    inferInstanceAs (LocallyCompactSpace (Fin nT → Fin nS → AF F ⊗[F] E))
  have : SecondCountableTopology (WOF F E nS nT) :=
    inferInstanceAs (SecondCountableTopology (Fin nT → Fin nS → AF F ⊗[F] E))
  have : T2Space (WOF F E nS nT) := inferInstanceAs (T2Space (Fin nT → Fin nS → AF F ⊗[F] E))
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  have hdisc : DiscreteTopology (ratLF F E nS nT) := by
    obtain ⟨U, hU, hx⟩ := GlobalTheory.AdelicMatrixLattice.discrete_tensor (F := F) (E := E) (AF F)
      (GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F)
    have hN : (Set.univ.pi fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => U) ∈
        nhds (0 : WOF F E nS nT) :=
      set_pi_mem_nhds Set.finite_univ fun _ _ => set_pi_mem_nhds Set.finite_univ fun _ _ => hU
    refine discreteTopology_of_isOpen_singleton_zero ?_
    rw [isOpen_singleton_iff_nhds_eq_pure]
    refine le_antisymm (Filter.le_pure_iff.2 ?_) (pure_le_nhds _)
    have hc : ContinuousAt (fun x : ratLF F E nS nT => (x : WOF F E nS nT)) 0 :=
      continuous_subtype_val.continuousAt
    refine Filter.mem_of_superset (hc.preimage_mem_nhds hN) ?_
    rintro ⟨_, y, rfl⟩ hy
    have hy0 : y = 0 := by
      funext i j
      exact hx _ (hy i (Set.mem_univ i) j (Set.mem_univ j))
    subst hy0
    exact Subtype.ext (map_zero _)
  obtain ⟨K, hK, hx⟩ := GlobalTheory.AdelicMatrixLattice.cocompact_tensor (F := F) (E := E) (AF F)
    (GlobalTheory.AdeleCocompact.exists_compact_adele F)
  choose c hc using hx
  have hcov : ∀ x : WOF F E nS nT, ∃ γ ∈ ratLF F E nS nT, γ + x ∈
      (Set.univ.pi fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => K) :=
    fun x => ⟨_, ⟨Matrix.of fun i j => c (x i j), rfl⟩, fun i _ j _ => hc (x i j)⟩
  have hKc : IsCompact (Set.univ.pi (fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => K) :
      Set (WOF F E nS nT)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK
  have tZ : IsTopologicalAddGroup (WOF F E nS nT) := inferInstance
  obtain ⟨μ, 𝓕, hμ, h𝓕, -⟩ :=
    (@GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WOF F E nS nT) _ _ tZ _ _ _ _ _ (ratLF F E nS nT) hdisc _
      hKc hcov).1
  exact ⟨μ, 𝓕, hμ, h𝓕⟩

end GlobalTheory.TowerFD
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.FamSep

theorem typesSep_of_ok_isFam : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) {s : ℕ}, A.fam.Ok s → R.IsFam → A.fam.TypesSep :=
  fun {_ _ _ _ _ _ A _ _ _ _} _ _ hOk hF => typesSep_of_ok A hOk fun P => (hF.degR A.μ0 P).1

end GlobalTheory.FamSep
end
