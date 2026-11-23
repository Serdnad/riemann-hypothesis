module

public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHatMxHomLatIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle404
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralMulRightOfCompact
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle293
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle375
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Formalism.LocalToGlobal.IndefiniteReal.Bundle015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle386
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle378
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.HalfScalarHat

open GlobalTheory.FunObj.HatFrame

theorem smul_map_mem_genGrp {D : D7} {m n : ℕ} (M : Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E))
    (𝔪 : Ideal (𝓞 D.host.E)) {g : Matrix (Fin m) (Fin n) D.host.E} (hg : g ∈ M)
    {t : Formalism.L2.Herm.intAf D.host.F D.host.E} (ht : t ∈ Formalism.L2.DIV.idS D.host.F 𝔪) :
    (t : EAf D) • g.map (eToEAf D) ∈ genGrp D.host.F (𝔪 • M) := by
  have hgen : ∀ a ∈ 𝔪, ((Formalism.L2.DIV.oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) •
      g.map (eToEAf D) ∈ genGrp D.host.F (𝔪 • M) := by
    intro a ha
    refine AddSubgroup.subset_closure ⟨1, one_mem _, a • g, Submodule.smul_mem_smul ha hg, ?_⟩
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, Formalism.L2.DIV.oToS_coe, smul_eq_mul, eToEAf,
      Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, Algebra.smul_def]
  have hspan : t ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E)
      ((Formalism.L2.DIV.oToS D.host.F D.host.E) '' (𝔪 : Set (𝓞 D.host.E))) := ht
  clear ht
  induction hspan using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨a, ha, rfl⟩ := hu
    exact hgen a ha
  | zero =>
    simp only [ZeroMemClass.coe_zero, zero_smul]
    exact zero_mem _
  | add u v _ _ hu hv =>
    simp only [AddMemClass.coe_add, add_smul]
    exact add_mem hu hv
  | smul r u _ hu =>
    simp only [smul_eq_mul, MulMemClass.coe_mul, mul_smul]
    exact smul_mem_genGrp _ _ r.2 _ hu

theorem tmul_split {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (x : A ⊗[R] B) (b g : A) (α : B) :
    x * ((b * g) ⊗ₜ[R] α) = x * ((b ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] α)) * (g ⊗ₜ[R] (1 : B)) := by
  simp only [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem v_triple_le {D : D7} {w : HeightOneSpectrum (𝓞 D.host.E)} {s x y z : EAf D} {c : WithZero (Multiplicative ℤ)} (h : s = x * (y * z))
    (hx : GlobalTheory.StdFrames.cpt (D := D) w x = 1) (hy : Valued.v (GlobalTheory.StdFrames.cpt (D := D) w y) ≤ c)
    (hz : Valued.v (GlobalTheory.StdFrames.cpt (D := D) w z) ≤ 1) : Valued.v (GlobalTheory.StdFrames.cpt (D := D) w s) ≤ c := by
  subst h
  rw [map_mul, hx, one_mul, map_mul, map_mul]
  calc Valued.v (GlobalTheory.StdFrames.cpt (D := D) w y) * Valued.v (GlobalTheory.StdFrames.cpt (D := D) w z) ≤ c * 1 :=
        mul_le_mul' hy hz
    _ = c := mul_one c

theorem scalar_mem_idS {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {s x y z : EAf D}
    (h : s = x * (y * z)) (e1 : ∀ w ∈ G.pl.W0, GlobalTheory.StdFrames.cpt (D := D) w x = 1)
    (e2 : ∀ w ∉ G.pl.W0, GlobalTheory.StdFrames.cpt (D := D) w x = 0)
    (hy : ∀ w ∈ G.pl.W0, Valued.v (GlobalTheory.StdFrames.cpt (D := D) w y) ≤ WithZero.exp (-(cosExp G w : ℤ)))
    (hz : z ∈ GlobalTheory.StdFrames.OA D) :
    ∃ t ∈ Formalism.L2.DIV.idS D.host.F G.modul, t.1 = s := by
  have hz' : ∀ w, Valued.v (GlobalTheory.StdFrames.cpt (D := D) w z) ≤ 1 := fun w =>
    (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ((GlobalTheory.StdFrames.mem_OA_iff z).1 hz w)
  have hs : s ∈ GlobalTheory.StdFrames.OA D := by
    rw [GlobalTheory.StdFrames.mem_OA_iff]
    intro w
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    by_cases hw : w ∈ G.pl.W0
    · refine v_triple_le h (e1 w hw) ((hy w hw).trans ?_) (hz' w)
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
    · rw [h, map_mul, e2 w hw, zero_mul, map_zero]
      exact zero_le'
  refine ⟨⟨s, hs⟩, ?_, rfl⟩
  rw [GlobalTheory.FunObj.Comparison₂.mem_idS_modul]
  intro w hw
  exact v_triple_le h (e1 w hw) (hy w hw) (hz' w)

theorem toEAf_pair {D : D7} (α : Formalism.L2.Herm.Af D.host.F) (x : D.host.E) :
    toEAf D (pairA D.host.F 0 α ⊗ₜ[D.host.F] x) = x ⊗ₜ[D.host.F] α := rfl

theorem map_toEAf_smul {D : D7} {m n : ℕ} (e : AE D) (X : Mx D m n) :
    (e • X).map (toEAf D) = toEAf D e • X.map (toEAf D) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

theorem infPart_smul {D : D7} {m n : ℕ} {e : AE D} (he : infPart D e = 0) (X : Mx D m n) (i : Fin m) (j : Fin n) :
    infPart D ((e • X) i j) = 0 := by
  rw [Matrix.smul_apply, smul_eq_mul, map_mul, he, zero_mul]

theorem smul_pair {D : D7} {m n : ℕ} (x : EAf D) (α : Formalism.L2.Herm.Af D.host.F) (b : D.host.E)
    (g : Matrix (Fin m) (Fin n) D.host.E) :
    x • (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (b * g i j) : Mx D m n).map (toEAf D) =
      (x * ((b ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) : EAf D) * ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D))) •
        g.map (eToEAf D) := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, smul_eq_mul, toEAf_pair, eToEAf,
    Algebra.TensorProduct.includeLeftRingHom_apply]
  exact tmul_split _ b (g i j) α

end GlobalTheory.HalfScalarHat

open GlobalTheory.FunObj.HatFrame GlobalTheory.HalfScalarHat in
theorem GlobalTheory.HalfScalarHat.idemSum_smul_mem_hatMx : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {m n : ℕ} (M : Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E)) (e : AE D), IsIdemSum e G.pl.W0 → ∀ α ∈ intAf D.host.F, ∀ b : D.host.E, (∀ w ∈ G.pl.W0, Valued.v (algebraMap D.host.E (Kw w) b) ≤ WithZero.exp (-(cosExp G w : ℤ))) → ∀ g ∈ M, e • (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (b * g i j) : Mx D m n) ∈ hatMx (G.modul • M) := by
  intro D T L sc G m n M e he α hα b hb g hg
  obtain ⟨hinf, h1, h0⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he
  rw [GlobalTheory.FunObj.HatFrame.mem_hatMx_iff]
  refine ⟨fun i j => infPart_smul hinf _ i j, ?_⟩
  rw [map_toEAf_smul, smul_pair]
  have hα' : ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) ∈ GlobalTheory.StdFrames.OA D :=
    Subring.subset_closure (Or.inr ⟨⟨α, fun v => hα v⟩, rfl⟩)
  obtain ⟨t, ht, hts⟩ := scalar_mem_idS G rfl h1 h0
    (fun w hw => by rw [GlobalTheory.FunObj.Comparison₂.cpt_tmul]; exact hb w hw) hα'
  rw [← hts]
  exact smul_map_mem_genGrp M G.modul hg ht
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FirstRowLaw

section Gen
variable {Gg Γg : Type} [Group Gg] [Group Γg] {Wg : Type} [NormedAddCommGroup Wg] [InnerProductSpace ℂ Wg]

theorem adForms_law (ι : Γg →* Gg) (ρ : Γg →* Module.End ℂ Wg) (J : Subgroup Gg) (χ : J →* ℂˣ) {F : Gg → Wg}
    (hF : F ∈ Bridge.AdForms ι ρ J χ) (h : Gg) (k : J) : F (h * k) = (χ k : ℂ) • F h := by
  have e := hF 1 h k
  rwa [map_one, one_mul, map_one, Module.End.one_apply] at e

end Gen

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts}
  {G : GridData R.toLevCh sc} {W : G.Weil} {U : Set T}

theorem cast_mul_unitaryAdelicGroup_of_eq {X Y : LSp D} (h : X = Y) (a b : GA D X.sp) :
    cast (congrArg (fun X : LSp D => GA D X.sp) h) (a * b) =
      cast (congrArg (fun X : LSp D => GA D X.sp) h) a * cast (congrArg (fun X : LSp D => GA D X.sp) h) b := by
  subst h; rfl

theorem toXf_mul (y k : FinPt G (.grid 0 D.R.m)) : toXf (y * k) = toXf y * toXf k := by
  unfold toXf
  rw [← map_mul, Subgroup.coe_mul]
  exact congrArg _ (cast_mul_unitaryAdelicGroup_of_eq (colY_m R.toLevCh) _ _)

theorem formC_apply (S : SumChoice W U) (t : T) (u : (R.HX t).H) (y : FinPt G (.grid 0 D.R.m)) :
    S.formC t u y = S.co ((R.HX t).e u (toXf y)) := rfl

theorem formC_mul (S : SumChoice W U) (hHX : R.models_HX) (t : T) (u : (R.HX t).H) (y k : FinPt G (.grid 0 D.R.m))
    (hk : toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J) :
    S.formC t u (y * k) = (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) • S.formC t u y := by
  have h : ∀ F, F ∈ LinearMap.range (R.HX t).e → F ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ
      (levEnv D.sp.X' R.βX (R.datXt t)).J (levEnv D.sp.X' R.βX (R.datXt t)).χ := fun F hF => (hHX t).2.1 ▸ hF
  have e : (R.HX t).e u (toXf y * toXf k) =
      (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) • (R.HX t).e u (toXf y) :=
    adForms_law (Bridge.ratF D.sp.X') _ _ _ (h _ (LinearMap.mem_range_self (R.HX t).e u)) (toXf y) ⟨toXf k, hk⟩
  calc S.formC t u (y * k) = S.co ((R.HX t).e u (toXf (y * k))) := formC_apply S t u (y * k)
    _ = S.co ((R.HX t).e u (toXf y * toXf k)) := congrArg (fun z => S.co ((R.HX t).e u z)) (toXf_mul y k)
    _ = S.co ((((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) • (R.HX t).e u (toXf y)) := congrArg S.co e
    _ = (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) • S.co ((R.HX t).e u (toXf y)) := S.co.map_smul _ _
    _ = _ := congrArg _ (formC_apply S t u y).symm

end GlobalTheory.FirstRowLaw

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host
open Matrix

namespace GlobalTheory.DepthBound

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_unit_bound {ι : Type} [Fintype ι] (f : ι → k) :
    ∃ R : kˣ, ∀ i, valuation k (f i) ≤ valuation k (R : k) := by
  classical
  let γ : ValueGroupWithZero k := ∏ i, max 1 (valuation k (f i))
  have h1 : 1 ≤ γ := Finset.one_le_prod' (fun i _ => le_max_left _ _)
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective γ
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact absurd (hx ▸ h1) (not_le.2 zero_lt_one)
  refine ⟨Units.mk0 x hx0, fun i => ?_⟩
  rw [Units.val_mk0, hx]
  exact (le_max_right _ _).trans
    (Finset.single_le_prod' (f := fun j => max 1 (valuation k (f j))) (fun j _ => le_max_left _ _) (Finset.mem_univ i))

theorem frameMatrixSecondColumnBlock_mul_transpose {A A' D : Type} [Fintype A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
    (σ : A ⊕ A' ≃ D) : Y0 k σ * (Y0 k σ)ᵀ = 1 := by
  ext i j
  rw [frameMatrixSecondColumnBlock_mul_apply]
  by_cases hij : i = j
  · subst hij; simp [Y0]
  · simp [Y0, Matrix.one_apply, hij, Ne.symm hij]

theorem latticeDepth_comp_frameBlock_bounded_periodic : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D] (σ : A ⊕ A' ≃ D) {ϖ : kˣ} {e : ℕ}, IsUnif ϖ → ∀ (c : D → kˣ) {Ψ : Matrix A' D k → ℂ}, HasDepth ϖ e (diagLat c) Ψ → ∀ h : GL D k, ∃ R : kˣ, ∃ N : ℕ, (∀ g : Matrix A' A' k, Ψ (g * (Y0 k σ * h.val)) ≠ 0 → ∀ i j, valuation k (g i j) ≤ valuation k (R : k)) ∧ ∀ g Z : Matrix A' A' k, (∀ i j, valuation k (Z i j) ≤ valuation k ((ϖ ^ N : kˣ) : k)) → Ψ ((g + Z) * (Y0 k σ * h.val)) = Ψ (g * (Y0 k σ * h.val)) := by
  intro k _ _ _ _ A A' D _ _ _ _ _ _ σ ϖ e hϖ c Ψ hΨ h
  set Y : Matrix A' D k := Y0 k σ * h.val with hYdef
  set W : Matrix D A' k := (h⁻¹).val * (Y0 k σ)ᵀ with hWdef
  have hYW : Y * W = 1 := by
    rw [hYdef, hWdef, Matrix.mul_assoc, ← Matrix.mul_assoc h.val, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul, frameMatrixSecondColumnBlock_mul_transpose]
  obtain ⟨R, hR⟩ := exists_unit_bound (fun p : D × A' => (c p.1 : k) * W p.1 p.2)
  obtain ⟨R', hR'⟩ := exists_unit_bound (fun p : A' × D => Y p.1 p.2 / (((ϖ ^ e) * c p.2 : kˣ) : k))
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have hR'0 : valuation k (R' : k) ≠ 0 := by simp
  obtain ⟨N, hN⟩ := exists_pow_lt₀ hlt (Units.mk0 (valuation k (R' : k))⁻¹ (inv_ne_zero hR'0))
  have hN' : valuation k (ϖ : k) ^ N * valuation k (R' : k) ≤ 1 := by
    have : valuation k (ϖ : k) ^ N ≤ (valuation k (R' : k))⁻¹ := by simpa using hN.le
    calc valuation k (ϖ : k) ^ N * valuation k (R' : k)
        ≤ (valuation k (R' : k))⁻¹ * valuation k (R' : k) := mul_le_mul' this le_rfl
      _ = 1 := inv_mul_cancel₀ hR'0
  refine ⟨R, N, ?_, ?_⟩
  · intro g hg i j
    have hmem : g * Y ∈ matLat A' (diagLat c) := by
      by_contra hc; exact hg (hΨ.1 _ hc)
    have hg' : g = (g * Y) * W := by rw [Matrix.mul_assoc, hYW, Matrix.mul_one]
    rw [hg', Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [map_mul]
    calc valuation k ((g * Y) i l) * valuation k (W l j)
        ≤ valuation k (c l : k) * valuation k (W l j) := mul_le_mul' (mem_diagLat.1 (hmem i) l) le_rfl
      _ = valuation k ((c l : k) * W l j) := (map_mul _ _ _).symm
      _ ≤ valuation k (R : k) := hR (l, j)
  · intro g Z hZ
    rw [Matrix.add_mul]
    refine hΨ.2 _ _ fun i => ?_
    rw [smul_diagLat, mem_diagLat]
    intro m
    show valuation k ((Z * Y) i m) ≤ _
    rw [Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [map_mul]
    have hpos : 0 < valuation k ((((ϖ ^ e) * c m : kˣ)) : k) := zero_lt_iff.2 (by simp)
    have h1 := hR' (l, m)
    simp only at h1
    rw [map_div₀, div_le_iff₀ hpos] at h1
    have hz : valuation k (Z i l) ≤ valuation k (ϖ : k) ^ N := by
      simpa [Units.val_pow_eq_pow_val, map_pow] using hZ i l
    calc valuation k (Z i l) * valuation k (Y l m)
        ≤ valuation k (ϖ : k) ^ N * (valuation k (R' : k) * valuation k ((((ϖ ^ e) * c m : kˣ)) : k)) :=
          mul_le_mul' hz h1
      _ = (valuation k (ϖ : k) ^ N * valuation k (R' : k)) * valuation k ((((ϖ ^ e) * c m : kˣ)) : k) :=
          (mul_assoc _ _ _).symm
      _ ≤ 1 * valuation k ((((ϖ ^ e) * c m : kˣ)) : k) := mul_le_mul' hN' le_rfl
      _ = _ := one_mul _

end GlobalTheory.DepthBound
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

noncomputable section

namespace GlobalTheory.FlipMatch.FourierInv

open ValuativeRel

theorem card_res_pow (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (e : ℕ) : Fintype.card (Res k e) = resCard k ^ e := by
  rw [← Nat.card_eq_fintype_card]
  have hne : IsLocalRing.maximalIdeal 𝒪[k] ≠ ⊥ := IsDiscreteValuationRing.not_a_field _
  have hq := cardQuot_pow_of_prime (P := IsLocalRing.maximalIdeal 𝒪[k]) hne (i := e)
  rw [Submodule.cardQuot_apply, Submodule.cardQuot_apply] at hq
  exact hq

theorem fourierSum_invFourierSum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A : Type) [Fintype A] [DecidableEq A] (C : Type) [Fintype C] [DecidableEq C] (ψ : AddChar k Circle) (ϖ : kˣ) (n : ℕ) (P : Finset C), IsUnif ϖ → HasConductor ψ 1 →
    ∀ Ξ : Matrix A C k → ℂ, HasDepth ϖ n (blockLat ϖ n P) Ξ → fourierSum ψ ϖ n P (invFourierSum ψ ϖ n P Ξ) = Ξ := by
  intro k _ _ _ _ A _ _ C _ _ ψ ϖ n P hϖ hψ Ξ hΞ
  funext Y
  rw [fourierSum_apply]
  split_ifs with hY
  · let r : A → P → 𝒪[k] := fun i j => ⟨((ϖ ^ n : kˣ) : k) * Y i j, hY i j j.2⟩
    let S₀ : A → P → Res k n := fun i j => Ideal.Quotient.mk _ (r i j)
    set M : Matrix A P k := (ϖ ^ n)⁻¹ • liftRes S₀ with hM
    have h0 : 0 < valuation k ((ϖ ^ n : kˣ) : k) := zero_lt_iff.2 (by simp)
    have hdiff : ∀ i (j : P), Y i j - M i j ∈ 𝒪[k] := fun i j => by
      have h1 : ((Quotient.out (S₀ i j) : 𝒪[k]) - r i j) ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ n :=
        Ideal.Quotient.eq.1 (Ideal.Quotient.mk_out _)
      rw [GlobalTheory.SplitFlip.Model.val_le_iff_mem hϖ] at h1
      have e1 : Y i j - M i j = -((((ϖ ^ n)⁻¹ : kˣ) : k) * (((Quotient.out (S₀ i j) : 𝒪[k]) - r i j : 𝒪[k]) : k)) := by
        simp only [hM, Matrix.smul_apply, Units.smul_def, smul_eq_mul, liftRes, Matrix.of_apply, r]
        push_cast
        rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ ϖ.ne_zero), one_mul]
        ring
      rw [e1, Valuation.mem_integer_iff, Valuation.map_neg, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
      exact inv_mul_le_one_of_le₀ h1 h0.le
    have triv : ∀ y : k, y ∈ 𝒪[k] → ψ y = 1 := fun y hy =>
      (hψ 1).2 le_rfl y (by simpa using (Valuation.mem_integer_iff _ _).1 hy)
    have hpair : ∀ T : A → P → Res k n,
        ψ (pairCols P Y (liftRes T)) = ψ (pairCols P (setCols P Y M) (liftRes T)) := fun T => by
      have e2 : pairCols P Y (liftRes T) = pairCols P (setCols P Y M) (liftRes T) +
          ∑ i, ∑ j : P, liftRes T i j * (Y i j - M i j) := by
        simp only [pairCols, setCols, Matrix.of_apply, Finset.coe_mem, dif_pos, Subtype.coe_eta,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [e2, AddChar.map_add_eq_mul, triv _ (Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ =>
        mul_mem (liftRes_mem T i j) (hdiff i j)), mul_one]
    have hinv : Ξ (setCols P Y M) = Ξ Y := by
      have e3 : setCols P Y M = Y + Matrix.of fun i j => if h : j ∈ P then M i ⟨j, h⟩ - Y i j else 0 := by
        ext i j; by_cases h : j ∈ P <;> simp [setCols, h]
      rw [e3]
      refine hΞ.2 Y _ (GlobalTheory.SplitFlip.FourierDepth.mem_matLat_smul_blockLat.2 ⟨fun i j hj => ?_, fun i j hj => ?_⟩)
      · simp only [Matrix.of_apply, dif_pos hj]
        have := neg_mem (hdiff i ⟨j, hj⟩)
        simpa using this
      · simp [hj]
    simp_rw [hpair]
    rw [GlobalTheory.SplitFlip.Model.sum_invFourierSum hϖ hψ n P Ξ Y S₀]
    have hq : (resCard k : ℂ) ≠ 0 := by
      show ((Nat.card 𝓀[k] : ℕ) : ℂ) ≠ 0
      exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField 𝒪[k])).ne'
    have hc : ((resCard k : ℂ) ^ (n * Fintype.card A * P.card))⁻¹ *
        ((resCard k : ℂ) ^ n) ^ (Fintype.card A * P.card) = 1 := by
      rw [← pow_mul, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hq)]
    rw [← hM, hinv, card_res_pow, Nat.cast_pow, ← mul_assoc, hc, one_mul]
  · symm
    refine hΞ.1 Y fun h => hY ?_
    exact (GlobalTheory.SplitFlip.FourierDepth.mem_matLat_blockLat.1 h).1

end GlobalTheory.FlipMatch.FourierInv
end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem

namespace GlobalTheory

theorem idemOp_fix_span : ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), GlobalTheory.PRep.IsSmooth σ → ∀ (v : T.S) (x : W), x ∈ Submodule.span ℂ {y | ∃ φ : T.W v →ₗ[ℂ] W, (∀ (k : Kv V v) z, φ (T.τ v ((T.frame v).red k) z) = σ (locFin V v k) (φ z)) ∧ y ∈ LinearMap.range φ} → smoothOp (σ.comp (locFin V v)) (μf v) (T.idem μf v) x = x := by
  intro D V T μf hμ W _ _ σ hσ v x hx
  have := hμ v
  have := SelfDual.isLattice_frameLat V
  have hc : Continuous (locFin V v) := (continuous_emb _ _ _).subtype_mk _
  have hs : IsSmooth (σ.comp (locFin V v)) := fun y => (hσ y).preimage hc
  have hk : IsOpen (((T.frame v).red.ker : Subgroup (Kv V v)) : Set (Kv V v)) := by
    rw [show ((T.frame v).red.ker : Set (Kv V v)) =
        (↑) ⁻¹' (stabLocOne D.sp.cm.sig V.gram (T.frame v).emb (frameLat V) : Set (GLoc D.sp.cm.sig V.gram v)) from
      Set.ext (T.frame v).red_eq_one_iff]
    exact (isOpen_stabLocOne _ (T.frame v).emb _ (T.frame v).cm).preimage continuous_subtype_val
  obtain ⟨-, h2, h3, -⟩ := (typeIdem_projector (μf v) (isOpen_stabLoc _ _ _ v.1) (isCompact_stabLoc _ _ _ v.1)
    (T.frame v).red_surjective hk (T.irred v)).2.1 _ _ hs
  change smoothOp (σ.comp (locFin V v)) (μf v) (typeIdem (μf v) (T.frame v).red (T.τ v)) x = x
  have hle : Submodule.span ℂ {y | ∃ φ : T.W v →ₗ[ℂ] W, (∀ (k : Kv V v) z,
      φ (T.τ v ((T.frame v).red k) z) = σ (locFin V v k) (φ z)) ∧ y ∈ LinearMap.range φ} ≤
      LinearMap.range (smoothOp (σ.comp (locFin V v)) (μf v) (typeIdem (μf v) (T.frame v).red (T.τ v))) := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨φ, hφ, z, rfl⟩
    rw [SetLike.mem_coe, h3]
    exact GlobalTheory.LocGL.apply_mem_isotypic ⟨φ, fun k => LinearMap.ext fun z => hφ k z⟩ z
  obtain ⟨w, rfl⟩ := hle hx
  exact LinearMap.congr_fun h2 w

end GlobalTheory
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

open scoped TensorProduct


theorem _root_.GlobalTheory.T.finitePart_localToFiniteAdelic_component_ne : ∀ {D : D7} (V : HSp D) {v u : HeightOneSpectrum (𝓞 D.host.F)}, u ≠ v → ∀ (g : Gv V v), (Formalism.IndefR.Lev.finE V (locFin V v g : GA D V)).val.map (Formalism.UG.prV (E := D.host.E) u) = 1 := by
  first | exact @GlobalTheory.LocFinComp.finE_locFin_map_prV_ne | exact GlobalTheory.LocFinComp.finE_locFin_map_prV_ne | (intros; apply GlobalTheory.LocFinComp.finE_locFin_map_prV_ne <;> assumption)
end
