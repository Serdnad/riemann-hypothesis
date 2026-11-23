module

public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle129
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle078
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle067
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle043
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle025
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle020
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralOfPullAl
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle072
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle007
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle014
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle021
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle144
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle125
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle014
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain

namespace GlobalTheory.PowData



theorem exists_powData : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
 letI := H.starRing
 ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G) (ϖ : T.V), Irreducible ϖ → (∃ Q : P.D.toPre.X → ℤ, IsQ P.D.toPre ϖ Q) ∧ ∀ n : ℕ, ∃ (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) (_ : GrpObj G') (_ : IsCommMonObj G') (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G') (_ : UnifPowOf3 pD pA pG U' P.U) (_ : Module (𝓞 E) D'.toPre.X) (oD' : D'.toPre.OAct (𝓞 E)), (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) ∧ (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ Q : P.D.toPre.X → ℤ, IsQ P.D.toPre ϖ Q → ∀ (α : 𝓞 E) (N : ℕ), 0 < N → α * star α = (N : 𝓞 E) → ∃ (θ : Fam D'.toPre F 1) (θα : Fam D'.toPre F (1 * N)), NuGe D' (sumQ pD.xe Q) F v 1 θ 0 ∧ ThFrame D' ϖ F θ ∧ PullAl D' F oD' α 1 N θ θα := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y C P ϖ hϖ
  obtain ⟨hL, hL2, -, hL4, -⟩ := firstFiveLaws
  have hT := GlobalTheory.twistBaseChange
  refine ⟨?_, fun n => ?_⟩
  · choose Q hQ using exists_QVal hϖ P.D
    exact ⟨Q, hQ⟩
  obtain ⟨t', P', pG, pD, pA, ⟨PU⟩, -⟩ := PelUnifPowerDvr.main hL hT T.V E H C.I.G P n
  obtain ⟨M, oD, hx, hact⟩ := powOAct_of_globalFns hL.globalFns E H T.V C.I.G P n P'.D pD
  refine ⟨P'.D, P'.A, t'.G, inferInstance, inferInstance, pD, pA, pG, P'.U, PU, M, oD, hx, hact, ?_⟩
  intro F _ _ _ _ _ _ v hv Q hQ α N hN hα
  obtain ⟨θ, hν, hθ⟩ := exists_thetaFrame hL hL2 hL4 hT T.V ϖ hϖ P'.D (sumQ pD.xe Q)
    (QBox.main T.V ϖ hϖ n P.D P'.D pD Q hQ) F v hv
  letI := M
  have hw : TraceFormTwistIso P'.D.toPre oD H.w0 :=
    PsiWZeroProd.main T.V n P.D.toPre P'.D.toPre pD (𝓞 E) (fun a x => funext (hx a x)) P.oD oD hact H.w0 P.w0
  obtain ⟨f, -, hf⟩ := PullLin.exists_pull_linearMap hL T.V P'.D F (𝓞 E) oD H.w0 hw α N 1 hN le_rfl hα
  exact ⟨θ, f θ, hν, hθ, (hf _ _).2 rfl⟩

end GlobalTheory.PowData
end

section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.ThetaFrameLine

section
variable {V : Type} [CommRing V] [IsDomain V]

theorem cst_prB (D : DegPre V) (F : Type) [Field F] [Algebra (FractionRing V) F] (y : (DegPre.BF D F).left) (a : V) :
    Geo.Tor.cst ((𝟙 _ ≫ (DegPre.prB D F).left) ≫ D.P.A.hom) y a =
      gs (𝟙 _) y ⊤ (gF D F (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) a))) := by
  have hw : (DegPre.prB D F).left ≫ D.P.A.hom = (fst (TF (R := V) F) D.P.A).left ≫ jFK (R := V) F ≫ jK V :=
    (Over.w (DegPre.prB D F)).trans (Over.w (fst (TF (R := V) F) D.P.A)).symm
  have e : (jFK (R := V) F ≫ jK V).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
        (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) a)) := by
    have h := Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))))
    have h' := congrArg (fun f => f.hom a) h
    rw [jFK, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact h'.symm
  rw [Category.assoc, hw, Geo.Tor.cst]
  refine (gs_pull (𝟙 _) _ y ⊤ trivial _).symm.trans (congrArg (gs (𝟙 _) y ⊤) ?_)
  exact congrArg (fst (TF (R := V) F) D.P.A).left.appTop.hom e

end

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ θ θ' : Fam D.toPre F 1, ThFrame D ϖ F θ → ThFrame D ϖ F θ' → ∃ u : F, v u = 0 ∧ Fam.IsSmul D.toPre F u θ θ' := by
  intro V _ _ _ _ ϖ hϖ D F _ _ v hv θ θ' h h'
  obtain ⟨σ, σF, hs, he, hn⟩ := h
  obtain ⟨τ, τF, ht, hf, hm⟩ := h'
  have hL := D.toPre.P.isLB
  have gσ := GlobalTheory.IndivisibleSection.secBGenerates_of_not_dvd GlobalTheory.firstFiveLaws.1.secBaseChange V ϖ hϖ D σ hn
  obtain ⟨a, ha, -⟩ := gσ τ
  have hu : IsUnit a := by
    by_contra hna
    have hmem : a ∈ maximalIdeal V := hna
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton] at hmem
    obtain ⟨b, rfl⟩ := hmem
    refine hm ⟨SecOps.secScale (Out.scal D.toPre.P.A.hom b) σ, ?_⟩
    show SecIsMul D.toPre.P.A.hom ϖ τ (SecOps.secScale (Out.scal D.toPre.P.A.hom b) σ)
    intro j
    refine (ha j).trans ?_
    simp only [SecOps.secScale, Out.scal, resTop, map_mul, _root_.mul_assoc]
  refine ⟨algebraMap (FractionRing V) F (algebraMap V (FractionRing V) a), ?_, ?_⟩
  · have := hv (algebraMap V (FractionRing V) a) 0 ⟨hu.unit, by simp⟩
    simpa using this
  · set u := algebraMap (FractionRing V) F (algebraMap V (FractionRing V) a) with hudef
    have eθ : θ.s 0 = σF := SecOps.sec_ext he
    have eθ' : θ'.s 0 = τF := SecOps.sec_ext hf
    have h0 : ∀ j, (θ'.s 0).f j = ((u • θ).s 0).f j := by
      refine sec_ext_val hL fun y J hJ => ?_
      have e₁ := GlobalTheory.PullIntegral.sval_of_secScal hs (𝟙 _) y hJ
      have e₂ := GlobalTheory.PullIntegral.sval_of_secScal ht (𝟙 _) y hJ
      have e₃ := GlobalTheory.IndivisibleSection.sval_of_secIsMul ha (𝟙 _ ≫ (DegPre.prB D.toPre F).left) y hJ
      have o : gs (𝟙 (DegPre.BF D.toPre F).left) y ⊤ 1 = 1 := by
        rw [gs_eq _ y ⊤ trivial, map_one, map_one]
      rw [o, _root_.one_mul] at e₁ e₂
      rw [e₁, e₂, cst_prB, ← eθ, ← eθ'] at e₃
      refine e₃.trans ?_
      have hmem := hJ.mem (DegPre.famφ D.toPre F 0) (𝟙 _)
      exact ((gs_mul (𝟙 _) y _ hmem _ _).trans (congrArg₂ (· * ·) (gs_res (𝟙 _) y le_top hmem _) rfl)).symm
    refine (isSmul_iff u θ θ').2 (sub_eq_zero.1 (fam_ext fun α j => TG.fam_eq_zero hϖ (θ' - u • θ) (fun j => ?_) α j))
    exact (congrArg (· + -((u • θ).s 0).f j) (h0 j)).trans (add_neg_cancel _)

end GlobalTheory.ThetaFrameLine
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_pull [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab)
    {S T : Type} [CommRing S] [Algebra c.F S] [Field T] [Algebra c.F T] (ψ : S →ₐ[c.F] T)
    (y : FrPt Xo c S) (z : FrPt Xo c T) (hm : FrMap ψ y z) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : Fin n → Dw.La)
    (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmA c a n)
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y.x)))
    (hF : ∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y.s (levPt Xo y.x (x b)) (F b)) :
    ∃ F' : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo z.x)),
      (∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) z.s (levPt Xo z.x (x b)) (F' b)) ∧
      ψ (thExpr Xo c nab y P F) = thExpr Xo c nab z P F' := by
  let h : ptO Xo z.x ⟶ ptO Xo y.x := Over.homMk (spMap ψ.toRingHom) hm.1.symm
  choose F' hF' using fun b => GermD.exists_pullSec Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2)
    (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) (F b)
  refine ⟨F', fun b => ?_, ?_⟩
  · have e : h ≫ levPt Xo y.x (x b) = levPt Xo z.x (x b) := by
      unfold levPt
      rw [← Category.assoc, comp_toUnit]
    rw [← e]
    exact (GlobalTheory.VtBaseChange.isVtOver_isUUOver_baseChange E H Dw l Xo l.M (l.Mb ^ 2) _ _ h y.s z.s
      (GlobalTheory.FramedBaseChange.isPullSec ψ hm h rfl) (F b) (F' b) (hF' b)).1 _ (hF b)
  · unfold thExpr
    rw [map_mul, AlgHom.commutes,
      GlobalTheory.T.harmonicConnectionValue_baseChange_field E H Dw l Xo c nab hnab S T ψ y z hm h rfl a n P hP.1 l.M F F' hF']

theorem exists_algHom_field (F U : Type) [Field F] [CommRing U] [Algebra F U] [Nontrivial U] :
    ∃ (K : Type) (_ : Field K) (_ : Algebra F K), Nonempty (U →ₐ[F] K) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal U
  exact ⟨U ⧸ m, Ideal.Quotient.field m, inferInstance, ⟨Ideal.Quotient.mkₐ F m⟩⟩

theorem thetaValue_natural_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (S T : Type) [CommRing S] [Algebra c.F S] [Field T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y0 : FrPt Xo c S) (y : FrPt Xo c T), FrMap φ y0 y → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ v0 w, ThValAt Xo c nab y0 x P v0 → ThValAt Xo c nab y x P w → φ v0 = w := by
  intro E _ _ _ H Dw l Xo c _ nab hnab S T _ _ _ _ φ y0 y hφ a n x P hP v0 w hv hw
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨S₁, i₁, j₁, φ₁, y₁, F₁, hff₁, hm₁, hV₁, he₁⟩ := hv
  obtain ⟨T₁, i₂, j₂, κ, y₂, F₂, hff₂, hm₂, hV₂, he₂⟩ := hw
  obtain ⟨U, iU, jU, ψ₁, ψ₂, hcomm, -, hinj⟩ :=
    exists_faithfullyFlat_pushout c.F S T₁ S₁ (κ.comp φ) φ₁ hff₁
  have hκ : Function.Injective κ := hff₂.injective
  haveI : Nontrivial U := (hinj.comp hκ).nontrivial
  obtain ⟨K, iK, jK, ⟨π⟩⟩ := exists_algHom_field c.F U
  have hψ : (π.comp ψ₁).comp (κ.comp φ) = (π.comp ψ₂).comp φ₁ := by
    rw [AlgHom.comp_assoc, hcomm, AlgHom.comp_assoc]
  obtain ⟨z, hz1⟩ := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c T₁ K (π.comp ψ₁) y₂
  have hz : FrMap ((π.comp ψ₂).comp φ₁) y0 z :=
    hψ ▸ GlobalTheory.FramedBaseChange.trans (κ.comp φ) (π.comp ψ₁) (FramedBaseChange.trans φ κ hφ hm₂) hz1
  have hz2 : FrMap (π.comp ψ₂) y₁ z := GlobalTheory.FramedBaseChange.cancel φ₁ (π.comp ψ₂) hm₁ hz
  obtain ⟨G1, w1, e1⟩ := exists_pull nab hnab (π.comp ψ₁) y₂ z hz1 a n x P hP F₂ hV₂
  obtain ⟨G2, w2, e2⟩ := exists_pull nab hnab (π.comp ψ₂) y₁ z hz2 a n x P hP F₁ hV₁
  have hG : G1 = G2 := funext fun b => vtUniq_obj hL.globalFns Xo.univ (w1 b) (w2 b)
  apply ((π.comp ψ₁).comp κ).toRingHom.injective
  change (π.comp ψ₁) (κ (φ v0)) = (π.comp ψ₁) (κ w)
  rw [he₂, e1, hG, ← e2, ← he₁]
  exact AlgHom.congr_fun hψ v0

end GlobalTheory.ThetaField
end
end
