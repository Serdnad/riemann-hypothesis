module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2352
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixUnique
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle298
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2450
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
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390

@[expose] public section

section

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
namespace GlobalTheory.HSApp
theorem generated_weights_mul_stable_and_bounded : _root_.GlobalTheory.CovTop.Hypotheses'' → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (P : WtPar (T.Q.Dw j)) (R : Choice TF.X Z Y.U P) (ω : CanId R.toModif) (h : Ready R ω (xiR D) (fun _ => D.sp.W j) Y.dict) (f₁ : CuspFrame Z Y.U (xiR D) (fun _ => D.sp.W j) Y.dict P.u₁) (f₂ : CuspFrame Z Y.U (xiR D) (fun _ => D.sp.W j) Y.dict P.u₂) (th : R.L.Sec) (k : Consts), BergLe Z Y.U (fun _ => D.sp.W j) Y.dict P.u₁ k.beta → (h.data f₁ f₂ th k).MulStable ∧ (h.data f₁ f₂ th k).MulBound fun _ => k.beta := by
  intro hPr D T j Y e o hG hE Z TF P R ω h f₁ f₂ th k hB
  have tr : ∀ (a b : AllWt.Weight (T.Q.Dw j)) (_ : a = b) (g : Cusp Z Y.U a), ∃ g' : Cusp Z Y.U b, g'.1 = g.1 ∧
      (g ∈ latOn Y.U Z (wtOf _ a 0) → g' ∈ latOn Y.U Z (wtOf _ b 0)) := by
    rintro a b rfl g
    exact ⟨g, rfl, id⟩
  have key : ∀ (i : ℕ) (hi : i < P.T) (w' : Cusp Z Y.U P.u₁) (f' : Cusp Z Y.U (P.wt i)),
      ∃ g' : Cusp Z Y.U (P.wt (i + 1)), g'.1 = w'.1 * f'.1 ∧
        (w' ∈ latOn Y.U Z (wtOf _ P.u₁ 0) → f' ∈ latOn Y.U Z (wtOf _ (P.wt i) 0) →
          g' ∈ latOn Y.U Z (wtOf _ (P.wt (i + 1)) 0)) ∧
        ((h.equivV f₁ f₂ th k (Nat.succ_le_of_lt hi) g' : (h.data f₁ f₂ th k).V (i + 1)) :
            (h.data f₁ f₂ th k).Sec (i + 1)) =
          (h.data f₁ f₂ th k).mulW i (f₁.b.equivFun w') (h.equivV f₁ f₂ th k hi.le f') := by
    intro i hi w' f'
    have hx := _root_.GlobalTheory.T.cuspidal_sections_mul_mem D T j Y e o hG hE Z P.u₁ (P.wt i) w' f' hPr
    obtain ⟨g, hg, hgl⟩ := hx
    have hy := tr _ _ (P.u₁_add_wt i) g
    obtain ⟨g', hg', hgl'⟩ := hy
    refine ⟨g', hg'.trans hg, fun a b => hgl' (hgl a b), ?_⟩
    exact (h.coe_equivV f₁ f₂ th k _ g').trans ((h.mulW_adjSec f₁ f₂ th k i w' f' g' (hg'.trans hg)).symm.trans
      (congrArg _ (h.coe_equivV f₁ f₂ th k hi.le f').symm))
  refine ⟨?_, ?_⟩
  · intro i hi w hw f hf
    have hk := key i hi (f₁.b.equivFun.symm w) ((h.equivV f₁ f₂ th k hi.le).symm f)
    obtain ⟨g', -, hl, he⟩ := hk
    have hw' : f₁.b.equivFun.symm w ∈ latOn Y.U Z (wtOf _ P.u₁ 0) :=
      (h.mem_lattice f₁ f₂ th k _).1
        (Eq.mpr (congrArg (· ∈ (h.data f₁ f₂ th k).lattice) (f₁.b.equivFun.apply_symm_apply w)) hw)
    have hf' : (h.equivV f₁ f₂ th k hi.le).symm f ∈ latOn Y.U Z (wtOf _ (P.wt i) 0) :=
      (h.equivV_mem f₁ f₂ th k hi.le _).1
        (Eq.mpr (congrArg (· ∈ (h.data f₁ f₂ th k).M i) (LinearEquiv.apply_symm_apply _ f)) hf)
    refine ⟨h.equivV f₁ f₂ th k (Nat.succ_le_of_lt hi) g', (h.equivV_mem f₁ f₂ th k _ g').2 (hl hw' hf'), ?_⟩
    exact he.trans (congrArg₂ (fun a b => (h.data f₁ f₂ th k).mulW i a b) (f₁.b.equivFun.apply_symm_apply w)
      (congrArg Subtype.val (LinearEquiv.apply_symm_apply _ f)))
  · intro i hi σ w hw f hf g hg
    have pe : ∀ (a b : AllWt.Weight (T.Q.Dw j)), a = b → ∀ σ x,
        petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ a 0) σ x =
          petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ b 0) σ x := by
      rintro a b rfl σ x
      rfl
    have hk := key i hi (f₁.b.equivFun.symm w) ((h.equivV f₁ f₂ th k hi.le).symm f)
    obtain ⟨g', hgp, -, he⟩ := hk
    have hgg : g = h.equivV f₁ f₂ th k (Nat.succ_le_of_lt hi) g' :=
      Subtype.ext (hg.trans ((congrArg₂ (fun a b => (h.data f₁ f₂ th k).mulW i a b) (f₁.b.equivFun.apply_symm_apply w)
        (congrArg Subtype.val (LinearEquiv.apply_symm_apply _ f))).symm.trans he.symm))
    have hb := GlobalTheory.T.petersson_norm_mul_le_sqrt_bergman_mul_component D T j Y e o hG hE Z P.u₁ (P.wt i) (f₁.b.equivFun.symm w)
      ((h.equivV f₁ f₂ th k hi.le).symm f) k.beta (zero_le_one.trans k.one_le_beta) hB σ
    have e0 : petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ (P.wt (i + 1)) 0) σ g'.1 =
        petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ (P.u₁ + P.wt i) 0) σ
          ((f₁.b.equivFun.symm w).1 * ((h.equivV f₁ f₂ th k hi.le).symm f).1) :=
      (congrArg (petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ (P.wt (i + 1)) 0) σ) hgp).trans
        (pe _ _ (P.u₁_add_wt i).symm σ _)
    have e1 := h.nrm_equivV f₁ f₂ th k (Nat.succ_le_of_lt hi) σ g'
    have e2 := h.normAt_eq f₁ f₂ th k σ (f₁.b.equivFun.symm w)
    have e3 := h.nrm_equivV f₁ f₂ th k hi.le σ ((h.equivV f₁ f₂ th k hi.le).symm f)
    have e2' := (congrArg ((h.data f₁ f₂ th k).normAt σ) (f₁.b.equivFun.apply_symm_apply w).symm).trans e2
    have e3' := (congrArg (((h.data f₁ f₂ th k).nm i).nrm σ) (LinearEquiv.apply_symm_apply _ f).symm).trans e3
    calc _ = _ := congrArg (((h.data f₁ f₂ th k).nm (i + 1)).nrm σ) hgg
      _ = _ := e1
      _ = _ := e0
      _ ≤ _ := hb
      _ = _ := congrArg₂ (fun a b => Real.sqrt k.beta * a * b) e2'.symm e3'.symm
end GlobalTheory.HSApp
end
end

section

section
noncomputable section
namespace GlobalTheory.CovTop.LevelIndex
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV
section Gen
variable {E : Type} [Field E] [NumberField E]
variable {F : Type} [Field F] [NumberField F] [StarRing E] [Algebra F E] {n : ℕ} {LL : Type} [CommRing LL]
end Gen
end GlobalTheory.CovTop.LevelIndex
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem GlobalTheory.CovTop.LevelIndex.level_index_le_bound : ∀ (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ), GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.IndexBound C i P := by
  intro _ D Tu C t0 hC i P
  have hB : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i (LevelP.full _ _ _) = parLev D.sp.cm (Wc D i).gram (C.βW i) (C.datWp i P) := by
    have e : C.datWp i (LevelP.full _ _ _) = { C.datWp i P with P := LevelP.full (C.datWp i P).Pg (C.datWp i P).r ℂ } := by
      simp only [LevCh.datWp, datY, if_true]
    rw [← GlobalTheory.CovTop.LevelIndex.lev_full, ← e]
  obtain ⟨h0, h1⟩ := GlobalTheory.CovTop.LevelIndex.relIndex_lev_le D.sp.cm (Wc D i).gram (C.βW i) (C.datWp i P) _ hB
  refine ⟨h0, ?_⟩
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring
  have hN : D.host.g 0 * D.host.g 1 ≠ 0 := mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  have hg : ∀ PP ∈ C.Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    intro PP hP
    obtain ⟨k, hk⟩ := (hC.Pg PP).1 hP
    have h0 := C.C.P.pb_over k
    rw [← hk] at h0
    have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal := h0
    rw [map_natCast] at h2
    rw [Nat.cast_mul]
    fin_cases k
    · exact Ideal.mul_mem_right _ _ h2
    · exact Ideal.mul_mem_left _ _ h2
  have h2 := GlobalTheory.CovTop.LevelIndex.prod_absNorm_le C.Pg hN hg
  have h3 := GlobalTheory.CovTop.LevelIndex.card_levelQuotientGroup_le_prod_absNorm_pow_sq C.Pg D.R.r
  have h4 : (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P).relIndex (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i (LevelP.full _ _ _)) ≤
      (D.host.g 0 * D.host.g 1) ^ (2 * D.R.f * D.R.r ^ 2) := by
    rw [pow_mul, ← hfr]
    exact h1.trans (h3.trans (Nat.pow_le_pow_left h2 _))
  have h5 := Real.log_le_log (Nat.cast_pos.2 (Nat.pos_of_ne_zero h0)) (Nat.cast_le (α := ℝ).2 h4)
  refine h5.trans (le_of_eq ?_)
  push_cast
  rw [Real.log_pow]
  push_cast
  ring
end
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta

theorem _root_.GlobalTheory.T.level_subgroup_index_bounded : ∀ (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ), GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.IndexBound C i P := by
  first | exact @_root_.GlobalTheory.CovTop.LevelIndex.level_index_le_bound | exact _root_.GlobalTheory.CovTop.LevelIndex.level_index_le_bound | (intros; apply _root_.GlobalTheory.CovTop.LevelIndex.level_index_le_bound <;> assumption)
end
end

section

section
set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.AllWt
open scoped Classical
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.DeRham
open GlobalTheory.Cris GlobalTheory.CatCoh GlobalTheory.Published GlobalTheory.Published.AbelianDeRham DividedPowers MonoidalCategory CartesianMonoidalCategory MonObj
variable {R : Type} [CommRing R]
end GlobalTheory.DeRham
namespace GlobalTheory.FlagTan
open GlobalTheory.DeRham GlobalTheory.Cris GlobalTheory.Published ReciprocityTheory.ChartRestriction.G.PullbackSections MonoidalCategory CartesianMonoidalCategory MonObj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K]
section Frame
variable {y : FrPt Xo c K} {B : Over (Sp K)} [GrpObj B] [IsCommMonObj B] {ρ : B.left ⟶ Xo.univ.t.G.left}
  (hρ : IsGrpPullback B Xo.univ.t.G y.x ρ)
end Frame
theorem kodaira_spencer_map_unique : _root_.GlobalTheory.CovTop.Hypotheses'' → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K]
    [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' →
    ∀ M M' : GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K, GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x' M →
      GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x' M' → M = M' :=
  fun Pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h h' => IsKS.unique Pr.p5 h h'
end GlobalTheory.FlagTan
end
end

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory

theorem _root_.GlobalTheory.T.flag_tangent_kodaira_spencer_unique : _root_.GlobalTheory.CovTop.Hypotheses'' → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → ∀ M M' : GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K, GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x' M → GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x' M' → M = M' := by
  first | exact @_root_.GlobalTheory.FlagTan.kodaira_spencer_map_unique | exact _root_.GlobalTheory.FlagTan.kodaira_spencer_map_unique | (intros; apply _root_.GlobalTheory.FlagTan.kodaira_spencer_map_unique <;> assumption)
end
end

section

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ConstDeform
theorem constDeformation_objMap_eq : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (q : A'.left ⟶ A.left), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G y.x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → i ≫ q = 𝟙 _ → IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q → ∀ o : Obj Dw l (baseKA l) (x' ≫ Xo.s), Nonempty (ObjMap o Xo.univ x') → Nonempty (ObjMap o Xo.univ (constPt x')) := by
  intro hP hGD E _ _ _ H Dw l Xo c K _ _ y x' hpq hT A _ A' _ π π' i q hi hπ hπ' hiπ hiq hq o ⟨m⟩
  have hw : m.cm.F ≫ Xo.univ.t.G.hom = o.t.G.hom ≫ x' := m.cart.1.w
  let g : o.t.G.left ⟶ A'.left := hπ'.1.lift m.cm.F o.t.G.hom hw
  have hg : g ≫ π' = m.cm.F := hπ'.1.lift_fst _ _ _
  have hgw : g ≫ A'.hom = o.t.G.hom := hπ'.1.lift_snd _ _ _
  have hgc : IsGrpPullback o.t.G A' (𝟙 _) g :=
    hπ'.cancel (m.cart.congr (Category.id_comp _).symm hg.symm) (by rw [hgw, Category.comp_id])
  have hred : spMap (algebraMap K (DualNumber K)) ≫ y.x = constPt x' := by
    rw [← hT.2]; rfl
  have hF : IsGrpPullback o.t.G Xo.univ.t.G (constPt x') (g ≫ q ≫ π) :=
    (hgc.comp (hq.comp hπ)).congr (by rw [Category.id_comp, hred]) rfl
  haveI : CharZero K := (RingHom.charZero_iff (algebraMap c.F K).injective).1 inferInstance
  have hgq := hgc.comp hq
  have hcomm : ∀ (T : Over (Sp K)) (x y : T ⟶ A), x * y = y * x := by
    intro T x y
    apply Over.OverMorphism.ext
    apply hπ.1.hom_ext
    · have e1 := hπ.2 T x y (pushPt hπ.1.w x) (pushPt hπ.1.w y) rfl rfl
      have e2 := hπ.2 T y x (pushPt hπ.1.w y) (pushPt hπ.1.w x) rfl rfl
      rw [← e1, ← e2, _root_.mul_comm]
    · rw [Over.w (x * y), Over.w (y * x)]
  have key : ∀ (σ : 𝟙_ (Over (Sp (DualNumber K))) ⟶ o.t.G) (τ : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G) (n : ℕ),
      0 < n → σ ^ n = 1 → σ.left ≫ m.cm.F = x' ≫ τ.left →
      σ.left ≫ (g ≫ q ≫ π) = constPt x' ≫ τ.left := by
    intro σ τ n hn hσ hστ
    let u := pushHom hgq (𝟙_ (Over (Sp (DualNumber K)))) σ
    have hu : u ^ n = 1 := by rw [← map_pow, hσ, map_one]
    have e := GlobalTheory.T.torsion_dualNumber_point_eq_constant_charZero K A _ (by simp) (hcomm _) u n hn hu
    have hul : u.left = σ.left ≫ g ≫ q := by
      show σ.left ≫ (g ≫ q) = _; rfl
    rw [hul] at e
    let w := spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ σ.left ≫ g
    have hw' : w ≫ A'.hom = 𝟙 _ ≫ GlobalTheory.DeRham.epsRed K := by
      simp only [w, Category.assoc, hgw, Category.id_comp]
      rw [Over.w σ]; rfl
    let s₀ := hi.1.lift w (𝟙 _) hw'
    have hs₀ : s₀ ≫ i = w := hi.1.lift_fst _ _ _
    calc σ.left ≫ (g ≫ q ≫ π) = (σ.left ≫ g ≫ q) ≫ π := by simp only [Category.assoc]
      _ = (spMap (algebraMap K (DualNumber K)) ≫ w ≫ q) ≫ π := by rw [e]; simp only [w, Category.assoc]
      _ = spMap (algebraMap K (DualNumber K)) ≫ s₀ ≫ i ≫ π' := by
          rw [← hs₀]; simp only [Category.assoc]; rw [reassoc_of% hiq, hiπ]
      _ = spMap (algebraMap K (DualNumber K)) ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ σ.left ≫ m.cm.F := by
          rw [reassoc_of% hs₀]; simp only [w, Category.assoc, hg]
      _ = constPt x' ≫ τ.left := by rw [hστ]; rfl
  have hpow : ∀ (f : Dw.La → (𝟙_ (Over (Sp (DualNumber K))) ⟶ o.t.G)), (∀ a b, f (a + b) = f a * f b) →
      ∀ (n : ℕ) a, f (n • a) = f a ^ n := by
    intro f hf n a
    induction n with
    | zero =>
      have h0 := hf 0 0
      rw [add_zero] at h0
      rw [zero_smul, pow_zero]
      exact mul_left_cancel (h0.symm.trans (_root_.mul_one _).symm)
    | succ n ih => rw [succ_nsmul, hf, ih, pow_succ]
  have hM : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
    have h1 : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    exact Ideal.mul_le_left (I := l.Mb) (J := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) h1
  exact ⟨{
    cm := cubeMapOf hF
    cart := hF
    base := rfl
    act := _root_.GlobalTheory.T.const_deformation_action_trivial hP hGD E H Dw l Xo c K y x' hpq hT A A' π π' i q hi hπ hπ' hiπ hiq hq o m g hg hgw hF
    lin := _root_.GlobalTheory.T.cubical_structure_const_section_pullback hP hGD E H Dw l Xo c K y x' hpq hT A A' π π' i q hi hπ hπ' hiπ hiq hq o m g hg hgw hF
    eta := fun a => key (o.eta a) (Xo.univ.eta a) l.M (by have := l.three_le; omega)
      (by rw [← hpow _ o.eta_add]; exact o.eta_ker _ (by
        rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]; exact Submodule.smul_mem_smul hM Submodule.mem_top))
      (m.eta a)
    etaA := fun a => key (o.etaA a) (Xo.univ.etaA a) l.A l.A_pos
      (by rw [← hpow _ o.etaA_add]; exact o.etaA_ker a) (m.etaA a) }⟩
end GlobalTheory.ConstDeform
end

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.const_deformation_obj_eq : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (q : A'.left ⟶ A.left), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G y.x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → i ≫ q = 𝟙 _ → IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q → ∀ o : Obj Dw l (baseKA l) (x' ≫ Xo.s), Nonempty (ObjMap o Xo.univ x') → Nonempty (ObjMap o Xo.univ (constPt x')) := by
  first | exact @_root_.GlobalTheory.ConstDeform.constDeformation_objMap_eq | exact _root_.GlobalTheory.ConstDeform.constDeformation_objMap_eq | (intros; apply _root_.GlobalTheory.ConstDeform.constDeformation_objMap_eq <;> assumption)
end
end
