module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.AffineMonoid.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqBasicOpen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle538
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle013
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.SiegelLatticeTheory.PtEquivApply
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle010
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001

@[expose] public section

section


open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefFree

theorem mem_smul_top_of_coprime {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] (I J : Ideal R) (hIJ : J ⊔ I = ⊤)
    (f : N →ₗ[R] N) (h : ∀ z ∈ J • (⊤ : Submodule R N), f z ∈ I • (⊤ : Submodule R N)) (x : N) :
    f x ∈ I • (⊤ : Submodule R N) := by
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (hIJ ▸ Submodule.mem_top : (1 : R) ∈ J ⊔ I)
  have e : f x = f (a • x) + b • f x := by rw [map_smul, ← add_smul, hab, one_smul]
  rw [e]
  exact add_mem (h _ (Submodule.smul_mem_smul ha Submodule.mem_top)) (Submodule.smul_mem_smul hb Submodule.mem_top)

theorem natCast_not_isUnit {K : Type} [Field K] [NumberField K] {g : ℕ} (hg : g.Prime) : ¬ IsUnit (g : 𝓞 K) := by
  intro hu
  have h1 := hu.map (Algebra.norm ℤ : 𝓞 K →* ℤ)
  have e : ((g : 𝓞 K)) = algebraMap ℤ (𝓞 K) (g : ℤ) := by simp
  rw [e, Algebra.norm_algebraMap] at h1
  have hn : Module.finrank ℤ (𝓞 K) ≠ 0 := Module.finrank_pos.ne'
  rw [isUnit_pow_iff hn, Int.isUnit_iff] at h1
  have := hg.two_le
  rcases h1 with h1 | h1 <;> omega

theorem sup_span_ne_top {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (l : Level H)
    {g : ℕ} (hg : g.Prime) (hd : g ∣ l.M) : l.Mb ⊔ Ideal.span {(g : 𝓞 E)} ≠ ⊤ := by
  intro htop
  have hb : Ideal.map (H.bar : 𝓞 E →+* 𝓞 E) l.Mb ⊔ Ideal.span {(g : 𝓞 E)} = ⊤ := by
    have := congrArg (Ideal.map (H.bar : 𝓞 E →+* 𝓞 E)) htop
    rwa [Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_natCast, Ideal.map_top] at this
  have hle : (⊤ : Ideal (𝓞 E)) ≤ Ideal.span {(g : 𝓞 E)} := by
    calc (⊤ : Ideal (𝓞 E)) = (l.Mb ⊔ Ideal.span {(g : 𝓞 E)}) * (Ideal.map (H.bar : 𝓞 E →+* 𝓞 E) l.Mb ⊔ Ideal.span {(g : 𝓞 E)}) := by
          rw [htop, hb, Ideal.top_mul]
      _ ≤ Ideal.span {(g : 𝓞 E)} := by
          rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup, l.prod]
          refine sup_le (sup_le ?_ (Ideal.mul_le_inf.trans inf_le_right)) (sup_le (Ideal.mul_le_inf.trans inf_le_left) (Ideal.mul_le_inf.trans inf_le_left))
          rw [Ideal.span_singleton_le_span_singleton]
          exact_mod_cast (Nat.cast_dvd_cast hd : ((g : 𝓞 E)) ∣ (l.M : 𝓞 E))
  exact natCast_not_isUnit hg (Ideal.span_singleton_eq_top.1 (top_le_iff.1 hle))

end GlobalTheory.DefFree
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LBGerm GlobalTheory.AmpleOverBase

namespace GlobalTheory.GenNearExtend

theorem exists_sec_of_gen_near : ∀ (Z X : Scheme.{0}) (e : X ⟶ Z), IsOpenImmersion e → CompactSpace X →
    QuasiSeparatedSpace X → ∀ (M : LB Z), M.IsLB → ∀ (r : Γ(X, ⊤)) (O : Z.Opens),
    (∀ x ∈ X.basicOpen r, e x ∈ O) → ∀ t : LB.Gen (M.pull O.ι), t.IsGen →
    ∃ σ : LB.Sec (M.pull e), X.basicOpen r ≤ nonzeroLocus σ := by
  intro Z X e _ _ _ M hM r O hO t ht
  have hL : (M.pull e).IsLB := LB.isLB_pull hM e
  let f : (X.basicOpen r).toScheme ⟶ X := (X.basicOpen r).ι
  have hrange : Set.range (f ≫ e).base ⊆ Set.range O.ι.base := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hO _ y.2
  let ψ : (X.basicOpen r).toScheme ⟶ O.toScheme := IsOpenImmersion.lift O.ι (f ≫ e) hrange
  have hψ : ψ ≫ O.ι = f ≫ e := IsOpenImmersion.lift_fac _ _ _
  have hpt : ∀ y, O.ι (ψ y) = e (f y) := fun y => by
    rw [← Scheme.Hom.comp_apply, hψ, Scheme.Hom.comp_apply]
  let a : ChartPull (lbPow ((M.pull e).pull f) 1) (M.pull O.ι) ψ :=
    { idx := fun J _ => J PUnit.unit PUnit.unit PUnit.unit
      le := fun J y hy => by
        have h1 := mem_pull.1 (mem_pull.1 (mem_powChart.1 hy))
        show ψ y ∈ (M.pull O.ι).U _
        rw [mem_pull, hpt]
        exact h1
      g := fun y J J' hJ hJ' => by
        have h1 := mem_powChart.1 hJ
        have h2 := mem_powChart.1 hJ'
        have h1' : (𝟙 _ ≫ f) y ∈ (M.pull e).U (J PUnit.unit PUnit.unit) := mem_pull.1 h1
        have h2' : (𝟙 _ ≫ f) y ∈ (M.pull e).U (J' PUnit.unit PUnit.unit) := mem_pull.1 h2
        have h3 : ψ y ∈ (M.pull O.ι).U (fun _ => J PUnit.unit PUnit.unit PUnit.unit) := by
          rw [mem_pull, hpt]; exact mem_pull.1 (mem_pull.1 h1)
        have h4 : ψ y ∈ (M.pull O.ι).U (fun _ => J' PUnit.unit PUnit.unit PUnit.unit) := by
          rw [mem_pull, hpt]; exact mem_pull.1 (mem_pull.1 h2)
        refine (gm_lbPow_g 1 (𝟙 _) y J J' hJ hJ').trans ?_
        rw [pow_one, gm_pull_g ((M.pull e)) f (𝟙 _) y _ _ h1 h2, gm_pull_g M e (𝟙 _ ≫ f) y _ _ h1' h2',
          gm_pull_g M O.ι ψ y _ _ h3 h4, hψ, Category.id_comp] }
  let s0 : (M.pull O.ι).Sec := ⟨fun i => (t.s i).val, fun i j => congrArg Units.val (ht i j)⟩
  let t' := chartSec a s0
  have ht' : ∀ y, y ∈ nonzeroLocus t' := fun y => by
    obtain ⟨i, hi⟩ := exists_chart hM (e (f y))
    have hJ : y ∈ (lbPow ((M.pull e).pull f) 1).U (fun _ _ _ => i) :=
      mem_powChart.2 (mem_pull.2 (mem_pull.2 hi))
    rw [mem_nonzeroLocus_iff_isUnit t' hJ, gs_chartSec a s0 (𝟙 _) y _ hJ]
    have hm : (𝟙 _ ≫ ψ) y ∈ (M.pull O.ι).U (a.idx (fun _ _ _ => i)) := a.le _ hJ
    rw [gs_unit _ y _ hm]
    exact Units.isUnit _
  have hr : X.basicOpen r = f.opensRange := (Scheme.Opens.opensRange_ι _).symm
  have hs₀ : nonzeroLocus (secOfFn (M.pull e) r) = f.opensRange := (nonzeroLocus_secOfFn hL r).trans hr
  obtain ⟨T, hT, hTu⟩ := exists_push f (nonzeroLocus (secOfFn (M.pull e) r)) hs₀ t'
  obtain ⟨N, hN⟩ := exists_sec_eq_pow_mul hL (secOfFn (M.pull e) r) T hT
  obtain ⟨u, hu⟩ := hN N le_rfl
  have key : ∀ (y' : (X.basicOpen r).toScheme) (J : PUnit → (M.pull e).ι), f y' ∈ powChart (M.pull e) J →
      (f y' ∈ nonzeroLocus u ↔ y' ∈ nonzeroLocus t') := fun y' J hJ => by
    have hs : f y' ∈ nonzeroLocus (secOfFn (M.pull e) r) := hs₀ ▸ ⟨y', rfl⟩
    have hy : f y' ∈ nonzeroLocus (secOfFn (M.pull e) r) ⊓ powChart (M.pull e) J := ⟨hs, hJ⟩
    have e' := congrArg (gs (𝟙 X) (f y') _) (hu J)
    rw [gs_res (𝟙 X) (f y') _ hy, gs_mul (𝟙 X) (f y') _ hy, gs_pow (𝟙 X) (f y') _ hy,
      gs_res (𝟙 X) (f y') _ hy] at e'
    rw [mem_nonzeroLocus_iff_powFn u hJ, e', IsUnit.mul_iff, hTu y' J hJ]
    exact and_iff_right (((mem_nonzeroLocus_iff_powFn _ hJ).1 hs).pow N)
  refine ⟨secOfPowOne (secCast (by omega) u), ?_⟩
  rw [nonzeroLocus_secOfPowOne, nonzeroLocus_secCast]
  intro x hx
  obtain ⟨y, rfl⟩ : ∃ y, f y = x := ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨i, hi⟩ := exists_chart hL (f y)
  exact (key y (fun _ => i) (mem_powChart.2 hi)).2 (ht' y)

end GlobalTheory.GenNearExtend
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TanPull

theorem one_left_congr {X Z : Scheme.{0}} {G : Over X} [GrpObj G] {f g : Z ⟶ X} (h : f = g) :
    (1 : Over.mk f ⟶ G).left = (1 : Over.mk g ⟶ G).left := by
  subst h; rfl

theorem isTanAtG_comp
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
    {V : Type} [CommRing V] (x : Sp V ⟶ Y.X) (G : SAB H (Sp V)) (ψ : SABMap G Y.t x)
    (w : epsOver V V ⟶ G.G) (hw : IsTan w) : IsTanAtG Y.t x (w.left ≫ ψ.φ) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, ψ.cart.1.w, ← Category.assoc, Over.w w]
    rfl
  · rw [← Category.assoc, hw]
    refine (Formalism.L2.Pj.grpPull_one ψ.cart (ptOver V V)).symm.trans (one_left_congr ?_)
    show spMap (algebraMap V V) ≫ x = x
    have : spMap (algebraMap V V) = 𝟙 _ := by
      rw [Algebra.algebraMap_self]; exact Spec.map_id _
    rw [this, Category.id_comp]

theorem exists_tanM_of_isTan
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
    {V : Type} [CommRing V] (x : Sp V ⟶ Y.X) (G : SAB H (Sp V)) (ψ : SABMap G Y.t x)
    (w : epsOver V V ⟶ G.G) (hw : IsTan w) :
    ∃ v : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x Y.t.G, (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left = w.left ≫ ψ.φ :=
  ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.mkT (Formalism.L2.Pj.ovT (isTanAtG_comp x G ψ w hw)) (Formalism.L2.Pj.smT_zero_ovT _), rfl⟩

end GlobalTheory.TanPull
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.TanLiftPull

theorem toUnit_left_eq {S : Scheme.{0}} (A : Over S) (f : A ⟶ 𝟙_ (Over S)) : f.left = A.hom := by
  simpa using Over.w f

theorem one_left_eq {S : Scheme.{0}} (A : Over S) (G : Over S) [GrpObj G] :
    (1 : A ⟶ G).left = A.hom ≫ η[G].left := by
  rw [← toUnit_left_eq A (toUnit A)]
  rfl

theorem exists_isTan_lift : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {V : Type} [CommRing V] (x : Sp V ⟶ Y.X) (G : SAB H (Sp V)) (ψ : SABMap G Y.t x) (v : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x Y.t.G), ∃ w : epsOver V V ⟶ G.G, IsTan w ∧ (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left = w.left ≫ ψ.φ := by
  intro E _ _ _ H Dw l Xo c O _ β Y V _ x G ψ v
  have hpb : IsPullback ψ.φ G.G.hom Y.t.G.hom x := ψ.cart.1
  have hsq : (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left ≫ Y.t.G.hom = (epsOver V V).hom ≫ x := by
    rw [Over.w]; rfl
  have hfa : spMap (TrivSqZeroExt.fstHom V V V).toRingHom ≫ spMap (algebraMap V (DualNumber V)) = 𝟙 _ := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    convert Spec.map_id (CommRingCat.of V)
    ext a
    simp
  refine ⟨Over.homMk (hpb.lift _ _ hsq) (hpb.lift_snd _ _ _), ?_, (hpb.lift_fst _ _ _).symm⟩
  show spMap (TrivSqZeroExt.fstHom V V V).toRingHom ≫ hpb.lift _ _ hsq = (1 : ptOver V V ⟶ G.G).left
  apply hpb.hom_ext
  · rw [Category.assoc, hpb.lift_fst]
    have h1 := congrArg (fun f => f.left) (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem v)
    simp only [smT_left] at h1
    have key : spMap (TrivSqZeroExt.fstHom V V V).toRingHom ≫ spMap (epsMul (0 : V)) =
        spMap (TrivSqZeroExt.fstHom V V V).toRingHom := by
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext <;> simp [epsMul]
    have hunit : η[G.G].left ≫ ψ.φ = x ≫ η[Y.t.G].left := by
      have h := ψ.cm.e_comm
      rw [ψ.base] at h
      exact h
    rw [← key, Category.assoc, h1, one_left_eq, one_left_eq, Category.assoc, hunit]
    simp only [Over.mk_hom, ← Category.assoc, hfa]
    simp [spMap]
  · rw [Category.assoc, hpb.lift_snd, Over.w]
    simp only [Over.mk_hom]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2

end GlobalTheory.TanLiftPull
end
end
