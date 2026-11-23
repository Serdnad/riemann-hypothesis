module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2687
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2745
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1171
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1100
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2713
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle289
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2746
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DivMemOfForallPowSuccDivPowMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.glued_section_generic_value_nonvanishing : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (K : Type) [Field K] (ξ : Sp K ⟶ S)
    (V : S.Opens) (κ : Type) (N : κ → S.Opens) (s : ∀ k, LocSec G L (N k)) (s' : LocSec G L V)
    (v : SecM G L 1 (Over.mk ξ)) (hN : ∀ k, N k ≤ V), (⨆ k, N k) = V →
    (∀ k i, resG _ (fun _ hx => ⟨hx.1, hN k hx.2⟩ : L.U i ⊓ G.hom ⁻¹ᵁ N k ≤ L.U i ⊓ G.hom ⁻¹ᵁ V) (s' i) = s k i) →
    (∀ k, GenIs ξ (s k) v) → (∀ k, FibNz (s k) (N k)) → (Nonempty κ → GenIs ξ s' v) ∧ FibNz s' V := by
  first | exact @GlobalTheory.UMin.ThBdl.Glued.glued | exact GlobalTheory.UMin.ThBdl.Glued.glued | (intros; apply GlobalTheory.UMin.ThBdl.Glued.glued <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_glued_lineBundleSection_over_cover : ∀ (S : Scheme.{0}) (G : Over S) (L : LB G.left) (V : S.Opens) (κ : Type) (N : κ → S.Opens)
    (s : ∀ k, LocSec G L (N k)) (hN : ∀ k, N k ≤ V), (⨆ k, N k) = V → (∀ k, IsLocSec (s k)) →
    (∀ k k' i, resG _ (fun _ hx => ⟨hx.1, hx.2.1⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N k ⊓ N k') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N k) (s k i) =
      resG _ (fun _ hx => ⟨hx.1, hx.2.2⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N k ⊓ N k') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N k') (s k' i)) →
    ∃ s' : LocSec G L V, IsLocSec s' ∧ ∀ k i,
      resG _ (fun _ hx => ⟨hx.1, hN k hx.2⟩ : L.U i ⊓ G.hom ⁻¹ᵁ N k ≤ L.U i ⊓ G.hom ⁻¹ᵁ V) (s' i) = s k i := by
  first | exact @GlobalTheory.UMin.ThBdl.locSec_glue | exact GlobalTheory.UMin.ThBdl.locSec_glue | (intros; apply GlobalTheory.UMin.ThBdl.locSec_glue <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lineBundleLocalSection_eq_of_generic_fibre : ∀ (S : Scheme.{0}) [IsIntegral S] (G : Over S) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ (L : LB G.left) (K : Type) [Field K] (ξ : Sp K ⟶ S), Set.range ξ = {genericPoint S} →
    ∀ (N N' : S.Opens) (s : LocSec G L N) (s' : LocSec G L N') (v : SecM G L 1 (Over.mk ξ)),
      GenIs ξ s v → GenIs ξ s' v → ∀ i,
        resG _ (fun _ hx => ⟨hx.1, hx.2.1⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N ⊓ N') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N) (s i) =
          resG _ (fun _ hx => ⟨hx.1, hx.2.2⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N ⊓ N') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N') (s' i) := by
  first | exact @GlobalTheory.UMin.ThBdl.locSec_eq_of_genIs | exact GlobalTheory.UMin.ThBdl.locSec_eq_of_genIs | (intros; apply GlobalTheory.UMin.ThBdl.locSec_eq_of_genIs <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyVals.PolOpen

section
open TopologicalSpace ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} {φ : A'.left ⟶ A.left}
  {L : LB A.left} {L' : LB A'.left}

theorem relAmple_pull_of_affine (h : IsPullback φ A'.hom A.hom f) (hL : L.IsLB) (hL' : L'.IsLB)
    {w : LB.Iso L' (L.pull φ)} (hw : PGen w)
    (hf : ∀ U' : S'.Opens, IsAffineOpen U' → ∃ U : S.Opens, IsAffineOpen U ∧ U' ≤ f ⁻¹ᵁ U) (hA : RelAmple A L) :
    RelAmple A' L' := by
  intro U' hU'
  obtain ⟨U, hU, le⟩ := hf U' hU'
  obtain ⟨N, hN, M, s, hcov, hs⟩ := hA U hU
  have le' : A'.hom ⁻¹ᵁ U' ≤ φ ⁻¹ᵁ (A.hom ⁻¹ᵁ U) := fun y hy => (congrArg (fun q => q y ∈ U) h.w).mpr (le hy)
  let ψ := φ.resLE (A.hom ⁻¹ᵁ U) (A'.hom ⁻¹ᵁ U') le'
  have hψ : ψ ≫ (A.hom ⁻¹ᵁ U).ι = (A'.hom ⁻¹ᵁ U').ι ≫ φ := Scheme.Hom.resLE_comp_ι φ le'
  have H : IsPullback ψ (A'.hom ∣_ U') (A.hom ∣_ U) (f.resLE U U' le) := by
    refine IsPullback.of_right ?_ ?_ (isPullback_morphismRestrict A.hom U).flip
    · rw [hψ, Scheme.Hom.resLE_comp_ι]
      exact (isPullback_morphismRestrict A'.hom U').flip.paste_horiz h
    · rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hψ, Category.assoc, h.w, Category.assoc,
        Scheme.Hom.resLE_comp_ι, ← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  have : IsAffine U := hU
  have : IsAffine U' := hU'
  have : IsAffineHom ψ := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  have hP := linComb_isLB L hL (K := Fin N) (fun _ => (A.hom ⁻¹ᵁ U).ι) (fun _ => 1)
  have hP' := linComb_isLB L' hL' (K := Fin N) (fun _ => (A'.hom ⁻¹ᵁ U').ι) (fun _ => 1)
  obtain ⟨W, hW⟩ := LBIso.chartPull (chartPullId _) (chartPullOut L (fun _ : Fin N => (A.hom ⁻¹ᵁ U).ι) (fun _ => 1) ψ _
    fun _ => hψ.symm) (iso_linComb hw (fun _ : Fin N => (A'.hom ⁻¹ᵁ U').ι) (fun _ => 1))
  choose s' hs' using fun i => sec_pull_down ((isGen_iff W).1 hW) hP hP' (s i)
  have loc : ∀ i, nonzeroLocus (M := powOver A' L' U' N) (s' i) = ψ ⁻¹ᵁ nonzeroLocus (s i) := fun i => by
    ext y
    refine (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.mem_nonzeroLocus _ y).trans
      (Iff.trans ⟨fun ⟨k, hk, u⟩ => ?_, fun ⟨j, hj, u⟩ => ?_⟩
        (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.mem_nonzeroLocus _ (ψ y)).symm)
    · obtain ⟨j, hj⟩ := exists_chart hP (ψ y)
      have e := hs' i _ (𝟙 _) y j k hj hk
      rw [Category.id_comp, gs_stalkMap ψ y _ hj] at e
      exact ⟨j, hj, (isUnit_map_iff (ψ.stalkMap y).hom _).1 ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))⟩
    · obtain ⟨k, hk⟩ := exists_chart hP' y
      have e := hs' i _ (𝟙 _) y j k hj hk
      rw [Category.id_comp] at e
      exact ⟨k, hk, isUnit_of_mul_isUnit_right ((congrArg IsUnit ((gs_stalkMap ψ y _ hj _).symm.trans e)).mp (u.map _))⟩
  refine ⟨N, hN, M, s', ?_, fun i => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (show ψ y ∈ ⨆ i, nonzeroLocus (s i) by rw [hcov]; trivial)
    exact Opens.mem_iSup.2 ⟨i, by rw [loc]; exact hi⟩
  obtain ⟨haff, r, hr, hsurj⟩ := hs i
  refine ⟨by rw [loc]; exact haff.preimage ψ, fun j => (ψ.appLE _ _ (loc i).le).hom (r j), fun j k => fn_ext fun y hy => ?_, ?_⟩
  · obtain ⟨l, hl⟩ := exists_chart hP (ψ y)
    have hm : ψ y ∈ nonzeroLocus (s i) ⊓ (powOver A L U N).U l := ⟨(loc i).le hy.1, hl⟩
    have e := congrArg (gs ψ y _) (hr j l)
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
    have e₁ := hs' j _ (𝟙 _) y l k hl hy.2
    have e₂ := hs' i _ (𝟙 _) y l k hl hy.2
    rw [Category.id_comp] at e₁ e₂
    have e₃ := (gw W (𝟙 _) y l k).mul_right_inj.1 (e₁.symm.trans (e.trans ((congrArg _ e₂).trans (mul_left_comm _ _ _))))
    refine (gs_res _ y _ hy _).trans (e₃.trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_res _ y _ hy _).trans ((gs_appLE ψ _ _ _ (𝟙 _) y hy.1 _).trans (by rw [Category.id_comp]))) (gs_res _ y _ hy _)))))
  · have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := nonzeroLocus (s i)) le_top le_top
      (UY := nonzeroLocus (M := powOver A' L' U' N) (s' i)) (by rw [loc]; simp)).1
      (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) haff)
    rw [← RingHom.range_eq_top, ← top_le_iff, ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po,
      Subring.closure_le]
    rintro _ (⟨d, rfl⟩ | ⟨c, rfl⟩)
    · obtain ⟨p, rfl⟩ := hsurj d
      refine ⟨MvPolynomial.map ((f.resLE U U' le).appLE ⊤ ⊤ le_top).hom p, ?_⟩
      rw [MvPolynomial.eval₂Hom_map_hom]
      exact ((congrArg (fun q => MvPolynomial.eval₂Hom q _ p) (congrArg CommRingCat.Hom.hom po.w.symm)).trans
        (MvPolynomial.map_eval₂Hom _ _ _ p).symm)
    · exact ⟨MvPolynomial.C c, MvPolynomial.eval₂Hom_C _ _ _⟩

end

theorem mem_abLocus_of_open {S S' : Scheme.{0}} (j : S' ⟶ S) [IsOpenImmersion j] (G : Over S) (s : S')
    (hs : s ∈ abLocus ((Over.pullback j).obj G)) : j s ∈ abLocus G := by
  rintro K _ _ t ⟨p, hp⟩
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have hr : Set.range t ⊆ Set.range j := by
    rintro _ ⟨q, rfl⟩
    exact ⟨s, by rw [Subsingleton.elim q p, hp]⟩
  let t' := IsOpenImmersion.lift j t hr
  have ht : t' ≫ j = t := IsOpenImmersion.lift_fac _ _ _
  have hp' : t' p = s := j.isOpenEmbedding.injective ((congrArg (fun q => q p) ht).trans hp)
  have h₁ : IsProper (pullback.snd (pullback.snd G.hom j) t') := hs K t' ⟨p, hp'⟩
  have h₂ := (IsPullback.of_hasPullback (pullback.snd G.hom j) t').paste_horiz (IsPullback.of_hasPullback G.hom j)
  rw [ht] at h₂
  rw [← h₂.isoPullback_inv_snd]
  infer_instance

theorem polOnAb_open {S S' : Scheme.{0}} (j : S' ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] (L : LB G.left)
    (hL : L.IsLB) (h : PolOnAb G L) : PolOnAb ((Over.pullback j).obj G) (L.pull (pullback.fst G.hom j)) := by
  intro W' hW'
  letI : (Over.pullback j).Monoidal := (Over.instBraidedPullback (f := j)).toMonoidal
  letI : GrpObj ((Over.pullback j).obj G) := Functor.grpObjObj (F := Over.pullback j)
  letI : (Over.pullback W'.ι).Monoidal := (Over.instBraidedPullback (f := W'.ι)).toMonoidal
  letI : GrpObj ((Over.pullback W'.ι).obj ((Over.pullback j).obj G)) :=
    Functor.grpObjObj (F := Over.pullback W'.ι)
  obtain ⟨ha, hK⟩ := h (j ''ᵁ W') (by
    rintro _ ⟨s, hs, rfl⟩
    exact mem_abLocus_of_open j G s (hW' hs))
  have hr : Set.range (W'.ι ≫ j) ⊆ Set.range (j ''ᵁ W').ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    exact ⟨y.1, y.2, rfl⟩
  let e := IsOpenImmersion.lift (j ''ᵁ W').ι (W'.ι ≫ j) hr
  have he : e ≫ (j ''ᵁ W').ι = W'.ι ≫ j := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (e ≫ (j ''ᵁ W').ι) := by rw [he]; infer_instance
  have : IsOpenImmersion e := IsOpenImmersion.of_comp e (j ''ᵁ W').ι
  have p₀ := isGrpPullback_pullback G (j ''ᵁ W').ι
  have p₁ := (isGrpPullback_pullback ((Over.pullback j).obj G) W'.ι).comp (isGrpPullback_pullback G j)
  have w₁ := p₁.1.w.trans ((congrArg _ he.symm).trans (Category.assoc _ _ _).symm)
  have p₂ := IsGrpPullback.cancel p₀ (p₁.congr he.symm (p₀.1.lift_fst _ _ w₁).symm) (p₀.1.lift_snd _ _ w₁)
  have hL₀ := pull_isLB hL (pullback.fst G.hom (j ''ᵁ W').ι)
  have hL₁ := pull_isLB (pull_isLB hL (pullback.fst G.hom j)) (pullback.fst ((Over.pullback j).obj G).hom W'.ι)
  obtain ⟨w, hw⟩ : LBIso ((L.pull (pullback.fst G.hom j)).pull (pullback.fst ((Over.pullback j).obj G).hom W'.ι))
      ((L.pull (pullback.fst G.hom (j ''ᵁ W').ι)).pull (p₀.1.lift _ _ w₁)) := by
    refine (CechPic.cls_eq_iff hL₁ (pull_isLB hL₀ _)).1 ?_
    rw [CechPic.cls_pull (pull_isLB hL _), CechPic.cls_pull (pull_isLB hL _), CechPic.cls_pull hL, CechPic.cls_pull hL]
    exact (CechPic.pull_comp _ _ _).symm.trans ((congrArg (fun q => CechPic.pull q _) (p₀.1.lift_fst _ _ w₁).symm).trans
      (CechPic.pull_comp _ _ _))
  exact ⟨relAmple_pull_of_affine p₂.1 hL₀ hL₁ ((isGen_iff w).1 hw)
    (fun U' hU' => ⟨e ''ᵁ U', hU'.image_of_isOpenImmersion e, fun y hy => ⟨y, hy, rfl⟩⟩) ha,
    kTriv_pull p₂ hL₀ hL₁ ((isGen_iff w).1 hw) hK⟩

theorem polOnAb_affine : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (W : S.Opens) (hW : IsAffineOpen W),
    IsOpen (abLocus G) → PolOnAb G L.L → PolOnAb (KeyVals.bG G hW.fromSpec) (KeyVals.bL L hW.fromSpec).L :=
  fun _ G _ _ L _ hW _ h => polOnAb_open hW.fromSpec G L.L L.isLB h

end GlobalTheory.KeyVals.PolOpen

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyVals.Vec

open TopologicalSpace GlobalTheory.LieVB GlobalTheory.Conormal GlobalTheory.VB
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.DualPull (appLE_resG resG_appLE)
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO LieG)

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {k : Type} [CommRing k] {x : Sp k ⟶ S}
  {G₁ : Over (Sp k)} [GrpObj G₁] {φ : G₁.left ⟶ G.left}

def form (h : IsGrpPullback G₁ G x φ) (p : LieG G₁) :
    (Scheme.Modules.pullback x).obj (omega G) ⟶ GlobalTheory.structureModule (Sp k) :=
  omegaBase h ≫ cotMap p.1 (epsZero_comp p) ≫ (epsIso k).hom

theorem form_app (h : IsGrpPullback G₁ G x φ) (p : LieG G₁) {T : (Sp k).Opens}
    (s : Γ((Scheme.Modules.pullback x).obj (omega G), T)) :
    (form h p).app T s = dualApp (tangent p) le_top ((omegaBase h).app T s) := rfl

theorem pre_le (h : IsGrpPullback G₁ G x φ) (p : LieG G₁) {V : S.Opens} {W : G.left.Opens}
    (hW : V ≤ unitSec G ⁻¹ᵁ W) {T : (Sp k).Opens} (hT : T ≤ x ⁻¹ᵁ V) :
    (specO k (DualNumber k)).hom ⁻¹ᵁ T ≤ p.1.left ⁻¹ᵁ φ ⁻¹ᵁ W :=
  preimage_le_of_lieG p (le_of_sq (unitSec_comp h) hW hT)

theorem form_dUnit (h : IsGrpPullback G₁ G x φ) (p : LieG G₁) {V : S.Opens} {W : G.left.Opens}
    (hW : V ≤ unitSec G ⁻¹ᵁ W) {T : (Sp k).Opens} (hT : T ≤ x ⁻¹ᵁ V) (f : Γ(G.left, W))
    (a b : Γ(Sp k, T))
    (e : ((p.1.left ≫ φ).appLE W _ (pre_le h p hW hT) f :
        Γ((specO k (DualNumber k)).left, (specO k (DualNumber k)).hom ⁻¹ᵁ T)) =
      (specO k (DualNumber k)).hom.appLE T _ le_rfl a +
        (specO k (DualNumber k)).hom.appLE T _ le_rfl b * resG _ le_top (epsFn k)) :
    (form h p).app T (pullbackSections x (omega G) hT (dUnit G hW f)) = b := by
  have hV : T ≤ sec (epsZero k) ⁻¹ᵁ (specO k (DualNumber k)).hom ⁻¹ᵁ T :=
    (le_preimage_of_comp (sec_hom (epsZero k))).2 le_rfl
  rw [form_app, omegaBase_dUnit h hW hT (le_of_sq (unitSec_comp h) hW hT) le_rfl]
  exact dualApp_tangent_dUnit p _ _ hV le_rfl (pre_le h p hW hT) a b
    ((appLE_appLE rfl _ _ _ f).trans e)

variable {k' : Type} [CommRing k'] (r : k →+* k') (F : DualNumber k →+* DualNumber k')

theorem spMap_comp_hom (hF : ∀ a, F (algebraMap k _ a) = algebraMap k' _ (r a)) :
    spMap F ≫ (specO k (DualNumber k)).hom = (specO k' (DualNumber k')).hom ≫ spMap r := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext hF)

theorem spMap_epsFn (he : F DualNumber.eps = DualNumber.eps) :
    (spMap F).appLE ⊤ ⊤ (le_preimage_top _ _) (epsFn k) = epsFn k' := by
  refine congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom F)) DualNumber.eps).symm.trans ?_
  exact congrArg (Scheme.ΓSpecIso (.of (DualNumber k'))).inv.hom he

theorem epsZero_spMap (hF : ∀ a, F (algebraMap k _ a) = algebraMap k' _ (r a))
    (he : F DualNumber.eps = DualNumber.eps) :
    sec (epsZero k') ≫ spMap F = spMap r ≫ sec (epsZero k) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  change (F a).fst = r a.fst
  have : a = algebraMap k _ a.fst + algebraMap k _ a.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  conv_lhs => rw [this, map_add (f := _), map_mul, hF, hF, he]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

variable {G₂ : Over (Sp k')} [GrpObj G₂] {ψ : G₂.left ⟶ G.left}

theorem form_baseChange [QuasiSeparated G.hom] (hF : ∀ a, F (algebraMap k _ a) = algebraMap k' _ (r a))
    (he : F DualNumber.eps = DualNumber.eps) (h₁ : IsGrpPullback G₁ G x φ) (h₂ : IsGrpPullback G₂ G (spMap r ≫ x) ψ)
    (p : LieG G₁) (q : LieG G₂) (hq : q.1.left ≫ ψ = spMap F ≫ p.1.left ≫ φ)
    {V : S.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V) (h' : ⊤ ≤ (spMap r ≫ x) ⁻¹ᵁ V) (s : Γ(omega G, V)) :
    ((form h₂ q).app ⊤ (pullbackSections _ (omega G) h' s) : Γ(Sp k', ⊤)) =
      (spMap r).appLE ⊤ ⊤ (le_preimage_top _ _)
        ((form h₁ p).app ⊤ (pullbackSections x (omega G) h s) : Γ(Sp k, ⊤)) := by
  have key (y : (⊤ : (Sp k').Opens)) : ∃ T' : (Sp k').Opens, y.1 ∈ T' ∧
      resG (Sp k') (le_top : T' ≤ ⊤) ((form h₂ q).app ⊤ (pullbackSections _ (omega G) h' s) : Γ(Sp k', ⊤)) =
      resG (Sp k') (le_top : T' ≤ ⊤) ((spMap r).appLE ⊤ ⊤ (le_preimage_top _ _)
        ((form h₁ p).app ⊤ (pullbackSections x (omega G) h s) : Γ(Sp k, ⊤))) := by
    obtain ⟨U, W, hU, hle, c⟩ := GlobalTheory.Conormal.exists_isChart (sec_hom (MonObj.one (X := G))) (V := V)
      (x := x (spMap r y.1)) (h trivial)
    obtain ⟨T, hT, hyT, hTU⟩ := QCoh.exists_affine_mem_le (U := x ⁻¹ᵁ U) (spMap r y.1) hU
    obtain ⟨f, hf⟩ := c.d_surjective (sec_hom (MonObj.one (X := G))) (resM _ hle s)
    have hf' : dUnit G c.le f = resM (omega G) hle s := hf
    have hTU' : spMap r ⁻¹ᵁ T ≤ (spMap r ≫ x) ⁻¹ᵁ U := (spMap r).preimage_mono hTU
    obtain ⟨⟨a, b⟩, e⟩ := (bijective_add_mul_epsFn k T hT).2
      ((p.1.left ≫ φ).appLE W _ (pre_le h₁ p c.le hTU) f)
    have e₁ := form_dUnit h₁ p c.le hTU f a b e.symm
    have kk : (specO k' (DualNumber k')).hom ⁻¹ᵁ spMap r ⁻¹ᵁ T ≤
        spMap F ⁻¹ᵁ (specO k (DualNumber k)).hom ⁻¹ᵁ T :=
      (le_preimage_of_comp (spMap_comp_hom r F hF)).2 le_rfl
    have kk' : (specO k' (DualNumber k')).hom ⁻¹ᵁ spMap r ⁻¹ᵁ T ≤
        ((specO k' (DualNumber k')).hom ≫ spMap r) ⁻¹ᵁ T := le_rfl
    have n (z : Γ(Sp k, T)) : (spMap F).appLE _ _ kk
        ((specO k (DualNumber k)).hom.appLE T _ le_rfl z) =
        (specO k' (DualNumber k')).hom.appLE _ _ le_rfl ((spMap r).appLE T _ le_rfl z) :=
      (appLE_appLE (spMap_comp_hom r F hF) _ _ kk' z).trans (appLE_appLE rfl _ _ kk' z).symm
    have n' : (spMap F).appLE _ _ kk (resG _ le_top (epsFn k)) =
        resG _ le_top (epsFn k') :=
      (appLE_resG _ _ _ _).trans ((resG_appLE _ le_top (le_preimage_top _ _) _).symm.trans
        (congrArg _ (spMap_epsFn F he)))
    have e₂ := form_dUnit h₂ q c.le hTU' f ((spMap r).appLE T _ le_rfl a)
      ((spMap r).appLE T _ le_rfl b) (by
        refine (appLE_appLE hq.symm (pre_le h₁ p c.le hTU) kk _ f).symm.trans ?_
        refine (congrArg ((spMap F).appLE _ _ kk) e.symm).trans ?_
        refine (map_add _ _ _).trans ?_
        exact congrArg₂ (· + ·) (n a) ((map_mul _ _ _).trans (congrArg₂ (· * ·) (n b) n')))
    rw [hf', QCoh.pullbackSections_res] at e₁ e₂
    refine ⟨spMap r ⁻¹ᵁ T, hyT, ?_⟩
    refine (app_resM (form h₂ q) le_top _).symm.trans ?_
    rw [QCoh.res_pullbackSections, e₂, ← e₁]
    refine .trans ?_ ((appLE_resG (spMap r) (le_top : T ≤ ⊤) le_rfl _).trans
      (resG_appLE (spMap r) le_top (le_preimage_top _ _) _).symm)
    refine congrArg _ ?_
    refine .trans ?_ (app_resM (form h₁ p) le_top _)
    rw [QCoh.res_pullbackSections]
  choose T hT hs using key
  exact LB.fun_ext_of_cover T (fun _ => le_top) (fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hT _⟩) hs

theorem exists_lieG (hF : ∀ a, F (algebraMap k _ a) = algebraMap k' _ (r a))
    (he : F DualNumber.eps = DualNumber.eps) (h₁ : IsGrpPullback G₁ G x φ) (h₂ : IsGrpPullback G₂ G (spMap r ≫ x) ψ)
    (p : LieG G₁) : ∃ q : LieG G₂, q.1.left ≫ ψ = spMap F ≫ p.1.left ≫ φ := by
  have w : (spMap F ≫ p.1.left ≫ φ) ≫ G.hom = (specO k' (DualNumber k')).hom ≫ spMap r ≫ x := by
    rw [Category.assoc, Category.assoc, h₁.1.w, ← Category.assoc p.1.left, Over.w p.1, ← Category.assoc,
      ← Category.assoc]
    exact congrArg (· ≫ x) (spMap_comp_hom r F hF)
  let q : specO k' (DualNumber k') ⟶ G₂ :=
    Over.homMk (h₂.1.lift _ (specO k' (DualNumber k')).hom w) (h₂.1.lift_snd _ _ _)
  have hq : q.left ≫ ψ = spMap F ≫ p.1.left ≫ φ := h₂.1.lift_fst _ _ _
  have ht : (toUnit (specO k' k')).left = 𝟙 (Sp k') := by
    rw [Over.toUnit_left]
    exact Spec.map_id _
  refine ⟨⟨q, Over.OverMorphism.ext (h₂.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))⟩, hq⟩
  rw [Over.comp_left, Over.comp_left, ht, Category.assoc, hq, Category.assoc]
  have e : sec (epsZero k') ≫ spMap F ≫ p.1.left ≫ φ = (spMap r ≫ x) ≫ unitSec G := by
    rw [← Category.assoc, epsZero_spMap r F hF he, Category.assoc, ← Category.assoc (sec _), sec_epsZero_comp,
      unitSec_comp h₁, Category.assoc]
  exact e.trans ((unitSec_comp h₂).symm.trans (Category.id_comp _).symm)

theorem dual_vec : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (c : VB.Chart (LieVB.omega G) g) (R R' : Type)
    [CommRing R] [CommRing R'] (ξ : Sp R ⟶ S) (r : R →+* R') (ξ' : Sp R' ⟶ S) (y : Fin g → (epsR R ⟶ KeyVals.bG G ξ))
    (y' : Fin g → (epsR R' ⟶ KeyVals.bG G ξ')), spMap r ≫ ξ = ξ' → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom →
    KeyVals.IsDual c ξ y → KeyVals.IsDual c ξ' y' →
    ∀ F : DualNumber R →+* DualNumber R', (∀ a, F (algebraMap R _ a) = algebraMap R' _ (r a)) →
      F DualNumber.eps = DualNumber.eps → ∀ j, (y' j).left ≫ pullback.fst G.hom ξ' = spMap F ≫ (y j).left ≫ pullback.fst G.hom ξ := by
  rintro S G _ _ g c R R' _ _ ξ r _ y y' rfl hG - ⟨hc, hy⟩ ⟨hc', hy'⟩ F hF he j
  obtain ⟨p, hp, hp'⟩ := hy j
  obtain ⟨q, hq, hq'⟩ := hy' j
  have h₁ := isGrpPullback_pullback G ξ
  have h₂ := isGrpPullback_pullback G (spMap r ≫ ξ)
  obtain ⟨w, hw⟩ := exists_lieG r F hF he h₁ h₂ p
  have hfr : VB.IsFrame (pfr c (spMap r ≫ ξ) hc') := by
    have k₁ := ((c.isFrame.pullback (spMap r ≫ ξ)).res hc').map_iso (omegaBase h₂)
    have k₂ (b : Fin g) : resM _ hc' (pullbackSections (spMap r ≫ ξ) (omega G) le_rfl (c.e b)) =
        pullbackSections (spMap r ≫ ξ) (omega G) hc' (c.e b) := QCoh.res_pullbackSections _ _ _ _ _
    simp only [k₂] at k₁
    exact k₁
  obtain rfl : w = q := tangent_injective R' _ (hfr.dual_ext le_rfl fun b => by
    rw [resM_self]
    refine (form_baseChange r F hF he h₁ h₂ p w hw hc hc' (c.e b)).trans ?_
    refine .trans (congrArg ((spMap r).appLE ⊤ ⊤ (le_preimage_top _ _)) (hp' b)) (.trans ?_ (hq' b).symm)
    exact (apply_ite _ _ _ _).trans (if_congr Iff.rfl
      (map_one ((spMap r).appLE ⊤ ⊤ (le_preimage_top _ _)).hom) (map_zero ((spMap r).appLE ⊤ ⊤ (le_preimage_top _ _)).hom)))
  rw [← hq, ← hp]
  exact hw

end GlobalTheory.KeyVals.Vec

end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem genPt_mem_cover : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) (Ω : Type) [CommRing Ω] [IsDomain Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ G.left), x' ≫ G.hom = spMap φ → ∀ (c : R), φ c ≠ 0 → ∀ (J : Type) (W : J → G.left.Opens), ⨆ i, W i = G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 → ∃ i, ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x') ⁻¹ᵁ W i := by
  intro R _ G Ω _ _ φ x' hx c hc J W hW
  set K := FractionRing Ω
  have hK : (⊤ : (Sp K).Opens) ≤ (spMap (algebraMap Ω K) ≫ x') ⁻¹ᵁ (⨆ i, W i) := by
    rw [hW, ← Scheme.Hom.comp_preimage]
    rw [Category.assoc, hx]
    simp only [GlobalTheory.HeatV.bo, Scheme.affineBasicOpen_coe, Scheme.preimage_basicOpen_top]
    rw [Scheme.basicOpen_of_isUnit]
    have e : spMap (algebraMap Ω K) ≫ spMap φ = Spec.map (CommRingCat.ofHom ((algebraMap Ω K).comp φ)) := by
      simp only [spMap, ← Spec.map_comp]; rfl
    rw [e]
    have h1 := congrArg (fun f => f.hom c)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ((algebraMap Ω K).comp φ)))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1
    rw [← h1]
    refine IsUnit.map _ ?_
    refine isUnit_iff_ne_zero.mpr ?_
    intro h0
    exact hc ((IsFractionRing.injective Ω K) (by simpa using h0))
  obtain ⟨p⟩ : Nonempty (Sp K) := inferInstance
  have hp := hK (Set.mem_univ p)
  obtain ⟨i, hi⟩ := (TopologicalSpace.Opens.mem_iSup).mp hp
  refine ⟨i, fun q _ => ?_⟩
  have : q = p := Subsingleton.elim _ _
  subst this
  exact hi

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem _root_.GlobalTheory.T.zarhin_polarisation_kernel_le_unit_kernel : ∀ (h M d : ℕ), 0 < d → ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (z : SiegPre (8 * h) M (zetaAway M) t) (act : GlobalTheory.ZarhinFam.ord d → (z.A ⟶ z.A)) (inc : c.A ⟶ z.A) (pr : z.A ⟶ c.A), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → z.Principal → IsRAct z.A act → Adj z.A z.P (GlobalTheory.ZarhinFam.bar d) act → IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 c.A → pr ≫ inc = act (GlobalTheory.ZarhinFam.idem d) → LBIso c.P (z.P.pull (inc ⊗ₘ inc).left) → ∀ (T : Over S) (x : T ⟶ c.A), (∃ u : (c.P.pull (lift (snd c.A T ≫ x) (fst c.A T)).left).Gen, u.IsGen) → x ≫ inc ≫ act (GlobalTheory.ZarhinFam.polUnit d) = 1 := by
  first | (exact @GlobalTheory.ZarhinFam.ker_pol_le_ker_polUnit) | (exact GlobalTheory.ZarhinFam.ker_pol_le_ker_polUnit) | (intros; apply GlobalTheory.ZarhinFam.ker_pol_le_ker_polUnit  <;> assumption)
end
