module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle673
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3285
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2785
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3310
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1402
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1211
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle046
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle183
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2912
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2795
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3311
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2682
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle621
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3312
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle090
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle172
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle054
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle065
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle044
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3313
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MetricIndep

theorem compactSpace_of_projOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : CompactSpace X := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  have : IsProper (i ≫ PSpace.str R m) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R m)

theorem int_sub_half {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    (L : Fin D → MLine p σ) {f v : CxPts p σ → ℝ} (hf : Intg L f) (hv : Intg L v) :
    Mix.int L (fun y => f y - v y / 2) = Mix.int L f - Mix.int L v / 2 := by
  unfold Mix.int
  rw [integral_sub hf.1 (hv.1.div_const 2), integral_sub hf.2 (hv.2.div_const 2),
    integral_div, integral_div]
  ring

theorem upd_cons {α : Type*} {n : ℕ} (a b : α) (L : Fin n → α) :
    Function.update (Fin.cons a L : Fin (n + 1) → α) 0 b = Fin.cons b L :=
  Fin.update_cons_zero (α := fun _ => α) a L b

theorem side_sub_side_addFn : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → ∀ (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), side N L ((M.addFn u hu).logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) - side (M.addFn u hu) L (N.logSec t) ((M.addFn u hu).logSec s) (divOfSec N.φ.isLB t ht) = side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) - side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  intro hP F _ X _ _ p σ e hproj hdim L M N s hs t ht hcod u hu
  have hσ : Function.Injective σ := σ.injective
  have hcont : Continuous u := continuous_iff_continuousAt.2 fun y => (hu y).continuousAt
  have hcomp : CompactSpace X := compactSpace_of_projOver hproj
  obtain ⟨-, -, -, hlog⟩ := GlobalTheory.Mix.SecNorm.logSec_basic F X p σ M s

  have hA : Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) ((M.addFn u hu).logSec s) =
      Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) (M.logSec s) -
        Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) u / 2 := by
    have hae : ∀ ε : ℤˣ, (M.addFn u hu).logSec s =ᵐ[part (Fin.cons N L : Fin (e + 1) → MLine p σ) ε]
        fun y => M.logSec s y - u y / 2 := by
      intro ε
      refine ae_iff.2 (measure_mono_null (fun y hy => ?_)
        (GlobalTheory.MixNull.part_compl_null F X p σ hσ hproj (e + 1) (Fin.cons N L) ε (nonzeroLocus s) hs))
      exact fun hy' => hy (hlog u hu y hy')
    have hf := GlobalTheory.T.log_norm_section_integrable_mixedChern_projective hP F X p σ (e + 1) hproj hdim (Fin.cons N L) M s hs
    have hv := (GlobalTheory.T.mixedChernMeasure_finite_integrable_projective hP F X p σ (e + 1) hproj hdim (Fin.cons N L)).2 u hcont
    rw [← int_sub_half _ hf hv]
    unfold Mix.int
    rw [integral_congr_ae (hae 1), integral_congr_ae (hae (-1))]

  have hB : Mix.int (Fin.cons (M.addFn u hu) L : Fin (e + 1) → MLine p σ) (N.logSec t) =
      Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) (N.logSec t) +
        Mix.int (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) (N.logSec t) := by
    obtain ⟨hrefl, -, -, -, haddFn, -⟩ := GlobalTheory.Mix.isom_calculus F X X p p σ (𝟙 X) (Category.id_comp p)
    have hpart : ∀ ε : ℤˣ, part (Fin.cons (M.addFn u hu) L : Fin (e + 1) → MLine p σ) ε =
        part (Fin.cons (M.tens (MLine.ofFun u hu)) L : Fin (e + 1) → MLine p σ) ε :=
      GlobalTheory.Mix.part_eq_of_isom F X p σ hproj (e + 1) _ _ fun i => Fin.cases (haddFn M u hu) (fun j => hrefl (L j)) i
    have h1 := GlobalTheory.T.log_norm_section_integrable_mixedChern_projective hP F X p σ (e + 1) hproj hdim (Fin.cons M L) N t ht
    have h2 := GlobalTheory.T.log_norm_section_integrable_mixedChern_projective hP F X p σ (e + 1) hproj hdim (Fin.cons (MLine.ofFun u hu) L) N t ht
    have hadd := GlobalTheory.T.mixedChernIntegral_additive_in_factor F X p σ hproj (e + 1) (Fin.cons M L : Fin (e + 1) → MLine p σ) 0 M
      (MLine.ofFun u hu) (N.logSec t)
    rw [upd_cons, upd_cons, upd_cons] at hadd
    replace hadd := hadd h1 h2
    rw [← hadd.2]
    unfold Mix.int
    rw [hpart, hpart]

  have hC : ∀ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L ((M.addFn u hu).logSec s) z =
      ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L (M.logSec s) z -
        ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L u z / 2 := by
    intro z
    by_cases h : (divOfSec N.φ.isLB t ht).mult z = 0
    · simp [h]
    have hz1 := CartierDiv.coheight_eq_one_of_mult_ne_zero h
    have hzs : z ∈ nonzeroLocus s := (hcod z hz1).resolve_right fun hzt =>
      (notMem_supp_divOfSec.2 hzt) (CartierDiv.mem_supp_of_mult_ne_zero h)
    have hdz := (GlobalTheory.FieldDimCoheight.coheight_eq_one_iff F X p e hproj hdim z).1 hz1
    obtain ⟨-, hcc, hnull, hlc⟩ := GlobalTheory.T.mixedChernForm_finite_integrable_pointClosure hP F X p σ hproj e L z hdz
    have hae : ∀ ε : ℤˣ, (fun y => (M.addFn u hu).logSec s (ptMap (closι z) rfl σ y)) =ᵐ[part (fun i => (L i).pull (closι z) rfl) ε]
        fun y => M.logSec s (ptMap (closι z) rfl σ y) - u (ptMap (closι z) rfl σ y) / 2 := by
      intro ε
      refine ae_iff.2 (measure_mono_null (fun y hy => ?_) (hnull (nonzeroLocus s) hzs ε))
      exact fun hy' => hy (hlog u hu _ hy')
    have hcyc : cycInt L ((M.addFn u hu).logSec s) z = cycInt L (M.logSec s) z - cycInt L u z / 2 := by
      have e2 := int_sub_half (fun i => (L i).pull (closι z) rfl) (hlc M s hzs) (hcc u hcont)
      unfold cycInt
      rw [← e2]
      unfold Mix.int
      rw [integral_congr_ae (hae 1), integral_congr_ae (hae (-1))]
    rw [hcyc]
    ring
  have hfs := CartierDiv.finite_support_mult (divOfSec N.φ.isLB t ht)
  have hsub : ∀ g : X → ℝ, (Function.support fun z => ((divOfSec N.φ.isLB t ht).mult z : ℝ) * g z).Finite :=
    fun g => hfs.subset fun z hz h0 => hz (by simp [h0])
  have hsum : ∑ᶠ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L ((M.addFn u hu).logSec s) z =
      ∑ᶠ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L (M.logSec s) z -
        (∑ᶠ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L u z) / 2 := by
    simp only [hC]
    rw [div_eq_mul_inv, finsum_mul]
    exact finsum_sub_distrib (hsub _) ((hsub (fun z => cycInt L u z)).subset fun z hz h0 => hz (by
      have h1 : ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L u z = 0 := h0
      simp only [h1, zero_div]))
  have hPL := GlobalTheory.T.poincareLelong_formula_section_projective hP F X p σ e hproj hdim L N t ht u hu
  simp only [side]
  rw [hA, hB, hsum]
  linarith

end GlobalTheory.MetricIndep
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SiegOpen

theorem isIso_stalkMap_of_isHom {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M M' : RatModel o Ω}
    {f : M'.Z ⟶ M.Z} (hf : M.IsHom M' (AlgHom.id o Ω) f) :
    IsDominant f ∧ IsIso (f.stalkMap (genericPoint M'.Z)) := by
  have hid : spMap (AlgHom.id o Ω).toRingHom ≫ M.pt = M.pt :=
    (congrArg (· ≫ M.pt) (Spec.map_id _)).trans (Category.id_comp _)
  have : IsDominant (M'.pt ≫ f) := by
    rw [hf, hid]; infer_instance
  have hd : IsDominant f := IsDominant.of_comp M'.pt f
  refine ⟨hd, ?_⟩
  have hz : f (genericPoint M'.Z) = genericPoint M.Z := GlobalTheory.apply_genericPoint_of_isDominant f
  have key : ∀ a, M'.stalkHom (genericPoint M'.Z) (f.stalkMap (genericPoint M'.Z) a) =
      M.stalkHom (f (genericPoint M'.Z)) a := by
    intro a
    obtain ⟨U, hzU, s, rfl⟩ := M.Z.presheaf.germ_exist a
    rw [Scheme.Hom.germ_stalkMap_apply]
    exact (M'.stalkHom_germ (U := f ⁻¹ᵁ U) hzU _).trans ((hf.valF_app ⟨_, hzU⟩ s).trans (M.stalkHom_germ hzU s).symm)
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun a b h => M.stalkHom_injective _ ?_, fun b => ?_⟩
  · rw [← key, ← key, h]
  · have hx : M'.stalkHom (genericPoint M'.Z) b ∈ M.O (f (genericPoint M'.Z)) := by
      rw [hz, M.O_genericPoint]; exact Algebra.mem_top
    obtain ⟨a, ha⟩ := (M.stalkEquiv _).surjective ⟨_, hx⟩
    refine ⟨a, M'.stalkHom_injective _ ?_⟩
    rw [key]
    exact congrArg Subtype.val ha

end GlobalTheory.SiegOpen

namespace GlobalTheory.SiegOpen

theorem level_openImmersion : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (m N : ℕ) (f : F.X ⟶ PSpace (cycAway n) N), ThAt F W P rig m f → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SysAt F W β S ρ u → QFin f → ∀ (Y X : RatModel o Ω) (q : Y.Z ⟶ F.X), LevAt F β u Y q → X.IsNm S.th → Geo.Tor.IsNormalScheme X.Z → ∃ d : Y.Z ⟶ X.Z, X.IsHom Y (AlgHom.id o Ω) d ∧ IsOpenImmersion d := by
  intro g n hg hn hodd F W hW P rig m N f hTh o Ω _ _ _ _ β S ρ u hSys hQ Y X q hLev hNm hXn

  have hYdiv : Y.HasDiv S.th := GlobalTheory.T.siegelThetaConstants_projectively_integral g n hg hn hodd F W hW P rig m N f hTh o Ω β S ρ u hSys Y (q ≫ f)
    hLev.1 (by rw [← Category.assoc, hLev.2.2.2.2, Category.assoc])

  obtain ⟨d, hd⟩ := hNm.exists_isHom (M' := Y) (φ := AlgHom.id o Ω) hYdiv (RatModel.isIntegrallyClosed_O hLev.1)
  refine ⟨d, hd, ?_⟩
  have hid : spMap (AlgHom.id o Ω).toRingHom ≫ X.pt = X.pt :=
    (congrArg (· ≫ X.pt) (Spec.map_id _)).trans (Category.id_comp _)
  have hYd : Y.pt ≫ d = X.pt := hd.trans hid

  obtain ⟨e, hSymE, hPe⟩ := GlobalTheory.T.exists_symmetric_theta_constants_eq_thetaMap_coords g n hg hn hodd F W hW P rig m N f hTh o Ω β S ρ u hSys
  have hSame := GlobalTheory.T.thetaConstant_pow_eq_unit_mul_symmetricFunction g n hg hn hodd F W hW P rig m N f hTh o Ω β S ρ u hSys X e hXn hNm.1 hSymE
  have hXe : X.HasDiv e := fun z => by
    obtain ⟨i, hi⟩ := hNm.1 z
    obtain ⟨j, hj, -⟩ := hSame z i hi
    exact ⟨j, hj⟩
  obtain ⟨hX, hXs, hXP⟩ := GlobalTheory.T.exists_projSpace_map_of_tuple_hasDivisor o Ω (cycAway n) β X N e hXe
  have hfs : f ≫ PSpace.str (cycAway n) N = F.s := hTh.2.2.2.2.2.2.2.1

  have heq : d ≫ hX = q ≫ f := by
    refine GlobalTheory.T.eq_of_same_generic_projective_coords (cycAway n) N Y.Z (Y.s ≫ spMap β) (d ≫ hX) (q ≫ f) Ω Y.pt e ?_ ?_ Y.gen ?_ ?_
    · rw [Category.assoc, hXs, ← Category.assoc, hd.inducedModelMorphism_comp_structureMap]
    · rw [Category.assoc, hfs, hLev.2.2.2.1]
    · rw [← Category.assoc, hYd]; exact hXP
    · rw [← Category.assoc, hLev.2.2.2.2]; exact hPe _ rfl

  have : LocallyOfFiniteType F.s := by
    haveI := F.smooth
    haveI : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
    infer_instance
  have : LocallyOfFiniteType (f ≫ PSpace.str (cycAway n) N) := by rw [hfs]; assumption
  haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (PSpace.str (cycAway n) N)
  haveI : LocallyQuasiFinite f :=
    LocallyQuasiFinite.of_finite_preimage_singleton f (GlobalTheory.SiegMin.finite_preimage_singleton_of_qFin f hQ)
  haveI : IsFinite q := hLev.2.1
  haveI : LocallyQuasiFinite (d ≫ hX) := by rw [heq]; infer_instance
  haveI : LocallyQuasiFinite d := LocallyQuasiFinite.of_comp d hX

  haveI := Y.sep
  haveI := Y.qc
  haveI := Y.lft
  haveI := X.sep
  haveI : IsSeparated (d ≫ X.s) := by rw [hd.inducedModelMorphism_comp_structureMap]; infer_instance
  haveI : QuasiCompact (d ≫ X.s) := by rw [hd.inducedModelMorphism_comp_structureMap]; infer_instance
  haveI : LocallyOfFiniteType (d ≫ X.s) := by rw [hd.inducedModelMorphism_comp_structureMap]; infer_instance
  haveI : IsSeparated d := IsSeparated.of_comp d X.s
  haveI : QuasiCompact d := QuasiCompact.of_comp d X.s
  haveI : LocallyOfFiniteType d := locallyOfFiniteType_of_comp d X.s
  obtain ⟨h1, h2⟩ := isIso_stalkMap_of_isHom hd

  exact GlobalTheory.isOpenImmersion_of_quasiFinite_of_isIso_stalkMap d fun z => (hXn z).2

end GlobalTheory.SiegOpen
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LocalPull



theorem exists_pelUnif_pull : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base R → GlobalTheory.Mum.Base V → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (θ : R →+* V), IsLocalHom θ → ∀ f : R, θ f ≠ 0 → (∀ y, PsiUnitOn P.D.toPre y (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))) → ∃ (t' : SAB H (Sp V)) (P' : PELUnif (maximalIdeal V) t') (hD : IsPullDeg θ P.D.toPre P'.D.toPre), Nonempty (SABMap t' t (spMap θ)) ∧ (∀ (x : 𝓞 E) y, hD.xe (x • y) = x • hD.xe y) ∧ (letI := H.starRing; ∀ x, P'.oD.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf θ)).map (P.oD.onB.act x)) := by
  intro E _ _ _ H R V _ _ _ _ _ _ hR hV t P θ hθ f hf hψ
  letI := H.starRing
  obtain ⟨-, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  have aR := hR.1
  have aV := hV.1
  have hI : (maximalIdeal R).map θ ≤ maximalIdeal V :=
    Ideal.map_le_iff_le_comap.2 fun a ha => (map_mem_nonunits_iff θ a).2 ha
  obtain ⟨PP', cub, sym, adj, prim, m₁, hm₁⟩ := sabPull CubePf.cubePull (spMap θ) t
  let t' : SAB H (Sp V) := ⟨(Over.pullback (spMap θ)).obj t.G, IsSemiAbelian.pullback _ t.G t.semi,
    OAct.pullback _ t.G t.act, PP', cub, sym, adj, prim⟩
  let m₀ : SABMap t' t (spMap θ) := m₁
  have hm₀ : m₀.φ = pullback.fst t.G.hom (spMap θ) := hm₁
  let W : (Sp R).Opens := PrimeSpectrum.basicOpen f
  have hψW : ∀ y, PsiUnitOn P.D.toPre y (W : Set (Sp R)) := hψ
  have hgen : (specOf θ).base (genericPoint (Sp V)) ∈ W := by
    rw [genericPoint_eq_bot_of_affine]
    show f ∉ Ideal.comap θ ⊥
    rw [Ideal.mem_comap, Ideal.mem_bot]
    exact hf

  let x : Sp (FractionRing V) ⟶ Sp R := jK V ≫ specOf θ
  have hxW : Set.range x ⊆ (W : Set (Sp R)) := by
    rintro _ ⟨z, rfl⟩
    have hz : (jK V).base z = genericPoint (Sp V) := by
      rw [genericPoint_eq_bot_of_affine]
      apply PrimeSpectrum.ext
      show Ideal.comap (algebraMap V (FractionRing V)) z.asIdeal = ⊥
      haveI := z.isPrime
      rw [Ideal.eq_bot_of_prime z.asIdeal]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective V (FractionRing V))
    show (specOf θ).base ((jK V).base z) ∈ W
    rw [hz]
    exact hgen
  obtain ⟨hamp, hkt⟩ := GlobalTheory.Mum.PolFibre.relAmple_kTriv_fibre R hR P.D P.A t.G t.semi P.U W hψW (FractionRing V) x hxW
  obtain ⟨PK, cubK, symK, adjK, primK, mK, hmK⟩ := sabPull CubePf.cubePull x t
  let tK : SAB H (Sp (FractionRing V)) := ⟨(Over.pullback x).obj t.G, IsSemiAbelian.pullback _ t.G t.semi,
    OAct.pullback _ t.G t.act, PK, cubK, symK, adjK, primK⟩
  have hLK : LBIso tK.PP.L (P.U.LG.L.pull (pullback.fst t.G.hom x)) := by
    obtain ⟨wK, gK, -⟩ := mK.lin
    rw [P.bundle, ← hmK]
    exact ⟨wK, gK⟩
  have hMK : (P.U.LG.L.pull (pullback.fst t.G.hom x)).IsLB := pull_isLB P.U.LG.isLB _
  have hp : IsProper tK.G.hom := GlobalTheory.ZH.isProper_hom_of_relAmple hamp
  haveI := hp
  have hA : RelAmple tK.G tK.PP.L :=
    GlobalTheory.ModelAbLocus.relAmple_of_lbIso_pull (f := 𝟙 _) (φ := 𝟙 _) (IsPullback.of_horiz_isIso ⟨by simp⟩) hMK tK.PP.isLB
      (hLK.chartPull (chartPullId _) (Geo.Tor.chartPullPull _ _ _ rfl)) hamp
  have hK : KTriv tK.G tK.PP.L := GlobalTheory.MulDescent.kTriv_of_lbIso hMK tK.PP.isLB hLK.symm hkt

  have := t.semi.smooth
  have := t.semi.geomConnected
  have : ConnectedSpace (Sp R) := inferInstanceAs (ConnectedSpace (PrimeSpectrum R))
  have : ConnectedSpace t.G.left := GeometricallyConnected.connectedSpace t.G.hom t.G.hom.isOpenMap
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected t.G.hom (Classical.arbitrary _)
  have hgA := GlobalTheory.ThetaBaseChange.grp_generic P.U.toUnifPre
  have dA : d = P.A.g := H1.dim_unique _ ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hgA.1 hd)
    P.A.smoothDim (eSec P.A.A (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R)))
  have hpbG := isGrpPullback_pullback t.G x
  have hdB : SmoothOfRelativeDimension P.A.g tK.G.hom :=
    dA ▸ (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hpbG.1 hd
  let A' : PolAV (Sp (FractionRing V)) := GlobalTheory.GenericPol.toPolAV tK P.A.g hdB hp hA hK
  let oA' : A'.OAct (𝓞 E) := ⟨tK.act.toRingAct, GlobalTheory.GenericPol.rosatiAdj tK⟩
  have mR : IsMonHom (Iso.refl t'.G).hom := by show IsMonHom (𝟙 _); infer_instance
  have hbc : IsGrpPullback t'.G t.G (specOf θ) ((Iso.refl t'.G).hom.left ≫ pullback.fst t.G.hom (specOf θ)) :=
    ((isGrpPullback_of_iso (Iso.refl t'.G)).comp (isGrpPullback_pullback t.G (specOf θ))).congr (Category.id_comp _) rfl
  have hgK := (isGrpPullback_pullback t'.G (jK V)).comp hbc
  obtain ⟨eA, meA, heA⟩ := grpPullback_iso hgK hpbG
  have wA : ∃ wA : LB.Iso (A'.L.pull eA.hom.left)
      (P.U.LG.L.pull (pullback.fst t'.G.hom (jK V) ≫ (Iso.refl t'.G).hom.left ≫ pullback.fst t.G.hom (specOf θ))),
      wA.IsGen := by
    rw [← heA]
    exact LBIso.trans (pull_isLB tK.PP.isLB _) (pull_isLB hMK _) (pull_isLB P.U.LG.isLB _)
      (GlobalTheory.RigidBundleGlue.LBIso.pull hLK _) ⟨GlobalTheory.Proof.TautologicalModel.taut _ _ _, GlobalTheory.Proof.TautologicalModel.taut_isGen P.U.LG.isLB _ _⟩

  have hbc' : (Iso.refl t'.G).hom.left ≫ pullback.fst t.G.hom (specOf θ) = pullback.fst t.G.hom (spMap θ) :=
    Category.id_comp _
  obtain ⟨wL, heL, gL, rL⟩ := rigIso_congr P.bundle m₀.cm m₀.lin (hbc'.trans hm₀.symm) (e := specOf θ) m₀.base.symm
  have hψn := GlobalTheory.PelCoordPull.nonempty_psiOn P.D.toPre W ⟨_, hgen⟩ hψW
  have extA₀ : ∀ a, (Over.pullback (jK V)).map (t'.act.act a) ≫ eA.hom =
      eA.hom ≫ (OAct.pullback x t.G t.act).act a := by
    intro a
    apply Over.OverMorphism.ext
    apply hpbG.1.hom_ext
    · have a₁ : ((Over.pullback (jK V)).map (t'.act.act a)).left ≫ pullback.fst t'.G.hom (jK V) =
          pullback.fst t'.G.hom (jK V) ≫ (t'.act.act a).left := pullback.lift_fst _ _ _
      have a₂ : (t'.act.act a).left ≫ pullback.fst t.G.hom (specOf θ) =
          pullback.fst t.G.hom (specOf θ) ≫ (t.act.act a).left := pullback.lift_fst _ _ _
      have a₃ : ((OAct.pullback x t.G t.act).act a).left ≫ pullback.fst t.G.hom x =
          pullback.fst t.G.hom x ≫ (t.act.act a).left := pullback.lift_fst _ _ _
      have i₀ : (Iso.refl t'.G).hom.left = 𝟙 _ := rfl
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, a₃, heA, ← Category.assoc eA.hom.left, heA,
        i₀, Category.id_comp, reassoc_of% a₁, a₂, Category.assoc]
    · exact (Over.w _).trans (Over.w _).symm
  obtain ⟨D', hD, U', hLG, hgenU, hPU⟩ := h4.unifBaseChange R V _ _ aR aV θ hI P.D P.A t.G t.semi P.U W hψn hgen
    t'.G (Iso.refl _) mR A' rfl eA meA wA t'.PP wL heL gL rL
  have extA : ∀ a, (Over.pullback (jK V)).map (t'.act.toRingAct.act a) ≫ U'.gen.hom = U'.gen.hom ≫ oA'.act a := by
    intro a
    rw [hgenU]
    exact extA₀ a
  obtain ⟨mod', oD', xl, el, lin', w0'⟩ := h5.oLinBaseChange R V _ _ aR aV θ P.D P.A t.G P.U t'.G (Iso.refl _) mR
    A' D' hD U' hPU (𝓞 E) P.oD P.oA t.act.toRingAct P.lin t'.act.toRingAct
    (fun a => (Category.comp_id _).trans (Category.id_comp _).symm) oA' extA
  let P' : PELUnif (maximalIdeal V) t' :=
    { D := D'
      mod := mod'
      oD := oD'
      A := A'
      oA := oA'
      U := U'
      bundle := hLG
      lin := lin'
      w0 := w0' H.w0 P.w0 }
  exact ⟨t', P', hD, ⟨m₀⟩, xl, el⟩

end GlobalTheory.LocalPull
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.steinFibre_closedFibre_point_subset_open_part : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ E : Emb M.π G', ∀ (H' : E.H.toScheme.Opens) (X'' : Scheme.{0}) (ν : X'' ⟶ pullback (PSpace.str R E.N) M.π) (i : H'.toScheme ⟶ X'') (P'' : Scheme.{0}) (a'' : X'' ⟶ P'') (b'' : P'' ⟶ PSpace R E.N), IsFinite ν → IsOpenImmersion i → i ≫ ν = H'.ι ≫ pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over → a'' ≫ b'' = ν ≫ pullback.fst (PSpace.str R E.N) M.π → IsFinite b'' → IsProper a'' → (∀ y : P'', _root_.IsPreconnected {x : X'' | a'' x = y}) → (∀ h : E.H.toScheme, M.π (G'.hom (E.H.ι h)) = closedPoint R → h ∈ H') → ∀ z : H'.toScheme, M.π (G'.hom (E.H.ι (H'.ι z))) = closedPoint R → ∀ w : X'', a'' w = a'' (i z) → w ∈ Set.range i := by
  first | exact @GlobalTheory.Mum.steinFibre_subset_range | exact GlobalTheory.Mum.steinFibre_subset_range | (intros; apply GlobalTheory.Mum.steinFibre_subset_range <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.relAmple_principal_polarisation_every_fibre_of_generate : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ W : (Sp R).Opens, (∀ y, PsiUnitOn D.toPre y W) → ∀ (K : Type) [Field K] (x : Sp K ⟶ Sp R), Set.range x ⊆ (W : Set (Sp R)) → RelAmple ((Over.pullback x).obj G) (U.LG.L.pull (pullback.fst G.hom x)) ∧ KTriv ((Over.pullback x).obj G) (U.LG.L.pull (pullback.fst G.hom x)) := by
  first | exact @GlobalTheory.Mum.PolFibre.relAmple_kTriv_fibre | exact GlobalTheory.Mum.PolFibre.relAmple_kTriv_fibre | (intros; apply GlobalTheory.Mum.PolFibre.relAmple_kTriv_fibre <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.eq_of_sectionRatio_eq_near_thickening_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ (e k : ℕ), k₀ ≤ k → ∀ (s₀ : H0 U.LG.L k) (i : Fin 1 → U.LG.L.ι) (w : (thickObj R (maximalIdeal R) e G).left), (fstG (maximalIdeal R) e G).left w ∈ secChart U.LG.L i → IsUnit (secGerm (fstG (maximalIdeal R) e G).left w s₀ i) → ∃ (N : (thickObj R (maximalIdeal R) e G).left.Opens) (m : ℕ) (σ : Fin m → H0 U.LG.L k), w ∈ N ∧ ∀ (W : Scheme.{0}) (a b : W ⟶ (thickObj R (maximalIdeal R) e G).left), a ≫ (thickObj R (maximalIdeal R) e G).hom = b ≫ (thickObj R (maximalIdeal R) e G).hom → (∀ x, a x ∈ N) → (∀ x, b x ∈ N) → (∀ l, SecRatioEq U.LG.L (a ≫ (fstG (maximalIdeal R) e G).left) (b ≫ (fstG (maximalIdeal R) e G).left) (σ l) s₀ (σ l) s₀) → a = b := by
  exact @GlobalTheory.Mum.eq_of_secRatioEq_near
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.fibre_eighth_power_theta_object_subfield : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ : ℕ), ∃ (J : Type) (_ : Finite J)
    (Mat : J → Matrix (Fin (2 * (8 * gQ))) (Fin (2 * (8 * gQ))) ℤ) (κ : ℕ) (w w' : J),
  ∀ (l : ℕ), l.Prime → Odd l → ∀ j : ℕ, 1 ≤ j →
  ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) →
  ∀ (Q : Data V), Q.g = gQ → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X),
  SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁),
  (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) →
  ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
  (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) →
  ∃ (bT : TBase k₀ ((l ^ j) ^ 2)) (t : TObj (8 * gQ) ((l ^ j) ^ 2) J bT (spMap k₀.subtype))
    (v : Ix (8 * gQ) ((l ^ j) ^ 2) → k₀) (ψ : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ t.A.left),
    t.Shape Mat κ ∧ t.Prim w w' ∧ t.HasTh (𝟙 _) (fun a => k₀.subtype (v a)) ∧
    IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) t.A (𝟙 _) ψ ∧
    LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (t.L.pull ψ) ∧
    ∀ (y : Over.mk (spMap ev) ⟶ D.P.A), y ^ ((l ^ j) ^ 2) = 1 →
      ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left,
      q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ →
      ∃ a, q ≫ ψ = (t.lab a).left := by
  first | exact @GlobalTheory.Poinc.Sep.sharp_fibre_theta_object | exact GlobalTheory.Poinc.Sep.sharp_fibre_theta_object | (intros; apply GlobalTheory.Poinc.Sep.sharp_fibre_theta_object <;> assumption)
end
