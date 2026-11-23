module

public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SumNegOnePowFinrankEqZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle180
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1374
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1685
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1538
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1376
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1584
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1394
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2281
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2300
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2186
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1947
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1453
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2080
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairFirstConjEqSumCosetIndicators
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2182
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2313
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2315
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
open GlobalTheory.Twist GlobalTheory.SerreCriterion

set_option autoImplicit false
noncomputable section
namespace GlobalTheory
namespace IsolatedSec
variable {X : Scheme.{0}}

theorem exists_germ_eq_of_isolated {F : X.Modules} {y : X} (hy : IsClosed ({y} : Set X))
    {U : X.Opens} (hyU : y ∈ U) (hF : ∀ z ∈ U, z ∈ support F → z = y)
    (t : (F.presheaf.stalk y :)) : ∃ s : Γ(F, ⊤), F.presheaf.germ ⊤ y trivial s = t := by
  obtain ⟨V, hyV, s, rfl⟩ := F.presheaf.exists_germ_eq t
  let W : X.Opens := ⟨{y}ᶜ, hy.isOpen_compl⟩
  let C : Bool → X.Opens := fun b => if b then V ⊓ U else W
  have hzero : ∀ (O : X.Opens), O ≤ V ⊓ U ⊓ W → ∀ r : Γ(F, O), r = 0 := fun O hO r => by
    refine TopCat.Presheaf.section_ext (abSheaf F) O r 0 fun z hz => ?_
    have hz' := hO hz
    have hns : z ∉ support F := fun h => hz'.2 (hF z hz'.1.2 h)
    exact (notMem_support_iff.1 hns).elim _ _
  obtain ⟨g, hg⟩ := exists_sec_of_cover (F := F) C (fun _ => le_top)
    (fun z _ => by
      by_cases h : z = y
      · subst h; exact Opens.mem_iSup.2 ⟨true, ⟨hyV, hyU⟩⟩
      · exact Opens.mem_iSup.2 ⟨false, h⟩)
    (fun b => match b with
      | true => resM F (inf_le_left : V ⊓ U ≤ V) s
      | false => 0)
    (fun k l => by
      cases k <;> cases l
      · rfl
      · exact (hzero _ (le_inf inf_le_right inf_le_left) _).trans (hzero _ (le_inf inf_le_right inf_le_left) _).symm
      · exact (hzero _ (le_inf inf_le_left inf_le_right) _).trans (hzero _ (le_inf inf_le_left inf_le_right) _).symm
      · rfl)
  refine ⟨g, ?_⟩
  have hyVU : y ∈ V ⊓ U := ⟨hyV, hyU⟩
  have := congrArg (F.presheaf.germ (V ⊓ U) y hyVU) (hg true)
  dsimp only at this
  rw [germ_resM, germ_resM] at this
  exact this
end IsolatedSec

theorem exists_sec_mem_nonzeroLocus_of_isolated : ∀ (k : Type) [Field k] (X : Scheme.{0})
    [IsIntegral X] (q : X ⟶ Sp k), IsProjOver q → ∀ (L : LB X), L.IsLB →
    ∀ (J : X.IdealSheafData) (x : X) (U : X.Opens), IsClosed ({x} : Set X) → x ∈ U →
    (∀ y ∈ U, y ∈ J.support ↔ y = x) → Subsingleton (coh (twist (idealModule J) L) 1) →
    ∃ s : L.Sec, x ∈ nonzeroLocus s := by
  intro k _ X _ q _ L hL J x U hx hxU hJ h
  set φ := toSubscheme J with hφ
  let S : ShortComplex X.Modules :=
    ShortComplex.mk (kernel.ι φ) (cokernel.π (kernel.ι φ)) (cokernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  have hS' : (S.map (twistFunctor L)).ShortExact := Twist.shortExact_map hL hS
  have h' : Subsingleton (coh (twist (kernel φ) L) 1) := by
    exact h
  have hsurj := cohOn.app_surjective hS' ⊤ h'
  have hQ : ∀ z ∈ U, z ∈ support (twist S.X₃ L) → z = x := by
    intro z hzU hz
    rw [support_twist hL] at hz
    have := mem_support_iff.1 hz
    refine (hJ z hzU).1 (support_pushforward_subscheme_subset J ?_)
    exact mem_support_iff.2 (stalkLinear_injective (Abelian.factorThruCoimage φ) z).nontrivial
  have hxJ : x ∈ J.support := (hJ x hxU).2 rfl
  obtain ⟨c, hc⟩ := exists_chart hL x
  let t : Γ(QCoh.structureModule X, ⊤) := (structureModuleSectionsEquiv ⊤).symm 1
  have ht : structureModuleSectionsEquiv ⊤ t = 1 := LinearEquiv.apply_symm_apply _ _
  obtain ⟨b, hb⟩ := IsolatedSec.exists_germ_eq_of_isolated hx hxU hQ
    ((stalkEquiv S.X₃ hL c hc).symm (stalkLinear S.g x
      ((QCoh.structureModule X).presheaf.germ ⊤ x trivial t)))
  obtain ⟨a, rfl⟩ := hsurj b
  refine ⟨secOfTwist (𝟙 _) a, basicOpen_le_nonzeroLocus _ c ((X.mem_basicOpen _ x hc).2 ?_)⟩
  have hm : x ∈ ⊤ ⊓ L.U c := ⟨trivial, hc⟩
  replace hb := (stalkEquiv_germ hL c hc (V := ⊤) trivial _).symm.trans
    ((LinearEquiv.eq_symm_apply _).1 hb)
  have h₁ : stalkLinear S.g x ((QCoh.structureModule X).presheaf.germ _ x hm
      (coord (F := QCoh.structureModule X) a c)) =
      stalkLinear S.g x ((QCoh.structureModule X).presheaf.germ ⊤ x trivial t) :=
    (stalkLinear_germ S.g x hm _).trans hb
  have h₂ : stalkLinear φ x ((QCoh.structureModule X).presheaf.germ ⊤ x trivial t -
      (QCoh.structureModule X).presheaf.germ _ x hm (coord (F := structureModule X) a c)) = 0 := by
    rw [← Abelian.coimage.fac φ, stalkLinear_comp, LinearMap.comp_apply, map_sub]
    exact (congrArg _ (sub_eq_zero.2 h₁.symm)).trans (map_zero _)
  have h₃ := not_isUnit_of_toSubscheme_eq_zero J (y := x) hxJ _ h₂
  rw [map_sub, structureModuleStalkEquiv_germ] at h₃
  erw [structureModuleStalkEquiv_germ] at h₃
  rw [ht, map_one] at h₃
  have hu := (IsLocalRing.isUnit_or_isUnit_one_sub_self _).resolve_right h₃
  exact (congrArg IsUnit (X.presheaf.germ_res_apply (homOfLE _) x hc _)).mpr hu
end GlobalTheory
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
open GlobalTheory.Twist GlobalTheory.SerreCriterion

set_option autoImplicit false
noncomputable section
namespace GlobalTheory
namespace IsolatedSecZero
variable {X : Scheme.{0}}

theorem exists_germ_eq_zero_of_isolated {F : X.Modules} {y : X} (hy : IsClosed ({y} : Set X))
    {U : X.Opens} (hyU : y ∈ U) (hF : ∀ z ∈ U, z ∈ support F → z = y)
    (t : (F.presheaf.stalk y :)) : ∃ s : Γ(F, ⊤), F.presheaf.germ ⊤ y trivial s = t ∧
      ∀ z, z ≠ y → F.presheaf.germ ⊤ z trivial s = 0 := by
  obtain ⟨V, hyV, s, rfl⟩ := F.presheaf.exists_germ_eq t
  let W : X.Opens := ⟨{y}ᶜ, hy.isOpen_compl⟩
  let C : Bool → X.Opens := fun b => if b then V ⊓ U else W
  have hzero : ∀ (O : X.Opens), O ≤ V ⊓ U ⊓ W → ∀ r : Γ(F, O), r = 0 := fun O hO r => by
    refine TopCat.Presheaf.section_ext (abSheaf F) O r 0 fun z hz => ?_
    have hz' := hO hz
    have hns : z ∉ support F := fun h => hz'.2 (hF z hz'.1.2 h)
    exact (notMem_support_iff.1 hns).elim _ _
  obtain ⟨g, hg⟩ := exists_sec_of_cover (F := F) C (fun _ => le_top)
    (fun z _ => by
      by_cases h : z = y
      · subst h; exact Opens.mem_iSup.2 ⟨true, ⟨hyV, hyU⟩⟩
      · exact Opens.mem_iSup.2 ⟨false, h⟩)
    (fun b => match b with
      | true => resM F (inf_le_left : V ⊓ U ≤ V) s
      | false => 0)
    (fun k l => by
      cases k <;> cases l
      · rfl
      · exact (hzero _ (le_inf inf_le_right inf_le_left) _).trans (hzero _ (le_inf inf_le_right inf_le_left) _).symm
      · exact (hzero _ (le_inf inf_le_left inf_le_right) _).trans (hzero _ (le_inf inf_le_left inf_le_right) _).symm
      · rfl)
  refine ⟨g, ?_, fun z hz => ?_⟩
  · have hyVU : y ∈ V ⊓ U := ⟨hyV, hyU⟩
    have := congrArg (F.presheaf.germ (V ⊓ U) y hyVU) (hg true)
    dsimp only at this
    rw [germ_resM, germ_resM] at this
    exact this
  · have hzW : z ∈ W := hz
    have := congrArg (F.presheaf.germ W z hzW) (hg false)
    dsimp only at this
    rw [germ_resM, map_zero] at this
    exact this
end IsolatedSecZero

theorem exists_sec_mem_nonzeroLocus_of_isolated_zero_else : ∀ (k : Type) [Field k] (X : Scheme.{0})
    [IsIntegral X] (q : X ⟶ Sp k), IsProjOver q → ∀ (L : LB X), L.IsLB →
    ∀ (J : X.IdealSheafData) (x : X) (U : X.Opens), IsClosed ({x} : Set X) → x ∈ U →
    (∀ y ∈ U, y ∈ J.support ↔ y = x) → Subsingleton (coh (twist (idealModule J) L) 1) →
    ∃ s : L.Sec, x ∈ nonzeroLocus s ∧ ∀ y ∈ J.support, y ≠ x → y ∉ nonzeroLocus s := by
  intro k _ X _ q _ N hN J x U hxc hxU hJ h
  set φ := toSubscheme J with hφ
  let S : ShortComplex X.Modules :=
    ShortComplex.mk (kernel.ι φ) (cokernel.π (kernel.ι φ)) (cokernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  have hS' : (S.map (twistFunctor N)).ShortExact := Twist.shortExact_map hN hS
  have hsurj := cohOn.app_surjective hS' ⊤ h
  have hQ : ∀ z ∈ U, z ∈ support (twist S.X₃ N) → z = x := by
    intro z hzU hz
    rw [support_twist hN] at hz
    have := mem_support_iff.1 hz
    refine (hJ z hzU).1 (support_pushforward_subscheme_subset J ?_)
    exact mem_support_iff.2 (stalkLinear_injective (Abelian.factorThruCoimage φ) z).nontrivial
  have hx : x ∈ J.support := (hJ x hxU).2 rfl
  obtain ⟨c, hc⟩ := exists_chart hN x
  let one : Γ(QCoh.structureModule X, ⊤) := (structureModuleSectionsEquiv ⊤).symm 1
  obtain ⟨b, hb, hb0⟩ := IsolatedSecZero.exists_germ_eq_zero_of_isolated hxc hxU hQ
    ((stalkEquiv S.X₃ hN c hc).symm
      (stalkLinear S.g x ((QCoh.structureModule X).presheaf.germ ⊤ x trivial one)))
  obtain ⟨a, rfl⟩ := hsurj b
  refine ⟨secOfTwist (𝟙 _) a, ?_, ?_⟩
  · have hm : x ∈ ⊤ ⊓ N.U c := ⟨trivial, hc⟩
    replace hb := (stalkEquiv_germ hN c hc (V := ⊤) trivial _).symm.trans
      ((LinearEquiv.eq_symm_apply _).1 hb)
    have h₁ : stalkLinear S.g x ((QCoh.structureModule X).presheaf.germ _ x hm
        (coord (F := QCoh.structureModule X) a c)) =
        stalkLinear S.g x ((QCoh.structureModule X).presheaf.germ ⊤ x trivial one) :=
      (stalkLinear_germ S.g x hm _).trans hb
    have h₂ : stalkLinear φ x ((QCoh.structureModule X).presheaf.germ ⊤ x trivial one -
        (QCoh.structureModule X).presheaf.germ _ x hm (coord (F := QCoh.structureModule X) a c)) = 0 := by
      rw [← Abelian.coimage.fac φ, stalkLinear_comp, LinearMap.comp_apply, map_sub]
      exact (congrArg _ (sub_eq_zero.2 h₁.symm)).trans (map_zero _)
    have h₃ := not_isUnit_of_toSubscheme_eq_zero J hx _ h₂
    rw [map_sub] at h₃
    erw [structureModuleStalkEquiv_germ, structureModuleStalkEquiv_germ] at h₃
    have h1 : structureModuleSectionsEquiv ⊤ one = 1 := by simp [one]
    rw [h1, map_one] at h₃
    have hu := (IsLocalRing.isUnit_or_isUnit_one_sub_self _).resolve_right h₃
    refine basicOpen_le_nonzeroLocus _ c ((X.mem_basicOpen _ x hc).2 ?_)
    erw [secOfTwist_f]
    exact (congrArg IsUnit (X.presheaf.germ_res_apply (homOfLE _) x hc _)).mpr hu
  · intro y hy hyx hmem
    obtain ⟨d, hd⟩ := Opens.mem_iSup.1 hmem
    have hyd : y ∈ N.U d := X.basicOpen_le _ hd
    have hm : y ∈ ⊤ ⊓ N.U d := ⟨trivial, hyd⟩
    have e0 := hb0 y hyx
    have h₁ : stalkLinear S.g y ((QCoh.structureModule X).presheaf.germ _ y hm
        (coord (F := QCoh.structureModule X) a d)) = 0 := by
      have := (stalkEquiv_germ hN d hyd (V := ⊤) trivial _).symm.trans
        (congrArg (stalkEquiv S.X₃ hN d hyd) e0)
      rw [map_zero] at this
      exact (stalkLinear_germ S.g y hm _).trans this
    have h₂ : stalkLinear φ y ((QCoh.structureModule X).presheaf.germ _ y hm
        (coord (F := QCoh.structureModule X) a d)) = 0 := by
      rw [← Abelian.coimage.fac φ, stalkLinear_comp, LinearMap.comp_apply]
      exact (congrArg _ h₁).trans (map_zero _)
    have h₃ := not_isUnit_of_toSubscheme_eq_zero J hy _ h₂
    rw [structureModuleStalkEquiv_germ] at h₃
    apply h₃
    erw [secOfTwist_f] at hd
    exact (congrArg IsUnit (X.presheaf.germ_res_apply (homOfLE _) y hyd _)).mp
      ((X.mem_basicOpen _ y hyd).1 hd)
end GlobalTheory
end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section
namespace GlobalTheory.WeilUnitaryTransportF

theorem isUnitaryOn_transportF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → IsUnitaryOn (adeleClass F) om := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ h0 hσ χS χT hcS hcT rS rT ω hω JA JB ξ hA hBm κ _ co hrat om hom
  have hψ := hω.std
  rintro μ hμ ⟨a, b⟩ Φ hΦ
  obtain ⟨g, h, hh, hg⟩ := GlobalTheory.T.exists_unitaryPair_partner_cmExtension F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm a b
  obtain ⟨ν, 𝓕, hν, h𝓕⟩ := GlobalTheory.T.exists_haar_fundamentalDomain_rationalMatrices_tower F E nS nT
  obtain ⟨ν', 𝓕', hν', h𝓕', heq⟩ :=
    GlobalTheory.T.darbouxCoords_transfer_haar_fundamentalDomain_cm F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm κ co hrat ν 𝓕 hν h𝓕
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_lintegral_sq_eq_mul_setLIntegral_thetaTransform F B.ψ hψ.1 κ μ hμ ν' hν' 𝓕' h𝓕'
  have hiso : ∀ Ψ ∈ schA F κ, ∫⁻ x, ‖Ψ x‖ₑ ^ 2 ∂μ =
      c * ∫⁻ w in 𝓕, ‖GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Ψ w‖ₑ ^ 2 ∂ν := by
    intro Ψ hΨ
    rw [hc Ψ hΨ, ← heq]
    rfl
  have hth : IsThetaFunOF σ JS JT ξ₀ B.ψ (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) :=
    ⟨GlobalTheory.T.thetaTransform_rationalTranslate_quasiInvariant_cm F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm κ co hrat Φ hΦ,
     GlobalTheory.T.thetaTransform_adelicSchwartz_hasFiniteLevel_CM F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm κ co hrat Φ hΦ,
     GlobalTheory.T.continuous_thetaTransform_schwartz_cm F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm κ co hrat Φ hΦ,
     GlobalTheory.T.contDiff_thetaTransform_archimedean_cm F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm κ co hrat Φ hΦ⟩
  have ht := hom a b g h hh hg Φ hΦ
  calc
    _ = c * ∫⁻ w in 𝓕, ‖GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ ((om (a, b)) Φ) w‖ₑ ^ 2 ∂ν := hiso _ ht.1
    _ = c * ∫⁻ w in 𝓕, ‖GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ w‖ₑ ^ 2 ∂ν := by
      calc
        _ = c * ∫⁻ w in 𝓕, ‖(ω (g, h)) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) w‖ₑ ^ 2 ∂ν := by
          congr 1
          apply lintegral_congr
          intro w
          exact congrArg (fun z : ℂ => ‖z‖ₑ ^ 2) (congrFun ht.2 w)
        _ = _ := congrArg (c * ·) (hω.om_unit ν 𝓕 hν h𝓕 _ _ hth)
    _ = _ := (hiso _ hΦ).symm

end GlobalTheory.WeilUnitaryTransportF

end
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SwapActs

theorem swap_acts_box : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v)
    (ι : (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι →
    ∀ (d' : Darboux (symp (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J)) (Fin a' × Fin (a + a'))),
    (∀ x : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.W.J) (dbl (incM F G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')))),
    IsDblCoord (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J) d' dd →
    ∀ (omd : UG (cA σ) (dbl (incM F G.V'.J)) →* Module.End ℂ (((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → AF F) → ℂ)),
    IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd →
    ∀ (f : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f → f * f = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) →
    f * cA σ f = -algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) → piW t f = 1 → piW (t.comp σ) f = -1 →
    ∀ w : UG (cA σ) (dbl (incM F G.V'.J)),
      ((w : GL (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
        Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin a') (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) (f • 1) (f • 1)
          ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) →
    ∃ c : ℂ, ∀ φ₁ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ φ₂ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v),
      ∀ ψ₁ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ ψ₂ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v),
      ι ψ₁ = (fun Y => starRingEnd ℂ (ι (fun y => starRingEnd ℂ (φ₂ y)) (-Y))) →
      ι (fun y => starRingEnd ℂ (ψ₂ y)) = (fun Y => starRingEnd ℂ (ι φ₁ (-Y))) →
      Acts (evFin F v) (omd w) (boxFun φ₁ φ₂) (c • boxFun ψ₁ ψ₂) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hv t ι hι d' hd' dd hdd omd hspl f hf1 hf2 hf3 hf4 hf5 w hw
  have hcm : IsCMExt F E σ := hT.base.cm
  obtain ⟨hAt, -⟩ := GlobalTheory.T.local_idempotent_character_value σ hcm (incM F G.V'.J) (d := a + a') v t f hf1 hf2 hf3 hf4 hf5 w hw
  have atAct : ∀ u : Matrix (Fin (a + a')) (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) u →
      At (evFin F v) (actB (cA σ) w u) := by
    intro u hu r hr
    simp only [actB]
    rw [← Matrix.smul_mul, hu r hr, Matrix.zero_mul]
  have hex := GlobalTheory.T.doubledUnitaryElement_acts_localOperatorAtPlace F E σ B a a' G hT.base dd omd hspl v w hAt
  obtain ⟨S, hS, hSh⟩ := GlobalTheory.T.splitting_preserves_local_schwartz dd B.ψ hT.base.std (actB (cA σ)) omd hspl.toIsSplitting v w atAct hex
  have hSlin := GlobalTheory.LocWeilAct.linear_of_acts v (omd w) S hS
  obtain ⟨c, hc⟩ := GlobalTheory.T.linear_bar_model_local_triple F E σ B a a' G X om om' hT v t ι hι d' hd' dd hdd f hf1 hf2 hf3 hf4 hf5 w hw S
    (fun Φ hΦ => (hS Φ hΦ).1) hSlin hSh
  refine ⟨c, fun φ₁ h₁ φ₂ h₂ ψ₁ k₁ ψ₂ k₂ e₁ e₂ => ?_⟩
  have hbij := GlobalTheory.T.slice_transform_schwartz_bijective ι hι.bij
  have hΦ := GlobalTheory.BoxSpan.boxFun_mem_SB' h₁ h₂
  have hΨ : c • boxFun ψ₁ ψ₂ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v) :=
    (SB _).smul_mem c (GlobalTheory.BoxSpan.boxFun_mem_SB' k₁ k₂)
  have key : S (boxFun φ₁ φ₂) = c • boxFun ψ₁ ψ₂ := by
    refine hbij.injOn (hS _ hΦ).1 hΨ ?_
    rw [hc _ hΦ, map_smul]
    congr 1
    funext Z
    rw [Function.comp_apply, GlobalTheory.SwapSlice.sliceT_boxFun, GlobalTheory.SwapSlice.sliceT_boxFun, GlobalTheory.SwapSlice.swapNeg_apply,
      GlobalTheory.SwapSlice.barL_apply, GlobalTheory.SwapSlice.barL_apply, e₁, e₂]
    simp only [Complex.conj_conj]
    ring
  have h := (hS _ hΦ).2
  rwa [key] at h

end GlobalTheory.SwapActs
end
end

section

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead


theorem _root_.GlobalTheory.T.standardPairFirst_conj_eq_sum_cosetIndicators : ∀ {D : D7} (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d), a ≤ d → ∀ (e : AE D) (𝔪 : Ideal (𝓞 D.host.E)), GoodMod e 𝔪 →
  ∀ ν : (AE D)ˣ →* Circle, KillsCong ν 𝔪 → ∀ β : GL (Fin S.rank) (EAf D), IsIntM β.val → IsIntM (β⁻¹).val →
  ∀ R : Finset (Formalism.MainNotions.StandardLatticesGL3.GA D a), (∀ r ∈ R, r ∈ intG D a) → (∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k)) →
  ∀ z : Formalism.MainNotions.StandardLatticesGL3.GA D a → Matrix (Fin d) (Fin a) D.host.E, (∀ r ∈ R, IsIntE (z r) ∧ Approx 𝔪 0 r (z r)) →
  (fun w => starRingEnd ℂ (stdFst ν e 𝔪 S T β 1 w)) =
    starRingEnd ℂ (unitChar ν e β.val) • ∑ r ∈ R, unitChar ν e (matE r) • cosInd e 𝔪 hS hT (z r) := by
  first | exact @GlobalTheory.StdExpand.conj_stdFst_eq_sum | exact GlobalTheory.StdExpand.conj_stdFst_eq_sum | (intros; apply GlobalTheory.StdExpand.conj_stdFst_eq_sum <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.AV.KerPart
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.MonObj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_isogeny_kernel_finite_algebra_finrank_eq_degree : ∀ (k : Type) [Field k] (A B : AbVar k) (f : A ⟶ B), IsIsogeny f → ∃ (H : Type) (_ : CommRing H) (_ : Algebra k H) (i : ptOver k H ⟶ A.X), KerPow f 0 H i ∧ Module.finrank k H = deg f := by
  first | exact @GlobalTheory.AV.KerPart.exists_kerPow_zero_finrank_eq_deg | exact GlobalTheory.AV.KerPart.exists_kerPow_zero_finrank_eq_deg | (intros; apply GlobalTheory.AV.KerPart.exists_kerPow_zero_finrank_eq_deg; all_goals assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS

theorem _root_.GlobalTheory.T.kodairaSpencerCoords_two_charts_transition : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)), (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → ∀ (i i' : M.K.bundle.ι) (k k' : X.F.J) (K : Type) [Field K] (z : Sp K ⟶ M.X), ⊤ ≤ z ⁻¹ᵁ ksOpen M i k → ⊤ ≤ z ⁻¹ᵁ ksOpen M i' k' → ∀ (hg : ⊤ ≤ z ⁻¹ᵁ ((LB.div M.K.bundle ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M.σ)).U (i, flagIdx M _ k) ⊓ (LB.div M.K.bundle ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M.σ)).U (i', flagIdx M _ k'))) (x x' : K), KSRel M i k z x → KSRel M i' k' z x' → x = GlobalTheory.FlagMod.ev z _ hg ((LB.div M.K.bundle ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M.σ)).g (i, flagIdx M _ k) (i', flagIdx M _ k')).val * x' := by
  first | exact @GlobalTheory.CompHS.ksRel_change | exact GlobalTheory.CompHS.ksRel_change | (intros; apply GlobalTheory.CompHS.ksRel_change <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.crystallineClass_mem_hodgeFiltration_of_cechRep_zero : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) (W : J → X.Opens), ⨆ j, W j = ⊤ → ∀ c : Z1 (O (dp0 R) s), IsRep W c 0 → H1.mk _ c ∈ F1 s := by
  first | exact @GlobalTheory.CechKS.h1_mk_mem_f1_of_isRep_zero | exact GlobalTheory.CechKS.h1_mk_mem_f1_of_isRep_zero | (intros; apply GlobalTheory.CechKS.h1_mk_mem_f1_of_isRep_zero <;> assumption)
end
