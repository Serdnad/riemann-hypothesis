module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle015
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPullCubicalOfIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PulledComparisonEven
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Convex.Contractible
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory.AnyUnif

theorem injective_of_ker_le_discrete {g g' : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (h : ∀ z, F z = 0 → z ∈ Λ) : Function.Injective F := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro z hz
  let c : ℂ → Λ := fun t => ⟨t • z, h _ (by rw [map_smul, hz, smul_zero])⟩
  have hc : Continuous c := Continuous.subtype_mk (by fun_prop) _
  have e : c 1 = c 0 := (IsLocallyConstant.iff_continuous c).2 hc |>.apply_eq_of_preconnectedSpace 1 0
  simpa [c] using congrArg Subtype.val e

theorem lbIso_pow_pull_id {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (n : ℕ) :
    LBIso (lbPow (L.pull (𝟙 X)) n) (lbPow L n) := by
  obtain ⟨w, hw⟩ : LBIso (L.pull (𝟙 X)) L :=
    LBIso.chartPull (chartPullPull L (𝟙 X) (𝟙 X) rfl) (chartPullId L) (PolBaseChange.lbIso_refl hL)
  exact ⟨LB.linCombIso w _ _, DVR.linCombIso_isGen w hw _ _⟩

theorem tangent_and_unimodular : ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g),
    (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) ∧
    ∀ (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ →
      ∃ Ef : LinearMap.BilinForm ℤ u.Λ, (∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧
        Function.Bijective Ef := by
  intro hU P u
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨u', Hm', χ', Ef', hA', -, h1, h2, -, -, hE, hB, -⟩ := hU P rig hrig
  obtain ⟨F, hF₀, -⟩ := HomLinear.exists_linear_of_isMonHom P.A P.A P.isAb P.isAb P.L P.L P.g P.g u u' h1 h2
    (𝟙 P.A) inferInstance
  have hF : ∀ z, u'.ex (F z) = u.ex z := fun z => (hF₀ z).trans (Category.comp_id _)
  have hΛ : ∀ z, F z ∈ u'.Λ ↔ z ∈ u.Λ := fun z => by rw [← u'.ker, hF, u.ker]
  haveI := u.discrete
  have hinj := injective_of_ker_le_discrete u.Λ F fun z hz => (hΛ z).1 (hz ▸ u'.Λ.zero_mem)
  let e := LinearEquiv.ofInjectiveEndo F hinj
  have he : ∀ z, e z = F z := fun _ => rfl
  have hd : ∀ w v, IsTangent v → (u.IsDiff w v ↔ u'.IsDiff (e w) v) := fun w v hv => by
    constructor
    · intro h
      simpa [he] using HomLinear.isDiff_comp u u' (𝟙 P.A) F hF₀ hv h
    · intro h
      simpa using HomLinear.isDiff_comp u' u (𝟙 P.A) e.symm.toLinearMap
        (fun z => by rw [Category.comp_id, ← hF, ← he]; simp) hv h
  refine ⟨fun v hv => ?_, fun w => ?_, fun Hm χ hA => ?_⟩
  · obtain ⟨w, hw, hu⟩ := h1 v hv
    refine ⟨e.symm w, (hd _ v hv).2 (by simpa using hw), fun w' hw' => ?_⟩
    rw [← hu _ ((hd _ v hv).1 hw'), e.symm_apply_apply]
  · obtain ⟨v, ⟨hv, hw⟩, hu⟩ := h2 (e w)
    exact ⟨v, ⟨hv, (hd w v hv).2 hw⟩, fun v' hv' => hu v' ⟨hv'.1, (hd w v' hv'.1).1 hv'.2⟩⟩
  · have hH := hermForm_pull_eq_of_lbIso_pow P.A P.A P.L P.L P.isLB P.isLB P.g P.g u u' Hm χ Hm' χ' hA hA'
      (𝟙 P.A) F hF₀ 1 1 (lbIso_pow_pull_id P.isLB 1)
    simp only [Nat.cast_one, _root_.one_mul] at hH
    let l : u.Λ ≃ₗ[ℤ] u'.Λ :=
      { toFun := fun a => ⟨e a, (hΛ a).2 a.2⟩
        invFun := fun b => ⟨e.symm b, (hΛ _).1 (by rw [← he, e.apply_symm_apply]; exact b.2)⟩
        map_add' := fun a b => Subtype.ext (map_add e _ _)
        map_smul' := fun n a => Subtype.ext (map_zsmul e n _)
        left_inv := fun a => Subtype.ext (e.symm_apply_apply _)
        right_inv := fun b => Subtype.ext (e.apply_symm_apply _) }
    refine ⟨Ef'.comp l.toLinearMap l.toLinearMap, fun a b => ?_, ?_⟩
    · rw [← hH]
      exact hE (l a) (l b)
    · exact l.dualMap.bijective.comp (hB.comp l.bijective)

end GlobalTheory.AnyUnif
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory.TripleModel

open GlobalTheory.PrimNorm GlobalTheory.MulPull

section Charts

variable {Y Y' : Scheme.{0}}

end Charts

section Cubical

theorem isPullCubical_of_lbIso (hG : Out.GlobalFnsSt) {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G']
    [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (hA : IsAbelianScheme G') {f : S' ⟶ S} {α : G'.left ⟶ G.left}
    (gp : IsGrpPullback G' G f α) {L' : RigLB G'} {L : RigLB G}
    (c' : CubicalStr G' L') (c : CubicalStr G L) (h : LBIso L'.L (L.L.pull α)) :
    (cubeMapOf gp).IsPullCubical c' c := by
  obtain ⟨w, hw⟩ := h
  have hw' := (isGen_iff w).1 hw
  obtain ⟨a, ha, hm⟩ := DegPull.exists_pmaps (K := PUnit) hw' L.isLB L'.isLB (φ' := fun _ => eSec G')
    (φ := fun _ => eSec G) (ε := fun _ => 1) (cubeMapOf gp).e (fun _ => (cubeMapOf gp).e_comm) L.rig L.rigGen
  obtain ⟨u, hu⟩ := HeckePoint.exists_unit_ratio L'.isLB a L'.rig ha L'.rigGen
  let w₁ : LB.Iso L'.L (L.L.pull α) :=
    ⟨fun p => w.s p * res (U := G'.hom ⁻¹ᵁ ⊤) (fun _ _ => trivial) (pullU G'.hom ⊤ u)⟩
  have g₁ : ∀ (Y : Scheme.{0}) (f : Y ⟶ G'.left) (y : Y) j k, α (f y) ∈ L.L.U j → f y ∈ L'.L.U k →
      gw w₁ f y j k = gw w f y j k * gm (f ≫ G'.hom) y ⊤ u := fun Y f y j k hj hk =>
    (map_mul _ _ _).trans (congrArg _ ((gm_res f y _ (show f y ∈ (L.L.pull α).U (fun _ => j) ⊓ L'.L.U k from
      ⟨mem_pull.2 hj, hk⟩) _).trans (gm_pull f G'.hom y ⊤ trivial u)))
  have hw₁ : PGen w₁ := fun Y f y j j' k k' hj hj' hk hk' => by
    rw [g₁ Y f y j k hj hk, g₁ Y f y j' k' hj' hk', hw' Y f y j j' k k' hj hj' hk hk', _root_.mul_assoc]
  refine (isPullCubical_iff _ c c').2 ⟨w₁, hw₁, fun Z r z p q hp hq => ?_, ?_⟩
  · refine (hm Z r z p q hp hq).trans ?_
    have e : (r ≫ eSec G') ≫ G'.hom = r := by
      rw [Category.assoc, show eSec G' ≫ G'.hom = 𝟙 _ from Over.w η[G'], Category.comp_id]
    have e₂ := g₁ Z (r ≫ eSec G') z _ _ (hp default) (hq default)
    rw [e] at e₂
    rw [hu Z r z q (Set.mem_iInter.2 hq), Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one]
    exact (_root_.mul_assoc _ _ _).symm.trans (congrArg (· * _) e₂.symm)
  · let e : 𝟙_ (Over S') ⟶ G3 G' := lift 1 (lift 1 1)
    have s₁ := (hG _ _ hA).2
    have hψ : ∀ I : thK, thφ G' (x3 G') I ≫ α = (cubeMapOf gp).F3 ≫ thφ G (x3 G) I :=
      fun I => (cubeMapOf gp).psum_comm I.down
    refine EvenPull.pmaps_of_section (φ' := thφ G' (x3 G')) (φ := thφ G (x3 G)) (ε := thε) hw₁ L.isLB L'.isLB
      (cubeMapOf gp).F3 hψ c'.t c'.isGen
      c.t c.isGen (G3 G').hom e.left (Over.w e) (AbLaw.Cube.surj_tensor hG hA (AbLaw.Cube.surj_tensor hG hA s₁))
      (fun y J J' hJ hJ' => ?_)
    have a₁ : e.left ≫ (cubeMapOf gp).F3 =
        (lift (1 : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G) (lift 1 1)).left := hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
      have o := congrArg (fun q => q.left) (map_one (pushHom gp (𝟙_ (Over S'))))
      have e₁ : e ≫ x3 G' i = 1 := by fin_cases i <;> simp [e, x3]
      have e₂ : lift (1 : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G) (lift 1 1) ≫ x3 G i = 1 := by
        fin_cases i <;> simp [x3]
      rw [e₁, e₂]
      exact o
    have b₁ := (isCub_cubV c (T := Over.mk ((𝟙_ (Over S')).hom ≫ f)) hJ).face 1 1
    have b₂ := (isCub_cubV c' (T := 𝟙_ (Over S')) hJ').face 1 1
    have b₃ := prod_cub (1 : 𝟙_ (Over S') ⟶ G') 1 1 (fun ψ => gw w₁ ψ y (J (ψ ≫ α)) (J' ψ))
    refine Eq.trans ((congrArg (fun q => val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) c.t q y J) a₁).trans b₁)
      (Eq.symm ?_)
    refine (congrArg₂ (· * ·) b₃ b₂).trans ?_
    simp

end Cubical

section Ample

variable {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

end Ample

section Extend

variable {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {A : Over (Sp R)} [GrpObj A] {B : Over (Sp K)} [GrpObj B] {φ : B.left ⟶ A.left} {L : LB A.left} {L' : LB B.left}

end Extend

section Points

variable {S S' : Scheme.{0}} {A : Over S} [GrpObj A] {B : Over S'} [GrpObj B] {j : S' ⟶ S} {φ : B.left ⟶ A.left}

end Points

section Triple

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (hLaws : Out.Laws) (t₀ : SAB H (Sp K)) {A : Over (Sp R)} [GrpObj A] {φ : t₀.G.left ⟶ A.left}
  (hA : IsAbelianScheme A) (gp : IsGrpPullback t₀.G A (spMap (algebraMap R K)) φ)
  {L : LB A.left} (hL : L.IsLB) (hr : Out.Rigidified A L) (i : LBIso t₀.PP.L (L.pull φ))

include hLaws hA gp hL hr i

end Triple

end GlobalTheory.TripleModel
end
end
