module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle582
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2659
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle083
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelObjectOfDescendedData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpanningPosDefRelationHarrisTaylorOrder
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle547
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle070
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2637
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle585
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1661
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle581
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2618
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2605
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle975
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle956
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1364
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle101
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2638
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false
namespace GlobalTheory.ClosedLev

theorem exists_nhd (R : Type) [CommRing R] (I : Ideal R) (X Z : Scheme.{0}) (φ : X ⟶ Z)
    (p : Z ⟶ Spec (CommRingCat.of R)) (hφ : IsProper φ)
    (hc : IsClosedImmersion (((baseIdeal p I).comap φ).subschemeι ≫ φ)) (z : Z)
    (hz : I ≤ (p z).asIdeal) : ∃ U : Z.Opens, z ∈ U ∧ IsClosedImmersion (φ ∣_ U) := by
  have hfin : (⇑φ ⁻¹' {z}).Finite := (GlobalTheory.T.fibre_subsingleton_of_closedImmersion_mod_ideal R I X Z φ p hc z hz).finite
  obtain ⟨V₀, hzV₀, hV₀⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton φ z hfin
  obtain ⟨V, hV, hzV, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Z.isBasis_affineOpens hzV₀
  have hVf : IsFinite (φ ∣_ V) := GlobalTheory.PushFinite.isFinite_restrict_of_le φ hle
  obtain ⟨haff, hfr⟩ := GlobalTheory.T.isAffineOpen_preimage_and_finite_app_of_isFinite X Z φ V hV hVf
  obtain ⟨r, hr1, hr⟩ := GlobalTheory.T.exists_sub_one_mem_mul_mem_range_of_finite_surj_mod _ _ (φ.app V).hom hfr _ (GlobalTheory.T.surjective_sections_mod_baseIdeal_of_closedImmersion R I X Z φ p hc V hV haff)
  exact ⟨Z.basicOpen r, GlobalTheory.T.mem_basicOpen_of_sub_one_mem_baseIdealSheaf R I Z p V hV r z hzV hz hr1, GlobalTheory.T.isClosedImmersion_restrict_basicOpen_of_mul_mem_range X Z φ V hV haff r hr⟩

theorem isClosedImmersion_of_mod : ∀ (R : Type) [CommRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (X Z : Scheme.{0}) (φ : X ⟶ Z) (p : Z ⟶ Spec (CommRingCat.of R)), IsProper φ → UniversallyClosed p → IsClosedImmersion (((baseIdeal p I).comap φ).subschemeι ≫ φ) → IsClosedImmersion φ := by
  intro R _ I hI X Z φ p hφ hp hc
  let O : Z.Opens := ⨆ U : {U : Z.Opens // IsClosedImmersion (φ ∣_ U)}, U.1
  have hO : O = ⊤ := by
    have h0 := GlobalTheory.T.eq_empty_of_isClosed_of_universallyClosed_of_le_jacobson R I hI Z p hp ((O : Set Z)ᶜ) O.isOpen.isClosed_compl fun z hz hIz => by
      obtain ⟨U, hzU, hU⟩ := exists_nhd R I X Z φ p hφ hc z hIz
      exact hz (TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU⟩, hzU⟩)
    exact TopologicalSpace.Opens.ext (by simpa [Set.compl_empty_iff] using h0)
  exact IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion)
    (fun U : {U : Z.Opens // IsClosedImmersion (φ ∣_ U)} => U.1) hO fun U => U.2

end GlobalTheory.ClosedLev
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.RosatiDescent

open GlobalTheory.CechPic

theorem lift_left_fst {S : Scheme.{0}} {A T : Over S} (f g : T ⟶ A) :
    (lift f g).left ≫ (fst A A).left = f.left :=
  congrArg (fun q => q.left) (lift_fst f g)

theorem lift_left_snd {S : Scheme.{0}} {A T : Over S} (f g : T ⟶ A) :
    (lift f g).left ≫ (snd A A).left = g.left :=
  congrArg (fun q => q.left) (lift_snd f g)

theorem eSec_comp_of_isMonHom {S : Scheme.{0}} {A : Over S} [GrpObj A] (u : A ⟶ A) [IsMonHom u] :
    eSec A ≫ u.left = eSec A := by
  show (η[A] ≫ u).left = η[A].left
  rw [IsMonHom.one_hom]

theorem lbIso_act_descent : ∀ (O : Type) [Ring O] (star : O → O) (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left) (act : OActN O A) (act₀ : OActN O A₀), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∃ t : (P₀.pull (eSec (G2 A₀))).Gen, t.IsGen) → (∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left) → (∀ c, LBIso (P.pull (lift (fst A A ≫ act.act c) (snd A A)).left) (P.pull (lift (fst A A) (snd A A ≫ act.act (star c))).left)) → ∀ c, LBIso (P₀.pull (lift (fst A₀ A₀ ≫ act₀.act c) (snd A₀ A₀)).left) (P₀.pull (lift (fst A₀ A₀) (snd A₀ A₀ ≫ act₀.act (star c))).left) := by
  intro O _ star X Y π Ga _ ρ A _ _ A₀ _ _ φ φ₂ P P₀ act act₀ hG hA hA₀ gp hsq hP hP₀ iP _ hact hros c
  have := hG.fin
  have := hG.etale
  have := hG.onto
  have hB : IsAbelianScheme (G2 A₀) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA₀ hA₀
  have h₁ := pull_isLB hP₀ (lift (fst A₀ A₀ ≫ act₀.act c) (snd A₀ A₀)).left
  have h₂ := pull_isLB hP₀ (lift (fst A₀ A₀) (snd A₀ A₀ ≫ act₀.act (star c))).left
  have hN := LB.isLB_div h₂ h₁
  have cN := cls_div h₂ h₁ hN
  rw [cls_pull hP₀, cls_pull hP₀] at cN
  have m₀ := act₀.hom c
  have m₀' := act₀.hom (star c)
  have c₁ : φ₂ ≫ (lift (fst A₀ A₀ ≫ act₀.act c) (snd A₀ A₀)).left =
      (lift (fst A A ≫ act.act c) (snd A A)).left ≫ φ₂ := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst A₀ A₀).left = (_ ≫ _) ≫ (fst A₀ A₀).left
      rw [Category.assoc, lift_left_fst, Category.assoc, hsq.1, ← Category.assoc, lift_left_fst]
      show φ₂ ≫ (fst A₀ A₀).left ≫ (act₀.act c).left = (fst A A).left ≫ (act.act c).left ≫ φ
      rw [reassoc_of% hsq.1, hact]
    · show (_ ≫ _) ≫ (snd A₀ A₀).left = (_ ≫ _) ≫ (snd A₀ A₀).left
      rw [Category.assoc, lift_left_snd, Category.assoc, hsq.2, ← Category.assoc, lift_left_snd]
  have c₂ : φ₂ ≫ (lift (fst A₀ A₀) (snd A₀ A₀ ≫ act₀.act (star c))).left =
      (lift (fst A A) (snd A A ≫ act.act (star c))).left ≫ φ₂ := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst A₀ A₀).left = (_ ≫ _) ≫ (fst A₀ A₀).left
      rw [Category.assoc, lift_left_fst, Category.assoc, hsq.1, ← Category.assoc, lift_left_fst]
    · show (_ ≫ _) ≫ (snd A₀ A₀).left = (_ ≫ _) ≫ (snd A₀ A₀).left
      rw [Category.assoc, lift_left_snd, Category.assoc, hsq.2, ← Category.assoc, lift_left_snd]
      show φ₂ ≫ (snd A₀ A₀).left ≫ (act₀.act (star c)).left = (snd A A).left ≫ (act.act (star c)).left ≫ φ
      rw [reassoc_of% hsq.2, hact]
  have e₁ : eSec (G2 A₀) ≫ (lift (fst A₀ A₀ ≫ act₀.act c) (snd A₀ A₀)).left = eSec (G2 A₀) := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst A₀ A₀).left = _ ≫ (fst A₀ A₀).left
      rw [Category.assoc, lift_left_fst, GlobalTheory.SquareDescent.eSec_fst]
      show eSec (G2 A₀) ≫ (fst A₀ A₀).left ≫ (act₀.act c).left = _
      rw [reassoc_of% GlobalTheory.SquareDescent.eSec_fst, eSec_comp_of_isMonHom]
    · show (_ ≫ _) ≫ (snd A₀ A₀).left = _ ≫ (snd A₀ A₀).left
      rw [Category.assoc, lift_left_snd]
  have e₂ : eSec (G2 A₀) ≫ (lift (fst A₀ A₀) (snd A₀ A₀ ≫ act₀.act (star c))).left = eSec (G2 A₀) := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst A₀ A₀).left = _ ≫ (fst A₀ A₀).left
      rw [Category.assoc, lift_left_fst]
    · show (_ ≫ _) ≫ (snd A₀ A₀).left = _ ≫ (snd A₀ A₀).left
      rw [Category.assoc, lift_left_snd, GlobalTheory.SquareDescent.eSec_snd]
      show eSec (G2 A₀) ≫ (snd A₀ A₀).left ≫ (act₀.act (star c)).left = _
      rw [reassoc_of% GlobalTheory.SquareDescent.eSec_snd, eSec_comp_of_isMonHom]
  have hPφ : pull φ₂ (cls _ hP₀) = cls _ hP := ((cls_eq_iff hP (pull_isLB hP₀ φ₂)).2 iP).symm
  have hR : pull (lift (fst A A ≫ act.act c) (snd A A)).left (cls _ hP) =
      pull (lift (fst A A) (snd A A ≫ act.act (star c))).left (cls _ hP) :=
    (cls_eq_iff (pull_isLB hP _) (pull_isLB hP _)).2 (hros c)
  have hpb := GlobalTheory.SiegelDescent.isPullback_square gp.1 φ₂ hsq
  have z₁ : pull (eSec (G2 A₀)) (cls _ hN) = 0 := by
    rw [cN, map_sub, ← pull_comp, ← pull_comp, e₁, e₂, sub_self]
  have z₂ : pull (pullback.fst (G2 A₀).hom π) (cls _ hN) = 0 := by
    rw [cN, ← hpb.isoPullback_inv_fst, pull_comp, map_sub, ← pull_comp φ₂, ← pull_comp φ₂, c₁, c₂,
      pull_comp, pull_comp, hPφ, hR, sub_self, map_zero]
  obtain ⟨t, ht⟩ := GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange GlobalTheory.SemiRigid.globalFns Y X π (G2 A₀) _ hB hN
    inferInstance inferInstance inferInstance
    ((cls_eq_zero_iff (pull_isLB hN _)).1 ((cls_pull hN _ _).trans z₁))
    ((cls_eq_zero_iff (pull_isLB hN _)).1 ((cls_pull hN _ _).trans z₂))
  have h0 : cls _ hN = 0 := (cls_eq_zero_iff hN).2 ⟨t, ht⟩
  rw [cN, sub_eq_zero, ← cls_pull hP₀ _ h₁, ← cls_pull hP₀ _ h₂] at h0
  exact (cls_eq_iff h₁ h₂).1 h0.symm

end GlobalTheory.RosatiDescent
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

theorem _root_.GlobalTheory.T.exists_harrisTaylorObjectMap_of_common_pullback : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S₀ : Scheme.{0}) (A₀ : Over S₀) [GrpObj A₀] (P₀ : LB (G2 A₀).left), P₀.IsLB → ∀ (T Z : Scheme.{0}) (t₁ : T ⟶ Sp R) (t₂ : Z ⟶ Sp R) (o : Obj b N t₁) (u : Obj b N t₂) (g : T ⟶ S₀) (πZ : Z ⟶ S₀) (z : T ⟶ Z) (φo : o.A.left ⟶ A₀.left) (φ₂o : (G2 o.A).left ⟶ (G2 A₀).left) (φu : u.A.left ⟶ A₀.left) (φ₂u : (G2 u.A).left ⟶ (G2 A₀).left) (ψ : o.A.left ⟶ u.A.left), IsGrpPullback o.A A₀ g φo → IsSquare φo φ₂o → LBIso o.P (P₀.pull φ₂o) → IsGrpPullback u.A A₀ πZ φu → IsSquare φu φ₂u → LBIso u.P (P₀.pull φ₂u) → z ≫ πZ = g → ψ ≫ φu = φo → ψ ≫ u.A.hom = o.A.hom ≫ z → (∀ a : D.O, (o.act.act a).left ≫ ψ = ψ ≫ (u.act.act a).left) → (∀ y, (o.eta y).left ≫ ψ = z ≫ (u.eta y).left) → ∃ m : ObjMap o u z, m.φ = ψ := by
  first | (exact @GlobalTheory.HTObjMap.exists_objMap_of_common_pullback) | (exact GlobalTheory.HTObjMap.exists_objMap_of_common_pullback) | (intros; apply GlobalTheory.HTObjMap.exists_objMap_of_common_pullback  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

theorem _root_.GlobalTheory.T.exists_spanning_posDef_relation_harrisTaylorOrder : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), ∃ (r : ℕ) (e : Fin r → D.Oᵐᵒᵖ) (W : Matrix (Fin r) (Fin r) ℤ) (d : ℕ), Submodule.span ℤ (Set.range e) = ⊤ ∧ ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef ∧ 0 < d ∧ ∑ i, ∑ j, W i j • (e j * MulOpposite.op ((D.star (e i).unop).unop)) = (d : D.Oᵐᵒᵖ) := by
  first | (exact @GlobalTheory.CasimirOrder.exists_posdef_relation) | (exact GlobalTheory.CasimirOrder.exists_posdef_relation) | (intros; apply GlobalTheory.CasimirOrder.exists_posdef_relation  <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.HeckeWeilValue

open GlobalTheory.CechPic

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

theorem lbIso_mulA_diag (hA : IsAbelianScheme A) {P : LB (G2 A).left} (hP : P.IsLB)
    (hamp : Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left))
    (h₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen)
    (h₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) (k : ℕ) :
    LBIso (lbPow (P.pull (lift (𝟙 A) (𝟙 A)).left) (k ^ 2))
      ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull (Out.mulA A k).left) := by
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have hB : ∀ (T : Over S) (x x' y : T ⟶ A), DiagPairing.pc hP (x * x') y =
      DiagPairing.pc hP x y + DiagPairing.pc hP x' y := fun T x x' y => by
    obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A _ hA hD hamp P hP h₁ h₂ T x x' y).1
    have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, one_smul, neg_smul] at e
    unfold DiagPairing.pc
    rw [← sub_eq_zero, ← e]
    abel
  have hB' : ∀ (T : Over S) (x y y' : T ⟶ A), DiagPairing.pc hP x (y * y') =
      DiagPairing.pc hP x y + DiagPairing.pc hP x y' := fun T x y y' => by
    obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A _ hA hD hamp P hP h₁ h₂ T y y' x).2
    have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, one_smul, neg_smul] at e
    unfold DiagPairing.pc
    rw [← sub_eq_zero, ← e]
    abel
  refine (cls_eq_iff (LB.isLB_linComb hD _ _) (pull_isLB hD _)).1 ?_
  rw [cls_lbPow hD, cls_pull hD, cls_pull hP, ← pull_comp, ← Over.comp_left, comp_lift, Category.comp_id]
  have e1 : pull (lift (Out.mulA A k) (Out.mulA A k)).left (cls P hP) =
      DiagPairing.pc hP (Out.mulA A k) (Out.mulA A k) := rfl
  have e2 : pull (lift (𝟙 A) (𝟙 A)).left (cls P hP) = DiagPairing.pc hP (𝟙 A) (𝟙 A) := rfl
  rw [e1, e2, Out.mulA, DiagPairing.pc_pow_left hP hB, DiagPairing.pc_pow_right hP hB', smul_smul, sq]

end GlobalTheory.HeckeWeilValue


open GlobalTheory.HeckeWeilValue in
theorem GlobalTheory.UPel.HT.Hecke.weil_value_translate : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k M : ℕ), c.Coprime p → k.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (β : R →+* κ), x ≫ s = spMap β → ∀ (I : TateIsoO D κ (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c) (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z))) (n : ℕ), 0 < n → n.Coprime p → ∀ (u v : D.La) (e : (Γ((Over.mk x).left, ⊤))ˣ), Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) ((n * (k ^ 2 / c) : ℕ) : ℤ) (I.ev (n * k) (g u)) (I.ev (n * k) (g v)) e → e = unitOn (I.ζ n ^ (2 * D.EF u v)) := by
  intro p _ D R _ b g c k M hc hk hEF _ hck S s o κ _ _ x β _ I n hn hnp u v e he
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hL : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB := pull_isLB o.isLB _
  have hk0 : 0 < k := levelPos_of_coprime hk
  have hc0 : 0 < c := levelPos_of_coprime hc
  have hmc : k ^ 2 / c * c = k ^ 2 := Nat.div_mul_cancel hck
  have hm0 : 0 < k ^ 2 / c := Nat.div_pos (Nat.le_of_dvd (by positivity) hck) hc0
  have hmp : (k ^ 2 / c).Coprime p := Nat.Coprime.coprime_dvd_left (Dvd.intro c hmc) (Nat.Coprime.pow_left 2 hk)
  set m := k ^ 2 / c with hm
  have hN : 0 < n * (m * k ^ 2) := by positivity
  have hNp : (n * (m * k ^ 2)).Coprime p :=
    Nat.Coprime.mul_left hnp (Nat.Coprime.mul_left hmp (Nat.Coprime.pow_left 2 hk))
  have eN : n * (m * k ^ 2) = n * k * (m * k) := by ring
  have hev : ∀ w : D.La, I.ev (n * k) (g w) = I.ev (n * (m * k ^ 2)) (m • g w) ≫ Out.mulA o.A k := fun w => by
    rw [Out.mulA, MonObj.comp_pow, Category.comp_id, ← TateIsoO.ev_nsmul, smul_smul, mul_comm k m,
      TateIsoO.ev_nsmul, eN, I.tower (n * k) (m * k) (by positivity) (by positivity) (by rw [← eN]; exact hNp)]
  letI : IsCommMonObj o.A := o.ab.comm
  haveI : IsMonHom (Out.mulA o.A k) := by
    change IsMonHom ((𝟙 o.A) ^ k)
    constructor
    · rw [MonObj.comp_pow, Category.comp_id, MonObj.one_eq_one, one_pow]
    · rw [MonObj.comp_pow, Category.comp_id, MonObj.mul_eq_mul, MonObj.comp_mul, tensorHom_fst,
        tensorHom_snd, MonObj.comp_pow, MonObj.comp_pow, Category.comp_id, Category.comp_id, mul_pow]
  have hw := lbIso_mulA_diag o.ab o.isLB o.ample o.rig₁ o.rig₂ k
  rw [hev u, hev v] at he
  have h1 := GlobalTheory.WeilIsogeny.weilIs_pull_hom hG o.ab hL hL (Out.mulA o.A k) hw he
  have h2 := I.isom (n * (m * k ^ 2)) hN hNp (m • g u) (m • g v)
  have eZ : ((n * m : ℕ) : ℤ) * ((k ^ 2 : ℕ) : ℤ) = ((n * (m * k ^ 2) : ℕ) : ℤ) := by push_cast; ring
  rw [eZ] at h1
  rw [GlobalTheory.CommutatorPairing.weilIs_unique hG o.ab hL h1 h2]
  congr 1
  have eF : D.EF (m • g u) (m • g v) = ((m * k ^ 2 : ℕ) : ℤ) * D.EF u v := by
    simp only [map_nsmul, LinearMap.smul_apply, hEF, nsmul_eq_mul]
    rw [← hmc]
    push_cast
    ring
  rw [eF, show (2 : ℤ) * (((m * k ^ 2 : ℕ) : ℤ) * D.EF u v) = ((m * k ^ 2 : ℕ) : ℤ) * (2 * D.EF u v) by ring,
    zpow_mul, zpow_natCast, I.ζ_pow n (m * k ^ 2) hn (by positivity) hNp]
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegRigid

open GlobalTheory.CechPic GlobalTheory.AmpleRigid

theorem serreAmple : SerreAmpleSt :=
  serreAmple_of_finiteOrder_of_separated (GlobalTheory.AmpleFiniteOrder.finiteOrder_of_const_of_cube constSt GlobalTheory.AmpleCube.cubeSt)
    (separatedSt_of_const_cube constSt GlobalTheory.AmpleCube.cubeSt)

theorem exists_aut {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ φ' : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) (h' : IsGrpPullback A' A f φ') :
    ∃ σ : A' ≅ A', IsMonHom σ.hom ∧ σ.hom.left ≫ φ' = φ := by
  let ψ : A'.left ⟶ A'.left := h'.1.lift φ A'.hom h.1.w
  have e₁ : ψ ≫ φ' = φ := h'.1.lift_fst _ _ _
  have e₂ : ψ ≫ A'.hom = A'.hom := h'.1.lift_snd _ _ _
  have hψ : IsGrpPullback A' A' (𝟙 _) ψ :=
    IsGrpPullback.cancel h' (by rw [Category.id_comp, e₁]; exact h) (by rw [e₂, Category.comp_id])
  haveI : IsIso ψ := hψ.1.isIso_fst_of_isIso
  let σ : A' ≅ A' := Over.isoMk (asIso ψ) e₂
  exact ⟨σ, isMonHom_of_mul_comp σ.hom fun T x y => mul_comp_of_grpPullback_id σ.hom hψ x y, e₁⟩

theorem eq_of_field {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) (hamp : Out.RelAmple A L)
    {K : Type} [Field K] [IsAlgClosed K] {A' : Over (Sp K)} [GrpObj A'] (hA' : IsAbelianScheme A') {z : Sp K ⟶ S}
    {φ φ' : A'.left ⟶ A.left} (h : IsGrpPullback A' A z φ) (h' : IsGrpPullback A' A z φ')
    (hc : pull φ (cls L hL) = pull φ' (cls L hL)) {N : ℕ} (hN : 3 ≤ N) (hNK : (N : K) ≠ 0)
    (hfix : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Sp K) (x : Over.mk t ⟶ A'), x ^ N = 1 →
      x.left ≫ φ = x.left ≫ φ') : φ = φ' := by
  obtain ⟨σ, hσ, e⟩ := exists_aut h h'
  have := hA'.comm
  have hL' := pull_isLB hL φ'
  obtain ⟨w, hw⟩ := (cls_eq_iff hL' hL').1 rfl
  obtain ⟨U, hU, hcl, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤)
    (x := z (IsLocalRing.closedPoint K)) trivial
  have hy : ∀ y, z y ∈ U := fun y =>
    (congrArg (fun V => y ∈ V) (Scheme.preimage_eq_top_of_closedPoint_mem z hcl)).mpr trivial
  have key := serreAmple K A' hA' (L.pull φ') hL'
    (relAmple_pull h'.1 hL hL' ((isGen_iff w).1 hw) U hU hy hamp) N hN hNK σ hσ
    (by rw [cls_pull hL, ← pull_comp, e, hc]) fun Ω _ _ t x hx => by
      apply Over.OverMorphism.ext
      apply h'.1.hom_ext
      · rw [Over.comp_left, Category.assoc, e]
        exact hfix Ω t x hx
      · rw [Over.w, Over.w]
  rw [← e, key, Over.id_left, Category.id_comp]

variable {h n n' : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {ζ' : B'} {S S' : Scheme.{0}}
  {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'}

theorem pull_cls_diag {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {φ : c'.A.left ⟶ c.A.left}
    {φ₂ : (G2 c'.A).left ⟶ (G2 c.A).left} (hs : IsSquare φ φ₂) (hw : LBIso c'.P (c.P.pull φ₂)) :
    pull φ (cls c.diag (pull_isLB c.isLB _)) = cls c'.diag (pull_isLB c'.isLB _) := by
  have e : (lift (𝟙 c'.A) (𝟙 c'.A)).left ≫ φ₂ = φ ≫ (lift (𝟙 c.A) (𝟙 c.A)).left := by
    have a₁ := congrArg (fun q => q.left) (lift_fst (𝟙 c.A) (𝟙 c.A))
    have a₂ := congrArg (fun q => q.left) (lift_snd (𝟙 c.A) (𝟙 c.A))
    have b₁ := congrArg (fun q => q.left) (lift_fst (𝟙 c'.A) (𝟙 c'.A))
    have b₂ := congrArg (fun q => q.left) (lift_snd (𝟙 c'.A) (𝟙 c'.A))
    simp only [Over.comp_left, Over.id_left] at a₁ a₂ b₁ b₂
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst c.A c.A).left = (_ ≫ _) ≫ (fst c.A c.A).left
      rw [Category.assoc, hs.1, ← Category.assoc, b₁, Category.assoc, a₁]; simp
    · show (_ ≫ _) ≫ (snd c.A c.A).left = (_ ≫ _) ≫ (snd c.A c.A).left
      rw [Category.assoc, hs.2, ← Category.assoc, b₂, Category.assoc, a₂]; simp
  have h1 : pull φ₂ (cls c.P c.isLB) = cls c'.P c'.isLB :=
    ((cls_eq_iff c'.isLB (pull_isLB c.isLB φ₂)).2 hw).symm
  unfold SiegPre.diag
  rw [cls_pull c.isLB, cls_pull c'.isLB, ← pull_comp, ← e, pull_comp, h1]

theorem eq_on_torsion (hζ : IsUnit ζ) (c : SiegPre h n ζ s) {A' : Over S'} [GrpObj A'] {f : S' ⟶ S}
    {φ φ' : A'.left ⟶ c.A.left} (hφ : IsGrpPullback A' c.A f φ)
    (lv : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S') ⟶ A'))
    (h₁ : ∀ a, (lv a).left ≫ φ = f ≫ (c.lev a).left) (h₂ : ∀ a, (lv a).left ≫ φ' = f ≫ (c.lev a).left)
    (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S') (y : Over.mk x ⟶ A') (hy : y ^ n = 1) :
    y.left ≫ φ = y.left ≫ φ' := by
  let β : B →+* k := (Spec.preimage ((x ≫ f) ≫ s)).hom
  obtain ⟨-, hs, -⟩ := c.geom k (x ≫ f) β (hζ.map β).unit (Spec.map_preimage _).symm rfl
  have hy₁ : pushHom hφ (Over.mk x) y ^ n = 1 := by rw [← map_pow, hy, map_one]
  obtain ⟨a, ha⟩ := hs _ hy₁
  have hu : (toUnit (Over.mk (x ≫ f))).left = x ≫ f := (Category.comp_id _).symm.trans (Over.w (toUnit _))
  have e : (x ≫ f) ≫ (c.lev a).left = y.left ≫ φ := by
    rw [← hu]
    exact congrArg (fun q => q.left) ha
  have e₁ : y.left = x ≫ (lv a).left := by
    apply hφ.1.hom_ext
    · rw [Category.assoc]
      exact e.symm.trans ((Category.assoc _ _ _).trans (congrArg (x ≫ ·) (h₁ a).symm))
    · rw [Over.w, Category.assoc, Over.w]
      exact (Category.comp_id _).symm
  rw [e₁, Category.assoc, Category.assoc]
  exact congrArg (x ≫ ·) ((h₁ a).trans (h₂ a).symm)

theorem eq_of_sRelBy : ∀ (h n n' d' : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (b : TBase B n) (ζ' : B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (c : SiegPre h n (b.ζ : B) s) (c' : SiegPre h n' ζ' s') (f : S' ⟶ S) (φ φ' : c'.A.left ⟶ c.A.left), 3 ≤ n → Odd n → c.Principal → SRelBy c' c d' 1 f φ → SRelBy c' c d' 1 f φ' → φ = φ' := by
  intro h n n' d' B B' _ _ b ζ' S S' s s' c c' f φ φ' hn _ hc ⟨g, ⟨φ₂, q, w⟩, l⟩ ⟨g', ⟨φ₂', q', w'⟩, l'⟩
  simp only [pow_one] at l l'
  obtain ⟨σ, hσ, e⟩ := exists_aut g g'
  have key : σ.hom = 𝟙 _ := by
    refine eq_id_of_forall_geometric_fibre laws_without_cohomology.1 c'.A c'.ab σ.hom (IsMonHom.one_hom σ.hom)
      fun t => ?_
    let K : Type := AlgebraicClosure (S'.residueField t)
    let j : Sp K ⟶ S' := Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField t) K)) ≫ S'.fromSpecResidueField t
    have hp := isGrpPullback_pullback c'.A j
    have := c'.ab.smooth
    have := c'.ab.proper
    have := c'.ab.geomConnected
    have hab : IsAbelianScheme ((Over.pullback j).obj c'.A) :=
      { comm := Functor.isCommMonObj_obj
        smooth := by change Smooth (pullback.snd c'.A.hom j); infer_instance
        proper := by change IsProper (pullback.snd c'.A.hom j); infer_instance
        geomConnected := by change GeometricallyConnected (pullback.snd c'.A.hom j); infer_instance }
    have hNK : (n : K) ≠ 0 := by
      have hu := b.unit.map (Spec.preimage ((j ≫ f) ≫ s)).hom
      rw [map_natCast] at hu
      exact hu.ne_zero
    have e' := eq_of_field (pull_isLB c.isLB _) hc.1 hab (hp.comp g) (hp.comp g')
      (by rw [pull_comp, pull_comp]; exact congrArg _ ((pull_cls_diag q w).trans (pull_cls_diag q' w').symm)) hn hNK
      fun Ω _ _ x y hy => by
        have hy₁ : pushHom hp (Over.mk x) y ^ n = 1 := by rw [← map_pow, hy, map_one]
        have e₁ := eq_on_torsion b.ζ.isUnit c g _ l l' Ω (x ≫ j) _ hy₁
        rw [← Category.assoc, ← Category.assoc]
        exact e₁
    refine ⟨_, _, j, _, _, (default : PrimeSpectrum K), ?_, hp.1, ?_⟩
    · exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply t _)
    · apply g'.1.hom_ext
      · rw [Category.assoc, e]
        exact e'
      · rw [Category.assoc, Over.w]
  rw [← e, key, Over.id_left, Category.id_comp]

end GlobalTheory.SiegRigid
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.principal_descent_finite_etale_surjective : ∀ (h M M₀ d d₀ : ℕ) (B B₀ : Type) [CommRing B] [CommRing B₀] (ζ : B) (ζ₀ : B₀) (X Y : Scheme.{0}) [IsLocallyNoetherian Y] (s : X ⟶ Sp B) (s₀ : Y ⟶ Sp B₀) (π : X ⟶ Y) (c : SiegPre h M ζ s) (c₀ : SiegPre h M₀ ζ₀ s₀), IsFinite π → Etale π → Surjective π → SRel c c₀ d d₀ π → c.Principal → c₀.Principal := by
  first | exact @GlobalTheory.SiegLevDescent.principal_of_sRel_finite_etale | exact GlobalTheory.SiegLevDescent.principal_of_sRel_finite_etale | (intros; apply GlobalTheory.SiegLevDescent.principal_of_sRel_finite_etale <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.descendedData_transport_identity_levelChange : ∀ (h n N d : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (ζ' : B') (X Y : Scheme.{0}) (s : X ⟶ Sp B) (s' : X ⟶ Sp B') (C : SiegPre h N ζ' s') (c : SiegPre h n ζ s) (π : X ⟶ Y) (A₀ : Over Y) [GrpObj A₀] (φ : C.A.left ⟶ A₀.left) (φ₂ : (G2 C.A).left ⟶ (G2 A₀).left) (P₀ : LB (G2 A₀).left) (lev₀ : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over Y) ⟶ A₀)), SRel C c d 1 (𝟙 X) → IsGrpPullback C.A A₀ π φ → IsSquare φ φ₂ → P₀.IsLB → LBIso C.P (P₀.pull φ₂) → (∀ a, (C.lev a ^ d).left ≫ φ = π ≫ (lev₀ a).left) → ∃ (φ' : c.A.left ⟶ A₀.left) (φ₂' : (G2 c.A).left ⟶ (G2 A₀).left), IsGrpPullback c.A A₀ π φ' ∧ IsSquare φ' φ₂' ∧ LBIso c.P (P₀.pull φ₂') ∧ ∀ a, (c.lev a).left ≫ φ' = π ≫ (lev₀ a).left := by
  first | exact @GlobalTheory.SiegLev.descData_transport_id | exact GlobalTheory.SiegLev.descData_transport_id | (intros; apply GlobalTheory.SiegLev.descData_transport_id <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_siegelObject_lowered_level : ∀ (h n N : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (ζ' : B') (j : B →+* B') (S : Scheme.{0}) (s' : S ⟶ Sp B') (C : SiegPre h N ζ' s'), N ≠ 0 → IsUnit (N : B') → n ∣ N → j ζ = ζ' ^ (N / n) → ∃ c : SiegPre h n ζ (s' ≫ spMap j), SRel C c (N / n) 1 (𝟙 S) ∧ SRel c C 1 (N / n) (𝟙 S) := by
  first | exact @GlobalTheory.SiegLower.exists_lower | exact GlobalTheory.SiegLower.exists_lower | (intros; apply GlobalTheory.SiegLower.exists_lower <;> assumption)
end
