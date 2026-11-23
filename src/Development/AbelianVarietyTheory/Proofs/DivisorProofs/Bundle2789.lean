module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2755
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2725
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2760
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle074
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomOfDerivation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2752
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle671
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle533
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle191
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2683
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle033
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsSharpAndPrim
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2690
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.TranslHoriz

theorem isHoriz_of_comm : ∀ (k : Type) [Field k] (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) (_ : GrpObj B') (π₁ π₂ : B'.left ⟶ A.left), IsGrpPullback B' A (spMap ρ) π₁ → IsGrpPullback B' A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ (A₀ : Over (Sp k)) (_ : GrpObj A₀) (m₀ : A₀.left ⟶ A.left), IsGrpPullback A₀ A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ (dl : ∀ W : A.left.Opens, Γ(A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)), GlobalTheory.KS.LocDerK A₀.hom A.hom m₀ (fun r => (ρ r).snd) ⊤ dl → ∀ (s : 𝟙_ (Over (Sp R)) ⟶ A) (T₀ : A₀.left ⟶ A₀.left), T₀ ≫ m₀ = m₀ ≫ (lift (toUnit A ≫ s) (𝟙 A) ≫ μ[A]).left → T₀ ≫ A₀.hom = A₀.hom → (∀ (W : A.left.Opens) (f : Γ(A.left, W)), dl ((lift (toUnit A ≫ s) (𝟙 A) ≫ μ[A]).left ⁻¹ᵁ W) (((lift (toUnit A ≫ s) (𝟙 A) ≫ μ[A]).left.app W).hom f) = pbT T₀ (dl W f) (m₀ ⁻¹ᵁ ((lift (toUnit A ≫ s) (𝟙 A) ≫ μ[A]).left ⁻¹ᵁ W))) → ∀ x : Sp (DualNumber k) ⟶ B'.left, x ≫ B'.hom = 𝟙 _ → x ≫ π₁ = spMap ρ ≫ s.left → x ≫ π₂ = spMap (constHom ρ) ≫ s.left := by
  intro k _ R _ A _ hA ρ B' _ π₁ π₂ h₁ h₂ hcl A₀ _ m₀ hm₀ dl hdl s T₀ hT₀ hT₀h hcomm x hx hx1
  set fst := (TrivSqZeroExt.fstHom k k k).toRingHom with hfst
  set alg := algebraMap k (DualNumber k) with halg
  have e_fa : spMap fst ≫ spMap alg = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]; congr 1
  have e_c : spMap (constHom ρ) = spMap alg ≫ spMap (fst.comp ρ) := by
    simp only [spMap, constHom, ← Spec.map_comp]; rfl
  have e_r : spMap (fst.comp ρ) = spMap fst ≫ spMap ρ := by
    simp only [spMap, ← Spec.map_comp]; rfl
  have P₁ := h₁.1
  have P₂ := h₂.1
  have P₀ := hm₀.1
  have wr : π₂ ≫ A.hom = (B'.hom ≫ spMap alg) ≫ spMap (fst.comp ρ) := by
    rw [P₂.w, e_c, Category.assoc]
  let r : B'.left ⟶ A₀.left := P₀.lift π₂ (B'.hom ≫ spMap alg) wr
  have hr1 : r ≫ m₀ = π₂ := P₀.lift_fst _ _ _
  have hr2 : r ≫ A₀.hom = B'.hom ≫ spMap alg := P₀.lift_snd _ _ _
  have Pr : IsPullback r B'.hom A₀.hom (spMap alg) := by
    refine IsPullback.of_right ?_ hr2 P₀
    rw [hr1, ← e_c]; exact P₂
  have wj : m₀ ≫ A.hom = (A₀.hom ≫ spMap fst) ≫ spMap (constHom ρ) := by
    rw [P₀.w, Category.assoc, e_c, ← Category.assoc (spMap fst), e_fa, Category.id_comp]
  let j : A₀.left ⟶ B'.left := P₂.lift m₀ (A₀.hom ≫ spMap fst) wj
  have hj1 : j ≫ π₂ = m₀ := P₂.lift_fst _ _ _
  have hj2 : j ≫ B'.hom = A₀.hom ≫ spMap fst := P₂.lift_snd _ _ _
  have hjr : j ≫ r = 𝟙 _ := P₀.hom_ext (by rw [Category.assoc, hr1, hj1, Category.id_comp])
    (by rw [Category.assoc, hr2, ← Category.assoc, hj2, Category.assoc, e_fa, Category.comp_id, Category.id_comp])
  have hjπ₁ : j ≫ π₁ = m₀ := by rw [hcl A₀.left j A₀.hom hj2, hj1]
  obtain ⟨-, Pj, -⟩ := GlobalTheory.ConstThickening.structure_dualNumber k A₀.left B'.left A₀.hom B'.hom r j Pr hjr hj2
  have hjs : Surjective j :=
    MorphismProperty.of_isPullback (P := @Surjective) Pj.flip GlobalTheory.ConstThickening.surjective_spMap_fst
  have hm : m₀ ≫ A.hom = A₀.hom ≫ spMap fst ≫ spMap ρ := by rw [P₀.w, e_r]
  obtain ⟨Φ, hΦj, hΦp, hΦ⟩ := GlobalTheory.KS.DerMorK.exists_hom_of_derivation k A₀.left B'.left A₀.hom B'.hom r j Pr hjr hj2
    R ρ A.left A.hom m₀ dl hm hdl
  have hb : ∀ y, Φ y = m₀ (r y) := by
    intro y
    obtain ⟨y₀, rfl⟩ := hjs.surj y
    show (j ≫ Φ) y₀ = (j ≫ r ≫ m₀) y₀
    rw [hΦj, ← Category.assoc, hjr, Category.id_comp]
  have wT : (r ≫ T₀) ≫ A₀.hom = B'.hom ≫ spMap alg := by rw [Category.assoc, hT₀h, hr2]
  let TB : B'.left ⟶ B'.left := Pr.lift (r ≫ T₀) B'.hom wT
  have hTB1 : TB ≫ r = r ≫ T₀ := Pr.lift_fst _ _ _
  have hTB2 : TB ≫ B'.hom = B'.hom := Pr.lift_snd _ _ _
  have hcΦ : TB ≫ Φ = Φ ≫ (lift (toUnit A ≫ s) (𝟙 A) ≫ μ[A]).left :=
    GlobalTheory.T.firstOrderLift_derivation_comm_translations k A₀.left B'.left A.left m₀ B'.hom r dl Φ hb hΦ _ T₀ TB hT₀ hTB1 hTB2 hcomm
  let α : B'.left ⟶ B'.left := P₁.lift Φ B'.hom hΦp
  have hα1 : α ≫ π₁ = Φ := P₁.lift_fst _ _ _
  have hα2 : α ≫ B'.hom = B'.hom := P₁.lift_snd _ _ _
  have hjα : j ≫ α = j := P₁.hom_ext (by rw [Category.assoc, hα1, hΦj, hjπ₁]) (by rw [Category.assoc, hα2])
  let αo : B' ⟶ B' := Over.homMk α hα2
  have hB' : IsAbelianScheme B' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h₁
  set w : 𝟙_ (Over (Sp (DualNumber k))) ⟶ B' := η[B'] ≫ αo with hw
  have hαo : αo = lift (toUnit B' ≫ w) (𝟙 B') ≫ μ[B'] := GlobalTheory.T.abelianScheme_dualNumber_endo_eq_translation k B' hB' αo (fun Z z y hz => by
    change z ≫ α = z
    rw [← Pj.lift_fst z y hz, Category.assoc, hjα])
  let xo : 𝟙_ (Over (Sp (DualNumber k))) ⟶ B' := Over.homMk x hx
  have wσ : (spMap (constHom ρ) ≫ s.left) ≫ A.hom = 𝟙 _ ≫ spMap (constHom ρ) := by
    rw [Category.assoc, Over.w s, Category.id_comp]; rfl
  let σ : Sp (DualNumber k) ⟶ B'.left := P₂.lift (spMap (constHom ρ) ≫ s.left) (𝟙 _) wσ
  have hσ1 : σ ≫ π₂ = spMap (constHom ρ) ≫ s.left := P₂.lift_fst _ _ _
  have hσ2 : σ ≫ B'.hom = 𝟙 _ := P₂.lift_snd _ _ _
  let σo : 𝟙_ (Over (Sp (DualNumber k))) ⟶ B' := Over.homMk σ hσ2
  have tx := GlobalTheory.T.groupPullback_translation_comp_eq B' A (spMap ρ) π₁ h₁ xo s hx1
  have tσ := GlobalTheory.T.groupPullback_translation_comp_eq B' A (spMap (constHom ρ)) π₂ h₂ σo s hσ1
  have hTBσ : TB = (lift (toUnit B' ≫ σo) (𝟙 B') ≫ μ[B']).left := by
    refine P₂.hom_ext ?_ ?_
    · rw [tσ, ← hr1, ← Category.assoc, hTB1, Category.assoc, hT₀, ← Category.assoc]
    · rw [hTB2, Over.w]
  have hcα : αo ≫ (lift (toUnit B' ≫ xo) (𝟙 B') ≫ μ[B']) = (lift (toUnit B' ≫ σo) (𝟙 B') ≫ μ[B']) ≫ αo := by
    apply Over.OverMorphism.ext
    refine P₁.hom_ext ?_ ?_
    · show α ≫ (lift (toUnit B' ≫ xo) (𝟙 B') ≫ μ[B']).left ≫ π₁ =
        (lift (toUnit B' ≫ σo) (𝟙 B') ≫ μ[B']).left ≫ α ≫ π₁
      rw [tx, ← Category.assoc, hα1, ← hcΦ, hTBσ]
    · simp only [Over.comp_left, Category.assoc, Over.w]
  haveI : IsCommMonObj B' := hB'.comm
  have hτ : ∀ (u y : 𝟙_ (Over (Sp (DualNumber k))) ⟶ B'), y ≫ (lift (toUnit B' ≫ u) (𝟙 B') ≫ μ[B']) = u * y := by
    intro u y
    rw [← Category.assoc, comp_lift, ← Category.assoc, toUnit_unique (y ≫ toUnit B') (𝟙 _), Category.id_comp,
      Category.comp_id, ← Hom.mul_def]
  have h1 : (η[B'] : 𝟙_ _ ⟶ B') = 1 := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have e1 : η[B'] ≫ αo ≫ (lift (toUnit B' ≫ xo) (𝟙 B') ≫ μ[B']) = xo * w := by
    rw [← Category.assoc, ← hw, hτ]
  have e2 : η[B'] ≫ (lift (toUnit B' ≫ σo) (𝟙 B') ≫ μ[B']) ≫ αo = w * σo := by
    rw [← Category.assoc, hτ, h1, _root_.mul_one]
    nth_rewrite 1 [hαo]
    rw [hτ]
  have key : xo * w = w * σo := by
    rw [← e1, ← e2]
    exact congrArg (η[B'] ≫ ·) hcα
  have hxσ : xo = σo := by
    rw [_root_.mul_comm w σo] at key
    exact _root_.mul_right_cancel key
  have : x = σ := congrArg Over.Hom.left hxσ
  rw [this, hσ1]

end GlobalTheory.TranslHoriz
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

namespace GlobalTheory.NormBlowupInt

theorem isFinite_fromNormalization_int_of_isReduced {X Y : Scheme.{0}} {o : CommRingCat.{0}}
    [Algebra.FiniteType ℤ o] (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (g : Y ⟶ Spec o)
    [LocallyOfFiniteType g] [IsReduced X] [IsLocallyNoetherian X]
    (hess : ∀ x ∈ genericPoints X, (f.residueFieldMap x).hom.EssFiniteType) :
    IsFinite f.fromNormalization := by
  refine ⟨fun U hU => ?_⟩
  letI := (f.app U).hom.toAlgebra
  letI : Algebra o Γ(Y, U) := ((Scheme.ΓSpecIso o).inv ≫ g.appLE ⊤ U le_top).hom.toAlgebra
  haveI : Algebra.FiniteType o Γ(Y, U) :=
    (g.finiteType_appLE (isAffineOpen_top _) hU le_top).comp
      (.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso o).inv).2)
  haveI : Algebra.FiniteType ℤ Γ(Y, U) := .trans (S := o) inferInstance inferInstance
  haveI : IsNoetherianRing Γ(Y, U) := Algebra.FiniteType.isNoetherianRing ℤ _
  let D : Set X := genericPoints X
  have hD : Dense D := dense_iff_closure_eq.mpr genericPoints.closure
  let ι := ↥(D ∩ (f ⁻¹ᵁ U : X.Opens))
  haveI : Finite ι := (GlobalTheory.finite_genericPoints_inter _ (f.isCompact_preimage hU.isCompact)).to_subtype
  letI (x : ι) : Algebra Γ(Y, U) (X.residueField x.1) :=
    (f.app U ≫ X.evaluation (f ⁻¹ᵁ U) x.1 x.2.2).hom.toAlgebra
  haveI (x : ι) : Algebra.EssFiniteType Γ(Y, U) (X.residueField x.1) := by
    change (f.app U ≫ X.evaluation (f ⁻¹ᵁ U) x.1 x.2.2).hom.EssFiniteType
    rw [← Scheme.evaluation_naturality f (V := U) x.1 x.2.2]
    exact .comp (.comp (essFiniteType_germ hU (f x.1) x.2.2)
      (RingHom.FiniteType.of_surjective _ (Y.residue_surjective _)).essFiniteType) (hess _ x.2.1)
  haveI (x : ι) := GlobalTheory.ZMain.finite_integralClosure_field Γ(Y, U) (X.residueField x.1)
  haveI : Module.Finite Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)) := by
    refine finite_integralClosure_of_family (L := fun x : ι => X.residueField x.1)
      (fun x => { (X.evaluation (f ⁻¹ᵁ U) x.1 x.2.2).hom with commutes' := fun _ => rfl })
      fun b hb => ?_
    rw [← basicOpen_eq_bot_iff, eq_bot_iff]
    intro y hy
    obtain ⟨x, hx, hxD⟩ := hD.inter_open_nonempty _ (X.basicOpen b).isOpen ⟨y, hy⟩
    exact ((X.evaluation_eq_zero_iff_notMem_basicOpen x (X.basicOpen_le b hx) b).mp
      (hb ⟨x, hxD, X.basicOpen_le b hx⟩) hx).elim
  rw [f.fromNormalization_app hU]
  exact RingHom.Finite.comp
    (.of_surjective _ (ConcreteCategory.bijective_of_isIso (f.normalizationObjIso hU).inv).2)
    (RingHom.finite_algebraMap.mpr this)

theorem dense_preimage_of_blowup {Z X' : Scheme.{0}} (J : Z.IdealSheafData) (b : X' ⟶ Z)
    (hb : FinalTheorems.Blowup b J) (hiso : ∀ V : Z.Opens, (∀ x ∈ V, x ∉ J.support) → IsIso (b ∣_ V))
    (W : Z.Opens) (hWd : Dense (W : Set Z)) : Dense ((b ⁻¹ᵁ W : X'.Opens) : Set X') := by
  obtain ⟨D, hD⟩ := EffCartierData.exists_idealSheaf_eq hb.1
  have hD' : Dense (((J.comap b).support : Set X')ᶜ) := by
    rw [← hD, ← D.coe_nonzeroLocus_canonical]
    exact D.dense_nonzeroLocus_canonical
  let Uc : Z.Opens := J.support.compl
  haveI : IsIso (b ∣_ Uc) := hiso Uc fun x hx => hx
  haveI hoi : IsOpenImmersion ((b ⁻¹ᵁ Uc).ι ≫ b) := by
    rw [← morphismRestrict_ι]; infer_instance
  rw [dense_iff_inter_open]
  intro O hO hne
  obtain ⟨y, hyO, hy⟩ := hD'.inter_open_nonempty O hO hne
  have hyU : y ∈ b ⁻¹ᵁ Uc := by
    change b y ∉ J.support
    intro h
    exact hy ((GlobalTheory.ProjBlowup.mem_support_comap J b y).2 h)
  let O' : (b ⁻¹ᵁ Uc).toScheme.Opens := (b ⁻¹ᵁ Uc).ι ⁻¹ᵁ ⟨O, hO⟩
  have hopen : IsOpen (((b ⁻¹ᵁ Uc).ι ≫ b) '' (O' : Set (b ⁻¹ᵁ Uc).toScheme)) :=
    ((b ⁻¹ᵁ Uc).ι ≫ b).isOpenEmbedding.isOpenMap _ O'.isOpen
  obtain ⟨w, ⟨t, htO, rfl⟩, hwW⟩ := hWd.inter_open_nonempty _ hopen ⟨_, ⟨⟨y, hyU⟩, hyO, rfl⟩⟩
  refine ⟨(b ⁻¹ᵁ Uc).ι t, htO, ?_⟩
  change b ((b ⁻¹ᵁ Uc).ι t) ∈ W
  rwa [← Scheme.Hom.comp_apply]

end GlobalTheory.NormBlowupInt

namespace GlobalTheory.NormBlowupInt

theorem exists_normBl : ∀ (n : ℕ) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)), IsProjOver z →
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → ∀ (J : Z.IdealSheafData) (W : Z.Opens),
    Dense (W : Set Z) → (∀ x ∈ J.support, x ∉ W) → ∃ (S : Scheme.{0}) (π : S ⟶ Z)
    (BD : EffCartierData S), IsNormBl π J ∧ IsProjOver (π ≫ z) ∧ BD.idealSheaf = J.comap π ∧
    IsIso (π ∣_ W) ∧ Dense (π ⁻¹' W : Set S) := by
  intro n Z z hz hZ J W hWd hWJ
  haveI : Algebra.FiniteType ℤ (cycAway n) := finiteType_cycAway n
  haveI : Algebra.FiniteType ℤ (CommRingCat.of (cycAway n)) := ‹Algebra.FiniteType ℤ (cycAway n)›
  haveI : IsNoetherianRing (cycAway n) := Algebra.FiniteType.isNoetherianRing ℤ _
  obtain ⟨X', b, hb, hbs, hiso⟩ := GlobalTheory.ProjBlowup.exists_blowup z hz J
  haveI : LocallyOfFiniteType (b ≫ z) := by
    obtain ⟨m, i, hi, e⟩ := hbs
    have := isProper_str (cycAway n) m
    rw [← e]; infer_instance
  haveI : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (b ≫ z)
  let V : X'.Opens := b ⁻¹ᵁ W
  haveI hbW : IsIso (b ∣_ W) := hiso W fun x hx hJ => hWJ x hJ hx
  haveI hoi : IsOpenImmersion (V.ι ≫ b) := by
    rw [← morphismRestrict_ι]; infer_instance
  haveI : GlobalTheory.IsNormalScheme Z := .of_pred hZ
  haveI hN : GlobalTheory.IsNormalScheme V.toScheme := .of_isOpenImmersion (V.ι ≫ b)
  haveI : IsReduced V.toScheme := by
    exact inferInstance
  haveI hfin : IsFinite V.ι.fromNormalization :=
    isFinite_fromNormalization_int_of_isReduced (o := CommRingCat.of (cycAway n)) V.ι (b ≫ z)
      fun x _ => (LocallyOfFiniteType.stalkMap V.ι x).residueFieldMap
  let ν := V.ι.fromNormalization
  have hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme V.ι.normalization := IsNormalScheme.pred _
  have hν : IsIso (ν ∣_ V) := by
    have H := isPullback_toNormalization_of_mono (𝟙 _) V.ι V.ι (Category.id_comp _).symm
    have e := IsPullback.isoIsPullback_hom_fst _ _ (isPullback_morphismRestrict V.ι.fromNormalization V) H.flip
    rw [← e]
    infer_instance
  have hd : Dense ((ν ⁻¹ᵁ V : V.ι.normalization.Opens) : Set V.ι.normalization) := by
    refine V.ι.toNormalization.denseRange.mono ?_
    rintro _ ⟨x, rfl⟩
    change V.ι.fromNormalization (V.ι.toNormalization x) ∈ V
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.toNormalization_fromNormalization]
    exact x.2
  have hVd : Dense (V : Set X') := dense_preimage_of_blowup J b hb hiso W hWd
  obtain ⟨D, hD⟩ := EffCartierData.exists_idealSheaf_eq hb.1
  have hK : D.KeepsRegular ν := by
    refine D.keepsRegular_of_dense ν (fun y => (hS y).1) (hd.mono fun t ht => ?_)
    show ν t ∉ D.idealSheaf.support
    rw [hD, GlobalTheory.ProjBlowup.mem_support_comap]
    exact fun h => hWJ _ h ht
  refine ⟨V.ι.normalization, ν ≫ b, D.pull ν hK,
    ⟨inferInstance, X', b, ν, V, hb, rfl, hfin, hVd, hd, hν⟩, ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc]; exact isProjOver_comp_of_isFinite ν hbs
  · rw [EffCartierData.idealSheaf_pull, hD, Scheme.IdealSheafData.comap_comp]
  · rw [morphismRestrict_comp]; exact IsIso.comp_isIso' hν hbW
  · convert hd using 1
    ext t
    simp [V]

end GlobalTheory.NormBlowupInt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Arith

theorem idlAlong_monomial : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (φ : InvFun ℤ)
    (J : Z.IdealSheafData) (d : ℕ), ValOn F i φ J d →
    ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (m : ℕ) (ga δ : Fin m → LinearMap.BilinForm ℤ X)
      (M : ℕ), IsCone id φ ga → (∀ k, δ k = (M : ℤ) • ga k) → ∀ b : Fin m → ℕ, (∀ k, (b k : ℝ) = d * φ.evalZ (δ k)) →
    ∀ (T : Trait F) (W : Type) [CommRing W] [IsLocalRing W] (σ : W →+* T.V) (c : Fin m → ℕ) (e' : T.D.toPre.X ≃+ X)
      (x : Sp W ⟶ Z) (s : Fin m → W), Function.Bijective σ → jK T.V ≫ spMap σ ≫ x = T.y ≫ i →
      (∀ k, Associated (σ (s k)) (T.ϖ ^ c k)) → (∀ a b, T.β a b = ∑ k, (c k : ℤ) * δ k (e' a) (e' b)) →
      idlAlong J x = Ideal.span {∏ k, s k ^ b k} := by
  intro o _ ζ g n F Z i φ J d hV X _ _ _ m ga δ M hcone hδ b hb T W _ _ σ c e' x s hσ hcomm hs hβ
  obtain ⟨a, ha, hid⟩ := hV T (spMap σ ≫ x) hcomm
  have heq (χ : Sp W ⟶ Z) (U : Z.affineOpens) (hle : ⊤ ≤ χ ⁻¹ᵁ U.1) :
      idlAlong J χ = (J.ideal U).map (χ.appLE U.1 ⊤ hle ≫ (Scheme.ΓSpecIso (.of W)).hom).hom := by
    have hx : χ (closedPoint W) ∈ U.1 := hle trivial
    unfold idlAlong
    rw [ds_stalkId_eq_map J U _ hx, Ideal.map_map, ← CommRingCat.hom_comp, Scheme.germ_stalkClosedPointTo]
    congr 2
  have hcomp : idlAlong J (spMap σ ≫ x) = (idlAlong J x).map σ := by
    obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Z.isBasis_affineOpens
      (show x (closedPoint W) ∈ (⊤ : Z.Opens) from trivial)
    have hle : ⊤ ≤ x ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem x hx).ge
    have hle' : ⊤ ≤ (spMap σ ≫ x) ⁻¹ᵁ U := fun y _ => hle (show spMap σ y ∈ (⊤ : (Sp W).Opens) from trivial)
    have heq' : idlAlong J (spMap σ ≫ x) = (J.ideal ⟨U, hU⟩).map
        ((spMap σ ≫ x).appLE U ⊤ hle' ≫ (Scheme.ΓSpecIso (.of T.V)).hom).hom := by
      have hx' : (spMap σ ≫ x) (closedPoint T.V) ∈ U := hle' trivial
      unfold idlAlong
      rw [ds_stalkId_eq_map J ⟨U, hU⟩ _ hx', Ideal.map_map, ← CommRingCat.hom_comp, Scheme.germ_stalkClosedPointTo]
      congr 2
    rw [heq x ⟨U, hU⟩ hle, heq', Ideal.map_map]
    congr 1
    have e : (spMap σ ≫ x).appLE U ⊤ hle' = x.appLE U ⊤ hle ≫ (spMap σ).appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    rw [e, Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc, CommRingCat.hom_comp]
    rfl
  rw [hcomp] at hid
  have hlin : φ.LinearOn δ := by
    have := hcone.linearOn_smul M
    rwa [show δ = fun k => (M : ℤ) • ga k from funext hδ]
  have hev : φ.evalZ T.β = ∑ k, (c k : ℝ) * φ.evalZ (δ k) := by
    refine InvFun.LinearOn.eval_eq_sum (X := X) hlin (r := e'.symm.toIntLinearEquiv.toLinearMap)
      e'.symm.surjective (fun k => Nat.cast_nonneg _) ?_
    intro u v
    simp [hβ]
  have haN : a = ∑ k, c k * b k := by
    have : (a : ℝ) = ∑ k, (c k : ℝ) * b k := by
      rw [ha, hev, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hb k]; ring
    exact_mod_cast this
  have hassoc : Associated (∏ k, σ (s k) ^ b k) (T.ϖ ^ a) := by
    rw [haN, ← Finset.prod_pow_eq_pow_sum]
    refine Associated.prod _ _ _ fun k _ => ?_
    rw [pow_mul]
    exact (hs k).pow_pow
  have hmap : (idlAlong J x).map σ = (Ideal.span {∏ k, s k ^ b k}).map σ := by
    rw [hid, Ideal.map_span, Set.image_singleton, map_prod]
    simp only [map_pow]
    exact (Ideal.span_singleton_eq_span_singleton.2 hassoc).symm
  rw [← Ideal.comap_map_of_bijective σ hσ (I := idlAlong J x), hmap, Ideal.comap_map_of_bijective σ hσ]

end GlobalTheory.Poinc.Arith
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegEighth

theorem exists_isSharpBasis (h : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W) :
    ∃ bas : (Fin (2 * (8 * h)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)), IsSharpBasis W bas := by
  have hS : (W + W.transpose).transpose = W + W.transpose := by
    rw [Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  have h1 : (W + W.transpose) * (W + W.transpose).adjugate = 1 := by rw [Matrix.mul_adjugate, hW.2, one_smul]
  have h2 : (W + W.transpose).adjugate * (W + W.transpose) = 1 := by rw [Matrix.adjugate_mul, hW.2, one_smul]
  let e : (Fin 8 → (Fin h ⊕ Fin h → ℤ)) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)) :=
    { twistSnd (W + W.transpose).adjugate with
      invFun := twistSnd (W + W.transpose)
      left_inv := twistSnd_twistSnd _ _ h1
      right_inv := twistSnd_twistSnd _ _ h2 }
  refine ⟨(sharpReindex h).trans e, fun i j => ?_⟩
  rw [← sum_omegaStd_single h i j]
  exact sum_omegaStd_twistSnd _ _ hS h1 _ _

theorem exists_polAV_sharpOver : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∃ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))), P.g = 8 * g ∧ GlobalTheory.Poinc.SharpOver F W P (𝟙 F.X) ∧ rig.IsGen ∧ (letI := P.isAb.comm; HypS P.A P.L) := by
  intro g n _ hn hno F W hW
  have hn0 : n ≠ 0 := by omega
  let b := cycBase hn0
  let c : SiegPre g n (b.ζ : cycAway n) (𝟙 F.X ≫ F.s) := GlobalTheory.LowChart.siegPull F.univ (𝟙 F.X) (𝟙 F.X ≫ F.s) rfl
  have hc : c.Principal := GlobalTheory.LowChart.principal_siegPull F.univ _ _ rfl F.princ
  have hd : SmoothOfRelativeDimension g c.A.hom :=
    SiegSharpCover.smoothDim c (by omega) b.ζ.isUnit b.unit
  have hpow : b.ζ ^ n = 1 :=
    Units.ext ((Units.val_pow_eq_pow_val _ _).trans (Subtype.ext (Complex.isPrimitiveRoot_exp n hn0).pow_eq_one))
  obtain ⟨L₁, L₂⟩ := abelianSchemeLaws_all
  haveI : IsDedekindDomain (cycAway n) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway _
  haveI : IsLocallyNoetherian (Sp (cycAway n)) :=
    inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of _)))
  haveI := F.smooth
  haveI : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
  haveI : IsLocallyNoetherian F.X := LocallyOfFiniteType.isLocallyNoetherian F.s
  obtain ⟨bas, hb⟩ := exists_isSharpBasis g W hW
  obtain ⟨a, w, w', hw, hw', hs⟩ := EighthPowerFactor.exists_matrices hW.2
  obtain ⟨t, ⟨pr, hpr, hu, hL, -, -⟩, hp⟩ := GlobalTheory.exists_isSharp_and_prim L₁ L₂ Moduli.cube_of_isLB g (8 * g) W _ a w w'
    bas hW hb hw hw' hs n (cycAway n) b F.X (𝟙 F.X ≫ F.s) c hpow hno hc hd
  obtain ⟨r, hr⟩ := t.rigid
  exact ⟨t.pol, r, rfl, ⟨c, GlobalTheory.LowChart.siegPB_siegPull F.univ _ _ rfl, pr, hpr, hu, hL⟩, hr,
    t.act w, t.act w', t.hom w, t.hom w', hp.1, hp.2.2, hp.2.1⟩

end GlobalTheory.SiegEighth
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.NormBlPrincipal

theorem idlAlong_comap_principal : ∀ {S Z : Scheme.{0}} (π : S ⟶ Z) (J : Z.IdealSheafData), IsNormBl π J →
    ∀ (R : Type) [CommRing R] [IsLocalRing R]
    (ξ : Sp R ⟶ S), ∃ g₀ : R, idlAlong (J.comap π) ξ = Ideal.span {g₀} := by
  intro S Z π J h R _ _ ξ
  obtain ⟨-, S₀, π₀, ν, -, hbl, hc, -⟩ := h
  obtain ⟨U, f, hx, -, hU⟩ := hbl.1 ((ξ ≫ ν) (closedPoint R))
  have hle : ⊤ ≤ (ξ ≫ ν) ⁻¹ᵁ U.1 := (Scheme.preimage_eq_top_of_closedPoint_mem (ξ ≫ ν) hx).ge
  refine ⟨((ξ ≫ ν).appLE U.1 ⊤ hle ≫ (Scheme.ΓSpecIso (.of R)).hom).hom f, ?_⟩
  have e : idlAlong (J.comap π) ξ = idlAlong (J.comap π₀) (ξ ≫ ν) := by
    rw [GlobalTheory.PullAlong.idlAlong_comap_eq, GlobalTheory.PullAlong.idlAlong_comap_eq, ← hc, Category.assoc]
  have hmap : idlAlong (J.comap π₀) (ξ ≫ ν) =
      ((J.comap π₀).ideal U).map
        ((ξ ≫ ν).appLE U.1 ⊤ hle ≫ (Scheme.ΓSpecIso (.of R)).hom).hom := by
    unfold idlAlong
    rw [ds_stalkId_eq_map (J.comap π₀) U _ hx, Ideal.map_map,
      ← CommRingCat.hom_comp, Scheme.germ_stalkClosedPointTo]
    congr 2
  rw [e, hmap, hU, Ideal.map_span, Set.image_singleton]

end GlobalTheory.NormBlPrincipal
end
end
