module

public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteTorusExtensionOfModel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle069
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGeneratorNeZero
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle074
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
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle049

@[expose] public section

section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS GlobalTheory.FieldModel

namespace GlobalTheory

theorem exists_finite_isAbelianScheme_range {K : Type} [Field K] (B : Over (Sp K)) [GrpObj B]
    (hB : IsAbelianScheme B) :
    ∃ s : Set K, s.Finite ∧ ∀ (k₁ : Type) [Field k₁] (β : k₁ →+* K), s ⊆ Set.range β →
      ∃ (B₁ : Over (Sp k₁)) (_ : GrpObj B₁) (φ : B.left ⟶ B₁.left),
        IsAbelianScheme B₁ ∧ IsGrpPullback B B₁ (spMap β) φ := by
  have := hB.proper
  obtain ⟨s₀, hs₀⟩ := hasModel B
  let k₀ := Subfield.closure (s₀ : Set K)
  obtain ⟨B₀, φ₀, H₀⟩ := hs₀ k₀ k₀.subtype fun x hx => ⟨⟨x, Subfield.subset_closure hx⟩, rfl⟩
  have lB : LocallyOfFiniteType B.hom := inferInstance
  have pBB : IsProper (B ⊗ B).hom := inferInstanceAs (IsProper (pullback.fst B.hom B.hom ≫ B.hom))
  obtain ⟨sm, hm⟩ := GlobalTheory.T.hom_descends_to_subfield_containing_finset_alt k₀ K _ _ _ _ _ _ _ (isPullback_sq H₀) H₀ inferInstance inferInstance lB μ[B]
  obtain ⟨si, hi⟩ := GlobalTheory.T.hom_descends_to_subfield_containing_finset_alt k₀ K _ _ _ _ _ _ _ H₀ H₀ inferInstance inferInstance lB ι[B]
  obtain ⟨se, he⟩ := GlobalTheory.T.hom_descends_to_subfield_containing_finset_alt k₀ K _ _ _ _ _ _ _ (isPullback_unit _) H₀
    (inferInstanceAs (QuasiCompact (𝟙 (Sp K)))) (inferInstanceAs (QuasiSeparated (𝟙 (Sp K)))) lB η[B]
  refine ⟨s₀ ∪ (sm ∪ (si ∪ se)), by simp, fun k₁ _ β hs => ?_⟩
  simp only [Set.union_subset_iff] at hs
  obtain ⟨b₀, bm, bi, be⟩ := hs
  obtain ⟨ρ, hρ⟩ := exists_factor β (s₀ : Set K) b₀
  obtain ⟨φ₁, eφ, H₁⟩ := exists_baseChange (spMap_comp hρ) H₀
  have P₁ : IsPullback (pullback.fst B₀.hom (spMap ρ)) ((Over.pullback (spMap ρ)).obj B₀).hom B₀.hom (spMap ρ) :=
    .of_hasPullback _ _
  obtain ⟨m₁, hm₁⟩ := hm k₁ ρ β hρ bm _ _ (sq H₁.w) _ φ₁ _ (isPullback_sq P₁) P₁ (sq_comp eφ _ _ _) eφ
    (isPullback_sq H₁).w H₁.w
  obtain ⟨i₁, hi₁⟩ := hi k₁ ρ β hρ bi _ _ φ₁ _ φ₁ _ P₁ P₁ eφ eφ H₁.w H₁.w
  obtain ⟨e₁, he₁⟩ := he k₁ ρ β hρ be (𝟙_ _) _ (spMap β) _ φ₁ _ (isPullback_unit (spMap ρ)) P₁ (spMap_comp hρ) eφ
    (isPullback_unit (spMap β)).w H₁.w
  obtain ⟨gB, ab, gpB⟩ := GlobalTheory.T.group_structure_descends_along_pullback k₁ K β B _ φ₁ hB H₁ m₁ i₁ e₁ _ (sq_fst _) (sq_snd _) hm₁ hi₁ he₁
  exact ⟨_, gB, φ₁, ab, gpB⟩

theorem exists_finite_isAbelianScheme_descends : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (B : Over (Sp Ω)) [GrpObj B], IsAbelianScheme B → ∃ (L : IntermediateField K Ω) (_ : FiniteDimensional K L) (B₁ : Over (Sp L)) (_ : GrpObj B₁) (e : (Over.pullback (spMap (algebraMap L Ω))).obj B₁ ≅ B), IsAbelianScheme B₁ ∧ IsMonHom e.hom := by
  intro K Ω _ _ _ _ B _ hB
  obtain ⟨s, hs, h⟩ := exists_finite_isAbelianScheme_range B hB
  have := hs.to_subtype
  have : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  obtain ⟨B₁, g, φ, ab, gp⟩ := h _ (algebraMap (IntermediateField.adjoin K s) Ω)
    fun x hx => ⟨⟨x, IntermediateField.subset_adjoin K s hx⟩, rfl⟩
  obtain ⟨e, he, -⟩ := grpPullback_iso (isGrpPullback_pullback B₁ _) gp
  exact ⟨IntermediateField.adjoin K s, IntermediateField.finiteDimensional_adjoin
    fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral, B₁, g, e, ab, he⟩

end GlobalTheory
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UnitTheta

theorem exists_pull_one {X Y : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (θ : LB.Sec L) :
    ∃ th : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => f) (fun _ => 1)),
      ∀ (Z : Scheme.{0}) (ρ : Z ⟶ Y) (z : Z) (J), Good L z J →
        sval th ρ z J = gs (ρ ≫ f) z _ (θ.f (J (ρ ≫ f))) := by
  have le : ∀ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => f) j ≤ f ⁻¹ᵁ L.U (j 0) :=
    fun j y hy => Set.mem_iInter.1 hy 0
  let u : ∀ j : Fin 1 → L.ι, Γ(Y, LB.wchart L (fun _ : Fin 1 => f) j) := fun j =>
    (Y.presheaf.map (homOfLE (le j)).op).hom ((f.app _).hom (θ.f (j 0)))
  have hu : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ Y) (z : Z) j, ρ z ∈ LB.wchart L (fun _ : Fin 1 => f) j →
      gs ρ z _ (u j) = gs (ρ ≫ f) z _ (θ.f (j 0)) := fun Z ρ z j h =>
    (gs_res ρ z _ h _).trans (gs_pull ρ f z _ (le j h) _)
  refine ⟨⟨u, fun j j' => fn_ext fun y hy => ?_⟩, fun Z ρ z J hJ => hu Z ρ z _ (hJ.mem (fun _ : Fin 1 => f) ρ)⟩
  refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
    ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val
      (gm_linComb L (fun _ : Fin 1 => f) (fun _ => 1) (𝟙 Y) y j j' hy.1 hy.2))) (gs_res (𝟙 Y) y _ hy _))).symm)
  rw [Fin.prod_univ_one, zpow_one]
  exact (hu _ (𝟙 Y) y j hy.1).trans ((gs_compat θ (𝟙 Y ≫ f) y (le j hy.1) (le j' hy.2)).trans
    (congrArg (_ * ·) (hu _ (𝟙 Y) y j' hy.2).symm))

theorem exists_good_point_of_sec : PolBaseChangeSt → GoodPtSt → ∀ (S : Scheme.{0}) (P : PolAV S) (θ : LB.Sec P.L) (κ : Type) [Field κ] [IsAlgClosed κ] (r : Sp κ ⟶ S) (n : ℕ), 2 ≤ n → (n : κ) ≠ 0 → (∃ z ∈ nonzeroLocus θ, P.A.hom z ∈ Set.range r) → ∀ b : Over.mk r ⟶ P.A, ∃ x : Over.mk r ⟶ P.A, x ^ n = 1 ∧ ⊤ ≤ (b * x).left ⁻¹ᵁ nonzeroLocus θ := by
  intro hB hG S P θ κ _ _ r n hn hκ ⟨z, hz, p, hp⟩ b
  obtain ⟨th, hth⟩ := exists_pull_one P.L (snd (Over.mk r) P.A).left θ
  have hne : SecM.ofSec P.A (a := 1) (T := Over.mk r) th ≠ 0 := fun e => by
    obtain ⟨y, -, hy⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback r P.A.hom) p z hp
    let y' : (Over.mk r ⊗ P.A).left := y
    obtain ⟨J, hJ, -⟩ := exists_good P.L P.isLB y' (K := Empty) Empty.elim Empty.elim (·.elim) (·.elim)
    have h₁ : (𝟙 _ ≫ (snd (Over.mk r) P.A).left) y' ∈ nonzeroLocus θ := by
      rw [Category.id_comp]; exact hy ▸ hz
    have h₂ := (AmpleSpan.mem_nonzeroLocus_iff_gs θ _ y' (hJ _)).1 h₁
    rw [← hth _ _ y' J hJ] at h₂
    have h₃ : th.f (fun _ => J (𝟙 _ ≫ (snd (Over.mk r) P.A).left)) = 0 :=
      congrArg (fun s : SecM P.A P.L 1 (Over.mk r) => s.1 _) e
    rw [sval, h₃] at h₂
    exact not_isUnit_zero ((congrArg IsUnit (GlobalTheory.UT.ExactTerm.gs_zero' _ _ _ (hJ.mem (fun _ : Fin 1 => (snd (Over.mk r) P.A).left) (𝟙 _)))).mp h₂)
  obtain ⟨x, hx, hu⟩ := GlobalTheory.UT.ExactTerm.exists_good_point hG hB P r hn hκ th hne b
  refine ⟨x, hx, fun q _ => ?_⟩
  obtain ⟨J, hJ, -⟩ := exists_good P.L P.isLB q (K := Empty) Empty.elim Empty.elim (·.elim) (·.elim)
  have h₁ : IsUnit (sval th (ptSecT P.A (b * x)).left q J) := hu q J hJ
  have e : (ptSecT P.A (b * x)).left ≫ (snd (Over.mk r) P.A).left = (b * x).left := by
    rw [← Over.comp_left, ptSecT, lift_snd]
  rw [hth _ _ q J hJ, e] at h₁
  exact (AmpleSpan.mem_nonzeroLocus_iff_gs θ _ q (hJ _)).2 h₁

end GlobalTheory.UnitTheta
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

theorem _root_.GlobalTheory.T.exists_isTorsFrame_of_symLift' : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))), rig.IsGen → ∀ (n : ℕ), Odd n → ∀ (T : Over S) (y x : T ⟶ P.A), y ^ (n ^ 2) = 1 → y ^ n = x → ∀ θ : ThetaGrp P.A P.L (n ^ 2 : ℕ) T, SymLift P.A P.L (n ^ 2 : ℕ) (n ^ 2) y θ → ∃ τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => 1)), IsTorsFrame P rig n x τ := by
  first | exact @GlobalTheory.exists_isTorsFrame_of_symLift | exact GlobalTheory.exists_isTorsFrame_of_symLift | (intros; apply GlobalTheory.exists_isTorsFrame_of_symLift <;> assumption)
end
