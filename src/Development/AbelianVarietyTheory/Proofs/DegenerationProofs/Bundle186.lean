module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle005
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle057
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle078
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBundleOfDividingMaximalMinor
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle185
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasGradedChartsNearGenericPointClosure
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle184
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnAbelianLocusUniformisation
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle058
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGlobalGenerators
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle068
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle056
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle046
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle047
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle059
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle080
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle089
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle054
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle183
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle079
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelPointsEqOfSameDegenerationData
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.semiAbelian_reduction_along_isogeny_strict_henselian : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] (G' : Over (Sp R)) [GrpObj G'] (g m : ℕ), IsAbelianScheme A → GlobalTheory.AbLaw.IsProjBy A.hom → IsSemiAbelian G' → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap R K))).obj G').hom → ∀ (i : A ⟶ (Over.pullback (spMap (algebraMap R K))).obj G') (r : (Over.pullback (spMap (algebraMap R K))).obj G' ⟶ A), IsMonHom i → IsMonHom r → 1 ≤ m → r ≫ i = 𝟙 _ ^ m → ∃ (G : Over (Sp R)) (_ : GrpObj G) (e : (Over.pullback (spMap (algebraMap R K))).obj G ≅ A), SmConn G ∧ IsMonHom e.hom ∧ Nonempty (TorusExtension (spFibre G)) := by
  first | exact @GlobalTheory.IsogRed.semiAbelian_reduction_of_isogeny | exact GlobalTheory.IsogRed.semiAbelian_reduction_of_isogeny | (intros; apply GlobalTheory.IsogRed.semiAbelian_reduction_of_isogeny <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MorAlgTower

theorem step_comm {C : Type*} [Category C] {Y Y' B S S' T : C} {p : B ⟶ T} {t : S ⟶ T}
    {t' : S' ⟶ T} [HasPullback p t] [HasPullback p t'] {τ : S ⟶ S'} {β : Y ⟶ Y'} {b : Y ⟶ B}
    {b' : Y' ⟶ B} {y : Y ⟶ S} {y' : Y' ⟶ S'} (hb : IsPullback b y p t)
    (hb' : IsPullback b' y' p t') (h₁ : β ≫ b' = b) (h₂ : β ≫ y' = y ≫ τ)
    (e₁ : p ≫ 𝟙 T = 𝟙 B ≫ p) (e₂ : t ≫ 𝟙 T = τ ≫ t') {Z : C} {c : Y ⟶ Z} {c' : Y' ⟶ Z}
    (hc : β ≫ c' = c) :
    pullback.map p t p t' (𝟙 _) τ (𝟙 _) e₁ e₂ ≫ hb'.isoPullback.inv ≫ c'
      = hb.isoPullback.inv ≫ c := by
  have key : β ≫ hb'.isoPullback.hom
      = hb.isoPullback.hom ≫ pullback.map p t p t' (𝟙 _) τ (𝟙 _) e₁ e₂ := by
    apply pullback.hom_ext
    · simp [h₁, pullback.map, pullback.lift_fst]
    · simp [h₂, pullback.map, pullback.lift_snd]
  rw [Iso.eq_inv_comp, ← Category.assoc, ← key, Category.assoc, Iso.hom_inv_id_assoc, hc]

theorem base_comm {C : Type*} [Category C] {Y B S T Z : C} {p : B ⟶ T} {t : S ⟶ T}
    [HasPullback p t] {b : Y ⟶ B} {y : Y ⟶ S} (hb : IsPullback b y p t) {c : Y ⟶ Z} {z : Z ⟶ T}
    (hc : c ≫ z = y ≫ t) : (hb.isoPullback.inv ≫ c) ≫ z = pullback.fst p t ≫ p := by
  rw [← hb.isoPullback_inv_fst, Category.assoc, Category.assoc, hc, hb.w]

theorem final_comm {C : Type*} [Category C] {Y B S T Z : C} {p : B ⟶ T} {t : S ⟶ T}
    [HasPullback p t] {b : Y ⟶ B} {y : Y ⟶ S} (hb : IsPullback b y p t) {c : Y ⟶ Z} {g : B ⟶ Z}
    (hg : pullback.fst p t ≫ g = hb.isoPullback.inv ≫ c) : b ≫ g = c := by
  have h := hb.isoPullback_hom_fst
  calc b ≫ g = (hb.isoPullback.hom ≫ pullback.fst p t) ≫ g := by rw [h]
    _ = c := by rw [Category.assoc, hg, Iso.hom_inv_id_assoc]

theorem exists_hom_of_tower : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → IsAdicComplete I R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (B : Over (Spec (CommRingCat.of R))) (b : ∀ e, (Y e).left ⟶ B.left), IsProjBy B.hom → Flat B.hom → (∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ Z : Over (Spec (CommRingCat.of R)), IsProjBy Z.hom → ∀ c : ∀ e, (Y e).left ⟶ Z.left, (∀ e, c e ≫ Z.hom = (Y e).hom ≫ thick R I e) → (∀ e, β e ≫ c (e + 1) = c e) → ∃ g : B ⟶ Z, ∀ e, b e ≫ g.left = c e := by
  intro R _ _ _ I hI hc Y β hβ B b hB hfl hb hβb Z hZ c hcZ hβc
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_hom_algebraising_thickenings_projective R I hI hc B Z hB hZ hfl (fun e => (hb e).isoPullback.inv ≫ c e)
    (fun e => base_comm (hb e) (hcZ e))
    (fun e => step_comm (hb e) (hb (e + 1)) (hβb e) (hβ e).w _ _ (hβc e))
  exact ⟨g, fun e => final_comm (hb e) (hg e)⟩

end GlobalTheory.MorAlgTower
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

theorem _root_.GlobalTheory.T.exists_uniformisation_complete_local_normal_prime : Laws → Laws2 → Laws3 → Laws4 → Laws5 → Ega → USt → PelSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → IsPrincipalIdealRing (R ⧸ I) → ∀ (t : SAB H (Sp R)), PolAt t (jK R) → SplitOver t.G I → ThetaNZ t.G t.PP.L → ∃ P : PELUnif I t, P.TorsionIso := by
  first | exact @GlobalTheory.LN.UnifPrime.exists_pelUnif | exact GlobalTheory.LN.UnifPrime.exists_pelUnif | (intros; apply GlobalTheory.LN.UnifPrime.exists_pelUnif <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

theorem _root_.GlobalTheory.T.psiUnitOn_abelian_locus_uniformisation : Laws → Laws2 → Laws3 → Laws4 → Laws5 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif I D A G, IsOpen (abLocus G) → ∀ y, PsiUnitOn D.toPre y (abLocus G) := by
  first | exact @GlobalTheory.PsiAbelian.psiUnitOn_abLocus | exact GlobalTheory.PsiAbelian.psiUnitOn_abLocus | (intros; apply GlobalTheory.PsiAbelian.psiUnitOn_abLocus <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH.MinorModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

variable (S : ThetaSys o Ω)

end GlobalTheory.ZH.MinorModel

namespace GlobalTheory.ZH

open MinorModel

open CategoryTheory Limits AlgebraicGeometry in
open Classical in
private theorem exists_open_ringOn_contains_of_fg_of_finite {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
    (M : _root_.GlobalTheory.ZH.RatModel o Ω) (A : Subalgebra o Ω) (hA : A.FG) (F : Set Ω)
    (hF : F.Finite) :
    ∃ U : M.Z.Opens, (U : Set M.Z).Nonempty ∧ A ≤ M.ringOn U ∧ ∀ x ∈ F, x ∈ M.ringOn U := by
  obtain ⟨s, rfl⟩ := hA
  have hT : ((s : Set Ω) ∪ F).Finite := s.finite_toSet.union hF
  let U : M.Z.Opens := ⟨⋂ x ∈ (s : Set Ω) ∪ F, {z | x ∈ M.O z},
    hT.isOpen_biInter fun x _ => M.isOpen_setOf_mem_O x⟩
  have hU : ∀ x ∈ (s : Set Ω) ∪ F, x ∈ M.ringOn (U : Set M.Z) := fun x hx =>
    _root_.GlobalTheory.ZH.RatModel.mem_ringOn.2 fun z hz =>
      Set.mem_iInter₂.1 hz x hx
  refine ⟨U, ⟨genericPoint M.Z, ?_⟩, ?_, fun x hx => hU x (Or.inr hx)⟩
  · show genericPoint M.Z ∈ ⋂ x ∈ (s : Set Ω) ∪ F, {z | x ∈ M.O z}
    simp [M.O_genericPoint]
  · exact Algebra.adjoin_le fun x hx => hU x (Or.inl hx)

open CategoryTheory Limits AlgebraicGeometry in
open Classical in
private theorem exists_open_over0_ringOn_of_fg {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
    (S : _root_.GlobalTheory.ZH.ThetaSys o Ω) (M : _root_.GlobalTheory.ZH.RatModel o Ω) (R' : Subalgebra o Ω)
    (hfg : R'.FG) (hR : S.R ≤ R') (hn : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z) (hp : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver M.s) (hd : M.HasDiv S.th) :
    ∃ U : M.Z.Opens, S.Over₀ M U ∧ R' ≤ M.ringOn U := by
  obtain ⟨U, hUne, hAU, hFU⟩ := exists_open_ringOn_contains_of_fg_of_finite M R' hfg
    (Set.range (fun x => (S.th x)⁻¹) ∪ Set.range (fun q : Σ T : AddSubgroup S.Gam,
      (T →+ ZMod S.N) × (S.J × (T → ZMod ((S.r * S.N) ^ 2))) => (S.FF q.1 q.2.1 q.2.2)⁻¹))
    ((Set.finite_range _).union (Set.finite_range _))
  exact ⟨U, ⟨hn, hp, hd, hUne, hR.trans hAU, fun x _ => hFU _ (Or.inl ⟨x, rfl⟩),
    fun T c k _ _ => hFU _ (Or.inr ⟨⟨T, c, k⟩, rfl⟩)⟩, hAU⟩

open CategoryTheory Limits AlgebraicGeometry in
open Classical in
private theorem module_finite_of_subfield_le {Ω : Type} [Field Ω] {K K' : Subfield Ω} (h : K ≤ K')
    [Module.Finite K Ω] : Module.Finite K' Ω := by
  letI : Algebra K K' := (Subfield.inclusion h).toAlgebra
  haveI : IsScalarTower K K' Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
  exact Module.Finite.of_restrictScalars_finite K K' Ω

open CategoryTheory Limits AlgebraicGeometry in
open Classical in
private theorem isProper_of_isProjOver_degeneration {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
    (M : _root_.GlobalTheory.ZH.RatModel o Ω) (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver M.s) : IsProper M.s := by
  obtain ⟨N, i, hi, e⟩ := h
  haveI := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str o N
  rw [← e]
  infer_instance


open CategoryTheory Limits AlgebraicGeometry in
open Classical in
theorem _root_.GlobalTheory.ZH.exists_minor_model : ∀ (o Ω : Type) [CommRing o] [Field Ω]
    [Algebra o Ω] [_root_.GlobalTheory.ZH.ArithBase o Ω] (S : _root_.GlobalTheory.ZH.ThetaSys o Ω), S.HasTests →
    Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = S.th j / S.th i})) Ω →
    ∃ (n a : ℕ) (GG : Fin n → S.J → Ω) (X Z : _root_.GlobalTheory.ZH.RatModel o Ω) (U₀ : Z.Z.Opens)
      (EE : Z.Lat S.J) (f : Z.Z ⟶ X.Z) (Xab : X.Z.Opens), X.IsNm S.th ∧ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver X.s ∧
      Z.IsNm (fun q : S.Gam × (S.J → Fin n) => S.th q.1 * Matrix.det (Matrix.of fun i j => GG (q.2 i) j)) ∧
      S.Over₀ Z U₀ ∧ S.IsEE Z U₀ EE ∧ X.IsHom Z (AlgHom.id o Ω) f ∧
      (Xab : Set X.Z) = {x | S.TT X x = ⊥} ∧ IsIso (f ∣_ Xab) ∧
      (∀ z : Z.Z, ∀ x₀ ∈ S.supI Z z, ∀ w : S.J → Ω,
        w ∈ Submodule.span (Z.O z) (Set.range fun k j => GG k j / S.th x₀ ^ a) ↔
          ∀ v ∈ EE.E z, w ⬝ᵥ v ∈ Z.O z) ∧
      ∀ z : Z.Z, ∀ x₀ ∈ S.supI Z z,
        (∀ k : S.J → Fin n, Matrix.det (Matrix.of fun i j => GG (k i) j) / S.th x₀ ^ (a * Fintype.card S.J) ∈ Z.O z) ∧
        (S.TT Z z = ⊥ ↔ ∃ k : S.J → Fin n, Matrix.det (Matrix.of fun i j => GG (k i) j) ≠ 0 ∧
          S.th x₀ ^ (a * Fintype.card S.J) / Matrix.det (Matrix.of fun i j => GG (k i) j) ∈ Z.O z) := by
  intro o Ω _ _ _ _ S hT hfin
  haveI : Algebra.FiniteType ℤ o := _root_.GlobalTheory.ZH.ArithBase.ft (o := o) Ω
  haveI : CharZero Ω := _root_.GlobalTheory.ZH.ArithBase.char o (Ω := Ω)
  haveI : IsDedekindDomain o := _root_.GlobalTheory.ZH.ArithBase.ded (o := o) Ω
  have hwt := _root_.GlobalTheory.ZH.test_weights o Ω S
  obtain ⟨M₁, U₁, hAdm₁, hAff₁, -⟩ := _root_.GlobalTheory.ZH.exists_admissible_affine_model_dividing_tuple o Ω S Unit (fun _ => 1) ⟨(), one_ne_zero⟩
    (by
      rw [show {x | ∃ i j : S.Gam × Unit, x = S.th j.1 * (fun _ => (1:Ω)) j.2 / (S.th i.1 * (fun _ => (1:Ω)) i.2)}
          = {x | ∃ i j, x = S.th j / S.th i} by ext x; simp]
      exact hfin)
  have hO₁ := hAdm₁.1
  have hreg₁ := _root_.GlobalTheory.ZH.classical_points_and_local_regularity o Ω M₁ U₁ hO₁.normal
  have htst₁ := _root_.GlobalTheory.ZH.exists_at_test_of_cen o Ω S M₁ U₁ hT hO₁
  have hsup₁ := _root_.GlobalTheory.ZH.ThetaSys.mem_supI_iff_and_HH_eq_ker o Ω S M₁ U₁ hO₁
  have hiso₁ := _root_.GlobalTheory.ZH.isoFree_TT_and_supI_specializes o Ω S M₁ U₁ hO₁ hreg₁ htst₁ hsup₁
  obtain ⟨EE₁, hEE₁, hspan₁⟩ := _root_.GlobalTheory.ZH.exists_isEE_of_adm o Ω S M₁ U₁ hT hAdm₁
  have hFF₁ := _root_.GlobalTheory.ZH.FF_TT_ne_zero o Ω S M₁ U₁ hO₁ hreg₁ htst₁ hsup₁ hiso₁ hwt
  have hdot₁ := _root_.GlobalTheory.ZH.DualSection.ff_div_th_mul_dotProduct_mem o Ω S M₁ U₁ EE₁ hAdm₁ hreg₁ htst₁ hsup₁ hiso₁ hwt
  have hnorm := _root_.GlobalTheory.thetaSys_norm_FF_le_exp o Ω S hwt
  have hnd₁ := _root_.GlobalTheory.norm_val_FF_eq_of_div o Ω S M₁ U₁ hO₁ hsup₁ hnorm htst₁
  have hdot₁' := hdot₁ hnorm hnd₁ hFF₁ hspan₁
  obtain ⟨n, a, GG₀, hGG₀⟩ := _root_.GlobalTheory.ZH.GlobalGen.exists_global_generators o Ω S M₁ U₁ EE₁ hAdm₁ hreg₁.2 hiso₁ hFF₁ hspan₁ hdot₁'
  obtain ⟨R', hR, GG, hfg, hGGeq, htests⟩ := _root_.GlobalTheory.ZH.exists_generators_at_all_tests o Ω S M₁ U₁ EE₁ n a GG₀ hO₁ hAff₁ hsup₁ hEE₁ hGG₀
  have hinj : Function.Injective (algebraMap o Ω) := (inferInstance : _root_.GlobalTheory.ZH.ArithBase o Ω).4
  obtain ⟨X, hXn, hXp⟩ := _root_.GlobalTheory.ZH.exists_isNm_isProjOver o Ω hinj S.Gam S.th S.th_ne hfin
  have hXnorm := hXn.isNormalScheme
  obtain ⟨UX, hOX, hRX⟩ := exists_open_over0_ringOn_of_fg S X R' hfg hR hXnorm hXp hXn.1
  have hregX := _root_.GlobalTheory.ZH.classical_points_and_local_regularity o Ω X UX hXnorm
  have htstX := _root_.GlobalTheory.ZH.exists_at_test_of_cen o Ω S X UX hT hOX
  have hsupX := _root_.GlobalTheory.ZH.ThetaSys.mem_supI_iff_and_HH_eq_ker o Ω S X UX hOX
  have hisoX := _root_.GlobalTheory.ZH.isoFree_TT_and_supI_specializes o Ω S X UX hOX hregX htstX hsupX
  have hminX := _root_.GlobalTheory.ZH.minors_regular_and_unit_iff o Ω S X UX R' hR n a GG hOX hRX hregX htstX hsupX hisoX hwt htests
  obtain ⟨ξ, hξ⟩ := hOX.ne
  obtain ⟨x₀, hx₀⟩ := hXn.1 ξ
  obtain ⟨k₀, hk₀, -⟩ := ((hminX ξ x₀ hx₀).2).1 (hisoX.2.2.1 ξ hξ)
  obtain ⟨Z, hZn, hZp⟩ := _root_.GlobalTheory.ZH.exists_isNm_isProjOver o Ω hinj (S.Gam × (S.J → Fin n))
    (fun q => S.th q.1 * Matrix.det (Matrix.of fun i j => (GG (q.2 i) j : Ω)))
    ⟨(x₀, k₀), mul_ne_zero hx₀.1 hk₀⟩
    (by
      haveI := hfin
      refine module_finite_of_subfield_le (K := Subfield.closure (Set.range (algebraMap o Ω) ∪
        {x | ∃ i j, x = S.th j / S.th i})) ?_
      refine Subfield.closure_le.2 (Set.union_subset (fun x hx => Subfield.subset_closure (Or.inl hx)) ?_)
      rintro x ⟨i, j, rfl⟩
      exact Subfield.subset_closure (Or.inr ⟨(i, k₀), (j, k₀), (mul_div_mul_right _ _ hk₀).symm⟩))
  have hZdiv := (_root_.GlobalTheory.ZH.isNm_normal_and_div_prod o Ω Z S.Gam S.th).2.1 (S.J → Fin n)
    (fun k : S.J → Fin n => Matrix.det (Matrix.of fun i j => (GG (k i) j : Ω)))
  have hZth : Z.HasDiv S.th := fun z => by
    obtain ⟨⟨i, k⟩, h⟩ := hZn.1 z
    exact ⟨i, ((hZdiv i k z).1 h).1⟩
  have hZd : Z.HasDiv (fun k : S.J → Fin n => Matrix.det (Matrix.of fun i j => (GG (k i) j : Ω))) := fun z => by
    obtain ⟨⟨i, k⟩, h⟩ := hZn.1 z
    exact ⟨k, ((hZdiv i k z).1 h).2⟩
  have hZnorm := hZn.isNormalScheme
  obtain ⟨UZ, hOZ, hRZ⟩ := exists_open_over0_ringOn_of_fg S Z R' hfg hR hZnorm hZp hZth
  have hregZ := _root_.GlobalTheory.ZH.classical_points_and_local_regularity o Ω Z UZ hZnorm
  have htstZ := _root_.GlobalTheory.ZH.exists_at_test_of_cen o Ω S Z UZ hT hOZ
  have hsupZ := _root_.GlobalTheory.ZH.ThetaSys.mem_supI_iff_and_HH_eq_ker o Ω S Z UZ hOZ
  have hisoZ := _root_.GlobalTheory.ZH.isoFree_TT_and_supI_specializes o Ω S Z UZ hOZ hregZ htstZ hsupZ
  obtain ⟨EE, hEE, hspanZ⟩ := _root_.GlobalTheory.ZH.exists_isEE_of_hasDiv_minors o Ω S Z UZ R' hR n a GG hOZ hRZ hregZ htstZ hsupZ htests hZd
  have hminZ := _root_.GlobalTheory.ZH.minors_regular_and_unit_iff o Ω S Z UZ R' hR n a GG hOZ hRZ hregZ htstZ hsupZ hisoZ hwt htests
  obtain ⟨f, hf⟩ := hXn.exists_isHom (φ := AlgHom.id o Ω)
    (show Z.HasDiv (fun j => (AlgHom.id o Ω) (S.th j)) from hZth)
    (fun z => _root_.GlobalTheory.ZH.RatModel.isIntegrallyClosed_O hZnorm z)
  let Xab : X.Z.Opens := ⟨{x | S.TT X x = ⊥}, by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨y₀, hy₀⟩ := hXn.1 x
    obtain ⟨k, hk, hmem⟩ := ((hminX x y₀ hy₀).2).1 hx
    refine ⟨{y | X.Div S.th y₀ y} ∩ {y | S.th y₀ ^ (a * Fintype.card S.J) /
      Matrix.det (Matrix.of fun i j => (GG (k i) j : Ω)) ∈ X.O y}, ?_,
      (X.isOpen_setOf_div S.th y₀).inter
        (X.isOpen_setOf_mem_O _), hy₀, hmem⟩
    rintro y ⟨hy1, hy2⟩
    exact ((hminX y y₀ hy1).2).2 ⟨k, hk, hy2⟩⟩
  have hiso := _root_.GlobalTheory.ZH.isIso_morphismRestrict_of_isNm_prod o Ω X Z S.Gam (S.J → Fin n) S.th
    (fun k : S.J → Fin n => Matrix.det (Matrix.of fun i j => (GG (k i) j : Ω))) f hXn hZn (isProper_of_isProjOver_degeneration Z hZp) hf Xab (by
      intro z hz
      obtain ⟨y₀, hy₀⟩ := hXn.1 z
      obtain ⟨k, hk, hmem⟩ := ((hminX z y₀ hy₀).2).1 hz
      refine ⟨k, hk, fun j => ?_⟩
      have h1 := (hminX z y₀ hy₀).1 j
      have ht : S.th y₀ ^ (a * Fintype.card S.J) ≠ 0 := pow_ne_zero _ hy₀.1
      have h2 := (X.O z).mul_mem h1 hmem
      beta_reduce at h1 hmem h2 ⊢
      rwa [div_mul_div_cancel₀ ht] at h2)
  exact ⟨n, a, fun k j => (GG k j : Ω), X, Z, UZ, EE, f, Xab, hXn, hXp, hZn, hOZ, hEE, hf, rfl, hiso, hspanZ, hminZ⟩

end GlobalTheory.ZH
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_semiAbelian_groupScheme_cubical_bundle_closure : Laws → Laws2 → ThmUSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : Clos ρ M U₀ EE) (ex : Q.Ext), S.Big → ex.core.HasTests → ex.core.Indep → ex.core.HasCharts → ex.core.TorsSec (S.r * S.N) → (∃ T : ex.core.Theta, LBIso T.L.L (ρ.P.L.pull (pullback.fst ρ.P.A.hom Q.u₀))) → ∃ Z : ZHPre ρ M U₀, (∃ e : Z.G.left ≅ Q.G.toScheme, e.hom ≫ Q.G.ι ≫ Q.P.hom = Z.G.hom ∧ Z.u₀ = Q.u₀ ∧ HEq (Z.φ ≫ e.hom) ex.a) ∧ Z.LocTheta ∧ Nonempty ex.core.Law := by
  first | exact @GlobalTheory.ClosureGroup.exists_pre | exact GlobalTheory.ClosureGroup.exists_pre | (intros; apply GlobalTheory.ClosureGroup.exists_pre <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.hasGradedCharts_near_generic_point_closure : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (ex : Q.Ext), S.Big → ρ.HasGeo → ex.core.Fib → ex.core.HasCharts := by
  first | exact @GlobalTheory.ZH.GradedCharts.hasCharts | exact GlobalTheory.ZH.GradedCharts.hasCharts | (intros; apply GlobalTheory.ZH.GradedCharts.hasCharts <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.specialFibre_image_test_independent : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → ∀ x : Sp (kb p) ⟶ Q.P.left, x ≫ Q.P.hom = rPt p ≫ y → ((∃ c' : Sp (kb p) ⟶ t.u.G.left, c' ≫ t.u.G.hom = rPt p ≫ spMap t.u.j ∧ c' ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = x) ↔ (⊤ ≤ x ⁻¹ᵁ Q.G ∧ Q.InFib x)) := by
  first | exact @GlobalTheory.ZH.TestFib.image_special_fibre_iff | exact GlobalTheory.ZH.TestFib.image_special_fibre_iff | (intros; apply GlobalTheory.ZH.TestFib.image_special_fibre_iff <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.model_points_eq_of_same_degeneration_data : Laws → Laws2 → Laws3 → Laws4 → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (I : Ideal R) (f : O' →+* R) (u : R), AdmBase R I → I ≠ ⊤ → Function.Injective f → ∀ (χ χ' : Sp R ⟶ Y.X) (y y' : Sp (FractionRing R) ⟶ Xo.XF c), y ≫ Y.j = jK R ≫ χ → y' ≫ Y.j = jK R ≫ χ' → χ ≫ Y.s = spMap f ≫ spMap b → χ' ≫ Y.s = spMap f ≫ spMap b → Y.HasArcData a I f u χ → Y.HasArcData a I f u χ' → χ = χ' := by
  first | exact @GlobalTheory.ArcUnique.eq_of_hasArcData | exact GlobalTheory.ArcUnique.eq_of_hasArcData | (intros; apply GlobalTheory.ArcUnique.eq_of_hasArcData <;> assumption)
end
