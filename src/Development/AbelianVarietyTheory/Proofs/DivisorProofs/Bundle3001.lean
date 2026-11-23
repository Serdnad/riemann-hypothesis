module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle085
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2799
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsDegenerationDataExtensionOverDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullFOfGenRel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SemiAbelianHomExtensionUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2890
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2636
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2605
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2777
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2898
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2886
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2766
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DivMemOfForallPowSuccDivPowMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.germ_dvd_of_sectionExpansion_dvd_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G) (σ : U.SecGT (𝟙_ _) 1) (f g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) 1 α) (q : R), U.ExpT (𝟙_ _) 1 σ f → (∀ α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom q (f α) (g α)) → ∀ (x : (𝟙_ (Over (Sp R)) ⊗ G).left), (𝟙_ (Over (Sp R)) ⊗ G).hom x = closedPoint R → ∀ (j : Fin 1 → U.P.L.L.ι), x ∈ LB.wchart U.P.L.L (fun _ : Fin 1 => (snd (𝟙_ (Over (Sp R))) G).left) j → ∃ t, gs (𝟙 _) x (LB.wchart U.P.L.L (fun _ : Fin 1 => (snd (𝟙_ (Over (Sp R))) G).left) j) (σ.f j) = cst (𝟙_ (Over (Sp R)) ⊗ G).hom x q * t := by
  first | exact @GlobalTheory.ClosedFibreDvd.germ_dvd_of_expT_dvd | exact GlobalTheory.ClosedFibreDvd.germ_dvd_of_expT_dvd | (intros; apply GlobalTheory.ClosedFibreDvd.germ_dvd_of_expT_dvd <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
noncomputable section

namespace GlobalTheory.PullDegUniq

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem nonempty_psiOn_pull {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') :
    Nonempty (PsiOn D' (specOf φ ⁻¹ᵁ hD.W)) := by
  have hm : (specOf φ ∣_ hD.W) ≫ hD.W.ι = (specOf φ ⁻¹ᵁ hD.W).ι ≫ specOf φ := morphismRestrict_ι _ _
  have key : ∀ x : D'.X, ∃ a : LB.Gen (LB.LinComb D'.P.L (K := PUnit)
      (fun _ => (toUnit (TW (specOf φ ⁻¹ᵁ hD.W)) ≫ D'.c x).left) (fun _ => -1)), a.IsGen ∧
      LB.Gen.Corr D'.P.L _ _ _ _ (LB.pullGen D'.P.L _ _ a (jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)))
        (LB.pullGen D'.P.L _ _ (D'.psi x) (jK R' ⁻¹ᵁ (specOf φ ⁻¹ᵁ hD.W)).ι) := by
    intro x
    have hψ : (toUnit (TW (specOf φ ⁻¹ᵁ hD.W)) ≫ D'.c x).left ≫ proj hD =
        (specOf φ ∣_ hD.W) ≫ (toUnit (TW hD.W) ≫ D.c (hD.xe x)).left := by
      show (specOf φ ⁻¹ᵁ hD.W).ι ≫ (D'.c x).left ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) =
        (specOf φ ∣_ hD.W) ≫ hD.W.ι ≫ (D.c (hD.xe x)).left
      rw [hD.c_pr x, ← Category.assoc, ← Category.assoc, hm]
    obtain ⟨a, ha, H⟩ := DegPull.exists_pmaps ((isGen_iff _).1 hD.w_gen) D.P.isLB D'.P.isLB (K := PUnit)
      (ε := fun _ => -1) (specOf φ ∣_ hD.W) (fun _ => hψ) (hD.psiW.psi (hD.xe x)) (hD.psiW.psi_gen _)
    refine ⟨a, ha, corr_of_val D'.P.isLB fun y J' hJ' => ?_⟩
    obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
    have hz : ((jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)) ≫ (specOf φ ∣_ hD.W)) ≫ hD.W.ι =
        (jK R' ⁻¹ᵁ (specOf φ ⁻¹ᵁ hD.W)).ι ≫ jK R' ≫ specOf φ := by
      rw [Category.assoc, hm, ← Category.assoc, morphismRestrict_ι, Category.assoc]
    obtain ⟨hp, P⟩ := ArcSpecialise.pmaps_psiOn hD hD.psiW _ _ hz x
    have v₁ := DegPull.pmaps_val (fun _ => hψ) H (jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)) y hJ hJ'
    have v₂ := DegPull.pmaps_val (fun _ => hp) P (𝟙 _) y hJ hJ'
    rw [val_pull hJ', val_pull hJ']
    rw [val_pull hJ, val_pull hJ'] at v₂
    simp only [Category.id_comp] at v₁ v₂ ⊢
    have hmor : (jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)) ≫ (toUnit (TW (specOf φ ⁻¹ᵁ hD.W)) ≫ D'.c x).left =
        (jK R' ⁻¹ᵁ (specOf φ ⁻¹ᵁ hD.W)).ι ≫ D'.xK x := by
      show (jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)) ≫ (specOf φ ⁻¹ᵁ hD.W).ι ≫ (D'.c x).left =
        (jK R' ⁻¹ᵁ (specOf φ ⁻¹ᵁ hD.W)).ι ≫ jK R' ≫ (D'.c x).left
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    rw [hmor] at v₁
    exact mul_left_cancel (v₁.symm.trans v₂)
  choose a ha hc using key
  exact ⟨⟨a, ha, hc⟩⟩

theorem exists_generic_section {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') :
    ∃ s : (TK R').left ⟶ (specOf φ ⁻¹ᵁ hD.W).toScheme, s ≫ (specOf φ ⁻¹ᵁ hD.W).ι = jK R' :=
  ⟨(isPullback_morphismRestrict (specOf φ) hD.W).lift hD.g (jK R') hD.g_comm,
    (isPullback_morphismRestrict (specOf φ) hD.W).lift_snd _ _ _⟩

theorem nonempty_isPullDeg_cancel {R₀ R₁ R₂ : Type} [CommRing R₀] [IsDomain R₀] [CommRing R₁] [IsDomain R₁]
    [CommRing R₂] [IsDomain R₂] {α : R₀ →+* R₁} {β : R₁ →+* R₂} (hα : Function.Injective α)
    (hβ : Function.Injective β) {D₀ : DegPre R₀} {D₁ : DegPre R₁} {D : DegPre R₂} (h₁ : IsPullDeg α D₀ D₁)
    (h : IsPullDeg (β.comp α) D₀ D) : Nonempty (IsPullDeg β D₁ D) := by
  have p₁ : IsGrpPullback D₁.P.A D₀.P.A (spMap α) (proj h₁) := pull_grp h₁
  have sc : spMap β ≫ spMap α = spMap (β.comp α) := (spMap_comp α β).symm
  have p : IsGrpPullback D.P.A D₀.P.A (spMap β ≫ spMap α) (proj h) := (pull_grp h).congr sc.symm rfl
  obtain ⟨Φ, e₁, e₂⟩ : ∃ Φ : D.P.A.left ⟶ D₁.P.A.left, Φ ≫ proj h₁ = proj h ∧ Φ ≫ D₁.P.A.hom = D.P.A.hom ≫ spMap β :=
    ⟨p₁.1.lift (proj h) (D.P.A.hom ≫ spMap β) (p.1.w.trans (Category.assoc _ _ _).symm), p₁.1.lift_fst _ _ _,
      p₁.1.lift_snd _ _ _⟩
  have gp : IsGrpPullback D.P.A D₁.P.A (spMap β) Φ := IsGrpPullback.cancel p₁ (p.congr rfl e₁.symm) e₂
  obtain ⟨w, hw, hr, T⟩ := FieldPull.exists_cancel_of_eq e₁ D₀.P.isLB D₁.P.isLB D.P.isLB h₁.w h.w
    ((isGen_iff _).1 h₁.w_gen) ((isGen_iff _).1 h.w_gen) sc (cubeMapOf gp).e_comm (FieldPull.pmaps_rig h₁)
    (FieldPull.pmaps_rig h)
  let xe : D.X ≃+ D₁.X := h.xe.trans h₁.xe.symm
  have hxe : ∀ x, h₁.xe (xe x) = h.xe x := fun x => h₁.xe.apply_symm_apply _
  have hc : ∀ x, (D.c x).left ≫ Φ = spMap β ≫ (D₁.c (xe x)).left := fun x => by
    apply p₁.1.hom_ext
    · rw [Category.assoc, e₁, Category.assoc, h₁.c_pr, hxe]
      exact (h.c_pr x).trans ((congrArg (· ≫ _) sc.symm).trans (Category.assoc _ _ _))
    · rw [Category.assoc, e₂, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨ψW⟩ := nonempty_psiOn_pull h₁
  obtain ⟨s, hs⟩ := exists_generic_section h₁
  obtain ⟨hD, -⟩ := DvrDeg.exists_isPullDeg_of_val hβ D₁ D ψW s hs gp w hw hr xe hc (fun x z J₁ J hJ₁ hJ => by
    obtain ⟨J₀, hJ₀⟩ := DegPull.exists_good' D₀.P.isLB z
    have sβ : jK R₂ ≫ spMap β = genMap hβ ≫ jK R₁ :=
      (Category.id_comp _).symm.trans (fracMap_sq hβ)
    have sα : jK R₁ ≫ spMap α = genMap hα ≫ jK R₀ :=
      (Category.id_comp _).symm.trans (fracMap_sq hα)
    have q₁ : genMap hβ ≫ jK R₁ ≫ spMap α = (genMap hβ ≫ genMap hα) ≫ jK R₀ :=
      (congrArg (_ ≫ ·) sα).trans (Category.assoc _ _ _).symm
    have q : 𝟙 (TK R₂).left ≫ jK R₂ ≫ spMap (β.comp α) = (genMap hβ ≫ genMap hα) ≫ jK R₀ :=
      (Category.id_comp _).trans ((congrArg (_ ≫ ·) sc.symm).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) sβ).trans ((Category.assoc _ _ _).trans q₁))))
    have v := psi_val h _ _ q hJ₀ hJ x
    have v₁ := psi_val h₁ _ _ q₁ hJ₀ hJ₁ (xe x)
    have hx : D.xK x ≫ Φ = genMap hβ ≫ D₁.xK (xe x) := by
      show (jK R₂ ≫ (D.c x).left) ≫ Φ = genMap hβ ≫ jK R₁ ≫ (D₁.c (xe x)).left
      rw [Category.assoc, hc, ← Category.assoc, sβ, Category.assoc]
    rw [hxe, v, Category.id_comp, T _ z J₀ J₁ J hJ₀ hJ₁ hJ, hx, mul_inv, _root_.mul_assoc] at v₁
    exact (mul_left_cancel v₁).symm)
  exact ⟨hD⟩

end GlobalTheory.PullDegUniq

namespace GlobalTheory.Mum

theorem isPullDeg_unique_and_comp : (∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R'), Function.Injective ρ → ∀ (D : DegPre R) (D₁ D₂ : DegPre R'), Nonempty (IsPullDeg ρ D D₁) → Nonempty (IsPullDeg ρ D D₂) → Nonempty (IsPullDeg (RingHom.id R') D₁ D₂)) ∧ ∀ (R R' R'' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [CommRing R''] [IsDomain R''] (ρ : R →+* R') (ρ' : R' →+* R''), Function.Injective ρ → Function.Injective ρ' → ∀ (D : DegPre R) (D' : DegPre R') (D'' : DegPre R''), Nonempty (IsPullDeg ρ D D') → Nonempty (IsPullDeg ρ' D' D'') → Nonempty (IsPullDeg (ρ'.comp ρ) D D'') :=
  ⟨fun _ R' _ _ _ _ ρ hρ _ _ _ ⟨p₁⟩ ⟨p₂⟩ =>
    GlobalTheory.PullDegUniq.nonempty_isPullDeg_cancel (β := RingHom.id R') hρ Function.injective_id p₁
      ((RingHom.id_comp ρ).symm ▸ p₂),
   fun _ _ _ _ _ _ _ _ _ _ _ hρ hρ' _ _ _ ⟨p⟩ ⟨q⟩ => GlobalTheory.PullDegComp.nonempty_isPullDeg_comp hρ hρ' p q⟩

end GlobalTheory.Mum
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
open GlobalTheory.Poinc.Tors

noncomputable section

namespace GlobalTheory.Poinc.Tors

theorem torsion_extend : Laws → ∀ (R : Type) [CommRing R] [IsDomain R], IsNoetherianRing R → IsIntegrallyClosed R → ∀ (P : PolAV (Spec (CommRingCat.of R))) (N : ℕ), 1 ≤ N → ∀ x : TF (R := R) (FractionRing R) ⟶ P.A, x ^ N = 1 → ∃ b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ P.A, b ^ N = 1 ∧ x = toUnit _ ≫ b := by
  intro hL R _ _ hR hIC P N hN x hx
  have hfin : IsFinite (mulA P.A N).left := (hL.mulN _ P N hN).1
  have hj : jFK (R := R) (FractionRing R) = 𝟙 _ := by
    simp [jFK]
  have hTF : (TF (R := R) (FractionRing R)).hom = jK R := by
    simp [TF, hj]
  have e1 : x ≫ mulA P.A N = toUnit _ ≫ η[P.A] := by
    rw [mulA, MonObj.comp_pow, Category.comp_id, hx]; rfl
  have h : x.left ≫ (mulA P.A N).left = jK R ≫ η[P.A].left := by
    have := congrArg CommaMorphism.left e1
    simp only [Over.comp_left] at this
    rw [this]
    congr 1
  obtain ⟨l, hl1, hl2⟩ := GlobalTheory.FiniteLift.exists_lift (mulA P.A N).left η[P.A].left x.left h
  have hl3 : l ≫ P.A.hom = 𝟙 _ := by
    rw [← Over.w (mulA P.A N), ← Category.assoc, hl1, Over.w η[P.A]]
    simp
  let b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ P.A := Over.homMk l (by simpa using hl3)
  refine ⟨b, ?_, ?_⟩
  · have e2 : b ^ N = b ≫ mulA P.A N := by rw [mulA, MonObj.comp_pow, Category.comp_id]
    rw [e2]
    ext1
    simp only [Over.comp_left, b, Over.homMk_left, hl1]
    show _ = (toUnit _ ≫ η[P.A]).left
    rw [toUnit_unit, Category.id_comp]
  · ext1
    simp only [Over.comp_left, b, Over.homMk_left]
    have w := Over.w (toUnit (TF (R := R) (FractionRing R)))
    have w' : (toUnit (TF (R := R) (FractionRing R))).left = jK R := by
      rw [← hTF, ← w]
      first | rfl | simp | (erw [Category.comp_id])
    rw [w', hl2]

end GlobalTheory.Poinc.Tors
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.StalkExt

theorem exists_agree_of_generic {U S : Scheme.{0}} (j : U ⟶ S) [IsOpenImmersion j] (G H : Over S) [GrpObj G]
    [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H) (f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj H)
    (hf : IsMonHom f) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (t : Sp R ⟶ S) [Mono t] (k : Sp (FractionRing R) ⟶ U) (hk : k ≫ j = Out.jK R ≫ t) :
    ∃ g : pullback G.hom t ⟶ H.left, g ≫ H.hom = pullback.fst G.hom t ≫ G.hom ∧
      GlobalTheory.DedekindExt.Agree (pullback.fst G.hom j) (f.left ≫ pullback.fst H.hom j) (pullback.fst G.hom t) g := by
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G hG
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian H hH
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.spec_fractionRing R (FractionRing R)

  obtain ⟨a, ha, ha'⟩ := grpPullback_iso (isGrpPullback_pullback G (Out.jK R ≫ t))
    (((isGrpPullback_pullback ((Over.pullback j).obj G) k).comp (isGrpPullback_pullback G j)).congr hk rfl)
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso (isGrpPullback_pullback H (Out.jK R ≫ t))
    (((isGrpPullback_pullback ((Over.pullback j).obj H) k).comp (isGrpPullback_pullback H j)).congr hk rfl)
  haveI := ha; haveI := hb; haveI := hf
  have hfK : IsMonHom (a.hom ≫ (Over.pullback k).map f ≫ b.inv) := inferInstance
  have hρ : (a.hom.left ≫ pullback.fst ((Over.pullback j).obj G).hom k) ≫ pullback.fst G.hom j =
      pullback.fst G.hom (Out.jK R ≫ t) := (Category.assoc _ _ _).trans ha'
  have hb2 : b.inv.left ≫ pullback.fst H.hom (Out.jK R ≫ t) =
      pullback.fst ((Over.pullback j).obj H).hom k ≫ pullback.fst H.hom j := by
    rw [← hb', ← Category.assoc, ← Over.comp_left, b.inv_hom_id, Over.id_left, Category.id_comp]
  have hK : (a.hom ≫ (Over.pullback k).map f ≫ b.inv).left ≫ pullback.fst H.hom (Out.jK R ≫ t) =
      (a.hom.left ≫ pullback.fst ((Over.pullback j).obj G).hom k) ≫ f.left ≫ pullback.fst H.hom j := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hb2, ← Category.assoc (((Over.pullback k).map f).left),
      GlobalTheory.ExtUnique.pullback_map_left_fst, Category.assoc, Category.assoc]

  obtain ⟨g, hg, hA⟩ := GlobalTheory.DedekindExt.exists_agree_of_extend (k := Out.jK R) (t := t) rfl G H
    (a.hom ≫ (Over.pullback k).map f ≫ b.inv) fun f' hf' => by
      obtain ⟨F, ⟨-, hF⟩, -⟩ := GlobalTheory.T.semiAbelian_hom_extends_from_generic_fibre R ((Over.pullback t).obj G) ((Over.pullback t).obj H)
        (IsSemiAbelian.pullback t G hG) (IsSemiAbelian.pullback t H hH) f' hf'
      exact ⟨F, hF⟩

  have hw : f.left ≫ pullback.snd H.hom j = pullback.snd G.hom j := Over.w f
  have hf₀ : (f.left ≫ pullback.fst H.hom j) ≫ H.hom = pullback.fst G.hom j ≫ G.hom := by
    refine (Category.assoc _ _ _).trans ?_
    rw [pullback.condition, pullback.condition, ← hw]
    exact (Category.assoc _ _ _).symm
  let c : pullback G.hom (Out.jK R ≫ t) ⟶ pullback G.hom t :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Out.jK R) (by rw [pullback.condition, Category.assoc])
  have hc₁ : c ≫ pullback.fst G.hom t = pullback.fst G.hom (Out.jK R ≫ t) := pullback.lift_fst _ _ _
  have hc₂ : c ≫ pullback.snd G.hom t = pullback.snd G.hom (Out.jK R ≫ t) ≫ Out.jK R := pullback.lift_snd _ _ _
  have sq : IsPullback c (pullback.snd G.hom (Out.jK R ≫ t)) (pullback.snd G.hom t) (Out.jK R) := by
    refine IsPullback.of_right ?_ hc₂ (IsPullback.of_hasPullback G.hom t)
    rw [hc₁]
    exact IsPullback.of_hasPullback G.hom (Out.jK R ≫ t)
  have : QuasiCompact c := MorphismProperty.of_isPullback sq.flip ‹_›
  have : IsSchemeTheoreticallyDominant c := .of_isPullback sq.flip
  refine ⟨g, hg, GlobalTheory.DedekindExt.Agree.of_dominant G.hom H.hom hf₀ hg c fun T u u' e => ?_⟩
  have h₁ := hA T (u ≫ c) u (by rw [Category.assoc, hc₁])
  have hu : u' = u ≫ a.hom.left ≫ pullback.fst ((Over.pullback j).obj G).hom k := by
    rw [← cancel_mono (pullback.fst G.hom j), ← e, Category.assoc, Category.assoc, hc₁, ← hρ, Category.assoc]
  rw [hu, ← Category.assoc, h₁, hK, Category.assoc, Category.assoc, Category.assoc]

theorem exists_agree_at_stalk : ∀ {U S : Scheme.{0}} (j : U ⟶ S) [IsOpenImmersion j] (G H : Over S) [GrpObj G] [GrpObj H], IsSemiAbelian G → IsSemiAbelian H → ∀ f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj H, IsMonHom f → ∀ (s : S) [IsDomain (S.presheaf.stalk s)] [IsNoetherianRing (S.presheaf.stalk s)] [IsIntegrallyClosed (S.presheaf.stalk s)] (k : Sp (FractionRing (S.presheaf.stalk s)) ⟶ U), k ≫ j = ReciprocityTheory.ChartRestriction.G.Out.jK (S.presheaf.stalk s) ≫ S.fromSpecStalk s → ∃ g : pullback G.hom (S.fromSpecStalk s) ⟶ H.left, g ≫ H.hom = pullback.fst G.hom (S.fromSpecStalk s) ≫ G.hom ∧ GlobalTheory.DedekindExt.Agree (pullback.fst G.hom j) (f.left ≫ pullback.fst H.hom j) (pullback.fst G.hom (S.fromSpecStalk s)) g := by
  intro U S j _ G H _ _ hG hH f hf s i₁ i₂ i₃ k hk
  haveI := i₁; haveI := i₂; haveI := i₃
  exact @exists_agree_of_generic U S j _ G H _ _ hG hH f hf (S.presheaf.stalk s) _ i₁ i₂ i₃ (S.fromSpecStalk s) _ k hk

end GlobalTheory.StalkExt
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem isIso_of_isIso_reductions : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (T X : Scheme.{0}) (φ : T ⟶ X) (f : X ⟶ Spec (CommRingCat.of R)), IsProper φ → IsProper f → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (c : ∀ e, (Y e).left ⟶ T), (∀ e, IsPullback (c e) (Y e).hom (φ ≫ f) (thick R I e)) → (∀ e, IsPullback (c e ≫ φ) (Y e).hom f (thick R I e)) → IsIso φ := by
  intro R _ _ I hI T X φ f hφ hf Y c hpb hpb'
  have hc := fun e => GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf R (I ^ (e + 1)) T (Y e).left (φ ≫ f) (c e) (Y e).hom (hpb e)
  have hc' := fun e => GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf R (I ^ (e + 1)) X (Y e).left f (c e ≫ φ) (Y e).hom (hpb' e)

  have hK : (baseIdeal f I).comap φ = (c 0).ker := by
    rw [(hc 0).2.1, (GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support).1 R X T f φ I, zero_add, pow_one]
  haveI : IsClosedImmersion (c 0) := (hc 0).1
  haveI : IsClosedImmersion (c 0 ≫ φ) := (hc' 0).1
  have hφc : IsClosedImmersion φ := by
    refine GlobalTheory.T.isClosedImmersion_of_proper_closedImmersion_mod_ideal R I hI T X φ f hφ inferInstance ?_
    rw [hK]
    have he : (c 0).ker.subschemeι ≫ φ = inv (c 0).toImage ≫ (c 0 ≫ φ) := by
      rw [IsIso.eq_inv_comp]
      exact Scheme.Hom.toImage_imageι_assoc _ _
    rw [he]
    infer_instance
  haveI := hφc

  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hker : φ.ker ≤ ⊥ := by
    refine GlobalTheory.T.idealSheaf_le_of_le_on_reductions_jacobson R I hI X f φ.ker ⊥ inferInstance fun e => ?_
    rw [bot_sup_eq, ← (hc' e).2.1]
    exact Scheme.Hom.le_ker_comp (c e) φ
  have hbot : φ.ker = ⊥ := le_bot_iff.1 hker
  haveI : IsIso φ.imageι := by
    change IsIso φ.ker.subschemeι
    rw [hbot]
    infer_instance
  rw [← φ.toImage_imageι]
  infer_instance

end GlobalTheory.FormalAlg
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.SiegApprox

open GlobalTheory.SiegelDescent ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison

theorem model_exists : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (F : Finset R), IsAbelianScheme A → ∀ P : LB (G2 A).left, P.IsLB → ∃ (S : Subring R) (B : Over (Sp S)) (_ : GrpObj B) (_ : IsCommMonObj B) (φ : A.left ⟶ B.left) (φ₂ : (G2 A).left ⟶ (G2 B).left) (P₀ : LB (G2 B).left), (F : Set R) ⊆ S ∧ Algebra.FiniteType ℤ S ∧ IsAbelianScheme B ∧ IsGrpPullback A B (spMap S.subtype) φ ∧ IsSquare φ φ₂ ∧ P₀.IsLB ∧ LBIso P (P₀.pull φ₂) := GlobalTheory.T.exists_finiteType_subring_model_abelian_lineBundle

theorem rig_descends : ∀ (R : Type) [CommRing R] (S : Subring R) (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (B : Over (Sp S)) [GrpObj B] [IsCommMonObj B] (φ : A.left ⟶ B.left) (φ₂ : (G2 A).left ⟶ (G2 B).left) (P : LB (G2 A).left) (P₀ : LB (G2 B).left) (a : A ⟶ G2 A) (a₀ : B ⟶ G2 B), IsAbelianScheme B → IsGrpPullback A B (spMap S.subtype) φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → a.left ≫ φ₂ = φ ≫ a₀.left → (∃ t : (P.pull a.left).Gen, t.IsGen) → ∃ F : Finset R, ∀ (R₁ : Subring R) (h : S ≤ R₁), (F : Set R) ⊆ R₁ → ∀ a₁ : (Over.pullback (spMap (Subring.inclusion h))).obj B ⟶ G2 ((Over.pullback (spMap (Subring.inclusion h))).obj B), a₁.left ≫ pφ₂ (spMap (Subring.inclusion h)) B = pφ (spMap (Subring.inclusion h)) B ≫ a₀.left → ∃ t : ((P₀.pull (pφ₂ (spMap (Subring.inclusion h)) B)).pull a₁.left).Gen, t.IsGen := GlobalTheory.T.exists_finset_generator_descends_subring

theorem symm_descends : ∀ (R : Type) [CommRing R] (S : Subring R) (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (B : Over (Sp S)) [GrpObj B] [IsCommMonObj B] (φ : A.left ⟶ B.left) (φ₂ : (G2 A).left ⟶ (G2 B).left) (P : LB (G2 A).left) (P₀ : LB (G2 B).left), IsAbelianScheme B → IsGrpPullback A B (spMap S.subtype) φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → ∃ F : Finset R, ∀ (R₁ : Subring R) (h : S ≤ R₁), (F : Set R) ⊆ R₁ → LBIso (P₀.pull (pφ₂ (spMap (Subring.inclusion h)) B)) ((P₀.pull (pφ₂ (spMap (Subring.inclusion h)) B)).pull (lift (snd ((Over.pullback (spMap (Subring.inclusion h))).obj B) ((Over.pullback (spMap (Subring.inclusion h))).obj B)) (fst ((Over.pullback (spMap (Subring.inclusion h))).obj B) ((Over.pullback (spMap (Subring.inclusion h))).obj B))).left) := GlobalTheory.T.symm_lineBundleIso_descends_subring_finset

end GlobalTheory.SiegApprox
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.diagonal_restriction_relAmple_locus_open : ∀ (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → ∃ U : S'.Opens, (∀ V : S'.Opens, V ≤ U → Out.RelAmple ((Over.pullback V.ι).obj G) ((P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)).pull (lift (𝟙 ((Over.pullback V.ι).obj G)) (𝟙 ((Over.pullback V.ι).obj G))).left)) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S') (A' : Over T) [GrpObj A'] (φ : A'.left ⟶ G.left) (φ₂ : (G2 A').left ⟶ (G2 G).left) (P' : LB (G2 A').left), IsGrpPullback A' G g φ → IsSquare φ φ₂ → P'.IsLB → LBIso P' (P.pull φ₂) → Out.RelAmple A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) → Set.range g.base ⊆ (U : Set S') := by
  first | (exact @GlobalTheory.DiagAmpleLocus.diag_relAmple_locus) | (exact GlobalTheory.DiagAmpleLocus.diag_relAmple_locus) | (intros; apply GlobalTheory.DiagAmpleLocus.diag_relAmple_locus  <;> assumption)
end
