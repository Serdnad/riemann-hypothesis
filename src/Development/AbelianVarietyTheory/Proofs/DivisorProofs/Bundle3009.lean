module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2909
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle033
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveCubeBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2955
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle085
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupGaloisMapMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle073
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2911
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.SymDesc

open GlobalTheory.CechPic

theorem exists_gen_of_invariant {X Y Y' : Scheme.{0}} {K : Type} [Fintype K] {L : LB X} (hL : L.IsLB) (π : Y' ⟶ Y)
    {Γ₀ : Type} (act : Γ₀ → (Y' ⟶ Y')) (hact : ∀ σ, act σ ≫ π = π)
    (H : ∀ V : Y.Opens, Function.Injective (π.app V).hom ∧ ∀ u : Γ(Y', π ⁻¹ᵁ V),
      (∀ σ (h : π ⁻¹ᵁ V ≤ act σ ⁻¹ᵁ (π ⁻¹ᵁ V)), ((act σ).appLE _ _ h).hom u = u) → u ∈ Set.range (π.app V).hom)
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (u : LB.Gen (LB.LinComb L (fun k => π ≫ φ k) ε)) (hu : u.IsGen)
    (h : ∀ σ (z : Y') (J), Good L z J → val u (act σ) z J = val u (𝟙 Y') z J) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen := by
  have le : ∀ j : K → L.ι, π ⁻¹ᵁ LB.wchart L φ j ≤ LB.wchart L (fun k => π ≫ φ k) j :=
    fun j y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have inv : ∀ (j : K → L.ι) σ (h₁ : π ⁻¹ᵁ LB.wchart L φ j ≤ act σ ⁻¹ᵁ (π ⁻¹ᵁ LB.wchart L φ j)),
      ((act σ).appLE _ _ h₁).hom (res (le j) (u.s j)).val = (res (le j) (u.s j)).val := by
    intro j σ h₁
    refine fn_ext fun z hz => ?_
    have hz' : act σ z ∈ π ⁻¹ᵁ LB.wchart L φ j := h₁ hz
    have e₀ : gs (𝟙 Y') z _ (((act σ).appLE _ _ h₁).hom (res (le j) (u.s j)).val) =
        gs (act σ) z _ (res (le j) (u.s j)).val := by
      have := (gs_res (𝟙 Y') z h₁ hz (((act σ).app _).hom (res (le j) (u.s j)).val)).trans
        (gs_pull (𝟙 Y') (act σ) z _ hz' _)
      rw [Category.id_comp] at this
      exact this
    rw [e₀, gs_unit (act σ) z _ hz', gs_unit (𝟙 Y') _ _ hz]
    choose I hI using fun χ : Y' ⟶ X => exists_chart hL (χ z)
    have c₁ := gen_trans hu (act σ) z (le j hz') (Good.mem hI _ (act σ))
    have c₂ := gen_trans hu (𝟙 Y') z (le j hz) (Good.mem hI _ (𝟙 Y'))
    have c₃ : trF (fun k => π ≫ φ k) ε (act σ) z j (fun k => I (act σ ≫ π ≫ φ k)) =
        trF (fun k => π ≫ φ k) ε (𝟙 Y') z j (fun k => I (𝟙 Y' ≫ π ≫ φ k)) := by
      refine Finset.prod_congr rfl fun k _ => ?_
      have : act σ ≫ π ≫ φ k = 𝟙 Y' ≫ π ≫ φ k := by rw [reassoc_of% hact σ, Category.id_comp]
      show gm (act σ ≫ π ≫ φ k) z (L.U (j k) ⊓ L.U (I (act σ ≫ π ≫ φ k))) (L.g (j k) (I (act σ ≫ π ≫ φ k))) ^ _ =
        gm (𝟙 Y' ≫ π ≫ φ k) z (L.U (j k) ⊓ L.U (I (𝟙 Y' ≫ π ≫ φ k))) (L.g (j k) (I (𝟙 Y' ≫ π ≫ φ k))) ^ _
      rw [this]
    exact congrArg Units.val ((gm_res (act σ) z (le j) hz' _).trans
      ((c₁.trans ((congrArg₂ (· * ·) c₃ (h σ z I hI)).trans c₂.symm)).trans
        (gm_res (𝟙 Y') z (le j) hz _).symm))
  have desc : ∀ j : K → L.ι, ∃ a : Γ(Y, LB.wchart L φ j)ˣ, pullU π _ a = res (le j) (u.s j) := by
    intro j
    obtain ⟨a, ha⟩ := (H _).2 _ (inv j)
    obtain ⟨b, hb⟩ := (H _).2 (res (le j) (u.s j))⁻¹.val (fun σ h₁ => by
      refine (Units.mul_left_inj (res (le j) (u.s j))).1 ?_
      rw [Units.inv_mul]
      conv_lhs => rw [← inv j σ h₁]
      rw [← map_mul, Units.inv_mul, map_one])
    have ab : a * b = 1 := (H _).1 (by rw [map_mul, ha, hb, Units.mul_inv, map_one])
    exact ⟨⟨a, b, ab, (mul_comm b a).trans ab⟩, Units.ext ha⟩
  choose a ha using desc
  have hv : ∀ j (Z : Scheme.{0}) (r : Z ⟶ Y') (y : Z), π (r y) ∈ LB.wchart L φ j →
      gm (r ≫ π) y (LB.wchart L φ j) (a j) = gm r y (LB.wchart L (fun k => π ≫ φ k) j) (u.s j) := by
    intro j Z r y hy
    exact (gm_pull r π y _ hy _).symm.trans ((congrArg (gm r y _) (ha j)).trans (gm_res r y (le j) hy _))
  refine ⟨⟨a⟩, fun j j' => Units.ext ((H (LB.wchart L φ j ⊓ LB.wchart L φ j')).1 ?_)⟩
  refine congrArg Units.val (unit_ext (a := pullU π _ _) (b := pullU π _ _) fun y hy => ?_)
  have hy' : π y ∈ LB.wchart L φ j ⊓ LB.wchart L φ j' := hy
  refine (gm_pull (𝟙 Y') π y _ hy' _).trans (Eq.trans ?_ (gm_pull (𝟙 Y') π y _ hy' _).symm)
  refine ((gm_res (𝟙 Y' ≫ π) y _ hy' _).trans ((hv j _ _ y hy'.1).trans
    (gen_trans hu (𝟙 Y') y (le j hy'.1) (le j' hy'.2)))).trans (Eq.symm ?_)
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_linComb L φ ε (𝟙 Y' ≫ π) y j j' hy'.1 hy'.2).trans ?_)
    ((gm_res (𝟙 Y' ≫ π) y _ hy' _).trans (hv j' _ _ y hy'.2)))
  simp only [trF, Category.id_comp]

theorem isSymmetric_of_exists_gen {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G)
    (t : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])) (ht : t.IsGen) :
    L.IsSymmetric := by
  have e₂ : eSec G ≫ (ι[G]).left = eSec G := by
    rw [eSec, ← Over.comp_left, GrpObj.one_inv]
  have hi : LBIso L.L (L.L.pull (ι[G]).left) := by
    refine gen_chartPull (h := 𝟙 G.left) ⟨fun p => ![p.1 PUnit.unit, p.2], ?_, ?_⟩ t ht
    · intro p y hy
      exact Set.mem_iInter.2 fun k => by
        fin_cases k
        · exact mem_pull.1 hy.1
        · exact hy.2
    · intro y p q hp hq
      have hp1 := mem_pull.1 hp.1
      have hq1 := mem_pull.1 hq.1
      have hm : ∀ (p : (L.L.pull (ι[G]).left).ι × L.L.ι),
          y ∈ (LB.div (L.L.pull (ι[G]).left) L.L).U p →
          y ∈ LB.wchart L.L ![(ι[G]).left, 𝟙 G.left] ![p.1 PUnit.unit, p.2] := by
        intro p hp
        exact Set.mem_iInter.2 fun k => by
          fin_cases k
          · exact mem_pull.1 hp.1
          · exact hp.2
      refine (gm_div L.L (L.L.pull (ι[G]).left) (𝟙 _) y p q ⟨hp, hq⟩).trans ?_
      rw [gm_pull_g L.L (ι[G]).left (𝟙 _) y p.1 q.1 hp.1 hq.1]
      refine Eq.trans ?_ (gm_linComb L.L ![(ι[G]).left, 𝟙 G.left] ![1, -1] (𝟙 _) y _ _ (hm p hp) (hm q hq)).symm
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        zpow_one, zpow_neg, Category.id_comp]
      rfl
  have he : eSec G ≫ (ι[G]).left = 𝟙 _ ≫ eSec G := e₂.trans (Category.id_comp _).symm
  exact ⟨he, Unif.RigidifyIso.exists_rigidified_iso S S (𝟙 S) G G _ he L L hi⟩

theorem exists_sym_pull {S S' : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {G' : Over S'} [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {β : G'.left ⟶ G.left} (gp : IsGrpPullback G' G f β) {L : LB G.left} (hL : L.IsLB)
    {L' : LB G'.left} (hL' : L'.IsLB) (hiso : LBIso L' (L.pull β))
    (s : LB.Gen (LB.LinComb L' (K := Fin 2) ![(ι[G']).left, 𝟙 G'.left] ![1, -1])) (hs : s.IsGen)
    (hr : LB.Gen.Corr L' _ _ _ _ (LB.pullGen L' _ _ s (eSec G')) (LB.oneGen L')) :
    ∃ u : LB.Gen (LB.LinComb L (fun k : Fin 2 => β ≫ ![(ι[G]).left, 𝟙 G.left] k) ![1, -1]), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over S')).left) (z : Z) (I), Good L z I → val u (r ≫ eSec G') z I = 1 := by
  obtain ⟨w, hw⟩ := hiso
  have hp := (isGen_iff w).1 hw
  have hι : (ι[G']).left ≫ β = β ≫ (ι[G]).left := by
    have e := congrArg (fun q => q.left) (map_inv (pushHom gp G') (𝟙 G'))
    simp only [Hom.inv_def, Category.id_comp] at e
    refine e.trans ?_
    show (𝟙 _ ≫ β) ≫ _ = _
    rw [Category.id_comp]
  have e₁ : eSec G' ≫ (ι[G']).left = eSec G' := by
    rw [eSec, ← Over.comp_left, GrpObj.one_inv]
  have hc : ∀ k : Fin 2, ![(ι[G']).left, 𝟙 G'.left] k ≫ β = β ≫ ![(ι[G]).left, 𝟙 G.left] k := fun k => by
    fin_cases k
    · exact hι
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨t₁, ht₁, v₁⟩ := exists_up hp hL hL' s hs
  obtain ⟨u, hu, vu⟩ := exists_gen hL (φ' := fun k : Fin 2 => β ≫ ![(ι[G]).left, 𝟙 G.left] k) (ε' := ![1, -1])
    (fun U _ h => Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ (![1, -1] : Fin 2 → ℤ) k) (hc k)) t₁ ht₁
  refine ⟨u, hu, fun Z r z I hI => ?_⟩
  choose J hJ using fun χ : Z ⟶ G'.left => exists_chart hL' (χ z)
  rw [vu Z _ z I hI, val_of t₁ _ z I (fun k => I (((r ≫ eSec G') ≫ ![(ι[G']).left, 𝟙 G'.left] k) ≫ β))
    (fun k => congrArg I (Category.assoc _ _ _).symm)]
  refine (v₁ Z (r ≫ eSec G') z _ _ (Set.mem_iInter.2 fun k => hI (((r ≫ eSec G') ≫ ![(ι[G']).left, 𝟙 G'.left] k) ≫ β))
    (Good.mem hJ _ _)).trans ?_
  have h1 : val s (r ≫ eSec G') z J = 1 :=
    (val_pull hJ s (eSec G') r).symm.trans ((val_corr hJ hr r).trans (val_one _))
  refine (congrArg₂ (· * ·) ?_ h1).trans (_root_.mul_one 1)
  have k : ∀ (V : Type) [CommGroup V] (q : (Z ⟶ G'.left) → V),
      ∏ k : Fin 2, q ((r ≫ eSec G') ≫ ![(ι[G']).left, 𝟙 G'.left] k) ^ (![1, -1] : Fin 2 → ℤ) k = 1 := by
    intro V _ q
    simp [Fin.prod_univ_two, e₁]
  exact k _ (fun q => gw w q z (I (q ≫ β)) (J q))

end GlobalTheory.Mum.SymDesc

namespace GlobalTheory.Mum

open SymDesc

theorem isSymmetric_of_pull_iso_unif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → ∀ (L : LB G.left) (hL : L.IsLB), LBIso U'.LG.L (L.pull β) → ∀ (rig : LB.Gen (L.pull (eSec G))) (hr : rig.IsGen), RigLB.IsSymmetric (⟨L, rig, hL, hr⟩ : RigLB G) := by
  intro R _ _ _ _ R' _ _ _ ρ hρ hg D D' hD A' G' _ _ _ U' a G _ _ β hG gp hβ L hL hiso rig hr
  obtain ⟨u, hu, h1⟩ := exists_sym_pull gp hL U'.LG.isLB hiso U'.symG U'.symG_gen U'.symG_rig
  have := U'.smooth
  have := hG.smooth
  have hsurj : Function.Surjective (pullback.snd G'.hom (jK R')).appTop.hom := by
    have hw : U'.gen.hom.left ≫ A'.A.hom = pullback.snd G'.hom (jK R') := Over.w U'.gen.hom
    have : IsIso U'.gen.hom.left := ((Over.forget _).mapIso U'.gen).isIso_hom
    have : IsIso U'.gen.hom.left.appTop := inferInstanceAs (IsIso (U'.gen.hom.left.app ⊤))
    rw [← hw]
    exact surj_comp (ConcreteCategory.bijective_of_isIso U'.gen.hom.left.appTop).2
      (GlobalTheory.SemiRigid.globalFns _ _ A'.isAb).2
  have he : eSec G' ≫ G'.hom = 𝟙 _ := Over.w η[G']
  obtain ⟨t, ht⟩ := exists_gen_of_invariant hL β a.act hβ
    (GlobalTheory.T.galois_invariant_functions_flat_baseChange R R' ρ hρ hg _ _ G.hom G'.hom β inferInstance gp.1 a.act hβ fun σ => (a.cart σ).1.w)
    _ _ u hu fun σ z J hJ => by
      have key := GlobalTheory.ValueForm.gen_unique_of_injective hL (φ := fun k : Fin 2 => a.act σ ≫ β ≫ ![(ι[G]).left, 𝟙 G.left] k)
        (fun V _ q => Finset.prod_congr rfl fun k _ => by
          dsimp only
          rw [reassoc_of% hβ σ])
        (pullback.fst G'.hom (jK R')) (GlobalTheory.ValueForm.app_generic_injective _) (pullback.snd _ _)
        (pullback.lift (jK R' ≫ eSec G') (𝟙 _) (by
          rw [Category.id_comp]
          exact (Category.assoc _ _ _).trans ((congrArg (jK R' ≫ ·) he).trans (Category.comp_id _))))
        (pullback.lift_snd _ _ _) hsurj (DVR.pullGen_isGen _ _ _ _ hu (a.act σ)) hu (fun y I hI => by
          rw [pullback.lift_fst]
          refine (val_pull hI _ _ _).trans (Eq.trans ?_ (h1 _ (jK R') y I hI).symm)
          have e : (jK R' ≫ eSec G') ≫ a.act σ = (jK R' ≫ (cubeMapOf (a.cart σ)).e) ≫ eSec G' :=
            (Category.assoc _ _ _).trans ((congrArg (jK R' ≫ ·) (cubeMapOf (a.cart σ)).e_comm).trans
              (Category.assoc _ _ _).symm)
          exact (congrArg (fun q => val u q y I) e).trans (h1 _ _ y I hI)) _ (𝟙 _) z J hJ
      have k₂ := (val_pull hJ u (a.act σ) (𝟙 _)).symm.trans key
      rwa [Category.id_comp] at k₂
  exact isSymmetric_of_exists_gen _ t ht

end GlobalTheory.Mum
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

theorem existsUnique_of_openImmersion : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ) (M : Model b N) (Y₀ Y : Scheme.{0}) (i : Y₀ ⟶ Y) (s₀ : Y₀ ⟶ M.X) (s : Y ⟶ M.X) (σ₀ : Y₀ ⟶ Sp R) (σ : Y ⟶ Sp R) (o o' : Obj b N σ) (o₀ o₀' : Obj b N σ₀) (m : ObjMap o₀ o i) (m' : ObjMap o₀' o' i) (ψ₀ : o₀.A ⟶ o₀'.A) (ψ : o.A ⟶ o'.A), IsOpenImmersion i → i ≫ s = s₀ → m.φ ≫ ψ.left = ψ₀.left ≫ m'.φ → (∀ (S : Scheme.{0}) (f : S ⟶ Y), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∃ f₀ : S ⟶ Y₀, f₀ ≫ i = f) → (∀ (S : Scheme.{0}) (x : S ⟶ M.X) (o₁ o₁' : Obj b N (x ≫ M.s)) (m₁ : ObjMap o₁ M.univ x) (ψ₁ : o₁.A ⟶ o₁'.A), IsUnit ((p : ℕ) : Γ(S, ⊤)) → IsPIsog c o₁ o₁' ψ₁ → IsTj r w j o₁ o₁' ψ₁ → ∃! y : S ⟶ Y₀, y ≫ s₀ = x ∧ ∃ (m₀ : ObjMap o₁ o₀ y) (m₂ : ObjMap o₁' o₀' y), m₀.φ ≫ ψ₀.left = ψ₁.left ≫ m₂.φ) → ∀ (S : Scheme.{0}) (x : S ⟶ M.X) (o₁ o₁' : Obj b N (x ≫ M.s)) (m₁ : ObjMap o₁ M.univ x) (ψ₁ : o₁.A ⟶ o₁'.A), IsUnit ((p : ℕ) : Γ(S, ⊤)) → IsPIsog c o₁ o₁' ψ₁ → IsTj r w j o₁ o₁' ψ₁ → ∃! y : S ⟶ Y, y ≫ s = x ∧ ∃ (m₀ : ObjMap o₁ o y) (m₂ : ObjMap o₁' o' y), m₀.φ ≫ ψ.left = ψ₁.left ≫ m₂.φ := by
  intro p _ D R _ b N _ _ r w j c M Y₀ Y i s₀ s σ₀ σ o o' o₀ o₀' m m' ψ₀ ψ _ his hsq hfac hU S x o₁ o₁' m₁ ψ₁
    hp hisog htj
  have comp_map {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
      {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : Obj b N s₁}
      {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} (h₁ : ObjMap o₁ o₂ f) (h₂ : ObjMap o₂ o₃ g) :
      ∃ m : ObjMap o₁ o₃ (f ≫ g), m.φ = h₁.φ ≫ h₂.φ := by
    have sq : IsSquare (h₁.φ ≫ h₂.φ) (h₁.φ₂ ≫ h₂.φ₂) := by
      constructor
      · rw [Category.assoc, h₂.sq.1, ← Category.assoc, h₁.sq.1, Category.assoc]
      · rw [Category.assoc, h₂.sq.2, ← Category.assoc, h₁.sq.2, Category.assoc]
    have act : ∀ c, (o₁.act.act c).left ≫ (h₁.φ ≫ h₂.φ) = (h₁.φ ≫ h₂.φ) ≫ (o₃.act.act c).left := by
      intro c
      rw [← Category.assoc, h₁.act, Category.assoc, h₂.act, Category.assoc]
    have eta : ∀ y, (o₁.eta y).left ≫ (h₁.φ ≫ h₂.φ) = (f ≫ g) ≫ (o₃.eta y).left := by
      intro y
      rw [← Category.assoc, h₁.eta, Category.assoc, h₂.eta, Category.assoc]
    have H : LBIso (o₂.P.pull h₁.φ₂) ((o₃.P.pull h₂.φ₂).pull h₁.φ₂) :=
      LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o₂.P h₁.φ₂ h₁.φ₂ rfl)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (o₃.P.pull h₂.φ₂) h₁.φ₂ h₁.φ₂ rfl) h₂.pol
    have H' : LBIso (o₂.P.pull h₁.φ₂) (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
      LBIso.chartPull (chartPullId _) (chartPullIn o₃.P (fun _ : PUnit => h₂.φ₂) (fun _ => 1) h₁.φ₂) H
    have pol : LBIso o₁.P (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
      LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol H'
    exact ⟨⟨h₁.φ ≫ h₂.φ, h₁.φ₂ ≫ h₂.φ₂, h₁.cart.comp h₂.cart, sq, act, pol, eta⟩, rfl⟩
  obtain ⟨y₀, ⟨hy₀, m₀, m₂, hsq₀⟩, huniq⟩ := hU S x o₁ o₁' m₁ ψ₁ hp hisog htj
  obtain ⟨a, ha⟩ := comp_map m₀ m
  obtain ⟨b, hb⟩ := comp_map m₂ m'
  refine ⟨y₀ ≫ i, ⟨by rw [Category.assoc, his, hy₀], a, b, ?_⟩, ?_⟩
  · rw [ha, hb]
    rw [Category.assoc, hsq, ← Category.assoc, hsq₀, Category.assoc]
  · rintro y ⟨hy, n₀, n₂, hsqn⟩
    obtain ⟨f₀, rfl⟩ := hfac S y hp
    obtain ⟨k₀, hk₀⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ n₀ m
    obtain ⟨k₂, hk₂⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ n₂ m'
    have hsqk : k₀.φ ≫ ψ₀.left = ψ₁.left ≫ k₂.φ := by
      apply m'.cart.1.hom_ext
      · rw [Category.assoc, Category.assoc, ← hsq, ← Category.assoc, hk₀, hsqn, ← hk₂]
      · rw [Category.assoc, Over.w ψ₀, k₀.cart.1.w, Category.assoc, k₂.cart.1.w, ← Category.assoc, Over.w ψ₁]
    have e := huniq f₀ ⟨by rw [← his, ← Category.assoc]; exact hy, k₀, k₂, hsqk⟩
    rw [e]

end GlobalTheory.UPel.HT.ES
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.SelfPull

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

theorem exists_cast {R₀ R₁ : Type} [CommRing R₀] [IsDomain R₀] [CommRing R₁] [IsDomain R₁] {f₀ f₁ : R₀ →+* R₁}
    {D₀ : DegPre R₀} {D₁ : DegPre R₁} (e : f₀ = f₁) (h : IsPullDeg f₀ D₀ D₁) :
    ∃ h' : IsPullDeg f₁ D₀ D₁, proj h' = proj h ∧ h'.xe = h.xe := by
  subst e; exact ⟨h, rfl, rfl⟩

theorem proj_def {R₀ R₁ : Type} [CommRing R₀] [IsDomain R₀] [CommRing R₁] [IsDomain R₁] {f : R₀ →+* R₁}
    {D₀ : DegPre R₀} {D₁ : DegPre R₁} (h : IsPullDeg f D₀ D₁) :
    proj h = h.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf f) := rfl

theorem exists_self_of_comp {R₀ R₁ : Type} [CommRing R₀] [IsDomain R₀] [CommRing R₁] [IsDomain R₁]
    {α : R₀ →+* R₁} {β : R₁ →+* R₁} (hα : Function.Injective α) (hβ : Function.Injective β)
    {D₀ : DegPre R₀} {D : DegPre R₁} (h₁ : IsPullDeg α D₀ D) (h : IsPullDeg (β.comp α) D₀ D)
    (hp : proj h = proj h₁) (hx : h.xe = h₁.xe) :
    ∃ h' : IsPullDeg β D D, proj h' ≫ proj h₁ = proj h₁ ∧ ∀ x, h'.xe x = x := by
  have p₁ : IsGrpPullback D.P.A D₀.P.A (spMap α) (proj h₁) := pull_grp h₁
  have sc : spMap β ≫ spMap α = spMap (β.comp α) := (spMap_comp α β).symm
  have p : IsGrpPullback D.P.A D₀.P.A (spMap β ≫ spMap α) (proj h) := (pull_grp h).congr sc.symm rfl
  obtain ⟨Φ, e₁, e₂⟩ : ∃ Φ : D.P.A.left ⟶ D.P.A.left, Φ ≫ proj h₁ = proj h ∧ Φ ≫ D.P.A.hom = D.P.A.hom ≫ spMap β :=
    ⟨p₁.1.lift (proj h) (D.P.A.hom ≫ spMap β) (p.1.w.trans (Category.assoc _ _ _).symm), p₁.1.lift_fst _ _ _,
      p₁.1.lift_snd _ _ _⟩
  have gp : IsGrpPullback D.P.A D.P.A (spMap β) Φ := IsGrpPullback.cancel p₁ (p.congr rfl e₁.symm) e₂
  obtain ⟨w, hw, hr, T⟩ := FieldPull.exists_cancel_of_eq e₁ D₀.P.isLB D.P.isLB D.P.isLB h₁.w h.w
    ((isGen_iff _).1 h₁.w_gen) ((isGen_iff _).1 h.w_gen) sc (cubeMapOf gp).e_comm (FieldPull.pmaps_rig h₁)
    (FieldPull.pmaps_rig h)
  let xe : D.X ≃+ D.X := h.xe.trans h₁.xe.symm
  have hxe : ∀ x, h₁.xe (xe x) = h.xe x := fun x => h₁.xe.apply_symm_apply _
  have hc : ∀ x, (D.c x).left ≫ Φ = spMap β ≫ (D.c (xe x)).left := fun x => by
    apply p₁.1.hom_ext
    · rw [Category.assoc, e₁, Category.assoc, h₁.c_pr, hxe]
      exact (h.c_pr x).trans ((congrArg (· ≫ _) sc.symm).trans (Category.assoc _ _ _))
    · rw [Category.assoc, e₂, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨ψW⟩ := GlobalTheory.PullDegUniq.nonempty_psiOn_pull h₁
  obtain ⟨s, hs⟩ := GlobalTheory.PullDegUniq.exists_generic_section h₁
  obtain ⟨hD, hD₁, hD₂, -⟩ := GalMul.exists_isPullDeg_of_val hβ D D ψW s hs gp w hw hr xe hc (fun x z J₁ J hJ₁ hJ => by
    obtain ⟨J₀, hJ₀⟩ := DegPull.exists_good' D₀.P.isLB z
    have sβ : jK R₁ ≫ spMap β = genMap hβ ≫ jK R₁ :=
      (Category.id_comp _).symm.trans (fracMap_sq hβ)
    have sα : jK R₁ ≫ spMap α = genMap hα ≫ jK R₀ :=
      (Category.id_comp _).symm.trans (fracMap_sq hα)
    have q₁ : genMap hβ ≫ jK R₁ ≫ spMap α = (genMap hβ ≫ genMap hα) ≫ jK R₀ :=
      (congrArg (_ ≫ ·) sα).trans (Category.assoc _ _ _).symm
    have q : 𝟙 (TK R₁).left ≫ jK R₁ ≫ spMap (β.comp α) = (genMap hβ ≫ genMap hα) ≫ jK R₀ :=
      (Category.id_comp _).trans ((congrArg (_ ≫ ·) sc.symm).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) sβ).trans ((Category.assoc _ _ _).trans q₁))))
    have v := psi_val h _ _ q hJ₀ hJ x
    have v₁ := psi_val h₁ _ _ q₁ hJ₀ hJ₁ (xe x)
    have hx : D.xK x ≫ Φ = genMap hβ ≫ D.xK (xe x) := by
      show (jK R₁ ≫ (D.c x).left) ≫ Φ = genMap hβ ≫ jK R₁ ≫ (D.c (xe x)).left
      rw [Category.assoc, hc, ← Category.assoc, sβ, Category.assoc]
    rw [hxe, v, Category.id_comp, T _ z J₀ J₁ J hJ₀ hJ₁ hJ, hx, mul_inv, _root_.mul_assoc] at v₁
    exact (mul_left_cancel v₁).symm)
  refine ⟨hD, by rw [hD₁, e₁, hp], fun x => ?_⟩
  rw [hD₂]
  show h₁.xe.symm (h.xe x) = x
  rw [hx]; exact h₁.xe.symm_apply_apply x

theorem exists_isPullDeg_self_pullOver : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R'), Function.Injective ρ →
    ∀ (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg ρ D D') (σ : Gal ρ),
      ∃ h : IsPullDeg (Gal.hom σ) D' D', PullOver hD h := by
  intro R R' _ _ _ _ ρ hρ D D' hD σ
  have eq : ρ = (Gal.hom σ).comp ρ := RingHom.ext fun r => (σ.2 r).symm
  obtain ⟨h₀, cp, cx⟩ := exists_cast eq hD
  obtain ⟨h, h₁, h₂⟩ := exists_self_of_comp hρ σ.1.injective hD h₀ cp cx
  refine ⟨h, h₂, fun b c hb hc => ?_⟩
  rw [hb, hc, ← proj_def, ← proj_def]
  exact h₁

end GlobalTheory.Mum.SelfPull
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.TwBack

variable {R : Type} [CommRing R] [IsDomain R]

theorem prod_tw (D : DegPre R) (a : D.P.A ⟶ D.P.A) (n : ℕ) (β : D.X) {U : Type} [CommGroup U]
    (g : (D.P.A.left ⟶ D.P.A.left) → U) :
    ∏ k, g (tφ D a β k) ^ tε n 0 k = ∏ k, g (D.famφB β k) ^ DegPre.famε n k := by
  rw [Fin.prod_univ_castSucc (n := 4)]
  show (∏ k : Fin 4, _) * g a.left ^ (0 : ℤ) = _
  rw [zpow_zero, _root_.mul_one]
  refine Finset.prod_congr rfl fun k _ => ?_
  fin_cases k <;> rfl

theorem vanMod_of_van (I : Ideal R) {D : DegPre R} {k : ℕ} {α : D.X} (b : D.SecB k α) (e : ℕ) (h : Van I b e) :
    VanMod I b e := by
  intro j
  refine fn_ext fun y hy => ?_
  choose J hJ using fun χ : (thickObj R I e D.P.A).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ y)
  refine (gs_pull (𝟙 _) _ y _ hy _).trans (Eq.trans ?_ (DVR.gs_zero _ y _ hy).symm)
  refine (sec_trans b _ y hy (Good.mem hJ (D.famφB α) _)).trans ?_
  exact (congrArg _ (h _ (𝟙 _) y J hJ)).trans (mul_zero _)

theorem shift_zero {X : Type} [AddCommGroup X] (h h' : X →+ X) (n : ℕ) (mu : X) :
    shift h h' n 0 mu = n • mu := by
  rw [shift, zero_smul, add_zero, natCast_zsmul]

theorem famFE_of_tfe (D : DegPre R) (a : D.P.A ⟶ D.P.A) (h h' : D.X →+ D.X) (n : ℕ) (F : ∀ β, SecT D a n 0 β)
    (hF : TFE h h' F)
    (s : ∀ α : D.X, LB.Sec (LB.LinComb D.P.L (DegPre.famφ D (FractionRing R) α) (DegPre.famε n)))
    (hs : ∀ α (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D (FractionRing R)).left) (z : Z) (J), Good D.P.L z J →
      sval (s α) x z J = sval (F α) (x ≫ (DegPre.prB D (FractionRing R)).left) z J) :
    DegPre.FamFE D (FractionRing R) n s := by
  intro mu α u hu hc
  have hT : TRel h mu (F α) (F (α + n • mu)) := by
    have := hF mu α
    rwa [shift_zero] at this
  obtain ⟨u', hu', hv⟩ := exists_gen D.P.isLB (φ' := dφ D a mu α (α + n • mu)) (ε' := dε n 0) (fun U _ g => by
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, DegPre.deltaφ, DegPre.deltaε, dφ, dε, zpow_neg,
      Finset.prod_inv_distrib, DVR.GC.famφ_eq]
    rw [prod_tw D a n _ (fun ψ => g ((DegPre.prB D (FractionRing R)).left ≫ ψ)),
      prod_tw D a n _ (fun ψ => g ((DegPre.trF D (FractionRing R) mu).left ≫ (DegPre.prB D (FractionRing R)).left ≫ ψ))])
    u hu
  have hfac : IsFac D a h n 0 mu α (α + n • mu) u' := by
    refine ⟨hu', fun z J hJ => ?_⟩
    have e := val_corr hJ hc (𝟙 _)
    rw [val_pull hJ, Category.id_comp, DegPre.famMult, val_pull hJ, val_mul hJ, val_mul hJ, Category.id_comp] at e
    rw [hv _ _ z J hJ, zpow_zero, _root_.mul_one, add_zero, zpow_natCast, zpow_natCast]
    exact e.trans (congrArg₂ (· * ·) (congrArg₂ (· * ·) (map_pow _ _ _) rfl) (map_pow _ _ _))
  refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_
  rw [hs _ _ _ y J hJ, hs _ _ _ y J hJ, ← hv _ _ y J hJ, Category.assoc]
  exact hT u' hfac _ (𝟙 _) y J hJ

theorem exists_intFam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (h h' : D.toPre.X →+ D.toPre.X) (n : ℕ) (F : ∀ β, SecT D.toPre a n 0 β), Small (maximalIdeal R) (w := id) F → TFE h h' F → ∃ Φ : IntFam (maximalIdeal R) D.toPre n, ∀ β, (∀ (Z : Scheme.{0}) (x : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J → sval (Φ.f β) x z J = sval (F β) x z J) := by
  intro R _ _ _ _ D a h h' n F hS hF
  have hL := D.toPre.P.isLB
  choose f hf using fun β => exists_sec hL (φ' := D.toPre.famφB β) (ε' := DegPre.famε n)
    (fun U _ g => prod_tw D.toPre a n β g) (F β)
  choose s hs using fun β => exists_sec hL (φ' := DegPre.famφ D.toPre (FractionRing R) β) (ε' := DegPre.famε n)
    (fun U _ g => Finset.prod_congr rfl fun i _ => by rw [DVR.GC.famφ_eq])
    (DVR.pullSec D.toPre.P.L _ _ (f β) (DegPre.prB D.toPre (FractionRing R)).left)
  have hs' : ∀ β (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J),
      Good D.toPre.P.L z J → sval (s β) x z J = sval (f β) (x ≫ (DegPre.prB D.toPre (FractionRing R)).left) z J :=
    fun β Z x z J hJ => (hs β Z x z J hJ).trans (DVR.SectionScalarValuation.sval_pullSec _ _ _ _ x z hJ)
  have h1 : Out.scal (DegPre.BF D.toPre (FractionRing R)).hom (1 : R) = 1 := by
    unfold Out.scal; rw [map_one, map_one]
  refine ⟨⟨⟨s, famFE_of_tfe D.toPre a h h' n F hF s fun β Z x z J hJ => (hs' β Z x z J hJ).trans (hf β Z _ z J hJ)⟩,
    f, fun β => ?_, fun e => (hS e).subset fun β hβ hv => hβ (vanMod_of_van _ _ e fun Z x z J hJ =>
      (hf β Z _ z J hJ).trans (hv Z x z J hJ))⟩, hf⟩
  rw [h1]
  exact DVR.SectionScalarValuation.secScal_of_sval hL fun y J hJ => (hs' β _ _ y J hJ).symm

end GlobalTheory.TwBack
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.polarisation_topChernDensity_eq_factorial_mixed : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (L : Fin D → HermLB p) (c : AlgChart p σ D), ∀ y ∈ c.e.source, FibreProj.pol (fun n => c.chernDens ((ArInt.comb L n).φ σ) y) = D.factorial * dens (fun i => MLine.ofHerm (L i) σ) c y := by
  first | exact @GlobalTheory.Mix.pol_chernDens_comb | exact GlobalTheory.Mix.pol_chernDens_comb | (intros; apply GlobalTheory.Mix.pol_chernDens_comb <;> assumption)
end
