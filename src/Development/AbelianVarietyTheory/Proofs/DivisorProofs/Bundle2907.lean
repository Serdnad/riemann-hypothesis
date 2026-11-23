module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2883
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle634
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2779
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle833
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1113
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle853
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2862
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2778
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem transport_extLam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∀ (K' : Type) [Field K'] (io : FractionRing R →+* K') (A₁ : PolAV (Sp K')) (α₁ : A₁.A.left ⟶ A.A.left) (α₁₂ : (G2 A₁.A).left ⟶ (G2 A.A).left), IsGrpPullback A₁.A A.A (spMap io) α₁ → Geo.Tor.IsSquare α₁ α₁₂ → LBIso (abelian₂ A₁.A A₁.L) ((abelian₂ A.A A.L).pull α₁₂) → ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (ρ : R →+* R₂) (i : K' ≃+* FractionRing R₂), Function.Injective ρ → (∀ r, i (io (algebraMap R _ r)) = algebraMap R₂ _ (ρ r)) → ∀ (G₂ : Over (Sp R₂)) [GrpObj G₂] [IsCommMonObj G₂] (β : G₂.left ⟶ G.left) (β₂ : (G2 G₂).left ⟶ (G2 G).left), IsGrpPullback G₂ G (spMap ρ) β → Geo.Tor.IsSquare β β₂ → ∃ (A₂ : PolAV (Sp (FractionRing R₂))) (gen₂ : ((Over.pullback (jK R₂)).obj G₂) ≅ A₂.A) (q : A₂.A.left ⟶ A₁.A.left), IsMonHom gen₂.hom ∧ ExtLam G₂ (A₂.L.pull gen₂.hom.left) (PP.pull β₂) ∧ IsGrpPullback A₂.A A₁.A (spMap i.toRingHom) q ∧ LBIso A₂.L (A₁.L.pull q) ∧ gen₂.inv.left ≫ pullback.fst G₂.hom (jK R₂) ≫ β = q ≫ α₁ ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) := by
  intro R _ _ _ G _ _ A gen hgen PP hExt K' _ io A₁ α₁ α₁₂ hα hsqα hΛ R₂ _ _ _ ρ i hρ hi G₂ _ _ β β₂ hβ hsqβ
  haveI := hgen
  have : IsCommMonObj ((Over.pullback (jK R)).obj G) := Functor.isCommMonObj_obj
  have : IsCommMonObj ((Over.pullback (jK R₂)).obj G₂) := Functor.isCommMonObj_obj
  obtain ⟨A₂, q, pq, -, mq, t, ht⟩ := GlobalTheory.polBaseChange_holds _ _ (spMap i.toRingHom) A₁
  have hq : IsGrpPullback A₂.A A₁.A (spMap i.toRingHom) q := ⟨pq, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pq.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pq.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mq]; rfl⟩
  have hLq : LBIso A₂.L (A₁.L.pull q) := LBIso.symm ⟨t, ht⟩
  have hsq : jK R₂ ≫ spMap ρ = spMap i.toRingHom ≫ spMap io ≫ jK R := by
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp [hi]
  haveI : IsMonHom gen.symm.hom := by show IsMonHom gen.inv; infer_instance
  have hgi : IsGrpPullback A.A ((Over.pullback (jK R)).obj G) (𝟙 _) gen.inv.left := isGrpPullback_of_iso gen.symm
  have gG : IsGrpPullback A.A G (jK R) (gen.inv.left ≫ pullback.fst G.hom (jK R)) :=
    (hgi.comp (isGrpPullback_pullback G (jK R))).congr (Category.id_comp _) rfl
  have gA : IsGrpPullback A₂.A G (spMap i.toRingHom ≫ spMap io ≫ jK R)
      (q ≫ α₁ ≫ gen.inv.left ≫ pullback.fst G.hom (jK R)) := hq.comp (hα.comp gG)
  have g₂ : IsGrpPullback ((Over.pullback (jK R₂)).obj G₂) G (spMap i.toRingHom ≫ spMap io ≫ jK R)
      (pullback.fst G₂.hom (jK R₂) ≫ β) :=
    ((isGrpPullback_pullback G₂ (jK R₂)).comp hβ).congr hsq rfl
  obtain ⟨e, he, hee⟩ := grpPullback_iso g₂ gA
  haveI := he
  have hei : e.inv.left ≫ e.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hgh : gen.inv.left ≫ gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have h5 : e.inv.left ≫ pullback.fst G₂.hom (jK R₂) ≫ β = q ≫ α₁ ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) := by
    rw [← hee, ← Category.assoc, hei, Category.id_comp]
  refine ⟨A₂, e, q, he, ⟨pull_isLB hExt.1 β₂, fun κ₂ hκ₂ => ?_⟩, hq, hLq, h5⟩

  obtain ⟨g₂m, hg₂, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ G ((Over.pullback (jK R)).obj G) _
    (isGrpPullback_pullback G (jK R))
  obtain ⟨γ₁, hsqγ, Ha⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ ((Over.pullback (jK R)).obj G) A.A _ hgi
  obtain ⟨q₂, hsqq, Hc⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ A₁.A A₂.A _ hq
  obtain ⟨e₂, hsqe, Hd⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ A₂.A ((Over.pullback (jK R₂)).obj G₂) _
    (isGrpPullback_of_iso e)
  have hLK := pull_isLB A.isLB gen.hom.left
  have i₀ : LBIso A.L ((A.L.pull gen.hom.left).pull gen.inv.left) :=
    LBIso.chartPull (chartPullUnpull A.L (𝟙 _) rfl)
      (chartPullLinComb A.L gen.hom.left (fun _ => gen.inv.left) (fun _ => 𝟙 _) _ (𝟙 _)
        (fun _ => by rw [hgh, Category.id_comp]))
      (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB A.isLB (𝟙 _)))
  have Ha' := Ha _ _ _ PP g₂m hLK A.isLB hExt.1 i₀ (hExt.2 g₂m hg₂)
  have Hb : LBIso (abelian₂ A₁.A A₁.L) (PP.pull (α₁₂ ≫ γ₁ ≫ g₂m)) :=
    LBIso.trans (DVR.linComb_isLB _ A₁.isLB _ _) (pull_isLB (DVR.linComb_isLB _ A.isLB _ _) _)
      (pull_isLB hExt.1 _) hΛ
      (LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ α₁₂ α₁₂ rfl)
        (chartPullSame PP (fun _ => α₁₂ ≫ γ₁ ≫ g₂m) (fun _ => γ₁ ≫ g₂m) _ α₁₂ fun _ => rfl) Ha')
  have Hc' := Hc _ _ _ PP _ A₁.isLB A₂.isLB hExt.1 hLq Hb
  have Hd' := Hd _ _ _ PP _ A₂.isLB (pull_isLB A₂.isLB _) hExt.1
    (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB A₂.isLB _)) Hc'
  have E : e₂ ≫ q₂ ≫ α₁₂ ≫ γ₁ ≫ g₂m = κ₂ ≫ β₂ := by
    apply pullback.hom_ext
    · show (e₂ ≫ q₂ ≫ α₁₂ ≫ γ₁ ≫ g₂m) ≫ (fst G G).left = (κ₂ ≫ β₂) ≫ (fst G G).left
      simp only [Category.assoc, hg₂.1, reassoc_of% hsqγ.1, reassoc_of% hsqα.1, reassoc_of% hsqq.1,
        reassoc_of% hsqe.1, hsqβ.1, reassoc_of% hκ₂.1, hee]
    · show (e₂ ≫ q₂ ≫ α₁₂ ≫ γ₁ ≫ g₂m) ≫ (snd G G).left = (κ₂ ≫ β₂) ≫ (snd G G).left
      simp only [Category.assoc, hg₂.2, reassoc_of% hsqγ.2, reassoc_of% hsqα.2, reassoc_of% hsqq.2,
        reassoc_of% hsqe.2, hsqβ.2, reassoc_of% hκ₂.2, hee]
  exact LBIso.trans (DVR.linComb_isLB _ (pull_isLB A₂.isLB _) _ _) (pull_isLB hExt.1 _)
    (pull_isLB (pull_isLB hExt.1 β₂) κ₂) Hd'
    (LBIso.chartPull (chartPullSame PP _ (fun _ => β₂) _ κ₂ fun _ => E) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ κ₂ κ₂ rfl)
      (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hExt.1 β₂)))

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum
open GlobalTheory.CechPic

theorem exists_ext_translate : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (L : LB ((Over.pullback (jK R)).obj G).left) (PP : LB (G2 G).left), L.IsLB → ExtLam G L PP →
    ∀ (O : G.left.Opens) (N : LB O.toScheme), N.IsLB →
    LBIso (N.pull (pullback.fst O.ι (pullback.fst G.hom (jK R)))) (L.pull (pullback.snd O.ι (pullback.fst G.hom (jK R)))) →
    ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, ∃ N' : LB ((𝟙 G * (toUnit G ≫ a)).left ⁻¹ᵁ O).toScheme, N'.IsLB ∧
      LBIso (N'.pull (pullback.fst ((𝟙 G * (toUnit G ≫ a)).left ⁻¹ᵁ O).ι (pullback.fst G.hom (jK R))))
        (L.pull (pullback.snd ((𝟙 G * (toUnit G ≫ a)).left ⁻¹ᵁ O).ι (pullback.fst G.hom (jK R)))) := by
  intro R _ _ G _ _ L PP hL hExt O N hN hNL a
  have hPP : PP.IsLB := hExt.1
  let GK := (Over.pullback (jK R)).obj G
  let J := pullback.fst G.hom (jK R)
  let T := (𝟙 G * (toUnit G ≫ a)).left
  let V := T ⁻¹ᵁ O
  let σ := (lift (𝟙 G) (toUnit G ≫ a)).left
  obtain ⟨N', hN', hc⟩ := cls_surj (pull (T ∣_ O) (cls N hN) - pull (V.ι ≫ σ) (cls PP hPP))
  refine ⟨N', hN', ?_⟩
  let p₁ := pullback.fst V.ι J
  let p₂ := pullback.snd V.ι J
  rw [← cls_eq_iff (pull_isLB hN' _) (pull_isLB hL _), cls_pull hN', cls_pull hL, hc]

  have hNL' : pull (pullback.fst O.ι J) (cls N hN) = pull (pullback.snd O.ι J) (cls L hL) := by
    rw [← cls_pull hN, ← cls_pull hL]
    exact (cls_eq_iff (pull_isLB hN _) (pull_isLB hL _)).2 hNL

  obtain ⟨κ₂, hκ, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ (jK R) G GK J (isGrpPullback_pullback G (jK R))
  have hLamc : lam (cls L hL) (fst GK GK) (snd GK GK) = pull κ₂ (cls PP hPP) := by
    rw [← cls_cube_two hL (fst GK GK) (snd GK GK) (LB.isLB_linComb hL _ _), ← cls_pull hPP κ₂ (pull_isLB hPP _)]
    exact (cls_eq_iff (LB.isLB_linComb hL _ _) (pull_isLB hPP _)).2 (hExt.2 κ₂ hκ)

  have hw : p₁ ≫ V.ι ≫ G.hom = p₂ ≫ GK.hom ≫ jK R := by
    rw [← Category.assoc, pullback.condition, Category.assoc]
    exact congrArg (p₂ ≫ ·) pullback.condition
  let Ty : Over (Sp (FractionRing R)) := Over.mk (p₂ ≫ GK.hom)
  let y : Ty ⟶ GK := Over.homMk p₂ rfl
  have haw : a.left ≫ G.hom = 𝟙 _ := by simpa using Over.w a
  let aK : 𝟙_ (Over (Sp (FractionRing R))) ⟶ GK :=
    Over.homMk (pullback.lift (jK R ≫ a.left) (𝟙 _) (by rw [Category.assoc, haw]; simp)) (pullback.lift_snd _ _ _)
  let aY : Ty ⟶ GK := toUnit Ty ≫ aK
  have hzero : ∀ (z : 𝟙_ (Over (Sp (FractionRing R))) ⟶ GK) (c : Pic GK.left), pull (toUnit Ty ≫ z).left c = 0 := by
    intro z c
    rw [Over.comp_left, pull_comp, GlobalTheory.DualOpen.pic_sp_local_eq_zero (FractionRing R) (pull z.left c), map_zero]
  have haY : aY.left ≫ J = p₁ ≫ V.ι ≫ G.hom ≫ a.left := by
    have : aY.left = (p₂ ≫ GK.hom) ≫ aK.left := rfl
    rw [this, Category.assoc, show aK.left ≫ J = jK R ≫ a.left from pullback.lift_fst _ _ _, ← Category.assoc,
      ← Category.assoc, ← Category.assoc]
    simp only [Category.assoc]
    rw [← Category.assoc p₁, ← Category.assoc (p₁ ≫ V.ι), Category.assoc p₁, hw]
    simp only [Category.assoc]

  have hsq : (lift y aY).left ≫ κ₂ = p₁ ≫ V.ι ≫ σ := by
    apply pullback.hom_ext
    · show ((lift y aY).left ≫ κ₂) ≫ (fst G G).left = (p₁ ≫ V.ι ≫ σ) ≫ (fst G G).left
      rw [Category.assoc, hκ.1, ← Category.assoc, ← Over.comp_left, lift_fst]
      simp only [Category.assoc, σ, ← Over.comp_left, lift_fst, Over.id_left, Category.comp_id]
      exact pullback.condition.symm
    · show ((lift y aY).left ≫ κ₂) ≫ (snd G G).left = (p₁ ≫ V.ι ≫ σ) ≫ (snd G G).left
      rw [Category.assoc, hκ.2, ← Category.assoc, ← Over.comp_left, lift_snd, haY]
      show p₁ ≫ V.ι ≫ G.hom ≫ a.left = (p₁ ≫ V.ι ≫ (lift (𝟙 G) (toUnit G ≫ a)).left) ≫ (snd G G).left
      rw [Category.assoc, Category.assoc, ← Over.comp_left, lift_snd, Over.comp_left, Over.toUnit_left]
  have hlam : pull (p₁ ≫ V.ι ≫ σ) (cls PP hPP) = @id (Pic (pullback V.ι J)) (pull (y * aY).left (cls L hL)) - pull p₂ (cls L hL) := by
    have h := congrArg (pull (lift y aY).left) hLamc
    rw [pull_lam, lift_fst, lift_snd, ← pull_comp, hsq] at h
    rw [← h, lam, hzero, show (1 : Ty ⟶ GK) = toUnit Ty ≫ 1 from (MonObj.comp_one _).symm, hzero]
    simp only [sub_zero, add_zero]
    rfl

  let u : Over.mk (Ty.hom ≫ jK R) ⟶ G := Over.homMk (p₁ ≫ V.ι) (by simpa [Ty] using hw)
  have hmul : (y * aY).left ≫ J = p₁ ≫ V.ι ≫ T := by
    have e := (isGrpPullback_pullback G (jK R)).2 Ty y aY u (u ≫ toUnit G ≫ a) (pullback.condition (f := V.ι) (g := J))
      (by rw [haY, Over.comp_left, Over.comp_left, Over.toUnit_left]; show (p₁ ≫ V.ι) ≫ _ = _; simp only [Category.assoc])
    have e' : u * (u ≫ toUnit G ≫ a) = u ≫ (𝟙 G * (toUnit G ≫ a)) := by rw [MonObj.comp_mul, Category.comp_id]
    rw [← e, e', Over.comp_left]
    exact Category.assoc _ _ _
  have hq : (p₁ ≫ (T ∣_ O)) ≫ O.ι = (y * aY).left ≫ J := by
    rw [Category.assoc, morphismRestrict_ι, hmul]
  have hN2 := congrArg (pull (pullback.lift _ _ hq)) hNL'
  rw [← pull_comp, ← pull_comp, pullback.lift_fst, pullback.lift_snd] at hN2
  rw [map_sub, ← pull_comp, ← pull_comp, hN2, hlam]
  exact sub_sub_cancel _ _

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.EndThick

theorem q_comm_of_coordEnd {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
    (a a' : D.P.A ⟶ D.P.A) (h' : D.X →+ D.X)
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A a' a) rosatiε))
    (F : thickObj R I e G ⟶ thickObj R I e G) (hF : IsCoordEnd g a a' h' u F) :
    F ≫ g.q = g.q ≫ (Over.pullback (thick R I e)).map a := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc]
    have h2 : ((Over.pullback (thick R I e)).map a).left ≫ pullback.fst D.P.A.hom (thick R I e) =
        pullback.fst D.P.A.hom (thick R I e) ≫ a.left := by
      simp
    rw [h2]
    exact hF.1
  · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc]
    have w1 : g.q.left ≫ pullback.snd D.P.A.hom (thick R I e) = pullback.snd G.hom (thick R I e) := Over.w g.q
    have w2 : ((Over.pullback (thick R I e)).map a).left ≫ pullback.snd D.P.A.hom (thick R I e) =
        pullback.snd D.P.A.hom (thick R I e) := Over.w ((Over.pullback (thick R I e)).map a)
    have w3 : F.left ≫ pullback.snd G.hom (thick R I e) = pullback.snd G.hom (thick R I e) := Over.w F
    rw [w2, w1]
    exact w3

theorem formalEnd_exists : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∃ b, FormalEnd U.toUnifPre a h' b := by
  intro R _ _ _ _ D A G _ _ _ U a a' h h' hE
  obtain ⟨ha, ha', hr, -, hc, -⟩ := hE
  have hr' := GlobalTheory.Mum.RosatiSymmetry.rosatiAdj_symm D.toPre.P.A D.toPre.P.L D.toPre.P.isLB a a' hr
  obtain ⟨u, hu, h₀⟩ := exists_ros GlobalTheory.globalFns_holds D.toPre.P.isAb D.toPre.P.isLB a' a hr'
  choose F hF using fun e => GlobalTheory.T.exists_thickenedGroup_endomorphism_torusCoordinates (U.gt e) a a' h' hc u hu h₀
  exact ⟨F, fun e => GlobalTheory.T.isMonHom_thickenedGroup_endomorphism_torusCoordinates (U.gt e) a a' h' hc u hu h₀ (F e) (hF e),
    fun e => GlobalTheory.T.thickenedGroup_endomorphism_transition_compat U.toUnifPre e a a' h' u (F e) (F (e + 1)) (hF e) (hF (e + 1)),
    fun e => q_comm_of_coordEnd (U.gt e) a a' h' u (F e) (hF e),
    fun e => GlobalTheory.T.thickenedGroup_endomorphism_torus_via_characters (U.gt e) a a' h' u hu h₀ (F e) (hF e)⟩

end GlobalTheory.Mum.EndThick
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.MapUniq

open GlobalTheory.UPel.HT.MapComp

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

theorem exists_auto {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o' : Obj b N s'} {o : Obj b N s}
    {f : S' ⟶ S} (m m' : ObjMap o' o f) : ∃ a : ObjMap o' o' (𝟙 S'), a.φ ≫ m'.φ = m.φ := by
  have w : m.φ ≫ o.A.hom = o'.A.hom ≫ f := m.cart.1.w
  set ψ := m'.cart.1.lift m.φ o'.A.hom w
  have hψ : ψ ≫ m'.φ = m.φ := m'.cart.1.lift_fst _ _ _
  have hψ₀ : ψ ≫ o'.A.hom = o'.A.hom := m'.cart.1.lift_snd _ _ _
  have hψ' : ψ ≫ o'.A.hom = o'.A.hom ≫ 𝟙 S' := by rw [Category.comp_id]; exact hψ₀
  have n : IsGrpPullback o'.A o.A (𝟙 S' ≫ f) (ψ ≫ m'.φ) := by rw [hψ, Category.id_comp]; exact m.cart
  obtain ⟨ψ₂, sq⟩ := exists_isSquare hψ'
  have e : m.φ₂ = ψ₂ ≫ m'.φ₂ := isSquare_unique m.sq (hψ ▸ isSquare_comp sq m'.sq)
  have hact : ∀ c, (o'.act.act c).left ≫ ψ = ψ ≫ (o'.act.act c).left := by
    intro c
    apply m'.cart.1.hom_ext
    · rw [Category.assoc, hψ, m.act, Category.assoc, m'.act, ← Category.assoc, hψ]
    · rw [Category.assoc, hψ₀, Over.w, Category.assoc, Over.w, hψ₀]
  have heta : ∀ y, (o'.eta y).left ≫ ψ = 𝟙 S' ≫ (o'.eta y).left := by
    intro y
    apply m'.cart.1.hom_ext
    · rw [Category.assoc, hψ, m.eta, Category.id_comp, m'.eta]
    · rw [Category.assoc, hψ₀, Category.id_comp]
  exact ⟨{ φ := ψ
           φ₂ := ψ₂
           cart := m'.cart.cancel n hψ'
           sq := sq
           act := hact
           pol := LBIso.trans o'.isLB (pull_isLB o.isLB _) (pull_isLB o'.isLB _) m.pol
             (LBIso.symm (lbIso_pull_comp m'.pol ψ₂ e))
           eta := heta }, hψ⟩

theorem objMap_φ_unique : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R)
    (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (o' : Obj b N s')
    (o : Obj b N s) (f : S' ⟶ S) (m m' : ObjMap o' o f), m.φ = m'.φ := by
  intro p _ D R _ b N hN hNp S S' s s' o' o f m m'
  obtain ⟨a, ha⟩ := exists_auto m m'
  have h1 := GlobalTheory.UPel.HT.Rigid.eq_id p D R b N hN hNp S' s' o' a
  rw [← ha, h1, Category.id_comp]

end GlobalTheory.UPel.HT.MapUniq
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

namespace GlobalTheory.TorsCount

variable {κ Q : Type} [Fintype κ] [Group Q]

theorem map_zero_of_add {L : Type} [AddCommGroup L] (e : L → Q) (hadd : ∀ a c, e (a + c) = e a * e c) :
    e 0 = 1 := by
  have h := hadd 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem map_sub_of_add {L : Type} [AddCommGroup L] (e : L → Q) (hadd : ∀ a c, e (a + c) = e a * e c)
    (a c : L) : e (a - c) = e a * (e c)⁻¹ := by
  have h := hadd (a - c) c
  rw [sub_add_cancel] at h
  rw [h, mul_inv_cancel_right]

def red (M : ℕ) (e : (κ → ℤ) → Q) (hpow : ∀ a, e a ^ M = 1) : (κ → ZMod M) → {g : Q // g ^ M = 1} :=
  fun c => ⟨e fun i => ((c i).val : ℤ), hpow _⟩

theorem exists_red (M : ℕ) [NeZero M] (e : (κ → ℤ) → Q) (hadd : ∀ a c, e (a + c) = e a * e c)
    (hker : ∀ a, e a = 1 ↔ ∃ c, a = M • c) (a : κ → ℤ) :
    ∃ c : κ → ZMod M, e (fun i => ((c i).val : ℤ)) = e a := by
  refine ⟨fun i => (a i : ZMod M), ?_⟩
  have h : e (a - fun i => (((a i : ZMod M)).val : ℤ)) = 1 := by
    refine (hker _).2 ⟨fun i => a i / (M : ℤ), funext fun i => ?_⟩
    simp only [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul, ZMod.val_intCast]
    have := Int.emod_add_mul_ediv (a i) (M : ℤ)
    linarith
  rw [map_sub_of_add e hadd, mul_inv_eq_one] at h
  exact h.symm

theorem red_injective (M : ℕ) [NeZero M] (e : (κ → ℤ) → Q) (hadd : ∀ a c, e (a + c) = e a * e c)
    (hpow : ∀ a, e a ^ M = 1) (hker : ∀ a, e a = 1 ↔ ∃ c, a = M • c) : Function.Injective (red M e hpow) := by
  intro c c' hcc
  have h1 : e (fun i => ((c i).val : ℤ)) = e (fun i => ((c' i).val : ℤ)) := congrArg Subtype.val hcc
  have h2 : e ((fun i => ((c i).val : ℤ)) - fun i => ((c' i).val : ℤ)) = 1 := by
    rw [map_sub_of_add e hadd, h1, mul_inv_cancel]
  obtain ⟨d, hd⟩ := (hker _).1 h2
  funext i
  have h3 := congrArg (fun x : κ → ℤ => ((x i : ℤ) : ZMod M)) hd
  simp only [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul, Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val,
    Int.cast_mul, ZMod.natCast_self, zero_mul] at h3
  exact sub_eq_zero.1 h3

theorem card_tors (M : ℕ) (hM : 0 < M) (e : (κ → ℤ) → Q) (hadd : ∀ a c, e (a + c) = e a * e c)
    (hpow : ∀ a, e a ^ M = 1) (hker : ∀ a, e a = 1 ↔ ∃ c, a = M • c)
    (hon : ∀ g : Q, g ^ M = 1 → ∃ a, e a = g) : Nat.card {g : Q // g ^ M = 1} = M ^ Fintype.card κ := by
  classical
  haveI : NeZero M := ⟨hM.ne'⟩
  have hb : Function.Bijective (red M e hpow) := by
    refine ⟨red_injective M e hadd hpow hker, fun ⟨g, hg⟩ => ?_⟩
    obtain ⟨a, rfl⟩ := hon g hg
    obtain ⟨c, hc⟩ := exists_red M e hadd hker a
    exact ⟨c, Subtype.ext hc⟩
  rw [← Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]

end GlobalTheory.TorsCount

namespace GlobalTheory.HTSympCover

theorem onto_tors_iff : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M → M.Coprime p → ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ S) (e : (Fin h ⊕ Fin h → ℤ) → (Over.mk y ⟶ o.A)), (∀ a c, e (a + c) = e a * e c) → (∀ a, e a ^ M = 1) → (∀ a, e a = 1 ↔ ∃ c, a = M • c) → ((∀ g : Over.mk y ⟶ o.A, g ^ M = 1 → ∃ a, e a = g) ↔ (M = 1 ∨ 2 * h = Module.finrank ℤ D.La)) := by
  intro p _ D R _ b N h M hM hcop S t o k _ _ y e hadd hpow hker
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨β, hβ⟩ := GlobalTheory.LevCover.exists_spMap (y ≫ t)
  obtain ⟨I, -⟩ := o.geom k y β hβ
  haveI := D.freeLa
  haveI := D.finLa
  let B := Module.Free.chooseBasis ℤ D.La
  let ev' : (Module.Free.ChooseBasisIndex ℤ D.La → ℤ) → (Over.mk y ⟶ o.A) := fun a => I.ev M (B.equivFun.symm a)
  have hadd' : ∀ a c, ev' (a + c) = ev' a * ev' c := fun a c => by
    simp only [ev', map_add (f := _)]
    exact I.add M _ _
  have hpow' : ∀ a, ev' a ^ M = 1 := fun a => (I.onto M hM hcop _).2 ⟨_, rfl⟩
  have hker' : ∀ a, ev' a = 1 ↔ ∃ c, a = M • c := fun a => by
    simp only [ev']
    rw [I.ker M hM hcop]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨B.equivFun c, by rw [← map_nsmul, ← hc, LinearEquiv.apply_symm_apply]⟩
    · rintro ⟨c, rfl⟩
      exact ⟨B.equivFun.symm c, map_nsmul _ _ _⟩
  have hon' : ∀ g, g ^ M = 1 → ∃ a, ev' a = g := fun g hg => by
    obtain ⟨x, hx⟩ := (I.onto M hM hcop g).1 hg
    exact ⟨B.equivFun x, by simp only [ev', LinearEquiv.symm_apply_apply, hx]⟩
  have hcard := GlobalTheory.TorsCount.card_tors M hM ev' hadd' hpow' hker' hon'
  rw [← Module.finrank_eq_card_chooseBasisIndex] at hcard
  have hinj := GlobalTheory.TorsCount.red_injective M e hadd hpow hker
  have hdom : Nat.card (Fin h ⊕ Fin h → ZMod M) = M ^ (2 * h) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_sum, Fintype.card_fin, two_mul]
  rcases Nat.lt_or_ge M 2 with hM2 | hM2
  · have h1 : M = 1 := by omega
    subst h1
    simp only [true_or, iff_true]
    intro g hg
    rw [pow_one] at hg
    exact ⟨0, by rw [hg]; exact GlobalTheory.TorsCount.map_zero_of_add e hadd⟩
  · have hMne : M ≠ 1 := by omega
    simp only [hMne, false_or]
    haveI : Finite {g : Over.mk y ⟶ o.A // g ^ M = 1} :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
    constructor
    · intro hon
      have hb : Function.Bijective (GlobalTheory.TorsCount.red M e hpow) := by
        refine ⟨hinj, fun ⟨g, hg⟩ => ?_⟩
        obtain ⟨a, rfl⟩ := hon g hg
        obtain ⟨c, hc⟩ := GlobalTheory.TorsCount.exists_red M e hadd hker a
        exact ⟨c, Subtype.ext hc⟩
      have h2 := Nat.card_eq_of_bijective _ hb
      rw [hcard, hdom] at h2
      exact Nat.pow_right_injective hM2 h2
    · intro hr g hg
      have hs : Function.Surjective (GlobalTheory.TorsCount.red M e hpow) :=
        (hinj.bijective_of_nat_card_le (by rw [hcard, hdom, hr])).2
      obtain ⟨c, hc⟩ := hs ⟨g, hg⟩
      exact ⟨_, congrArg Subtype.val hc⟩

end GlobalTheory.HTSympCover
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.semiAbelian_endomorphism_unique_over_degenerationData : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A) (h' : D.toPre.X →+ D.toPre.X), (∀ b b', FormalEnd U.toUnifPre a h' b → FormalEnd U.toUnifPre a h' b' → b = b') ∧ ∀ b b' : G ⟶ G, (∀ e, (Over.pullback (thick R (maximalIdeal R) e)).map b = (Over.pullback (thick R (maximalIdeal R) e)).map b') → b = b' := by
  first | exact @GlobalTheory.MumUniq.main | exact GlobalTheory.MumUniq.main | (intros; apply GlobalTheory.MumUniq.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.siegelQuotientFamily_local_points_eq_of_object : ∀ (h n N : ℕ) (o o' : Type) [CommRing o] [CommRing o'] (ζ : o) (ζ' : o') (F : SFam h N ζ') (j : o →+* o') (Q : SQuot F n ζ j) (R : Type) [CommRing R] [IsLocalRing R] (x y : Sp R ⟶ Q.X) (s' : Sp R ⟶ Sp o) (c : SiegPre h n ζ s'), x ≫ Q.s = y ≫ Q.s → SiegPB c Q.univ x → SiegPB c Q.univ y → x = y := by
  first | exact @GlobalTheory.SiegLev.SQuot.eq_of_siegPB | exact GlobalTheory.SiegLev.SQuot.eq_of_siegPB | (intros; apply GlobalTheory.SiegLev.SQuot.eq_of_siegPB <;> assumption)
end
