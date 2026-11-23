module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle716
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle960
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle534
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2985
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2988
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2994
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3282
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle088
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle099
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle620
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixTrivLocus

theorem lbIso_pull_comp' {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a : Y ⟶ X) (b : Z ⟶ Y) :
    LBIso (L.pull (b ≫ a)) ((L.pull a).pull b) :=
  LBIso.symm (LBIso.chartPull (chartPullLinComb L a (fun _ : PUnit => b)
      (fun _ => b ≫ a) (fun _ => 1) (𝟙 _) fun _ => (Category.id_comp _).symm)
      (chartPullId _) (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hL _)))

theorem isoLocus_closed : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (Z₁ : Scheme.{0}) [IsLocallyNoetherian Z₁] (t₁ : Z₁ ⟶ Sp Rg) (A₁ B₁ : Over Z₁) [GrpObj A₁] [GrpObj B₁] (φA₁ : A₁.left ⟶ A.left) (φB₁ : B₁.left ⟶ B.left) (Φ₁ : A₁ ⟶ B₁), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → eA.IsGen → eB.IsGen → RelAmple A L → IsGrpPullback A₁ A t₁ φA₁ → IsGrpPullback B₁ B t₁ φB₁ → IsMonHom Φ₁ → ∃ (Z : Scheme.{0}) (i : Z ⟶ Z₁), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (u : T ⟶ Z₁) (A' B' : Over T) [GrpObj A'] [GrpObj B'] (ψA : A'.left ⟶ A₁.left) (ψB : B'.left ⟶ B₁.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A₁ u ψA → IsGrpPullback B' B₁ u ψB → Φ'.left ≫ ψB = ψA ≫ Φ₁.left → (LBIso (L.pull (ψA ≫ φA₁)) ((M.pull (ψB ≫ φB₁)).pull Φ'.left) ↔ ∃ w : T ⟶ Z, w ≫ i = u) := by
  intro Rg _ A B _ _ L M eA eB Z₁ _ t₁ A₁ B₁ _ _ φA₁ φB₁ Φ₁ hA hB hL hM hgA hgB hamp hpA hpB hΦ
  haveI : IsMonHom Φ₁ := hΦ
  haveI : IsCommMonObj A := hA.comm
  haveI : IsCommMonObj A₁ := GlobalTheory.isCommMonObj_of_grpPullback _ _ A A₁ t₁ φA₁ hpA
  obtain ⟨hA₁, hL₁, hrA₁, haA₁⟩ := GlobalTheory.GrpPullbackPol.isAbelianScheme_and_pull_of_isGrpPullback _ _ t₁ A A₁ φA₁ L
    hpA hA hL ⟨eA, hgA⟩ hamp
  have hrB₁ : Out.Rigidified B₁ (M.pull φB₁) := GlobalTheory.PolBaseChange.rigidified_pull hpB ⟨eB, hgB⟩
  have hM₁ : (M.pull (Φ₁.left ≫ φB₁)).IsLB := pull_isLB hM _
  have hN : (LB.div (M.pull (Φ₁.left ≫ φB₁)) (L.pull φA₁)).IsLB := LB.isLB_div hM₁ hL₁
  have hrN : Out.Rigidified A₁ (LB.div (M.pull (Φ₁.left ≫ φB₁)) (L.pull φA₁)) := by
    refine (GlobalTheory.IsoExtend.lbIso_pull_iff_gen (L.pull φA₁) (M.pull (Φ₁.left ≫ φB₁)) (eSec A₁)).1 ?_
    obtain ⟨s, hs⟩ := hrA₁
    obtain ⟨t, ht⟩ := hrB₁
    have e1 : LBIso ((L.pull φA₁).pull (eSec A₁)) ((M.pull φB₁).pull (eSec B₁)) :=
      GlobalTheory.SabMapDescent.lbIso_of_gen_of_gen s hs t ht
    have hc : eSec A₁ ≫ Φ₁.left = eSec B₁ := congrArg (fun z => z.left) (IsMonHom.one_hom Φ₁)
    have e2 : LBIso ((M.pull φB₁).pull (eSec B₁)) ((M.pull (Φ₁.left ≫ φB₁)).pull (eSec A₁)) :=
      GlobalTheory.HomFixTransport.lbIso_pull_pull hM _ _ _ _ (by rw [← Category.assoc, hc])
    exact LBIso.trans (pull_isLB hL₁ _) (pull_isLB (pull_isLB hM _) _) (pull_isLB hM₁ _) e1 e2
  obtain ⟨Z, i, hi, H⟩ := GlobalTheory.T.trivial_locus_rigidified_bundle_closed_seesaw Z₁ A₁ (L.pull φA₁) (LB.div (M.pull (Φ₁.left ≫ φB₁)) (L.pull φA₁))
    hA₁ hL₁ haA₁ hN hrN
  refine ⟨Z, i, hi, fun T u A' B' _ _ ψA ψB Φ' hpA' hpB' hc => ?_⟩
  refine Iff.trans ?_ ((GlobalTheory.IsoExtend.lbIso_pull_iff_gen (L.pull φA₁) (M.pull (Φ₁.left ≫ φB₁)) ψA).trans
    (H T u A' ψA hpA'))
  have a1 : LBIso (L.pull (ψA ≫ φA₁)) ((L.pull φA₁).pull ψA) := lbIso_pull_comp' hL φA₁ ψA
  have a2 : LBIso ((M.pull (ψB ≫ φB₁)).pull Φ'.left) ((M.pull (Φ₁.left ≫ φB₁)).pull ψA) :=
    GlobalTheory.HomFixTransport.lbIso_pull_pull hM _ _ _ _ (by rw [← Category.assoc, hc, Category.assoc])
  have h1 := pull_isLB hL (ψA ≫ φA₁)
  have h2 := pull_isLB hL₁ ψA
  have h3 := pull_isLB (pull_isLB hM (ψB ≫ φB₁)) Φ'.left
  have h4 := pull_isLB hM₁ ψA
  exact ⟨fun h => GlobalTheory.HomFixTransport.lbIso_congr h1 h2 h3 h4 (LBIso.symm a1) h a2,
    fun h => GlobalTheory.HomFixTransport.lbIso_congr h2 h1 h4 h3 a1 h (LBIso.symm a2)⟩

end GlobalTheory.HomFixTrivLocus
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.DescGrp

theorem quasiCompact_of_isPullback {R : Type} [CommRing R] {S : Scheme.{0}} (π : S ⟶ Sp R) [Surjective π]
    (G' : Over S) (G : Over (Sp R)) (β : G'.left ⟶ G.left) (h : IsPullback β G'.hom G.hom π) [QuasiCompact π]
    [QuasiCompact G'.hom] : QuasiCompact G.hom := by
  have hs : Surjective β := MorphismProperty.of_isPullback (P := @Surjective) h.flip ‹_›
  have hc : QuasiCompact (β ≫ G.hom) := by rw [h.w]; infer_instance
  rw [quasiCompact_iff] at hc ⊢
  intro U hU hK
  have := (hc U hU hK).image β.continuous
  rwa [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp, Set.image_preimage_eq _ hs.surj] at this

theorem exists_semiAbelian_descent : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (G : Over (Sp R)) (β : G'.left ⟶ G.left), Smooth G.hom → IsPullback β G'.hom G.hom π → ∀ φ : (Over.pullback (pullback.fst π π)).obj G' ≅ (Over.pullback (pullback.snd π π)).obj G', IsMonHom φ.hom → pullback.fst G'.hom (pullback.fst π π) ≫ β = φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β → ∃ (_ : GrpObj G) (_ : IsCommMonObj G), IsSemiAbelian G ∧ IsGrpPullback G' G π β := by
  intro R _ _ _ _ S π hp hs hi G' _ _ hG G β hsm hpb φ hφ hc
  obtain ⟨m, hm⟩ := GlobalTheory.T.group_multiplication_descends_proper_surjection R S π hp hs hi G' G β hsm hpb φ hφ hc
  obtain ⟨e, he⟩ := GlobalTheory.T.group_unit_descends_proper_surjection R S π hp hs hi G' G β hpb φ hφ hc
  obtain ⟨i, hiv⟩ := GlobalTheory.T.group_inverse_descends_proper_surjection R S π hp hs hi G' G β hsm hpb φ hφ hc
  obtain ⟨g, c, hP⟩ := GlobalTheory.T.descended_comm_group_of_pullback_proper_surjection R S π hp hs hi G' G β hsm hpb m e i hm he hiv
  haveI := hG.quasiCompact
  refine ⟨g, c, ⟨c, hsm, GlobalTheory.T.isSeparated_of_isPullback_universallyClosed_surjective' R S π inferInstance hs G' G β hpb hG.separated,
    quasiCompact_of_isPullback π G' G β hpb,
    GlobalTheory.T.geometricallyConnected_of_isPullback_surjective_lft R S π inferInstance hs G' G β hpb hG.geomConnected,
    GlobalTheory.T.torusExtension_geometricFibres_of_descended_group R S π inferInstance hs G' G β hP hG.fibres⟩, hP⟩

end GlobalTheory.DescGrp
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

open GlobalTheory.CechPic

noncomputable section

namespace GlobalTheory.EndLoc.AdjClosed

variable {S : Scheme.{0}}

theorem hom_ext_sq {A : Over S} {X : Scheme.{0}} {u v : X ⟶ (A ⊗ A).left}
    (h₁ : u ≫ (fst A A).left = v ≫ (fst A A).left) (h₂ : u ≫ (snd A A).left = v ≫ (snd A A).left) : u = v := by
  have p : IsPullback (fst A A).left (snd A A).left A.hom A.hom := IsPullback.of_hasPullback _ _
  exact p.hom_ext h₁ h₂

theorem comm_left {S' : Scheme.{0}} {A : Over S} {A' : Over S'} {φ : A'.left ⟶ A.left}
    {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left} (hsq : IsSquare φ φ₂) (f : A ⟶ A) (g : A' ⟶ A')
    (hg : g.left ≫ φ = φ ≫ f.left) :
    (lift (fst A' A' ≫ g) (snd A' A')).left ≫ φ₂ = φ₂ ≫ (lift (fst A A ≫ f) (snd A A)).left := by
  apply hom_ext_sq
  · rw [Category.assoc, hsq.1, Category.assoc, ← Over.comp_left, lift_fst, ← Category.assoc, ← Over.comp_left,
      lift_fst, Over.comp_left, Over.comp_left, Category.assoc, hg]
    simp only [← Category.assoc, hsq.1]
  · rw [Category.assoc, hsq.2, Category.assoc, ← Over.comp_left, lift_snd, ← Category.assoc, ← Over.comp_left,
      lift_snd, hsq.2]

theorem comm_right {S' : Scheme.{0}} {A : Over S} {A' : Over S'} {φ : A'.left ⟶ A.left}
    {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left} (hsq : IsSquare φ φ₂) (f : A ⟶ A) (g : A' ⟶ A')
    (hg : g.left ≫ φ = φ ≫ f.left) :
    (lift (fst A' A') (snd A' A' ≫ g)).left ≫ φ₂ = φ₂ ≫ (lift (fst A A) (snd A A ≫ f)).left := by
  apply hom_ext_sq
  · rw [Category.assoc, hsq.1, Category.assoc, ← Over.comp_left, lift_fst, ← Category.assoc, ← Over.comp_left,
      lift_fst, hsq.1]
  · rw [Category.assoc, hsq.2, Category.assoc, ← Over.comp_left, lift_snd, ← Category.assoc, ← Over.comp_left,
      lift_snd, Over.comp_left, Over.comp_left, Category.assoc, hg]
    simp only [← Category.assoc, hsq.2]

end GlobalTheory.EndLoc.AdjClosed


open GlobalTheory.EndLoc.AdjClosed in
theorem GlobalTheory.EndLoc.exists_closed_adj : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), IsAbelianScheme A → Q.IsLB → (∃ t : (Q.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (Q.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso Q (Q.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (Q.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (f f' : A ⟶ A), IsMonHom f → IsMonHom f' → ∃ (Z : Scheme.{0}) (i : Z ⟶ S), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' : Over T) [GrpObj A'] [IsCommMonObj A'] (φ' : A'.left ⟶ A.left) (φ₂' : (A' ⊗ A').left ⟶ (A ⊗ A).left) (g g' : A' ⟶ A'), IsGrpPullback A' A t φ' → IsSquare φ' φ₂' → g.left ≫ φ' = φ' ≫ f.left → g'.left ≫ φ' = φ' ≫ f'.left → (LBIso ((Q.pull φ₂').pull (lift (fst A' A' ≫ g) (snd A' A')).left) ((Q.pull φ₂').pull (lift (fst A' A') (snd A' A' ≫ g')).left) ↔ ∃ z : T ⟶ Z, z ≫ i = t) := by
  intro S _ A _ _ Q hA hQ h0l h0r hsym hamp f f' hf hf'
  let β := (lift (fst A A ≫ f) (snd A A)).left
  let β' := (lift (fst A A) (snd A A ≫ f')).left
  let N := LB.LinComb Q (K := Fin 2) ![β, β'] ![1, -1]
  have hN : N.IsLB := LB.isLB_linComb hQ _ _
  have hc : cls N hN = pull β (cls Q hQ) - pull β' (cls Q hQ) := by
    rw [cls_linComb hQ]
    simp [Fin.sum_univ_two, sub_eq_add_neg]
  have hrig : Out.Rigidified (A ⊗ A) N := by
    have e : η[A ⊗ A] ≫ lift (fst A A ≫ f) (snd A A) = η[A ⊗ A] ≫ lift (fst A A) (snd A A ≫ f') := by
      have h₁ : η[A ⊗ A] ≫ fst A A = η[A] := IsMonHom.one_hom (fst A A)
      have h₂ : η[A ⊗ A] ≫ snd A A = η[A] := IsMonHom.one_hom (snd A A)
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, lift_fst, Category.assoc, lift_fst, ← Category.assoc, h₁, IsMonHom.one_hom]
      · rw [Category.assoc, lift_snd, Category.assoc, lift_snd, ← Category.assoc, h₂, IsMonHom.one_hom]
    have e' : eSec (A ⊗ A) ≫ β = eSec (A ⊗ A) ≫ β' := by
      simp only [eSec, β, β', ← Over.comp_left, e]
    refine (cls_eq_zero_iff (pull_isLB hN _)).1 ?_
    rw [cls_pull hN, hc, map_sub, ← pull_comp, ← pull_comp, e', sub_self]
  let L₀ := Out.boxLB (Q.pull (lift (𝟙 A) (𝟙 A)).left) (GlobalTheory.SquarePol.sqIsPowGrp A).pr
  have hL₀ : L₀.IsLB := LB.isLB_linComb (pull_isLB hQ _) _ _
  have hamp₀ : Out.RelAmple (A ⊗ A) L₀ :=
    GlobalTheory.relAmple_boxLB S _ A 2 (GlobalTheory.SquarePol.sqIsPowGrp A) _ (pull_isLB hQ _) hamp
  have hAA : IsAbelianScheme (A ⊗ A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  obtain ⟨Z, i, hi, hZ⟩ := GlobalTheory.T.trivial_locus_rigidified_bundle_closed_seesaw S (A ⊗ A) L₀ N hAA hL₀ hamp₀ hN hrig
  refine ⟨Z, i, hi, fun T t A' _ _ φ' φ₂' g g' hpb hsq hg hg' => ?_⟩
  have hpb₂ := GlobalTheory.WeilIntegral.isGrpPullback_prod hpb hpb hsq.1 hsq.2
  rw [← hZ T t (A' ⊗ A') φ₂' hpb₂, ← cls_eq_zero_iff (pull_isLB hN _), cls_pull hN, hc, map_sub, ← pull_comp,
    ← pull_comp, ← comm_left hsq f g hg, ← comm_right hsq f' g' hg', pull_comp, pull_comp, sub_eq_zero,
    ← cls_eq_iff (pull_isLB (pull_isLB hQ _) _) (pull_isLB (pull_isLB hQ _) _)]
  rfl
end
end
