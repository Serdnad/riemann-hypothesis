module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3292
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3144
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.DenseGenericOfFlat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2858
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3297
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3146
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilySimilitudeGroupActionFreeTransitive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3089
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2641
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2778
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle111
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle938
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1384
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1476
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3204
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1304
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3284
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3106
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3285
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

theorem _root_.GlobalTheory.T.chernMass_eq_selfIntersection_of_generated : ∀ (Y : Var ℂ) (L : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L), φ.IsCInf → ∀ (n : ℕ) (u : Fin n → L.Sec), ⨆ i, nonzeroLocus (u i) = ⊤ → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = (topSelfIntersection ℂ L Y.dim : ℝ) := by
  first | exact @GlobalTheory.chernInt_eq_topSelf_of_generated | exact GlobalTheory.chernInt_eq_topSelf_of_generated | (intros; apply GlobalTheory.chernInt_eq_topSelf_of_generated <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg

theorem subsingleton_idealSheafData_of_isEmpty (W : Scheme.{0}) [IsEmpty W] :
    Subsingleton W.IdealSheafData := by
  constructor
  intro a b
  apply Scheme.IdealSheafData.ext
  funext U
  exact Subsingleton.elim _ _

theorem alg_of_isEmpty {R : Type} [CommRing R] {W : Scheme.{0}} [IsEmpty W]
    (f : W ⟶ Spec (CommRingCat.of R)) (I : Ideal R) : Alg f I := by
  have := subsingleton_idealSheafData_of_isEmpty W
  intro t _ hp
  exact ⟨t 0, hp 0, fun _ => Subsingleton.elim _ _⟩

theorem alg_of_isSeparated : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
    ∀ (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)), IsSeparated f → LocallyOfFiniteType f →
      QuasiCompact f → Alg f I := by
  intro R _ _ I hI W₀ f₀ hsep hlft hqc
  have : IsLocallyNoetherian W₀ := LocallyOfFiniteType.isLocallyNoetherian f₀
  have : CompactSpace W₀ := QuasiCompact.compactSpace_of_compactSpace f₀
  have : AlgebraicGeometry.IsNoetherian W₀ := {}
  suffices H : ∀ Z : TopologicalSpace.Closeds W₀, ∀ (W : Scheme.{0}) (i : W ⟶ W₀), IsClosedImmersion i →
      Set.range i ⊆ (Z : Set W₀) → Alg (i ≫ f₀) I by
    simpa using H ⊤ W₀ (𝟙 _) inferInstance (by simp)
  intro Z
  induction Z using WellFoundedLT.induction with
  | _ Z ih =>
  intro W i hi hZ
  have hsep' : IsSeparated (i ≫ f₀) := inferInstance
  have hlft' : LocallyOfFiniteType (i ≫ f₀) := inferInstance
  have hqc' : QuasiCompact (i ≫ f₀) := inferInstance
  by_cases hW : Nonempty W
  · obtain ⟨W', P, π, q, s, U, hπ, hU, hiso, hs, hq, hcomm⟩ :=
      GlobalTheory.T.chow_lemma_projective_modification R W (i ≫ f₀) hsep' hlft' hqc' hW
    have hA : Alg (π ≫ i ≫ f₀) I := by
      rw [← hcomm]
      exact GlobalTheory.T.algebraise_of_isImmersion_projective_completeNoeth R I hI W' P q s hs hq
    let K := Scheme.IdealSheafData.vanishingIdeal
      (⟨(U : Set W)ᶜ, U.isOpen.isClosed_compl⟩ : TopologicalSpace.Closeds W)
    have hK : ((K.support : Set W)) = (U : Set W)ᶜ := Scheme.IdealSheafData.coe_support_vanishingIdeal _
    refine GlobalTheory.T.algebraisation_of_proper_modification_noetherian_step R I W (i ≫ f₀) hsep' hlft' hqc' W' π U hπ hiso K ?_ hA ?_
    · intro x hx
      by_contra hxU
      apply hx
      rw [← SetLike.mem_coe, hK]
      exact hxU
    · intro k
      let Z' : TopologicalSpace.Closeds W₀ :=
        ⟨i '' (U : Set W)ᶜ, i.isClosedEmbedding.isClosedMap _ U.isOpen.isClosed_compl⟩
      have hlt : Z' < Z := by
        refine lt_of_le_of_ne ?_ ?_
        · rintro y ⟨x, _, rfl⟩
          exact hZ ⟨x, rfl⟩
        · intro heq
          obtain ⟨u, hu⟩ := hU
          have h1 : i u ∈ (Z : Set W₀) := hZ ⟨u, rfl⟩
          rw [← heq] at h1
          obtain ⟨x, hx, hxu⟩ := h1
          exact hx (i.isClosedEmbedding.injective hxu ▸ hu)
      have h2 := ih Z' hlt _ ((K ^ k).subschemeι ≫ i) inferInstance (by
        rintro _ ⟨x, rfl⟩
        refine ⟨(K ^ k).subschemeι x, ?_, rfl⟩
        have hsub : ((K ^ k).support : Set W) ⊆ (U : Set W)ᶜ := by
          rcases Nat.eq_zero_or_pos k with rfl | hk
          · rw [pow_zero, Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.support_top]
            intro y hy
            exact hy.elim
          · rw [Scheme.IdealSheafData.support_pow _ _ hk.ne', hK]
        apply hsub
        rw [← Scheme.IdealSheafData.range_subschemeι]
        exact ⟨x, rfl⟩)
      rwa [Category.assoc] at h2
  · have : IsEmpty W := not_nonempty_iff.1 hW
    exact alg_of_isEmpty _ I

end GlobalTheory.FormalAlg
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_finExt_lbExt_of_factor : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ExtLam G (A.L.pull gen.hom.left) ((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ φ : R →+* W, Function.Injective φ → IsLocalHom φ → ∀ (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW) (κ : pullback GW.hom (jK W) ⟶ pullback G.hom (jK R)), IsGrpPullback GW G (spMap φ) βW → κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW → LBIso (UW.LG.L.pull (pullback.fst GW.hom (jK W))) ((A.L.pull gen.hom.left).pull κ) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (κ₁ : pullback G₁.hom (jK R') ⟶ pullback G.hom (jK R)) (L₁ : LB G₁.left), FinExt ρ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ κ₁ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β ∧ L₁.IsLB ∧ LBIso (L₁.pull (pullback.fst G₁.hom (jK R'))) ((A.L.pull gen.hom.left).pull κ₁) := by
  intro R _ _ _ hR D D' F A' G' _ _ hG' U' oA oG hOL G _ _ hG inc pr hinc hpr h1 h2 A gen hgen hext W _ _ _ hW φ hφ hloc GW _ _ βW DW AW UW κ hpb hκ hiso
  obtain ⟨L₁, hL₁, hiso₁⟩ := GlobalTheory.T.symmetricPrincipalPolarisation_extends_semiAbelian R hR.1 G hG A gen hgen _ hext
  have hsp : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _
  have hL : (A.L.pull gen.hom.left).IsLB := LB.isLB_pull A.isLB _
  refine ⟨R, inferInstance, inferInstance, inferInstance, RingHom.id R, G, inferInstance, inferInstance, 𝟙 _, 𝟙 _, L₁,
    ⟨hR.1, Function.injective_id, RingHom.Finite.id R⟩, ?_, by simp, hL₁, ?_⟩
  · haveI : IsMonHom (Iso.refl G).hom := (inferInstance : IsMonHom (𝟙 G))
    exact (isGrpPullback_of_iso (Iso.refl G)).congr hsp.symm rfl
  · exact LBIso.trans (LB.isLB_pull hL₁ _) hL (LB.isLB_pull hL _) hiso₁ (GlobalTheory.TInj.GenPull.pull_id_iso hL)

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor GlobalTheory.SiegLevCalc
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SiegLevCover



theorem exists_levelCover : ∀ (g n ℓ j : ℕ) (F : SFam g n (zetaAway n)), 1 ≤ g → 3 ≤ n → Odd n → ℓ.Prime → ℓ ∣ n →
    1 ≤ j →
    ∃ (κ : cycAway n →+* cycAway (n * (ℓ ^ j) ^ 2)) (F' : SFam g (n * (ℓ ^ j) ^ 2) (zetaAway (n * (ℓ ^ j) ^ 2)))
      (q : F'.X ⟶ F.X),
      (Function.Injective κ ∧ κ (zetaAway n) = zetaAway (n * (ℓ ^ j) ^ 2) ^ ((ℓ ^ j) ^ 2) ∧ IsFinite (spMap κ) ∧
        Etale (spMap κ) ∧ Surjective (spMap κ)) ∧
      (q ≫ F.s = F'.s ≫ spMap κ ∧ IsFinite q ∧ Etale q ∧ Surjective q ∧ SRel F'.univ F.univ ((ℓ ^ j) ^ 2) 1 q) ∧
      ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ) (ρ : Γ → (F'.X ⟶ F'.X)) (ν : Γ → (F'.univ.A.left ⟶ F'.univ.A.left)),
        ρ 1 = 𝟙 _ ∧ (∀ a b, ρ (a * b) = ρ a ≫ ρ b) ∧ ν 1 = 𝟙 _ ∧ (∀ a b, ν (a * b) = ν a ≫ ν b) ∧
        (∀ a, SRelBy F'.univ F'.univ ((ℓ ^ j) ^ 2) ((ℓ ^ j) ^ 2) (ρ a) (ν a)) ∧ (∀ a, ρ a ≫ q = q) ∧
        ∀ (K : Type) [Field K] [IsAlgClosed K] (x y : Sp K ⟶ F'.X), x ≫ q = y ≫ q → ∃! a, x ≫ ρ a = y := by
  intro g n ℓ j F hg hn hodd hℓ hℓn hj
  have hn0 : n ≠ 0 := by omega
  have hd0 : (ℓ ^ j) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)
  have hN0 : n * (ℓ ^ j) ^ 2 ≠ 0 := Nat.mul_ne_zero hn0 hd0
  have hnN : n ∣ n * (ℓ ^ j) ^ 2 := dvd_mul_right n _
  have hNn : n * (ℓ ^ j) ^ 2 / n = (ℓ ^ j) ^ 2 := Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hn0)
  have hℓodd : Odd ℓ := Odd.of_dvd_nat hodd hℓn
  have hNodd : Odd (n * (ℓ ^ j) ^ 2) := hodd.mul (hℓodd.pow.pow)
  have hN3 : 3 ≤ n * (ℓ ^ j) ^ 2 := le_trans hn (Nat.le_mul_of_pos_right n (Nat.pos_of_ne_zero hd0))
  have hpow : ∃ a, n * (ℓ ^ j) ^ 2 ∣ n ^ a := ⟨2 * j + 1, by
    rw [pow_succ' n (2 * j)]
    refine mul_dvd_mul_left n ?_
    rw [← pow_mul, mul_comm j 2]
    exact pow_dvd_pow_of_dvd hℓn _⟩
  obtain ⟨κ, hinj, hζ, hfes⟩ := GlobalTheory.SiegelTor.exists_inclusion_cycAway n (n * (ℓ ^ j) ^ 2) hN0 hnN
  obtain ⟨hfin, het, hsurj⟩ := hfes hpow
  obtain ⟨F'⟩ := GlobalTheory.SiegelTor.exists_sFam_cycAway g (n * (ℓ ^ j) ^ 2) hg hN3 hNodd
  obtain ⟨Q⟩ := GlobalTheory.SiegLev.nonempty_sQuot g n _ F' κ hn hNodd hnN hζ hfin het
  let Fq : SFam g n (zetaAway n) :=
    { X := Q.X
      s := Q.s
      smooth := Q.smooth
      qproj := Q.qproj
      univ := Q.univ
      princ := Q.princ
      rep := fun S s' c hred hdense hpr =>
        GlobalTheory.quotFam_represents g n _ F' κ Q hn hNodd hnN hinj hζ hfin het hsurj S s' c hred hdense hpr
      inj := fun R _ _ x y s' c hs h₁ h₂ =>
        GlobalTheory.SiegLev.SQuot.eq_of_siegPB g n _ _ _ (zetaAway n) (zetaAway _) F' κ Q R x y s' c hs h₁ h₂ }
  obtain ⟨e, he, hpb⟩ := SFam.exists_iso Fq F
  obtain ⟨Ga, _, _, ρ, ν, h1, hmul, hν1, hνmul, hbase, hrel, hfree, htrans⟩ :=
    GlobalTheory.SiegAct.siegel_group_action g n _ F' κ hn hNodd hnN hζ
  rw [hNn] at hζ hrel htrans
  have hlow : SRel F'.univ Q.univ ((ℓ ^ j) ^ 2) 1 Q.π := by
    have := Q.low
    rwa [hNn] at this
  let q : F'.X ⟶ F.X := Q.π ≫ e.hom
  have hqs : q ≫ F.s = F'.s ≫ spMap κ := by
    show (Q.π ≫ e.hom) ≫ F.s = _
    rw [Category.assoc, he]
    exact Q.base
  have hq : SRel F'.univ F.univ ((ℓ ^ j) ^ 2) 1 q :=
    sRel_comp ((sRel_one_one_iff Q.univ F.univ e.hom).2 hpb) hlow
  haveI := Q.fin
  haveI := Q.etale
  haveI := Q.onto
  have hinv : ∀ a, ρ a ≫ q = q := by
    intro a
    obtain ⟨c, hc⟩ := (GlobalTheory.siegPre_pullback g n (cycAway n) (zetaAway n) F.X F'.X F.s (q ≫ F.s) q F.univ rfl).1
    have m1 : SRel c F'.univ 1 ((ℓ ^ j) ^ 2) (𝟙 F'.X) :=
      SiegLevCalc.sRel_cancel (f' := 𝟙 F'.X) hq (by rw [Category.id_comp]; exact (sRel_one_one_iff _ _ _).2 hc)
    have m2 : SRel F'.univ F.univ ((ℓ ^ j) ^ 2) 1 (ρ a ≫ q) := sRel_comp hq ⟨ν a, hrel a⟩
    have m3 := sRel_comp m2 m1
    rw [Category.id_comp, sRel_one_one_iff] at m3
    refine SFam.hom_ext F c _ _ ?_ m3 hc
    rw [Category.assoc, hqs]
    exact hbase a
  refine ⟨κ, F', q, ⟨hinj, hζ, hfin, het, hsurj⟩, ⟨hqs, inferInstance, inferInstance, inferInstance, hq⟩,
    Ga, inferInstance, inferInstance, ρ, ν, h1, hmul, hν1, hνmul, hrel, hinv, ?_⟩
  intro K _ _ x y hxy
  obtain ⟨c, hc⟩ :=
    (GlobalTheory.siegPre_pullback g n (cycAway n) (zetaAway n) F.X (Sp K) F.s ((x ≫ q) ≫ F.s) (x ≫ q) F.univ rfl).1
  have mx : SRel c F'.univ 1 ((ℓ ^ j) ^ 2) x := SiegLevCalc.sRel_cancel hq ((sRel_one_one_iff _ _ _).2 hc)
  have my : SRel c F'.univ 1 ((ℓ ^ j) ^ 2) y := SiegLevCalc.sRel_cancel hq (by rw [← hxy]; exact (sRel_one_one_iff _ _ _).2 hc)
  have hs : x ≫ F'.s ≫ spMap κ = y ≫ F'.s ≫ spMap κ := by
    rw [← hqs, ← Category.assoc, hxy, Category.assoc]
  obtain ⟨a, ha⟩ := htrans K x y _ c hs mx my
  refine ⟨a, ha, fun b hb => ?_⟩
  have hy : y ≫ ρ (a⁻¹ * b) = y := by
    calc y ≫ ρ (a⁻¹ * b) = x ≫ ρ (a * (a⁻¹ * b)) := by rw [hmul a, ← ha, Category.assoc]
      _ = y := by rw [mul_inv_cancel_left, hb]
  exact (inv_mul_eq_one.1 (hfree K y _ hy)).symm

end GlobalTheory.SiegLevCover
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory.PELU

theorem pow_eq_one_of_isGrpPullback {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (hG : IsGrpPullback G' G f φ) (e : 𝟙_ (Over S) ⟶ G)
    (e' : 𝟙_ (Over S') ⟶ G') (h : e'.left ≫ φ = f ≫ e.left) (N : ℕ) (hN : e ^ N = 1) : e' ^ N = 1 := by
  let T : Over S' := 𝟙_ (Over S')
  let ψ : (T ⟶ G') → (Over.mk (T.hom ≫ f) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ φ) (by
      rw [Category.assoc, hG.1.w, ← Category.assoc, Over.w x]; rfl)
  have hψ : ∀ x y, ψ (x * y) = ψ x * ψ y := fun x y => by
    ext1
    exact (hG.2 T x y (ψ x) (ψ y) rfl rfl).symm
  let Ψ : (T ⟶ G') →* (Over.mk (T.hom ≫ f) ⟶ G) := MonoidHom.mk' ψ hψ
  have inj : Function.Injective ψ := fun x y hxy => by
    ext1
    apply hG.1.hom_ext
    · exact congrArg CommaMorphism.left hxy
    · rw [Over.w x, Over.w y]
  have h1 : ψ e' = toUnit _ ≫ e := by
    ext1
    simp only [ψ, Over.homMk_left, Over.comp_left, h]
    congr 1
  apply inj
  have : Ψ (e' ^ N) = Ψ 1 := by
    rw [map_pow, map_one]
    show (ψ e') ^ N = 1
    rw [h1, ← comp_pow, hN, comp_one]
  exact this

end GlobalTheory.PELU

namespace GlobalTheory.PELU

theorem nonempty_unif : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (R : Type) [CommRing R] (σ : R →+* ℂ) (Λ : Type) (F : Fam R O Λ g) (N : ℕ) (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (d : ℕ), 3 ≤ N → (∀ a, F.eta a ^ N = 1) → SmoothOfRelativeDimension d F.s → QuasiCompact F.s → (∀ D' t, C D' t → FullMark N D' t) → FineAt F σ ρ N C → Nonempty (Unif F σ ρ N C) := by
  intro O _ bar g ρ R _ σ Λ F N C d hN heta hsm hqc hfull hfine
  obtain ⟨F', hbc⟩ := GlobalTheory.T.exists_complexBaseChange_polarizedAbelianFamily O g R σ Λ F
  obtain ⟨f, φ, hX, hA, -, -, heta'⟩ := id hbc
  have e' : ∀ a, F'.eta a ^ N = 1 := fun a =>
    pow_eq_one_of_isGrpPullback f φ hA (F.eta a) (F'.eta a) (heta' a) N (heta a)
  have s' : SmoothOfRelativeDimension d F'.s :=
    (smoothOfRelativeDimension_isStableUnderBaseChange d).of_isPullback hX hsm
  have q' : QuasiCompact F'.s := MorphismProperty.of_isPullback hX hqc
  exact GlobalTheory.T.complexUniformisation_of_complexBaseChange O bar g ρ R σ Λ F N C F' hbc
    (GlobalTheory.T.complexUniformisation_of_markedPeriods_family O bar g ρ Λ F' N C d hN e' s' q' hfull (GlobalTheory.T.isFineModuliAtComplexEmbedding_complexBaseChange O bar g ρ R σ Λ F N C F' hbc hfine))

end GlobalTheory.PELU
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.mul_descends_near_closed_fibre_of_embedding : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (E : Emb M.π G') (N : Near M.π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom M.π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u → l ≫ E.f = pullback.fst _ _ ≫ fU → N.Law := by
  first | exact @GlobalTheory.Mum.Near.law_of_emb | exact GlobalTheory.Mum.Near.law_of_emb | (intros; apply GlobalTheory.Mum.Near.law_of_emb <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_galoisAction_on_uniformisedGroup_pulledData : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), Base R → FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), Nonempty (GalAct ρ hD U') := by
  first | exact @GlobalTheory.Mum.galAct_exists | exact GlobalTheory.Mum.galAct_exists | (intros; apply GlobalTheory.Mum.galAct_exists <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES.IsogDVR

theorem exists_obj_extend_of_isPIsog : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (c : ℕ) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (v : Sp V ⟶ Sp R) (o : Obj b N v) (oK o₁ : Obj b N (spMap (algebraMap V K) ≫ v)) (m : ObjMap oK o (spMap (algebraMap V K))) (ψ : oK.A ⟶ o₁.A), IsPIsog c oK o₁ ψ → ∃ o' : Obj b N v, Nonempty (ObjMap o₁ o' (spMap (algebraMap V K))) := by
  intro p _ D R _ b N _ _ c V K _ _ _ _ _ _ v o o₀ o₀' m ψ₀ h
  have hc := h.pos
  obtain ⟨-, hhom, -, -, -, ψ', hhom', h1, h2⟩ := id h
  obtain ⟨hf, hfl⟩ := GlobalTheory.IsogFiniteFlat.isFinite_and_flat_of_quasiInverse _ o₀.A o₀'.A o₀.ab o₀'.ab ψ₀ ψ' c hc.ne'
    hhom hhom' h1 h2
  have hsc : Surjective (ψ'.left ≫ ψ₀.left) := by
    rw [← Over.comp_left, h2]; exact GlobalTheory.AbelianLimit.surjective_pow o₀'.A o₀'.ab c hc
  have hs : Surjective ψ₀.left := Surjective.of_comp ψ'.left ψ₀.left
  have hcomm := o.ab.comm
  obtain ⟨B, _, φB, hB, hφB⟩ := exists_model V K o.A o.ab o₀.A o₀'.A m.φ ψ₀ c m.cart o₀'.ab hc
    (fun T x hx => by
      have : x ≫ ψ₀ ≫ ψ' = 1 := by rw [← Category.assoc, hx, MonObj.one_comp]
      rwa [h1, MonObj.comp_pow, Category.comp_id] at this)
  exact exists_obj V K v _ rfl o₀' B φB hB hφB

end GlobalTheory.UPel.HT.ES.IsogDVR
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES.ValExt

theorem exists_ext_target : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∀ (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs gt : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → gt ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = t₀ → IsFinite gs → Etale gs → IsFinite gt → Etale gt → IsPIsog c o₀ o₀' ψ₀ → IsTj r w j o₀ o₀' ψ₀ → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (y : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ s₀ → ∃ z : Sp V ⟶ M.X, spMap (algebraMap V K) ≫ z = x ≫ t₀ :=
  of_ext GlobalTheory.UPel.HT.ES.IsogDVR.exists_isPIsog_extend_dvr

end GlobalTheory.UPel.HT.ES.ValExt
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianScheme_dual_representable_affine_base : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → HasRep A g (𝟙_ _) := by
  first | exact @GlobalTheory.DualCon.hasRep_affine | exact GlobalTheory.DualCon.hasRep_affine | (intros; apply GlobalTheory.DualCon.hasRep_affine <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem int_update_tens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (D : ℕ) (L : Fin D → MLine p σ) (i : Fin D) (A B : MLine p σ) (f : CxPts p σ → ℝ), Intg (Function.update L i A) f → Intg (Function.update L i B) f → Intg (Function.update L i (A.tens B)) f ∧ Mix.int (Function.update L i (A.tens B)) f = Mix.int (Function.update L i A) f + Mix.int (Function.update L i B) f := by
  intro k _ X p σ hp D L i A B f hA hB
  haveI : SecondCountableTopology (CxPts p σ) := CxPts.secondCountableTopology_of_isProjOver σ hp
  have h := GlobalTheory.T.mixedChern_integral_add_of_density_add k X p σ D _ _ _ (fun c => GlobalTheory.T.mixedChernFormDensity_update_tensor_add k X p σ D L i A B c) f
  exact ⟨h.1 hA hB, h.2 (h.1 hA hB) hA hB⟩

end GlobalTheory.Mix
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.uniformisedPoint_extends_along_thetaMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o : Type) [CommRing o] (m n : ℕ) (f : Xo.XF c ⟶ PSpace o n), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) → ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f → ∀ b : o →+* c.F, f ≫ PSpace.str o n = pullback.snd _ _ ≫ spMap b → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)), Nonempty (PELUnif (IsLocalRing.maximalIdeal R) t) → ∀ y : Sp (FractionRing R) ⟶ Xo.XF c, GenOf Xo c y t → ∀ σ : Sp R ⟶ Sp o, jK R ≫ σ = y ≫ pullback.snd _ _ ≫ spMap b → ∃ ξ : Sp R ⟶ PSpace o n, jK R ≫ ξ = y ≫ f ∧ ξ ≫ PSpace.str o n = σ := by
  first | exact @GlobalTheory.UMin.ExtP.extend_theta | exact GlobalTheory.UMin.ExtP.extend_theta | (intros; apply GlobalTheory.UMin.ExtP.extend_theta <;> assumption)
end
