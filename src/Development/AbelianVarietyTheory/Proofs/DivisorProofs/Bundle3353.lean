module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle536
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3233
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle011
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle673
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle595
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle581
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeQuotientByFiniteTranslations
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle698
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle643
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle597
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle621
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle656
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3323
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3331
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1399
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2230
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3347
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle061
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2464
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2278
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2527
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

theorem _root_.GlobalTheory.T.exists_fixedPullbackHomScheme_of_sectionBases : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Rigidified A L → Rigidified B M → RelAmple A L → 1 ≤ k → VeryAmpleAt B M k → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow A L (k : ℤ) (overRes (T := baseOver (Sp Rg)) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) ⊤).left) (b' : Fin m → LB.Sec (LPow A L (k : ℤ) (baseAt t))), (∀ i, IsPullSec A L (k : ℤ) (homAt t ▷ A) (whiskerRight_snd (homAt t) A) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) = ⊤) → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow B M (k : ℤ) (overRes (T := baseOver (Sp Rg)) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) ⊤).left) (b' : Fin m → LB.Sec (LPow B M (k : ℤ) (baseAt t))), (∀ i, IsPullSec B M (k : ℤ) (homAt t ▷ B) (whiskerRight_snd (homAt t) B) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec B (b' i) : SecM B M (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec B (b' i) : SecM B M (k : ℤ) (baseAt t))) = ⊤) → ∃ R : HomFixRep A B L M, QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  first | (exact @GlobalTheory.HomFixGlob.exists_homFixRep_of_secBases) | (exact GlobalTheory.HomFixGlob.exists_homFixRep_of_secBases) | (intros; apply GlobalTheory.HomFixGlob.exists_homFixRep_of_secBases  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_finiteExtension_trait_uniformisingMumfordBundle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ : R →+* R₂), FinExt ρ ∧ ∀ (G₂ : Over (Sp R₂)) [GrpObj G₂] [IsCommMonObj G₂] (β : G₂.left ⟶ G.left) (β₂ : (G2 G₂).left ⟶ (G2 G).left), IsGrpPullback G₂ G (spMap ρ) β → Geo.Tor.IsSquare β β₂ → ∃ (A₂ : PolAV (Sp (FractionRing R₂))) (gen₂ : ((Over.pullback (jK R₂)).obj G₂) ≅ A₂.A) (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R₂ →+* W) (GW : Over (Sp W)) (_ : GrpObj GW) (_ : IsCommMonObj GW) (βW : GW.left ⟶ G₂.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW) (κ : pullback GW.hom (jK W) ⟶ pullback G₂.hom (jK R₂)), IsMonHom gen₂.hom ∧ ExtLam G₂ (A₂.L.pull gen₂.hom.left) (PP.pull β₂) ∧ GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ IsGrpPullback GW G₂ (spMap φ) βW ∧ κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW ∧ LBIso (UW.LG.L.pull (pullback.fst GW.hom (jK W))) ((A₂.L.pull gen₂.hom.left).pull κ) := by
  first | exact @GlobalTheory.Mum.exists_finExt_trait_unif_lam | exact GlobalTheory.Mum.exists_finExt_trait_unif_lam | (intros; apply GlobalTheory.Mum.exists_finExt_trait_unif_lam <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumSec

def zeroSec {X : Scheme.{0}} (L : LB X) : LB.Sec L where
  f := fun _ => 0
  compat := fun _ _ => by simp

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∃ N : ℕ, 1 ≤ N ∧ ∃ S : ∀ k : ℕ, H0 U.LG.L k → H0 U.LG.L (N * k), (∀ (k e : ℕ) (s₁ s₂ : H0 U.LG.L k), SecRatioEq U.LG.L ((b e).left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left s₁ s₂ (S k s₁) (S k s₂)) ∧ (∀ k : ℕ, 3 ≤ k → ∃ s₀ : H0 U.LG.L k, SecCoNonzero U.LG.L ((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left s₀ (S k s₀)) := by
  intro R _ _ _ hB D A G _ _ hG U a a' h h' hE b hb
  obtain ⟨N, hN, hP⟩ := GlobalTheory.T.mumfordSections_multiplier_thickenings R hB D A G hG U a a' h h' hE b hb
  classical
  let S : ∀ k : ℕ, H0 U.LG.L k → H0 U.LG.L (N * k) := fun k =>
    if hk : 3 ≤ k then (hP k hk).choose else fun _ => zeroSec _
  refine ⟨N, hN, S, ?_, ?_⟩
  · intro k e s₁ s₂ i i'
    by_cases hk : 3 ≤ k
    · obtain ⟨c, hc, -⟩ := (hP k hk).choose_spec
      have e1 := hc e s₁ i i'
      have e2 := hc e s₂ i i'
      have hS : S k = (hP k hk).choose := dif_pos hk
      rw [hS, e1, e2]
      ring
    · have hS : S k = fun _ => zeroSec _ := dif_neg hk
      rw [hS]
      dsimp only [zeroSec]
      erw [map_zero, map_zero]
      simp only [map_zero, mul_zero]
  · intro k hk
    obtain ⟨c, hc, y, ⟨i', hi'⟩, hy⟩ := (hP k hk).choose_spec
    obtain ⟨s₀, i, hs⟩ := GlobalTheory.T.exists_section_nonvanishing_closedFibre_of_three_le R hB D A G hG U k hk ((b 0).left.base y)
    have hu : y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen
        ((((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left).app (secChart U.LG.L i)).hom (s₀.f i)) := by
      have h1 : y ∈ (b 0).left ⁻¹ᵁ (thickObj R (maximalIdeal R) 0 G).left.basicOpen
          (((fstG (maximalIdeal R) 0 G).left.app (secChart U.LG.L i)).hom (s₀.f i)) := hs
      rw [Scheme.preimage_basicOpen] at h1
      exact h1
    have hyW : y ∈ ((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) ⁻¹ᵁ secChart U.LG.L i ⊓
        (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart U.LG.L i' :=
      ⟨Scheme.basicOpen_le _ _ hu, hi'⟩
    have hS : S k = (hP k hk).choose := dif_pos hk
    refine ⟨s₀, y, i, i', hu, ?_⟩
    rw [hS]
    have key := hc 0 s₀ i i'
    have hprod : y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen (c 0 i i' *
        ((thickObj R (maximalIdeal R) 0 G).left.presheaf.map (homOfLE (inf_le_left :
          ((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) ⁻¹ᵁ secChart U.LG.L i ⊓
            (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart U.LG.L i' ≤
            ((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) ⁻¹ᵁ secChart U.LG.L i)).op).hom
          ((((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left).app (secChart U.LG.L i)).hom (s₀.f i))) := by
      rw [Scheme.basicOpen_mul, Scheme.basicOpen_res]
      exact ⟨hy i i' hyW, hyW, hu⟩
    rw [← key, Scheme.basicOpen_res] at hprod
    exact hprod.2

end GlobalTheory.MumSec
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTTors

theorem isIsogDeg_of_geomFibres (S : Scheme.{0}) (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) (φ : A ⟶ A)
    (d : ℕ) (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S),
      GlobalTheory.IwLevel.IsIsogDeg ((Over.pullback t).map φ) d) : GlobalTheory.IwLevel.IsIsogDeg φ d := by
  have := hA.smooth
  have hfin : IsFinite φ.left := GlobalTheory.T.abelianScheme_endomorphism_finite_of_geometric_fibres S A hA φ fun k _ _ t => (h k t).fin
  have hflat : Flat φ.left :=
    GlobalTheory.T.flat_of_finite_flat_geometric_fibres_over_base S A A φ inferInstance inferInstance inferInstance hfin fun k _ _ t => (h k t).flat
  refine ⟨hfin, hflat, GlobalTheory.AbLaw.MulN.surjective_of_geomFibres φ fun k _ _ t => (h k t).surj, fun y => ?_⟩
  let K := AlgebraicClosure (A.left.residueField y)
  let u : Sp K ⟶ A.left := spMap (algebraMap (A.left.residueField y) K) ≫ A.left.fromSpecResidueField y
  let t := u ≫ A.hom
  let q : Sp K := (⊥ : PrimeSpectrum K)
  let v : Sp K ⟶ pullback A.hom t := pullback.lift u (𝟙 _) (by simp [t])
  have hP := GlobalTheory.AbLaw.MulN.isPullback_baseChange t φ
  have e := Scheme.Hom.finrank_of_isPullback _ _ _ _ hP (v q)
  have hv : pullback.fst A.hom t (v q) = y := by
    rw [← Scheme.Hom.comp_apply]
    have : v ≫ pullback.fst A.hom t = u := pullback.lift_fst _ _ _
    rw [this]
    exact (Scheme.Hom.comp_apply _ _ q).trans (Scheme.fromSpecResidueField_apply y _)
  rw [hv] at e
  rw [← e]
  exact (h K t).rank _

theorem isIsogDeg_fibre (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A] (hA : IsAbelianScheme A)
    (F : Type) [Field F] [NumberField F] (ρ : OAct (𝓞 F) A) (l d : ℕ) (hl : l.Prime) (hl0 : (l : k) ≠ 0)
    (hcard : Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ A // x ^ l = 1} = l ^ (d * Module.finrank ℚ F))
    (c : 𝓞 F) (hc : c ≠ 0) : GlobalTheory.IwLevel.IsIsogDeg (ρ.act c) ((Algebra.norm ℤ c).natAbs ^ d) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.T.isFinite_and_finrank_act_eq_norm_pow k A hA F ρ l d hl hl0 hcard c hc
  exact GlobalTheory.T.isogeny_degree_of_fibre_rank k A hA _ (ρ.hom c) h1 _ h2

def pullAct {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {S : Scheme.{0}} {A : Over S} [GrpObj A]
    [IsCommMonObj A] (act : GlobalTheory.UPel.HT.OActN D.O A) {T : Scheme.{0}} (t : T ⟶ S) :
    OAct (𝓞 D.F) ((Over.pullback t).obj A) where
  act c := (Over.pullback t).map (act.act (algebraMap (𝓞 D.F) D.O c))
  hom c := by have := act.hom (algebraMap (𝓞 D.F) D.O c); infer_instance
  one := by rw [map_one, act.one, CategoryTheory.Functor.map_id]
  mul a b := by rw [mul_comm a b, map_mul, act.mul, Functor.map_comp]
  add a b := by
    rw [map_add (f := _), act.add]
    exact map_mul (Over.pullback t).homMonoidHom _ _

theorem isIsogDeg_intAct : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s) (c : 𝓞 D.F),
    c ≠ 0 → GlobalTheory.IwLevel.IsIsogDeg (o.act.act (algebraMap (𝓞 D.F) D.O c)) ((Algebra.norm ℤ c).natAbs ^ (D.m * D.n)) := by
  intro p _ D R _ b N S s o c hc
  refine isIsogDeg_of_geomFibres S o.A o.ab _ _ fun k _ _ t => ?_
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (t ≫ s)
  have hβ : t ≫ s = spMap φ.hom := by rw [← hφ]; rfl
  obtain ⟨I, -⟩ := o.geom k t φ.hom hβ
  obtain ⟨l, hlp, hl⟩ := Nat.exists_infinite_primes (p + 1)
  have hlp' : l ≠ p := by omega
  have hcop : l.Coprime p := (Nat.coprime_primes hl (Fact.out)).2 hlp'
  have hl0 : (l : k) ≠ 0 := by
    have := (b.unit l hcop).map φ.hom
    rw [map_natCast] at this
    exact this.ne_zero
  have hcount := GlobalTheory.T.card_lTorsion_eq_pow_of_tateSimilitude p D k _ _ _ I l hl hlp'
  let e := GlobalTheory.TorsionLift.ptsEquiv t o.A (𝟙_ (Over (Sp k))) t (Category.id_comp t)
  have hc2 : Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ (Over.pullback t).obj o.A // x ^ l = 1} =
      l ^ ((D.m * D.n) * Module.finrank ℚ D.F) := by
    rw [← hcount]
    refine Nat.card_congr (e.toEquiv.subtypeEquiv fun x => ?_)
    show x ^ l = 1 ↔ e x ^ l = 1
    rw [← map_pow, map_eq_one_iff e e.injective]
  exact isIsogDeg_fibre k _ (GlobalTheory.isAbelianScheme_pullback_obj t o.A o.ab) D.F (pullAct o.act t) l _ hl hl0 hc2 c hc

end GlobalTheory.HTTors
end
end

section

noncomputable section

namespace GlobalTheory.UPel.HT.Hecke

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem exists_isHecke : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∃ (o' : Obj b N s) (ψ : o.A ⟶ o'.A), IsHecke g c k N o o' ψ := by
  intro p _ D R _ b g c k N hc hk hN hNp hEF hg hck S s o
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hk; exact (Fact.out : p.Prime).one_lt.ne' hk)
  have hN0 : 0 < N := by omega
  obtain ⟨hfin, hfree⟩ := GlobalTheory.UPel.HT.Hecke.heckeSub_finite_free p D R b g k N hk0 hN0 hk hNp S s o
  obtain ⟨A', _, _, ψ, hA', hψ, hgal⟩ := GlobalTheory.TranslQuotient.exists_quotient S o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left)
    (heckeSub o g N) o.ab (pull_isLB o.isLB _) o.ample hfin hfree
  have hepi : Epi ψ := by
    have := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover hgal
    exact (Over.forget S).epi_of_epi_map this
  have kill : ∀ h ∈ heckeSub o g N, h ≫ ψ = 1 := fun h hh =>
    comp_eq_one_of_transl ψ h (hgal.inv ⟨h, hh⟩)
  have stab : ∀ c' : D.O, ∀ h ∈ heckeSub o g N, h ≫ o.act.act c' ∈ heckeSub o g N := by
    rintro c' _ ⟨x, rfl⟩
    refine ⟨c' • x, ?_⟩
    rw [← o.eta_lin, map_smul, smul_comm]
  choose actf hactf using fun c' : D.O => GlobalTheory.UPel.HT.Hecke.exists_desc_endo S o.A A' (heckeSub o g N) ψ hψ hgal (o.act.act c') (o.act.hom c') (stab c')
  let act' : OActN D.O A' :=
    { act := actf
      hom := fun c' => (hactf c').1
      one := by
        rw [← cancel_epi ψ, (hactf 1).2, o.act.one, Category.id_comp, Category.comp_id]
      mul := fun b' c' => by
        rw [← cancel_epi ψ, (hactf _).2, o.act.mul, Category.assoc, ← (hactf b').2, ← Category.assoc,
          ← (hactf c').2, Category.assoc]
      add := fun b' c' => by
        rw [← cancel_epi ψ, (hactf _).2, o.act.add, mul_comp, comp_mul, (hactf _).2, (hactf _).2] }
  have hcomp : ∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ act'.act c' := fun c' => ((hactf c').2).symm
  obtain ⟨P', hP', r1, r2, hsym, hamp, hker, hros, hpull⟩ :=
    GlobalTheory.T.exists_hecke_translate_polarisation_bundle p D R b g c k N hc hk hN hNp hEF hg hck S s o A' act' ψ hA' hψ hgal hcomp
  obtain ⟨hlie, hlieR⟩ := GlobalTheory.UPel.HT.EtaleLie.lie_of_etale p D R b (N * k) S s o A' act' ψ _ _ hA' hψ hgal hcomp
  have hgeom := GlobalTheory.T.exists_tateSimilitude_hecke_translate_geometric p D R b g c k N hc hk hN hNp hEF hg hck S s o A' act' ψ hA' hψ hgal hcomp P' hP' r1 r2 hpull
  let o' : Obj b N s :=
    { A := A'
      ab := hA'
      act := act'
      P := P'
      isLB := hP'
      rig₁ := r1
      rig₂ := r2
      symm := hsym
      ample := hamp
      kerP := hker
      rosati := hros
      lie := hlie
      lieRank := hlieR
      eta := fun x => o.eta (g x) ≫ ψ
      eta_add := fun x y => by rw [map_add (f := _), o.eta_add, mul_comp]
      eta_lin := fun c' x => by
        show o.eta (g (c' • x)) ≫ ψ = (o.eta (g x) ≫ ψ) ≫ act'.act c'
        rw [map_smul, o.eta_lin, Category.assoc, hcomp, Category.assoc]
      eta_ker := fun x => by rw [map_nsmul]; exact kill _ (mem_heckeSub o g N x)
      geom := hgeom }
  exact ⟨o', ψ, hψ, hcomp, fun x => rfl, hgal, ⟨hpull⟩, hck⟩

end GlobalTheory.UPel.HT.Hecke
end
end

section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu.CharpolyAV

section Rho

variable {p : ℕ} [Fact p.Prime] (T : Theory p) {k : Type} [Field k] [CharP k p] [PerfectRing k p]
  {A : AbVar k} {G : PDivGroup p k} (t : G.TorsionTower A.X)

def rho : End A →+ Module.End (WittVector p k) (T.M G) :=
  AddMonoidHom.mk' (fun g => T.map (t.map t g.asHom.hom)) fun g h => by
    have hfun := base_functor_props p (fun _ _ _ => True) T.base k G G G trivial trivial trivial
    haveI : IsMonHom (g.asHom.hom * h.asHom.hom) := inferInstanceAs (IsMonHom (g + h).asHom.hom)
    show T.map (t.map t (g.asHom.hom * h.asHom.hom)) = _
    rw [TorsionTower.map_mul]
    exact hfun.2.2.1 _ _

theorem rho_apply (g : End A) : rho T t g = T.map (t.map t g.asHom.hom) := rfl

theorem rho_pow (f : End A) (n : ℕ) : rho T t (f ^ n) = rho T t f ^ n := by
  have hfun := base_functor_props p (fun _ _ _ => True) T.base k G G G trivial trivial trivial
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, rho_apply]
    show T.map (t.map t (𝟙 A.X)) = _
    rw [TorsionTower.map_id]
    exact hfun.1
  | succ n ih =>
    rw [pow_succ, pow_succ', ← ih, rho_apply, rho_apply, rho_apply]
    show T.map (t.map t (f.asHom.hom ≫ (f ^ n).asHom.hom)) = _
    rw [TorsionTower.map_comp t t t]
    exact hfun.2.1 _ _

theorem rho_aeval (f : End A) (R : Polynomial ℤ) :
    rho T t (Polynomial.aeval f R) = Polynomial.aeval (rho T t f) R := by
  induction R using Polynomial.induction_on' with
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, eq_intCast (algebraMap ℤ (End A)),
      eq_intCast (algebraMap ℤ (Module.End (WittVector p k) (T.M G))), ← zsmul_eq_mul, ← zsmul_eq_mul, map_zsmul, rho_pow]

end Rho

theorem charpoly_map_eq : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (A : AbVar k) (G : PDivGroup p k) (t : G.TorsionTower A.X)
    [Module.Free (WittVector p k) (T.M G)] [Module.Finite (WittVector p k) (T.M G)] (f : End A),
    (T.map (t.map t f.asHom.hom)).charpoly = (GlobalTheory.AV.AbVar.charpoly f).map (Int.castRingHom (WittVector p k)) := by
  intro p _ T k _ _ _ A G t _ _ f
  have hfun := base_functor_props p (fun _ _ _ => True) T.base k G G G trivial trivial trivial
  have hFc : ∀ (g : End A) (x : T.M G), T.map (t.map t g.asHom.hom) (T.F G x) = T.F G (T.map (t.map t g.asHom.hom) x) :=
    fun g x => hfun.2.2.2.2.2.2.1 _ x
  have hFinj : Function.Injective (T.F G) := (GlobalTheory.T.dieudonneTheory_V_eq_verschiebung_injective p T k G).1
  let ψ : ℤ_[p] →+* WittVector p k :=
    (WittVector.map (ZMod.castHom (dvd_refl p) k)).comp (WittVector.equiv p).symm.toRingHom
  have hψ : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    rw [PadicInt.unitCoeff_spec hx0, map_mul, map_pow, map_natCast] at hx
    have hu : IsUnit (ψ (PadicInt.unitCoeff hx0 : ℤ_[p])) := (Units.isUnit _).map ψ
    have hpn : ((p : WittVector p k)) ^ x.valuation ≠ 0 := pow_ne_zero _ (WittVector.p_nonzero p k)
    exact hpn ((hu.mul_right_eq_zero).1 hx)
  have hrank : Module.finrank (WittVector p k) (T.M G) = 2 * A.dim :=
    hfun.2.2.2.2.2.2.2.1.trans ((GlobalTheory.T.exists_torsionTower_and_height_eq_two_dim p k A).2 G t)
  obtain ⟨P, hPm, hP⟩ := GlobalTheory.T.exists_padicInt_charpoly_commute_frobeniusSemilinear p k (T.M G) (T.F G) ψ (T.map (t.map t f.asHom.hom)) hFinj (hFc f)
  obtain ⟨⟨hQm, hQdeg, -⟩, -⟩ := GlobalTheory.T.abelianVarietyEndCharpoly_spec k A f
  have hPdeg : P.natDegree = 2 * A.dim := by
    rw [← hPm.natDegree_map ψ, hP, LinearMap.charpoly_natDegree, hrank]
  have key : P.map (algebraMap ℤ_[p] ℚ_[p]) = (charpoly f).map (Int.castRingHom ℚ_[p]) := by
    refine GlobalTheory.T.eq_of_norm_prod_aeval_eq' p _ _ (hPm.map _) (hQm.map _) ?_ ?_
    · rw [hPm.natDegree_map, hQm.natDegree_map, hPdeg, hQdeg]
    · intro R
      obtain ⟨PR, -, hPR⟩ := GlobalTheory.T.exists_padicInt_charpoly_commute_frobeniusSemilinear p k (T.M G) (T.F G) ψ
        (T.map (t.map t (Polynomial.aeval f R).asHom.hom)) hFinj (hFc _)
      set d : ℤ_[p] := (-1) ^ Module.finrank (WittVector p k) (T.M G) * PR.coeff 0 with hd_def
      have hd : LinearMap.det (T.map (t.map t (Polynomial.aeval f R).asHom.hom)) = ψ d := by
        rw [LinearMap.det_eq_sign_charpoly_coeff, ← hPR, Polynomial.coeff_map, hd_def, map_mul, map_pow,
          map_neg, map_one]
      have habs := GlobalTheory.Dieu.AbsDet.norm_det_eq_norm_deg p T k A G t ψ (Polynomial.aeval f R) d hd
      have hd' : LinearMap.det (Polynomial.aeval (T.map (t.map t f.asHom.hom)) R) = ψ d := by
        rw [← hd]; exact congrArg LinearMap.det (rho_aeval T t f R).symm
      rw [GlobalTheory.T.prod_aeval_padicRoots_charpoly_eq_det p (WittVector p k) (T.M G) ψ _ P R d hψ hP hd']
      have hQ : (charpoly f).map (Int.castRingHom ℚ_[p]) =
          ((charpoly f).map (Int.castRingHom ℚ)).map (algebraMap ℚ ℚ_[p]) := by
        rw [Polynomial.map_map]; congr 1 <;> exact RingHom.ext_int _ _
      have h2 := GlobalTheory.T.deg_aeval_end_eq_prod_aroots k A f (PadicAlgCl p) R
      rw [hQ, Polynomial.aroots_map]
      erw [← h2]
      rw [PadicAlgCl.norm_extends, map_natCast, ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends]
      rw [PadicInt.padic_norm_e_of_padicInt, habs]
      rw [← PadicInt.padic_norm_e_of_padicInt]; push_cast; rfl
  have hP' : P = (charpoly f).map (Int.castRingHom ℤ_[p]) := by
    apply Polynomial.map_injective (algebraMap ℤ_[p] ℚ_[p]) (IsFractionRing.injective ℤ_[p] ℚ_[p])
    rw [key, Polynomial.map_map]; congr 1 <;> exact RingHom.ext_int _ _
  rw [← hP, hP', Polynomial.map_map]; congr 1 <;> exact RingHom.ext_int _ _

end GlobalTheory.Dieu.CharpolyAV
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.nef_hermitian_small_sections_key_inequality : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (B : HermLB p) (β : ℝ), B.IsNef D → B.IsSelfInter β → ∀ (x : Fin D → X.functionField) (Δ : ℝ), AlgebraicIndependent ℤ x → 0 < Δ → ∀ (J : Type) [Fintype J] [Nonempty J] (e : J → X.functionField) (n : J → ℕ), LinearIndependent ℤ e → SmallFam B (boxFam e x) (fun c => n c.1 * Δ) → ((D + 1).factorial : ℝ) * Δ * ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ β + ((D : ℝ) + 1) * (Δ + D * Real.log 2 / 2 + Real.log (Fintype.card J) / 2) * gdeg B D := by
  first | exact @GlobalTheory.HSNefCore.key_ineq | exact GlobalTheory.HSNefCore.key_ineq | (intros; apply GlobalTheory.HSNefCore.key_ineq <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.mixedHeightInduction_symmetric_firstTwo : ArchInteg → ArchRecip → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 + 1 : ℕ) → ∀ T, IsMix q (e + 1) T → ∀ (M N : HermLB q) (L : Fin e → HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r) (r' : N.B.ι → Y.functionFieldˣ) (hr' : IsRatSec N.B r'), recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) M hr = recVal (T (e + 1) (Fin.cons M L)) (Fin.cons M L : Fin (e + 1) → HermLB q) N hr' := by
  first | exact @GlobalTheory.MixHt.VSwap.main | exact GlobalTheory.MixHt.VSwap.main | (intros; apply GlobalTheory.MixHt.VSwap.main <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.mixedHeightRecursiveValue_well_defined : ArchInteg → ArchRecip → ∀ m : ℕ, (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∃ T, IsMix q m T) → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsAmb p → ∀ T, IsMix p m T → ∀ (x : X), HasDim x (m + 1) → ∀ (M : HermLB p) (L : Fin m → HermLB p), ∃ v : ℝ, ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (i : Y ⟶ X) [IsClosedImmersion i] (hi : i ≫ p = q), i (genericPoint Y) = x → ∀ (M' : HermLB q) (L' : Fin m → HermLB q), (M.pull i hi).Isometric M' → (∀ a, ((L a).pull i hi).Isometric (L' a)) → ∀ (r : M'.B.ι → Y.functionFieldˣ) (hr : IsRatSec M'.B r), v = recVal (fun z => T m L (i z)) L' M' hr := by
  first | exact @GlobalTheory.MixHt.StepVal.step_val | exact GlobalTheory.MixHt.StepVal.step_val | (intros; apply GlobalTheory.MixHt.StepVal.step_val <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory

theorem connectedness_at_normal_point :
    GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Z : Closeds X), η ≠ 0 → 0 < m → Z ≠ ⊤ → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (s : Y ⟶ X) (_ : IsDominant s) (K : CartierDiv Y) (B : Closeds Y), IsLogRes p n η m G s K B ∧ (∀ y, s y ∈ Z → y ∈ B) ∧ ∀ (y : X) (σ : Y), IsIntegrallyClosed (X.presheaf.stalk y) → (∀ z, z ⤳ y → ∀ E : DivOver p, E.IsAt z → ∀ g, G.IsEqn z g → discrep E η m g ≤ 0) → (pullCart s G - m • K).mult σ = m → s σ ⤳ y → (∀ v w : Y, v ≠ σ → v ⤳ w → σ ⤳ w → s w ⤳ y → (pullCart s G - m • K).mult v < m) → ∀ v : Y, v ≠ σ → s v ⤳ y → (pullCart s G - m • K).mult v < m := by
  intro hP X _ _ p n hp hdim η m G Z hη hm hZ
  obtain ⟨Y, hYi, hYn, s, hs, K, B, F, N, hres, hB, hF, hvan⟩ :=
    GlobalTheory.T.exists_logResolution_localVanishing hP X p n hp hdim η m G Z hη hm hZ
  refine ⟨Y, hYi, hYn, s, hs, K, B, hres, hB, ?_⟩
  intro y σ hy hdisc hσ hσy hloc
  exact GlobalTheory.T.logResolution_mult_lt_of_connectedness X p n hp hdim η m G N Y s K B F hη hm hres hF hvan y σ hy hdisc hσ hσy hloc

end GlobalTheory
end
