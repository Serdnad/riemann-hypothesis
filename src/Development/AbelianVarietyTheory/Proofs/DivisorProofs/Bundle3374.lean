module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3311
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3092
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1402
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2982
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1541
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1626
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1224
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1404
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1466
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3301
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3284
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2995
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3337
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3302
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3368
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3310
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3370
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureStalkFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2640
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3290
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle078
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3369
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefUpper

theorem log_ncard_smallSec {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p) :
    Real.log (P.L.smallSec.ncard : ℝ) = P.lc 1 0 1 := by
  have h := SmallBall.encard_eq_Bl P (Pair.rep_base k X p P).1 P.L.smallSec 1 zero_le_one fun u => by
    simp only [HermLB.smallSec, Set.mem_setOf_eq, one_pow]
  unfold Pair.lc
  rw [Set.ncard_def, Set.ncard_def, h]

theorem main : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L N : HermLB p) (a : ℝ), L.IsNef D → L.IsSelfInter a →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
      Real.log (((L.pow m).tens N).smallSec.ncard : ℝ) ≤ (a / (D + 1).factorial + ε) * (m : ℝ) ^ (D + 1) := by
  intro HC HA HS k _ X _ p D hX L N a hL ha ε hε
  obtain ⟨⟨x, hx⟩, -⟩ := GlobalTheory.T.isTranscendenceBasis_functionField_arithmeticVariety k X p D hX
  obtain ⟨H, hNH, hbox⟩ := GlobalTheory.T.exists_twist_nef_squarefree_monomials_small HC k X p D hX N x
  set G := N.tens H with hG

  have hnef : ∀ m : ℕ, ((L.pow m).tens G).IsNef D := fun m =>
    GlobalTheory.T.hermLineBundle_isNef_tens HC k X p D hX _ _ (GlobalTheory.NefPow.isNef_pow HC k X p D hX L m hL) hNH
  obtain ⟨α, hα, hαlim⟩ := GlobalTheory.SelfInterGrowth.main HC k X p D hX L G a ha
  have hα0 : ∀ m, 0 ≤ α m := fun m => by
    obtain ⟨h, Hh, e⟩ := hα m
    rw [← e]
    exact (GlobalTheory.T.arithKleiman_heightNef_of_isNef HC HA HS k X p D hX _ (hnef m)).2 h Hh _
  have hg0 : ∀ m, 0 ≤ gdeg ((L.pow m).tens G) D := fun m =>
    GlobalTheory.T.hermLineBundleGeometricDegree_nonneg_of_semiPos k X p D hX _ (hnef m).semiPos
  have hglim := GlobalTheory.T.tendsto_hermLineBundleGeometricDegree_pow_tens_div_pow HC k X p D hX L G
  refine GlobalTheory.T.eventually_le_of_smallSectionLogCountUpperBound D (fun m => Real.log (((L.pow m).tens N).smallSec.ncard : ℝ)) α
    (fun m => gdeg ((L.pow m).tens G) D) a (gdeg L D) hα0 hg0 hαlim hglim (fun m q hq => ?_) ε hε
  obtain ⟨P, hPL, hPA, hPbox⟩ := hbox ((L.pow m).tens N)
  have hiso : (P.L.tens P.A).Isometric ((L.pow m).tens G) := by
    rw [hPL, hPA]
    exact HermLB.isometric_tens_assoc _ _ _
  have T := GlobalTheory.T.hermitianLineBundle_positivity_preserved_isometric HC k X p D hX _ _ hiso.symm
  have hb := GlobalTheory.T.arith_log_small_sections_upper_bound HC HA HS k X p D hX P x (α m) q hx.1 hPbox (T.2.1 (hnef m)) (T.2.2.2.1 _ (hα m)) hq
  rw [hiso.gdeg_eq, ← log_ncard_smallSec] at hb
  have e : Real.log (P.L.smallSec.ncard : ℝ) = Real.log (((L.pow m).tens N).smallSec.ncard : ℝ) := by
    rw [hPL]
  simpa only [e] using hb

end GlobalTheory.NefUpper
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

theorem exists_finExt_evenCP_of_factor_extLam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ₁ : R →+* R₁) (G₁ : Over (Sp R₁)) [GrpObj G₁] [IsCommMonObj G₁] (β₁ : G₁.left ⟶ G.left) (β₁₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R₁))) (gen₁ : (Over.pullback (jK R₁)).obj G₁ ≅ A₁.A), FinExt ρ₁ → IsGrpPullback G₁ G (spMap ρ₁) β₁ → Geo.Tor.IsSquare β₁ β₁₂ → IsMonHom gen₁.hom → ExtLam G₁ (A₁.L.pull gen₁.hom.left) (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull β₁₂) → ∃ (R₉ : Type) (_ : CommRing R₉) (_ : IsDomain R₉) (_ : IsLocalRing R₉) (ρ₉ : R →+* R₉) (G₉ : Over (Sp R₉)) (_ : GrpObj G₉) (_ : IsCommMonObj G₉) (β₉ : G₉.left ⟶ G.left) (β₉₂ : (G2 G₉).left ⟶ (G2 G).left) (P₉ : GlobalTheory.UU.CP G₉) (A₉ : PolAV (Sp (FractionRing R₉))) (gen₉ : (Over.pullback (jK R₉)).obj G₉ ≅ A₉.A), FinExt ρ₉ ∧ IsGrpPullback G₉ G (spMap ρ₉) β₉ ∧ Geo.Tor.IsSquare β₉ β₉₂ ∧ IsSemiAbelian G₉ ∧ LBIso (abelian₂ G₉ P₉.L.L) ((abelian₂ G' U'.LG.L).pull (β₉₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) ∧ EvenOn P₉ ∧ IsMonHom gen₉.hom ∧ LBIso (A₉.L.pull gen₉.hom.left) (P₉.L.L.pull (pullback.fst G₉.hom (jK R₉))) := by
  intro R _ _ _ hR D D' F A' G' _ _ hG' U' oA oG hOL G _ _ hG inc pr hinc hpr hip hpi R₁ _ _ _ ρ₁ G₁ _ _ β₁ β₁₂ A₁ gen₁ hρ₁ hβ₁ hsq₁ hgen₁ hE
  obtain ⟨R₂, _, _, _, ρ₂, D₂, D₂', F₂, A₂', G₂', _, _, U₂', oA₂, oG₂, G₂, _, _, inc₂, pr₂, β₂, β₂₂, A₂, gen₂, W, _, _, _,
    φ, GW, _, _, βW, DW, AW, UW, κ, hρ₂, hR₂, hG₂', hOL₂, hG₂, hinc₂, hpr₂, hip₂, hpi₂, hβ₂, hsq₂, hgen₂, hE₂, hPP₂,
    hW, hφ, hφl, hβW, hκ, hUW⟩ :=
    GlobalTheory.T.exists_finiteExtension_idempotentFactor_trait_unif R hR D D' F A' G' hG' U' oA oG hOL G hG inc pr hinc hpr hip hpi R₁ ρ₁ G₁ β₁ β₁₂ A₁ gen₁ hρ₁ hβ₁ hsq₁ hgen₁ hE
  obtain ⟨R₃, _, _, _, ρ₃, G₃, _, _, β₃, κ₃, L₃, hρ₃, hβ₃, hκ₃, hL₃, hL₃iso⟩ :=
    GlobalTheory.T.exists_finiteExtension_symmBundle_extension_on_factor R₂ hR₂ D₂ D₂' F₂ A₂' G₂' hG₂' U₂' oA₂ oG₂ hOL₂ G₂ hG₂ inc₂ pr₂ hinc₂ hpr₂ hip₂ hpi₂ A₂ gen₂ hgen₂ hE₂
      W hW φ hφ hφl GW βW DW AW UW κ hβW hκ hUW
  obtain ⟨R₉, _, _, _, ρ, G₉, _, _, β₉, β₉₂, P, A₉, gen₉, hρ, hβ₉, hsq₉, hG₉, hlam, hev, hgen₉, hiso₉⟩ :=
    GlobalTheory.T.exists_evenCubicalStructure_of_genericPolarisation_extension R₂ hR₂ G₂ hG₂ A₂ gen₂ hgen₂ _ hE₂ W φ GW βW DW AW UW κ hW hφ hφl hβW hκ hUW R₃ ρ₃ G₃ β₃ κ₃ L₃ hρ₃ hβ₃ hκ₃
      hL₃ hL₃iso
  have hΛ : (abelian₂ G' U'.LG.L).IsLB := LB.isLB_linComb U'.LG.isLB _ _
  have hΛ₂ : (abelian₂ G₂' U₂'.LG.L).IsLB := LB.isLB_linComb U₂'.LG.isLB _ _
  refine ⟨R₉, inferInstance, inferInstance, inferInstance, ρ.comp ρ₂, G₉, inferInstance, inferInstance, β₉ ≫ β₂,
    β₉₂ ≫ β₂₂, P, A₉, gen₉, ⟨hρ.1, hρ.2.1.comp hρ₂.2.1, hρ.2.2.comp hρ₂.2.2⟩, ?_, ?_, hG₉, ?_, hev, hgen₉, hiso₉⟩
  · rw [spMap_comp]
    exact hβ₉.comp hβ₂
  · exact ⟨by rw [Category.assoc, hsq₂.1, ← Category.assoc, hsq₉.1, Category.assoc],
      by rw [Category.assoc, hsq₂.2, ← Category.assoc, hsq₉.2, Category.assoc]⟩
  · have a := GlobalTheory.GenSpread.lbIso_pullback hPP₂ β₉₂
    have b := GlobalTheory.GenSpread.lbIso_pull_pull (pull_isLB hΛ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left) β₉₂ (a' := β₉₂ ≫ β₂₂) rfl
    have c := GlobalTheory.GenSpread.lbIso_pull_pull hΛ (β₉₂ ≫ β₂₂)
      (a' := (β₉₂ ≫ β₂₂) ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left) rfl
    have hL : (abelian₂ G₉ P.L.L).IsLB := LB.isLB_linComb P.L.isLB _ _
    refine LBIso.trans hL (pull_isLB (pull_isLB hΛ₂ _) _) (pull_isLB hΛ _) hlam ?_
    refine LBIso.trans (pull_isLB (pull_isLB hΛ₂ _) _) (pull_isLB (pull_isLB (pull_isLB hΛ _) _) _) (pull_isLB hΛ _) a ?_
    refine LBIso.trans (pull_isLB (pull_isLB (pull_isLB hΛ _) _) _) (pull_isLB (pull_isLB hΛ _) _) (pull_isLB hΛ _)
      (LBIso.symm b) (LBIso.symm c)

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.PoincDown

theorem exists_assoc_pow {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V']
    [IsDiscreteValuationRing V'] (f : V →+* V') (hf : Function.Injective f) [IsLocalHom f] {ϖ : V} (hϖ : Irreducible ϖ)
    {ϖ' : V'} (hϖ' : Irreducible ϖ') : ∃ m : ℕ, 1 ≤ m ∧ Associated (f ϖ) (ϖ' ^ m) := by
  have h0 : f ϖ ≠ 0 := fun h => hϖ.ne_zero (hf (by rw [h, map_zero]))
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible h0 hϖ'
  refine ⟨m, Nat.one_le_iff_ne_zero.2 fun e => ?_, hm⟩
  subst e
  rw [pow_zero] at hm
  exact hϖ.not_isUnit ((isUnit_map_iff f ϖ).1 (associated_one_iff_isUnit.1 hm))

theorem map_eq_span_pow {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V']
    [IsDiscreteValuationRing V'] (f : V →+* V') {ϖ : V} (hϖ : Irreducible ϖ) {ϖ' : V'} (hϖ' : Irreducible ϖ') {m : ℕ}
    (hm : Associated (f ϖ) (ϖ' ^ m)) {I : Ideal V} {b : ℕ} (h : I.map f = Ideal.span {ϖ' ^ b}) :
    ∃ a : ℕ, b = m * a ∧ I = Ideal.span {ϖ ^ a} := by
  have hI : I ≠ ⊥ := by
    rintro rfl
    rw [Ideal.map_bot, eq_comm, Ideal.span_singleton_eq_bot] at h
    exact pow_ne_zero _ hϖ'.ne_zero h
  obtain ⟨a, rfl⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hϖ
  refine ⟨a, ?_, rfl⟩
  rw [Ideal.map_span, Set.image_singleton, map_pow, Ideal.span_singleton_eq_span_singleton] at h
  have h2 : Associated (ϖ' ^ (m * a)) (ϖ' ^ b) := by
    rw [pow_mul]; exact (hm.pow_pow (n := a)).symm.trans h
  have e1 := (pow_dvd_pow_iff hϖ'.ne_zero hϖ'.not_isUnit).1 h2.dvd
  have e2 := (pow_dvd_pow_iff hϖ'.ne_zero hϖ'.not_isUnit).1 h2.symm.dvd
  omega

theorem idealDescent : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ W : Set Z, IsClopen W → IsIrreducible W → ∀ (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι → Set.range X₁.π = W → (∀ x ∈ J₁.support, X₁.π x ∉ Set.range i) → (∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong J₁ ξ₁ = Ideal.span {T.ϖ ^ a}) → ∃ (d : ℕ) (J : Z.IdealSheafData), 1 ≤ d ∧ (∀ x ∈ J.support, x ∈ W ∧ x ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ : Sp T.V ⟶ Z), jK T.V ≫ ξ = T.y ≫ i → ξ (closedPoint T.V) ∈ W → ∃ a : ℕ, (a : ℝ) = d * φ.evalZ T.β ∧ idlAlong J ξ = Ideal.span {T.ϖ ^ a} := by
  intro g n hg hn hodd F Z z i hZ φ hφ W hWc hWi W8 X₁ ι J₁ hι hπ hsupp hord
  obtain ⟨k, J, hk, hJs, hJo⟩ := GlobalTheory.T.norm_descent_ideal_thetaModel_to_clopen_component g n hg hn hodd F Z z i hZ φ hφ W hWc hWi W8 X₁ ι J₁ hι hπ hsupp hord
  refine ⟨k * ι, J, Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), hJs, ?_⟩
  intro T ξ hξ hW
  have hc : IsClopen (Set.range X₁.π) := by rw [hπ]; exact hWc
  obtain ⟨T', f, fK, ξ₁, hf, hfl, hfK, hy, hsq, hgen⟩ := GlobalTheory.T.exists_trait_lift_thetaSetup_model_after_extension g n F Z i W8 X₁ hc T ξ hξ (by rw [hπ]; exact hW)
  obtain ⟨a₁, ha₁, hJ₁⟩ := hord T' ξ₁ hgen
  have hJ := hJo T' ξ₁ hgen
  obtain ⟨m, hm1, hm⟩ := exists_assoc_pow f hf T.irr T'.irr
  have hφ' := GlobalTheory.Poinc.TraitRam.evalZ_eq_mul g n _ _ (by omega) (cycBase (show n ≠ 0 by omega)).ζ.isUnit F T T' f fK hf hfl hfK hy m hm φ hφ
  have e1 : (idlAlong J ξ).map f = Ideal.span {T'.ϖ ^ (a₁ * k)} := by
    rw [← GlobalTheory.TraitOrder.idlAlong_comp, hsq, hJ, hJ₁, Ideal.span_singleton_pow, ← pow_mul]
  obtain ⟨a, hb, ha⟩ := map_eq_span_pow f T.irr T'.irr hm e1
  refine ⟨a, ?_, ha⟩
  have hb' : ((a₁ : ℝ) * k) = m * a := by exact_mod_cast hb
  rw [ha₁, hφ'] at hb'
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  push_cast
  apply mul_left_cancel₀ hm0.ne'
  linarith [hb']

end GlobalTheory.PoincDown
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical


theorem _root_.GlobalTheory.T.traitOrders_effectiveCartier_extend_from_generic : ∀ (g n : ℕ), 3 ≤ n → ∀ (F : SFam g n (zetaAway n)) (φ : InvFun ℤ), IsPolFan id g φ → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SharpOver F W ρ.P u → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → ∀ (D : GlobalTheory.EffCartierData M.Z) (ι : ℕ), (∀ z ∈ D.idealSheaf.support, z ∉ V) → (∀ (T : Trait F) (ξ : Sp T.V ⟶ M.Z) (γ : Ω →+* FractionRing T.V), jK T.V ≫ ξ = spMap γ ≫ M.pt → T.y = spMap γ ≫ spMap S.R.val.toRingHom ≫ u → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a}) → ∀ (T : Trait F) (ξ : Sp T.V ⟶ M.Z), ThroughU M V v (𝟙 F.X) T ξ → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a} := by
  first | exact @GlobalTheory.Poinc.Extend.orders_extend | exact GlobalTheory.Poinc.Extend.orders_extend | (intros; apply GlobalTheory.Poinc.Extend.orders_extend <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep.ConjFib

theorem isGrpPullback_self {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have ey : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [ex, ey, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

end GlobalTheory.Poinc.Sep.ConjFib


open GlobalTheory.Poinc.Sep.ConjFib in
theorem GlobalTheory.Poinc.Sep.conj_fibre_iso : ∀ (g l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) → ∀ (Q : Data V), Q.g ≤ g → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (o' : Type) [CommRing o'] (ζ' : o') (g' n' : ℕ) (F' : SFam g' n' ζ') (lam : Sp V ⟶ F'.X) (β : Q.B.left ⟶ F'.univ.A.left) (β₂ : (G2 Q.B).left ⟶ (G2 F'.univ.A).left), 1 ≤ n' → DefOver k₀ (spMap (ev.comp ρ) ≫ lam ≫ F'.s) → IsGrpPullback Q.B F'.univ.A lam β → IsSquare β β₂ → LBIso (abelian₂ Q.B Q.M.L) (F'.univ.P.pull β₂) → ∀ (φ₀₂ : (G2 ((Over.pullback (spMap (ev.comp ρ))).obj Q.B)).left ⟶ (G2 F'.univ.A).left), IsSquare (pullback.fst Q.B.hom (spMap (ev.comp ρ)) ≫ β) φ₀₂ → ∀ (σ : K ≃+* K), (∀ r ∈ k₀, σ r = r) → ∀ (a : Q.X) (p : Sp K ⟶ ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left), p ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) = spMap (ev.comp ρ) ≫ (Q.c a).left → p ≫ pullback.snd Q.B.hom (spMap (ev.comp ρ)) = 𝟙 _ → ∃ (x' : Sp K ⟶ F'.X) (φ : ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left ⟶ F'.univ.A.left) (φ₂ : (G2 ((Over.pullback (spMap (ev.comp ρ))).obj Q.B)).left ⟶ (G2 F'.univ.A).left), x' ≫ F'.s = spMap (ev.comp ρ) ≫ lam ≫ F'.s ∧ IsGrpPullback ((Over.pullback (spMap (ev.comp ρ))).obj Q.B) F'.univ.A x' φ ∧ IsSquare φ φ₂ ∧ LBIso (F'.univ.P.pull φ₀₂) (F'.univ.P.pull φ₂) ∧ spMap σ.toRingHom ≫ p ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) ≫ β = p ≫ φ := by
  intro g l hl hlo W hW
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.polarisedAbelianPart_fibre_conjugate_iso_mumford g l hl hlo W hW
  refine ⟨j₀, ?_⟩
  intro j hj V V₁ _ _ _ _ _ hCN hlu Q hQg ρ hρ D e hSh C u mo hmo hTh K _ _ ev k₀ hk₀ hu o' _ ζ' g' n' F' lam β β₂ hn' hdef hpb hsq hLB φ₀₂ hsq0 σ hσ a p hpf hps
  obtain ⟨f, f₂, hf, hfs, hfL, hfp⟩ :=
    hj₀ j hj V V₁ hCN hlu Q hQg ρ hρ D e hSh C u mo hmo hTh K ev k₀ hk₀ hu σ hσ a p hpf hps
  obtain ⟨hpbσ, φσ₂, hsqσ⟩ := GlobalTheory.T.isGrpPullback_baseChange_with_square F'.univ.A Q.B lam β hpb (spMap (σ.toRingHom.comp (ev.comp ρ)))
  obtain ⟨-, ψ₀, hψ₀⟩ := GlobalTheory.T.isGrpPullback_baseChange_with_square Q.B Q.B (𝟙 _) (𝟙 _) (isGrpPullback_self Q.B) (spMap (ev.comp ρ))
  obtain ⟨-, ψσ, hψσ⟩ := GlobalTheory.T.isGrpPullback_baseChange_with_square Q.B Q.B (𝟙 _) (𝟙 _) (isGrpPullback_self Q.B)
    (spMap (σ.toRingHom.comp (ev.comp ρ)))
  rw [Category.comp_id] at hψ₀ hψσ
  refine ⟨spMap (σ.toRingHom.comp (ev.comp ρ)) ≫ lam, f ≫ pullback.fst Q.B.hom _ ≫ β, f₂ ≫ φσ₂, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨P₀, hP₀⟩ := hdef
    have hk : (σ.toRingHom).comp k₀.subtype = k₀.subtype := by
      ext r; exact hσ r r.2
    have hk' : spMap σ.toRingHom ≫ spMap k₀.subtype = spMap k₀.subtype := by
      rw [← spMap_comp', hk]
    rw [spMap_comp' (ev.comp ρ) σ.toRingHom]
    simp only [Category.assoc]
    rw [← hP₀, ← Category.assoc, hk']
  · simpa only [Category.id_comp] using hf.comp hpbσ
  · exact ⟨by rw [Category.assoc, hsqσ.1, ← Category.assoc, hfs.1, Category.assoc],
      by rw [Category.assoc, hsqσ.2, ← Category.assoc, hfs.2, Category.assoc]⟩
  · have e0 : φ₀₂ = ψ₀ ≫ β₂ := by
      apply pullback.hom_ext
      · change φ₀₂ ≫ (fst F'.univ.A F'.univ.A).left = (ψ₀ ≫ β₂) ≫ (fst F'.univ.A F'.univ.A).left
        rw [hsq0.1, Category.assoc, hsq.1, ← Category.assoc ψ₀, hψ₀.1, Category.assoc]
      · change φ₀₂ ≫ (snd F'.univ.A F'.univ.A).left = (ψ₀ ≫ β₂) ≫ (snd F'.univ.A F'.univ.A).left
        rw [hsq0.2, Category.assoc, hsq.2, ← Category.assoc ψ₀, hψ₀.2, Category.assoc]
    have eσ : φσ₂ = ψσ ≫ β₂ := by
      apply pullback.hom_ext
      · change φσ₂ ≫ (fst F'.univ.A F'.univ.A).left = (ψσ ≫ β₂) ≫ (fst F'.univ.A F'.univ.A).left
        rw [hsqσ.1, Category.assoc, hsq.1, ← Category.assoc ψσ, hψσ.1, Category.assoc]
      · change φσ₂ ≫ (snd F'.univ.A F'.univ.A).left = (ψσ ≫ β₂) ≫ (snd F'.univ.A F'.univ.A).left
        rw [hsqσ.2, Category.assoc, hsq.2, ← Category.assoc ψσ, hψσ.2, Category.assoc]
    have hP := F'.univ.isLB
    have hΛ : (abelian₂ Q.B Q.M.L).IsLB := LB.isLB_linComb (RigLB.isLB Q.M) _ _
    have hA := GlobalTheory.GenSpread.lbIso_pull_of_lbIso hLB ψ₀ (a' := ψ₀ ≫ β₂) rfl
    have hB := GlobalTheory.GenSpread.lbIso_pull_of_lbIso hLB (f₂ ≫ ψσ) (a' := f₂ ≫ φσ₂) (by rw [eσ, Category.assoc])
    rw [e0]
    exact LBIso.trans (pull_isLB hP _) (pull_isLB hΛ _) (pull_isLB hP _) (LBIso.symm hA)
      (LBIso.trans (pull_isLB hΛ _) (pull_isLB hΛ _) (pull_isLB hP _) (hfL ψ₀ ψσ hψ₀ hψσ) hB)
  · have h5 := congrArg (· ≫ β) hfp
    simp only [Category.assoc] at h5
    exact h5.symm
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_labelled_uniformisedModel_thetaSystem_trait : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (ε : Matrix (Fin 8) (Fin 8) ℤ → (ρ.P.A ⟶ ρ.P.A)) (u' : Sp S.R ⟶ F.X), IsDiagEnd F W ρ.P u' ε → ∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (T : Trait F) (ι : FractionRing T.V →+* PadicAlgCl p), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))) → spMap y₀ ≫ u' = spMap ι ≫ T.y → (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∃ (u : ρ.UTest p y₀) (l : u.Lab) (j : u.D.toPre.X ≃+ (Fin 8 → T.D.toPre.X)), (∀ χ, l.q χ = -Real.log ‖ι (algebraMap T.V (FractionRing T.V) T.ϖ)‖ * ((qW W T.β (j χ) : ℤ) : ℝ)) ∧ ∀ (m : ℕ) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) m) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (E : Matrix (Fin 8) (Fin 8) ℤ), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk' x' → x'.left ≫ u.φ = x.left ≫ u.φ ≫ (ε E).left → CongMod m (j pk'.y) (fun a => ∑ b, E a b • j pk.y b) := by
  first | exact @GlobalTheory.Poinc.traitLabels | exact GlobalTheory.Poinc.traitLabels | (intros; apply GlobalTheory.Poinc.traitLabels <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.exists_secs_of_intFam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D), (∃ j₀ : ℕ, ∀ j ≥ j₀, ∃ Φ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → SecK C.P.L.L C.α (C.n ^ j), ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ F) F) ∧ ∀ F₁ : IntFam (maximalIdeal R) D.toPre 1, ∃ θ : SecK C.P.L.L C.α 1, ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, T.Exp 1 u θ F₁ :=
  GlobalTheory.Mum.SecsDesc.assemble GlobalTheory.T.exists_map_thetaExpansion_all_traits GlobalTheory.T.exists_origin_normalisation_unit_at_traits GlobalTheory.T.exists_thetaSection_normalised_unit_at_traits
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.GalLab

theorem eq_of_classSum_approx {X K : Type} [AddCommGroup X] [NormedAddCommGroup K] (m : ℕ) (τ : X → K) (ν ν' : X)
    (h : CongMod m ν ν') (u v : K)
    (hu : ∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset X, ∀ S : Finset X, (∀ μ ∈ S, CongMod m μ ν) →
      (∀ μ ∈ S₀, CongMod m μ ν → μ ∈ S) → ‖u - ∑ μ ∈ S, τ μ‖ ≤ δ)
    (hv : ∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset X, ∀ S : Finset X, (∀ μ ∈ S, CongMod m μ ν') →
      (∀ μ ∈ S₀, CongMod m μ ν' → μ ∈ S) → ‖v - ∑ μ ∈ S, τ μ‖ ≤ δ) : u = v := by
  obtain ⟨w, hw⟩ := h
  have key : ∀ μ, CongMod m μ ν ↔ CongMod m μ ν' := fun μ =>
    ⟨fun ⟨x, hx⟩ => ⟨w + x, by rw [hx, hw, smul_add, add_assoc]⟩,
      fun ⟨x, hx⟩ => ⟨x - w, by rw [hx, hw, smul_sub]; abel⟩⟩
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  obtain ⟨S₀, h₀⟩ := hu (δ / 2) (half_pos hδ)
  obtain ⟨S₁, h₁⟩ := hv (δ / 2) (half_pos hδ)
  have a := h₀ ((S₀ ∪ S₁).filter fun μ => CongMod m μ ν) (fun μ hμ => (Finset.mem_filter.1 hμ).2)
    fun μ hμ hc => Finset.mem_filter.2 ⟨Finset.mem_union_left _ hμ, hc⟩
  have b := h₁ ((S₀ ∪ S₁).filter fun μ => CongMod m μ ν) (fun μ hμ => (key μ).1 (Finset.mem_filter.1 hμ).2)
    fun μ hμ hc => Finset.mem_filter.2 ⟨Finset.mem_union_right _ hμ, (key μ).2 hc⟩
  have c := norm_sub_le_norm_sub_add_norm_sub u (∑ μ ∈ (S₀ ∪ S₁).filter fun μ => CongMod m μ ν, τ μ) v
  rw [norm_sub_rev] at b
  linarith

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X₁ : USetup C) (D : UDeep X₁) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∀ (f : D.X.S.Gam → X₁.S.HH X₁.M z₁ → D.X.Ω₁) (t : ∀ (ct : UCTrait X₁ p z₁) (_ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), ct.T.P.D.toPre.X → X₁.S.HH X₁.M z₁ → PadicAlgCl p), (∀ a κ (z' : D.X.M.Z), D.q z' = z₁ → f a κ ∈ D.X.M.O z') → (∀ (ct : UCTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), UIsLab X₁ ct yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X, UIsLab D.X (D.lift ct y h) yy → D.Compat yy₁ yy → ∀ a ν κ, yy a = QuotientAddGroup.mk ν → ∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset ct.T.P.D.toPre.X, ∀ S : Finset ct.T.P.D.toPre.X, (∀ μ ∈ S, CongMod D.m μ ν) → (∀ μ ∈ S₀, CongMod D.m μ ν → μ ∈ S) → ‖D.X.M.val (gPt p ≫ y) (f a κ) - ∑ μ ∈ S, t ct yy₁ μ κ‖ ≤ δ) → ∀ (w₁ : UWit X₁) (w₂ : UWit D.X), D.Comparison₂ w₁ w₂ → IsProjOver D.X.M.s → ∀ (σ' : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁) (s : D.X.M.Z ⟶ D.X.M.Z), s ≫ D.q = D.q → (∀ (K : Type) [Field K] (y : Sp K ⟶ D.X.M.Z) (b : D.X.Ω₁), D.X.M.val (y ≫ s) b = D.X.M.val y (σ' b)) → s z₂ = z₂ → ∀ aσ : D.X.S.Gam ≃+ D.X.S.Gam, (∀ (ct : UCTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), UIsLab X₁ ct yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y) (h' : (y ≫ s) ≫ D.q = ct.y) (yy yy' : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X), UIsLab D.X (D.lift ct y h) yy → D.Compat yy₁ yy → UIsLab D.X (D.lift ct (y ≫ s) h') yy' → D.Compat yy₁ yy' → ∀ x, yy' x = yy (aσ x)) → ∀ (ct₀ : UCTrait D.X p z₂) (yy₀ : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct₀.T.P.D.toPre.X), UIsLabW D.X w₂ ct₀ yy₀ → ∀ (a a' : D.X.S.Gam) (ν ν' : ct₀.T.P.D.toPre.X), yy₀ (aσ a) = QuotientAddGroup.mk ν → yy₀ a' = QuotientAddGroup.mk ν' → CongMod D.m ν ν' → ∀ κ, σ' (f a κ) = f a' κ := by
  intro E _ _ _ H Dw hpq l Xo cf C X₁ D p _ z₁ z₂ hz f t hf hsum w₁ w₂ htie hproj σ' s hs hval hsz aσ haσ ct₀ yy₀ hl₀
    a a' ν ν' ha ha' hνν' κ
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme D.X.M.Z :=
    fun x => ⟨D.X.normal.isDomain_stalk x, D.X.normal.isIntegrallyClosed_stalk x⟩
  have hσ : σ' (f a κ) ∈ D.X.M.O z₂ := by
    letI : Algebra (X₁.M.Z.presheaf.stalk z₁) D.X.Ω₁ :=
      ((algebraMap X₁.Ω₁ D.X.Ω₁).comp (X₁.M.stalkHom z₁)).toAlgebra
    have halg : ∀ x, algebraMap (X₁.M.Z.presheaf.stalk z₁) D.X.Ω₁ x =
      algebraMap X₁.Ω₁ D.X.Ω₁ (X₁.M.stalkHom z₁ x) := fun _ => rfl
    let φ : D.X.Ω₁ →ₐ[X₁.M.Z.presheaf.stalk z₁] D.X.Ω₁ :=
      { (σ' : D.X.Ω₁ →+* D.X.Ω₁) with commutes' := fun x => σ'.commutes (X₁.M.stalkHom z₁ x) }
    exact FinPts.mem_O_of_isIntegral hN D.gen halg
      ((FinPts.isIntegral_of_mem_O D.fin D.gen halg (hf a κ)).map φ) hz
  have hf' : f a' κ ∈ D.X.M.O z₂ := hf a' κ z₂ hz
  obtain ⟨U₁, hU₁, hct⟩ := GlobalTheory.UPoinc.UCTraitEx.exists_uCTrait_of_open E H Dw hpq l Xo cf C X₁ p
  have hc₀ := ct₀.cen
  rw [← sub_eq_zero]
  refine eq_zero_of_val_cen_eq_zero _ _ D.X.M hN (D.q ⁻¹ᵁ U₁) (FinPts.preimage_nonempty D.gen hU₁) p ct₀.y _
    (by rw [hc₀]; exact sub_mem hσ hf') fun y hy => ?_
  obtain ⟨hy, hyU⟩ := hy
  rw [hc₀] at hy
  obtain ⟨ct₁, hct₁⟩ := hct (y ≫ D.q) (by
    rintro _ ⟨w, rfl⟩
    exact hyU ⟨w, rfl⟩)
  have hz₁ : (y ≫ D.q) (cPt p) = z₁ := by rw [← hz, ← hy]; rfl
  let ct : UCTrait X₁ p z₁ := { ct₁ with cen := ct₁.cen.trans hz₁ }
  have h : y ≫ D.q = ct.y := hct₁.symm
  have h' : (y ≫ s) ≫ D.q = ct.y := by rw [Category.assoc, hs, h]
  have hys : (y ≫ s) (cPt p) = z₂ := by
    show s (y (cPt p)) = z₂
    rw [hy, hsz]
  obtain ⟨yy₁, hl₁⟩ := GlobalTheory.T.exists_labels_unitaryClassicalTrait E H Dw hpq l Xo cf C X₁ w₁ p z₁ ct
  obtain ⟨yy, hl, hco⟩ := GlobalTheory.T.unitary_trait_labels_extend_to_deeper_level E H Dw hpq l Xo cf C X₁ D w₁ w₂ htie p z₁ ct yy₁ hl₁ y h
  obtain ⟨yy', hl', hco'⟩ := GlobalTheory.T.unitary_trait_labels_extend_to_deeper_level E H Dw hpq l Xo cf C X₁ D w₁ w₂ htie p z₁ ct yy₁ hl₁ (y ≫ s) h'
  have hyy := haσ ct yy₁ hl₁.uIsLab y h h' yy yy' hl.uIsLab hco hl'.uIsLab hco'
  let ct₂ : UCTrait D.X p z₂ := { D.lift ct y h with cen := hy }
  obtain ⟨d, hd⟩ := exists_linearEquiv_labelled_of_uIsLabW E H Dw hpq l Xo cf C D.X w₂ hproj p z₂ ct₀ ct₂ yy₀ yy
    hl₀ hl
  have hdν : CongMod D.m (d ν) (d ν') := by
    obtain ⟨w, hw⟩ := hνν'
    exact ⟨d w, by rw [hw, map_add (f := _), map_nsmul]⟩
  have e := eq_of_classSum_approx D.m (fun μ => t ct yy₁ μ κ) _ _ hdν _ _
    (hsum ct yy₁ hl₁.uIsLab (y ≫ s) h' hys yy' hl'.uIsLab hco' a (d ν) κ ((hyy a).trans (hd _ _ ha)))
    (hsum ct yy₁ hl₁.uIsLab y h hy yy hl.uIsLab hco a' (d ν') κ (hd _ _ ha'))
  rw [← Category.assoc, hval] at e
  have hsp : ∀ w, (gPt p ≫ y) w ⤳ z₂ := RatModel.gPt_specializes hy
  have e' := map_sub (RatModel.valHomOf _ z₂ hsp) ⟨_, hσ⟩ ⟨_, hf'⟩
  exact e'.trans (sub_eq_zero.2 e)

end GlobalTheory.UPoinc.GalLab
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.canonicalFamily_base_injections_agree : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], GlobalTheory.Mum.Base R' → ∀ θ₁ θ₂ : R →+* R', Function.Injective θ₁ → Function.Injective θ₂ → IsLocalHom θ₁ → IsLocalHom θ₂ → ∀ κ₁ κ₂ : Sp (FractionRing R') ⟶ Sp (FractionRing R), κ₁ ≫ jK R = jK R' ≫ spMap θ₁ → κ₂ ≫ jK R = jK R' ≫ spMap θ₂ → κ₁ ≫ C.y = κ₂ ≫ C.y → θ₁.comp (Cn.ψ.comp MvPolynomial.C) = θ₂.comp (Cn.ψ.comp MvPolynomial.C) := by
  first | exact @GlobalTheory.UCanon.injBase | exact GlobalTheory.UCanon.injBase | (intros; apply GlobalTheory.UCanon.injBase <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep


theorem _root_.GlobalTheory.T.twistedSum_zeta_power_residue_dividing_label : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : Y1 → C → V1, 𝔪1.Terms x₀ lab T → ∀ (c : C), lab c ∈ X₁.S.supI X₁.M z₁ → ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ (sg : ℤˣ) (e : ℕ), GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪1 lab T sg c τ e → ∀ s u : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ s = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ e) → X₁.M.stalkHom z₁ u = X₁.S.th (lab c + τ) / X₁.S.th (lab c) → ev1 (s * u) - 1 ∈ maximalIdeal V1 := by
  first | exact @GlobalTheory.GSep.TwistResid.twist_resid | exact GlobalTheory.GSep.TwistResid.twist_resid | (intros; apply GlobalTheory.GSep.TwistResid.twist_resid <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical


theorem _root_.GlobalTheory.T.unitaryTrait_lifts_to_thetaSetup_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C), IsClopen (Set.range X₁.π) → ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ C.Z), T.y ≫ C.i = jK T.V ≫ ξ → ξ (closedPoint T.V) ∈ Set.range X₁.π → ∃ (T' : UTrait Xo c) (f : T.V →+* T'.V) (fK : FractionRing T.V →+* FractionRing T'.V) (ξ₁ : Sp T'.V ⟶ X₁.M.Z), Function.Injective f ∧ IsLocalHom f ∧ (∀ a, fK (algebraMap T.V (FractionRing T.V) a) = algebraMap T'.V (FractionRing T'.V) (f a)) ∧ T'.y = spMap fK ≫ T.y ∧ spMap f ≫ ξ = ξ₁ ≫ X₁.π ∧ T'.y ≫ C.i = jK T'.V ≫ ξ₁ ≫ X₁.π := by
  first | exact @GlobalTheory.UPoinc.uTraitLift_setup | exact GlobalTheory.UPoinc.uTraitLift_setup | (intros; apply GlobalTheory.UPoinc.uTraitLift_setup <;> assumption)
end
