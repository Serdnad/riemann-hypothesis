module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.TorsionZeroCountTwist
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle100
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle078
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle093
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle094
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFormCorrection
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfVeryAmpleBy
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle043
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle045
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle047
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle046
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IntegralFamilyPrescribedTermUnitAtPrime
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_h1Vanishes_generated_pullbackPow_tensor_dual : ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (W X : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of S)) (H : LB X) (a b : W ⟶ X) (n : ℕ) (s : Fin (n + 1) → LB.Sec (H.pull a)), H.IsLB → VeryAmpleBy f (H.pull a) s → ∃ t₀ : ℤ, ∀ t, t₀ ≤ t → (∀ (W₁ : Scheme.{0}) (σ : W ⟶ W₁) (a₁ b₁ : W₁ ⟶ X), σ ≫ a₁ = a → σ ≫ b₁ = b → FirstCohomologyVanishes ((LB.LinComb H (K := Fin 2) ![a₁, b₁] ![t, -1]).pull σ)) ∧ ∃ (m : ℕ) (u : Fin (m + 1) → LB.Sec (LB.LinComb H (K := Fin 2) ![a, b] ![t, -1])), ⨆ i, nonzeroLocus (u i) = ⊤ := by
  first | exact @GlobalTheory.TwistPair.twist_pair | exact GlobalTheory.TwistPair.twist_pair | (intros; apply GlobalTheory.TwistPair.twist_pair <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Unif

theorem exists_gen_of_thick : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : Over (Spec (CommRingCat.of R))), Smooth Y.hom → IsProjBy Y.hom → ∀ (W : Scheme.{0}) (L : LB W) (K : Type) [Fintype K] (φ : K → (Y.left ⟶ W)) (ε : K → ℤ) (φ' : ∀ e, K → ((thickObj R I e Y).left ⟶ W)), L.IsLB → (∀ e k, pullback.fst Y.hom (thick R I e) ≫ φ k = φ' e k) → ∀ f : ∀ e, LB.Gen (LB.LinComb L (φ' e) ε), (∀ e, (f e).IsGen) → (∀ e z J, Good L z J → val (f (e + 1)) (thickMap R I e Y) z J = val (f e) (𝟙 _) z J) → ∃ u : LB.Gen (LB.LinComb L φ ε), u.IsGen ∧ ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e Y).left) (z : Z) (J), Good L z J → val u (r ≫ pullback.fst Y.hom (thick R I e)) z J = val (f e) r z J := by
  intro R _ _ I hI Y hs hp W L K _ φ ε φ' hL hφ f hf hc
  obtain ⟨s, hsv⟩ := GlobalTheory.T.exists_section_linearCombination_of_compatible_thickenings R I hI Y hs hp W L K φ ε φ' hL hφ (fun e => genSec (f e) (hf e))
    (fun e z J hJ => (sval_genSec _ _ _ z hJ).trans
      ((congrArg Units.val (hc e z J hJ)).trans (sval_genSec _ _ _ z hJ).symm))
  have : IsProper Y.hom := GlobalTheory.AbLaw.isProper_of_isProjBy _ _ _ hp
  have top : nonzeroLocus s = ⊤ :=
    eq_top_of_special_part R I (IsAdicComplete.le_jacobson_bot I) Y _ fun z => by
      choose J hJ using fun ψ : (thickObj R I 0 Y).left ⟶ W => exists_chart hL (ψ z)
      have h1 := hsv 0 _ (𝟙 _) z J hJ
      rw [Category.id_comp, sval_genSec _ _ _ z hJ] at h1
      refine (TwistZero.mem_nonzeroLocus_iff s (pullback.fst Y.hom (thick R I 0)) z hJ).2 ?_
      exact (congrArg IsUnit h1).mpr (Units.isUnit _)
  have hu : ∀ j, IsUnit (s.f j) := fun j => Y.left.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    obtain ⟨J, hJ, e⟩ := sval_trans hL s y j hy
    exact (congrArg IsUnit ((gs_eq (𝟙 Y.left) y (LB.wchart L φ j) hy _).symm.trans e)).mpr
      ((Units.isUnit _).mul ((TwistZero.mem_nonzeroLocus_iff s (𝟙 _) y hJ).1 (by rw [top]; trivial)))
  refine ⟨⟨fun j => (hu j).unit⟩, fun i j => Units.ext (s.compat i j), fun e Z r z J hJ => Units.ext ?_⟩
  exact (gs_unit _ z _ (hJ.mem φ _) _).symm.trans ((hsv e Z r z J hJ).trans (sval_genSec _ _ r z hJ))

end GlobalTheory.Unif
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.descended_bundle_ample_special_fibre :
    type_of% @GlobalTheory.UU.AmpleZero.relAmple_zero :=
  @GlobalTheory.UU.AmpleZero.relAmple_zero
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.finite_exponent_base_change_field : GlobalFnsSt → AllPre fun {V} _ _ _ {_} {_} {_} _ _ U => ∀ k : ℕ, U.FE (Kbar V) k → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F], U.FE F k := by
  first | exact @GlobalTheory.UU.FEDesc.fe_of_fe_kbar | exact GlobalTheory.UU.FEDesc.fe_of_fe_kbar | (intros; apply GlobalTheory.UU.FEDesc.fe_of_fe_kbar <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.nonempty_mumfordTorusQuotientTower : (AllSet fun s => Nonempty (Tower s)) := by
  first | exact @GlobalTheory.UU.TowerEx.nonempty_tower | exact GlobalTheory.UU.TowerEx.nonempty_tower | (intros; apply GlobalTheory.UU.TowerEx.nonempty_tower <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.ExpansionClause

theorem expBij_of_match : Laws → Laws2 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : PreU (IsLocalRing.maximalIdeal V) D.toPre A G) (U' : UnifPre (IsLocalRing.maximalIdeal V) D A G), Match U U' → ∀ k : ℕ, 1 ≤ k → U.FE (FractionRing V) k → (∀ s : Fam D.toPre (FractionRing V) k, ∃ t, U.ExpF (FractionRing V) k t s.s) → U'.ExpBij k := by
  intro h1 h2 V _ _ _ hV D A G _ _ U U' hM k hk hFE hsurj
  have hT : U'.SecK k = LB.Sec (LB.LinComb U.P.L.L (K := Fin 1) (fun _ => pullback.fst G.hom (jK V)) (fun _ => (k : ℤ))) := by
    unfold UnifPre.SecK
    rw [hM.LG]
  have hK := GlobalTheory.GenericFibreSections.sameK_bijective V _ D.toPre A G U k
  have hu := GlobalTheory.T.fourierJacobiExpansion_overField_injective V hV D.toPre A G U (FractionRing V) k
  have ht := GlobalTheory.T.exists_fourierJacobi_expansion_over_field h1 h2 V hV D.toPre A G U (FractionRing V) k hk
  have e1 := GlobalTheory.T.valueExpansion_of_chartExpansion V _ D A G U U' hM k
  have e2 := GlobalTheory.T.chartExpansion_of_valueExpansion V _ D A G U U' hM k
  unfold UnifPre.ExpBij
  refine ⟨fun σ => ?_, fun s => ?_⟩
  · obtain ⟨t, hσt, -⟩ := hK.1 (cast hT σ)
    obtain ⟨s, hs⟩ := ht t
    refine ⟨⟨s, hFE t s hs⟩, e2 σ _ t _ (cast_heq hT σ).symm hσt hs, fun s' hs' => ?_⟩
    have h := (hu t t s'.s s (e1 σ _ t s' (cast_heq hT σ).symm hσt hs') hs).1 rfl
    obtain ⟨s', fe⟩ := s'
    cases h
    rfl
  · obtain ⟨t, hts⟩ := hsurj s
    obtain ⟨σ₀, hσt, huniq⟩ := hK.2 t
    refine ⟨cast hT.symm σ₀, e2 _ σ₀ t s (cast_heq hT.symm σ₀) hσt hts, fun σ hσ => ?_⟩
    obtain ⟨t', hσt', -⟩ := hK.1 (cast hT σ)
    have h := (hu t' t s.s s.s (e1 σ _ t' s (cast_heq hT σ).symm hσt' hσ) hts).2 rfl
    subst h
    rw [← huniq _ hσt']
    simp

end GlobalTheory.ExpansionClause
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU

theorem fe_one_of_psiRel : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → PsiRel D (𝟙_ _) f → U.FE (Kbar V) 1) := by
  intro h₁ h₂ V _ _ _ hV D A G _ _ U θ f hθ hψ t s hts
  obtain ⟨hp, hq⟩ := PullSec.pullEx V hV D A G U (Kbar V) (𝟙_ _) (toUnit _) 1
  obtain ⟨th, hth, -⟩ := hp θ
  obtain ⟨s₀, hs₀, -⟩ := hq f
  obtain ⟨c, hc⟩ := (GlobalTheory.T.expF_of_theta_degree_one h₁ h₂ V hV D A G U θ f hθ th s₀ hth hs₀).2.2 t s hts
  exact famFE_one_of_psiRel h₁.globalFns V D (Kbar V) s₀ s c (GlobalTheory.T.thetaPsiRelation_of_pullback_extension_field V D (Kbar V) f s₀ hs₀ hψ) hc

end GlobalTheory.UU
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.ThetaIntegral

theorem sval_eq_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) (J) : sval s r z J = 0 := by
  refine (congrArg (gs r z _) (h _)).trans ?_
  unfold gs
  split_ifs
  · exact (congrArg _ (map_zero _)).trans (map_zero _)
  · rfl

theorem exists_sec_ne_zero (h1 : Laws) (h2 : Laws2) (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (F : Type)
    [Field F] [IsAlgClosed F] (p : Spec (CommRingCat.of F) ⟶ S) :
    ∃ v : SecM P.A P.L ((1 : ℕ) : ℤ) (Over.mk p), v ≠ 0 := by
  obtain ⟨-, -, hr, -⟩ := GlobalTheory.ThetaRep.exists_projective_rep h1 h2 S P F p 1 (by simp)
  have : Nontrivial Γ((Over.mk p).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have : Nontrivial (SecM P.A P.L ((1 : ℕ) : ℤ) (Over.mk p)) :=
    Module.nontrivial_of_finrank_pos (R := Γ((Over.mk p).left, ⊤)) (by rw [hr]; simp)
  exact exists_ne 0

theorem exists_theta : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∃ θ f, U.Theta θ f) := by
  intro h1 h2 V _ _ _ hV D A G _ _ U
  obtain ⟨v, hv⟩ := exists_sec_ne_zero h1 h2 _ A (Kbar V) (jFK (R := V) (Kbar V))
  obtain ⟨s, n, c, σ, f, hE, hA, -⟩ := GlobalTheory.T.exists_fourierJacobi_expansion_over_field h1 h2 V hV D A G U (Kbar V) 1 le_rfl (SecM.toSec A.A v)
  by_contra hn
  have hz : ∀ i j, (σ i).f j = 0 := fun i j => by
    by_contra h
    exact hn ⟨σ i, f i, hE i, j, h⟩
  refine hv (Subtype.ext (funext fun j => ?_))
  refine sec_ext_val (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := V) (Kbar V)) A.A).left)
    (ε := fun _ => ((1 : ℕ) : ℤ)) A.isLB (s := SecM.toSec A.A v) (s' := SecM.toSec A.A 0) (fun z JA hJA => ?_) j
  obtain ⟨JG, hJG⟩ := exists_good_pt U.P.L.isLB z
  let y := (snd (TFK (R := V) (Kbar V)) A.A).left ≫ U.gen.inv.left
  let T : Over (Spec (CommRingCat.of V)) := Over.mk ((y ≫ pullback.fst G.hom (jK V)) ≫ G.hom)
  let x : T ⟶ G := Over.homMk (y ≫ pullback.fst G.hom (jK V)) rfl
  have e := hA _ (𝟙 _) y (lift (toUnit T) x).left
    (by rw [Category.id_comp, Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.comp_id])
    (congrArg (fun q => q.left) (lift_snd (toUnit T) x)) z JA JG hJA hJG
  rw [Finset.sum_eq_zero fun i _ => by rw [sval_eq_zero (σ i) (hz i), mul_zero], ← Units.val_pow_eq_pow_val,
    Units.mul_right_eq_zero] at e
  exact e.trans (sval_eq_zero _ (fun _ => rfl) _ _ _).symm

end GlobalTheory.ThetaIntegral
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU.ExpLinMap

theorem exists_linear_of_rel {F M X : Type} [Field F] [AddCommGroup M] [Module F M] {N : X → Type}
    [∀ α, AddCommGroup (N α)] [∀ α, Module F (N α)] (E : M → (∀ α, N α) → Prop)
    (tot : ∀ t, ∃ s, E t s) (uq : ∀ t t' s s', E t s → E t' s' → (t = t' ↔ s = s'))
    (lin : ∀ (c : F) t t' s s', E t s → E t' s' → E (c • t + t') (fun α => c • s α + s' α)) :
    ∃ ex : ∀ α, M →ₗ[F] N α, (∀ t, E t (fun α => ex α t)) ∧ (∀ t s, E t s → ∀ α, s α = ex α t) ∧
      (∀ t, (∀ α, ex α t = 0) → t = 0) ∧ ∀ α, ((∃ t s, E t s ∧ s α ≠ 0) ↔ ex α ≠ 0) := by
  choose e he using tot
  have hl : ∀ (c : F) t t' α, e (c • t + t') α = c • e t α + e t' α := fun c t t' α =>
    congrFun ((uq _ _ _ _ (he _) (lin c t t' _ _ (he t) (he t'))).1 rfl) α
  have h0 : ∀ α, e 0 α = 0 := fun α => by
    have h := hl 1 0 0 α
    simpa using h
  have hu : ∀ t s, E t s → ∀ α, s α = e t α := fun t s h α => congrFun ((uq _ _ _ _ h (he t)).1 rfl) α
  refine ⟨fun α => ⟨⟨fun t => e t α, fun t t' => ?_⟩, fun c t => ?_⟩, he, hu, fun t h => ?_, fun α => ⟨?_, fun h => ?_⟩⟩
  · simpa using hl 1 t t' α
  · simpa [h0] using hl c t 0 α
  · exact (uq _ _ _ _ (he t) (he 0)).2 (funext fun α => (h α).trans (h0 α).symm)
  · rintro ⟨t, s, h, hs⟩ hz
    exact hs ((hu t s h α).trans (LinearMap.congr_fun hz t))
  · by_contra hn
    refine h (LinearMap.ext fun t => ?_)
    by_contra ht
    exact hn ⟨t, e t, he t, ht⟩

theorem exists_expansion_linear : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∃ ex : ∀ α : D.X, EA A (jFK (R := V) F) k →ₗ[F] WB D F k α, (∀ t, U.ExpF F k t.sec (fun α => (ex α t).sec)) ∧ (∀ t s, U.ExpF F k t s → ∀ α, s α = (ex α (SecMod.mk _ t)).sec) ∧ (∀ t, (∀ α, ex α t = 0) → t = 0) ∧ ∀ α, (U.Supp F k α ↔ ex α ≠ 0)) := by
  intro h1 h2 V _ _ _ hV D A G _ _ U F _ _ k hk
  obtain ⟨ex, a, b, c, d⟩ := exists_linear_of_rel (F := F) (M := EA A (jFK (R := V) F) k) (N := fun α => WB D F k α)
    (fun t s => U.ExpF F k t.sec (fun α => (s α).sec))
    (fun t => GlobalTheory.T.exists_fourierJacobi_expansion_over_field h1 h2 V hV D A G U F k hk t.sec)
    (fun t t' s s' h h' => GlobalTheory.T.fourierJacobiExpansion_overField_injective V hV D A G U F k t.sec t'.sec _ _ h h')
    (fun c t t' s s' h h' => ExpLin.expF_linear V hV D A G U F k t.sec t'.sec _ _ _ _ c h h'
      (fun _ => rfl) (fun _ _ => rfl))
  refine ⟨ex, a, fun t s h α => b (SecMod.mk _ t) (fun α => SecMod.mk _ (s α)) h α, c, fun α => Iff.trans ?_ (d α)⟩
  constructor
  · rintro ⟨t, s, h, j, hj⟩
    exact ⟨SecMod.mk _ t, fun α => SecMod.mk _ (s α), h, fun hz => hj ((SecMod.eq_zero_iff_coord _).1 hz j)⟩
  · rintro ⟨t, s, h, hs⟩
    exact ⟨t.sec, fun α => (s α).sec, h, not_forall.1 fun hz => hs ((SecMod.eq_zero_iff_coord _).2 hz)⟩

end GlobalTheory.UU.ExpLinMap
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Unif.FormalEmb

open MvPolynomial GlobalTheory.Unif.PolyStep

variable {X X' : Scheme.{0}} {R : Type} [CommRing R] {σ : Type}

def vanIdeal (p : X ⟶ Spec (CommRingCat.of R)) {H : LB X} (s : σ → LB.Sec H) : Ideal (MvPolynomial σ R) :=
  ⨅ k : H.ι, RingHom.ker (eval₂Hom (AbLaw.cst p (H.U k)) (fun j => (s j).f k))

theorem mem_vanIdeal (p : X ⟶ Spec (CommRingCat.of R)) {H : LB X} (s : σ → LB.Sec H) (F : MvPolynomial σ R) :
    F ∈ vanIdeal p s ↔ ∀ k : H.ι, eval₂Hom (AbLaw.cst p (H.U k)) (fun j => (s j).f k) F = 0 := by
  simp only [vanIdeal, Ideal.mem_iInf, RingHom.mem_ker]

theorem mem_vanIdeal_of_sat (p : X ⟶ Spec (CommRingCat.of R)) {H : LB X} (s : σ → LB.Sec H)
    (hs : ⨆ i, nonzeroLocus (s i) = ⊤) {F : MvPolynomial σ R}
    (h : ∀ i, ∃ m : ℕ, MvPolynomial.X i ^ m * F ∈ vanIdeal p s) : F ∈ vanIdeal p s := by
  rw [mem_vanIdeal]
  intro k
  refine fn_ext fun y hy => ?_
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show y ∈ ⨆ i, nonzeroLocus (s i) by rw [hs]; trivial)
  obtain ⟨k', hk'⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
  have hy' : y ∈ H.U k' := X.basicOpen_le _ hk'
  have u' : IsUnit (gs (𝟙 X) y _ ((s i).f k')) := by
    rw [gs_eq (𝟙 X) y _ hy']
    exact (X.mem_basicOpen _ y hy').1 hk'
  have u : IsUnit (gs (𝟙 X) y _ ((s i).f k)) := by
    rw [gs_sec (s i) (𝟙 X) y hy hy']
    exact (Units.isUnit _).mul u'
  obtain ⟨m, hm⟩ := h i
  have e := congrArg (gsHom (𝟙 X) y _ hy) ((mem_vanIdeal p s _).1 hm k)
  rw [map_mul, map_pow, eval₂Hom_X', map_mul, map_pow, map_zero, gsHom_apply (𝟙 X) y _ hy,
    gsHom_apply (𝟙 X) y _ hy] at e
  rw [(u.pow m).mul_right_eq_zero.1 e, ← gsHom_apply (𝟙 X) y _ hy, map_zero]

theorem mem_vanIdeal_pull {H : LB X} {H' : LB X'} (hH : H.IsLB) {β : X' ⟶ X} {w : LB.Iso H' (H.pull β)}
    {s : σ → LB.Sec H} {s' : σ → LB.Sec H'} (h : ∀ j, Rel β w (s j) (s' j)) (p : X ⟶ Spec (CommRingCat.of R))
    {F : MvPolynomial σ R} {t : ℕ} (hF : F.IsHomogeneous t) (h0 : F ∈ vanIdeal p s) : F ∈ vanIdeal (β ≫ p) s' := by
  rw [mem_vanIdeal] at h0 ⊢
  intro k'
  refine fn_ext fun z hz => ?_
  obtain ⟨k, hk⟩ := exists_chart hH (β z)
  have e := Rel.form h p hF z k k' hk hz
  rw [h0 k, ← gsHom_apply β z _ hk, map_zero] at e
  rw [(Units.isUnit _).mul_right_eq_zero.1 e.symm, ← gsHom_apply (𝟙 X') z _ hz, map_zero]

theorem component_mem_span (S : Set (MvPolynomial σ R)) (hS : ∀ F ∈ S, ∃ t, F.IsHomogeneous t) :
    ∀ F ∈ Ideal.span S, ∀ t, homogeneousComponent t F ∈ Ideal.span S := by
  intro F hF t
  letI := MvPolynomial.gradedAlgebra (σ := σ) (R := R)
  have h := Ideal.homogeneous_span (homogeneousSubmodule σ R) S (fun F hF => hS F hF) t hF
  rwa [show (DirectSum.decompose (homogeneousSubmodule σ R) F t : MvPolynomial σ R) = homogeneousComponent t F from
    decomposition.decompose'_apply F t] at h

theorem exists_form_limit [Finite σ] (a : R) [IsAdicComplete (Ideal.span {a}) R] (K : ℕ → Ideal (MvPolynomial σ R))
    (t : ℕ) (h₁ : ∀ e F, F.IsHomogeneous t → F ∈ K (e + 1) → F ∈ K e) (h₂ : ∀ e, C (a ^ (e + 1)) ∈ K e)
    (h₃ : ∀ e F, F.IsHomogeneous t → F ∈ K e → ∃ G, G.IsHomogeneous t ∧ F - C (a ^ (e + 1)) * G ∈ K (e + 1))
    (e : ℕ) (F : MvPolynomial σ R) (hF : F.IsHomogeneous t) (h : F ∈ K e) :
    ∃ F₁ G : MvPolynomial σ R, F₁.IsHomogeneous t ∧ (∀ e', F₁ ∈ K e') ∧ F - F₁ = C (a ^ (e + 1)) * G := by
  haveI : Module.Finite R (homogeneousSubmodule σ R t) := Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg _ _ _)
  haveI := GlobalTheory.isPrecomplete_of_finite (Ideal.span {a}) (homogeneousSubmodule σ R t)
  obtain ⟨x', y, hx', hy⟩ := GlobalTheory.Unif.exists_limit_of_successive_corrections R a (homogeneousSubmodule σ R t)
    (fun e => ((K e).restrictScalars R).comap (homogeneousSubmodule σ R t).subtype)
    (fun e x hx => h₁ e x.1 x.2 hx)
    (fun e x => by
      show a ^ (e + 1) • x.1 ∈ K e
      rw [smul_eq_C_mul]
      exact Ideal.mul_mem_right _ _ (h₂ e))
    (fun e x hx => by
      obtain ⟨G, hG, h⟩ := h₃ e x.1 x.2 hx
      refine ⟨⟨G, hG⟩, ?_⟩
      show x.1 - a ^ (e + 1) • G ∈ K (e + 1)
      rwa [smul_eq_C_mul]) e ⟨F, hF⟩ h
  refine ⟨x'.1, y.1, x'.2, hx', ?_⟩
  rw [← smul_eq_C_mul]
  exact congrArg Subtype.val hy

end GlobalTheory.Unif.FormalEmb


open GlobalTheory.Unif.PolyStep GlobalTheory.Unif.FormalEmb in
theorem GlobalTheory.Unif.exists_projective_of_formal_embedding : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans V (IsLocalRing.maximalIdeal V) e)) → (∀ e, Flat (Y e).hom) → ∀ (H : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (H e) ((H (e + 1)).pull (β e))), (∀ e, (H e).IsLB ∧ (v e).IsGen) → ∀ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (H e)), (∀ e, (∀ j, (∀ z (k : (H (e + 1)).ι) (k' : (H e).ι), (β e) z ∈ (H (e + 1)).U k → z ∈ (H e).U k' → gs (β e) z _ ((s (e + 1) j).f k) = (Geo.Tor.gw (v e) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s e j).f k')))) → VeryAmpleBy (Y 0).hom (H 0) (s 0) → ∃ (B : Over (Spec (CommRingCat.of V))) (H' : LB B.left) (s' : Fin (n + 1) → LB.Sec H') (b : ∀ e, (Y e).left ⟶ B.left) (w : ∀ e, LB.Iso (H e) (H'.pull (b e))), H'.IsLB ∧ VeryAmpleBy B.hom H' s' ∧ (∀ e, IsPullback (b e) (Y e).hom B.hom (thick V (IsLocalRing.maximalIdeal V) e)) ∧ (∀ e, β e ≫ b (e + 1) = b e) ∧ (∀ e, (w e).IsGen ∧ (∀ j, (∀ z (k : (H').ι) (k' : (H e).ι), (b e) z ∈ (H').U k → z ∈ (H e).U k' → gs (b e) z _ ((s' j).f k) = (Geo.Tor.gw (w e) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s e j).f k')))) ∧ ∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) V), F.IsHomogeneous t → (∀ e, (∀ k : (H e).ι, MvPolynomial.eval₂Hom (cst ((Y (e)).hom ≫ thick V (IsLocalRing.maximalIdeal V) (e)) ((H e).U k)) (fun j => (s e j).f k) (F) = 0)) → (∀ k : (H').ι, MvPolynomial.eval₂Hom (cst (B.hom) ((H').U k)) (fun j => (s' j).f k) (F) = 0) := by
  intro V _ _ _ _ Y β hβ hflat H v hH n s hs hva
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  haveI : IsAdicComplete (Ideal.span {ϖ}) V := hϖ.maximalIdeal_eq ▸ inferInstance
  have hVA : ∀ e, VeryAmpleBy (Y e).hom (H e) (s e) := by
    rintro (_ | e)
    · exact hva
    · obtain ⟨j₀, hj, w, hw, hr⟩ := tower _ Y β hβ H v hH s hs e
      exact GlobalTheory.AbLaw.veryAmpleBy_of_isNilpotent _ _ _ (Ideal.Quotient.factor_surjective _) (nilpotent_ker hϖ _)
        _ _ _ _ j₀ hj _ _ w n _ _ (hH _).1 (hH _).1 ((isGen_iff _).2 hw) hr hva
  have c₁ : ∀ e, β e ≫ (Y (e + 1)).hom ≫ thick V (IsLocalRing.maximalIdeal V) (e + 1) =
      (Y e).hom ≫ thick V (IsLocalRing.maximalIdeal V) e := fun e => by
    rw [← Category.assoc, (hβ e).w, Category.assoc, thickTrans_comp]
  let K : ℕ → Ideal (MvPolynomial (Fin (n + 1)) V) := fun e =>
    vanIdeal ((Y e).hom ≫ thick V (IsLocalRing.maximalIdeal V) e) (s e)
  let S : Set (MvPolynomial (Fin (n + 1)) V) := {F | (∃ t, F.IsHomogeneous t) ∧ ∀ e, F ∈ K e}
  have hS : ∀ e, Ideal.span S ≤ K e := fun e => Ideal.span_le.2 fun F hF => hF.2 e
  obtain ⟨B, f, H', s', hH', hva', hB⟩ := GlobalTheory.ProjQuot.exists_veryAmpleBy_of_ideal V n (Ideal.span S)
    (component_mem_span S fun F hF => hF.1)
  have hB' : ∀ t (F : MvPolynomial (Fin (n + 1)) V), F.IsHomogeneous t → (∀ e, F ∈ K e) → ∀ k : H'.ι,
      MvPolynomial.eval₂Hom (cst f (H'.U k)) (fun j => (s' j).f k) F = 0 := fun t F hF h =>
    (hB t F hF).2 fun i => ⟨0, by rw [pow_zero, _root_.one_mul]; exact Ideal.subset_span ⟨⟨t, hF⟩, h⟩⟩
  choose b w hb hw hr using fun e => GlobalTheory.exists_hom_of_veryAmpleBy V B f H' n s' hH' hva' _
    ((Y e).hom ≫ thick V (IsLocalRing.maximalIdeal V) e) (H e) (s e) (hH e).1 (hVA e).1 (fun t F hF h =>
      (mem_vanIdeal _ _ _).1 (mem_vanIdeal_of_sat _ _ (hVA e).1 fun i =>
        ((hB t F hF).1 h i).imp fun _ hm => hS e hm))
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.Unif.exists_form_correction V ϖ hϖ Y β hβ hflat H v hH n s hs hva
  have hz : ∀ e, Ideal.Quotient.mk (IsLocalRing.maximalIdeal V ^ (e + 1)) (ϖ ^ (e + 1)) = 0 := fun e =>
    Ideal.Quotient.eq_zero_iff_mem.2 ((mem_pow hϖ _ _).2 dvd_rfl)
  refine ⟨Over.mk f, H', s', b, w, hH', hva', fun e => ?_, fun e => ?_, fun e => ⟨hw e, hr e⟩,
    fun t F hF h => hB' t F hF fun e => (mem_vanIdeal _ _ _).2 (h e)⟩
  · refine GlobalTheory.ProjBaseChange.isPullback_of_equations_lift V B f H' n s' hH' hva' _ _ Ideal.Quotient.mk_surjective
      _ (Y e).hom (H e) (s e) (b e) (w e) (hH e).1 (hVA e) (hb e) (hw e) (hr e) t₀ fun t ht F hF h => ?_
    obtain ⟨F₁, G, hF₁, hK, hG⟩ := exists_form_limit ϖ K t
      (fun e F hF h => by
        have := mem_vanIdeal_pull (hH (e + 1)).1 (hs e) _ hF h
        rwa [c₁] at this)
      (fun e => (mem_vanIdeal _ _ _).2 fun k => by
        rw [MvPolynomial.eval₂Hom_C, GlobalTheory.Unif.PolyStep.cst_comp, RingHom.comp_apply, hz, map_zero])
      (fun e F hF h => (ht₀ t ht e F hF ((mem_vanIdeal _ _ _).1 h)).imp fun G hG =>
        ⟨hG.1, (mem_vanIdeal _ _ _).2 hG.2⟩) e F hF ((mem_vanIdeal _ _ _).2 h)
    refine ⟨F₁, hF₁, hB' t F₁ hF₁ hK, ?_⟩
    rw [eq_comm, ← sub_eq_zero, ← map_sub, hG, map_mul, MvPolynomial.map_C, hz, map_zero, zero_mul]
  · have hv := (isGen_iff _).1 (hH e).2
    have hw' := (isGen_iff _).1 (hw (e + 1))
    obtain ⟨w'', T⟩ := exists_comp (hH (e + 1)).1 (w (e + 1)) (v e) hw' hv hH' (hH e).1
    exact GlobalTheory.MapUniq.hom_eq_of_pull_sections V B f H' n s' hH' hva' _ (H e) (s e) _ _ w'' (w e) (hH e).1
      (by rw [Category.assoc, hb, hb, c₁]) ((isGen_iff _).2 (T.pgen_comp (hH (e + 1)).1 hw' hv)) (hw e)
      (fun j => Rel.comp T (hH (e + 1)).1 (hr (e + 1) j) (hs e j)) (hr e)
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.integralFamily_prescribedTerm_unit_at_prime : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (W : (Spec (CommRingCat.of R)).Opens), Nonempty (PsiOn D.toPre W) → ∀ p : (Spec (CommRingCat.of R)), p ∈ W → ∀ (k : ℕ), 1 ≤ k → ∀ (ρ : D.toPre.X) (s : D.toPre.SecB k ρ), ∃ r : R, r ∉ p.asIdeal ∧ ∃ (F : Fam D.toPre (FractionRing R) k) (f : ∀ α, D.toPre.SecB k α), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (F.s α) (D.toPre.famφB α) (DegPre.famε k) (f α) (DegPre.prB D.toPre (FractionRing R)).left 1) ∧ (∀ j, (f ρ).f j = resTop _ (scal D.toPre.P.A.hom r) * (s).f j) ∧ ∀ β, (∀ mu, ρ + k • mu ≠ β) → ∀ j, (f β).f j = 0 := by
  first | exact @GlobalTheory.integralFamily_at_prime | exact GlobalTheory.integralFamily_at_prime | (intros; apply GlobalTheory.integralFamily_at_prime <;> assumption)
end
