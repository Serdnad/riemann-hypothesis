module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2790
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3308
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2926
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2967
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2939
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2805
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3387
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2988
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2989
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedCommGroupSchemeArtinFibreProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2870
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2869
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2871
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3302
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3250
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3101
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle095
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle032
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3388
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle003

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Poinc.PreSys

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

theorem rank_le (hn : 3 ≤ n) (T : Trait F) : Module.finrank ℤ T.D.toPre.X ≤ g := GlobalTheory.T.siegelTrait_characterGroup_finrank_le_genus_of_three_le g n F hn T

theorem lam (hE : IsE8 W) (hT : ThetaInt F W i) (X₁ : Setup F W i) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z)
    (hz : IsClosed ({z₁} : Set X₁.M.Z)) : ∃ C : ℝ, ∀ (c : CTrait X₁ p z₁) (x : c.T.D.toPre.X), x ≠ 0 →
      ∃ h ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁), Real.exp (-(C * (c.sc * c.T.β x x))) ≤ ‖c.val h‖ :=
  GlobalTheory.T.thetaSetup_classicalTraitPeriods_bounded_below_maxIdeal _ n F W Z i X₁ X₁.one_le X₁.three_le X₁.odd X₁.imm hE hT X₁.projM p z₁ hz

variable {X₁ : Setup F W i} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z}

def evC (c : CTrait X₁ p z₁) : X₁.M.Z.presheaf.stalk z₁ →+* PadicAlgCl p :=
  (RatModel.valHomOf (gPt p ≫ c.y) z₁ (RatModel.gPt_specializes c.cen)).comp (X₁.M.stalkEquiv z₁).toRingHom

theorem evC_apply (c : CTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) : evC c a = c.val a := rfl

theorem norm_evC_le (c : CTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) : ‖evC c a‖ ≤ 1 :=
  RatModel.norm_val_le_one c.cen (X₁.M.stalkEquiv z₁ a).2

theorem norm_evC_lt (c : CTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) (ha : a ∈ maximalIdeal _) :
    ‖evC c a‖ < 1 := by
  have h1 : ¬ IsUnit (X₁.M.stalkEquiv z₁ a) := fun hu => ha ((isUnit_map_iff (X₁.M.stalkEquiv z₁) a).1 hu)
  exact (RatModel.norm_val_lt_one_iff c.cen (X₁.M.stalkEquiv z₁ a).2).2 h1

theorem sc_pos (c : CTrait X₁ p z₁) : 0 < c.sc := by
  have hϖ0 : algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 c.T.irr.ne_zero
  have h0 : c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ) ≠ 0 := (map_ne_zero _).2 hϖ0
  have hlt : ‖c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ)‖ < 1 := by
    by_contra hge
    push_neg at hge
    have hinv : ‖c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ)⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ hge
    obtain ⟨w, hw⟩ := (c.int _).1 hinv
    apply c.T.irr.not_isUnit
    refine isUnit_iff_exists_inv.2 ⟨w, IsFractionRing.injective c.T.V (FractionRing c.T.V) ?_⟩
    rw [map_mul, hw, map_one, mul_inv_cancel₀ hϖ0]
  unfold CTrait.sc
  have := Real.log_neg (norm_pos_iff.2 h0) hlt
  linarith

theorem beta_pos (c : CTrait X₁ p z₁) (x : c.T.D.toPre.X) (hx : x ≠ 0) : 0 < c.T.β x x := by
  obtain ⟨j, hj⟩ := IsMonomial.exists_pos (IsLocalRing.maximalIdeal.isMaximal c.T.V).ne_top c.T.mono hx
  fin_cases j
  simpa using hj

end GlobalTheory.Poinc.PreSys

namespace GlobalTheory.Poinc.PreSys

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  {X₁ : Setup F W i} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z}


variable (X₁ p) in
abbrev Key : Type := (Sp (OO p) ⟶ X₁.M.Z) × (Σ k : ℕ, (Fin k → ℤ) → (Fin k → ℤ) → ℝ)

def Rep (c : CTrait X₁ p z₁) (q : Key X₁ p) : Prop :=
  c.y = q.1 ∧ ∃ e : (Fin q.2.1 → ℤ) ≃ₗ[ℤ] c.T.D.toPre.X, ∀ u v, q.2.2 u v = c.sc * c.T.β (e u) (e v)

def coord (c : CTrait X₁ p z₁) : (Fin (Module.finrank ℤ c.T.D.toPre.X) → ℤ) ≃ₗ[ℤ] c.T.D.toPre.X :=
  (Module.finBasis ℤ c.T.D.toPre.X).equivFun.symm

def keyOf (c : CTrait X₁ p z₁) : Key X₁ p :=
  (c.y, ⟨Module.finrank ℤ c.T.D.toPre.X, fun u v => c.sc * c.T.β (coord c u) (coord c v)⟩)

theorem rep_keyOf (c : CTrait X₁ p z₁) : Rep c (keyOf c) := ⟨rfl, coord c, fun _ _ => rfl⟩


variable (X₁ p z₁) in
def Pts : Type := {q : Key X₁ p // ∃ c : CTrait X₁ p z₁, Rep c q}

noncomputable def pick (y : Pts X₁ p z₁) : CTrait X₁ p z₁ := Classical.choose y.2

theorem pick_rep (y : Pts X₁ p z₁) : Rep (pick y) y.1 := Classical.choose_spec y.2


variable (X₁ p z₁) in
noncomputable def sys : FPre (id : ℤ → ℤ) g p (X₁.M.Z.presheaf.stalk z₁) where
  Y := Pts X₁ p z₁
  ev y := evC (pick y)
  ev_le y h := norm_evC_le _ h
  ev_lt y h hh := norm_evC_lt _ h hh
  X y := (pick y).T.D.toPre.X
  rank_le y := rank_le X₁.three_le _
  β y := (pick y).T.β
  bal y := ⟨(pick y).T.symm, fun a u v => by simp⟩
  pos y x hx := beta_pos _ x hx
  sc y := (pick y).sc
  sc_pos y := sc_pos _

theorem sys_matches : (sys X₁ p z₁ (g := g)).Matches := by
  intro c
  refine ⟨⟨keyOf c, c, rep_keyOf c⟩, fun a => ?_, ?_⟩
  · obtain ⟨hy, -⟩ := pick_rep ⟨keyOf c, c, rep_keyOf c⟩
    show evC _ a = c.val a
    rw [evC_apply]
    unfold CTrait.val
    rw [hy]
    rfl
  · obtain ⟨-, e', he'⟩ := pick_rep ⟨keyOf c, c, rep_keyOf c⟩
    have key : ∀ a b : (pick ⟨keyOf c, c, rep_keyOf c⟩).T.D.toPre.X,
        (pick ⟨keyOf c, c, rep_keyOf c⟩).sc * (pick ⟨keyOf c, c, rep_keyOf c⟩).T.β a b =
          c.sc * c.T.β (coord c (e'.symm a)) (coord c (e'.symm b)) := by
      intro a b
      have h := he' (e'.symm a) (e'.symm b)
      rw [e'.apply_symm_apply, e'.apply_symm_apply] at h
      exact h.symm
    exact ⟨e'.symm.trans (coord c), key⟩

theorem sys_lam (hE : IsE8 W) (hT : ThetaInt F W i) (hz : IsClosed ({z₁} : Set X₁.M.Z)) :
    (sys X₁ p z₁ (g := g)).abelian₂ := by
  obtain ⟨C, hC⟩ := lam hE hT X₁ p z₁ hz
  exact ⟨C, fun y x hx => by
    obtain ⟨h, hm, hle⟩ := hC (pick y) x hx
    exact ⟨h, hm, hle⟩⟩

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z),
    IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z), IsClosed ({z₁} : Set X₁.M.Z) →
      ∃ Φ : FPre (id : ℤ → ℤ) g p (X₁.M.Z.presheaf.stalk z₁), Φ.Matches ∧ Φ.abelian₂ ∧
        (∀ y, ∃ c : CTrait X₁ p z₁, (∀ a, Φ.ev y a = c.val a) ∧ ∃ e : Φ.X y ≃ₗ[ℤ] c.T.D.toPre.X,
          ∀ a b, Φ.sc y * Φ.β y a b = c.sc * c.T.β (e a) (e b)) := by
  intro g n F W Z i hE hT X₁ p _ z₁ hz
  exact ⟨sys X₁ p z₁, sys_matches, sys_lam hE hT hz, fun y => ⟨pick y, fun a => rfl, LinearEquiv.refl ℤ _,
    fun a b => rfl⟩⟩

end GlobalTheory.Poinc.PreSys
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum



theorem GlobalTheory.Mum.Emb.lift_closedPoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ E : Emb M.π G', ∀ (P' : Scheme.{0}) (b : P' ⟶ PSpace R E.N) (X : E.H.toScheme.Opens) (a : X.toScheme ⟶ P'), LocallyQuasiFinite b → Surjective a → a ≫ b = X.ι ≫ E.f → (∀ z : E.H.toScheme, M.π (G'.hom (E.H.ι z)) = closedPoint R → z ∈ X) → ∀ x : P', IsClosed ({x} : Set P') → (b ≫ PSpace.str R E.N) x = closedPoint R → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ P') (s : Sp Ω ⟶ M.S), Set.range ξ = {x} → ξ ≫ b ≫ PSpace.str R E.N = s ≫ M.π → ∃ p : Sp Ω ⟶ X.toScheme, p ≫ a = ξ ∧ p ≫ X.ι ≫ E.H.ι ≫ G'.hom = s := by
  intro R _ _ _ hAdm M G' _ _ hG E P' b X a hb ha hab hX x hx hxc Ω _ _ ξ s hξ hs
  have hxr : ∀ w, ξ w = x := fun w => by
    have : ξ w ∈ Set.range ξ := ⟨w, rfl⟩
    rw [hξ] at this; exact this
  have hfo : ∀ h : E.H.toScheme, PSpace.str R E.N (E.f h) = M.π (G'.hom (E.H.ι h)) := fun h => by
    rw [← Scheme.Hom.comp_apply, E.f_over]; rfl
  have hcl : ∀ h : E.H.toScheme, E.f h ∈ Set.range (ξ ≫ b) → M.π (G'.hom (E.H.ι h)) = closedPoint R := by
    rintro h ⟨w, hw⟩
    rw [← hfo, ← hw, ← Scheme.Hom.comp_apply, Category.assoc, Scheme.Hom.comp_apply, hxr]
    exact hxc
  obtain ⟨z, hz⟩ := ha.surj x
  have hzx : E.f (X.ι z) = b x := by
    rw [← hz, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hab]
  have hrng : E.f (X.ι z) ∈ Set.range (ξ ≫ b) := by
    let w : Sp Ω := Nonempty.some inferInstance
    exact ⟨w, by rw [Scheme.Hom.comp_apply, hxr, hzx]⟩
  have hg : ∃ g : E.H.toScheme, M.π (G'.hom (E.H.ι g)) = closedPoint R ∧ E.f g ∈ Set.range (ξ ≫ b) :=
    ⟨X.ι z, hcl _ hrng, hrng⟩
  have hs' : (ξ ≫ b) ≫ PSpace.str R E.N = s ≫ M.π := by rw [Category.assoc]; exact hs
  obtain ⟨Ω', _, io, q, hq1, hq2⟩ := GlobalTheory.T.exists_lift_after_field_extension R M.S M.π G' E Ω (ξ ≫ b) s hs' hg
  let φ : E.H.toScheme ⟶ pullback M.π (PSpace.str R E.N) :=
    pullback.lift (E.H.ι ≫ G'.hom) E.f (by rw [E.f_over, Category.assoc])
  haveI : Smooth G'.hom := hG.smooth
  have hφ : LocallyOfFiniteType φ := by
    have : LocallyOfFiniteType (φ ≫ pullback.fst _ _) := by
      rw [pullback.lift_fst]; infer_instance
    exact HasRingHomProperty.of_comp (fun _ _ => RingHom.FiniteType.of_comp_finiteType) this
  obtain ⟨p₀, hp₀⟩ := GlobalTheory.T.exists_rational_point_of_point_over_field_extension _ _ φ hφ Ω (pullback.lift s (ξ ≫ b) hs'.symm) Ω' io q (by
    apply pullback.hom_ext
    · simp only [φ, Category.assoc, pullback.lift_fst]; exact hq2
    · simp only [φ, Category.assoc, pullback.lift_snd]; exact hq1)
  have hp1 : p₀ ≫ E.f = ξ ≫ b := by
    have := congrArg (· ≫ pullback.snd M.π (PSpace.str R E.N)) hp₀
    simp only [φ, Category.assoc] at this
    rwa [pullback.lift_snd, pullback.lift_snd] at this
  have hp2 : p₀ ≫ E.H.ι ≫ G'.hom = s := by
    have := congrArg (· ≫ pullback.fst M.π (PSpace.str R E.N)) hp₀
    simp only [φ, Category.assoc] at this
    rwa [pullback.lift_fst, pullback.lift_fst, ← Category.assoc] at this
  have hU : ∀ h : E.H.toScheme, E.f h ∈ Set.range (ξ ≫ b) → h ∈ X := fun h hh => hX h (hcl h hh)
  have hpX : Set.range p₀ ⊆ Set.range X.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine hU _ ⟨w, ?_⟩
    rw [← Scheme.Hom.comp_apply, hp1]
  let p : Sp Ω ⟶ X.toScheme := IsOpenImmersion.lift X.ι p₀ hpX
  have hpι : p ≫ X.ι = p₀ := IsOpenImmersion.lift_fac _ _ _
  haveI : IsNoetherianRing R := hAdm.1
  have c4 := GlobalTheory.T.geometricFibre_projEmbedding_fixedGroup_connected R M.S M.π (by have := M.proper; infer_instance) G' hG.smooth E
    (GlobalTheory.T.connectedSpace_closedFibre_modification_fieldExtension R hAdm M) Ω (ξ ≫ b) hg
  have c3 := GlobalTheory.T.connectedSpace_pullback_restrict_open_containing_fibre _ _ _ X E.f (ξ ≫ b) hU c4
  have c2 := GlobalTheory.T.connectedSpace_pullback_of_comp_of_surjective _ _ _ _ a b (X.ι ≫ E.f) (ξ ≫ b) hab ha c3
  refine ⟨p, GlobalTheory.T.eq_of_comp_eq_of_connectedSpace_pullback' _ _ b hb Ω (ξ ≫ b) (p ≫ a) ξ ?_ rfl c2, ?_⟩
  · rw [Category.assoc, hab, ← Category.assoc, hpι, hp1]
  · rw [← Category.assoc, hpι, hp2]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_oLinear_of_oAct : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O), ∃ (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG := by
  intro R _ _ _ hR D A G _ _ hG U O _ _ _ o
  have hgen : IsMonHom U.gen.hom := U.gen_hom
  have hgeni : IsMonHom U.gen.inv := by infer_instance
  have L1 : ∀ a : O, ∃ g : G ⟶ G, IsMonHom g ∧ ActsAs U.toUnifPre (o.onB.act a) (fun χ => star a • χ) g := by
    intro a
    obtain ⟨f, hf, hfA⟩ := GlobalTheory.T.exists_genericEndomorphism_mumford_ringAction R hR D A G hG U O o a
    obtain ⟨g, hg, hgf⟩ := GlobalTheory.T.semiAbelian_generic_endomorphism_extends R hR G hG (U.gen.hom ≫ f ≫ U.gen.inv) inferInstance
    refine ⟨g, hg, hfA g hg ?_⟩
    rw [hgf]; simp
  have L2 := GlobalTheory.T.uniformisedGroup_endomorphism_unique_of_thickening_action R hR D A G hG U
  choose g hg hgA using L1
  have one : g 1 = 𝟙 G := by
    refine L2 _ _ _ _ (hg 1) inferInstance (hgA 1) ?_
    have := actsAs_id U.toUnifPre
    rw [o.onB.map_one]
    convert this using 1
    funext χ; simp
  have mul : ∀ a b : O, g (a * b) = g b ≫ g a := by
    intro a b
    haveI := hg a; haveI := hg b
    refine L2 _ _ _ _ (hg (a * b)) inferInstance (hgA (a * b)) ?_
    have := actsAs_comp U.toUnifPre (hgA b) (hgA a)
    rw [o.onB.map_mul]
    convert this using 1
    funext χ; simp [star_mul, mul_smul]
  have add : ∀ a b : O, g (a + b) = padd G (g a) (g b) := by
    intro a b
    haveI := hg a; haveI := hg b
    have hp : IsMonHom (padd G (g a) (g b)) := by unfold padd; infer_instance
    refine L2 _ _ _ _ (hg (a + b)) hp (hgA (a + b)) ?_
    have := actsAs_padd U.toUnifPre (hgA a) (hgA b)
    rw [o.onB.map_add]
    convert this using 1
    funext χ; simp [star_add, add_smul]
  let oG : RingAct G O := { act := g, hom := hg, map_one := one, map_mul := mul, map_add := add }
  let F := Over.pullback (jK R)
  let fA : O → (A.A ⟶ A.A) := fun a => U.gen.inv ≫ F.map (g a) ≫ U.gen.hom
  let oA : A.OAct O :=
    { act := fA
      hom := fun a => by haveI := hg a; dsimp [fA]; infer_instance
      map_one := by simp [fA, F, one]
      map_mul := fun a b => by simp [fA, F, mul]
      map_add := fun a b => by
        simp only [fA, F, add, pull_padd]
        rw [padd_comp_hom, padd, padd, comp_lift_assoc]
      rosati := fun a => GlobalTheory.T.rosatiAdjoint_genericFibre_of_acts_star R hR D A G hG U O o a (g a) (g (star a)) (hg a) (hg (star a)) (hgA a) (hgA (star a)) }
  refine ⟨oA, oG, ⟨fun a => ?_, fun e a => (hgA a e).1, fun e a => (hgA a e).2⟩⟩
  simp [oA, oG, fA, F]
end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.ClosedPt

theorem cpl_isIntegrallyClosed : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω) (x : M.Z), IsIntegrallyClosed (M.Z.presheaf.stalk x) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), IsCpl j → IsIntegrallyClosed R := by
  intro o' Ω _ _ _ hA M x hic R _ _ _ j hC
  obtain ⟨e, -⟩ := hC
  have hinjΩ := M.stalkHom_injective x
  haveI : IsDomain (M.Z.presheaf.stalk x) := hinjΩ.isDomain
  haveI : CharZero Ω := hA.char
  haveI : CharZero (M.Z.presheaf.stalk x) := (RingHom.charZero_iff hinjΩ).2 inferInstance
  haveI := hic
  haveI : Algebra.EssFiniteType ℤ (M.Z.presheaf.stalk x) := GlobalTheory.Poinc.CompletedStalk.essFiniteType_int_stalk M x
  obtain ⟨hRd, hRi⟩ := GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed (M.Z.presheaf.stalk x)
  exact IsIntegrallyClosed.of_equiv e

theorem exists_cong_of_cast {N n : ℕ} (v w : Fin n → ℤ) (h : ∀ i, ((v i : ℤ) : ZMod N) = ((w i : ℤ) : ZMod N)) :
    ∃ k : Fin n → ℤ, v = w + N • k := by
  have : ∀ i, ∃ k : ℤ, v i = w i + N * k := fun i => by
    obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub (w i) (v i) N).1 (h i).symm
    exact ⟨k, by linarith⟩
  choose k hk using this
  exact ⟨k, funext fun i => by simp [hk i, nsmul_eq_mul]⟩

theorem be_le_of_dvd {R V' X : Type} [CommRing R] [CommRing V'] [IsDomain V'] [AddCommGroup X] (g' : R →+* V') {w : V'}
    (hw : Irreducible w) (be : LinearMap.BilinForm ℤ X) {a b : X} {r s : R}
    (ha : 0 ≤ be a a ∧ Associated (g' r ^ 2) (w ^ (be a a).toNat))
    (hb : 0 ≤ be b b ∧ Associated (g' s ^ 2) (w ^ (be b b).toNat)) (hrs : r ∣ s) : be a a ≤ be b b := by
  have h0 : g' r ^ 2 ∣ g' s ^ 2 := pow_dvd_pow_of_dvd (map_dvd g' hrs) 2
  have h1 : w ^ (be a a).toNat ∣ w ^ (be b b).toNat :=
    (ha.2.dvd_iff_dvd_left).1 ((hb.2.dvd_iff_dvd_right).1 h0)
  have h2 := (pow_dvd_pow_iff hw.ne_zero hw.not_isUnit).1 h1
  have := Int.toNat_of_nonneg ha.1
  have := Int.toNat_of_nonneg hb.1
  omega

theorem exists_lattice_data : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (M : RatModel X₁.o₁ X₁.Ω₁) (U₀ : M.Z.Opens) (EE : M.Lat X₁.S.J) (out : ZHOut X₁.ρ M U₀ EE), X₁.S.admitted M U₀ → X₁.S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∃ (X : Type) (_ : AddCommGroup X) (_ : Module (𝓞 E) X) (_ : Module.Finite (𝓞 E) X) (_ : Module.Projective (𝓞 E) X) (n : ℕ) (eb : X ≃ₗ[ℤ] (Fin n → ℤ)) (b₀ : LinearMap.BilinForm ℤ X) (μ : (Fin n → ZMod X₁.S.N) → X) (e : (Fin n → ZMod X₁.S.N) → X₁.Ω₁), Module.finrank (𝓞 E) X ≤ min Dw.p Dw.q ∧ b₀ ∈ balForms H.bar X ∧ (∀ y, y ≠ 0 → 0 < b₀ y y) ∧ (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod X₁.S.N) = cl i) ∧ (∀ cl (α : X), (∀ i, ((eb α i : ℤ) : ZMod X₁.S.N) = cl i) → b₀ (μ cl) (μ cl) ≤ b₀ α α) ∧ (∀ cl, e cl ≠ 0 ∧ ∃ (T₀ : AddSubgroup X₁.S.Gam) (c' : T₀ →+ ZMod X₁.S.N) (κ : X₁.S.J × (T₀ → ZMod ((X₁.S.r * X₁.S.N) ^ 2))) (x₀ : X₁.S.Gam), X₁.S.IsoFree T₀ ∧ e cl = X₁.S.FF T₀ c' κ / X₁.S.th x₀) ∧ ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ π : X →ₗ[𝓞 E] T.P.D.toPre.X, Function.Surjective π ∧ (∀ cl (α : X), (∀ i, ((eb α i : ℤ) : ZMod X₁.S.N) = cl i) → T.be (π (μ cl)) (π (μ cl)) ≤ T.be (π α) (π α)) ∧ ∀ cl, UOrdEq M T ξ (e cl ^ (2 * X₁.S.N)) (T.be (π (μ cl)) (π (μ cl))).toNat := by
  intro E _ _ _ H Dw l Xo c C X₁ M U₀ EE out hAdm hEE x hx
  obtain ⟨R, _, _, _, j, G, _, _, gm, D, A, U, hB, hC, hpb, hL, hPsi⟩ :=
    GlobalTheory.Poinc.CompletedStalk.exists_completion_unif X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ X₁.big M U₀ EE out hAdm hEE x hx
  obtain ⟨f, hfm, hfT⟩ := GlobalTheory.T.integerAction_semiAbelian_along_traits_open E H Dw l Xo c C X₁ M U₀ EE out hAdm
  have hR := fun a => GlobalTheory.T.exists_completedLocalRing_endomorphism_character_action X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ M U₀ EE out x R j hB G gm hpb D A U (f a) (hfm a)
  choose fR m hfR using hR
  obtain ⟨T₀, ξ₀, hT₀, hξ₀⟩ := GlobalTheory.T.exists_unitaryTrait_centred_closedPoint E H Dw l Xo c C X₁ M U₀ EE out hAdm x hx
  have tr := GlobalTheory.T.exists_trait_lattice_map_at_closedPoint E H Dw l Xo c C X₁ M U₀ EE out hAdm f hfm hfT x hx R j hB hC G gm hpb D A U hL hPsi m
    (fun a => ⟨fR a, hfR a⟩)
  obtain ⟨V₀, _, _, _, h₀, g₀, ρ₀, -, hirr₀, hsq₀, hsurj₀, hco₀, hlin₀⟩ :=
    tr T₀ ξ₀ hT₀ (by rw [hξ₀])
  haveI : CharZero R := hB.2
  haveI : IsIntegrallyClosed R := cpl_isIntegrallyClosed X₁.o₁ X₁.Ω₁ M x (hAdm.1.normal x).2 R j hC
  have hco : ∀ y, ∃ r, PsiCoord D.toPre y r ∧ (y ≠ 0 → r ∈ maximalIdeal R) := fun y => by
    obtain ⟨r, h1, -, h3, -⟩ := (GlobalTheory.PsiCoordLocal.main R D inferInstance y).1
    exact ⟨r, h1, h3⟩
  obtain ⟨hdvr₀, -, -⟩ := T₀.cdvr
  haveI := hdvr₀
  haveI : IsLocalHom g₀ := GlobalTheory.T.isLocalHom_completedStalk_to_dvr_over_trait X₁.o₁ X₁.Ω₁ M x R j hC T₀.V T₀.ϖ V₀ h₀ g₀ ξ₀ hirr₀ hξ₀ hsq₀
  have hinj : Function.Injective ρ₀ := by
    refine (injective_iff_map_eq_zero ρ₀).2 fun y h0 => by_contra fun hy => ?_
    obtain ⟨r, hr, hrm⟩ := hco y
    obtain ⟨-, has⟩ := hco₀ y r hr
    simp only [h0, map_zero, LinearMap.zero_apply, Int.toNat_zero, pow_zero] at has
    have hu : IsUnit (g₀ r) := (isUnit_pow_iff two_ne_zero).1 (has.isUnit_iff.2 isUnit_one)
    exact (mem_maximalIdeal r |>.1 (hrm hy)) ((isUnit_map_iff g₀ r).1 hu)
  let e₀ : D.toPre.X ≃+ T₀.P.D.toPre.X := AddEquiv.ofBijective ρ₀ ⟨hinj, hsurj₀⟩
  have he₀ : ∀ y, e₀ y = ρ₀ y := fun _ => rfl
  obtain ⟨hbal, hposdef, hfin, hproj, n, ⟨eb⟩⟩ := GlobalTheory.T.balanced_posDef_finite_projective_lattice E H Dw l Xo c T₀
  let ℓ : ZMod X₁.S.N → ℤ := Function.surjInv ZMod.intCast_surjective
  have hℓ : ∀ z, ((ℓ z : ℤ) : ZMod X₁.S.N) = z := Function.surjInv_eq _
  let α₀ : (Fin n → ZMod X₁.S.N) → D.toPre.X := fun cl => e₀.symm (eb.symm (fun i => ℓ (cl i)))
  have hq := fun cl => GlobalTheory.T.exists_minimal_psiCoordinate_associated_fourierPower X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ X₁.big M U₀ EE out hAdm hEE x hx R j hB hC G gm hpb D A U hL
    hPsi (α₀ cl)
  choose mu hmu1 hmu2 e a he hFF hae hja using hq

  have hcong : ∀ cl (α : T₀.P.D.toPre.X), (∀ i, ((eb α i : ℤ) : ZMod X₁.S.N) = cl i) →
      CongMod X₁.S.N (e₀.symm α) (α₀ cl) := by
    intro cl α hα
    obtain ⟨k, hk⟩ := exists_cong_of_cast (N := X₁.S.N) (eb α) (fun i => ℓ (cl i)) (fun i => by rw [hα, hℓ])
    refine ⟨e₀.symm (eb.symm k), e₀.injective (eb.injective ?_)⟩
    simp only [α₀, map_add (f := _), map_nsmul, AddEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact hk
  refine ⟨T₀.P.D.toPre.X, inferInstance, inferInstance, hfin, hproj, n, eb, T₀.be, fun cl => ρ₀ (mu cl), e,
    UTrait.finrank_le_min E H Dw l Xo c T₀, hbal, hposdef, ?_, ?_, fun cl => ⟨he cl, hFF cl⟩, ?_⟩
  · intro cl i
    obtain ⟨w, hw⟩ := hmu1 cl
    show ((eb (ρ₀ (mu cl)) i : ℤ) : ZMod X₁.S.N) = cl i
    rw [← he₀, hw, map_add (f := _), map_nsmul, AddEquiv.apply_symm_apply, map_add (f := _), map_nsmul, LinearEquiv.apply_symm_apply]
    simp [hℓ, nsmul_eq_mul]
  · intro cl α hα
    obtain ⟨r, hr, -⟩ := hco (mu cl)
    obtain ⟨s, hs, -⟩ := hco (e₀.symm α)
    have := be_le_of_dvd g₀ hirr₀ T₀.be (hco₀ _ r hr) (hco₀ _ s hs) (hmu2 cl _ (hcong cl α hα) r s hr hs)
    rwa [← he₀ (e₀.symm α), AddEquiv.apply_symm_apply] at this
  · intro T ξ hT hsp
    obtain ⟨V', _, _, _, h, g', ρT, hh, hirr, hsq, hsurjT, hcoT, hlinT⟩ := tr T ξ hT hsp
    have hsm : ∀ (c' : 𝓞 E) (z : T₀.P.D.toPre.X), ρT (e₀.symm (c' • z)) = c' • ρT (e₀.symm z) := by
      intro c' z
      obtain ⟨a', rfl⟩ := H.bar.surjective c'
      have hz : H.bar a' • z = e₀ (m a' (e₀.symm z)) := by
        rw [he₀, hlin₀, ← he₀, AddEquiv.apply_symm_apply]
      rw [hz, AddEquiv.symm_apply_apply, hlinT]
    let π : T₀.P.D.toPre.X →ₗ[𝓞 E] T.P.D.toPre.X :=
      { toFun := fun z => ρT (e₀.symm z)
        map_add' := fun y z => by simp only [map_add (f := _)]
        map_smul' := fun c' z => hsm c' z }
    have hπ : ∀ y, π (ρ₀ y) = ρT y := fun y => by
      show ρT (e₀.symm (ρ₀ y)) = ρT y
      rw [← he₀, AddEquiv.symm_apply_apply]
    refine ⟨π, fun z => ?_, ?_, ?_⟩
    · obtain ⟨y, rfl⟩ := hsurjT z
      exact ⟨ρ₀ y, hπ y⟩
    · intro cl α hα
      obtain ⟨r, hr, -⟩ := hco (mu cl)
      obtain ⟨s, hs, -⟩ := hco (e₀.symm α)
      have := be_le_of_dvd g' hirr T.be (hcoT _ r hr) (hcoT _ s hs) (hmu2 cl _ (hcong cl α hα) r s hr hs)
      rwa [hπ, show π α = ρT (e₀.symm α) from rfl]
    · intro cl
      obtain ⟨r, hr, -⟩ := hco (mu cl)
      obtain ⟨-, has⟩ := hcoT (mu cl) r hr
      rw [hπ]
      have hord := GlobalTheory.T.uniformiserOrder_eq_of_associated_stalkImage E H Dw l Xo c X₁.o₁ X₁.Ω₁ M x T ξ hsp R j V' h g' hh hirr hsq (a cl ^ 2) _
        (by rw [map_pow, map_pow]; exact (((hja cl r hr).map g').pow_pow (n := 2)).trans has)
      rwa [map_pow, hae cl, ← pow_mul, mul_comm] at hord

end GlobalTheory.UPoinc.ClosedPt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.canonicalFamily_localInjections_eq_same_point : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R), Canon C → Inj C := by
  first | exact @GlobalTheory.UCanon.inj_of_canon | exact GlobalTheory.UCanon.inj_of_canon | (intros; apply GlobalTheory.UCanon.inj_of_canon <;> assumption)
end
