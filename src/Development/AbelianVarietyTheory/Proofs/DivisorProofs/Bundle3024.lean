module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2680
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2744
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2933
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2931
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2934
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.Poinc.Spread.noeth (o Ω : Type) [CommRing o] [IsNoetherianRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    (z : M.Z) : IsNoetherianRing (M.O z) := by
  haveI := M.lft
  haveI : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  exact isNoetherianRing_of_ringEquiv _ (M.stalkEquiv z)

theorem GlobalTheory.Poinc.Spread.endo_id {R O : Type} [CommRing R] [CommRing O] [IsDomain O] (f : R →+* O)
    (hf : ∀ o : O, ∃ a b : R, f b ≠ 0 ∧ f b * o = f a) (σ : Sp O ⟶ Sp O) (h : σ ≫ spMap f = spMap f) : σ = 𝟙 _ := by
  obtain ⟨s, rfl⟩ := Spec.map_surjective σ
  rw [← Spec.map_comp] at h
  have h' := Spec.map_injective h
  have hs : ∀ r, s.hom (f r) = f r := fun r => congrArg (fun g => g.hom r) h'
  have : s = 𝟙 _ := by
    ext o
    obtain ⟨a, b, hb, e⟩ := hf o
    have e2 := congrArg s.hom e
    rw [map_mul, hs, hs, ← e] at e2
    exact mul_left_cancel₀ hb e2
  rw [this, Spec.map_id]

theorem GlobalTheory.Poinc.Spread.sec {R₁ R₂ O M Γ : Type} [CommRing R₁] [CommRing R₂] [CommRing O] [IsDomain O] {P₁ : PolAV (Sp R₁)} {P₂ : PolAV (Sp R₂)} {f₁ : R₁ →+* O} {f₂ : R₂ →+* O} {e₁ : M → (P₁.A ⟶ P₁.A)} {e₂ : M → (P₂.A ⟶ P₂.A)} {t₁ : Γ → (baseOver (Sp R₁) ⟶ P₁.A)} {t₂ : Γ → (baseOver (Sp R₂) ⟶ P₂.A)}
    (hf : ∀ o : O, ∃ a b : R₁, f₁ b ≠ 0 ∧ f₁ b * o = f₁ a) (h : SameAt P₁ P₂ f₁ f₂ e₁ e₂ t₁ t₂) :
    ∃ (P : PolAV (Sp O)) (b₁ : P.A.left ⟶ P₁.A.left) (b₂ : P.A.left ⟶ P₂.A.left), IsGrpPullback P.A P₁.A (spMap f₁) b₁ ∧ IsGrpPullback P.A P₂.A (spMap f₂) b₂ ∧ LBIso P.L (P₁.L.pull b₁) ∧ LBIso P.L (P₂.L.pull b₂) ∧ (∀ E, ∃ e : P.A ⟶ P.A, e.left ≫ b₁ = b₁ ≫ (e₁ E).left ∧ e.left ≫ b₂ = b₂ ≫ (e₂ E).left) ∧ ∀ x, ∃ w : Sp O ⟶ P.A.left, w ≫ P.A.hom = 𝟙 _ ∧ w ≫ b₁ = spMap f₁ ≫ (t₁ x).left ∧ w ≫ b₂ = spMap f₂ ≫ (t₂ x).left := by
  obtain ⟨P, b₁, b₂, h₁, h₂, l₁, l₂, he, ht⟩ := h
  refine ⟨P, b₁, b₂, h₁, h₂, l₁, l₂, he, fun x => ?_⟩
  obtain ⟨w, w₁, w₂⟩ := ht x
  refine ⟨w, GlobalTheory.Poinc.Spread.endo_id f₁ hf _ ?_, w₁, w₂⟩
  have := Over.w (t₁ x)
  rw [Category.assoc, ← h₁.1.w, ← Category.assoc, w₁, Category.assoc, this]
  exact Category.comp_id _

theorem GlobalTheory.Poinc.Spread.main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X : Setup F W i) (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)) (p : ℕ) [Fact p.Prime] (z : X.M.Z) (c : CTrait X p z) (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X.o₁ X.Ω₁) (fg : R'.FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ R') (hev : ∀ x k, c₀ * X.S.ev x k ∈ R') (ρ' : (X.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)), Same X.ρ ε ρ' ε' (fun x => x) (RingHom.id _) → R' ≤ X.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) → ∀ (y₀ : R' →+* PadicAlgCl p), (∀ a : R', y₀ a = X.M.val (gPt p ≫ c.y) a) → ∀ (c₁ : X.Ω₁) (hc₁ : c₁ ≠ 0) (R'' : Subalgebra X.o₁ X.Ω₁) (fg₁ : R''.FG) (frac₁ : ∀ x : X.Ω₁, ∃ a ∈ R'', ∃ b ∈ R'', x = a / b) (hth₁ : ∀ x, c₁ * X.S.th x ∈ R'') (hev₁ : ∀ x k, c₁ * X.S.ev x k ∈ R'') (ρ'' : (X.S.rechart c₁ hc₁ R'' fg₁ frac₁ hth₁ hev₁).Real) (ε'' : Matrix (Fin 8) (Fin 8) ℤ → (ρ''.P.A ⟶ ρ''.P.A)), Same X.ρ ε ρ'' ε'' (fun x => x) (RingHom.id _) → R'' ≤ X.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) → ∀ (y₁ : R'' →+* PadicAlgCl p), (∀ a : R'', y₁ a = X.M.val (gPt p ≫ c.y) a) → ∀ (u : ρ'.UTest p y₀) (u' : ρ''.UTest p y₁), ∃ (P₀ : PolAV (Sp (PadicAlgCl p))) (a : P₀.A.left ⟶ u.A.A.left) (a' : P₀.A.left ⟶ u'.A.A.left), IsGrpPullback P₀.A u.A.A (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p))) a ∧ IsGrpPullback P₀.A u'.A.A (spMap (algebraMap (FractionRing u'.V) (PadicAlgCl p))) a' ∧ LBIso P₀.L (u.A.L.pull a) ∧ LBIso P₀.L (u'.A.L.pull a') ∧ (∀ b : X.S.Gam, ∃ (w : Sp (PadicAlgCl p) ⟶ P₀.A.left) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (x' : TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A), w ≫ P₀.A.hom = 𝟙 _ ∧ w ≫ a = x.left ∧ w ≫ a' = x'.left ∧ x.left ≫ u.φ = spMap y₀ ≫ (ρ'.pt b).left ∧ x'.left ≫ u'.φ = spMap y₁ ≫ (ρ''.pt b).left) ∧ ∀ (E : Matrix (Fin 8) (Fin 8) ℤ) (w w₂ : Sp (PadicAlgCl p) ⟶ P₀.A.left), w ≫ P₀.A.hom = 𝟙 _ → w₂ ≫ P₀.A.hom = 𝟙 _ → w₂ ≫ a ≫ u.φ = w ≫ a ≫ u.φ ≫ (ε' E).left → w₂ ≫ a' ≫ u'.φ = w ≫ a' ≫ u'.φ ≫ (ε'' E).left := by
  intro g n F W Z i X ε p _ z c c₀ hc R' fg frac hth hev ρ' ε' hS' hR' y₀ hy₀ c₁ hc₁ R'' fg₁ frac₁ hth₁ hev₁ ρ'' ε'' hS'' hR'' y₁ hy₁ u u'
  set z' := (gPt p ≫ c.y) (closedPoint (PadicAlgCl p)) with hz'
  haveI : IsDedekindDomain X.o₁ := ArithBase.ded (Ω := X.Ω₁)
  haveI : IsNoetherianRing (X.M.O z') := GlobalTheory.Poinc.Spread.noeth X.o₁ X.Ω₁ X.M z'
  haveI : IsIntegrallyClosed (X.M.Z.presheaf.stalk z') := X.normal.isIntegrallyClosed_stalk z'
  haveI : IsIntegrallyClosed (X.M.O z') := IsIntegrallyClosed.of_equiv (X.M.stalkEquiv z')
  let ι' : R' →+* X.M.O z' := (Subalgebra.inclusion hR').toRingHom
  let ι'' : R'' →+* X.M.O z' := (Subalgebra.inclusion hR'').toRingHom
  have h0 := GlobalTheory.Poinc.SameComb.combine _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hS' hS''
  have h1 := GlobalTheory.Poinc.sameAt_of_generic (X.M.O z') X.Ω₁ _ _ _ _ _ _ ι' ι'' _ _ _ _ h0
  have hfr : ∀ o : X.M.O z', ∃ a b : R', ι' b ≠ 0 ∧ ι' b * o = ι' a := by
    intro o
    obtain ⟨a, ha, b, hb, e⟩ := frac (o : X.Ω₁)
    by_cases hb0 : b = 0
    · refine ⟨0, 1, by simp, ?_⟩
      have : o = 0 := Subtype.ext (by simpa [hb0] using e)
      simp [this]
    · refine ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hb0 (congrArg Subtype.val h), Subtype.ext ?_⟩
      change b * (o : X.Ω₁) = a
      rw [e]; field_simp
  let v : X.M.O z' →+* PadicAlgCl p := RatModel.valHom (gPt p ≫ c.y) z' (RatModel.range_eq_singleton _ _)
  have e₀ : v.comp ι' = y₀ := RingHom.ext fun a => (hy₀ a).symm
  have e₁ : v.comp ι'' = y₁ := RingHom.ext fun a => (hy₁ a).symm
  obtain ⟨P₀, a, a', ha, ha', hL, hL', ht, hε⟩ := GlobalTheory.Poinc.Special.main _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.Poinc.Spread.sec hfr h1) v u.yK u'.yK
    (u.fac.trans e₀.symm) (u'.fac.trans e₁.symm) u.A u'.A u.φ u'.φ u.cart u'.cart u.lb u'.lb
  refine ⟨P₀, a, a', ha, ha', hL, hL', fun b => ?_, fun E w w₂ hw hw₂ h => ?_⟩
  · obtain ⟨w, hw, h₁, h₂⟩ := ht b
    have q₁ : (w ≫ a) ≫ u.A.A.hom = jFK (R := u.V) (PadicAlgCl p) := by
      rw [Category.assoc, ha.1.w, ← Category.assoc, hw, Category.id_comp]
    have q₂ : (w ≫ a') ≫ u'.A.A.hom = jFK (R := u'.V) (PadicAlgCl p) := by
      rw [Category.assoc, ha'.1.w, ← Category.assoc, hw, Category.id_comp]
    refine ⟨w, Over.homMk (w ≫ a) q₁, Over.homMk (w ≫ a') q₂, hw, rfl, rfl, ?_, ?_⟩
    · simpa [e₀] using h₁
    · simpa [e₁] using h₂
  · exact hε E w w₂ hw hw₂ h
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.diagonalEndOfEighthPower_of_polAV_pullback : ∀ {g n : ℕ} (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) {T T' : Scheme.{0}} (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (f : T' ⟶ T) (ψ : P'.A.left ⟶ P.A.left) (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)), IsDiagEnd F W P u ε → IsGrpPullback P'.A P.A f ψ → LBIso P'.L (P.L.pull ψ) → ∃ ε' : Matrix (Fin 8) (Fin 8) ℤ → (P'.A ⟶ P'.A), IsDiagEnd F W P' (f ≫ u) ε' ∧ ∀ E, (ε' E).left ≫ ψ = ψ ≫ (ε E).left := by
  first | exact @GlobalTheory.Poinc.isDiagEnd_pullback | exact GlobalTheory.Poinc.isDiagEnd_pullback | (intros; apply GlobalTheory.Poinc.isDiagEnd_pullback <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_generator_transfer_through_tensorIso : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) {Y : Scheme.{0}} {K : Type} [Fintype K] (φ' : K → (Y ⟶ D'.P.A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb D.P.L (fun p : K × ((Fin r × Fin r) × Fin 4) => φ' p.1 ≫ tensφ T.pr p.2) (fun p => ε p.1 * tensε W p.2))), t.IsGen → ∃ t' : LB.Gen (LB.LinComb D'.P.L φ' ε), t'.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' → (∏ a, gm (q ≫ φ' a) z _ (T.w.s (fun k => J ((q ≫ φ' a) ≫ tensφ T.pr k), J' (q ≫ φ' a))) ^ ε a) * val t' q z J' = val t q z J := by
  first | exact @GlobalTheory.TensGen.exists_gen_transfer | exact GlobalTheory.TensGen.exists_gen_transfer | (intros; apply GlobalTheory.TensGen.exists_gen_transfer <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_section_pullback_commuting_endomorphism_generator : ∀ {X Y : Scheme.{0}} (L : LB X), L.IsLB → ∀ (β : Y ⟶ X) (g : Y ⟶ Y) (h : X ⟶ X), g ≫ β = β ≫ h →
    ∀ (k k' : ℕ) (u : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, h] ![(k' : ℤ), -(k : ℤ)])), u.IsGen → ∀ (σ : SecK L β k),
    ∃ σ₂ : SecK L β k', ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
      sval σ₂ r z J = (val u (r ≫ β) z J).val * sval σ (r ≫ g) z J := by
  first | exact @GlobalTheory.Mum.exists_secK_pullMul_gen | exact GlobalTheory.Mum.exists_secK_pullMul_gen | (intros; apply GlobalTheory.Mum.exists_secK_pullMul_gen <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_cubeStep_generator_tensorPowerPairs : ∀ {S : Scheme.{0}} {B B' : Over S} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (L : RigLB B) (cb : CubicalStr B L) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (B' ⟶ B)), (∀ i, IsMonHom (pr i)) → ∃ c : LB.Gen (LB.LinComb L.L (Sum.elim (fun k : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr k.1.1) (snd B' B' ≫ pr k.1.2) k.2) (fun p : ULift.{0} (Finset (Fin 2)) × ((Fin r × Fin r) × Fin 4) => (psum B' (x2 B') p.1.down).left ≫ tensφ pr p.2)) (Sum.elim (fun k => (W + W.transpose) k.1.1 k.1.2 * Oε k.2) (fun p => -((-1) ^ (2 - p.1.down.card) * tensε W p.2)))), c.IsGen ∧ ∀ (T : Over S) (ρ : T ⟶ G2 B') (z : T.left) (J : (T.left ⟶ B.left) → L.L.ι), Good L.L z J → val c ρ.left z J = ∏ i, ∏ j, (cubV cb z J (ρ ≫ fst B' B' ≫ pr i) (ρ ≫ snd B' B' ≫ pr i) ((ρ ≫ fst B' B' ≫ pr j) * (ρ ≫ snd B' B' ≫ pr j)) * cubV cb z J (ρ ≫ fst B' B' ≫ pr j) (ρ ≫ snd B' B' ≫ pr j) (ρ ≫ fst B' B' ≫ pr i) * cubV cb z J (ρ ≫ fst B' B' ≫ pr j) (ρ ≫ snd B' B' ≫ pr j) (ρ ≫ snd B' B' ≫ pr i)) ^ (-W i j) := by
  exact @GlobalTheory.Mum.cube_step
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_lineBundlePowSection_transport_pullbackIso : ∀ {X X' : Scheme.{0}} (L : LB X) (L' : LB X') (f : X' ⟶ X) (w : LB.Iso L' (L.pull f)), L.IsLB → L'.IsLB → w.IsGen → ∀ (N : ℕ) (t : H0 L' N), ∃ s : SecK L f N, ∀ (Z : Scheme.{0}) (p : Z ⟶ X') (z : Z) J J', Good L z J → Good L' z J' → sval s p z J = (gw w p z (J (p ≫ f)) (J' p) ^ N).val * sval t p z J' := by
  first | exact @GlobalTheory.Mum.exists_secK_of_iso_pull | exact GlobalTheory.Mum.exists_secK_of_iso_pull | (intros; apply GlobalTheory.Mum.exists_secK_of_iso_pull <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.sharpEighthPower_relative_dimension_eq_eight_mul : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] (Q : Data V) (ρ : V →+* V₁) (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → D.P.g = 8 * Q.g := by
  first | exact @GlobalTheory.Poinc.Sep.sharpRef_relDim | exact GlobalTheory.Poinc.Sep.sharpRef_relDim | (intros; apply GlobalTheory.Poinc.Sep.sharpRef_relDim <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_tensorBundleRigidification : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (A' : Over (Spec (CommRingCat.of R))) [GrpObj A'] (L' : LB A'.left), L'.IsLB → ∀ (pr : Fin r → (A' ⟶ D.P.A)), (∀ i, IsMonHom (pr i)) → ∀ (w : LB.Iso L' (LB.LinComb D.P.L (tensφ pr) (tensε W))), w.IsGen → ∃ rig : LB.Gen (L'.pull (eSec A')), rig.IsGen ∧ ∀ (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι) (J' : ((TK R).left ⟶ A'.left) → L'.ι), Good D.P.L z J → Good L' z J' → val (LB.pullGen L' _ _ rig (toUnit (TK R)).left) (𝟙 _) z J' * gm (ptK η[A']) z _ (w.s (fun k => J (ptK η[A'] ≫ tensφ pr k), J' (ptK η[A']))) = 1 := by
  first | exact @GlobalTheory.Mum.TensRig.rig_exists | exact GlobalTheory.Mum.TensRig.rig_exists | (intros; apply GlobalTheory.Mum.TensRig.rig_exists <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_thetaLabel_common_generic_fibre_pullback : ∀ {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] (S₁ : ThetaSys o₁ Ω₁) (S₂ : ThetaSys o₂ Ω₂) (ρ₁ : S₁.Real) (ρ₂ : S₂.Real) (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₁.P.A ⟶ ρ₁.P.A)) (ε₂ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₂.P.A ⟶ ρ₂.P.A)) (φ : Ω₁ →+* Ω₂) (h : S₁.R →+* S₂.R) (ψ : ρ₂.P.A.left ⟶ ρ₁.P.A.left), (∀ a, ((h a : S₂.R) : Ω₂) = φ a) → IsGrpPullback ρ₂.P.A ρ₁.P.A (spMap h) ψ → LBIso ρ₂.P.L (ρ₁.P.L.pull ψ) → (∀ E, (ε₂ E).left ≫ ψ = ψ ≫ (ε₁ E).left) → S₁.r * S₁.N ∣ S₂.r * S₂.N → ∃ lab : S₁.Gam →+ S₂.Gam, Same ρ₁ ε₁ ρ₂ ε₂ lab φ ∧ ∀ x : S₂.Gam, ∃ a, lab a = (S₂.r * S₂.N / (S₁.r * S₁.N)) • x := by
  first | exact @GlobalTheory.Poinc.DeepLab.exists_lab_same | exact GlobalTheory.Poinc.DeepLab.exists_lab_same | (intros; apply GlobalTheory.Poinc.DeepLab.exists_lab_same <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.PsiUnit
open GlobalTheory.Poinc.PsiMono
variable {R : Type} [CommRing R] [IsDomain R]

instance isDominant_jK : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap R (FractionRing R))).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))]
    exact bot_le)⟩

theorem data_sep {V : Type} [CommRing V] [IsDomain V] (Q : Data V) : Q.B.left.IsSeparated := by
  have : IsSeparated Q.B.hom := Q.isAb.proper.toIsSeparated
  exact ⟨by rw [← terminal.comp_from Q.B.hom]; infer_instance⟩

theorem jK_cancel {Y : Scheme.{0}} [Y.IsSeparated] {f g : Sp R ⟶ Y} (h : jK R ≫ f = jK R ≫ g) : f = g :=
  ext_of_isDominant (jK R) h

theorem gm_local [IsLocalRing R] {Y : Scheme.{0}} (r : Sp R ⟶ Y) (O : Y.Opens) (hO : r (closedPoint R) ∈ O)
    (a : Γ(Y, O)ˣ) (x : Sp (FractionRing R)) :
    ∃ v : Rˣ, gm (jK R ≫ r) x O a = gm (𝟙 _) x ⊤ (unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom v)) := by
  have htop : (⊤ : (Sp R).Opens) ≤ r ⁻¹ᵁ O := ((IsLocalRing.closedPoint_mem_iff (r ⁻¹ᵁ O)).1 hO).ge
  let b : Γ(Sp R, ⊤)ˣ := res htop (pullU r O a)
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom b, ?_⟩
  have hb : unitOn (Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom b) = b := by
    ext; simp [unitOn]
  rw [← gm_spMap_unitOn, hb, ← gm_pull (jK R) r x O (htop trivial) a, ← gm_res (jK R) x htop trivial]

theorem gs_jK_toOpen (s : R) (hs : algebraMap R (FractionRing R) s ≠ 0) (x : Sp (FractionRing R)) :
    gs (jK R) x ⊤ (DegPre.toOpen (R := R) ⊤ s) = (gm (𝟙 _) x ⊤ (unitOn (Units.mk0 _ hs))).val := by
  rw [← gs_unit (𝟙 _) x ⊤ trivial]
  have h1 := gs_res (jK R) x (le_top : (⊤ : (Sp R).Opens) ≤ ⊤) trivial ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom s)
  refine h1.trans ?_
  have h2 := gs_pull (𝟙 _) (jK R) x ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom s)
  rw [Category.id_comp] at h2
  refine h2.symm.trans (congrArg _ ?_)
  have e := congrArg (fun g => g.hom s) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  simp only [unitOn, Units.val_mk0, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, Units.coe_map]
  exact e.symm

theorem coord_of_val [IsLocalRing R] (D : DegPre R) (χ : D.X) (s : R) (hs : algebraMap R (FractionRing R) s ≠ 0)
    (j : PUnit.{1} → D.P.L.ι) (hj : (⊤ : (Sp R).Opens) ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit))
    (H : ∀ x J', Good D.P.L x J' → J' (D.xK χ) = j PUnit.unit →
      val (D.psi χ) (𝟙 _) x J' = gm (𝟙 _) x ⊤ (unitOn (Units.mk0 _ hs))) : Formalism.L2.Pj.PsiCoord D χ s := by
  have h := GlobalTheory.PsiCoordLocal.generic_le D χ j hj
  refine ⟨j, hj, h, fn_ext fun x hx => ?_⟩
  obtain ⟨J, hJ, eJ⟩ := exists_good D.P.L D.P.isLB x (K := PUnit) (fun _ => D.xK χ) j (fun _ _ _ => rfl)
    (fun k => Set.mem_iInter.1 (h hx) k)
  have e := H x J hJ (eJ PUnit.unit)
  rw [val_of (D.psi χ) _ x J j (fun k => (congrArg J (Category.id_comp (D.xK χ))).trans (eJ k))] at e
  refine (gs_pull (𝟙 _) (jK R) x ⊤ trivial _).trans (Eq.trans ?_ (gs_res (𝟙 _) x h hx _).symm)
  rw [Category.id_comp, gs_jK_toOpen s hs x, gs_unit _ x _ (h hx)]
  exact congrArg Units.val e.symm

theorem exists_good_local [IsLocalRing R] {X : Scheme.{0}} [X.IsSeparated] (L : LB X) (hL : L.IsLB)
    (x : Sp (FractionRing R)) :
    ∃ J : (Sp (FractionRing R) ⟶ X) → L.ι, Good L x J ∧ ∀ g : Sp R ⟶ X, g (closedPoint R) ∈ L.U (J (jK R ≫ g)) := by
  classical
  choose d hd using fun y : X => exists_chart hL y
  refine ⟨fun f => if h : ∃ g : Sp R ⟶ X, f = jK R ≫ g then d (h.choose (closedPoint R)) else d (f x), fun f => ?_,
    fun g => ?_⟩
  · by_cases h : ∃ g : Sp R ⟶ X, f = jK R ≫ g
    · simp only [dif_pos h]
      have htop : (⊤ : (Sp R).Opens) ≤ h.choose ⁻¹ᵁ L.U (d (h.choose (closedPoint R))) :=
        ((IsLocalRing.closedPoint_mem_iff _).1 (hd _)).ge
      have e : f x = h.choose (jK R x) := by
        conv_lhs => rw [h.choose_spec]
        rfl
      rw [e]
      exact htop (show jK R x ∈ (⊤ : (Sp R).Opens) from trivial)
    · simp only [dif_neg h]
      exact hd _
  · have h : ∃ g' : Sp R ⟶ X, jK R ≫ g = jK R ≫ g' := ⟨g, rfl⟩
    simp only [dif_pos h]
    rw [← jK_cancel h.choose_spec]
    exact hd _

theorem val_local [IsLocalRing R] {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp R ⟶ Y) (x : Sp (FractionRing R)) (J : (Sp (FractionRing R) ⟶ X) → L.ι)
    (hJ : ∀ g : Sp R ⟶ X, g (closedPoint R) ∈ L.U (J (jK R ≫ g))) :
    ∃ v : Rˣ, val t (jK R ≫ r) x J = gm (𝟙 _) x ⊤ (unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom v)) :=
  gm_local r _ (Set.mem_iInter.2 fun k => by
    have := hJ (r ≫ φ k)
    show φ k (r (closedPoint R)) ∈ L.U (J ((jK R ≫ r) ≫ φ k))
    rw [Category.assoc]
    exact this) _ x

end GlobalTheory.Poinc.PsiUnit

namespace GlobalTheory.Poinc.Sep
open GlobalTheory.Poinc.PsiMono GlobalTheory.Poinc.PsiUnit

theorem psi_unit_mono : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (Q : Data V) (ρ : V →+* V₁), Function.Injective ρ → ∀ (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ k, t k ≠ 0) → Q.IsMonomialTau t δ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ mu, ∃ u : V₁ˣ, Formalism.L2.Pj.PsiCoord D (e mu) (u * mono W (fun k => ρ (t k)) δ mu) := by
  intro W hW V V₁ _ _ _ _ _ Q ρ hρ m t δ hsym hnn ht hmono D e hS mu
  classical
  obtain ⟨pr, w, -, -, -, -, hw⟩ := hS
  haveI := data_sep Q
  have hL : Q.M.L.IsLB := Q.M.isLB
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.PsiCoordLocal.exists_chart_top.{1} D (e mu)
  choose k hk hcoord using hmono
  choose u hug huv using hcoord
  let f := IsFractionRing.map (K := FractionRing V) (L := FractionRing V₁) hρ
  let x₀ : Sp (FractionRing V₁) := closedPoint (FractionRing V₁)
  obtain ⟨J, hJ, hJc⟩ := exists_good_local Q.M.L hL x₀
  obtain ⟨v₀, hv₀⟩ := gm_local (D.c (e mu)).left _ (by
      refine ⟨Set.mem_iInter.2 fun c => ?_, hj₀ trivial⟩
      have := hJc ((D.c (e mu)).left ≫ lamPts (pr c.1.1) (pr c.1.2) c.2 ≫ pullback.fst Q.B.hom (spMap ρ))
      rw [← Category.assoc] at this
      exact this)
    (w.s (fun c : (Fin 8 × Fin 8) × Fin 4 => J (D.xK (e mu) ≫ lamPts (pr c.1.1) (pr c.1.2) c.2 ≫
      pullback.fst Q.B.hom (spMap ρ)), j₀ PUnit.unit)) x₀
  choose v hv using fun a b => val_local (u a b) (spMap ρ) x₀ J hJc

  have hne : ∀ i, algebraMap V₁ (FractionRing V₁) (ρ (t i)) ≠ 0 := fun i h =>
    ht i (hρ ((IsFractionRing.injective V₁ (FractionRing V₁)) (h.trans (map_zero _).symm) |>.trans (map_zero ρ).symm))
  have hB : algebraMap V₁ (FractionRing V₁) (mono W (fun k => ρ (t k)) δ mu) =
      ∏ i, algebraMap V₁ (FractionRing V₁) (ρ (t i)) ^ qW W (δ i) mu := by
    rw [mono, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow, ← zpow_natCast, Int.toNat_of_nonneg (qW_nonneg hW (hsym i) (hnn i) mu)]
  have hfk : ∀ a b, ((Units.map f.toMonoidHom (k a b) : (FractionRing V₁)ˣ) : FractionRing V₁) =
      ∏ i, algebraMap V₁ (FractionRing V₁) (ρ (t i)) ^ δ i a b := by
    intro a b
    show f (k a b : FractionRing V) = _
    rw [hk a b, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zpow₀]
    simp [f, IsFractionRing.map, IsLocalization.map_eq]
  have hA : ∏ a, ∏ b, ((Units.map f.toMonoidHom (k (mu a) (mu b)) : (FractionRing V₁)ˣ) : FractionRing V₁) ^ W a b =
      ∏ i, algebraMap V₁ (FractionRing V₁) (ρ (t i)) ^ qW W (δ i) mu := by
    simp_rw [hfk]
    have hne' : ∀ c : Fin 8 × Fin 8, ∏ i, algebraMap V₁ (FractionRing V₁) (ρ (t i)) ^ δ i (mu c.1) (mu c.2) ≠ 0 :=
      fun c => Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (hne i)
    have e := prod_zpow_swap (fun i => algebraMap V₁ (FractionRing V₁) (ρ (t i)))
      (fun (c : Fin 8 × Fin 8) i => δ i (mu c.1) (mu c.2)) (fun (c : Fin 8 × Fin 8) => W c.1 c.2) hne'
    rw [Fintype.prod_prod_type] at e
    simp only [Fintype.sum_prod_type] at e
    rw [e]
    rfl

  have htau : ∀ a b, val (Q.tau a b) (fracPt ρ hρ) x₀ J =
      gm (𝟙 _) x₀ ⊤ (unitOn (Units.map f.toMonoidHom (k a b))) *
        gm (𝟙 _) x₀ ⊤ (unitOn (Units.map (algebraMap V₁ (FractionRing V₁)).toMonoidHom (v a b))) := by
    intro a b
    let t₁ := scaleGen (LB.pullGen Q.M.L (lamPts (Q.c a) (Q.c b)) negε (u a b) (toUnit (TK V)).left) (unitOn (k a b))
    have hc : LB.Gen.Corr Q.M.L _ _ _ _ (Q.tau a b) t₁ := corr_of_val hL fun y J₁ hJ₁ => by
      rw [val_scaleGen _ _ _ _ hJ₁, val_pull hJ₁, Category.id_comp]
      exact huv a b y J₁ hJ₁
    rw [val_corr hJ hc (fracPt ρ hρ), val_scaleGen _ _ _ _ hJ, val_pull hJ, ← hv a b]
    congr 1
    · exact gm_spMap_unitOn _ x₀ _
    · show val (u a b) (fracPt ρ hρ ≫ jK V) x₀ J = _
      rw [fracPt_comp]
  let Ψ : (FractionRing V₁)ˣ →* ((Sp (FractionRing V₁)).presheaf.stalk x₀)ˣ :=
    (gm (𝟙 (Sp (FractionRing V₁))) x₀ ⊤).comp
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V₁))).inv.hom.toMonoidHom)
  have hΨ : ∀ U, gm (𝟙 (Sp (FractionRing V₁))) x₀ ⊤ (unitOn U) = Ψ U := fun _ => rfl
  let U₁ : V₁ˣ := v₀ * ∏ a, ∏ b, v (mu a) (mu b) ^ W a b
  have hC : algebraMap V₁ (FractionRing V₁) (U₁ : V₁) =
      algebraMap V₁ _ v₀ * ∏ a, ∏ b, algebraMap V₁ (FractionRing V₁) (v (mu a) (mu b)) ^ W a b := by
    show ((Units.map (algebraMap V₁ (FractionRing V₁)).toMonoidHom U₁ : (FractionRing V₁)ˣ) : FractionRing V₁) = _
    simp only [U₁, map_mul, map_prod, map_zpow, Units.val_mul, Units.coe_prod, Units.val_zpow_eq_zpow_val,
      Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  have hx0 : algebraMap V₁ (FractionRing V₁) ((U₁ : V₁) * mono W (fun k => ρ (t k)) δ mu) ≠ 0 := by
    rw [map_mul, hB]
    exact mul_ne_zero ((U₁.isUnit.map (algebraMap V₁ (FractionRing V₁))).ne_zero)
      (Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (hne i))
  refine ⟨U₁, coord_of_val D (e mu) _ hx0 j₀ hj₀ fun x J' hJ' hJ'e => ?_⟩
  obtain rfl : x = x₀ := Subsingleton.elim (α := PrimeSpectrum (FractionRing V₁)) _ _
  rw [hw (fracPt ρ hρ) (fracPt_comp ρ hρ) mu x₀ J J' hJ hJ', hJ'e]
  erw [hv₀]
  simp only [htau]
  refine Eq.trans (b := Ψ (Units.map (algebraMap V₁ (FractionRing V₁)).toMonoidHom v₀ *
    ∏ a, ∏ b, (Units.map f.toMonoidHom (k (mu a) (mu b)) *
      Units.map (algebraMap V₁ (FractionRing V₁)).toMonoidHom (v (mu a) (mu b))) ^ W a b)) ?_ ?_
  · simp only [map_mul, map_prod, map_zpow]
    rfl
  show Ψ _ = Ψ _
  congr 1
  ext
  simp only [Units.val_mul, Units.coe_prod, Units.val_zpow_eq_zpow_val, Units.coe_map, MonoidHom.coe_coe,
    Units.val_mk0, mul_zpow, Finset.prod_mul_distrib, RingHom.toMonoidHom_eq_coe]
  rw [map_mul, hC, hB, ← hA]
  simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  rw [_root_.mul_comm (∏ a, ∏ b, _ ^ W a b) (∏ a, ∏ b, _ ^ W a b), _root_.mul_assoc]
end GlobalTheory.Poinc.Sep

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_complete_dvr_field_values_deeper_point : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra (FractionRing V) (PadicAlgCl p)], IsAdicComplete (IsLocalRing.maximalIdeal V) V → (∀ x : FractionRing V, ‖algebraMap (FractionRing V) (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) →
  ∃ (V₂ : Type) (_ : CommRing V₂) (_ : IsDomain V₂) (_ : IsDiscreteValuationRing V₂) (_ : Algebra (FractionRing V₂) (PadicAlgCl p)), IsAdicComplete (IsLocalRing.maximalIdeal V₂) V₂ ∧ (∀ x : FractionRing V₂, ‖algebraMap (FractionRing V₂) (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V₂ (FractionRing V₂))) ∧
    ∃ σ : FractionRing V →+* FractionRing V₂, (algebraMap (FractionRing V₂) (PadicAlgCl p)).comp σ = algebraMap (FractionRing V) (PadicAlgCl p) ∧
      ∀ a ∈ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))), D.X.M.val (gPt p ≫ y) a ∈ (algebraMap (FractionRing V₂) (PadicAlgCl p)).range := by
  first | exact @GlobalTheory.Poinc.exists_complete_dvr_values | exact GlobalTheory.Poinc.exists_complete_dvr_values | (intros; apply GlobalTheory.Poinc.exists_complete_dvr_values <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.lieMultiplicity_and_rank_tensorData_lattice : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) , ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∀ T : Tens D.toPre D'.toPre W, ∀ (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) [Module (𝓞 E) D'.toPre.X] (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) → ∀ s : ℕ, r = s * Module.finrank ℚ E → Module.finrank (𝓞 E) D'.toPre.X = s * Module.finrank ℤ D.toPre.X ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (τ : 𝓞 E →+* F), LieMult (letI := H.starRing; ofRingAct o.onB.toRingAct) (spMap ((algebraMap (FractionRing R) F).comp (algebraMap R _))) τ (s * D.toPre.P.g) := by
  first | exact @GlobalTheory.Mum.lieMult_tens | exact GlobalTheory.Mum.lieMult_tens | (intros; apply GlobalTheory.Mum.lieMult_tens <;> assumption)
end
