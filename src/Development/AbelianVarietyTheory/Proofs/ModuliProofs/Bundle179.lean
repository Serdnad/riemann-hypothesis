module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaSchemeSectionsGoodFibres
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle050
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle177
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle130
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle054
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle140
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle170
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle033
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DeeperLevelBaseModelFiniteOverShallower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle178
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle133
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle113
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfAmpleGeometricFibresAbelianScheme
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

theorem _root_.GlobalTheory.T.exists_model_dominating_models_on_open_cover : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (I : Type) [Finite I] [Nonempty I] (R : I → Type) [∀ i, CommRing (R i)] (a : I → O) (b : ∀ i, O →+* R i) (ω : ∀ i, R i →+* F) (C : ∀ i, Cpt c t (ω i)), IsDedFrac β → (∀ i, IsDedFrac (ω i) ∧ (ω i).comp (b i) = β ∧ @IsLocalization.Away O _ (a i) (R i) _ (b i).toAlgebra) → Ideal.span (Set.range a) = ⊤ → Algebra.FiniteType ℤ O → IsProper t.G.hom → ∃ C' : Cpt c t β, ∀ i, ∃ (f : pullback C'.s (spMap (b i)) ⟶ (C i).X) (t₁ : SAB H (pullback C'.s (spMap (b i)))) (m₁ : SABMap t₁ C'.t (pullback.fst _ _)) (m₂ : SABMap t₁ (C i).t f), f ≫ (C i).s = pullback.snd _ _ ∧ (∀ g : U ⟶ pullback C'.s (spMap (b i)), g ≫ pullback.fst _ _ = C'.j → g ≫ f = (C i).j) ∧ ∀ y : t.G.left ⟶ t₁.G.left, y ≫ m₁.φ = C'.m.φ → y ≫ m₂.φ = (C i).m.φ := by
  first | exact @GlobalTheory.exists_join_of_models | exact GlobalTheory.exists_join_of_models | (intros; apply GlobalTheory.exists_join_of_models <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_theta_scheme_sections_good_fibres : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R), VeryDense (objPrimes b Mat κ β v) → ∃ (Z : Over (Sp R)) (I : Ideal (MvPolynomial (Ix g ((n ^ j) ^ 2)) R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → R), (ProjRep I Z.hom M th ∧ SmoothOfRelativeDimension g Z.hom ∧ GeometricallyConnected Z.hom ∧ (∀ h, SecCoord M th (sc h).left (p h))) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x (v a)) → ∃ φ : t'.A.left ⟶ Z.left, (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left)) := by
  first | exact @GlobalTheory.ZM.FamilyScheme.exists_scheme_sections_fibres | exact GlobalTheory.ZM.FamilyScheme.exists_scheme_sections_fibres | (intros; apply GlobalTheory.ZM.FamilyScheme.exists_scheme_sections_fibres <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.familyUniformisation_of_abelianVariety_uniformisation : ThetaUnifAV → Out.Laws → N1c := by
  first | exact @GlobalTheory.familyUnif_of_thetaUnif | exact GlobalTheory.familyUnif_of_thetaUnif | (intros; apply GlobalTheory.familyUnif_of_thetaUnif <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.BaseModelEx

theorem natCast_ne_zero_of_pt {R k : Type} [CommRing R] [Field k] (y : Sp k ⟶ Sp R) {S : ℕ} (h : IsUnit (S : R)) :
    (S : k) ≠ 0 := by
  have := h.map (Spec.preimage y).hom
  rw [map_natCast] at this
  exact this.ne_zero

theorem natCast_notMem {X : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] (f : X ⟶ Sp R) (g : X ⟶ Sp R')
    {S : ℕ} (h : IsUnit (S : R')) (x : X) : (S : R) ∉ (f x).asIdeal := by
  have h1 : (S : X.residueField x) ≠ 0 := natCast_ne_zero_of_pt (X.fromSpecResidueField x ≫ g) h
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.fromSpecResidueField x ≫ f)
  have h2 : f x = (Spec.map φ) (IsLocalRing.closedPoint _) := by
    rw [hφ]
    exact (congrArg f (Scheme.fromSpecResidueField_apply x (IsLocalRing.closedPoint _))).symm
  rw [h2]
  intro hS
  have h3 : φ.hom (S : R) ∈ IsLocalRing.maximalIdeal (X.residueField x) := hS
  rw [map_natCast, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero] at h3
  exact h3 h1

theorem isUnit_RZ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {S : ℕ} (A : ℕ) (hS : 0 < S) :
    IsUnit (S : RZ H S A) := by
  refine IsUnit.of_mul_eq_one ⟨(S : ℂ)⁻¹, Subring.subset_closure (by simp)⟩ (Subtype.ext ?_)
  have : (S : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hS.ne'
  simp [this]

theorem exists_restrict {Z : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] (s : Z ⟶ Sp R) (b : R →+* R') {S : ℕ}
    [IsOpenImmersion (spMap b)] (hS : IsUnit (S : R'))
    (hr : ∀ x : Sp R, x ∈ Set.range (spMap b) ↔ (S : R) ∉ x.asIdeal) (ρ : Z ⟶ Z) :
    ∃ ρ' : pullback s (spMap b) ⟶ pullback s (spMap b), ρ' ≫ pullback.fst _ _ = pullback.fst _ _ ≫ ρ := by
  refine ⟨IsOpenImmersion.lift (pullback.fst s (spMap b)) (pullback.fst _ _ ≫ ρ) ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨w, rfl⟩
  rw [Scheme.Pullback.range_fst]
  have := natCast_notMem (pullback.fst s (spMap b) ≫ ρ ≫ s) (pullback.snd s (spMap b)) hS w
  rw [Set.mem_preimage, hr]
  simpa using this

theorem pow_hom_eq_iterate {X : Scheme.{0}} (r : Aut X) (m : ℕ) :
    (r ^ m).asIso.hom = (fun f : X ⟶ X => f ≫ r.asIso.hom)^[m] (𝟙 _) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ← ih, pow_succ']; rfl

theorem card_stab_ne_zero {X Y : Scheme.{0}} {Γ : Type} [Group Γ] [Finite Γ] (ρ : Γ →* Aut X) (x : Y ⟶ X) {n J : ℕ}
    (hn : n.Prime) (h : ∀ g, x ≫ (ρ g).asIso.hom = x → g ^ n ^ J = 1) {k : Type} [Field k] (hk : (n : k) ≠ 0) :
    (Nat.card {g // x ≫ (ρ g).asIso.hom = x} : k) ≠ 0 := by
  let P : Subgroup Γ :=
    { carrier := {g | x ≫ (ρ g).asIso.hom = x}
      one_mem' := by
        show x ≫ (ρ 1).asIso.hom = x
        rw [map_one]; exact Category.comp_id x
      mul_mem' := by
        intro a b ha hb
        show x ≫ (ρ (a * b)).asIso.hom = x
        rw [map_mul]
        show x ≫ (ρ b).asIso.hom ≫ (ρ a).asIso.hom = x
        rw [← Category.assoc, show x ≫ (ρ b).asIso.hom = x from hb]; exact ha
      inv_mem' := by
        intro a ha
        show x ≫ (ρ a⁻¹).asIso.hom = x
        rw [map_inv]
        show x ≫ (ρ a).asIso.inv = x
        exact (Iso.comp_inv_eq (ρ a).asIso).mpr (show x ≫ (ρ a).asIso.hom = x from ha).symm }
  haveI : Fact n.Prime := ⟨hn⟩
  have hP : IsPGroup n P := fun g => ⟨J, Subtype.ext (h g.1 g.2)⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hP
  have : Nat.card {g // x ≫ (ρ g).asIso.hom = x} = n ^ m := hm
  rw [this, Nat.cast_pow]
  exact pow_ne_zero _ hk

theorem exists_baseModel : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ (n J : ℕ) (T : Top Xo n (n ^ J)) (l₀ : Level H), AuxiliaryInertOddPrime H n → 1 ≤ J → l₀.A = 1 → Nonempty (BaseModel T l₀) := by
  intro hext L1 L2 L3 E _ _ _ H D Xo hD hN1 n J T l₀ hn hJ hA
  have hnp : n.Prime := hn.1
  have hM : 0 < l₀.M := by have := l₀.three_le; omega
  have hS : 0 < n * l₀.M := Nat.mul_pos hnp.pos hM
  have hN : 0 < n ^ J := pow_pos hnp.pos _
  have hdiv : n ^ J ∣ (n * l₀.M) ^ J := pow_dvd_pow_of_dvd (dvd_mul_right _ _) _
  let l₁ : Level H := { l₀ with A := n ^ J, A_pos := hN }
  have h₁ : l₁.A = n ^ J := rfl
  have R₀ := GlobalTheory.BaseRing.isDedFrac_RZ E H l₀ (n * l₀.M) 0 hS (by simp [hA])
  rw [hA] at R₀
  obtain ⟨⟨β, hβ⟩, ft₀, ded₀⟩ := R₀
  obtain ⟨⟨β₁, hβ₁⟩, ft₁, ded₁⟩ := GlobalTheory.BaseRing.isDedFrac_RZ E H l₁ (n * l₀.M) J hS hdiv
  obtain ⟨⟨b, hb⟩, hb2⟩ := GlobalTheory.T.cmModelCoefficient_inclusions_etale_openImmersion E H (n * l₀.M) (n * l₀.M) 1 (n ^ J) J hS hN dvd_rfl (one_dvd _)
  obtain ⟨bfin, -, -⟩ := (hb2 b hb).1 rfl hdiv
  obtain ⟨⟨b', hb'⟩, hb2'⟩ := GlobalTheory.T.cmModelCoefficient_inclusions_etale_openImmersion E H n (n * l₀.M) (n ^ J) (n ^ J) J hS hN (dvd_mul_right _ _) dvd_rfl
  obtain ⟨bop, brange⟩ := (hb2' b' hb').2 rfl
  obtain ⟨C₁, q, hq, qm, qfin, qj, qφ, qp⟩ := GlobalTheory.T.exists_compactModel_above_fullLevel E H D Xo n (n ^ J) T l₁ h₁ (n * l₀.M) J β₁ b' hS
    (dvd_mul_right _ _) hdiv hβ₁ hb'
  obtain ⟨k, r, ν, hr, hk, lev, -, -, -, -, -, rsurj⟩ := GlobalTheory.T.exists_finite_etale_surjective_levelMap E H D Xo hN1 l₀ l₁
    ⟨dvd_rfl, le_rfl, by rw [hA]; exact one_dvd _⟩
  obtain ⟨Γ, _, _, ρ₀, τ₀, ν₀, inj, quot, hω⟩ := GlobalTheory.T.moduli_level_quotient_by_finite_group L1 L2 L3 E H D Xo hD hN1 l₀ l₁ r ν k hA rfl rfl hk hr lev
  have hU : IsUnit ((n * l₀.M : ℕ) : RZ H (n * l₀.M) (n ^ J)) := isUnit_RZ H _ hS
  obtain ⟨ρ, τ, mu, hact⟩ := GlobalTheory.exists_action_model hext E H _ _ _ (Xo l₁).s (Xo l₁).univ.t β₁ C₁ _
    (pullback.lift q C₁.s hq) Γ ρ₀ τ₀ ν₀ (ded₁ β₁ hβ₁) ft₁ (Xo l₁).univ.proper inferInstance (fun g => (hω g).1) (by
      intro ω
      obtain ⟨h1, -, -, g, σ, h4, h5, h6⟩ := hω ω
      obtain ⟨ρZ, hρZ⟩ := T.sym l₁ h₁ (ρ₀ ω).asIso (ν₀ ω) g σ h4 h5 (by rw [h1]; exact h6)
      obtain ⟨ρ', hρ'⟩ := exists_restrict T.s b' hU brange ρZ.hom
      refine ⟨ρ', ?_⟩
      rw [← cancel_mono (pullback.fst T.s (spMap b'))]
      simp only [Category.assoc, hρ', pullback.lift_fst, pullback.lift_fst_assoc]
      rw [← Category.assoc, qj, hρZ])
  have hover : ∀ (κ : Type) [Field κ] (x : Sp κ ⟶ C₁.X) (ω : Γ), x ≫ (ρ ω).asIso.hom = x →
      (ρ₀ ω).asIso.hom ≫ (Xo l₁).s = (Xo l₁).s := by
    intro κ _ x ω hx
    obtain ⟨-, -, -, g, σ, h4, h5, -⟩ := hω ω
    have := GlobalTheory.galoisPart_eq_refl_of_fixes_point E H D l₁ (Xo l₁) (n * l₀.M) β₁ C₁ (ρ₀ ω).asIso (ρ ω).asIso σ hβ₁ hS ⟨J, hdiv⟩
      (hact ω).2.1 h4 h5 κ x hx
    subst this
    rw [h5]
    exact (congrArg _ (Spec.map_id _)).trans (Category.comp_id _)
  have hφ : ∀ ω, C₁.m.φ ≫ (mu ω).φ = (ν₀ ω).φ ≫ C₁.m.φ := fun ω => by
    rw [(hact ω).1, (hω ω).1]; exact (hact ω).2.2
  have htriv : ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ C₁.X) (ω : Γ), x ≫ (ρ ω).asIso.hom = x →
      pullback.fst C₁.t.G.hom x ≫ (mu ω).φ = pullback.fst C₁.t.G.hom x := by
    intro κ _ _ x ω hx
    exact GlobalTheory.T.finiteOrderAutomorphism_fixing_level_trivial_on_fixedFibre L1 L2 L3 E H D l₁ (Xo l₁) (n * l₀.M) β₁ C₁ (ρ₀ ω).asIso (ν₀ ω) (ρ ω).asIso (mu ω) hβ₁ hS ⟨J, hdiv⟩
      (hact ω).2.1 (hφ ω) (dvd_mul_left _ _) (hover κ x ω hx) (by rw [(hω ω).1]; exact (hω ω).2.2.1)
      ⟨τ ω, Nat.card Γ, Nat.card_pos, by rw [← map_pow, pow_card_eq_one', map_one], (hact ω).1.symm⟩ κ x hx
  have hcard : ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ C₁.X),
      (Nat.card {g // x ≫ (ρ g).asIso.hom = x} : κ) ≠ 0 := by
    intro κ _ _ x
    refine card_stab_ne_zero ρ x (J := J) hnp (fun ω hx => ?_) ?_
    · obtain ⟨h1, -, h3, g, σ, -, -, h6⟩ := hω ω
      have := GlobalTheory.T.iterate_eq_id_of_trivial_on_fixed_fibre L1 L2 L3 E H D l₁ (Xo l₁) (n * l₀.M) β₁ C₁ (ρ₀ ω).asIso (ν₀ ω) (ρ ω).asIso (mu ω) hβ₁ hS ⟨J, hdiv⟩
        (hact ω).2.1 (hφ ω) (hover κ x ω hx) (by rw [h1]; exact h3) g (by rw [h1]; exact h6) κ x hx (htriv κ x ω hx)
      apply inj
      rw [map_pow, map_one]
      exact Aut.ext (Iso.ext ((pow_hom_eq_iterate _ _).trans this))
    · have := natCast_ne_zero_of_pt (x ≫ C₁.s) hU
      rw [Nat.cast_mul] at this
      exact left_ne_zero_of_mul this
  have good₁ : Good C₁.t := good_pullback L3.gtBaseChange E H _ _ T.t C₁.t q qm T.good
  have push := GlobalTheory.T.pushforward_polarisationBundle_invertible_on_model L1 L2 L3 E H D l₁ _ _ _ (baseKA l₁) _ (Xo l₁).s (Xo l₁).univ (Xo l₁).s β₁ C₁
    (ded₁ β₁ hβ₁) good₁.2.2
  have hcomm : β₁.comp b = k.comp β := by
    ext x
    exact (hβ₁ (b x)).trans ((hb x).trans ((hβ x).symm.trans (hk (β x)).symm))
  obtain ⟨C, good, ⟨above⟩⟩ := GlobalTheory.T.exists_quotient_model_by_tame_finite_group E H _ _ _ (Xo l₁).s (Xo l₁).univ.t β₁ _ _ _ (Xo l₀).s (Xo l₀).univ.t β Γ C₁
    b k r ν ρ₀ τ₀ ρ τ mu (ded₁ β₁ hβ₁) (ded₀ β hβ) hcomm bfin hr quot (Xo l₁).univ.proper
    (fun g => ⟨(hact g).1, (hact g).2.1, (hact g).2.2, (hω g).2.1⟩) qp hcard
    (fun κ _ _ x g hx => by rw [← (hact g).1]; exact htriv κ x g hx) good₁ push
  have hcop : (n ^ J).Coprime l₁.M := ((GlobalTheory.T.exists_two_inert_odd_primes_coprime_level E H).2 n hn l₁).pow_left J
  exact ⟨⟨hA, β, hβ, C, good,
    GlobalTheory.T.levelChange_extends_base_model hext L1 L2 L3 E H D Xo n (n ^ J) T hD l₀ l₁ h₁ _ _ β β₁ C C₁ b r ν above b' q hq (ded₀ β hβ)
      (ded₁ β₁ hβ₁) ft₀ bfin qfin qj hA rfl rfl hcop lev rsurj ⟨k, hk, hr, hcomm⟩,
    l₁, rfl, rfl, h₁, β₁, hβ₁, C₁, b, hb, r, ν, lev, rsurj, above, b', hb', q, hq, qfin, qm, qj, qφ⟩⟩

end GlobalTheory.BaseModelEx

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

theorem _root_.GlobalTheory.T.deeper_level_base_model_finite_over_shallower : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l₀' : Level H) (B : BaseModel T l₀) (B' : BaseModel T l₀'), 0 < n → (∃ e, N ∣ n ^ e) → l₀.Dvd l₀' → ∃ (b : RZ H (n * l₀.M) 1 →+* RZ H (n * l₀'.M) 1) (r : (Xo l₀').X ⟶ (Xo l₀).X) (ν : SABMap (Xo l₀').univ.t (Xo l₀).univ.t r), IsInc (RZ H (n * l₀.M) 1).subtype (RZ H (n * l₀'.M) 1).subtype b ∧ LevComp (Xo l₀').univ (Xo l₀).univ r ν ∧ Nonempty (B'.C.Above B.C b r ν) := by
  first | exact @GlobalTheory.BaseTransition.baseModel_above | exact GlobalTheory.BaseTransition.baseModel_above | (intros; apply GlobalTheory.BaseTransition.baseModel_above <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.relAmple_of_ample_geometricFibres_abelianScheme : Out.Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → (∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S), Out.RelAmple (Over.mk (pullback.snd P.A.hom y)) (M.pull (pullback.fst P.A.hom y))) → Out.RelAmple P.A M := by
  first | exact @GlobalTheory.FibreAmple.relAmple_of_geometricFibres | exact GlobalTheory.FibreAmple.relAmple_of_geometricFibres | (intros; apply GlobalTheory.FibreAmple.relAmple_of_geometricFibres <;> assumption)
end
