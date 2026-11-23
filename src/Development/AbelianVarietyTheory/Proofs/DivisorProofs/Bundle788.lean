module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
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
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem sabMap_isOpenImmersion_opensRange (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (j : X' ⟶ X) [IsOpenImmersion j] (m : SABMap t' t j) : ∃ _ : IsOpenImmersion m.φ, m.φ.opensRange = t.G.hom ⁻¹ᵁ j.opensRange := by
  have h : IsPullback m.φ t'.G.hom t.G.hom j := m.cart.1
  have hφ : m.φ = h.isoPullback.hom ≫ pullback.fst t.G.hom j := by simp
  have hi : IsOpenImmersion m.φ := by rw [hφ]; infer_instance
  refine ⟨hi, ?_⟩
  ext1
  have h1 : Set.range m.φ = Set.range (pullback.fst t.G.hom j) := by
    rw [hφ, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr h.isoPullback.hom.surjective, Set.image_univ]
  simpa [h1] using Scheme.Pullback.range_fst t.G.hom j
end GlobalTheory
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.UnitValuedLeadingSection

variable (R : Type) [CommRing R] [IsDomain R]

def thK (z : (TK R).left) : FractionRing R →+* (TK R).left.presheaf.stalk z :=
  ((TK R).left.presheaf.germ ⊤ z trivial).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom

def uK (z : (TK R).left) : Rˣ →* ((TK R).left.presheaf.stalk z)ˣ :=
  Units.map ((thK R z).comp (algebraMap R (FractionRing R))).toMonoidHom

variable {R}

def TopGood (P : PolAV (Spec (CommRingCat.of R))) (z : (TK R).left) (J : ((TK R).left ⟶ P.A.left) → P.L.ι) : Prop :=
  Good P.L z J ∧ ∀ x : Spec (CommRingCat.of R) ⟶ P.A.left, x ≫ P.A.hom = 𝟙 _ → x ⁻¹ᵁ P.L.U (J (jK R ≫ x)) = ⊤

theorem gm_top_unit {R : Type} [CommRing R] [IsDomain R] (V : (Spec (CommRingCat.of R)).Opens) (hV : V = ⊤)
    (v : Γ(Spec (CommRingCat.of R), V)ˣ) (z : (TK R).left) : ∃ u : Rˣ, gm (jK R) z V v = uK R z u := by
  subst hV
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom v, Units.ext ?_⟩
  have hz : jK R z ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) := trivial
  simp only [gm, dif_pos hz]
  have e := congrArg (fun f => f.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (v : Γ(Spec (CommRingCat.of R), ⊤))))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  simp [uK, thK, pullU]
  rw [CommRingCat.hom_ofHom] at e
  have hv : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
      (v : Γ(Spec (CommRingCat.of R), ⊤))) = v := by
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
  rw [e, hv]
  rfl

theorem val_section_unit {R : Type} [CommRing R] [IsDomain R] (P : PolAV (Spec (CommRingCat.of R)))
    (z : (TK R).left) (J : ((TK R).left ⟶ P.A.left) → P.L.ι) (hJ : TopGood P z J) {Y : Scheme.{0}} {K : Type}
    [Fintype K] {φ : K → (Y ⟶ P.A.left)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb P.L φ ε))
    (q : Spec (CommRingCat.of R) ⟶ Y) (hq : ∀ k, (q ≫ φ k) ≫ P.A.hom = 𝟙 _) :
    ∃ u : Rˣ, val t (jK R ≫ q) z J = uK R z u := by
  have htop : q ⁻¹ᵁ LB.wchart P.L φ (fun k => J ((jK R ≫ q) ≫ φ k)) = ⊤ := by
    refine eq_top_iff.2 fun p _ => Set.mem_iInter.2 fun k => ?_
    have h := hJ.2 (q ≫ φ k) (hq k)
    have : p ∈ (q ≫ φ k) ⁻¹ᵁ P.L.U (J (jK R ≫ q ≫ φ k)) := by rw [h]; trivial
    show q p ∈ (φ k) ⁻¹ᵁ P.L.U (J ((jK R ≫ q) ≫ φ k))
    rw [Category.assoc]
    exact this
  have hz : q (jK R z) ∈ LB.wchart P.L φ (fun k => J ((jK R ≫ q) ≫ φ k)) := by
    have : jK R z ∈ q ⁻¹ᵁ LB.wchart P.L φ (fun k => J ((jK R ≫ q) ≫ φ k)) := by rw [htop]; trivial
    exact this
  obtain ⟨u, hu⟩ := gm_top_unit _ htop (pullU q _ (t.s (fun k => J ((jK R ≫ q) ≫ φ k)))) z
  exact ⟨u, (gm_pull (jK R) q z _ hz _).symm.trans hu⟩

theorem exists_topGood (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (P : PolAV (Spec (CommRingCat.of R)))
    (z : (TK R).left) : ∃ J, TopGood P z J := by
  classical
  haveI : IsProper P.A.hom := P.isAb.proper
  haveI : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical
    (algebraMap R (FractionRing R))).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))]
      exact bot_le)⟩
  have hext : ∀ x x' : Spec (CommRingCat.of R) ⟶ P.A.left, x ≫ P.A.hom = 𝟙 _ → x' ≫ P.A.hom = 𝟙 _ →
      jK R ≫ x = jK R ≫ x' → x = x' := fun x x' hx hx' h =>
    ext_of_isDominant_of_isSeparated P.A.hom (hx.trans hx'.symm) (jK R) h
  choose top htop using fun x : Spec (CommRingCat.of R) ⟶ P.A.left =>
    ReciprocityTheory.ChartRestriction.G.DVR.GC.exists_chart_top P.L P.isLB x
  choose d hd using fun φ : (TK R).left ⟶ P.A.left => exists_chart P.isLB (φ z)
  refine ⟨fun φ => if h : ∃ x, x ≫ P.A.hom = 𝟙 _ ∧ jK R ≫ x = φ then top h.choose else d φ,
    fun φ => ?_, fun x hx => ?_⟩
  · by_cases h : ∃ x, x ≫ P.A.hom = 𝟙 _ ∧ jK R ≫ x = φ
    · simp only [dif_pos h]
      have m : jK R z ∈ h.choose ⁻¹ᵁ P.L.U (top h.choose) := by rw [htop]; trivial
      have m' : (jK R ≫ h.choose) z ∈ P.L.U (top h.choose) := m
      rwa [h.choose_spec.2] at m'
    · simp only [dif_neg h]; exact hd φ
  · have h : ∃ x', x' ≫ P.A.hom = 𝟙 _ ∧ jK R ≫ x' = jK R ≫ x := ⟨x, hx, rfl⟩
    simp only [dif_pos h]
    rw [hext _ _ h.choose_spec.1 hx h.choose_spec.2]
    exact htop x

end GlobalTheory.Mum.UnitValuedLeadingSection
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.ActFin

def QHyp {S : Scheme.{0}} (A : Over S) [GrpObj A] (Q : LB (A ⊗ A).left) : Prop :=
  IsAbelianScheme A ∧ Q.IsLB ∧ (∃ t : (Q.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) ∧
    (∃ t : (Q.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) ∧
    LBIso Q (Q.pull (lift (snd A A) (fst A A)).left) ∧ Out.RelAmple A (Q.pull (lift (𝟙 A) (𝟙 A)).left)

def formLB {S : Scheme.{0}} (A : Over S) (Q : LB (A ⊗ A).left) {G : Over S} {r : ℕ} (pr : Fin r → (G ⟶ A))
    (W : Matrix (Fin r) (Fin r) ℤ) : LB G.left :=
  LB.LinComb Q (K := Fin r × Fin r) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)

def diagPow {S : Scheme.{0}} (A : Over S) (Q : LB (A ⊗ A).left) (d : ℤ) : LB A.left :=
  LB.LinComb Q (K := Fin 1) (fun _ => (lift (𝟙 A) (𝟙 A)).left) (fun _ => d)

def sqMap {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} (f : S' ⟶ S) (φ : G'.left ⟶ G.left)
    (w : φ ≫ G.hom = G'.hom ≫ f) : (G' ⊗ G').left ⟶ (G ⊗ G).left :=
  pullback.lift ((fst G' G').left ≫ φ) ((snd G' G').left ≫ φ) (by
    rw [Category.assoc, Category.assoc, w, ← Category.assoc, ← Category.assoc, Over.w (fst G' G'), Over.w (snd G' G')])

theorem isSquare_sqMap {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} (f : S' ⟶ S) (φ : G'.left ⟶ G.left)
    (w : φ ≫ G.hom = G'.hom ≫ f) : IsSquare φ (sqMap f φ w) :=
  ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

theorem isSquare_comp {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} {φ : G'.left ⟶ G.left}
    {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} {φ' : G''.left ⟶ G'.left} {φ₂' : (G'' ⊗ G'').left ⟶ (G' ⊗ G').left}
    (h' : IsSquare φ' φ₂') (h : IsSquare φ φ₂) : IsSquare (φ' ≫ φ) (φ₂' ≫ φ₂) :=
  ⟨by rw [Category.assoc, h.1, ← Category.assoc, h'.1, Category.assoc],
   by rw [Category.assoc, h.2, ← Category.assoc, h'.2, Category.assoc]⟩

theorem isMonHom_prodPow {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {r : ℕ} (f : Fin r → (A ⟶ A))
    (hf : ∀ k, IsMonHom (f k)) (c : Fin r → ℤ) : IsMonHom (∏ k, f k ^ c k) :=
  Finset.prod_induction _ (fun x => IsMonHom x) (fun a b ha hb => by
    haveI := ha; haveI := hb; exact GlobalTheory.Serre.isMonHom_mul a b) GlobalTheory.Serre.isMonHom_one fun k _ => by
    haveI := hf k; exact GlobalTheory.Serre.isMonHom_zpow _ _

theorem powext {S : Scheme.{0}} (A : Over S) (r : ℕ) {X : Scheme.{0}} (a b : X ⟶ (Out.powObj A r).left)
    (h0 : a ≫ (Out.powObj A r).hom = b ≫ (Out.powObj A r).hom)
    (h : ∀ k, a ≫ (Out.powPr A k).left = b ≫ (Out.powPr A k).left) : a = b := by
  have := (Out.powIsLimit A r).hom_ext (W := Over.mk (b ≫ (Out.powObj A r).hom)) (f := Over.homMk a h0)
    (f' := Over.homMk b rfl) (fun ⟨k⟩ => Over.OverMorphism.ext (by simpa using h k))
  exact congrArg (fun m => m.left) this

end GlobalTheory.ActFin
end
end
