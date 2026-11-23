module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle695
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle206
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle698
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle529
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle627
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle696
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceUniqueLiftAnyField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle667
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle702
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle700
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle685
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle699
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle693
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle682
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle697
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle668

@[expose] public section

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical


theorem _root_.GlobalTheory.T.flagSpaceComponent_baseMap_of_functionFields : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : C.Y.X ⟶ X.X), f ≫ j = C.π → (∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ j ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x ∧ C.Carries p g) → ∃ φ : X.Fn →ₐ[F] C.Y.Fn, (ratOf X).IsHom (ratOf C.Y) φ f := by
  first | exact @GlobalTheory.FlagBundle.exists_isHom_base_of_lifts | exact GlobalTheory.FlagBundle.exists_isHom_base_of_lifts | (intros; apply GlobalTheory.FlagBundle.exists_isHom_base_of_lifts <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix


theorem _root_.GlobalTheory.T.boundedDomainModelGram_contDiff_isUnit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) {n : ℕ} (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q) (w : ReciprocityTheory.L2DbarEstimates.V n), InDom (coordOf ix w) → ∀ τ, MContDiffAt 2 (fun u => modelGram H Dw (coordOf ix u) τ) w ∧ IsUnit (modelGram H Dw (coordOf ix w) τ).det := by
  first | exact @GlobalTheory.PointChern.modelGram_smooth_isUnit | exact GlobalTheory.PointChern.modelGram_smooth_isUnit | (intros; apply GlobalTheory.PointChern.modelGram_smooth_isUnit <;> assumption)
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GrassKernel

section Esymm

variable (R : Type) [CommRing R] {ι : Type} (m : ι → ℕ)

def blockEsymm : MvPolynomial (Root m) R →ₐ[R] MvPolynomial (Root m) R :=
  aeval fun x : Root m => rename (Sigma.mk x.1) (esymm (Fin (m x.1)) R (x.2 + 1))

theorem split_blockEsymm [DecidableEq ι] (τ₀ : ι) :
    (GlobalTheory.BlockSymm.splitEquiv R τ₀).toAlgHom.comp (blockEsymm R m) =
      ((aeval fun i : Fin (m τ₀) =>
          esymm (Fin (m τ₀)) (MvPolynomial (Root (fun τ : {τ // τ ≠ τ₀} => m τ.1)) R) (i + 1)).restrictScalars R).comp
        ((mapAlgHom (blockEsymm R (fun τ : {τ // τ ≠ τ₀} => m τ.1))).comp
          (GlobalTheory.BlockSymm.splitEquiv R τ₀).toAlgHom) := by
  ext ⟨τ, i⟩ : 1
  by_cases h : τ = τ₀
  · subst h
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, blockEsymm, aeval_X,
      GlobalTheory.BlockSymm.splitEquiv_X_self, mapAlgHom_apply, map_X, AlgHom.restrictScalars_apply]
    have hc : rename (Sigma.mk τ) (esymm (Fin (m τ)) R ((i : ℕ) + 1)) =
        GlobalTheory.BlockSymm.chernRootsOver R m (X (τ, (i : ℕ) + 1)) := by
      simp [GlobalTheory.BlockSymm.chernRootsOver]
    rw [hc, ← GlobalTheory.BlockSymm.splitEquiv_symm_esymm, AlgEquiv.apply_symm_apply]
  · simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, blockEsymm, aeval_X,
      GlobalTheory.BlockSymm.splitEquiv_X_ne R τ₀ h, mapAlgHom_apply, map_C, AlgHom.restrictScalars_apply, aeval_C]

    simp [esymm, map_sum, map_prod, GlobalTheory.BlockSymm.splitEquiv_X_ne R τ₀ h]

end Esymm

theorem blockEsymm_injective (n : ℕ) : ∀ (ι : Type) [Fintype ι], Fintype.card ι = n →
    ∀ (R : Type) [CommRing R] (m : ι → ℕ), Function.Injective (blockEsymm R m) := by
  induction n with
  | zero =>
    intro ι _ hc R _ m
    haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hc
    haveI : IsEmpty (Root m) := ⟨fun x => IsEmpty.false x.1⟩
    intro p q hpq
    rw [eq_C_of_isEmpty p, eq_C_of_isEmpty q] at hpq ⊢
    simp only [blockEsymm, aeval_C, algebraMap_eq] at hpq
    rw [hpq]
  | succ n ih =>
    intro ι _ hc R _ m
    classical
    obtain ⟨τ₀⟩ : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    have hc' : Fintype.card {τ // τ ≠ τ₀} = n := by
      simp [Fintype.card_subtype_compl, hc]
    let R' := MvPolynomial (Root (fun τ : {τ // τ ≠ τ₀} => m τ.1)) R
    have h1 : Function.Injective (aeval (R := R') fun i : Fin (m τ₀) => esymm (Fin (m τ₀)) R' (i + 1)) := by
      intro p q hpq
      apply esymmAlgHom_fin_injective R' (m := m τ₀) (n := m τ₀) le_rfl
      apply Subtype.ext
      rw [esymmAlgHom_apply, esymmAlgHom_apply]
      exact hpq
    have h2 : Function.Injective (mapAlgHom (R := R) (σ := Fin (m τ₀))
        (blockEsymm R (fun τ : {τ // τ ≠ τ₀} => m τ.1))) := by
      intro p q hpq
      exact map_injective _ (ih _ hc' R _) hpq
    have key := split_blockEsymm R m τ₀
    intro p q hpq
    apply (GlobalTheory.BlockSymm.splitEquiv R τ₀).injective
    apply h2
    apply h1
    have := congrArg (fun F => F p) key
    have h' := congrArg (fun F => F q) key
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgHom.restrictScalars_apply] at this h'
    rw [← this, ← h', hpq]

variable {ι : Type} (m : ι → ℕ)

def truncChern : MvPolynomial (ι × ℕ) ℝ →ₐ[ℝ] MvPolynomial (Root m) ℝ :=
  aeval fun x : ι × ℕ =>
    if x.2 = 0 then 1 else if h : x.2 - 1 < m x.1 then X (⟨x.1, ⟨x.2 - 1, h⟩⟩ : Root m) else 0

def liftChern : MvPolynomial (Root m) ℝ →ₐ[ℝ] MvPolynomial (ι × ℕ) ℝ :=
  aeval fun x : Root m => X (x.1, (x.2 : ℕ) + 1)

theorem chernRoots_eq_comp : chernRoots m = (blockEsymm ℝ m).comp (truncChern m) := by
  ext ⟨τ, k⟩ : 1
  simp only [AlgHom.comp_apply, truncChern, aeval_X]
  rcases k with _ | j
  · simp [chernRoots, esymm_zero]
  · by_cases h : j < m τ
    · simp [chernRoots, h, blockEsymm]
    · have hc : (Finset.univ : Finset (Fin (m τ))).card < j + 1 := by simp; omega
      simp [chernRoots, h, esymm, Finset.powersetCard_eq_empty.mpr hc]

def rankIdeal : Ideal (MvPolynomial (ι × ℕ) ℝ) :=
  Ideal.span ((Set.range fun τ : ι => (X (τ, 0) - 1 : MvPolynomial (ι × ℕ) ℝ)) ∪
    {P | ∃ (τ : ι) (k : ℕ), m τ < k ∧ P = X (τ, k)})

theorem mk_liftChern_truncChern :
    (Ideal.Quotient.mkₐ ℝ (rankIdeal m)).comp ((liftChern m).comp (truncChern m)) =
      Ideal.Quotient.mkₐ ℝ (rankIdeal m) := by
  ext ⟨τ, k⟩ : 1
  simp only [AlgHom.comp_apply, truncChern, aeval_X, Ideal.Quotient.mkₐ_eq_mk]
  rcases k with _ | j
  · simp only [if_true, map_one]
    rw [← map_one (Ideal.Quotient.mk (rankIdeal m)), Ideal.Quotient.eq]
    rw [← neg_mem_iff, neg_sub]
    exact Ideal.subset_span (Or.inl ⟨τ, rfl⟩)
  · by_cases h : j < m τ
    · simp [h, liftChern]
    · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, h, dif_neg, not_false_eq_true, map_zero]
      rw [eq_comm, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (Or.inr ⟨τ, j + 1, by omega, rfl⟩)

theorem mem_span_of_chernRoots_eq_zero : ∀ {ι : Type} [Fintype ι] (m : ι → ℕ) (Q : MvPolynomial (ι × ℕ) ℝ),
    chernRoots m Q = 0 → Q ∈ Ideal.span ((Set.range fun τ : ι => (X (τ, 0) - 1 : MvPolynomial (ι × ℕ) ℝ)) ∪
      {P | ∃ (τ : ι) (k : ℕ), m τ < k ∧ P = X (τ, k)}) := by
  intro ι _ m Q hQ
  have h0 : truncChern m Q = 0 := by
    apply blockEsymm_injective _ ι rfl ℝ m
    rw [map_zero, ← AlgHom.comp_apply, ← chernRoots_eq_comp, hQ]
  have h1 := congrArg (fun F => F Q) (mk_liftChern_truncChern m)
  simp only [AlgHom.comp_apply, h0, map_zero, Ideal.Quotient.mkₐ_eq_mk] at h1
  exact (Ideal.Quotient.eq_zero_iff_mem).mp h1.symm

end GlobalTheory.GrassKernel
end
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical


theorem _root_.GlobalTheory.T.fullFlagFrames_flagComponent_pullback_baseFrames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (X : Var F) (j : X.X ⟶ gen Z) (f : C.Y.X ⟶ X.X), f ≫ j = C.π → ∀ (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn), Tied e X j f₀ Eb A₀ → ∀ (φ : X.Fn →ₐ[F] C.Y.Fn), (ratOf X).IsHom (ratOf C.Y) φ f → ∀ (E' : Fr (ratOf C.Y) Dw.mult Dw.mult) (A₁ : Mat Dw.mult C.Y.Fn), Tied e C.Y C.π C.f0 E' A₁ → f₀.Coord (φ : X.Fn →+* C.Y.Fn) C.f0 (A₁ * (A₀.map φ)⁻¹) → ∀ z', ∀ A' ∈ E'.S z', ∀ A ∈ Eb.S (f z'), Par 0 ((ratOf C.Y).O z').toSubring (A' * (A.map φ)⁻¹) := by
  first | exact @GlobalTheory.LieBase.FlagPull.frames_sub | exact GlobalTheory.LieBase.FlagPull.frames_sub | (intros; apply GlobalTheory.LieBase.FlagPull.frames_sub <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical


theorem _root_.GlobalTheory.T.flagSpace_unique_lift_any_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : C.Y.X ⟶ X.X), f ≫ j = C.π → ∀ (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn), Tied e X j f₀ Eb A₀ → (∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ j ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x ∧ C.Carries p g) → ∀ (φ : X.Fn →ₐ[F] C.Y.Fn), (ratOf X).IsHom (ratOf C.Y) φ f → ∀ (E' : Fr (ratOf C.Y) Dw.mult Dw.mult) (A₁ : Mat Dw.mult C.Y.Fn), Tied e C.Y C.π C.f0 E' A₁ → f₀.Coord (φ : X.Fn →+* C.Y.Fn) C.f0 (A₁ * (A₀.map φ)⁻¹) → (∀ z', ∀ A' ∈ E'.S z', ∀ A ∈ Eb.S (f z'), Par 0 ((ratOf C.Y).O z').toSubring (A' * (A.map φ)⁻¹)) → ∀ (K : Type) [Field K] (x : Sp K ⟶ X.X), ∀ A ∈ Eb.S (x (IsLocalRing.closedPoint K)), ∀ h : Mat Dw.mult K, Par 0 ⊤ h → ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x ∧ Bears E' φ A h p := by
  first | exact @GlobalTheory.ShFam.FieldLift.lifts_of_closed | exact GlobalTheory.ShFam.FieldLift.lifts_of_closed | (intros; apply GlobalTheory.ShFam.FieldLift.lifts_of_closed <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

noncomputable section

namespace GlobalTheory.PolCell

open GlobalTheory.PolFan

theorem exists_finite_cover_rcone : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (φ : InvFun ℤ) (N p : ℕ) (P : Fin p → LinearMap.BilinForm ℤ X), IsPolFanOn (id : ℤ → ℤ) φ X → (∀ B ∈ psdCone (bar := (id : ℤ → ℤ)) (X := X), ∃ (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (w : (X × X) →₀ ℤ), IsCone (id : ℤ → ℤ) φ u ∧ StrictWith (id : ℤ → ℤ) φ N (linW w) u ∧ B ∈ rcone u) → (∀ i y z, P i y z = P i z y) → (∀ i y, 0 ≤ P i y y) → ∃ (s : ℕ) (m : Fin s → ℕ) (u : ∀ k, Fin (m k) → LinearMap.BilinForm ℤ X) (w : Fin s → (X × X) →₀ ℤ), (∀ k, IsCone (id : ℤ → ℤ) φ (u k) ∧ StrictWith (id : ℤ → ℤ) φ N (linW (w k)) (u k)) ∧ ∀ B ∈ rcone P, B ∈ psdCone (bar := (id : ℤ → ℤ)) (X := X) → ∃ k, B ∈ rcone (u k) := by
  intro X _ _ φ N p P hφ hcov hsym hpos
  let ι : Type := {x : Σ m : ℕ, (Fin m → LinearMap.BilinForm ℤ X) × ((X × X) →₀ ℤ) //
    IsCone (id : ℤ → ℤ) φ x.2.1 ∧ StrictWith (id : ℤ → ℤ) φ N (linW x.2.2) x.2.1}
  have hnn : ∀ (x : ι) i, 0 ≤ linW x.1.2.2 (P i) := by
    intro x i
    have h1 := x.2.2.2.1 (P i) (mem_balForms_int.2 (hsym i)) (hpos i)
    have h2 := hφ.evalZ_nonneg (mem_balForms_int.2 (hsym i)) (hpos i)
    have : (0 : ℝ) ≤ (linW x.1.2.2 (P i) : ℝ) := le_trans (mul_nonneg (Nat.cast_nonneg _) h2) h1
    exact_mod_cast this
  let f : ι → Fin p → ℕ := fun x i => (linW x.1.2.2 (P i)).toNat
  obtain ⟨F, hF⟩ := GlobalTheory.T.dickson_exists_finite_subfamily_below p f
  let e := F.equivFin
  let g : Fin F.card → ι := fun k => (e.symm k : ι)
  refine ⟨F.card, fun k => (g k).1.1, fun k => (g k).1.2.1, fun k => (g k).1.2.2, fun k => (g k).2, ?_⟩
  intro B hB hBp
  obtain ⟨m, u, w, hc, hs, hBu⟩ := hcov B hBp
  let i₀ : ι := ⟨⟨m, u, w⟩, hc, hs⟩
  obtain ⟨j, hjF, hj⟩ := hF i₀
  refine ⟨e ⟨j, hjF⟩, ?_⟩
  have hg : g (e ⟨j, hjF⟩) = j := by simp [g]
  show B ∈ rcone (g (e ⟨j, hjF⟩)).1.2.1
  rw [hg]
  obtain ⟨t, ht, rfl⟩ := hB
  have A := (GlobalTheory.T.strictlyConcave_polFan_cone_real_forms X φ N m u w hφ hc hs).1 _ hBu
  have C := (GlobalTheory.T.strictlyConcave_polFan_cone_real_forms X φ N j.1.1 j.1.2.1 j.1.2.2 hφ j.2.1 j.2.2).2 _ hBp
  apply C.2
  have hle : evalW j.1.2.2 (∑ i, t i • toReal (P i)) ≤ evalW w (∑ i, t i • toReal (P i)) := by
    rw [evalW_sum, evalW_sum]
    refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (ht i)
    have h1 := hj i
    have h2 := hnn j i
    have h3 := hnn i₀ i
    simp only [f] at h1
    have : linW j.1.2.2 (P i) ≤ linW w (P i) := by
      have h3' : 0 ≤ linW w (P i) := h3
      have h1' : (linW j.1.2.2 (P i)).toNat ≤ (linW w (P i)).toNat := h1
      omega
    exact_mod_cast this
  linarith [C.1]

end GlobalTheory.PolCell
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section
namespace GlobalTheory.PolFan

namespace MultBound
variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  {X₁ : Type} [AddCommGroup X₁] [Module O X₁] {m : ℕ}

theorem cellMult_map {Y : Type} [AddCommGroup Y] [Module O Y] (f : balForms bar X ≃ₗ[ℤ] balForms bar Y)
    (δ : Fin m → balForms bar X) : cellMult bar (fun i => f (δ i)) = cellMult bar δ := by
  unfold cellMult
  have hs : (Submodule.span ℤ (Set.range δ)).map (f : balForms bar X →ₗ[ℤ] balForms bar Y) =
      Submodule.span ℤ (Set.range fun i => f (δ i)) := by
    rw [Submodule.map_span, ← Set.range_comp]; rfl
  let g := Submodule.Quotient.equiv _ _ f hs
  symm
  refine Nat.card_congr (g.toEquiv.subtypeEquiv fun x => ?_)
  simp only [Submodule.mem_torsion_iff]
  refine exists_congr fun a => ?_
  rw [Submonoid.smul_def, Submonoid.smul_def]
  change _ ↔ (a : ℤ) • g x = 0
  rw [← g.map_smul, LinearEquiv.map_eq_zero_iff]

theorem cellMult_le_of_finite (T : Set (balForms bar X)) (hT : T.Finite) :
    ∃ C : ℕ, ∀ (m : ℕ) (δ : Fin m → balForms bar X), (∀ i, δ i ∈ T) → cellMult bar δ ≤ C := by
  classical
  let F : Set (balForms bar X) → ℕ := fun s => Nat.card (Submodule.torsion ℤ (balForms bar X ⧸ Submodule.span ℤ s))
  refine ⟨hT.toFinset.powerset.sup fun s => F ↑s, fun m δ hδ => ?_⟩
  have hr : Set.range δ ⊆ T := Set.range_subset_iff.2 hδ
  have e : Set.range δ = ↑((hT.subset hr).toFinset) := by simp
  have hmem : (hT.subset hr).toFinset ∈ hT.toFinset.powerset :=
    Finset.mem_powerset.2 (Set.Finite.toFinset_subset_toFinset.2 hr)
  show F (Set.range δ) ≤ _
  rw [e]
  exact Finset.le_sup_of_le hmem le_rfl

theorem zsmul_cancel {g : ℤ} (hg : g ≠ 0) {u w : balForms bar X} (h : g • u = g • w) : u = w :=
  Subtype.ext (LinearMap.ext₂ fun a b => by
    have := LinearMap.congr_fun₂ (congrArg Subtype.val h) a b
    simp only [Submodule.coe_smul, LinearMap.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hg this)

theorem prim_eq_of_smul {β β' : balForms bar X} (hβ : IsPrim bar β) (hβ' : IsPrim bar β') {p q : ℕ} (hp : 0 < p)
    (h : p • β = q • β') : β = β' := by
  have hd0 : 0 < Nat.gcd p q := Nat.gcd_pos_of_pos_left _ hp
  obtain ⟨p', q', hcop, hp', hq'⟩ := Nat.exists_coprime p q
  have h' : (p' : ℤ) • β = (q' : ℤ) • β' := by
    refine zsmul_cancel (g := (Nat.gcd p q : ℤ)) (by exact_mod_cast hd0.ne') ?_
    rw [smul_smul, smul_smul, ← Nat.cast_mul, ← Nat.cast_mul, mul_comm, ← hp', mul_comm, ← hq', natCast_zsmul,
      natCast_zsmul]
    exact h
  have hb : ((Nat.gcd p' q' : ℕ) : ℤ) = p' * Nat.gcdA p' q' + q' * Nat.gcdB p' q' := Nat.gcd_eq_gcd_ab p' q'
  rw [hcop, Nat.cast_one] at hb
  set A := Nat.gcdA p' q'
  set B := Nat.gcdB p' q'
  set x : balForms bar X := B • β + A • β'
  have e1 : β = q' • x := by
    rw [← natCast_zsmul, smul_add, smul_smul, smul_smul,
      show ((q' : ℤ) * A) • β' = (A * p') • β by rw [mul_comm, ← smul_smul, ← h', smul_smul], ← add_smul]
    conv_lhs => rw [← one_smul ℤ β]
    congr 1
    rw [hb]; ring
  have e2 : β' = p' • x := by
    rw [← natCast_zsmul, smul_add, smul_smul, smul_smul,
      show ((p' : ℤ) * B) • β = (B * q') • β' by rw [mul_comm, ← smul_smul, h', smul_smul], ← add_smul]
    conv_lhs => rw [← one_smul ℤ β']
    congr 1
    rw [hb]; ring
  have h1 := hβ _ _ e1
  have h2 := hβ' _ _ e2
  rw [e1, e2, h1, h2]

theorem transport [Module.Finite O X] [Module.Finite O X₁] (e : X ≃ₗ[O] X₁) {δ : Fin m → LinearMap.BilinForm ℤ X₁}
    (h : IsCell bar φ δ) (hl : LinearIndependent ℤ δ) (hp : ∀ i, IsPrim bar (⟨δ i, h.mem i⟩ : balForms bar X₁)) :
    ∃ h' : IsCell bar φ (fun i => pull e.toLinearMap (δ i)), LinearIndependent ℤ (fun i => pull e.toLinearMap (δ i)) ∧
      (∀ i, IsPrim bar (⟨_, h'.mem i⟩ : balForms bar X)) ∧
      cellMult bar (fun i => (⟨pull e.toLinearMap (δ i), h'.mem i⟩ : balForms bar X)) =
        cellMult bar (fun i => (⟨δ i, h.mem i⟩ : balForms bar X₁)) := by
  have h' : IsCell bar φ (fun i => pull e.toLinearMap (δ i)) :=
    ⟨fun i => pull_mem _ (h.mem i), fun i _ => h.nonneg i _, (linearOn_pull_iff e.surjective).2 h.linear,
      IsStrict.of_pull (r := e.symm.toLinearMap) e.symm.surjective (by simpa using h.strict)⟩
  have e0 : ∀ i, (pullBalEquiv bar e) ⟨δ i, h.mem i⟩ = ⟨pull e.toLinearMap (δ i), h'.mem i⟩ := fun i => rfl
  have hfam : (fun i => (pullBalEquiv bar e) ⟨δ i, h.mem i⟩) =
      fun i => (⟨pull e.toLinearMap (δ i), h'.mem i⟩ : balForms bar X) := funext e0
  refine ⟨h', ?_, fun i k β' hk => ?_, by rw [← hfam]; exact cellMult_map _ _⟩
  · let P : LinearMap.BilinForm ℤ X₁ →ₗ[ℤ] LinearMap.BilinForm ℤ X :=
      { toFun := pull e.toLinearMap, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    exact hl.map' P (LinearMap.ker_eq_bot.2 fun a b hab => by
      rw [← pull_symm_pull e a, ← pull_symm_pull e b]; exact congrArg _ hab)
  · exact hp i k ((pullBalEquiv bar e).symm β') (by rw [← (pullBalEquiv bar e).symm_apply_apply ⟨δ i, h.mem i⟩, e0, hk]; exact map_nsmul (pullBalEquiv bar e).symm.toAddMonoidHom k β')

theorem perModule [Module.Finite O X] (hF : IsPolyFanOn bar φ X)
    (hpsd : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → toReal β ∈ psdCone (bar := bar) (X := X)) :
    ∃ C : ℕ, ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell bar φ δ), LinearIndependent ℤ δ →
      (∀ i, IsPrim bar (⟨δ i, h.mem i⟩ : balForms bar X)) → cellMult bar (fun i => (⟨δ i, h.mem i⟩ : balForms bar X)) ≤ C := by
  classical
  obtain ⟨S, hS, hcov⟩ := hF.finite
  let T : Set (balForms bar X) :=
    {β | IsPrim bar β ∧ ∃ γ : balForms bar X, γ.1 ∈ S ∧ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a • β = b • γ}
  have hT : T.Finite := by
    have hS' : {γ : balForms bar X | γ.1 ∈ S}.Finite := hS.preimage Subtype.val_injective.injOn
    choose! f hf using fun β (hβ : β ∈ T) => hβ.2
    refine Set.Finite.of_injOn (f := f) (fun β hβ => (hf β hβ).1) (fun β hβ β' hβ' hff => ?_) hS'
    obtain ⟨-, a, b, ha, hb, h1⟩ := hf β hβ
    obtain ⟨-, a', b', ha', hb', h2⟩ := hf β' hβ'
    rw [hff] at h1
    refine prim_eq_of_smul hβ.1 hβ'.1 (p := b' * a) (q := b * a') (by positivity) ?_
    rw [mul_smul, h1, mul_smul, h2, smul_comm]
  obtain ⟨C, hC⟩ := cellMult_le_of_finite T hT
  refine ⟨C, fun m δ h hl hp => ?_⟩
  have hB : toReal (∑ i, δ i) ∈ psdCone (bar := bar) (X := X) := hpsd _ (Submodule.sum_mem _ fun i _ => h.mem i) fun y => by
    simp only [LinearMap.sum_apply]; exact Finset.sum_nonneg fun i _ => h.nonneg i y
  obtain ⟨e, n, γ, c, hγ, hγS, hc, hrel⟩ := hcov _ hB
  obtain ⟨h', hl', hp', hm⟩ := transport e h hl hp
  rw [← hm]
  refine hC m _ fun i => ⟨hp' i, ?_⟩
  have hrel' : ∑ i, toReal (pull e.toLinearMap (δ i)) = ∑ j, c j • toReal (γ j) := by
    rw [← hrel]; ext a b; simp [LinearMap.sum_apply]
  obtain ⟨j, a, b, ha, hb, hab⟩ := GlobalTheory.T.cellGenerator_on_ray_of_linIndep_subcell O bar φ X m n _ γ c h' hγ hl' hc hrel' i
  exact ⟨⟨γ j, hγ.mem j⟩, hγS j, a, b, ha, hb, Subtype.ext (by simpa using hab)⟩

end MultBound


open MultBound in
theorem maxMult_lt_top : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (φ : InvFun (𝓞 E)), IsPolyFan H.bar q φ → maxMult H.bar q φ < ⊤ := by
  intro E _ _ _ H q φ hφ
  obtain ⟨n, Y, hY⟩ := GlobalTheory.T.finitely_many_iso_classes_projective_numberField E q
  have hb : ∀ k : Fin n, ∃ C : ℕ, ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X]
      [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → Nonempty (X ≃ₗ[𝓞 E] Y k) → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell H.bar φ δ),
      LinearIndependent ℤ δ → (∀ i, IsPrim H.bar (⟨δ i, h.mem i⟩ : balForms H.bar X)) →
      cellMult H.bar (fun i => (⟨δ i, h.mem i⟩ : balForms H.bar X)) ≤ C := by
    intro k
    by_cases hk : ∃ (X : Type) (_ : AddCommGroup X) (_ : Module (𝓞 E) X) (_ : Module.Finite (𝓞 E) X)
      (_ : Module.Projective (𝓞 E) X), Module.finrank (𝓞 E) X ≤ q ∧ Nonempty (X ≃ₗ[𝓞 E] Y k)
    · obtain ⟨X, _, _, _, _, hX, ⟨e⟩⟩ := hk
      haveI : Module.Finite (𝓞 E) (Y k) := Module.Finite.equiv e
      haveI : Module.Projective (𝓞 E) (Y k) := Module.Projective.of_equiv e
      have hYr : Module.finrank (𝓞 E) (Y k) ≤ q := e.finrank_eq ▸ hX
      obtain ⟨C, hC⟩ := perModule (hφ (Y k) hYr) (GlobalTheory.T.intBilinFormToReal_mem_balancedPsdCone E H (Y k))
      refine ⟨C, fun X' _ _ _ _ _ he' m δ h hl hp => ?_⟩
      obtain ⟨e'⟩ := he'
      obtain ⟨h', hl', hp', hc⟩ := transport e'.symm h hl hp
      rw [← hc]
      exact hC m _ h' hl' hp'
    · exact ⟨0, fun X _ _ _ _ hX he => (hk ⟨X, _, _, inferInstance, inferInstance, hX, he⟩).elim⟩
  choose C hC using hb
  refine lt_of_le_of_lt (b := ((Finset.univ.sup C : ℕ) : ℕ∞)) ?_ (ENat.coe_lt_top _)
  unfold maxMult
  refine iSup_le fun X => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun hX =>
    iSup_le fun m => iSup_le fun δ => iSup_le fun h => iSup_le fun hl => iSup_le fun hp => ?_
  obtain ⟨k, he⟩ := hY X hX
  exact_mod_cast (hC k X hX he m δ h hl hp).trans (Finset.le_sup (Finset.mem_univ k))

end GlobalTheory.PolFan
end
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

namespace GlobalTheory.PolFan.Mark

theorem evalZ_eq_sum_of_toReal_eq_addcone {O : Type} [CommRing O] (ψ : InvFun O) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m : ℕ} {v : Fin m → LinearMap.BilinForm ℤ X} (hv : ψ.LinearOn v)
    {β : LinearMap.BilinForm ℤ X} {c : Fin m → ℝ} (hc : ∀ i, 0 ≤ c i)
    (h : toReal β = ∑ i, c i • toReal (v i)) : ψ.evalZ β = ∑ i, c i * ψ.evalZ (v i) := by
  rw [← hv c hc]
  unfold InvFun.evalZ
  congr 1
  funext a b
  have := LinearMap.congr_fun₂ h a b
  simpa [LinearMap.sum_apply] using this

theorem evalZ_add_of_linearOn_inRCone (O : Type) [CommRing O] (ψ : InvFun O) (X : Type) [AddCommGroup X] [Module O X]
    [Module.Finite O X] (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X) (hv : ψ.LinearOn v)
    (β x : LinearMap.BilinForm ℤ X) (hβ : InRCone v β) (hx : InRCone v x) :
    ψ.evalZ (β + x) = ψ.evalZ β + ψ.evalZ x := by
  obtain ⟨a, ha, hβ⟩ := hβ
  obtain ⟨b, hb, hx⟩ := hx
  have hs : toReal (β + x) = ∑ i, (a i + b i) • toReal (v i) := by
    have : toReal (β + x) = toReal β + toReal x := LinearMap.ext₂ fun s t => by simp
    rw [this, hβ, hx, ← Finset.sum_add_distrib]
    simp only [add_smul]
  rw [evalZ_eq_sum_of_toReal_eq_addcone ψ hv (fun i => add_nonneg (ha i) (hb i)) hs,
    evalZ_eq_sum_of_toReal_eq_addcone ψ hv ha hβ, evalZ_eq_sum_of_toReal_eq_addcone ψ hv hb hx,
    ← Finset.sum_add_distrib]
  simp only [add_mul]

end GlobalTheory.PolFan.Mark
end
end
