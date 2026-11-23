module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle003
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle030
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle031
public import Mathlib.AlgebraicGeometry.Noetherian
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeGlueOverPrimes
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.LatticesAgreeOfHeightOne
public import Mathlib.RingTheory.Ideal.Height
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle014
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle032
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.EvalPt

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem aeval_div_mul_prod {F : Type} [Field F] (v : (Σ k, J k) → F) (t : K → F) (ht : ∀ k, t k ≠ 0)
    {g : MRing J} {d : K → ℕ} (hg : IsMultiHomog g d) :
    aeval (fun p => v p / t p.1) g * ∏ k, t k ^ d k = aeval v g := by
  simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [mul_assoc]
  congr 1
  have key : ∏ k, t k ^ d k = ∏ p : (Σ k, J k), t p.1 ^ m p := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    dsimp only
    rw [Finset.prod_pow_eq_pow_sum, hg m hm k]
  rw [key, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ (ht p.1))]

theorem map_aeval_int {σ S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (s : σ → S) (f : MvPolynomial σ ℤ) :
    φ (aeval s f) = aeval (fun i => φ (s i)) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem norm_evC_of_specializes {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {y : (Σ k, J k) → Ω} {z : Spec (CommRingCat.of ℂ) ⟶ X} {w : (Σ k, J k) → ℂ} {A : HermLine J} {c₀ : Ω} {C : ℝ}
    {g h : MRing J} {dg dh : K → ℕ} (hz : genPt ξ ⤳ centre z) (hco : CoordsAt ξ y z w)
    (hyp : ∀ (cc : (k : K) → J k) (u : ℂ), (∀ k, w ⟨k, cc k⟩ ≠ 0) →
      ValAt ξ z (c₀ / ∏ k, y ⟨k, cc k⟩ ^ A.a k) u → ‖u‖ * ∏ k, ‖w ⟨k, cc k⟩‖ ^ A.a k = C * A.h w)
    (hg : IsMultiHomog g dg) (hh : IsMultiHomog h dh) (hd : ∀ k, (dg k : ℤ) - dh k = A.a k)
    (he : aeval y g = c₀ * aeval y h) (hw : evC w h ≠ 0) :
    ‖evC w g‖ = C * A.h w * ‖evC w h‖ := by
  classical
  obtain ⟨hcov, hco2⟩ := hco
  choose cc hcc using hcov
  have hw0 : ∀ k, w ⟨k, cc k⟩ ≠ 0 := fun k => (hcc k).ne_zero
  have hy0 : ∀ k, y ⟨k, cc k⟩ ≠ 0 := fun k => (hco2 k (cc k) (hcc k)).1
  have hr : ∀ p : (Σ k, J k), ∃ s : X.presheaf.stalk (centre z),
      genMap ξ ⟨centre z, hz⟩ s = y p / y ⟨p.1, cc p.1⟩ ∧
      w p = (Scheme.stalkClosedPointTo z).hom s * w ⟨p.1, cc p.1⟩ := by
    rintro ⟨k, i⟩
    obtain ⟨r, ⟨h', s, hs1, hs2⟩, hwr⟩ := (hco2 k (cc k) (hcc k)).2 i
    exact ⟨s, hs1, by rw [hwr, ← hs2]⟩
  choose s hs1 hs2 using hr
  have hφ1 : ∀ f : MRing J, genMap ξ ⟨centre z, hz⟩ (aeval s f) =
      aeval (fun p => y p / y ⟨p.1, cc p.1⟩) f := by
    intro f
    rw [map_aeval_int]
    simp only [hs1]
  have hwr : ∀ p : (Σ k, J k), w p / w ⟨p.1, cc p.1⟩ = (Scheme.stalkClosedPointTo z).hom (s p) := fun p => by
    rw [hs2 p, mul_div_cancel_right₀ _ (hw0 p.1)]
  have hφ2 : ∀ f : MRing J, (Scheme.stalkClosedPointTo z).hom (aeval s f) =
      aeval (fun p => w p / w ⟨p.1, cc p.1⟩) f := by
    intro f
    refine (map_aeval_int (Scheme.stalkClosedPointTo z).hom s f).trans ?_
    simp only [← hwr]
    try rfl
  have hev : ∀ f : MRing J, evC w f = aeval w f := fun f => by
    simp only [evC, MvPolynomial.eval_map, MvPolynomial.aeval_def, algebraMap_int_eq]
  have hg1 : aeval (fun p => w p / w ⟨p.1, cc p.1⟩) g * ∏ k, w ⟨k, cc k⟩ ^ dg k = aeval w g :=
    aeval_div_mul_prod w (fun k => w ⟨k, cc k⟩) hw0 hg
  have hh1 : aeval (fun p => w p / w ⟨p.1, cc p.1⟩) h * ∏ k, w ⟨k, cc k⟩ ^ dh k = aeval w h :=
    aeval_div_mul_prod w (fun k => w ⟨k, cc k⟩) hw0 hh
  have hg2 : aeval (fun p => y p / y ⟨p.1, cc p.1⟩) g * ∏ k, y ⟨k, cc k⟩ ^ dg k = aeval y g :=
    aeval_div_mul_prod y (fun k => y ⟨k, cc k⟩) hy0 hg
  have hh2 : aeval (fun p => y p / y ⟨p.1, cc p.1⟩) h * ∏ k, y ⟨k, cc k⟩ ^ dh k = aeval y h :=
    aeval_div_mul_prod y (fun k => y ⟨k, cc k⟩) hy0 hh
  rw [hev, hev] at *
  set Pg := aeval (fun p => w p / w ⟨p.1, cc p.1⟩) g with hPg
  set Ph := aeval (fun p => w p / w ⟨p.1, cc p.1⟩) h with hPh
  set Qg := aeval (fun p => y p / y ⟨p.1, cc p.1⟩) g with hQg
  set Qh := aeval (fun p => y p / y ⟨p.1, cc p.1⟩) h with hQh
  have hTg : ∏ k, w ⟨k, cc k⟩ ^ dg k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hw0 k)
  have hTh : ∏ k, w ⟨k, cc k⟩ ^ dh k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hw0 k)
  have hYg : ∏ k, y ⟨k, cc k⟩ ^ dg k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy0 k)
  have hYh : ∏ k, y ⟨k, cc k⟩ ^ dh k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy0 k)
  have hPh0 : Ph ≠ 0 := by
    intro h0
    apply hw
    rw [← hh1, h0, zero_mul]
  have hunit : IsUnit (aeval s h : X.presheaf.stalk (centre z)) :=
    isUnit_of_map_unit (Scheme.stalkClosedPointTo z).hom _ (by rw [hφ2]; exact hPh0.isUnit)
  have hQh0 : Qh ≠ 0 := by
    have := (hunit.map (genMap ξ ⟨centre z, hz⟩)).ne_zero
    rwa [hφ1] at this
  have hyh0 : aeval y h ≠ 0 := by
    rw [← hh2]
    exact mul_ne_zero hQh0 hYh
  have hval : ValAt ξ z (c₀ / ∏ k, y ⟨k, cc k⟩ ^ A.a k) (Pg / Ph) := by
    refine ⟨hz, aeval s g * ↑hunit.unit⁻¹, ?_, ?_⟩
    · rw [map_mul, map_units_inv, IsUnit.unit_spec, hφ1, hφ1]
      have hpow : ∏ k, y ⟨k, cc k⟩ ^ A.a k = (∏ k, y ⟨k, cc k⟩ ^ dg k) / ∏ k, y ⟨k, cc k⟩ ^ dh k := by
        rw [← Finset.prod_div_distrib]
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [← hd k, zpow_sub₀ (hy0 k), zpow_natCast, zpow_natCast]
      have hc0 : c₀ = (Qg * ∏ k, y ⟨k, cc k⟩ ^ dg k) / (Qh * ∏ k, y ⟨k, cc k⟩ ^ dh k) := by
        rw [hg2, hh2, he, mul_div_assoc, div_self hyh0, mul_one]
      rw [hpow, hc0, ← hQg, ← hQh]
      field_simp
      try ring
    · have hq : (aeval s g * ↑hunit.unit⁻¹ : X.presheaf.stalk (centre z)) * aeval s h = aeval s g := by
        rw [mul_assoc, Units.inv_mul_of_eq hunit.unit_spec, mul_one]
      have key2 := (RingHom.map_mul (Scheme.stalkClosedPointTo z).hom _ _).symm.trans
        (congrArg (Scheme.stalkClosedPointTo z).hom hq)
      rw [hφ2, hφ2] at key2
      exact (eq_div_iff hPh0).2 key2
  have key := hyp cc (Pg / Ph) hw0 hval
  have hnpow : ∏ k, ‖w ⟨k, cc k⟩‖ ^ A.a k =
      (∏ k, ‖w ⟨k, cc k⟩‖ ^ dg k) / ∏ k, ‖w ⟨k, cc k⟩‖ ^ dh k := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← hd k, zpow_sub₀ (norm_ne_zero_iff.2 (hw0 k)), zpow_natCast, zpow_natCast]
  have hnh : ∏ k, ‖w ⟨k, cc k⟩‖ ^ dh k ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (norm_ne_zero_iff.2 (hw0 k))
  have hPhn : ‖Ph‖ ≠ 0 := norm_ne_zero_iff.2 hPh0
  rw [← key, ← hg1, ← hh1, hnpow, norm_mul, norm_mul, norm_div, norm_prod, norm_prod]
  simp only [norm_pow]
  field_simp
  try ring

theorem norm_evC_of_forms : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] [Nonempty K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ) (A : HermLine J) (c₀ : Ω) (C : ℝ) (g h : MRing J) (dg dh : K → ℕ), IsCptGen ξ → CoordsAt ξ y z w → (∀ (cc : (k : K) → J k) (u : ℂ), (∀ k, w ⟨k, cc k⟩ ≠ 0) → ValAt ξ z (c₀ / ∏ k, y ⟨k, cc k⟩ ^ A.a k) u → ‖u‖ * ∏ k, ‖w ⟨k, cc k⟩‖ ^ A.a k = C * A.h w) → IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) - dh k = A.a k) → aeval y g = c₀ * aeval y h → evC w h ≠ 0 → ‖evC w g‖ = C * A.h w * ‖evC w h‖ := by
  intro X Ω _ ξ K _ _ J _ y z w A c₀ C g h dg dh _ hco hyp hg hh hd he hw
  obtain ⟨k⟩ := ‹Nonempty K›
  obtain ⟨c, hc⟩ := hco.1 k
  obtain ⟨r, ⟨hz, _⟩, _⟩ := (hco.2 k c hc).2 c
  exact norm_evC_of_specializes hz hco hyp hg hh hd he hw

end GlobalTheory.CompanionTheory.Ar.Flat.EvalPt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lie_model_pullback_map : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (G : Over X) (G' : Over X') [GrpObj G] [GrpObj G'] (φ : G'.left ⟶ G.left) (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (M : LieModel G ξ V) (M' : LieModel G' ξ' V'), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → IsGrpPullback G' G f φ → ∃ j : V →+ V', ∀ e, (M'.pt (j e)).left ≫ φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M.pt e).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieJ.exists_map | exact GlobalTheory.CompanionTheory.Ar.LieJ.exists_map | (intros; apply GlobalTheory.CompanionTheory.Ar.LieJ.exists_map <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagStep

theorem lieMap_act_pull (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X)
    (t' : SAB H X') (f : X' ⟶ X) (m : SABMap t' t f) (Ω Ω' : Type) [Field Ω] [Field Ω']
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω')
    (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V']
    (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ' V') (ρ : 𝓞 E →+* Module.End Ω V) (ρ' : 𝓞 E →+* Module.End Ω' V')
    (j : V →+ V') : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → M.IsActOf t.act.act ρ → M'.IsActOf t'.act.act ρ' →
    (∀ e, (M'.pt (j e)).left ≫ m.φ = spMap (dualMap i) ≫ (M.pt e).left) →
    ∀ a e, j (ρ a e) = ρ' a (j e) := by
  intro _ ha ha' hj a e
  have hcanc : ∀ v w : epsAt ξ' ⟶ t'.G, v.left ≫ m.φ = w.left ≫ m.φ → v = w := by
    intro v w h
    apply Over.OverMorphism.ext
    refine m.cart.1.hom_ext h ?_
    rw [Over.w v, Over.w w]
  apply M'.inj
  refine hcanc _ _ ?_
  rw [ha' a (j e), hj, ha a e, Over.comp_left, Over.comp_left, Category.assoc, m.act a]
  have h2 := congrArg (· ≫ (t.act.act a).left) (hj e)
  simp only [Category.assoc] at h2 ⊢
  exact h2.symm

end GlobalTheory.CompanionTheory.Ar.FlagStep
end
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.frame_change_by_unit_matrix : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (r : ℕ) (β : Fin r → E) (q : Cpt ξ) (P : Matrix (Fin r) (Fin r) Ω), L.IsFrameAt β q → (∀ a b, P a b ∈ regAt ξ q) → unitAt ξ q P.det → L.IsFrameAt (fun k => ∑ a, P a k • β a) q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.isFrameAt_matrix_comb | exact GlobalTheory.CompanionTheory.Ar.FlagBun.isFrameAt_matrix_comb | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.isFrameAt_matrix_comb <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.proper_dominating_surjective : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) [Finite κ] (x : κ → Ω) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (s' : X' ⟶ Spec (CommRingCat.of ℤ)) (f : X' ⟶ X) (i : Ω →+* Ω'), CoordTie ℤ ξ x → (∀ q : X, genPt ξ ⤳ q) → IsProper s' → Dominates ξ' ξ f i → Function.Surjective f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.surjective_of_dominates | exact GlobalTheory.CompanionTheory.Ar.FlagBun.surjective_of_dominates | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.surjective_of_dominates <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lattice_glue_over_primes : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] [CharZero Ω] [IsLocallyNoetherian X] (S : Finset ℕ) (L₀ : Lat ξ E) (Lp : ℕ → Lat ξ E) (r : ℕ) (V : Submodule Ω E), IsCptGen ξ → (∀ l ∈ S, l.Prime) → L₀.IsVBOn {q | ∀ l ∈ S, ¬ InFibre ξ l q} r V → (∀ l ∈ S, (Lp l).IsVBOn {q | ∀ l' : ℕ, l'.Prime → l' ≠ l → ¬ InFibre ξ l' q} r V) → (∀ l ∈ S, ∀ q : Cpt ξ, (∀ l' : ℕ, l'.Prime → ¬ InFibre ξ l' q) → Lp l q = L₀ q) → ∃ L : Lat ξ E, L.IsVB r V ∧ (∀ q : Cpt ξ, (∀ l ∈ S, ¬ InFibre ξ l q) → L q = L₀ q) ∧ ∀ l ∈ S, ∀ q : Cpt ξ, InFibre ξ l q → L q = Lp l q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lat_glue | exact GlobalTheory.CompanionTheory.Ar.lat_glue | (intros; apply GlobalTheory.CompanionTheory.Ar.lat_glue <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar

theorem lat_agree_of_height_one : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [IsLocallyNoetherian X], IsCptGen ξ → ∀ (T : Set (Cpt ξ)), (∀ p ∈ T, ∀ q : Cpt ξ, q.1 ⤳ p.1 → q ∈ T) → (∀ p ∈ T, IsIntegrallyClosed (X.presheaf.stalk p.1)) → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (L L' : Lat ξ E) (r : ℕ) (V : Submodule Ω E), L.IsVBOn T r V → L'.IsVBOn T r V → (∀ p ∈ T, ringKrullDim (X.presheaf.stalk p.1) = 1 → L p = L' p) → ∀ p ∈ T, L p = L' p :=
  @PositivityTheory.UnitarySelfGeneration.lattices_agree_of_height_one

end GlobalTheory.CompanionTheory.Ar
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

theorem evC_conj {K : Type} {ι : K → Type} (z : (Σ k, ι k) → ℂ) (g : MRing ι) :
    evC (fun p => (starRingEnd ℂ) (z p)) g = (starRingEnd ℂ) (evC z g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [evC]
  | add p q hp hq =>
    simp only [evC, Polynomial.map_add (f := _), map_add (f := _)] at hp hq ⊢
    rw [hp, hq]
  | mul_X p i hp =>
    simp only [evC, map_mul, map_X, eval_X] at hp ⊢
    rw [hp]

theorem ptOver_conj : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type)
    [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (σ : F →+* ℂ) (z : (Σ k, ι k) → ℂ),
    PtOver y φ σ z → PtOver y φ (ComplexEmbedding.conjugate σ) (fun p => (starRingEnd ℂ) (z p)) := by
  intro K _ ι _ Ω _ F _ _ y φ σ z h
  obtain ⟨⟨hne, hvan⟩, hrel⟩ := h
  refine ⟨⟨fun k => ?_, fun f hf => ?_⟩, fun a d g h' hg hh e => ?_⟩
  · obtain ⟨i, hi⟩ := hne k
    exact ⟨i, by simpa using hi⟩
  · have := evC_conj z f
    have h0 : evC z f = 0 := hvan f hf
    rw [h0, map_zero] at this
    exact this
  · rw [evC_conj, evC_conj, hrel a d g h' hg hh e, map_mul, ComplexEmbedding.conjugate_coe_eq]

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_point_of_prime {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (h : IsCptGen ξ) (p : Cpt ξ) (P : Ideal (regAt ξ p)) (hP : P.IsPrime) :
    ∃ q : Cpt ξ, q.1 ⤳ p.1 ∧ ringKrullDim (X.presheaf.stalk q.1) = (P.height : WithBot ℕ∞) ∧
      ∀ a ∈ regAt ξ q, ∃ s t : regAt ξ p, s ∉ P ∧ a * s = t := by
  obtain ⟨U, hU, hp, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := p.1) (U := ⊤) trivial
  have hg : genPt ξ ∈ U := p.2.mem_open U.2 hp
  let e := RegAtRing.stalkEquiv h p
  let P' : Ideal (X.presheaf.stalk p.1) := P.comap (e : X.presheaf.stalk p.1 →+* regAt ξ p)
  have hP' : P'.IsPrime := Ideal.comap_isPrime _ _
  letI algP := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨p.1, hp⟩ : U)
  have localization₂ := hU.isLocalization_stalk ⟨p.1, hp⟩
  let 𝔮 : Ideal Γ(X, U) := P'.comap (algebraMap Γ(X, U) (X.presheaf.stalk p.1))
  have h𝔮 : 𝔮.IsPrime := Ideal.comap_isPrime _ _
  let y : PrimeSpectrum Γ(X, U) := ⟨𝔮, h𝔮⟩
  have hyU : hU.fromSpec y ∈ U := by
    have : hU.fromSpec y ∈ Set.range hU.fromSpec := ⟨y, rfl⟩
    rwa [hU.range_fromSpec] at this

  have hsp : hU.fromSpec y ⤳ p.1 := by
    have hle : y ≤ hU.primeIdealOf ⟨p.1, hp⟩ := by
      change 𝔮 ≤ (hU.primeIdealOf ⟨p.1, hp⟩).asIdeal
      rw [← IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk p.1)
        (hU.primeIdealOf ⟨p.1, hp⟩).asIdeal]
      exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal hP'.ne_top)
    have := ((PrimeSpectrum.le_iff_specializes _ _).1 hle).map hU.fromSpec.continuous
    rwa [hU.fromSpec_primeIdealOf] at this

  have hgy : genPt ξ ⤳ hU.fromSpec y := by
    have hle : hU.primeIdealOf ⟨genPt ξ, hg⟩ ≤ y := by
      change (hU.primeIdealOf ⟨genPt ξ, hg⟩).asIdeal ≤ 𝔮
      intro r hr
      letI algG := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨genPt ξ, hg⟩ : U)
      have locG := hU.isLocalization_stalk ⟨genPt ξ, hg⟩
      have hnu : ¬ IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk (genPt ξ)) r) := by
        rw [← IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk (genPt ξ))
          (hU.primeIdealOf ⟨genPt ξ, hg⟩).asIdeal] at hr
        exact (IsLocalRing.mem_maximalIdeal _).1 hr
      have hz : (Scheme.stalkClosedPointTo ξ).hom
          (X.presheaf.germ U (genPt ξ) hg r) = 0 := by
        by_contra hne
        obtain ⟨w, hw⟩ := h.bij.2 ((Scheme.stalkClosedPointTo ξ).hom
          (X.presheaf.germ U (genPt ξ) hg r))⁻¹
        apply hnu
        refine IsUnit.of_mul_eq_one w (h.bij.1 ?_)
        erw [map_mul, hw, map_one]
        exact mul_inv_cancel₀ hne
      have hz' : X.presheaf.germ U p.1 hp r = 0 := by
        apply h.inj p
        rw [RegAtRing.genMap_germ p U hp hg, hz, map_zero]
      change algebraMap Γ(X, U) (X.presheaf.stalk p.1) r ∈ P'
      erw [hz']
      exact P'.zero_mem
    have := ((PrimeSpectrum.le_iff_specializes _ _).1 hle).map hU.fromSpec.continuous
    rwa [hU.fromSpec_primeIdealOf] at this
  letI algY : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨hU.fromSpec y, hyU⟩ : U)
  have locY : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec y)) y.asIdeal :=
    hU.isLocalization_stalk' y hyU
  have locY' : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec y)) 𝔮 := locY
  refine ⟨⟨hU.fromSpec y, hgy⟩, hsp, ?_, ?_⟩
  · have h1 : ringKrullDim (X.presheaf.stalk (hU.fromSpec y)) = (𝔮.height : WithBot ℕ∞) :=
      IsLocalization.AtPrime.ringKrullDim_eq_height 𝔮 (X.presheaf.stalk (hU.fromSpec y))
    have h2 : 𝔮.height = P'.height :=
      IsLocalization.height_under (hU.primeIdealOf ⟨p.1, hp⟩).asIdeal.primeCompl P'
    have h3 : P'.height = P.height := RingEquiv.height_comap e P
    change ringKrullDim (X.presheaf.stalk (hU.fromSpec y)) = _
    rw [h1, h2, h3]
  · rintro _ ⟨x, rfl⟩
    obtain ⟨⟨r, t⟩, he⟩ := IsLocalization.surj y.asIdeal.primeCompl
      (S := X.presheaf.stalk (hU.fromSpec y)) x
    have he' : x * (X.presheaf.germ U (hU.fromSpec y) hyU).hom t.1 =
        (X.presheaf.germ U (hU.fromSpec y) hyU).hom r := he
    have hgt := RegAtMono.genMap_germ_eq ξ p ⟨hU.fromSpec y, hgy⟩ hsp U hp hyU
    refine ⟨e ((X.presheaf.germ U p.1 hp).hom t.1), e ((X.presheaf.germ U p.1 hp).hom r), ?_, ?_⟩
    · exact t.2
    · change genMap ξ ⟨hU.fromSpec y, hgy⟩ x * genMap ξ p ((X.presheaf.germ U p.1 hp).hom t.1) =
        genMap ξ p ((X.presheaf.germ U p.1 hp).hom r)
      rw [← hgt, ← hgt, ← map_mul]
      exact congrArg _ he'

theorem mem_regAt_of_codim_one : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    [IsLocallyNoetherian X], IsCptGen ξ → NormalCpt ξ → ∀ (p : Cpt ξ) (a : Ω),
    (∀ q : Cpt ξ, q.1 ⤳ p.1 → ringKrullDim (X.presheaf.stalk q.1) = 1 → a ∈ regAt ξ q) →
    a ∈ regAt ξ p := by
  intro X Ω _ ξ _ h hn p a ha
  obtain ⟨hfr, hno, -⟩ := RegAtRing.regAt_ring X Ω ξ h p
  have : IsFractionRing (regAt ξ p) Ω := hfr
  have : IsNoetherianRing (regAt ξ p) := hno inferInstance
  have : IsIntegrallyClosed (regAt ξ p) := by
    rw [isIntegrallyClosed_iff Ω]
    intro x hx
    exact ⟨⟨x, hn p x hx⟩, rfl⟩
  obtain ⟨t, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := regAt ξ p) a
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hd1 : algebraMap (regAt ξ p) Ω d ≠ 0 := by
    simpa using hd0
  obtain ⟨b, hb⟩ := mem_range_of_integral_at_heightOne_over (regAt ξ p) Ω d
    (algebraMap (regAt ξ p) Ω t / algebraMap (regAt ξ p) Ω d) hd0
    ⟨1, t, by field_simp⟩
    (fun P hP h1 _ => by
      obtain ⟨q, hq, hdim, hiff⟩ := exists_point_of_prime h p P hP
      have hmem := ha q hq (by rw [hdim]; simp [h1])
      obtain ⟨s, u, hs, hsu⟩ := hiff _ hmem
      exact ⟨u, s, hs, by rw [mul_comm]; exact hsu.symm⟩)
  rw [← hb]
  exact b.2

end GlobalTheory.CompanionTheory.Ar.Flat
end
