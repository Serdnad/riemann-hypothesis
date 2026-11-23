module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle075
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle029
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle052
public import GroundTheory.HeightsAndTheta.Heights.ArithDegree
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.LinearIndependentSumElimOfExact
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle098
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle074
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle076
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SymplecticPolydiscPeriodBasis
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle019
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle103
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle087
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BlockRatio

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

section Forms

variable {σ : Type} [Fintype σ]

theorem aeval_scale {R : Type} [CommRing R] {F : MvPolynomial σ ℤ} {n : ℕ} (hF : F.IsHomogeneous n) (c : R)
    (x : σ → R) : MvPolynomial.aeval (fun j => c * x j) F = c ^ n * MvPolynomial.aeval x F := by
  simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ j, m j = n := by
    have h := hF (MvPolynomial.mem_support_iff.1 hm)
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h
    simpa using h
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

theorem aeval_map_hom {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (t : σ → A) (F : MvPolynomial σ ℤ) :
    MvPolynomial.aeval (fun j => f (t j)) F = f (MvPolynomial.aeval t F) :=
  by simpa using (MvPolynomial.comp_aeval_apply (f := t) f.toIntAlgHom F).symm

variable {Ω : Type} [Field Ω]

def IsFormQuot (x : σ → Ω) (i : σ) (b : Ω) : Prop :=
  ∃ (N n : ℕ) (G : MvPolynomial σ ℤ), N ≠ 0 ∧ G.IsHomogeneous n ∧
    MvPolynomial.aeval x G = (N : Ω) * x i ^ n * b

theorem isFormQuot_of_mem [CharZero Ω] {x : σ → Ω} {i : σ} (hi : x i ≠ 0) {b : Ω}
    (hb : b ∈ Algebra.adjoin ℚ (Set.range fun j => x j / x i)) : IsFormQuot x i b := by
  induction hb using Algebra.adjoin_induction with
  | mem b hb =>
    obtain ⟨j, rfl⟩ := hb
    refine ⟨1, 1, MvPolynomial.X j, one_ne_zero, MvPolynomial.isHomogeneous_X _ _, ?_⟩
    simp only [MvPolynomial.aeval_X, Nat.cast_one, one_mul, pow_one]
    field_simp
  | algebraMap r =>
    refine ⟨r.den, 0, MvPolynomial.C r.num, r.den_nz, MvPolynomial.isHomogeneous_C _ _, ?_⟩
    have hd : (r.den : Ω) ≠ 0 := Nat.cast_ne_zero.2 r.den_nz
    simp only [MvPolynomial.aeval_C, pow_zero, mul_one, eq_ratCast, eq_intCast, Rat.cast_def, map_intCast]
    field_simp
  | add a b _ _ ha hb =>
    obtain ⟨N, n, G, hN, hG, he⟩ := ha
    obtain ⟨N', n', G', hN', hG', he'⟩ := hb
    refine ⟨N * N', n + n', MvPolynomial.C (N' : ℤ) * MvPolynomial.X i ^ n' * G +
      MvPolynomial.C (N : ℤ) * MvPolynomial.X i ^ n * G', mul_ne_zero hN hN', ?_, ?_⟩
    · refine MvPolynomial.IsHomogeneous.add ?_ ?_
      · convert ((MvPolynomial.isHomogeneous_C _ _).mul
          ((MvPolynomial.isHomogeneous_X _ i).pow n')).mul hG using 1
        omega
      · convert ((MvPolynomial.isHomogeneous_C _ _).mul
          ((MvPolynomial.isHomogeneous_X _ i).pow n)).mul hG' using 1
        omega
    · simp only [map_add (f := _), map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X, he, he', eq_intCast,
        Int.cast_natCast, Nat.cast_mul, map_natCast]
      ring
  | mul a b _ _ ha hb =>
    obtain ⟨N, n, G, hN, hG, he⟩ := ha
    obtain ⟨N', n', G', hN', hG', he'⟩ := hb
    refine ⟨N * N', n + n', G * G', mul_ne_zero hN hN', hG.mul hG', ?_⟩
    simp only [map_mul, he, he', Nat.cast_mul]
    ring

theorem common_denominator {κ : Type} [Fintype κ] {x : σ → Ω} {i : σ} {b : κ → Ω}
    (h : ∀ j, IsFormQuot x i (b j)) :
    ∃ (N n : ℕ) (F : κ → MvPolynomial σ ℤ), N ≠ 0 ∧ (∀ j, (F j).IsHomogeneous n) ∧
      ∀ j, MvPolynomial.aeval x (F j) = (N : Ω) * x i ^ n * b j := by
  classical
  choose N n G hN hG he using h
  refine ⟨∏ j, N j, ∑ j, n j, fun j => MvPolynomial.C ((∏ l ∈ Finset.univ.erase j, N l : ℕ) : ℤ) *
    MvPolynomial.X i ^ (∑ l, n l - n j) * G j, Finset.prod_ne_zero_iff.2 fun j _ => hN j, fun j => ?_, fun j => ?_⟩
  all_goals have hle : n j ≤ ∑ l, n l := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  · convert ((MvPolynomial.isHomogeneous_C _ _).mul
      ((MvPolynomial.isHomogeneous_X _ i).pow (∑ l, n l - n j))).mul (hG j) using 1
    omega
  · have hp : x i ^ (∑ l, n l) = x i ^ (∑ l, n l - n j) * x i ^ n j := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    have hq : ((∏ l, N l : ℕ) : Ω) = (N j : Ω) * ((∏ l ∈ Finset.univ.erase j, N l : ℕ) : Ω) := by
      rw [← Nat.cast_mul, Finset.mul_prod_erase Finset.univ N (Finset.mem_univ j)]
    simp only [map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X, he, eq_intCast, Int.cast_natCast,
      map_natCast]
    rw [hp, hq]
    ring

theorem aeval_ne_zero_of_unit {L S : Type} [Field L] [CharZero L] [CommRing S] (g : S →+* Ω)
    (hg : Function.Injective g) (φ : S →+* L) {x : σ → Ω} {w : σ → L} {i : σ} (hx : x i ≠ 0) (hw : w i ≠ 0)
    (t : σ → S) (ht : ∀ j, g (t j) = x j / x i) (ht' : ∀ j, φ (t j) * w i = w j)
    {F : MvPolynomial σ ℤ} {n N : ℕ} (hN : N ≠ 0) (hF : F.IsHomogeneous n) {e : S} (he : IsUnit e)
    (hFe : MvPolynomial.aeval x F = (N : Ω) * x i ^ n * g e) : MvPolynomial.aeval w F ≠ 0 := by
  have h1 : x = fun j => x i * g (t j) := funext fun j => by rw [ht, mul_div_cancel₀ _ hx]
  have h2 : MvPolynomial.aeval x F = x i ^ n * g (MvPolynomial.aeval t F) := by
    conv_lhs => rw [h1]
    rw [aeval_scale hF, aeval_map_hom]
  have h3 : MvPolynomial.aeval t F = (N : S) * e := by
    apply hg
    apply mul_left_cancel₀ (pow_ne_zero n hx)
    rw [← h2, hFe, map_mul, map_natCast]
    ring
  have h4 : w = fun j => w i * φ (t j) := funext fun j => by rw [← ht', mul_comm]
  have h5 : MvPolynomial.aeval w F = w i ^ n * φ (MvPolynomial.aeval t F) := by
    conv_lhs => rw [h4]
    rw [aeval_scale hF, aeval_map_hom]
  rw [h5, h3, map_mul, map_natCast]
  exact mul_ne_zero (pow_ne_zero _ hw) (mul_ne_zero (Nat.cast_ne_zero.2 hN) (he.map φ).ne_zero)

end Forms

section Germs

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem exists_unit_germ {p : Cpt ξ} (hinj : Function.Injective (genMap ξ p)) {s : Ω} (h : unitAt ξ p s) :
    ∃ e : X.presheaf.stalk p.1, IsUnit e ∧ genMap ξ p e = s := by
  obtain ⟨h0, ⟨e, rfl⟩, ⟨e', he'⟩⟩ := h
  refine ⟨e, IsUnit.of_mul_eq_one e' (hinj ?_), rfl⟩
  rw [map_mul, he', mul_inv_cancel₀ h0, map_one]

theorem unitAt_natCast [CharZero Ω] {L : Type} [Field L] [CharZero L] {zz : Spec (CommRingCat.of L) ⟶ X}
    (h : genPt ξ ⤳ centre zz) {r : ℕ} (hr : r ≠ 0) : unitAt ξ ⟨centre zz, h⟩ (r : Ω) := by
  have hu : IsUnit ((r : X.presheaf.stalk (centre zz))) := (inferInstance : IsLocalHom (Scheme.stalkClosedPointTo zz).hom).map_nonunit _ (IsUnit.mk0 _
      ((map_natCast (Scheme.stalkClosedPointTo zz).hom r).trans_ne ((Nat.cast_ne_zero (R := L)).2 hr)))
  obtain ⟨u, hu⟩ := hu
  have hv : genMap ξ ⟨centre zz, h⟩ (u : X.presheaf.stalk (centre zz)) = (r : Ω) := by
    rw [hu, map_natCast]
  refine ⟨Nat.cast_ne_zero.2 hr, ⟨_, hv⟩, ⟨((u⁻¹ : (X.presheaf.stalk (centre zz))ˣ) : _), ?_⟩⟩
  rw [← hv]
  exact map_units_inv _ u

end Germs

theorem ratios_quotients_of_forms : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (k₀ : K), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → EmbedsGeneric ξ (fun i : J k₀ => y ⟨k₀, i⟩) → ∀ (L : Type) [Field L] [CharZero L] (z : (Σ k, J k) → L), z ∈ Small.ptsOver L (mCoordIdeal y) → ∀ (i : J k₀) (k : K) (c : J k), z ⟨k₀, i⟩ ≠ 0 → z ⟨k, c⟩ ≠ 0 → ∃ (n : ℕ) (F : J k → MvPolynomial (J k₀) ℤ), (∀ j, (F j).IsHomogeneous n) ∧ (∀ j, MvPolynomial.aeval (fun i' : J k₀ => y ⟨k₀, i'⟩) (F j) * y ⟨k, c⟩ = MvPolynomial.aeval (fun i' : J k₀ => y ⟨k₀, i'⟩) (F c) * y ⟨k, j⟩) ∧ MvPolynomial.aeval (fun i' : J k₀ => z ⟨k₀, i'⟩) (F c) ≠ 0 := by
  intro X Ω _ _ ξ K _ J _ y k₀ hT hE L _ _ z hz i k c hzi hzc
  classical
  obtain ⟨hblk, hvan⟩ := hz
  obtain ⟨zz, ⟨hsp, hco⟩, -⟩ := (GlobalTheory.T.local_ring_points_existsUnique X Ω ξ K J y hT L).1 z
    (fun k' => (hblk k').imp fun _ h => IsUnit.mk0 _ h) hvan
  let p : Cpt ξ := ⟨centre zz, hsp⟩
  have hinj : Function.Injective (genMap ξ p) := hT.gen.inj p
  have hfib : ∀ r : ℕ, r.Prime → ¬ InFibre ξ r p := fun r hr hn => hn (unitAt_natCast hsp hr.ne_zero)
  obtain ⟨hyi, hrat⟩ := hco.2 k₀ i (IsUnit.mk0 _ hzi)
  obtain ⟨hyc, hrat'⟩ := hco.2 k c (IsUnit.mk0 _ hzc)
  have hgerm : ∀ i' : J k₀, ∃ t : X.presheaf.stalk (centre zz),
      genMap ξ p t = y ⟨k₀, i'⟩ / y ⟨k₀, i⟩ ∧ (Scheme.stalkClosedPointTo zz).hom t * z ⟨k₀, i⟩ = z ⟨k₀, i'⟩ := by
    intro i'
    obtain ⟨r, ⟨_, t, h1, h2⟩, h3⟩ := hrat i'
    exact ⟨t, h1, by rw [h2, h3]⟩
  choose t ht ht' using hgerm
  have hchart : InChart ξ (fun i' : J k₀ => y ⟨k₀, i'⟩) i p := ⟨hyi, fun i' => ⟨t i', ht i'⟩⟩
  have hreg : ∀ j, y ⟨k, j⟩ / y ⟨k, c⟩ ∈ regAt ξ p := by
    intro j
    obtain ⟨r, ⟨_, u, h1, _⟩, _⟩ := hrat' j
    exact ⟨u, h1⟩
  choose s hsB hsU hsa using fun j => ((hE p hfib).2 i hchart).1 _ (hreg j)
  have hSU : unitAt ξ p (∏ j, s j) := by
    refine ⟨Finset.prod_ne_zero_iff.2 fun j _ => (hsU j).1, Subring.prod_mem _ fun j _ => (hsU j).2.1, ?_⟩
    rw [← Finset.prod_inv_distrib]
    exact Subring.prod_mem _ fun j _ => (hsU j).2.2
  have hSa : ∀ j, (∏ j, s j) * (y ⟨k, j⟩ / y ⟨k, c⟩) ∈
      Algebra.adjoin ℚ (Set.range fun j => y ⟨k₀, j⟩ / y ⟨k₀, i⟩) := by
    intro j
    rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ j), mul_right_comm]
    exact Subalgebra.mul_mem _ (hsa j) (Subalgebra.prod_mem _ fun l _ => hsB l)
  obtain ⟨N, n, F, hN, hF, he⟩ := common_denominator (x := fun i' : J k₀ => y ⟨k₀, i'⟩) (i := i)
    (b := fun j => (∏ j, s j) * (y ⟨k, j⟩ / y ⟨k, c⟩)) fun j =>
      isFormQuot_of_mem (x := fun i' : J k₀ => y ⟨k₀, i'⟩) (i := i) hyi (hSa j)
  obtain ⟨e, heu, hee⟩ := exists_unit_germ hinj hSU
  refine ⟨n, F, hF, fun j => ?_, ?_⟩
  · rw [he j, he c, div_self hyc]
    field_simp
  · refine aeval_ne_zero_of_unit (x := fun i' : J k₀ => y ⟨k₀, i'⟩) (w := fun i' : J k₀ => z ⟨k₀, i'⟩) (i := i)
      (genMap ξ p) hinj (Scheme.stalkClosedPointTo zz).hom hyi hzi t ht ht' hN (hF c) heu ?_
    rw [he c, div_self hyc, _root_.mul_one, hee]

end GlobalTheory.CompanionTheory.Ar.BlockRatio
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.EmbedsOfTie

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem isLocalRing_regAt {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : IsCptGen ξ) (p : Cpt ξ) :
    IsLocalRing (regAt ξ p) := by
  unfold regAt
  exact IsLocalRing.of_surjective' (genMap ξ p).rangeRestrict (genMap ξ p).rangeRestrict_surjective

theorem unitAt_iff_isUnit {ξ : Spec (CommRingCat.of Ω) ⟶ X} (p : Cpt ξ) (s : regAt ξ p) :
    unitAt ξ p (s : Ω) ↔ IsUnit s := by
  constructor
  · rintro ⟨h0, -, hinv⟩
    refine isUnit_iff_exists_inv.mpr ⟨⟨(s : Ω)⁻¹, hinv⟩, ?_⟩
    exact Subtype.ext (mul_inv_cancel₀ h0)
  · intro hs
    obtain ⟨t, ht⟩ := isUnit_iff_exists_inv.mp hs
    have ht' : (s : Ω) * (t : Ω) = 1 := by simpa using congrArg Subtype.val ht
    have h0 : (s : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one ht'
    refine ⟨h0, s.2, ?_⟩
    rw [inv_eq_of_mul_eq_one_right ht']
    exact t.2

theorem mem_adjoin_rat_of_int [CharZero Ω] {S : Set Ω} {a : Ω} (h : a ∈ Algebra.adjoin ℤ S) :
    a ∈ Algebra.adjoin ℚ S := by
  induction h using Algebra.adjoin_induction with
  | mem y hy => exact Algebra.subset_adjoin hy
  | algebraMap r =>
    rw [eq_intCast (algebraMap ℤ Ω) r]
    exact intCast_mem _ r
  | add y z _ _ hy hz => exact add_mem hy hz
  | mul y z _ _ hy hz => exact mul_mem hy hz

theorem embedsGeneric_of_coordTie : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω), CoordTie ℤ ξ x → EmbedsGeneric ξ x := by
  intro X Ω _ _ ξ κ x h
  unfold EmbedsGeneric
  intro p _
  refine ⟨h.cover p, fun i hi => ⟨?_, ?_⟩⟩
  · intro a ha
    obtain ⟨s, hs, hu, hsa⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ κ x h i p hi a).mp ha
    exact ⟨s, mem_adjoin_rat_of_int hs, hu, mem_adjoin_rat_of_int hsa⟩
  · intro q _ hq hpq
    haveI := isLocalRing_regAt h.gen p
    have hmem : ∀ a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x i), a ∈ regAt ξ p :=
      fun a ha => (h.ring i hi.1 a).mp ha p hi
    let φ : Algebra.adjoin ℤ (Set.range fun j => x j / x i) →+* regAt ξ p :=
      { toFun := fun s => ⟨s, hmem s s.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    let I : Ideal (Algebra.adjoin ℤ (Set.range fun j => x j / x i)) :=
      Ideal.comap φ (IsLocalRing.maximalIdeal (regAt ξ p))
    have hI : I.IsPrime := Ideal.comap_isPrime φ _
    have key : ∀ s : Algebra.adjoin ℤ (Set.range fun j => x j / x i), s ∉ I ↔ unitAt ξ p (s : Ω) := by
      intro s
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
      exact (unitAt_iff_isUnit p (φ s)).symm
    obtain ⟨p', -, huniq⟩ := GlobalTheory.T.prime_chart_existsUnique_point X Ω ξ ℤ κ x h i hi.1 I hI
    have e1 := huniq p ⟨hi, key⟩
    have e2 := huniq q ⟨hq, fun s => (key s).trans (hpq s (mem_adjoin_rat_of_int s.2))⟩
    exact e1.trans e2.symm

end GlobalTheory.CompanionTheory.Ar.EmbedsOfTie
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyDegFree


open scoped ComplexOrder in
theorem gramDet_eq_norm {L : Type} [Field L] [NumberField L] (B : HermitianBundle.{0} L) (σ : L →+* ℂ)
    {n : ℕ} {e : Fin n → B.carrier} (hli : LinearIndependent (𝓞 L) e) :
    GroundTheory.Heights₂.Heights.gramDet B.metric σ e = ‖B.gramDet σ e‖ := by
  have hd : B.gramDet σ e = (Matrix.gram ℂ fun i => fibreVec B.metric σ (e i)).det := rfl
  have hp : 0 < (Matrix.gram ℂ fun i => fibreVec B.metric σ (e i)).det :=
    (Matrix.posDef_gram_of_linearIndependent (linearIndependent_fibreVec B.metric σ hli)).det_pos
  obtain ⟨h1, h2⟩ := Complex.lt_def.mp hp
  have hz : (((Matrix.gram ℂ fun i => fibreVec B.metric σ (e i)).det).re : ℂ) =
      (Matrix.gram ℂ fun i => fibreVec B.metric σ (e i)).det :=
    Complex.ext (by simp) (by simpa using h2)
  rw [hd, ← hz, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by simpa using h1)]
  rfl

theorem normDegree_top_eq_mean_gramDet : ∀ (L : Type) [Field L] [NumberField L] (B : HermitianBundle.{0} L) (n : ℕ) (e : Fin n → B.carrier), LinearIndependent (𝓞 L) e → Submodule.span (𝓞 L) (Set.range e) = ⊤ → B.normDegree ⊤ = -(1 / 2) * mean L (fun σ => Real.log ‖B.gramDet σ e‖) := by
  intro L _ _ B n e hli hspan
  let s : Fin n → (⊤ : Submodule (𝓞 L) B.carrier) := fun i => ⟨e i, Submodule.mem_top⟩
  have hs : LinearIndependent (𝓞 L) s :=
    LinearIndependent.of_comp (⊤ : Submodule (𝓞 L) B.carrier).subtype hli
  have hcard : Fintype.card (Fin n) = B.rank ⊤ := by
    rw [Fintype.card_fin, HermitianBundle.rank, finrank_top,
      Module.finrank_eq_card_basis (Module.Basis.mk hli hspan.ge), Fintype.card_fin]
  have hsp : Submodule.span (𝓞 L) (Set.range s) = ⊤ := by
    have hmap : (Submodule.span (𝓞 L) (Set.range s)).map
        (⊤ : Submodule (𝓞 L) B.carrier).subtype = ⊤ := by
      rw [Submodule.map_span, ← Set.range_comp]
      exact hspan
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    have hx' : x ∈ (Submodule.span (𝓞 L) (Set.range s)).map
        (⊤ : Submodule (𝓞 L) B.carrier).subtype := by
      rw [hmap]
      exact Submodule.mem_top
    obtain ⟨y, hy, rfl⟩ := hx'
    exact hy
  have hone : Nat.card ((⊤ : Submodule (𝓞 L) B.carrier) ⧸ Submodule.span (𝓞 L) (Set.range s)) = 1 := by
    rw [hsp]
    exact Nat.card_unique
  have hg : ∀ σ : L →+* ℂ, GroundTheory.Heights₂.Heights.gramDet B.metric σ
      (fun i => ((s i : (⊤ : Submodule (𝓞 L) B.carrier)) : B.carrier)) = ‖B.gramDet σ e‖ :=
    fun σ => gramDet_eq_norm B σ hli
  rw [HermitianBundle.normDegree, B.degree_eq_of_linearIndependent ⊤ hs hcard,
    hone, Nat.cast_one, Real.log_one, zero_sub, mean]
  simp only [hg]
  ring

end GlobalTheory.CompanionTheory.Ar.Sl.KeyDegFree
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Centre.Sep

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

theorem isLocalRing_regAt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) :
    IsLocalRing (regAt ξ p) := by
  show IsLocalRing (genMap ξ p).range
  exact IsLocalRing.of_surjective' (genMap ξ p).rangeRestrict (genMap ξ p).rangeRestrict_surjective

theorem isUnit_regAt_iff {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ)
    (a : regAt ξ p) : IsUnit a ↔ unitAt ξ p (a : Ω) := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := h.exists_right_inv
    have e : (a : Ω) * (b : Ω) = 1 := congrArg Subtype.val hb
    have ha : (a : Ω) ≠ 0 := fun h0 => by simp [h0] at e
    refine ⟨ha, a.2, ?_⟩
    rw [inv_eq_of_mul_eq_one_right e]
    exact b.2
  · rintro ⟨h0, -, h2⟩
    exact isUnit_iff_exists_inv.2 ⟨⟨_, h2⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩

theorem unitAt_iff_of_dominated {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω']
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {i : Ω →+* Ω'} {p' : Cpt ξ'} {q : Cpt ξ}
    (h : (∀ a ∈ regAt ξ q, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt ξ q, unitAt ξ' p' (i a) → unitAt ξ q a)
    {a : Ω} (ha : a ∈ regAt ξ q) : unitAt ξ q a ↔ unitAt ξ' p' (i a) := by
  refine ⟨fun hu => ⟨(map_ne_zero i).2 hu.1, h.1 a hu.2.1, ?_⟩, h.2 a ha⟩
  rw [← map_inv₀]
  exact h.1 _ hu.2.2

theorem eq_of_dominated_of_inChart {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ]
    {x : κ → Ω} (M : PModel o x) {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] {ξ' : Spec (CommRingCat.of Ω') ⟶ X'}
    {i : Ω →+* Ω'} {p' : Cpt ξ'} {c : κ} {q r : Cpt M.ξ} (hq : InChart M.ξ x c q) (hr : InChart M.ξ x c r)
    (dq : (∀ a ∈ regAt M.ξ q, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ q, unitAt ξ' p' (i a) → unitAt M.ξ q a)
    (dr : (∀ a ∈ regAt M.ξ r, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ r, unitAt ξ' p' (i a) → unitAt M.ξ r a) :
    q = r := by
  have cq := (GlobalTheory.T.regAt_chart_localization o Ω κ x M c q hq).1
  have cr := (GlobalTheory.T.regAt_chart_localization o Ω κ x M c r hr).1
  haveI := isLocalRing_regAt M.ξ q
  let f : chRing o x c →+* regAt M.ξ q :=
    ((chRing o x c).val : chRing o x c →+* Ω).codRestrict (regAt M.ξ q) fun u => cq _ u.2
  have hP : ∀ u : chRing o x c, u ∈ (IsLocalRing.maximalIdeal (regAt M.ξ q)).comap f ↔ ¬ unitAt M.ξ q (u : Ω) := by
    intro u
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_regAt_iff]
    rfl
  obtain ⟨p, -, huniq⟩ := GlobalTheory.T.chart_prime_existsUnique_point o Ω κ x M c hq.1 _
    (inferInstance : ((IsLocalRing.maximalIdeal (regAt M.ξ q)).comap f).IsPrime)
  have e1 := huniq q ⟨hq, hP⟩
  have e2 := huniq r ⟨hr, fun u => by
    rw [hP, unitAt_iff_of_dominated dq (cq _ u.2), unitAt_iff_of_dominated dr (cr _ u.2)]⟩
  exact e1.trans e2.symm

theorem eq_of_dominated : ∀ {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω} (M : PModel o x) {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (p' : Cpt ξ') (q₁ q₂ : Cpt M.ξ), ((∀ a ∈ regAt M.ξ q₁, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ q₁, unitAt ξ' p' (i a) → unitAt M.ξ q₁ a) → ((∀ a ∈ regAt M.ξ q₂, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ q₂, unitAt ξ' p' (i a) → unitAt M.ξ q₂ a) → q₁ = q₂ := by
  intro o _ Ω _ _ κ _ x M X' Ω' _ ξ' i p' q₁ q₂ d₁ d₂
  obtain ⟨c₁, hc₁⟩ := M.tie.cover q₁
  obtain ⟨c₂, hc₂⟩ := M.tie.cover q₂
  have hctr : p' ∈ ctrSet o x i ξ' :=
    ⟨c₁, hc₁.1, fun a ha => d₁.1 a ((GlobalTheory.T.regAt_chart_localization o Ω κ x M c₁ q₁ hc₁).1 a ha)⟩
  obtain ⟨p₀, d₀, -, hp₀⟩ := GlobalTheory.T.centre_set_dominating_point o Ω κ x M X' Ω' ξ' i p' hctr
  have e₁ : q₁ = p₀ := eq_of_dominated_of_inChart M hc₁ (hp₀ c₁ hc₁.1 fun j => d₁.1 _ (hc₁.2 j)) d₁ d₀
  have e₂ : q₂ = p₀ := eq_of_dominated_of_inChart M hc₂ (hp₀ c₂ hc₂.1 fun j => d₂.1 _ (hc₂.2 j)) d₂ d₀
  exact e₁.trans e₂.symm

end GlobalTheory.CompanionTheory.Ar.Centre.Sep
end
end

section

open Filter Topology Matrix

theorem _root_.GlobalTheory.T.symplectic_polydisc_period_basis : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : GlobalTheory.CompanionTheory.Ar.Flat.LogPeriods n a g Λ), ∃ (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (Q : GroundTheory.Heights₂.Heights.Regular.PeriodPolydisc n a g) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ), (∀ i j, L.E (bas (.inl i)) (bas (.inl j)) = 0 ∧ L.E (bas (.inr i)) (bas (.inr j)) = 0 ∧ L.E (bas (.inl i)) (bas (.inr j)) = if i = j then -1 else 0) ∧ (∀ i j, DifferentiableOn ℂ (fun z => A z i j) (Metric.ball 0 1)) ∧ (A 0).det ≠ 0 ∧ Q.IsTau0Ext T0 ∧ (∀ i, ((Q.B i).map (Int.cast : ℤ → ℝ)).PosSemidef) ∧ (∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, ∀ i k, L.P w (bas (.inl i)) k = A (GroundTheory.Heights₂.Heights.Regular.expCover a w) i k) ∧ ∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, ∀ j, L.P w (bas (.inr j)) = ∑ k, Q.τ w j k • L.P w (bas (.inl k)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_markedPeriods_frame | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_markedPeriods_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_markedPeriods_frame <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

theorem sqAt_sum_eq_gram : ∀ (L : Type) [Field L] [NumberField L] (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (σ : L →+* ℂ) (n : ℕ)
    (ε : Fin n → B.carrier) (Γ : Matrix (Fin n) (Fin n) ℂ),
    (∀ a b, Γ a b = (B.metric.form σ).inner ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] ε a)
      ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] ε b)) → ∀ w : Fin n → ℂ,
    sqAt B σ (∑ a, GroundTheory.Heights₂.Heights.ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 L] ε a) = (star w ⬝ᵥ (Γ *ᵥ w)).re :=
  @PositivityTheory.Xgn.hermitian_norm_square_formula

end GlobalTheory.CompanionTheory.Ar.TorusUnif
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

theorem _root_.GlobalTheory.T.good_point_or_conjugate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X), GoodPt 𝔐 z ∨ GoodPt 𝔐 (spMap (starRingEnd ℂ) ≫ z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotUnif.Dich.goodPt_or_conj | exact GlobalTheory.CompanionTheory.Ar.QuotUnif.Dich.goodPt_or_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotUnif.Dich.goodPt_or_conj <;> assumption)
end
