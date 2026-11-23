module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle888
public import Development.AbelianVarietyTheory.Definitions.Divisors.CrystallineConnectionFormCoboundaryZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle901
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle856
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle555
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle603
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle604
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle889
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle607
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle830
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle606
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle683
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle723
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle561
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle890
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle891
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CoverHyp

theorem restrict_bijective : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) [Finite J] [SemilatticeInf J] (U : J → X.affineOpens) (hU : Monotone U), (∀ i j, (U (i ⊓ j)).1 = (U i).1 ⊓ (U j).1) → ⨆ i, (U i).1 = ⊤ → Function.Bijective (pullHyp1 (CoefMap.restrict (OAff s) hU.functor.op)) := by
  intro R _ X s J _ _ U hU hinf hcov
  classical
  haveI := Fintype.ofFinite J
  let B : Type := {V : X.affineOpens // ∃ i, V.1 ≤ (U i).1}
  have hne : ∀ V : B, (Finset.univ.filter fun i => V.1.1 ≤ (U i).1).Nonempty := fun V => by
    obtain ⟨i, hi⟩ := V.2
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩
  let σ : B → J := fun V => (Finset.univ.filter fun i => V.1.1 ≤ (U i).1).inf' (hne V) id
  let u : J → B := fun i => ⟨U i, i, le_rfl⟩
  have hσ : ∀ V : B, V.1.1 ≤ (U (σ V)).1 := fun V =>
    Finset.inf'_induction (p := fun i => V.1.1 ≤ (U i).1) (hne V) id
      (fun a ha b hb => by rw [hinf]; exact le_inf ha hb) fun i hi => (Finset.mem_filter.1 hi).2
  have gc : GaloisConnection σ u := fun V i =>
    ⟨fun h => (hσ V).trans (hU h), fun h =>
      Finset.inf'_le (s := Finset.univ.filter fun i : J => V.1.1 ≤ (U i).1) (id : J → J)
        (Finset.mem_filter.2 ⟨Finset.mem_univ i, h⟩)⟩
  let incl : Bᵒᵖ ⥤ AffOp X := (Monotone.functor (f := (Subtype.val : B → X.affineOpens)) fun _ _ h ↦ h).op
  have b1 : Function.Bijective (pullHyp1 (CoefMap.restrict (OAff s) incl)) :=
    GlobalTheory.T.cech_hyper_cohomology_cover_refinement R X s J (fun i => (U i).1) hcov
  have b2 := GlobalTheory.T.hyper_cohomology_restrict_adjoint_bijective R Bᵒᵖ Jᵒᵖ (incl ⋙ OAff s) gc.monotone_u.functor.op gc.monotone_l.functor.op
    gc.adjunction.op
  have e : ∀ c, pullHyp1 (CoefMap.restrict (OAff s) hU.functor.op) c =
      pullHyp1 (CoefMap.restrict (incl ⋙ OAff s) gc.monotone_u.functor.op)
        (pullHyp1 (CoefMap.restrict (OAff s) incl) c) := fun c =>
    (pullHyp1_eq_of_natTrans (CoefMap.restrict (OAff s) hU.functor.op)
      ((CoefMap.restrict (OAff s) incl).comp (CoefMap.restrict (incl ⋙ OAff s) gc.monotone_u.functor.op))
      (𝟙 _) (fun T b => mp_id (OAff s) _ b) c).trans (pullHyp1_comp _ _ c)
  have := b2.comp b1
  exact (funext e : _ = _) ▸ this

end GlobalTheory.CoverHyp
end

section

open CategoryTheory AlgebraicGeometry DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.Cris

theorem small_descent_H2_bijective (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I)
    (X : Scheme.{0}) (s : X ⟶ Sp R) (K : Type) (U : K → X.Opens) (hU : ⨆ i, U i = ⊤) :
    Function.Bijective (CoefMap.restrict (O κ s) (IsSmall κ s U).ι).pull2 := by
  refine GlobalTheory.CatCoh.Desc.pull2_bijective (O κ s) ?_ (IsSmall κ s U) ?_ ?_
  · intro T b
    obtain ⟨T', l, h1, h2, h3, h4⟩ := GlobalTheory.ThickLoc.exists_localization R I κ X s T b
    exact ⟨T', l, by simpa only [mp_O] using h1, by simpa only [mp_O] using h2,
      by simpa only [mp_O] using h3, by simpa only [mp_O] using h4⟩
  · rintro S S' φ ⟨i, hi⟩
    exact ⟨i, GlobalTheory.Cris.Thick.Hom.le_preimage φ hi⟩
  · intro T
    obtain ⟨n, b, hb, h⟩ := exists_finite_small_cover R I κ X s K U hU T
    exact ⟨n, b, hb, fun i S u hu => h i S u (by simpa only [mp_O] using hu)⟩

end GlobalTheory.Cris
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc WittVector

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharPeriod

theorem pow_dvd_of_theta_pow_dvd : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (x : B) (N : ℕ), (p : O) ∣ θ x ^ N → ∃ M : ℕ, (p : B) ∣ x ^ M := by
  intro p _ B O Q _ _ _ _ θ hF x N ⟨o, ho⟩
  obtain ⟨b, rfl⟩ := hF.surj o
  have hj : θ (x ^ N - p * b) = 0 := by rw [map_sub, map_pow, ho, map_mul, map_natCast, sub_self]
  obtain ⟨y, -, hy⟩ := hF.pd _ hj
  refine ⟨N * p, ?_⟩
  have h1 : (x ^ N - (x ^ N - p * b)) ∣ (x ^ N) ^ p - (x ^ N - p * b) ^ p := sub_dvd_pow_sub_pow _ _ _
  rw [sub_sub_cancel] at h1
  rw [pow_mul]
  have h2 : (x ^ N) ^ p = ((x ^ N) ^ p - (x ^ N - p * b) ^ p) + p * y := by rw [hy]; ring
  rw [h2]
  exact dvd_add (dvd_trans (dvd_mul_right _ _) h1) (dvd_mul_right _ _)

theorem root_iterate_pow {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    (n : ℕ) (y : PreTilt O p) : (root^[n] y) ^ (p ^ n) = y := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, pow_succ, pow_mul, ih]
    exact (_root_.frobeniusEquiv (PreTilt O p) p).apply_symm_apply y

theorem one_add_pow_of_sq_zero {R : Type} [CommRing R] {x : R} (hx : x * x = 0) (k : ℕ) :
    (1 + x) ^ k = 1 + k * x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination (k : R) * hx

theorem pow_mul_logValue : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p), IsPrimitiveSystem ε → ∀ (F : BFrame ε) [Algebra ℚ F.Q] (n k : ℕ) (w : F.B) (q : F.Q), F.θ w = zeta ε n ^ k → HasVal p (fun _ : Unit => w - 1) (PowerSeries.log F.Q : MvPowerSeries Unit F.Q) q → ∃ b : F.B, (p : F.Q) ^ n * q = algebraMap F.B F.Q (k * F.a (Sandwich.mu ε) + p ^ n * b) := by
  intro p _ O _ _ _ ε hε F _ n k w q hw hq
  have hF := F.frame
  haveI := hF.complete
  set r : F.B := F.a (teichmuller p (root^[n] ε)) with hr
  have hθr : F.θ r = zeta ε n := by rw [hr, F.θ_a, fontaineTheta_teichmuller]; rfl
  have hrp : r ^ (p ^ n) = 1 + F.a (Sandwich.mu ε) := by
    rw [hr, ← map_pow, ← map_pow, root_iterate_pow, Sandwich.mu, map_sub, map_one]
    ring
  set x : F.B := (k : F.B) * F.a (Sandwich.mu ε) with hx
  have hxx : x * x = 0 := by
    have h : F.a (Sandwich.mu ε) * F.a (Sandwich.mu ε) = 0 := by
      rw [← F.p_τ]; linear_combination ((p : F.B) * p) * F.τ_sq
    linear_combination ((k : F.B) * k) * h
  set e : F.B := r ^ k with he
  have hθe : F.θ e = zeta ε n ^ k := by rw [he, map_pow, hθr]
  have hep : e ^ (p ^ n) = 1 + x := by
    have h : F.a (Sandwich.mu ε) * F.a (Sandwich.mu ε) = 0 := by
      rw [← F.p_τ]; linear_combination ((p : F.B) * p) * F.τ_sq
    rw [he, ← pow_mul, mul_comm, pow_mul, hrp, one_add_pow_of_sq_zero h]
  have hpe : (p : F.B) ∣ (e - 1) ^ (p ^ n) := by
    obtain ⟨s, hs⟩ := exists_add_pow_prime_pow_eq (Fact.out : p.Prime) (e - 1) 1 n
    rw [sub_add_cancel, one_pow, hep] at hs
    refine ⟨k * F.τ - (e - 1) * s, ?_⟩
    have : (p : F.B) * F.τ = F.a (Sandwich.mu ε) := F.p_τ
    linear_combination -hs + hx - (k : F.B) * this
  have hnile : ∀ i : Unit, ∃ N : ℕ, (p : F.B) ∣ (fun _ : Unit => e - 1) i ^ N := fun _ => ⟨_, hpe⟩
  have hnilw : ∀ i : Unit, ∃ N : ℕ, (p : F.B) ∣ (fun _ : Unit => w - 1) i ^ N := by
    intro _
    have h1 : F.θ (w - 1) = F.θ (e - 1) := by rw [map_sub, map_sub, hw, hθe]
    obtain ⟨s, hs⟩ := hpe
    exact pow_dvd_of_theta_pow_dvd p F.B O F.Q F.θ hF (w - 1) (p ^ n)
      ⟨F.θ s, by rw [h1, ← map_pow, hs, map_mul, map_natCast]⟩
  have hD := GlobalTheory.T.diffCoeffsInIdeal_top_powerSeries_log F.B F.Q
  obtain ⟨q₁, hq₁, -⟩ := GlobalTheory.T.existsUnique_hasPAdicPowerSeriesValue_of_diffCoeffs p F.B O F.Q F.θ hF Unit (fun _ => e - 1) hnile _ hD
  have hJ : ∀ y ∈ RingHom.ker F.θ, ∃ y' ∈ RingHom.ker F.θ, y ^ p = p * y' := by
    intro y hy
    obtain ⟨y', hy', h⟩ := hF.pd y hy
    exact ⟨y', hy', h⟩
  obtain ⟨j, -, b', hjb⟩ := GlobalTheory.T.hasPAdicPowerSeriesValue_sub_mem_pd_ideal p F.B O F.Q F.θ hF Unit (fun _ => w - 1) hnilw
    (RingHom.ker F.θ) hJ (fun _ => e - 1) _ q q₁
    (fun _ => by rw [RingHom.mem_ker, sub_sub_sub_cancel_right, map_sub, hw, hθe, sub_self]) hD hq hq₁ 0
  obtain ⟨Ev, hEv, -⟩ := (GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural p F.B F.B Unit (fun _ => e - 1) hnile).1
  set u : Unit → MvPowerSeries Unit F.B := fun _ => (1 + X ()) ^ (p ^ n) - 1 with hu
  have hu0 : ∀ j, constantCoeff (u j) = 0 := fun _ => by simp [hu]
  have hEu : (fun j => Ev (u j)) = fun _ : Unit => x := by
    funext j
    simp only [hu, map_sub, map_pow, map_add (f := _), map_one, hEv.1 ()]
    rw [add_sub_cancel, hep, add_sub_cancel_left]
  have h1 : HasVal p (fun j => Ev (u j)) (PowerSeries.log F.Q : MvPowerSeries Unit F.Q) (algebraMap F.B F.Q x) := by
    rw [hEu]; exact GlobalTheory.T.hasVal_log_of_mul_self_eq_zero' F.B F.Q p x hxx
  have h2 := GlobalTheory.T.pAdicEvaluation_subst_compatible_thickening p F.B O F.Q F.θ hF Unit (fun _ => e - 1) hnile Ev hEv Unit u _ _ hu0 hD h1
  rw [hu, GlobalTheory.T.subst_one_add_X_pow_log_eq_nsmul F.B F.Q (p ^ n)] at h2
  have h3 := (GlobalTheory.T.hasPAdicPowerSeriesValue_add_smul_map p F.B O F.Q F.θ hF Unit (fun _ => e - 1) _ 0 q₁ 0 hq₁).2.1 ((p ^ n : ℕ) : F.Q)
  have h4 := HasVal.unique hF h3 h2
  refine ⟨j + b', ?_⟩
  rw [pow_zero, one_mul] at hjb
  have h5 : q = q₁ + algebraMap F.B F.Q (j + b') := by rw [← hjb]; ring
  rw [h5, mul_add, ← Nat.cast_pow, h4]
  simp only [map_add (f := _), map_mul, map_natCast, map_pow]
  push_cast
  ring

theorem hasPeriod_formalLog_char : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε) (F : BFrame ε) [Algebra ℚ F.Q] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (χ : G.dual.Tate) (g : MvPowerSeries (Fin d) F.B), constantCoeff g = 1 → (∀ n, c.ev n (map F.θ g) = charElem χ n) → ∀ t, c.HasPeriod F.θ t (formalLog (map (algebraMap F.B F.Q) g)) (F.a (Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ))) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F _ G d c χ g hg1 hgχ t
  have hF := F.frame
  haveI := hF.complete
  have hD : DIn (⊤ : Ideal F.B) (formalLog (map (algebraMap F.B F.Q) g)) := GlobalTheory.T.diffCoeffsInIdeal_top_formalLog_constOne F.B F.Q (Fin d) g hg1
  have hnil : ∀ n (z : Fin d → F.B), (∀ i, F.θ (z i) = t.pt n (c.x n i)) → ∀ i, ∃ N : ℕ, (p : F.B) ∣ z i ^ N := by
    intro n z hz i
    obtain ⟨N, w, hw⟩ := c.nil n i
    exact pow_dvd_of_theta_pow_dvd p F.B O F.Q F.θ hF (z i) N ⟨t.pt n w, by rw [hz, ← map_pow, hw, map_mul, map_natCast]⟩
  have hex : ∀ (n : ℕ) (z : Fin d → F.B), (∀ i, F.θ (z i) = t.pt n (c.x n i)) → ∃ q : F.Q, HasVal p z (formalLog (map (algebraMap F.B F.Q) g)) q :=
    fun n z hz => (GlobalTheory.T.existsUnique_hasPAdicPowerSeriesValue_of_diffCoeffs p F.B O F.Q F.θ hF (Fin d) z (hnil n z hz) _ hD).exists
  have hcong : ∀ (n : ℕ) (z : Fin d → F.B) (q : F.Q), (∀ i, F.θ (z i) = t.pt n (c.x n i)) → HasVal p z (formalLog (map (algebraMap F.B F.Q) g)) q → ∃ b : F.B, (p : F.Q) ^ n * q = algebraMap F.B F.Q (F.a (Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ)) + p ^ n * b) := by
    intro n z q hz hq
    obtain ⟨E, hE, -⟩ := (GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural p F.B F.B (Fin d) z (hnil n z hz)).1
    have hq1 := GlobalTheory.T.hasVal_log_eval_of_hasVal_formalLog p F.B O F.Q F.θ hF (Fin d) z (hnil n z hz) E hE g q hg1 hq
    have hθ := GlobalTheory.T.theta_eval_eq_zeta_pow_digit p O ε hε F G d c χ g hgχ t n z hz (hnil n z hz) E hE
    obtain ⟨b, hb⟩ := pow_mul_logValue p O ε hε F n _ (E g) q hθ hq1
    set a := epsPairing hε G t χ
    obtain ⟨e, he⟩ := GlobalTheory.PDiv.pow_dvd_sub_digit n a
    have hy : F.a (Sandwich.mu ε * ofPadic p O a) = (GlobalTheory.PDiv.digit n a : F.B) * F.a (Sandwich.mu ε) + p ^ n * F.a (Sandwich.mu ε * ofPadic p O e) := by
      have h2 : ofPadic p O a = ofPadic p O (GlobalTheory.PDiv.digit n a : ℤ_[p]) + ofPadic p O ((p : ℤ_[p]) ^ n * e) := by
        rw [← map_add (f := _), ← he, add_sub_cancel]
      rw [h2]
      simp only [map_add (f := _), map_mul, map_pow, map_natCast]
      ring
    refine ⟨b - F.a (Sandwich.mu ε * ofPadic p O e), ?_⟩
    rw [hb, hy]
    congr 1
    ring
  first
  | exact ⟨hex, hcong⟩
  | exact hcong

end GlobalTheory.CharPeriod
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz

theorem Chart.zero_app_eq {p : ℕ} [Fact p.Prime] {k : Type} [CommRing k] (G : PDivGroup p k)
    (n : ℕ) (a : G.A n) :
    (0 : G ⟶ G).app n a = algebraMap k _ (Coalgebra.counit (R := k) a) := by
  have h := congrArg (fun u : WithConv (G.A n →ₐ[k] G.A n) => u.ofConv a)
    (map_one (toPts (R := k) (A := G.A n) (C := G.A n)))
  simp only [toPts_ofConv] at h
  exact h.trans (AlgHom.convOne_apply _)

theorem Chart.isMapOf_nmul : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] (d : ℕ)
    (G : PDivGroup p k) (c : Katz.Chart G d) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k),
    c.IsLawOf μ → ∀ j : ℕ, c.IsMapOf c ((j : ℤ_[p]) • 𝟙 G) (nmul μ j) := by
  intro p _ k _ d G c μ hμ j
  induction j with
  | zero =>
    intro n i
    rw [Nat.cast_zero, zero_smul, Chart.zero_app_eq, c.aug, map_zero]
    show c.ev n ((fun _ => (0 : MvPowerSeries (Fin d) k)) i) = 0
    exact map_zero _
  | succ j ih =>
    have hX : c.IsMapOf c (𝟙 G) (fun i => (X i : MvPowerSeries (Fin d) k)) := fun n i => by
      rw [Chart.ev_X, id_app]; rfl
    have e1 : ((j + 1 : ℕ) : ℤ_[p]) • 𝟙 G = (j : ℤ_[p]) • 𝟙 G + 𝟙 G := by
      rw [Nat.cast_succ, add_smul, one_smul]
    have e2 : nmul μ (j + 1) = op μ (nmul μ j) (fun i => X i) :=
      Function.iterate_succ_apply' _ _ _
    rw [e1, e2]
    exact Chart.isMapOf_add p k d d G G c c μ _ _ _ _ hμ ih hX

end GlobalTheory.Katz
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

theorem coeff_mem_ideal_of_formalGroupCoboundaryOne_coeff_mem : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ I : Ideal O, (p : O) ∈ I → ∀ s : MvPowerSeries (Fin d) O, (∀ α, coeff α (cob1 c.μ s) ∈ I) → ∀ α, coeff α s ∈ I := by
  intro p _ O _ G d c I hp s hs α
  obtain ⟨c', hlaw, -, -⟩ := GlobalTheory.T.exists_formalChart_quotient_by_ideal_with_primePow p O G d c I 1 (by rwa [pow_one])
  have hpk : ((p : ℕ) : O ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]; exact hp
  have hmap := (GlobalTheory.T.map_coboundary_swap_pullback_commute O d c.μ c.isLaw.const (O ⧸ I) (Ideal.Quotient.mk I)).1 s
  have hz : map (Ideal.Quotient.mk I) (cob1 c.μ s) = 0 := by
    ext β
    rw [coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact hs β
  rw [hz] at hmap
  have h0 := GlobalTheory.Katz.eq_zero_of_cob1_eq_zero p (O ⧸ I) hpk d (G.baseChange (O ⧸ I)) c'
    (fun i => map (Ideal.Quotient.mk I) (c.μ i)) hlaw (map (Ideal.Quotient.mk I) s) hmap.symm
  have := congrArg (coeff α) h0
  rwa [coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem] at this

end GlobalTheory.QLog
end

section

noncomputable section

namespace GlobalTheory.UPel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {F : Type} [Field F] [NumberField F] [IsCMField F] {D : Datum F} {p N : ℕ}
  {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp (D.OEp p)} {s₂ : S₂ ⟶ Sp (D.OEp p)} {s₃ : S₃ ⟶ Sp (D.OEp p)}
  {o₁ : Obj D p N s₁} {o₂ : Obj D p N s₂} {o₃ : Obj D p N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}

def ObjMap.comp (m₁ : ObjMap o₁ o₂ f) (m₂ : ObjMap o₂ o₃ g) : ObjMap o₁ o₃ (f ≫ g) where
  φ := m₁.φ ≫ m₂.φ
  cart := IsGrpPullback.comp m₁.cart m₂.cart
  act a := by rw [← Category.assoc, m₁.act, Category.assoc, m₂.act, Category.assoc]
  pol := LBIso.trans o₁.PP.isLB (pull_isLB o₂.PP.isLB m₁.φ) (pull_isLB o₃.PP.isLB _) m₁.pol
    (LBIso.chartPull (chartPullPull o₂.PP.L m₁.φ)
      (chartPullSame o₃.PP.L (fun _ : PUnit => m₁.φ ≫ m₂.φ) (fun _ => m₂.φ) (fun _ => 1) m₁.φ (fun _ => rfl))
      m₂.pol)
  eta a := by rw [← Category.assoc, m₁.eta, Category.assoc, m₂.eta, Category.assoc]

theorem objMap_comp : ∀ (F : Type) [Field F] [NumberField F] [IsCMField F] (D : GlobalTheory.UPel.Datum F) (p N : ℕ)
    (S₁ S₂ S₃ : Scheme.{0}) (s₁ : S₁ ⟶ Sp (D.OEp p)) (s₂ : S₂ ⟶ Sp (D.OEp p)) (s₃ : S₃ ⟶ Sp (D.OEp p))
    (o₁ : GlobalTheory.UPel.Obj D p N s₁) (o₂ : GlobalTheory.UPel.Obj D p N s₂) (o₃ : GlobalTheory.UPel.Obj D p N s₃) (f : S₁ ⟶ S₂)
    (g : S₂ ⟶ S₃), GlobalTheory.UPel.ObjMap o₁ o₂ f → GlobalTheory.UPel.ObjMap o₂ o₃ g → Nonempty (GlobalTheory.UPel.ObjMap o₁ o₃ (f ≫ g)) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m₁ m₂ => ⟨m₁.comp m₂⟩

end GlobalTheory.UPel
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.eq_zero_of_formalGroupLawCoboundaryOne_eq_zero : ∀ (p : ℕ) (k : Type) [CommRing k] (h : (p : k) = 0) (d : ℕ) (G : PDivGroup p k) (c : Chart G d) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ → ∀ b, cob1 μ b = 0 → b = 0 := by
  first | exact @GlobalTheory.Katz.eq_zero_of_cob1_eq_zero | exact GlobalTheory.Katz.eq_zero_of_cob1_eq_zero | (intros; apply GlobalTheory.Katz.eq_zero_of_cob1_eq_zero <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.isMapOf_add_formalGroupLawEvalPoints : ∀ (p : ℕ) (k : Type) [CommRing k] (d e : ℕ) (G H : PDivGroup p k) (c : Chart G d) (c' : Chart H e), ∀ (ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k) (f g : G ⟶ H) (φ ψ : Fin e → MvPowerSeries (Fin d) k), c'.IsLawOf ν → c.IsMapOf c' f φ → c.IsMapOf c' g ψ → c.IsMapOf c' (f + g) (op ν φ ψ) := by
  first | exact @GlobalTheory.Katz.Chart.isMapOf_add | exact GlobalTheory.Katz.Chart.isMapOf_add | (intros; apply GlobalTheory.Katz.Chart.isMapOf_add <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.lazard_additive_law_wittVectorFractionField_mod_p : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d N : ℕ) (e : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k)), 2 ≤ N → (∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree ≠ N → coeff γ e = 0) → cob2 (addLaw (Fr p k) d) e ∈ intBy p k _ p → swap e - e ∈ intBy p k _ p → ∃ h : MvPowerSeries (Fin d) (Fr p k), (∀ α : Fin d →₀ ℕ, α.degree ≠ N → coeff α h = 0) ∧ e - cob1 (addLaw (Fr p k) d) h ∈ intBy p k _ p := by
  first | exact @GlobalTheory.Katz.lazard_mod_p_frac | exact GlobalTheory.Katz.lazard_mod_p_frac | (intros; apply GlobalTheory.Katz.lazard_mod_p_frac <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.connectedPDivGroupChart_coboundaryTwo_coord : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), ∀ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ → ∀ n (h : ∀ i, IsNilpotent ((Sum.elim (fun i => c.x n i ⊗ₜ[k] (1 : G.A n ⊗[k] G.A n)) (fun j => (1 : G.A n) ⊗ₜ[k] c.x₂ n j)) i)), (∀ s, evA k _ h (cob2 μ s) = cobTwo k (G.A n) (c.ev₂ n s)) ∧ ∀ i, evA k _ h (op μ (op μ x1 x2) x3 i) = evA k _ h (op μ x1 (op μ x2 x3) i) := by
  first | exact @GlobalTheory.Katz.CobCoord.evA_cob2_eq_cobTwo_and_op_assoc | exact GlobalTheory.Katz.CobCoord.evA_cob2_eq_cobTwo_and_op_assoc | (intros; apply GlobalTheory.Katz.CobCoord.evA_cob2_eq_cobTwo_and_op_assoc <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.exists_rigidifiedExtension_of_series_pair : ∀ (p : ℕ) (k : Type) [Field k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), ∃ ρ : MvPowerSeries (Fin d ⊕ Fin d) k × (Fin d → k) →ₗ[k] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n)))))), (∀ s w (z : G.cocycles) (u : G.omega), (∀ n, z.1 n = c.ev₂ n s) → (∀ n, u.1 n = ∑ i, w i • dUnit (R := k) (c.x n i)) → ρ (s, w) = G.rigMk (z, u)) := by
  first | exact @GlobalTheory.Katz.exists_rigMap | exact GlobalTheory.Katz.exists_rigMap | (intros; apply GlobalTheory.Katz.exists_rigMap <;> assumption)
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

theorem _root_.GlobalTheory.T.isHilbertEisensteinLatticeValue_of_eisensteinSeries : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (G : (Emb F → ℂ) → ℂ) (w : Emb F → ℂ), Even k → IsEis 𝔞 𝔟 k G → w ∈ upperHalf F → IsGVal k (split 𝔞 𝔟 0) w 1 (((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F) ^ k * G w) := by
  first | exact @GlobalTheory.HilbFam.EisCmp.isGVal_of_isEis | exact GlobalTheory.HilbFam.EisCmp.isGVal_of_isEis | (intros; apply GlobalTheory.HilbFam.EisCmp.isGVal_of_isEis <;> assumption)
end
