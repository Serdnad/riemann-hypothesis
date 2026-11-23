module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.MapUgAlgebraMap
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.FiltrationSpanDividedPowers
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.OnlyIsotropic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.TestCover

section Ring

variable {S : Type*} [CommRing S]

theorem mem_of_compare {f g d : S} (h : Ideal.span {f, g} = ⊤) (h1 : d * f ∈ Ideal.span {g})
    (h2 : (1 - d) * g ∈ Ideal.span {f}) : d ∈ Ideal.span {g} ∧ 1 - d ∈ Ideal.span {f} := by
  obtain ⟨x, y, hxy⟩ := Ideal.mem_span_pair.1 (Ideal.eq_top_iff_one _ |>.1 h)
  constructor
  · have e : d = x * (d * f) + (d * y) * g := by
      linear_combination (-d) * hxy
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1)
      (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self g))
  · have e : 1 - d = ((1 - d) * x) * f + y * ((1 - d) * g) := by
      linear_combination (-(1 - d)) * hxy
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self f))
      (Ideal.mul_mem_left _ _ h2)

theorem idem_prod {ι : Type*} (t : Finset ι) (f : ι → S) (h : ∀ k, IsIdempotentElem (f k)) :
    IsIdempotentElem (∏ k ∈ t, f k) := by
  unfold IsIdempotentElem
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => h k

theorem span_top_of_prod {m : ℕ} (e : Fin m → S) (h : ∏ k, (1 - e k) = 0) :
    Ideal.span (Set.range e) = ⊤ := by
  rw [Ideal.eq_top_iff_one, ← Ideal.Quotient.eq_zero_iff_mem]
  have hk : ∀ k, Ideal.Quotient.mk (Ideal.span (Set.range e)) (1 - e k) = 1 := fun k => by
    have h0 : Ideal.Quotient.mk (Ideal.span (Set.range e)) (e k) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_range_self k))
    rw [map_sub, map_one, h0, sub_zero]
  have := congrArg (Ideal.Quotient.mk (Ideal.span (Set.range e))) h
  rw [map_prod, Finset.prod_congr rfl fun k _ => hk k, Finset.prod_const_one, map_zero] at this
  rw [map_one, this]

theorem idem_refine
    (hV : ∀ f g : S, Ideal.span {f, g} = ⊤ →
      ∃ e : S, IsIdempotentElem e ∧ e * f ∈ Ideal.span {g} ∧ (1 - e) * g ∈ Ideal.span {f}) :
    ∀ (m : ℕ) (s : Fin m → S) (c : S), IsIdempotentElem c → c ∈ Ideal.span (Set.range s) →
      ∃ e : Fin m → S, (∀ k, IsIdempotentElem (e k)) ∧ (∀ k, e k ∈ Ideal.span {s k}) ∧
        c * ∏ k, (1 - e k) = 0 := by
  intro m
  induction m with
  | zero =>
    intro s c _ hc
    have h0 : c = 0 := by
      rw [Set.range_eq_empty, Ideal.span_empty] at hc
      exact (Submodule.mem_bot _).1 hc
    exact ⟨Fin.elim0, fun k => k.elim0, fun k => k.elim0, by rw [h0, zero_mul]⟩
  | succ m ih =>
    intro s c hc hcs
    have hr : Set.range s = insert (s 0) (Set.range (Fin.tail s)) := by
      conv_lhs => rw [← Fin.cons_self_tail s]
      exact Fin.range_cons _ _
    rw [hr, Ideal.mem_span_insert] at hcs
    obtain ⟨a, r, hr', hcr⟩ := hcs
    have htop : Ideal.span {s 0, r + (1 - c)} = ⊤ := by
      rw [Ideal.eq_top_iff_one, Ideal.mem_span_pair]
      exact ⟨a, 1, by linear_combination -hcr⟩
    obtain ⟨d, hd, h1, h2⟩ := hV _ _ htop
    obtain ⟨hdg, hds⟩ := mem_of_compare htop h1 h2
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hdg
    have hcc : c * c = c := hc
    have hcd : IsIdempotentElem (c * d) := hc.mul hd
    have hmem : c * d ∈ Ideal.span (Set.range (Fin.tail s)) := by
      have e : c * d = (t * c) * r := by
        rw [← ht]
        linear_combination (-t) * hcc
      rw [e]
      exact Ideal.mul_mem_left _ _ hr'
    obtain ⟨e', hi, hm, hp⟩ := ih (Fin.tail s) (c * d) hcd hmem
    refine ⟨Fin.cons (1 - d) e', ?_, ?_, ?_⟩
    · intro k
      refine Fin.cases ?_ (fun i => ?_) k
      · simpa using hd.one_sub
      · simpa using hi i
    · intro k
      refine Fin.cases ?_ (fun i => ?_) k
      · simpa using hds
      · simpa [Fin.tail] using hm i
    · rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      linear_combination hp

end Ring

theorem test_cover : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), A.IsTest → ∀ {m : ℕ} (s : Fin m → A.U),
    Ideal.span (Set.range s) = ⊤ → ∃ e : Fin m → A.A, (∀ k, IsIdempotentElem (e k)) ∧
      Ideal.span (Set.range e) = ⊤ ∧ ∀ k, A.sharp (e k) ∈ Ideal.span {s k} := by
  intro l _ A hA m s hs
  have hV : ∀ f g : A.U, Ideal.span {f, g} = ⊤ →
      ∃ e : A.U, IsIdempotentElem e ∧ e * f ∈ Ideal.span {g} ∧ (1 - e) * g ∈ Ideal.span {f} :=
    fun f g h => hA.val_aic.1 f g ⟨0, by rw [pow_zero, h]; trivial⟩
  obtain ⟨u, hi, hm, hp⟩ := idem_refine hV m s 1 IsIdempotentElem.one (by rw [hs]; trivial)
  rw [one_mul] at hp
  have hex : ∀ k, ∃ e₀ : A.A, IsIdempotentElem e₀ ∧ A.sharp e₀ = u k := fun k =>
    (RL.idem_au A (u k) (hi k)).exists
  choose e he hsh using hex
  have hc := (RL.sharp_cong A).2.2
  have hzero : A.sharp 0 = 0 := by
    have := hc 1 IsIdempotentElem.one
    rwa [sub_self, map_one, sub_self] at this
  have hsp : A.sharp (∏ k, (1 - e k)) = 0 := by
    rw [map_prod, ← hp]
    exact Finset.prod_congr rfl fun k _ => by rw [hc _ (he k), hsh]
  have hidem : IsIdempotentElem (∏ k, (1 - e k)) :=
    idem_prod _ _ fun k => (he k).one_sub
  have h0 : ∏ k, (1 - e k) = 0 :=
    (RL.idem_au A 0 IsIdempotentElem.zero).unique ⟨hidem, hsp⟩ ⟨IsIdempotentElem.zero, hzero⟩
  exact ⟨e, he, span_top_of_prod e h0, fun k => by rw [hsh]; exact hm k⟩

end GlobalTheory.CompanionTheory.TestCover
end

section

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.OnlyStab

section Core

variable {K : Type} [Field K] {n : ℕ}

theorem prof_nonneg {τ : ℝ} (hτ : 0 ≤ τ) {k : ℕ} (hk : k ≤ n) : 0 ≤ prof n τ k := by
  have h : (k : ℝ) ≤ n := by exact_mod_cast hk
  have h0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  unfold prof
  exact mul_nonneg (mul_nonneg hτ h0) (by linarith)

theorem finrank_le_n (W : Submodule K (Fin n → K)) : Module.finrank K W ≤ n := by
  simpa using Submodule.finrank_le W

theorem prof_second_diff (τ : ℝ) (a b k : ℕ) (hab : a + b = 2 * k) :
    prof n τ a + prof n τ b = 2 * prof n τ k - 2 * τ * ((k : ℝ) - a) ^ 2 := by
  have h : (b : ℝ) = 2 * k - a := by
    have : ((a + b : ℕ) : ℝ) = ((2 * k : ℕ) : ℝ) := by rw [hab]
    push_cast at this
    linarith
  unfold prof
  rw [h]
  ring

theorem core (deg' : Submodule K (Fin n → K) → ℝ) (g : Submodule K (Fin n → K) → Submodule K (Fin n → K))
    (τ D : ℝ) (hτ : 0 < τ) (hD : D < 2 * τ) (hbdd : BddAbove (Set.range deg'))
    (hsub : ∀ W W', deg' W + deg' W' ≤ deg' (W ⊓ W') + deg' (W ⊔ W'))
    (hmove : ∀ W, deg' W - D ≤ deg' (g W))
    (hrank : ∀ W, Module.finrank K (g W) = Module.finrank K W)
    (hst : ∀ W, g W = W → deg' W ≤ prof n τ (Module.finrank K W)) (W₀ : Submodule K (Fin n → K)) :
    deg' W₀ ≤ prof n τ (Module.finrank K W₀) := by
  by_contra hW₀
  push Not at hW₀
  set ψ : Submodule K (Fin n → K) → ℝ := fun W => deg' W - prof n τ (Module.finrank K W) with hψ
  have hψb : BddAbove (Set.range ψ) := by
    obtain ⟨B, hB⟩ := hbdd
    refine ⟨B, ?_⟩
    rintro _ ⟨W, rfl⟩
    have h1 : deg' W ≤ B := hB ⟨W, rfl⟩
    have h2 := prof_nonneg (n := n) hτ.le (finrank_le_n W)
    simp only [hψ]
    linarith
  set s : ℝ := ⨆ W, ψ W with hs
  have hle : ∀ W, ψ W ≤ s := fun W => le_ciSup hψb W
  have hs0 : 0 < s := lt_of_lt_of_le (by simp only [hψ]; linarith) (hle W₀)
  have hε : 0 < min s (τ - D / 2) := lt_min hs0 (by linarith)
  obtain ⟨W, hW⟩ : ∃ W, s - min s (τ - D / 2) < ψ W :=
    exists_lt_of_lt_ciSup (by rw [hs]; linarith [hε])
  have hε1 : min s (τ - D / 2) ≤ s := min_le_left _ _
  have hε2 : min s (τ - D / 2) ≤ τ - D / 2 := min_le_right _ _
  by_cases hg : g W = W
  · have h := hst W hg
    simp only [hψ] at hW
    linarith
  · have hsum := Submodule.finrank_sup_add_finrank_inf_eq W (g W)
    rw [hrank W] at hsum
    have hne : W ⊓ g W ≠ W := fun h => hg
      (Submodule.eq_of_le_of_finrank_le (inf_eq_left.1 h) (by rw [hrank W])).symm
    have hlt : Module.finrank K (W ⊓ g W : Submodule K (Fin n → K)) < Module.finrank K W :=
      Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left hne)
    have hid := prof_second_diff (n := n) τ (Module.finrank K (W ⊓ g W : Submodule K (Fin n → K)))
      (Module.finrank K (W ⊔ g W : Submodule K (Fin n → K))) (Module.finrank K W) (by omega)
    have hj : (1 : ℝ) ≤ (Module.finrank K W : ℝ) - Module.finrank K (W ⊓ g W : Submodule K (Fin n → K)) := by
      have : ((Module.finrank K (W ⊓ g W : Submodule K (Fin n → K)) + 1 : ℕ) : ℝ) ≤ Module.finrank K W := by
        exact_mod_cast hlt
      push_cast at this
      linarith
    have hj2 : τ * 1 ≤ τ * ((Module.finrank K W : ℝ) - Module.finrank K (W ⊓ g W : Submodule K (Fin n → K))) ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith) hτ.le
    have h1 := hle (W ⊓ g W)
    have h2 := hle (W ⊔ g W)
    have h3 := hsub W (g W)
    have h4 := hmove W
    simp only [hψ] at h1 h2 hW
    linarith

end Core

section Global

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem finrank_img (g : GL (Fin n) E) (W : Submodule E (Fin n → E)) :
    Module.finrank E (img g W) = Module.finrank E W := by
  have hinj : Function.Injective (Matrix.toLin' g.val) := by
    intro a b hab
    have h : (g⁻¹ : GL (Fin n) E).val *ᵥ (g.val *ᵥ a) = (g⁻¹ : GL (Fin n) E).val *ᵥ (g.val *ᵥ b) := by
      simpa [Matrix.toLin'_apply] using congrArg (fun y => (g⁻¹ : GL (Fin n) E).val *ᵥ y) hab
    simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using h
  exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj W).symm

theorem conjSrc_invol (v : HeightOneSpectrum (𝓞 E)) :
    conjSrc (IsCMField.complexConj E).toRingEquiv (conjSrc (IsCMField.complexConj E).toRingEquiv v) = v :=
  (eq_conjSrc fun x => by
    rw [← conjPl_conjSrc (IsCMField.complexConj E).toRingEquiv v ((IsCMField.complexConj E).toRingEquiv x)]
    exact congrArg _ (IsCMField.complexConj_apply_apply E x)).symm

theorem conjFin_invol (x : Af E) :
    conjFin (IsCMField.complexConj E).toRingEquiv (conjFin (IsCMField.complexConj E).toRingEquiv x) = x := by
  have key : ∀ (v w : HeightOneSpectrum (𝓞 E)) (_ : w = v) (f : w.adicCompletion E → v.adicCompletion E),
      Continuous f → (∀ k : E, f (algebraMap E _ k) = algebraMap E _ k) → f (pLoc E w x) = pLoc E v x := by
    rintro _ v rfl f hf h
    exact congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hf continuous_id (funext h)) _
  refine FiniteAdeleRing.ext _ fun v => key v _ (conjSrc_invol v) (conjLoc _ v ∘ conjLoc _ _)
    ((conjLoc_spec _ _).1.comp (conjLoc_spec _ _).1) fun k => ?_
  rw [Function.comp_apply, (conjLoc_spec _ _).2.1, (conjLoc_spec _ _).2.1]
  exact congrArg _ (IsCMField.complexConj_apply_apply E k)

theorem pInf_conj (x : Ad E) : pInf E (conjAd E x) = starRingEnd (Cinf E) (pInf E x) :=
  (infEq E).symm_apply_apply _

theorem conjAd_invol (x : Ad E) : conjAd E (conjAd E x) = x :=
  ad_ext (by rw [pInf_conj, pInf_conj, starRingEnd_self_apply]) (conjFin_invol _)

theorem thetaA_invol (x : GA E n) : thetaA E n (thetaA E n x) = x := by
  refine Units.ext ?_
  ext i j
  change conjAd E (conjAd E (x.val i j)) = x.val i j
  exact conjAd_invol _

theorem ratGL_thetaE (d : GL (Fin n) E) : ratGL E n (thetaE E n d) = thetaA E n (ratGL E n d) := by
  refine Units.ext ?_
  ext i j
  have h : ((ratGL E n d)⁻¹ : GA E n) = ratGL E n d⁻¹ := (map_inv _ _).symm
  rw [thetaR_val, h]
  change algebraMap E (Ad E) (conjE E ((d⁻¹ : GL (Fin n) E).val j i)) =
    conjAd E (algebraMap E (Ad E) ((d⁻¹ : GL (Fin n) E).val j i))
  rw [conjAd_algebraMap]
  rfl

theorem conj_nrm (x : GA E n) (d : GL (Fin n) E) :
    x⁻¹ * ratGL E n (nrm d) * x =
      twConj (thetaA E n) x (ratGL E n d) * thetaA E n (twConj (thetaA E n) x (ratGL E n d)) := by
  simp only [twConj, nrm, map_mul, map_inv, thetaA_invol, ratGL_thetaE]
  group

end Global

theorem arith (C₁ C₂ c L l τ : ℝ) (hL0 : 0 ≤ L) (hl0 : 0 ≤ l) (hl : l ≤ 2 * L + |c|)
    (hτ : (1 + |C₁| * (2 + |c|) + |C₂|) * (1 + L) ≤ τ) :
    0 < τ ∧ C₁ * (1 + l) < 2 * τ ∧ C₂ * (1 + L) ≤ τ := by
  have ha : 0 ≤ |C₁| := abs_nonneg _
  have hb : 0 ≤ |C₂| := abs_nonneg _
  have hcc : 0 ≤ |c| := abs_nonneg _
  have hprod : 0 ≤ |C₁| * (2 + |c|) * (1 + L) := by positivity
  have hprod2 : 0 ≤ |C₂| * (1 + L) := by positivity
  have hτ' : 1 + L + |C₁| * (2 + |c|) * (1 + L) + |C₂| * (1 + L) ≤ τ := by
    calc _ = (1 + |C₁| * (2 + |c|) + |C₂|) * (1 + L) := by ring
      _ ≤ τ := hτ
  have hτ0 : 0 < τ := by linarith
  refine ⟨hτ0, ?_, ?_⟩
  · have e1 : C₁ * (1 + l) ≤ |C₁| * (1 + l) := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
    have e2 : |C₁| * (1 + l) ≤ |C₁| * (1 + (2 * L + |c|)) := mul_le_mul_of_nonneg_left (by linarith) ha
    have e3 : |C₁| * (1 + (2 * L + |c|)) ≤ |C₁| * (2 + |c|) * (1 + L) := by
      have : 0 ≤ |C₁| * (1 + |c| * L) := by positivity
      nlinarith
    linarith
  · have h3 : C₂ * (1 + L) ≤ |C₂| * (1 + L) := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
    linarith

theorem onlyStable_of : DegSubmod → DegMove → DegBdd → DegPairing → SizeBasic → OnlyStable := by
  intro hSub hMove hBdd hPair hSize E _ _ _ n
  obtain ⟨C₁, h₁⟩ := hMove E n
  obtain ⟨C₂, h₂⟩ := hPair E n
  obtain ⟨-, hnn, hθ, c, hc⟩ := hSize E n
  refine ⟨1 + |C₁| * (2 + |c|) + |C₂|, fun τ x d hτ => ?_⟩
  have hls : logSize (x⁻¹ * ratGL E n (nrm d) * x) ≤
      2 * logSize (twConj (thetaA E n) x (ratGL E n d)) + |c| := by
    rw [conj_nrm]
    have h := hc (twConj (thetaA E n) x (ratGL E n d)) (thetaA E n (twConj (thetaA E n) x (ratGL E n d)))
    rw [hθ] at h
    have := le_abs_self c
    linarith
  obtain ⟨hτ0, hD, hC₂⟩ := arith C₁ C₂ c _ _ τ (hnn _) (hnn _) hls hτ
  constructor
  · exact fun h W _ => h.1 W
  · intro hst
    refine ⟨fun W => ?_, ?_⟩
    · exact core (deg x) (img (nrm d)) τ _ hτ0 hD ((hBdd E n).1 x) (hSub E n x) (fun W => h₁ x (nrm d) W)
        (fun W => finrank_img _ W) hst W
    · have h := (h₂ x d).2
      have := neg_abs_le (deg x (⊤ : Submodule E (Fin n → E)))
      linarith

end GlobalTheory.CompanionTheory.OnlyStab
end

section

open NumberField Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
open GlobalTheory.CuspRep PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.IsotropicDegreeBound

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem conjE_conjE (a : E) : conjE E (conjE E a) = a :=
  IsCMField.complexConj_apply_apply E a

theorem mem_perpD_iff (d : GL (Fin n) E) (W : Submodule E (Fin n → E)) (y : Fin n → E) :
    y ∈ perpD (conjE E) d W ↔ ∀ x ∈ W, (conjE E ∘ x) ⬝ᵥ ((d⁻¹).val *ᵥ y) = 0 := by
  have key : y ∈ perpD (conjE E) d W ↔ (d⁻¹).val *ᵥ y ∈ perp (conjE E) W := by
    constructor
    · rintro ⟨z, hz, rfl⟩
      have : (d⁻¹).val *ᵥ (Matrix.toLin' d.val z) = z := by
        rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec]
      rw [this]
      exact hz
    · intro h
      refine ⟨_, h, ?_⟩
      rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
  rw [key]
  exact Iff.rfl

theorem gram_nrm (d : GL (Fin n) E) :
    ((nrm d).val.map (conjE E))ᵀ * (d⁻¹).val * (nrm d).val = (d⁻¹).val := by
  set D := d.val with hD
  set Di := (d⁻¹).val with hDi
  have hval : (nrm d).val = D * (Di.map (conjE E))ᵀ := by
    simp only [nrm, Units.val_mul]
    rfl
  have hinv : Di * D = 1 := by
    rw [hDi, hD, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hc : (Di.map (conjE E)) * (D.map (conjE E)) = 1 := by
    rw [← Matrix.map_mul, hinv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hcc : (Di.map (conjE E)).map (conjE E) = Di := by
    ext i j
    simp [conjE_conjE]
  have hm : ((nrm d).val.map (conjE E))ᵀ = Di * (D.map (conjE E))ᵀ := by
    rw [hval, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_map, Matrix.transpose_transpose, hcc]
  rw [hm, hval]
  calc Di * (D.map (conjE E))ᵀ * Di * (D * (Di.map (conjE E))ᵀ)
      = Di * (D.map (conjE E))ᵀ * (Di * D) * (Di.map (conjE E))ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = Di * ((Di.map (conjE E)) * (D.map (conjE E)))ᵀ := by
        rw [hinv, Matrix.transpose_mul, Matrix.mul_one, Matrix.mul_assoc]
    _ = Di := by rw [hc, Matrix.transpose_one, Matrix.mul_one]

theorem pairing_nrm (d : GL (Fin n) E) (u v : Fin n → E) :
    (conjE E ∘ ((nrm d).val *ᵥ u)) ⬝ᵥ ((d⁻¹).val *ᵥ ((nrm d).val *ᵥ v)) =
      (conjE E ∘ u) ⬝ᵥ ((d⁻¹).val *ᵥ v) := by
  have h1 : conjE E ∘ ((nrm d).val *ᵥ u) = ((nrm d).val.map (conjE E)) *ᵥ (conjE E ∘ u) := by
    funext i
    exact RingHom.map_mulVec (conjE E) (nrm d).val u i
  rw [h1, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    gram_nrm]

theorem img_nrm_inf (d : GL (Fin n) E) (W : Submodule E (Fin n → E)) (hW : img (nrm d) W = W) :
    img (nrm d) (W ⊓ perpD (conjE E) d W) = W ⊓ perpD (conjE E) d W := by
  have hinj : Function.Injective (Matrix.toLin' (nrm d).val) := by
    intro a b hab
    have h := congrArg (fun z => ((nrm d)⁻¹).val *ᵥ z) hab
    simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul] using h
  have hle : img (nrm d) (W ⊓ perpD (conjE E) d W) ≤ W ⊓ perpD (conjE E) d W := by
    rintro _ ⟨y, ⟨hyW, hyP⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · have : Matrix.toLin' (nrm d).val y ∈ img (nrm d) W := ⟨y, hyW, rfl⟩
      rwa [hW] at this
    · rw [SetLike.mem_coe, mem_perpD_iff]
      intro x hx
      rw [← hW] at hx
      obtain ⟨x', hx', rfl⟩ := hx
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, pairing_nrm]
      exact (mem_perpD_iff d W y).1 hyP x' hx'
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  exact (Submodule.equivMapOfInjective _ hinj _).finrank_eq.symm

theorem inf_le_perpD_inf (d : GL (Fin n) E) (W : Submodule E (Fin n → E)) :
    W ⊓ perpD (conjE E) d W ≤ perpD (conjE E) d (W ⊓ perpD (conjE E) d W) := by
  intro y hy
  rw [mem_perpD_iff]
  exact fun x hx => (mem_perpD_iff d W y).1 hy.2 x hx.1

theorem prof_gap {τ : ℝ} (hτ : 0 ≤ τ) {a b m : ℕ} (hab : a < b) (hbm : b ≤ m) :
    prof m τ a + 2 * τ ≤ prof m τ b := by
  have h1 : (a : ℝ) + 1 ≤ b := by exact_mod_cast hab
  have h2 : (b : ℝ) ≤ m := by exact_mod_cast hbm
  have h3 : (2 : ℝ) ≤ ((b : ℝ) - a) * (2 * m + 1 - a - b) := by
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (by linarith : (0 : ℝ) ≤ 2 * m - 1 - a - b)]
  have h4 := mul_nonneg hτ (sub_nonneg.2 h3)
  simp only [prof]
  nlinarith

theorem onlyIsotropic_of : OnlyStable → DegPairing → SizeBasic → OnlyIsotropic := by
  intro h1 h2 h3 E _ _ _ n
  obtain ⟨C₁, hC₁⟩ := h1 E n
  obtain ⟨C₂, hC₂⟩ := h2 E n
  refine ⟨max 0 (max C₁ C₂), fun τ x d hτ => ?_⟩
  have hs0 : 0 ≤ logSize (twConj (thetaA E n) x (ratGL E n d)) := (h3 E n).2.1 _
  have hs1 : 0 ≤ 1 + logSize (twConj (thetaA E n) x (ratGL E n d)) := by linarith
  have l₁ : C₁ ≤ max 0 (max C₁ C₂) := (le_max_left _ _).trans (le_max_right _ _)
  have l₂ : C₂ ≤ max 0 (max C₁ C₂) := (le_max_right _ _).trans (le_max_right _ _)
  have hτ₁ := le_trans (mul_le_mul_of_nonneg_right l₁ hs1) hτ
  have hτ₂ := le_trans (mul_le_mul_of_nonneg_right l₂ hs1) hτ
  have hτ₀ : 0 ≤ τ := le_trans (mul_nonneg (le_max_left _ _) hs1) hτ
  refine ⟨fun hx W _ _ => hx.1 W, fun h => (hC₁ τ x d hτ₁).2 fun W hW => ?_⟩
  have hb := h _ (img_nrm_inf d W hW) (inf_le_perpD_inf d W)
  by_cases heq : W ⊓ perpD (conjE E) d W = W
  · exact h W hW (inf_eq_left.1 heq)
  · have hlt : W ⊓ perpD (conjE E) d W < W := lt_of_le_of_ne inf_le_left heq
    have hr := Submodule.finrank_lt_finrank_of_lt hlt
    have hn : Module.finrank E W ≤ n := by simpa using Submodule.finrank_le W
    have hg := prof_gap hτ₀ hr hn
    have hp := (hC₂ x d).1 W hW
    linarith

end GlobalTheory.CompanionTheory.IsotropicDegreeBound
end
