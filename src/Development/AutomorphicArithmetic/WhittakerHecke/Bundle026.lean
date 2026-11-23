module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle347
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Bundle001
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle014
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.ThInf
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.IsotypQuot
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle001
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle021
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle018
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle015
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.PSeriesComplex
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.bottomRow_congruence_iff_idele_congruence :
    ∀ N : ℕ, 0 < N → ∀ k ∈ KK ℚ, k ∈ SS N → ∀ ζ : (A ℚ)ˣ, ζ ∈ UU → (∀ v : H.P ℚ, (Bad N v → Dv N v ((ζ : A ℚ) * k 1 1 - 1)) ∧ (¬ Bad N v → H.cp v (ζ : A ℚ) = 1)) → ∀ y : (A ℚ)ˣ, (∀ v, Dv N v ((y : A ℚ) * (ζ : A ℚ) * k 1 0) ∧ Dv N v ((y : A ℚ) * (ζ : A ℚ) * k 1 1 - 1)) ↔ ((∀ v, Bad N v → Dv N v (((y : (A ℚ)ˣ) : A ℚ) - 1)) ∧ ∀ v : H.P ℚ, Valued.v (H.cp v ((y : (A ℚ)ˣ) : A ℚ)) ≤ 1) := by
  intro N hN k hk hS ζ hζ hz y
  have hi : ∀ v i j, Valued.v (H.cp v (k i j)) ≤ 1 := fun v i j => hk.2 v i j
  have hN1 : ∀ v : H.P ℚ, Valued.v (N : H.Kv v) ≤ 1 := fun v =>
    show (N : H.Kv v) ∈ v.adicCompletionIntegers ℚ from natCast_mem _ N
  have hv : ∀ v : H.P ℚ, (Bad N v → Valued.v (N : H.Kv v) < 1) ∧ (¬ Bad N v → Valued.v (N : H.Kv v) = 1) := fun v => by
    have h1 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) v (N : 𝓞 ℚ)
    rw [HeightOneSpectrum.valuation_of_algebraMap] at h1
    have h2 : Valued.v (N : H.Kv v) = v.intValuation (N : 𝓞 ℚ) := by simpa using h1
    rw [h2]
    exact ⟨fun h => (v.intValuation_lt_one_iff_mem _).2 h, fun h => HeightOneSpectrum.intValuation_eq_one_iff.2 h⟩
  have key : ∀ v : H.P ℚ, (Dv N v ((y : A ℚ) * (ζ : A ℚ) * k 1 0) ∧ Dv N v ((y : A ℚ) * (ζ : A ℚ) * k 1 1 - 1)) ↔
      ((Bad N v → Dv N v ((y : A ℚ) - 1)) ∧ Valued.v (H.cp v (y : A ℚ)) ≤ 1) := fun v => by
    have hd : H.cp v (k 0 0) * H.cp v (k 1 1) - H.cp v (k 0 1) * H.cp v (k 1 0) = 1 := by
      have := congrArg (H.cp v) ((Matrix.det_fin_two k.1).symm.trans k.2)
      simpa using this
    have hs := hS v
    have hz' := hz v
    have hu := hζ.2 v
    have i00 := hi v 0 0
    have i01 := hi v 0 1
    have i10 := hi v 1 0
    have i11 := hi v 1 1
    simp only [Dv, map_mul, map_sub, map_one] at hs hz' ⊢
    generalize H.cp v (k 0 0) = a at *
    generalize H.cp v (k 0 1) = b at *
    generalize H.cp v (k 1 0) = c at *
    generalize H.cp v (k 1 1) = d at *
    generalize H.cp v (y : A ℚ) = x at *
    generalize H.cp v (ζ : A ℚ) = z at *
    by_cases hb : Bad N v
    · have h1 := hz'.1 hb
      have hlt := (hv v).1 hb
      have h2 : Valued.v (z * d) = 1 := by
        have := Valuation.map_one_add_of_lt Valued.v (h1.trans_lt hlt)
        rwa [add_sub_cancel] at this
      constructor
      · rintro ⟨-, h3⟩
        have h4 : Valued.v x ≤ 1 := by
          have := Valuation.map_one_add_of_lt Valued.v (h3.trans_lt hlt)
          rw [add_sub_cancel, mul_assoc, map_mul, h2, mul_one] at this
          exact this.le
        refine ⟨fun _ => ?_, h4⟩
        rw [show x - 1 = (x * z * d - 1) - x * (z * d - 1) by ring]
        exact Valuation.map_sub_le _ h3 (by rw [map_mul]; exact (mul_le_mul' h4 h1).trans_eq (one_mul _))
      · rintro ⟨h3, h4⟩
        refine ⟨by rw [hu, mul_one]; exact (mul_le_mul' h4 hs).trans_eq (one_mul _), ?_⟩
        rw [show x * z * d - 1 = (x - 1) * (z * d) + (z * d - 1) by ring]
        exact Valuation.map_add_le _ (by rw [map_mul, h2, mul_one]; exact h3 hb) h1
    · obtain rfl := hz'.2 hb
      rw [(hv v).2 hb]
      simp only [map_one, mul_one]
      constructor
      · rintro ⟨h3, h4⟩
        refine ⟨fun h => absurd h hb, ?_⟩
        rw [show x = a * ((x * d - 1) + 1) - b * (x * c) by linear_combination (-x) * hd]
        refine Valuation.map_sub_le _ ?_ ?_
        · rw [map_mul]
          exact mul_le_one' i00 (Valuation.map_add_le _ h4 (map_one _).le)
        · rw [map_mul, map_mul]
          exact mul_le_one' i01 h3
      · rintro ⟨-, h4⟩
        exact ⟨mul_le_one' h4 i10, Valuation.map_sub_le _ (by rw [map_mul]; exact mul_le_one' h4 i11) (map_one _).le⟩
  simp only [key, forall_and]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.hasSum_coprime_inv_pow_two_mul_eq_LSeries :
    ∀ (N : ℕ) (s : ℂ), 0 < N → 1 < s.re → HasSum (fun n : {n : ℕ // 0 < n ∧ n.Coprime N} => ((n : ℕ) : ℂ) ^ (-(2 * s))) (LSeries (sqN N) s) := by
  intro N s _ hs
  have hsum : Summable fun n : {n : ℕ // 0 < n ∧ n.Coprime N} => ((n : ℕ) : ℂ) ^ (-(2 * s)) := by
    have h : Summable fun n : ℕ => 1 / (n : ℂ) ^ (2 * s) :=
      Complex.summable_one_div_nat_cpow.2 (by simp; linarith)
    refine (h.subtype _).congr fun n => ?_
    simp [Complex.cpow_neg]
  have hinj : Function.Injective fun m : {n : ℕ // 0 < n ∧ n.Coprime N} => (m : ℕ) * m := fun a b e =>
    Subtype.ext (Nat.mul_self_inj.1 e)
  have h2 : HasSum (LSeries.term (sqN N) s) (∑' n : {n : ℕ // 0 < n ∧ n.Coprime N}, ((n : ℕ) : ℂ) ^ (-(2 * s))) := by
    refine (hinj.hasSum_iff fun x hx => ?_).1 ?_
    · rcases eq_or_ne x 0 with rfl | h0
      · simp
      · rw [LSeries.term_of_ne_zero h0, sqN, if_neg, zero_div]
        rintro ⟨m, rfl, hm⟩
        exact hx ⟨⟨m, Nat.pos_of_ne_zero fun e => h0 (by simp [e]), hm⟩, rfl⟩
    · convert hsum.hasSum using 1
      funext m
      have h0 : (m : ℕ) * m ≠ 0 := mul_ne_zero m.2.1.ne' m.2.1.ne'
      rw [Function.comp_apply, LSeries.term_of_ne_zero h0, sqN, if_pos ⟨m, rfl, m.2.2⟩, Nat.cast_mul,
        Complex.natCast_mul_natCast_cpow, Complex.cpow_neg, two_mul,
        Complex.cpow_add _ _ (Nat.cast_ne_zero.2 m.2.1.ne'), one_div]
  rw [LSeries, h2.tsum_eq]
  exact hsum.hasSum
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem cp_pv (v w : H.P ℚ) :
    H.cp v ((pv w : (A ℚ)ˣ) : A ℚ) = if w = v then ((atFin v (unif v) : (H.Kv v)ˣ) : H.Kv v) else 1 := by
  obtain ⟨-, -, h3, h4, -, -, -, h8, -⟩ := UpperTheory.ConvolutionTheory.R2.H.sgLaws ℚ w
  rw [pv, h4, map_add (f := _), map_one]
  split_ifs with h
  · subst h
    rw [h3, add_sub_cancel]
  · have : H.cp v (H.sg w (((atFin w (unif w) : (H.Kv w)ˣ) : H.Kv w) - 1)) = 0 := (h8 _).2 v (Ne.symm h)
    rw [this, add_zero]

private theorem fin_supp {n : ℕ} : (Function.mulSupport fun v : H.P ℚ => pv v ^ n.factorization (normV v)).Finite := by
  refine (n.factorization.support.finite_toSet.preimage GlobalTheory.TwAtt.normV_injective.injOn).subset fun v hv => ?_
  exact Finsupp.mem_support_iff.2 fun (h : n.factorization (normV v) = 0) => hv (by simp only [h, pow_zero])

private theorem cp_pin (n : ℕ) (v : H.P ℚ) :
    H.cp v ((pin n : (A ℚ)ˣ) : A ℚ) = ((atFin v (unif v) : (H.Kv v)ˣ) : H.Kv v) ^ n.factorization (normV v) := by
  have h := ((H.cp v).toMonoidHom.comp (Units.coeHom (A ℚ))).map_finprod (fin_supp (n := n))
  refine h.trans ((finprod_eq_single _ v fun w hw => ?_).trans ?_)
  · rw [map_pow]
    change H.cp v ((pv w : (A ℚ)ˣ) : A ℚ) ^ _ = 1
    rw [cp_pv, if_neg hw, one_pow]
  · rw [map_pow]
    change H.cp v ((pv v : (A ℚ)ˣ) : A ℚ) ^ _ = _
    rw [cp_pv, if_pos rfl]

private theorem val_nat (v : H.P ℚ) (n : ℕ) : Valued.v (n : H.Kv v) = v.intValuation (n : 𝓞 ℚ) := by
  have h1 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) v (n : 𝓞 ℚ)
  rw [HeightOneSpectrum.valuation_of_algebraMap] at h1
  simpa using h1

private theorem fst_pin (n : ℕ) : ((pin n : (A ℚ)ˣ) : A ℚ).1 = 1 := by
  have h := ((RingHom.fst (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)).toMonoidHom.comp
    (Units.coeHom (A ℚ))).map_finprod (fin_supp (n := n))
  refine h.trans (finprod_eq_one_of_forall_eq_one fun w => ?_)
  rw [map_pow]
  exact one_pow _

private theorem iy_val {r : ℝ} (hr : r ≠ 0) :
    ((iy r : (A ℚ)ˣ) : A ℚ).1 = TR.infEq ℚ (fun _ => r) ∧ ∀ v : H.P ℚ, H.cp v ((iy r : (A ℚ)ˣ) : A ℚ) = 1 := by
  rw [iy, dite_eq_right hr]
  have e : ∀ u : (TR.Rinf ℚ)ˣ, ((TR.infId ℚ u : (A ℚ)ˣ) : A ℚ) = 1 - TR.sInf ℚ 1 + TR.sInf ℚ u := fun _ => rfl
  rw [e]
  refine ⟨?_, fun v => ?_⟩
  · change 1 - TR.infEq ℚ 1 + TR.infEq ℚ _ = _
    rw [map_one, sub_self, zero_add]
  · rw [map_add (f := _), map_sub, map_one]
    change 1 - 0 + 0 = _
    simp

theorem UpperTheory.exists_factorization_of_ideleCongruence_divisor_level :
    ∀ (L N : ℕ), 0 < N → L ∣ N → (∀ v, Bad N v → Bad L v) → ∀ y : (A ℚ)ˣ, (∀ v, Bad N v → Dv L v ((y : A ℚ) - 1)) → (∀ v : H.P ℚ, ¬ Bad N v → Valued.v (H.cp v (y : A ℚ)) ≤ 1) → ∃ (n : ℕ) (r : ℝ) (τ : (A ℚ)ˣ), 0 < n ∧ n.Coprime N ∧ r ≠ 0 ∧ τ ∈ TT L ∧ y = iy r * pin n * τ := by
  intro L N hN hLN hbad y h1 h2
  have hv : ∀ (M : ℕ) (v : H.P ℚ), (Bad M v → Valued.v (M : H.Kv v) < 1) ∧ (¬ Bad M v → Valued.v (M : H.Kv v) = 1) := fun M v => by
    rw [val_nat]
    exact ⟨fun h => (v.intValuation_lt_one_iff_mem _).2 h, fun h => HeightOneSpectrum.intValuation_eq_one_iff.2 h⟩
  have hb : ∀ v, Bad N v → Valued.v (H.cp v (y : A ℚ)) = 1 := fun v h => by
    have h3 := (h1 v h).trans_lt ((hv L v).1 (hbad v h))
    rw [map_sub, map_one] at h3
    have := Valuation.map_one_add_of_lt Valued.v h3
    rwa [add_sub_cancel] at this
  have hle : ∀ v, Valued.v (H.cp v (y : A ℚ)) ≤ 1 := fun v => by
    by_cases h : Bad N v
    exacts [(hb v h).le, h2 v h]
  have hinv : ∀ v, H.cp v (y : A ℚ) * H.cp v ((y⁻¹ : (A ℚ)ˣ) : A ℚ) = 1 := fun v => by
    rw [← map_mul, Units.mul_inv, map_one]
  have hne : ∀ v, Valued.v (H.cp v (y : A ℚ)) ≠ 0 := fun v =>
    (Valuation.ne_zero_iff _).2 (left_ne_zero_of_mul_eq_one (hinv v))
  have hex : ∀ v, ∃ e : ℕ, Valued.v (H.cp v (y : A ℚ)) = WithZero.exp (-1 : ℤ) ^ e := fun v => by
    have h3 : WithZero.log (Valued.v (H.cp v (y : A ℚ))) ≤ 0 := by
      rw [← WithZero.exp_le_exp, WithZero.exp_log (hne v)]
      exact hle v
    refine ⟨(-WithZero.log (Valued.v (H.cp v (y : A ℚ)))).toNat, ?_⟩
    rw [← WithZero.exp_nsmul, nsmul_eq_mul, Int.toNat_of_nonneg (by omega), mul_neg_one, neg_neg, WithZero.exp_log (hne v)]
  choose e he using hex
  have he0 : ∀ v, Valued.v (H.cp v (y : A ℚ)) = 1 → e v = 0 := fun v h => by
    rw [he v, ← WithZero.exp_nsmul, WithZero.exp_eq_one] at h
    simpa using h
  have hfin : (Function.support e).Finite := by
    have h3 : ∀ᶠ v : H.P ℚ in cofinite, ((y⁻¹ : (A ℚ)ˣ) : A ℚ).2 v ∈ v.adicCompletionIntegers ℚ := ((y⁻¹ : (A ℚ)ˣ) : A ℚ).2.2
    refine (Filter.eventually_cofinite.1 h3).subset fun v hv' h4 => hv' (he0 v (le_antisymm (hle v) ?_))
    have h5 := congrArg Valued.v (hinv v)
    rw [map_mul, map_one] at h5
    have h6 : Valued.v (H.cp v ((y⁻¹ : (A ℚ)ˣ) : A ℚ)) ≤ 1 := h4
    exact h5.symm.trans_le (mul_le_of_le_one_right' h6)
  let f : ℕ →₀ ℕ := Finsupp.mapDomain normV (Finsupp.ofSupportFinite e hfin)
  have hf : ∀ v, f (normV v) = e v := fun v => Finsupp.mapDomain_apply_of_injective GlobalTheory.TwAtt.normV_injective _ v
  have hfs : ∀ p ∈ f.support, ∃ v : H.P ℚ, normV v = p := fun p hp => by
    obtain ⟨v, -, hv'⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hp)
    exact ⟨v, hv'⟩
  have hpr : ∀ p ∈ f.support, p.Prime := fun p hp => (hfs p hp).elim fun v h => h ▸ GlobalTheory.TwAtt.normV_prime v
  have hfac := Nat.prod_pow_factorization_eq_self hpr
  set n := f.prod (· ^ ·) with hn
  have hn0 : 0 < n := Finset.prod_pos fun p hp => pow_pos (hpr p hp).pos _
  have hr : re (y : A ℚ) ≠ 0 := by
    have h3 := congrFun (congrArg (TR.pInf ℚ) y.mul_inv) Rat.infinitePlace
    rw [map_mul, map_one] at h3
    exact left_ne_zero_of_mul_eq_one h3
  obtain ⟨i1, i2⟩ := iy_val hr
  have hτ : ∀ v, H.cp v ((pin n : (A ℚ)ˣ) : A ℚ) * H.cp v (((iy (re (y : A ℚ)) * pin n)⁻¹ * y : (A ℚ)ˣ) : A ℚ) =
      H.cp v (y : A ℚ) := fun v => by
    conv_rhs => rw [← mul_inv_cancel_left (iy (re (y : A ℚ)) * pin n) y, Units.val_mul, Units.val_mul, map_mul, map_mul, i2,
      one_mul]
  have hu : ∀ v, Valued.v (H.cp v (((iy (re (y : A ℚ)) * pin n)⁻¹ * y : (A ℚ)ˣ) : A ℚ)) = 1 := fun v => by
    have h3 := congrArg Valued.v (hτ v)
    rw [map_mul, cp_pin, map_pow, unif_spec v, hfac, hf, ← he v] at h3
    exact (mul_eq_left₀ (hne v)).1 h3
  refine ⟨n, re (y : A ℚ), (iy (re (y : A ℚ)) * pin n)⁻¹ * y, hn0, ?_, hr, ⟨⟨?_, hu⟩, fun v => ?_⟩,
    (mul_inv_cancel_left _ _).symm⟩
  · refine Nat.Coprime.prod_left fun p hp => Nat.Coprime.pow_left _ (((hpr p hp).coprime_iff_not_dvd).2 fun hd => ?_)
    obtain ⟨v, rfl⟩ := hfs p hp
    exact Finsupp.mem_support_iff.1 hp ((hf v).trans (he0 v (hb v ((GlobalTheory.TwAtt.mem_iff v N).2 hd))))
  · have h3 : ((iy (re (y : A ℚ)) * pin n : (A ℚ)ˣ) : A ℚ).1 = (y : A ℚ).1 := by
      change ((iy (re (y : A ℚ)) : (A ℚ)ˣ) : A ℚ).1 * ((pin n : (A ℚ)ˣ) : A ℚ).1 = _
      rw [i1, fst_pin, mul_one, ← RingEquiv.eq_symm_apply]
      funext w
      rw [Subsingleton.elim w Rat.infinitePlace]
      rfl
    have h4 : (((iy (re (y : A ℚ)) * pin n)⁻¹ : (A ℚ)ˣ) : A ℚ).1 * ((iy (re (y : A ℚ)) * pin n : (A ℚ)ˣ) : A ℚ).1 = 1 :=
      congrArg Prod.fst (Units.inv_mul (iy (re (y : A ℚ)) * pin n))
    rw [h3] at h4
    exact h4
  · by_cases h : Bad N v
    · have h3 := hτ v
      rw [cp_pin, hfac, hf, he0 v (hb v h), pow_zero, one_mul] at h3
      have h4 := h1 v h
      simp only [Dv, map_sub] at h4 ⊢
      rwa [h3]
    · have h3 : ¬ Bad L v := fun h' => h ((GlobalTheory.TwAtt.mem_iff v N).2 (((GlobalTheory.TwAtt.mem_iff v L).1 h').trans hLN))
      simp only [Dv, map_sub, map_one]
      rw [(hv L v).2 h3]
      exact Valuation.map_sub_le _ (hu v).le (map_one _).le
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

theorem UpperTheory.measurePreserving_idele_scale_and_conj_on_maximalCompact :
    ∀ (M₀ : Meas ℚ) (t : ℝ) (u : IdeleGroup ℚ), u ∈ UU →
        MeasurePreserving (fun p : IdeleGroup ℚ × G1 ℚ => (Un.aa t u p.1, cD u p.2)) M₀.ν M₀.ν ∧
        MeasurableEmbedding (fun p : IdeleGroup ℚ × G1 ℚ => (Un.aa t u p.1, cD u p.2)) := by
  intro M₀ t u hu
  haveI := M₀.prob
  let c : IdeleGroup ℚ := (iy (Real.exp t) * u : (A ℚ)ˣ)
  have h1 : MeasurePreserving (fun z : IdeleGroup ℚ => c * z⁻¹) (ideleMeasure ℚ) (ideleMeasure ℚ) :=
    (measurePreserving_mul_left (ideleMeasure ℚ) c).comp (Measure.measurePreserving_inv (ideleMeasure ℚ))
  have h2 : MeasurePreserving (cD u : G1 ℚ → G1 ℚ) M₀.κ M₀.κ :=
    ⟨(M.continuous_cD u).measurable, UpperTheory.maximalCompact_measure_map_conjDiag_eq M₀ u hu⟩
  let e1 : IdeleGroup ℚ ≃ᵐ IdeleGroup ℚ := (MeasurableEquiv.inv (IdeleGroup ℚ)).trans (MeasurableEquiv.mulLeft c)
  let e2 : G1 ℚ ≃ᵐ G1 ℚ :=
    { toFun := cD u
      invFun := cD (u⁻¹ : (A ℚ)ˣ)
      left_inv := fun g => by rw [M.cD_cD, inv_mul_cancel, M.cD_one]
      right_inv := fun g => by rw [M.cD_cD, mul_inv_cancel, M.cD_one]
      measurable_toFun := (M.continuous_cD u).measurable
      measurable_invFun := (M.continuous_cD _).measurable }
  exact ⟨h1.prod h2, (e1.prodCongr e2).measurableEmbedding⟩
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem gen {T U P Y Q : Type*} [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace P] [MeasurableSpace Y]
    [MeasurableSpace Q] [Countable Q] [MeasurableSingletonClass Q]
    (τ : Measure T) (υ : Measure U) (ν : Measure P) (μ : Measure Y) [SFinite τ] [SFinite υ] [SFinite ν] [SFinite μ]
    (f : T → U → P → Q → Y) (hf : Measurable fun x : T × U × P × Q => f x.1 x.2.1 x.2.2.1 x.2.2.2) (c : ℝ≥0)
    (hc : ∀ p, ∀ h : Y → ℝ≥0∞, Measurable h → ∫⁻ t, ∫⁻ u, ∑' α, h (f t u p α) ∂υ ∂τ = c * ∫⁻ y, h y ∂μ)
    (H : Y × P → ℂ) (hH : Measurable H) (hI : Integrable H (μ.prod ν)) :
    (∀ᵐ t ∂τ, ∀ᵐ u ∂υ, ∀ᵐ p ∂ν, Summable fun α => H (f t u p α, p)) ∧
      ∫ t, ∫ u, ∫ p, ∑' α, H (f t u p α, p) ∂ν ∂υ ∂τ = (c : ℂ) * ∫ q, H q ∂(μ.prod ν) := by
  let Ψ : T × U × P × Q → Y × P := fun x => (f x.1 x.2.1 x.2.2.1 x.2.2.2, x.2.2.1)
  have hΨ : Measurable Ψ := hf.prodMk (measurable_fst.comp (measurable_snd.comp measurable_snd))
  let m : Measure (T × U × P × Q) := τ.prod (υ.prod (ν.prod Measure.count))
  have hmap : m.map Ψ = c • μ.prod ν := by
    refine Measure.ext_of_lintegral _ fun h hh => ?_
    have hΨh : Measurable fun x => h (Ψ x) := hh.comp hΨ
    have hG : Measurable fun x : T × U × P => ∑' α, h (f x.1 x.2.1 x.2.2 α, x.2.2) :=
      Measurable.tsum fun α => hΨh.comp (f := fun x : T × U × P => (x.1, x.2.1, x.2.2, α)) (by fun_prop)
    rw [lintegral_map hh hΨ, lintegral_smul_measure, lintegral_prod _ hΨh.aemeasurable, lintegral_prod_symm _ hh.aemeasurable]
    have e1 : ∀ t, ∫⁻ y, h (Ψ (t, y)) ∂(υ.prod (ν.prod Measure.count)) =
        ∫⁻ p, ∫⁻ u, ∑' α, h (f t u p α, p) ∂υ ∂ν := by
      intro t
      have a1 : Measurable fun y : U × P × Q => h (Ψ (t, y)) := hΨh.comp measurable_prodMk_left
      have a2 : Measurable (Function.uncurry fun (u : U) (p : P) => ∑' α, h (f t u p α, p)) :=
        hG.comp (measurable_prodMk_left (x := t))
      rw [lintegral_prod _ a1.aemeasurable, ← lintegral_lintegral_swap a2.aemeasurable]
      refine lintegral_congr fun u => ?_
      have a3 : Measurable fun y : P × Q => h (Ψ (t, u, y)) := a1.comp measurable_prodMk_left
      rw [lintegral_prod _ a3.aemeasurable]
      refine lintegral_congr fun p => ?_
      rw [lintegral_count]
    simp only [e1]
    have hG2 : Measurable fun x : T × P => ∫⁻ u, ∑' α, h (f x.1 u x.2 α, x.2) ∂υ :=
      Measurable.lintegral_prod_right' (f := fun x : (T × P) × U => ∑' α, h (f x.1.1 x.2 x.1.2 α, x.1.2))
        (hG.comp (f := fun x : (T × P) × U => (x.1.1, x.2, x.1.2)) (by fun_prop))
    rw [lintegral_lintegral_swap hG2.aemeasurable]
    have e2 : ∀ p, ∫⁻ t, ∫⁻ u, ∑' α, h (f t u p α, p) ∂υ ∂τ = c * ∫⁻ y, h (y, p) ∂μ :=
      fun p => hc p (fun y => h (y, p)) (hh.comp measurable_prodMk_right)
    simp only [e2]
    rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    rfl
  have hI1 : Integrable H (m.map Ψ) := by
    rw [hmap]
    exact hI.smul_measure ENNReal.coe_ne_top
  have hI2 : Integrable (fun x => H (Ψ x)) m := (integrable_map_measure hH.aestronglyMeasurable hΨ.aemeasurable).1 hI1
  have hval : ∫ x, H (Ψ x) ∂m = (c : ℂ) * ∫ q, H q ∂(μ.prod ν) := by
    rw [← integral_map hΨ.aemeasurable hH.aestronglyMeasurable, hmap, integral_smul_nnreal_measure, NNReal.smul_def,
      Complex.real_smul]
  constructor
  · filter_upwards [hI2.prod_right_ae] with t ht
    filter_upwards [ht.prod_right_ae] with u hu
    filter_upwards [hu.prod_right_ae] with p hp
    exact (integrable_count_iff.1 hp).of_norm
  · rw [← hval, integral_prod _ hI2]
    refine integral_congr_ae ?_
    filter_upwards [hI2.prod_right_ae] with t ht
    rw [integral_prod _ ht]
    refine integral_congr_ae ?_
    filter_upwards [ht.prod_right_ae] with u hu
    rw [integral_prod _ hu]
    refine integral_congr_ae ?_
    filter_upwards [hu.prod_right_ae] with p hp
    rw [integral_countable hp]
    simp [Ψ]

theorem UpperTheory.integral_tsum_ideleCovering_eq_const_mul :
    ∀ (U : UMeas) (c : ℝ≥0), (∀ h : IdeleGroup ℚ → ℝ≥0∞, Measurable h →
          ∫⁻ t : ℝ, ∫⁻ u, ∑' α : ℚˣ, h (Un.cov t u α) ∂U.υ = c * ∫⁻ y, h y ∂(ideleMeasure ℚ)) →
        ∀ (κ : Measure (G1 ℚ)) [IsProbabilityMeasure κ] (H : IdeleGroup ℚ × IdeleGroup ℚ × G1 ℚ → ℂ), Measurable H →
        Integrable H ((ideleMeasure ℚ).prod ((ideleMeasure ℚ).prod κ)) →
        (∀ᵐ t : ℝ, ∀ᵐ u ∂U.υ, ∀ᵐ p ∂((ideleMeasure ℚ).prod κ), Summable fun α : ℚˣ => H (Un.cov t u α * (p.1 * p.1)⁻¹, p)) ∧
        ∫ t : ℝ, ∫ u, ∫ p, ∑' α : ℚˣ, H (Un.cov t u α * (p.1 * p.1)⁻¹, p) ∂((ideleMeasure ℚ).prod κ) ∂U.υ =
          (c : ℂ) * ∫ q, H q ∂((ideleMeasure ℚ).prod ((ideleMeasure ℚ).prod κ)) := by
  intro U c hc κ _ H hH hI
  haveI := U.prob
  letI : MeasurableSpace ℚˣ := ⊤
  haveI : MeasurableSingletonClass ℚˣ := ⟨fun _ => trivial⟩
  haveI : Countable ℚˣ := Units.val_injective.countable
  have hiy : Measurable (fun t : ℝ => (iy (Real.exp t) : IdeleGroup ℚ)) := by
    have h : Continuous (fun t : ℝ => (iy (Real.exp t) : IdeleGroup ℚ)) := UpperTheory.realIdele_mul_abs_continuous_and_unit_abs_eq_one.2.2.1
    exact h.measurable
  have hd : Measurable (fun α : ℚˣ => (IdeleGroup.diagonal ℚ α : IdeleGroup ℚ)) := measurable_from_top
  refine gen volume U.υ ((ideleMeasure ℚ).prod κ) (ideleMeasure ℚ)
    (fun t u p α => Un.cov t u α * (p.1 * p.1)⁻¹) ?_ c ?_ H hH hI
  · have h1 : Measurable fun x : ℝ × IdeleGroup ℚ × (IdeleGroup ℚ × G1 ℚ) × ℚˣ => x.2.2.1.1 := by fun_prop
    exact (((hd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))).mul
      ((hiy.comp measurable_fst).mul (hiy.comp measurable_fst))).mul (measurable_fst.comp measurable_snd)).mul (h1.mul h1).inv
  · intro p h hh
    rw [hc (fun y => h (y * (p.1 * p.1)⁻¹)) (hh.comp (measurable_mul_const _)), lintegral_mul_right_eq_self]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

theorem UpperTheory.whittakerCoeff_lieDeriv_unipotent_eq_mul :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (f : Sm E 2), Pp.Lf f.1 →
        (∀ X, Continuous (lie E 2 X f).1 ∧ ∃ B : ℝ, ∀ g, ‖(lie E 2 X f).1 g‖ ≤ B) → ∀ (y : (A ℚ)ˣ) (k : GL (Fin 2) (A E)),
        Wo D (lie E 2 (toL (XB D k)) f).1 (em E (aE y) * k) = (2 * Real.pi * Complex.I * (re (y : A ℚ) : ℂ)) * Wo D f.1 (em E (aE y) * k) := by
  intro E _ _ _ D f hf hl y k
  obtain ⟨c0, cadd, cd, -⟩ := UpperTheory.archimedeanConjugateCurve_oneParameterSubgroup E D k
  have h1 := UpperTheory.hasDerivAt_whittakerPeriod_oneParameter E D f (cv D k) (toL (XB D k)) (em E (aE y) * k) c0 cadd cd hf.1 (hl _).1 (hl _).2
  have e : (fun t : ℝ => Wo D f.1 (em E (aE y) * k * infGL E 2 (cv D k t))) =
      fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((t : ℂ) * (re (y : A ℚ) : ℂ))) * Wo D f.1 (em E (aE y) * k) := by
    funext t
    rw [UpperTheory.diagonal_mul_archimedeanCurve_eq_unipotent_mul, UpperTheory.whittaker_unipotent_mul_eq_additiveChar_mul E D f.1 hf]
    have e1 : (![0, TR.sInf ℚ fun _ => t * re (y : A ℚ)] : Fin 2 → A ℚ) 1 = TR.sInf ℚ fun _ => t * re (y : A ℚ) := rfl
    rw [e1, UpperTheory.standardAddChar_neg_archimedean_rat]
    push_cast
    rfl
  rw [e] at h1
  have a : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := (hasDerivAt_id (0 : ℝ)).ofReal_comp
  have h2 := (((a.mul_const (re (y : A ℚ) : ℂ)).const_mul (2 * Real.pi * Complex.I)).cexp).mul_const
    (Wo D f.1 (em E (aE y) * k))
  have h3 := h1.unique h2
  rw [h3]
  simp
end
