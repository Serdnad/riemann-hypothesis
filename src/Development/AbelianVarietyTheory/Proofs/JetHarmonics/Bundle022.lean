module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle001
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle014
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle015
public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime
public import Formalism.RealPlaceAnalysis.Bundle003
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle013
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle008
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle018
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.RealPlaceAnalysis.Bundle001

@[expose] public section

section

open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer

section
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] {σ τ : Type}
  [Fintype σ] {s : σ → MvPowerSeries τ K}

theorem csub_add_of_bdd (hs : ∀ i, Small (s i)) {S T : MvPowerSeries σ K} (hS : Bdd S)
    (hT : Bdd T) : csub s (S + T) = csub s S + csub s T := by
  ext μ
  have h1 := (GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ τ s S hs hS).1 μ
  have h2 := (GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ τ s T hs hT).1 μ
  have h3 := (GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ τ s _ hs ((GlobalTheory.T.mvPowerSeries_integral_bounded_closure K σ).2.1 S T hS hT).1).1 μ
  rw [map_add (f := _)]
  refine h3.unique ?_
  simpa only [map_add (f := _), add_mul] using h1.add h2

theorem csub_sub_of_bdd (hs : ∀ i, Small (s i)) {S T : MvPowerSeries σ K} (hS : Bdd S)
    (hT : Bdd T) : csub s (S - T) = csub s S - csub s T := by
  ext μ
  have h1 := (GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ τ s S hs hS).1 μ
  have h2 := (GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ τ s T hs hT).1 μ
  have h3 := (GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ τ s _ hs ((GlobalTheory.T.mvPowerSeries_integral_bounded_closure K σ).2.1 S T hS hT).2.1).1 μ
  rw [map_sub]
  refine h3.unique ?_
  simpa only [map_sub, sub_mul] using h1.sub h2

theorem csub_mul_of_bdd (hs : ∀ i, Small (s i)) {S T : MvPowerSeries σ K} (hS : Bdd S)
    (hT : Bdd T) : csub s (S * T) = csub s S * csub s T := by
  classical
  ext μ
  have h3 := (GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ τ s _ hs ((GlobalTheory.T.mvPowerSeries_integral_bounded_closure K σ).2.1 S T hS hT).2.2).1 μ
  refine h3.unique ?_
  haveI : NonarchimedeanRing K := ⟨NonarchimedeanAddGroup.is_nonarchimedean⟩
  have h4 : HasSum (fun p : (σ →₀ ℕ) × (σ →₀ ℕ) =>
      MvPowerSeries.coeff p.1 S * MvPowerSeries.coeff p.2 T *
        MvPowerSeries.coeff μ (∏ i, s i ^ (p.1 + p.2) i))
      (MvPowerSeries.coeff μ (csub s S * csub s T)) := by
    rw [MvPowerSeries.coeff_mul]
    have h5 := hasSum_sum (s := Finset.HasAntidiagonal.antidiagonal μ) (fun q _ =>
      ((GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ τ s S hs hS).1 q.1).mul_of_nonarchimedean
        ((GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ τ s T hs hT).1 q.2))
    convert h5 using 2 with p
    simp only [Finsupp.add_apply, pow_add, Finset.prod_mul_distrib, MvPowerSeries.coeff_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  have h6 := Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff.2 h4
  refine h6.sigma fun ν => ?_
  rw [MvPowerSeries.coeff_mul, Finset.sum_mul, ← Finset.sum_coe_sort]
  convert hasSum_fintype _ using 2 with q
  have := Finset.HasAntidiagonal.mem_antidiagonal.1 q.2
  simp only [Function.comp, Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply, this]

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem csub_monomial (s : σ → MvPowerSeries τ K) (ν : σ →₀ ℕ) (a : K) :
    csub s (MvPowerSeries.monomial ν a) = MvPowerSeries.C a * ∏ i, s i ^ ν i := by
  classical
  ext μ
  rw [MvPowerSeries.coeff_C_mul]
  change ∑' ν' : σ →₀ ℕ, MvPowerSeries.coeff ν' (MvPowerSeries.monomial ν a) *
    MvPowerSeries.coeff μ (∏ i, s i ^ ν' i) = _
  rw [tsum_eq_single ν]
  · rw [MvPowerSeries.coeff_monomial_same]
  · intro b hb
    rw [MvPowerSeries.coeff_monomial_ne hb, zero_mul]

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem csub_C (s : σ → MvPowerSeries τ K) (a : K) :
    csub s (MvPowerSeries.C a) = MvPowerSeries.C a := by
  rw [← MvPowerSeries.monomial_zero_eq_C_apply, csub_monomial]
  simp

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem csub_X (s : σ → MvPowerSeries τ K) (i : σ) :
    csub s (MvPowerSeries.X i) = s i := by
  classical
  rw [MvPowerSeries.X_def, csub_monomial, map_one, one_mul, Finset.prod_eq_single i]
  · simp
  · intro b _ hb
    rw [Finsupp.single_eq_of_ne hb, pow_zero]
  · simp

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem csub_one (s : σ → MvPowerSeries τ K) : csub s 1 = 1 := by
  simpa using csub_C s (1 : K)

theorem csub_pow_of_bdd (hs : ∀ i, Small (s i)) {S : MvPowerSeries σ K} (hS : Bdd S) (n : ℕ) :
    csub s (S ^ n) = csub s S ^ n := by
  induction n with
  | zero => simpa using csub_one s
  | succ n ih =>
    rw [pow_succ, pow_succ, csub_mul_of_bdd hs (((GlobalTheory.T.mvPowerSeries_integral_bounded_closure K σ).2.2.1 S n).2.1 hS) hS, ih]

theorem csub_prod_of_bdd (hs : ∀ i, Small (s i)) {ι : Type} (t : Finset ι)
    (f : ι → MvPowerSeries σ K) (hf : ∀ i ∈ t, Bdd (f i)) :
    csub s (∏ i ∈ t, f i) = ∏ i ∈ t, csub s (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using csub_one s
  | insert a t ha ih =>
    have ht : ∀ i ∈ t, Bdd (f i) := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      csub_mul_of_bdd hs (hf a (Finset.mem_insert_self a t))
        (((GlobalTheory.T.mvPowerSeries_integral_bounded_closure K σ).2.2.2.2.2.1 ι t f).2 ht).1, ih ht]

theorem csub_eval₂_of_bdd (hs : ∀ i, Small (s i)) {k ι : Type} [CommRing k] (φ : k →+* K)
    (a : ι → MvPowerSeries σ K) (A : MvPolynomial ι k) (ha : ∀ j, Bdd (a j)) :
    csub s (MvPolynomial.eval₂ ((MvPowerSeries.C : K →+* MvPowerSeries σ K).comp φ) a A) =
      MvPolynomial.eval₂ ((MvPowerSeries.C : K →+* MvPowerSeries τ K).comp φ)
        (fun j => csub s (a j)) A := by
  have hb := fun B => (GlobalTheory.T.mvPowerSeries_integral_bounded_closure K σ).2.2.2.2.2.2.2.2.1 k ι φ a B ha
  induction A using MvPolynomial.induction_on with
  | C c => simp [csub_C]
  | add p q hp hq =>
    rw [MvPolynomial.eval₂_add, MvPolynomial.eval₂_add, csub_add_of_bdd hs (hb p) (hb q), hp, hq]
  | mul_X p j hp =>
    rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, MvPolynomial.eval₂_X,
      csub_mul_of_bdd hs (hb p) (ha j), hp]

end

theorem csub_ring_map : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (σ τ : Type) [Fintype σ] (s : σ → MvPowerSeries τ K), (∀ i, Small (s i)) → (∀ S T : MvPowerSeries σ K, Bdd S → Bdd T → csub s (S + T) = csub s S + csub s T ∧ csub s (S - T) = csub s S - csub s T ∧ csub s (S * T) = csub s S * csub s T) ∧ (∀ a : K, csub s (MvPowerSeries.C a) = MvPowerSeries.C a) ∧ (∀ i, csub s (MvPowerSeries.X i) = s i) ∧ (∀ (S : MvPowerSeries σ K) (n : ℕ), Bdd S → csub s (S ^ n) = csub s S ^ n) ∧ (∀ (ι : Type) (t : Finset ι) (f : ι → MvPowerSeries σ K), (∀ i ∈ t, Bdd (f i)) → csub s (∏ i ∈ t, f i) = ∏ i ∈ t, csub s (f i)) ∧ (∀ (k ι : Type) [CommRing k] (φ : k →+* K) (a : ι → MvPowerSeries σ K) (A : MvPolynomial ι k), (∀ j, Bdd (a j)) → csub s (MvPolynomial.eval₂ ((MvPowerSeries.C : K →+* MvPowerSeries σ K).comp φ) a A) = MvPolynomial.eval₂ ((MvPowerSeries.C : K →+* MvPowerSeries τ K).comp φ) (fun j => csub s (a j)) A) := by
  intro K _ _ _ σ τ _ s hs
  exact ⟨fun S T hS hT => ⟨csub_add_of_bdd hs hS hT, csub_sub_of_bdd hs hS hT,
      csub_mul_of_bdd hs hS hT⟩, csub_C s, csub_X s, fun S n hS => csub_pow_of_bdd hs hS n,
    fun ι t f hf => csub_prod_of_bdd hs t f hf,
    fun k ι _ φ a A ha => csub_eval₂_of_bdd hs φ a A ha⟩

end GlobalTheory.ConvSer
end

section

noncomputable section
open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators ComplexOrder

namespace GlobalTheory.MomOne.FrameChange

variable {g : ℕ}

theorem beta_sum_left {κ : Type} [Fintype κ] (d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (c : κ → ℂ)
    (v : κ → Fin g → ℂ) (w : Fin g → ℂ) :
    beta d Hm (∑ k, c k • v k) w = ∑ k, c k * beta d Hm (v k) w := by
  simp only [beta, hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun _ => Finset.univ) (h := by simp)]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin g))) (t := (Finset.univ : Finset κ))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem beta_conj (d : ℕ) {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian) (z w : Fin g → ℂ) :
    conj (beta d Hm z w) = beta d Hm w z := by

  simp only [beta, hf, map_mul, map_sum, Complex.conj_ofReal, Complex.conj_conj]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have : conj (Hm j i) = Hm i j := h.apply i j
  rw [this]; ring

theorem eq_sum_frame (d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (x : Fin g → Fin g → ℂ) (a : Fin g → ℕ)
    (hx : ∀ i j, beta d Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) (ha : ∀ i, (a i : ℂ) ≠ 0)
    (v : Fin g → ℂ) : v = ∑ i, (beta d Hm v (x i) / (a i : ℂ)) • x i := by
  have key : ∀ (z : Fin g → ℂ) k, beta d Hm (∑ i, z i • x i) (x k) = z k * a k := by
    intro z k
    rw [beta_sum_left]
    simp [hx]
  have hli : LinearIndependent ℂ x := by
    refine Fintype.linearIndependent_iff.2 fun z hz k => ?_
    have h := key z k
    rw [hz] at h
    have h0 : beta d Hm 0 (x k) = 0 := by simp [beta, hf]
    rw [h0] at h
    exact (mul_eq_zero.1 h.symm).resolve_right (ha k)
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by simp)
  have hv : v ∈ Submodule.span ℂ (Set.range x) := by rw [hsp]; trivial
  obtain ⟨z, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hv
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [key, mul_div_cancel_right₀ _ (ha i)]

def zcHom (q : ℕ) [Fact q.Prime] : ℤ_[q] →+* ℂ_[q] := (algebraMap ℚ_[q] ℂ_[q]).comp PadicInt.Coe.ringHom

theorem zcHom_injective (q : ℕ) [Fact q.Prime] : Function.Injective (zcHom q) :=
  (algebraMap ℚ_[q] ℂ_[q]).injective.comp Subtype.val_injective

end GlobalTheory.MomOne.FrameChange

namespace GlobalTheory.MomOne
open FrameChange

theorem frameChange : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (g : ℕ) (S : Setup g) (x : Fin g → Fin g → ℂ) (a : Fin g → ℕ) (r : ℕ) (b : Fin r → Fin g → ℂ), S.Ok → Split S.d q → (∀ i, x i ∈ S.La) → (∀ i j, beta S.d S.Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) → (∀ i, 0 < a i ∧ Nat.Coprime (a i) q) → S.NNBasis q b → ∃ T : (Fin r → ℤ_[q]) ≃ₜ (Fin g → ℤ_[q]), ∀ A i, GlobalTheory.MomOne.zc (T A i) = ∑ j, GlobalTheory.MomOne.zc (A j) * ι (beta S.d S.Hm (x i) (b j)) := by
  intro q _ ι g S x a r b hS hsp hxL hx ha hb
  obtain ⟨hd, hd7, hpos, -, -, -, hβ, -⟩ := hS
  obtain ⟨hbL, hgen, hind⟩ := hb
  have hq : q.Prime := Fact.out
  have hH : S.Hm.IsHermitian := hpos.isHermitian
  obtain ⟨⟨h1, -, hR⟩, hZ, -⟩ := okArith S.d q ι hd hd7 hsp
  let O : Subring ℂ :=
    { carrier := {z | InOK S.d z}
      one_mem' := h1
      zero_mem' := ⟨0, 0, by simp⟩
      mul_mem' := fun {u v} hu hv => (hR u v hu hv).2.1
      add_mem' := fun {u v} hu hv => (hR u v hu hv).1
      neg_mem' := fun {u} hu => (hR u u hu hu).2.2.1 }
  have hconj : ∀ u, InOK S.d u → InOK S.d (conj u) := fun u hu => (hR u u hu hu).2.2.2
  choose s hs c hc hsc using fun i => hgen (x i) (hxL i)
  have hs0 : ∀ i, (s i : ℂ) ≠ 0 := fun i h => by
    have h' : s i = 0 := by exact_mod_cast h
    have := hs i
    rw [h', Nat.coprime_zero_left] at this
    exact hq.one_lt.ne' this
  have ha0 : ∀ i, (a i : ℂ) ≠ 0 := fun i => by exact_mod_cast (ha i).1.ne'

  have hMN : ∀ i k, ∑ j, beta S.d S.Hm (x i) (b j) * (conj (c k j) / (s k * a k)) = if i = k then 1 else 0 := by
    intro i k
    have e := beta_sum_left S.d S.Hm (c k) b (x i)
    have e2 := beta_sum_left S.d S.Hm (fun _ : Unit => (s k : ℂ)) (fun _ => x k) (x i)
    simp only [Finset.univ_unique, Finset.sum_singleton] at e2
    rw [← hsc k, e2] at e
    have e3 := congrArg conj e

    simp only [map_sum, map_mul, beta_conj S.d hH, map_natCast] at e3
    simp_rw [← mul_div_assoc, mul_comm (beta _ _ _ _)]
    rw [← Finset.sum_div, ← e3, hx]
    split_ifs with h
    · subst h; exact div_self (mul_ne_zero (hs0 i) (ha0 i))
    · simp
  have hNM : ∀ j l, ∑ i, (conj (c i j) / (s i * a i)) * beta S.d S.Hm (x i) (b l) = if j = l then 1 else 0 := by
    intro j l
    set P : ℂ := ∏ i, ((s i : ℂ) * a i) with hP
    have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => mul_ne_zero (hs0 i) (ha0 i)
    let e : Fin r → ℂ := fun j => ∑ i, c i j / (s i * a i) * beta S.d S.Hm (b l) (x i)
    have hmem : ∀ j, P * (e j - if j = l then 1 else 0) ∈ O := by
      intro j
      have hPO : P ∈ O := O.prod_mem fun i _ => O.mul_mem (natCast_mem O _) (natCast_mem O _)
      rw [mul_sub, Finset.mul_sum]
      refine O.sub_mem (O.sum_mem fun i _ => ?_) (O.mul_mem hPO (by split_ifs; exacts [O.one_mem, O.zero_mem]))
      have : P * (c i j / (s i * a i) * beta S.d S.Hm (b l) (x i)) =
          (∏ k ∈ Finset.univ.erase i, ((s k : ℂ) * a k)) * c i j * beta S.d S.Hm (b l) (x i) := by
        rw [hP, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
        have := hs0 i
        have := ha0 i
        field_simp
      rw [this]
      exact O.mul_mem (O.mul_mem (O.prod_mem fun i _ => O.mul_mem (natCast_mem O _) (natCast_mem O _)) (hc i j))
        (hβ _ (hbL l) _ (hxL i))
    have hsum : ∑ j, e j • b j = b l := by
      conv_rhs => rw [eq_sum_frame S.d S.Hm x a hx ha0 (b l)]
      simp only [e, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hxi : x i = (s i : ℂ)⁻¹ • ∑ j, c i j • b j := by
        rw [← hsc i, smul_smul, inv_mul_cancel₀ (hs0 i), one_smul]
      generalize beta S.d S.Hm (b l) (x i) = t
      rw [hxi, smul_smul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul]
      congr 1
      have := hs0 i
      have := ha0 i
      field_simp
    have h0 := hind _ hmem (by
      simp only [mul_smul, sub_smul, ← Finset.smul_sum, Finset.sum_sub_distrib, hsum]
      simp [ite_smul]) j
    have h2 : e j = if j = l then 1 else 0 := sub_eq_zero.1 ((mul_eq_zero.1 h0).resolve_left hP0)
    have h3 := congrArg conj h2

    simp only [e, map_sum, map_mul, map_div₀, beta_conj S.d hH, map_natCast] at h3
    rw [h3]
    split_ifs <;> simp

  choose m hm using fun i j => (hZ _ (hβ _ (hxL i) _ (hbL j))).1
  choose n hn using fun i j => (hZ _ (hconj _ (hc i j))).1
  have hu : ∀ i, ∃ u : ℤ_[q], ι ((s i * a i : ℂ)⁻¹) = zcHom q u := by
    intro i
    have hun : IsUnit ((s i * a i : ℕ) : ℤ_[q]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
      exact (Nat.Coprime.mul_left (hs i) (ha i).2).symm
    obtain ⟨u, hu⟩ := hun.exists_left_inv
    refine ⟨u, ?_⟩
    have := congrArg (zcHom q) hu
    rw [map_mul, map_natCast, map_one] at this
    rw [map_inv₀, eq_inv_of_mul_eq_one_left this]
    simp
  choose u hu using hu
  let M : Matrix (Fin g) (Fin r) ℤ_[q] := Matrix.of m
  let N : Matrix (Fin r) (Fin g) ℤ_[q] := Matrix.of fun j i => n i j * u i
  have hM : ∀ i j, zcHom q (M i j) = ι (beta S.d S.Hm (x i) (b j)) := fun i j => (hm i j).symm
  have hN : ∀ j i, zcHom q (N j i) = ι (conj (c i j) / (s i * a i)) := fun j i => by
    rw [div_eq_mul_inv, map_mul, hu, hn]
    exact map_mul (zcHom q) _ _
  have e1 : M * N = 1 := by
    apply Matrix.ext
    intro i k
    apply zcHom_injective q

    rw [Matrix.mul_apply, map_sum]
    simp_rw [map_mul, hM, hN, ← map_mul]

    rw [← map_sum, hMN, Matrix.one_apply]
    split_ifs <;> simp
  have e2 : N * M = 1 := by
    apply Matrix.ext
    intro i k
    apply zcHom_injective q

    rw [Matrix.mul_apply, map_sum]
    simp_rw [map_mul, hM, hN, ← map_mul]

    rw [← map_sum, hNM, Matrix.one_apply]
    split_ifs <;> simp
  refine ⟨{ toFun := M.mulVec
            invFun := N.mulVec
            left_inv := fun A => by rw [Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]
            right_inv := fun A => by rw [Matrix.mulVec_mulVec, e1, Matrix.one_mulVec]
            continuous_toFun := continuous_const.matrix_mulVec continuous_id
            continuous_invFun := continuous_const.matrix_mulVec continuous_id }, fun A i => ?_⟩
  show zcHom q (∑ j, M i j * A j) = ∑ j, zcHom q (A j) * _

  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_mul, hM, mul_comm]

end GlobalTheory.MomOne
end
end

section

open Formalism.REAL Finset

namespace GlobalTheory

theorem qminor_comm_of_comm_columns (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ)
    (E : Fin n → Fin n → A) (x : A) (a b : Fin t → Fin n) (u : ℂ)
    (h : ∀ (c : Fin n) (i : Fin t), E c (b i) * x = x * E c (b i)) :
    qminor E a b u * x = x * qminor E a b u := by
  have hT : ∀ (v : ℂ) (c : Fin n) (i : Fin t), Commute (Tm E v c (b i)) x := by
    intro v c i
    have h1 : Commute (E c (b i)) x := h c i
    unfold Tm
    refine Commute.add_left ?_ h1
    split_ifs
    · exact Algebra.commutes v x
    · exact Commute.zero_left x
  change Commute (qminor E a b u) x
  unfold qminor
  refine Commute.sum_left _ _ _ fun σ _ => ?_
  have hp : ∀ f : Fin t → A, (∀ i, Commute (f i) x) → Commute (List.ofFn f).prod x := by
    intro f hf
    refine Commute.list_prod_left _ _ fun y hy => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
    exact hf i
  exact (Int.cast_commute _ x).mul_left (hp _ fun i => hT _ _ i)

end GlobalTheory
end

section

open Formalism.REAL Finset

namespace GlobalTheory

theorem exists_sum_eigen_split_of_resolvent : ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (n : ℕ) (Ω : Module.End ℂ N) (X : ℂ → Module.End ℂ N) (d : ℕ) (c : ℕ → Module.End ℂ N) (ν : Fin n → ℂ), Function.Injective ν → (∀ u, X u = ∑ i ∈ Finset.range d, u ^ i • c i) → (∀ (u : ℂ) (w : N), u • X u w + Ω (X u w) = (∏ s, (u + ν s)) • w) → ∀ w : N, ∃ v : Fin n → N, w = ∑ s, v s ∧ ∀ s (u : ℂ), X u (v s) = (∏ t ∈ Finset.univ.erase s, (u + ν t)) • v s := by
  intro N _ _ n Ω X d c ν hν hX hres w
  have key := GlobalTheory.T.aeval_neg_eq_zero_of_resolvent_identity N Ω X d c (∏ s, (Polynomial.X + Polynomial.C (ν s))) hX (by
    intro u w
    rw [hres u w, Polynomial.eval_prod]
    simp)
  obtain ⟨v, hv, hw⟩ := GlobalTheory.T.exists_eigen_decomp_of_aeval_prod_eq_zero N n Ω ν hν key.1 w
  refine ⟨v, hw, fun s u => ?_⟩
  have h := key.2 (ν s) (v s) (hv s)
    (∏ t ∈ Finset.univ.erase s, (Polynomial.X + Polynomial.C (ν t)))
    (Finset.mul_prod_erase Finset.univ (fun t => Polynomial.X + Polynomial.C (ν t))
      (Finset.mem_univ s)).symm u
  rw [h, Polynomial.eval_prod]
  simp

end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.exists_eq_const_mul_of_forall_exists_norm_eq' : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (ι : Type) [Countable ι] (O : Set V), IsOpen O → IsPreconnected O → O.Nonempty → ∀ (P : V → ℂ) (Q : ι → V → ℂ), DifferentiableOn ℂ P O → (∀ i, DifferentiableOn ℂ (Q i) O) → (∀ x ∈ O, ∃ i, ‖P x‖ = ‖Q i x‖) → ∃ (i : ι) (c : ℂ), ∀ x ∈ O, P x = c * Q i x := by
  first | exact @GlobalTheory.exists_eq_const_mul_of_forall_exists_norm_eq | exact GlobalTheory.exists_eq_const_mul_of_forall_exists_norm_eq | (intros; apply GlobalTheory.exists_eq_const_mul_of_forall_exists_norm_eq <;> assumption)
end
