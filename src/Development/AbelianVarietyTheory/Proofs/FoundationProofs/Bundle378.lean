module

public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.SlopeE
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle365
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle374
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TeichmullerDecompositionDirichletTwistedPower
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle372
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle294
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.CoeffSubstInvMemOfTwoLeOrder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle375
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle018
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Nonarchimedean.Completion
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp

theorem _root_.GlobalTheory.T.gaussSumModPrimePower_mul_inv_eq_prime_pow : ∀ (l : ℕ) [Fact l.Prime] (m : ℕ) (z : Qbar l) (ψ : DirichletCharacter (Qbar l) (l ^ m)), IsPrimitiveRoot z (l ^ m) → ψ.IsPrimitive → gSum m z ψ * gSum m z⁻¹ ψ⁻¹ = (l : Qbar l) ^ m := by
  first | exact @GlobalTheory.KZ.Cmp.gSum_mul_gSum_inv_prim | exact GlobalTheory.KZ.Cmp.gSum_mul_gSum_inv_prim | (intros; apply GlobalTheory.KZ.Cmp.gSum_mul_gSum_inv_prim; all_goals assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp

theorem _root_.GlobalTheory.T.norm_gaussSumModPrimePower_le_half_power : ∀ (l : ℕ) [Fact l.Prime] (m : ℕ) (z : Qbar l) (ψ : DirichletCharacter (Qbar l) (l ^ m)), z ^ (l ^ m) = 1 → ‖gSum m z ψ‖ ≤ ‖(l : Qbar l) ^ (m / 2)‖ := by
  first | (exact @GlobalTheory.KZ.Cmp.norm_gSum_le) | (exact GlobalTheory.KZ.Cmp.norm_gSum_le) | (intros; apply GlobalTheory.KZ.Cmp.norm_gSum_le  <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp

theorem _root_.GlobalTheory.T.teichmuller_decomposition_dirichlet_twisted_power : ∀ (l : ℕ) [Fact l.Prime] (φ : DirichletCharacter (Qbar l) l) (e R j : ℕ), l ≠ 2 → ∃ (ε : Qbar l) (t : ℕ), (ε = 0 ∨ ε ^ (l - 1) = 1) ∧ Cg R (φ (j : ZMod l) * (j : Qbar l) ^ e) (ε * ((1 + (l : Qbar l)) ^ e) ^ t) ∧ ∀ m, 1 ≤ m → m ≤ R → ∀ ψ : DirichletCharacter (Qbar l) (l ^ m), InComp φ e ψ → ψ⁻¹ (j : ZMod (l ^ m)) = ε * (ψ⁻¹ (1 + (l : ZMod (l ^ m)))) ^ t := by
  first | exact @GlobalTheory.TeichDec.teich | exact GlobalTheory.TeichDec.teich | (intros; apply GlobalTheory.TeichDec.teich; all_goals assumption)
end

section

open NumberField
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TestLat

theorem slopeK_holds : SlopeK := by
  intro K _ _ _ _ v₀ hv ι _ n lam R hR hs G hG C _ M hM N e X
  exact ⟨GlobalTheory.T.maxSlope_sum_weyl_and_dualWeyl_lattices_le K v₀ hv ι n lam R hR hs G hG C M hM N e X,
    GlobalTheory.T.maxSlope_dual_sum_weyl_lattices_le K v₀ hv ι n lam R hR hs G hG C M hM N e X⟩

theorem slopeE_holds : SlopeE := by
  intro E K _ _ _ _ _ _ v₀ hv cE hcE ι _ emb hemb n lam R hR hs J hJ C _ L hL N e X
  have h := GlobalTheory.T.defGram_selfDual_after_field_embedding E K cE hcE ι emb hemb n J hJ
  have h1 := slopeK_holds K v₀ hv ι n lam R hR hs (gramK emb J) (fun τ => (h τ).1) C
    (fun c τ => tauLat emb τ (L c)) (fun c τ => ((h τ).2.2 (L c) (hL c)).1) N e X
  have h2 := slopeK_holds K v₀ hv ι n lam R hR hs (gramKd emb J) (fun τ => (h τ).2.1) C
    (fun c τ => dualFr (tauLat emb τ (L c))) (fun c τ => ((h τ).2.2 (L c) (hL c)).2) N e X
  exact ⟨h1.2, fun hm => (h1.1 hm).1, h2.2, fun hm => (h2.1 hm).1⟩

theorem slope_holds : GlobalTheory.TestLat.SlopeK ∧ GlobalTheory.TestLat.SlopeE := ⟨slopeK_holds, slopeE_holds⟩

end GlobalTheory.TestLat
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ThetaSplit

theorem exists_sqrt_padic {p : ℕ} [hp : Fact p.Prime] (h2 : p ≠ 2) {a : ℤ} (h : jacobiSym a p = 1) :
    ∃ z : ℤ_[p], z ^ 2 = (a : ℤ_[p]) ∧ IsUnit (2 * z) := by
  rw [← jacobiSym.legendreSym.to_jacobiSym] at h
  have ha : (a : ZMod p) ≠ 0 := by
    intro h0
    rw [(legendreSym.eq_zero_iff p a).2 h0] at h
    exact zero_ne_one h
  obtain ⟨r, hr⟩ := (legendreSym.eq_one_iff p ha).1 h
  obtain ⟨r, rfl⟩ := ZMod.intCast_surjective r
  have hr0 : (r : ZMod p) ≠ 0 := fun h0 => ha (by rw [hr, h0, mul_zero])
  have h20 : ((2 : ℤ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro hd
    have : p ∣ 2 := by exact_mod_cast hd
    exact h2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 this)
  have hn : ‖((2 * r : ℤ) : ℤ_[p])‖ = 1 := by
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun hlt => ?_)
    rw [PadicInt.norm_int_lt_one_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd] at hlt
    push_cast at hlt h20
    exact mul_ne_zero h20 hr0 hlt
  have hlt : ‖((r ^ 2 - a : ℤ) : ℤ_[p])‖ < 1 := by
    rw [PadicInt.norm_int_lt_one_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hr]; ring
  have e1 : ∀ z : ℤ_[p], Polynomial.aeval z (Polynomial.X ^ 2 - Polynomial.C a : Polynomial ℤ) = z ^ 2 - a := by
    intro z; simp
  have e2 : ∀ z : ℤ_[p], Polynomial.aeval z
      (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C a : Polynomial ℤ)) = 2 * z := by
    intro z; simp [map_ofNat]
  obtain ⟨z, hz, -, hz', -⟩ := hensels_lemma (p := p) (F := (Polynomial.X ^ 2 - Polynomial.C a : Polynomial ℤ))
    (a := (r : ℤ_[p])) (by
      rw [e1, e2]
      push_cast at hn hlt
      rw [hn]; simpa using hlt)
  rw [e1] at hz
  rw [e2, e2] at hz'
  push_cast at hn
  exact ⟨z, sub_eq_zero.1 hz, PadicInt.isUnit_iff.2 (hz'.trans hn)⟩

theorem exists_emb (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) :
    ∃ ψ : D.host.E →+* ℂ_[p], ∀ x, lamC lam (D.host.φ₀ x) = ψ x := by
  have hm : ∀ x, D.host.φ₀ x ∈ Qbar := fun x => by
    rw [mem_algebraicClosure_iff]
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom D.host.φ₀.toRatAlgHom
  refine ⟨lam.comp (D.host.φ₀.codRestrict Qbar hm), fun x => ?_⟩
  simp only [lamC, dif_pos (hm x)]
  rfl

theorem exists_sqrt_host (D : D7) : ∃ b : 𝓞 D.host.K, ((b : D.host.K) : D.host.E) ^ 2 = -(D.host.d : D.host.E) ∧
    D.host.conj ((b : D.host.K) : D.host.E) = -((b : D.host.K) : D.host.E) := by
  have hb : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := D.host.sqd_sq
  have hK : D.host.sqrtMinusD ∈ D.host.K := IntermediateField.mem_adjoin_simple_self ℚ _
  have hi : IsIntegral ℤ (⟨D.host.sqrtMinusD, hK⟩ : D.host.K) := by
    refine IsIntegral.of_pow two_pos ?_
    have : (⟨D.host.sqrtMinusD, hK⟩ : D.host.K) ^ 2 = algebraMap ℤ D.host.K (-(D.host.d : ℤ)) := by
      apply Subtype.ext
      simpa using hb
    rw [this]; exact isIntegral_algebraMap
  exact ⟨⟨_, hi⟩, hb, D.host.conj_sqd⟩

theorem idem_mem (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (h2 : p ≠ 2)
    (hs : GL3Theta.SplitK D p) : ((1, 0) : ℂ_[p] × ℂ_[p]) ∈ GL3Theta.OKp D lam := by
  obtain ⟨ψ, hψ⟩ := exists_emb D lam
  obtain ⟨b, hb, hc⟩ := exists_sqrt_host D
  let ι : ℤ_[p] →+* ℂ_[p] := (algebraMap ℚ_[p] ℂ_[p]).comp PadicInt.Coe.ringHom
  have hι : Continuous ι := (continuous_algebraMap ℚ_[p] ℂ_[p]).comp continuous_subtype_val
  set s := ψ ((b : D.host.K) : D.host.E) with hsdef
  have hs2 : s ^ 2 = -(D.host.d : ℂ_[p]) := by rw [hsdef, ← map_pow, hb]; simp
  obtain ⟨z, hz, hu⟩ : ∃ z : ℤ_[p], ι z = s ∧ IsUnit (2 * z) := by
    obtain ⟨z, hz, hu⟩ := exists_sqrt_padic h2 hs
    have : ι z ^ 2 = s ^ 2 := by rw [← map_pow, hz, hs2]; simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 this with h | h
    · exact ⟨z, h, hu⟩
    · exact ⟨-z, by rw [map_neg, h, neg_neg], by simpa using hu.neg⟩
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  let f : ℤ_[p] × ℤ_[p] → ℂ_[p] × ℂ_[p] := fun x => (ι x.1 + ι x.2 * s, ι x.1 - ι x.2 * s)
  have hf : Continuous f := by fun_prop
  have hd : DenseRange (Prod.map (Int.cast : ℤ → ℤ_[p]) (Int.cast : ℤ → ℤ_[p])) :=
    PadicInt.denseRange_intCast.prodMap PadicInt.denseRange_intCast
  have hw' : 2 * s * ι w = 1 := by
    have := congrArg ι hw
    rwa [map_mul, map_mul, map_ofNat, hz, map_one] at this
  have h1 : f (z * w, w) = (1, 0) := by
    simp only [f, map_mul, hz]
    ext
    · linear_combination hw'
    · simp only; ring
  rw [← h1]
  refine map_mem_closure hf (hd (z * w, w)) ?_
  rintro _ ⟨⟨m, n⟩, rfl⟩
  refine ⟨(m : 𝓞 D.host.K) + n * b, ?_⟩
  simp only [GL3Theta.tauK, GL3Theta.tauKc, hψ, f, Prod.map]
  simp [hc, hsdef, sub_eq_add_neg]

section Series
variable {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) {σ : Type*}

theorem const_l : PowerSeries.constantCoeff g.l = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [GL3Theta.G1.l, flog]

theorem const_ph : PowerSeries.constantCoeff g.ph = 0 := by
  simp only [GL3Theta.G1.ph, map_neg, neg_eq_zero]
  show GL3Theta.logMv _ 0 = 0
  simp [GL3Theta.logMv]

theorem ex_l (h : g.Ok) : PowerSeries.subst g.l g.ex = PowerSeries.X := by
  apply _root_.GlobalTheory.CMEndo.ex_l <;> assumption

theorem pt_lg (h : g.Ok) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    g.pt (g.lg a) = a := by
  have ha' := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [GL3Theta.G1.pt, GL3Theta.G1.lg, ← PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' (const_l g)) ha', ex_l g h, PowerSeries.subst_X ha']

theorem subst_zero {f : PowerSeries ℂ_[p]} (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.subst (0 : MvPowerSeries σ ℂ_[p]) f = 0 := by
  obtain ⟨k, rfl⟩ := PowerSeries.X_dvd_iff.2 hf
  have h0 : PowerSeries.HasSubst (0 : MvPowerSeries σ ℂ_[p]) := PowerSeries.HasSubst.of_constantCoeff_zero (map_zero _)
  rw [PowerSeries.subst_mul h0, PowerSeries.subst_X h0, zero_mul]

theorem mulBy_one (h : g.Ok) (i : σ) : g.mulBy 1 (GL3Theta.Xv i) = GL3Theta.Xv i := by
  rw [GL3Theta.G1.mulBy, map_one, one_mul, pt_lg g h (MvPowerSeries.constantCoeff_X i)]

theorem mulBy_zero (h : g.Ok) (a : MvPowerSeries σ ℂ_[p]) : g.mulBy 0 a = 0 := by
  rw [GL3Theta.G1.mulBy, map_zero, zero_mul, GL3Theta.G1.pt, subst_zero h.2.2.1]

theorem be_zero (h : g.Ok) (i : σ) : g.be (GL3Theta.Xv i) 0 = 0 := by
  have h1 : g.lg (0 : MvPowerSeries σ ℂ_[p]) = 0 := subst_zero (const_l g)
  have h2 : g.phAt (0 : MvPowerSeries σ ℂ_[p]) = 0 := subst_zero (const_ph g)
  rw [GL3Theta.G1.be, GL3Theta.G1.add, h1, add_zero, pt_lg g h (MvPowerSeries.constantCoeff_X i), h2]
  simp

end Series

theorem splitZero : ∀ D : D7, GL3Theta.splitZero D := by
  intro D p _ cc δ g hg h2 hs
  obtain ⟨-, hN, hC⟩ := GlobalTheory.T.cmThetaPoints_integral_norm_conjugate_laws D
  have hα := idem_mem D g.lam h2 hs
  have hok : g.Ok := hg.2.2.2.2
  have h1 := hC p cc δ g hg h2 _ hα
  have h3 := hN p cc δ g hg h2 _ hα
  simp only [mulBy_one g hok, mulBy_zero g hok, be_zero g hok, mul_zero, map_zero, zero_mul] at h1 h3
  exact ⟨h1, h3⟩

end GlobalTheory.ThetaSplit
end
