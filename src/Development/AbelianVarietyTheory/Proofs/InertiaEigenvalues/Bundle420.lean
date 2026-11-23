module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle410
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle334
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle376
public import GroundTheory.LocalFields.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle226
public import GroundTheory.LocalFields.KroneckerWeber
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle404
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle409
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualSelmerDeterminantOrderBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem polyVal_le_sum_mul_pow (Q : MvPolynomial (Fin 3) ℕ) (f r t : ℕ) (hf : 1 ≤ f) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    EmbeddingTypeJumps.polyVal Q f r t ≤ (∑ m ∈ Q.support, Q.coeff m) * (f * r * t) ^ Q.totalDegree := by
  unfold EmbeddingTypeJumps.polyVal
  rw [MvPolynomial.eval_eq', Finset.sum_mul]
  refine Finset.sum_le_sum fun m hm => ?_
  refine Nat.mul_le_mul_left _ ?_
  have hM : ∀ i : Fin 3, (![f, r, t] : Fin 3 → ℕ) i ≤ f * r * t := by
    intro i
    fin_cases i
    · show f ≤ f * r * t
      simpa using Nat.mul_le_mul (Nat.mul_le_mul (le_refl f) hr) ht
    · show r ≤ f * r * t
      simpa using Nat.mul_le_mul (Nat.mul_le_mul hf (le_refl r)) ht
    · show t ≤ f * r * t
      simpa using Nat.mul_le_mul (Nat.mul_le_mul hf hr) (le_refl t)
  have hpos : 0 < f * r * t := by positivity
  calc ∏ i, (![f, r, t] : Fin 3 → ℕ) i ^ m i ≤ ∏ i : Fin 3, (f * r * t) ^ m i :=
        Finset.prod_le_prod' fun i _ => Nat.pow_le_pow_left (hM i) _
    _ = (f * r * t) ^ (∑ i, m i) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ (f * r * t) ^ Q.totalDegree := by
        apply Nat.pow_le_pow_right hpos
        have := MvPolynomial.le_totalDegree hm
        rwa [Finsupp.sum_fintype _ _ (by simp)] at this

theorem starG_of_thmB : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (ρ : FamilyRepresentationConstants.RhoFam D) (constantFirstHub C : ℝ)
    (Q : MvPolynomial (Fin 3) ℕ), FamilyRepresentationConstants.CG constantFirstHub Q ≤ C → EmbeddingTypeJumps.Conclusion2 ρ L constantFirstHub Q → KillingConditions.KillAt ρ →
    TwistedPlaces.ShaFinOdd D → StarG L ρ C := by
  intro D L P ρ constantFirstHub C Q hCG hB hK hSha
  unfold StarG
  intro i hi hl π hπ
  unfold Bd
  unfold FamilyRepresentationConstants.CG at hCG
  have hC67 : constantFirstHub ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCG
  have hS : ((∑ m ∈ Q.support, Q.coeff m : ℕ) : ℝ) ≤ C :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCG
  have hdeg : (Q.totalDegree : ℝ) ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCG
  have hC1 : (1 : ℝ) ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCG

  have ht1 : 1 ≤ D.R.t := D.R.t_odd.pos
  have hr1 : 1 ≤ D.R.r := by
    unfold Ranks.r
    have := D.R.m_add_three_le_k
    omega
  have hf1 : 1 ≤ D.R.f := by
    have := D.R.two_le_m
    have := D.R.m_le_f
    unfold Ranks.f Ranks.n
    omega
  have htr : 1 ≤ D.R.t * D.R.r := by simpa using Nat.mul_le_mul ht1 hr1

  have hlp : (D.nd.l i).Prime := by
    rcases hl with h | h <;> rw [h]
    exacts [D.host.hyp.1, D.host.hyp.2.1]
  have hl2 : 2 < D.nd.l i := by
    have hqd := D.host.qd_big
    rcases hl with h | h <;> rw [h] <;> nlinarith [hqd.1, hqd.2]
  have hodd : Odd (D.nd.l i) := hlp.odd_of_ne_two (by omega)
  have hlbig : L.sc.x ^ (2 * L.Ct + 5) < (D.nd.l i : ℝ) := by
    rcases hl with h | h <;> rw [h]
    exacts [P.qd_pow.1, P.qd_pow.2]
  have hsha : ∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤ := by
    intro e he
    rw [Finset.mem_Ioo] at he
    haveI : Fact (D.nd.l i).Prime := ⟨hlp⟩
    exact lt_top_iff_ne_top.2 (hSha (D.nd.l i) e he.1 he.2)
  have hK' := (hK i hi).1 π hπ
  have h := hB i hl hi hlbig π hπ hK'.1 hsha

  have hVV : TwistedPlaces.VVr D (D.nd.l i) =
      ((∑ e ∈ Finset.Ioo 0 D.R.t, D.what₂.shaLen (D.nd.l i) e : ℚ) : ℝ) := by
    show ((∑ e ∈ Finset.Ico 1 D.R.t, D.what₂.shaLen (D.nd.l i) e : ℚ) : ℝ) = _
    congr 2
  have hvh : TwistedPlaces.vhE D (D.nd.l i) = (padicValNat (D.nd.l i) (hE D.host) : ℝ) := rfl
  have heps : TwistedPlaces.epsL (D.nd.l i) = EmbeddingTypeJumps.epsL (D.nd.l i) := by
    unfold TwistedPlaces.epsL EmbeddingTypeJumps.epsL
    rw [one_div]

  have hLpos : 0 < TwistedPlaces.large₂ L := Real.rpow_pos_of_pos (by linarith [L.sc.one_lt_alt]) _
  have hlog : Real.log L.sc.b = TwistedPlaces.large₂ L := Real.log_exp _
  have hbpos : 0 < L.sc.b := Real.exp_pos _
  have hlpos : (0 : ℝ) < D.nd.l i := by exact_mod_cast hlp.pos
  have hbr : 0 ≤ (D.R.r : ℝ) * (L.sc.b / (D.nd.l i) + L.Sc + D.R.t + L.etaSz + TwistedPlaces.large₂ L) +
      D.R.m * L.sc.b := by
    have h1 := L.Sc_pos
    have h2 := L.etaSz_pos
    have h3 : 0 ≤ L.sc.b / (D.nd.l i) := div_nonneg hbpos.le hlpos.le
    have h4 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
    have h5 : 0 ≤ L.sc.b / (D.nd.l i) + L.Sc + D.R.t + L.etaSz + TwistedPlaces.large₂ L := by linarith
    positivity
  have hM1 : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * D.R.t := by exact_mod_cast Nat.mul_le_mul (Nat.mul_le_mul hf1 hr1) ht1
  have hpoly : ((EmbeddingTypeJumps.polyVal Q D.R.f D.R.r D.R.t : ℕ) : ℝ) ≤ C * ((D.R.f : ℝ) * D.R.r * D.R.t) ^ C := by
    have h1 : ((EmbeddingTypeJumps.polyVal Q D.R.f D.R.r D.R.t : ℕ) : ℝ) ≤
        ((∑ m ∈ Q.support, Q.coeff m : ℕ) : ℝ) * ((D.R.f : ℝ) * D.R.r * D.R.t) ^ Q.totalDegree := by
      exact_mod_cast polyVal_le_sum_mul_pow Q _ _ _ hf1 hr1 ht1
    have hpow : ((D.R.f : ℝ) * D.R.r * D.R.t) ^ Q.totalDegree ≤ ((D.R.f : ℝ) * D.R.r * D.R.t) ^ C := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hM1 hdeg
    exact h1.trans (mul_le_mul hS hpow (by positivity) (by linarith))
  have hbnd : EmbeddingTypeJumps.bndB D L constantFirstHub Q (D.nd.l i) ≤ TwistedPlaces.midG L C (D.nd.l i) := by
    unfold EmbeddingTypeJumps.bndB TwistedPlaces.midG
    rw [hlog]
    have e1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC67 (Nat.cast_nonneg D.R.f)) hbr
    have e2 := mul_le_mul_of_nonneg_right hpoly hLpos.le
    linarith
  rw [hVV, hvh, heps]
  linarith

end GlobalTheory.NLink

end
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NBand

theorem prime_eq_of_mem {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {w : HeightOneSpectrum (𝓞 E)} (h1 : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal) (h2 : ((q : ℕ) : 𝓞 E) ∈ w.asIdeal) :
    p = q := by
  by_contra hne
  have hc : IsCoprime ((p : ℕ) : 𝓞 E) ((q : ℕ) : 𝓞 E) :=
    Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left a h1) (w.asIdeal.mul_mem_left b h2)

theorem logb_le_of_le_four_exp {l : ℕ} (hl : (11 : ℝ) ≤ l) {large₂ h : ℝ} (hL : 1 ≤ large₂) (h0 : 0 ≤ h)
    (hh : h ≤ 4 * Real.exp large₂) : Real.logb l h ≤ large₂ := by
  have hl1 : (1 : ℝ) < l := by linarith
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hloge : Real.log 4 + 1 ≤ Real.log l := by
    have he := Real.exp_one_lt_d9
    have : Real.log (4 * Real.exp 1) = Real.log 4 + 1 := by
      rw [Real.log_mul (by norm_num) (Real.exp_pos 1).ne', Real.log_exp]
    rw [← this]
    exact Real.log_le_log (by positivity) (by linarith)
  have hlpos : 0 < Real.log l := Real.log_pos hl1
  rcases h0.eq_or_lt with h0' | h0'
  · rw [← h0', Real.logb_zero]; linarith
  have h1 : Real.logb l h ≤ Real.logb l (4 * Real.exp large₂) := Real.logb_le_logb_of_le hl1 h0' hh
  refine h1.trans ?_
  rw [Real.logb, Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp, div_le_iff₀ hlpos]
  nlinarith

theorem band_arith {lr s z Wb Lb e S Sc eta₃ lg large₂ T CB C : ℝ} (hl : 11 ≤ lr) (hs0 : 0 ≤ s)
    (hzs : |z - s| ≤ T) (hb1 : Lb - T ≤ Wb) (hb2 : Wb ≤ Lb - T + 1) (he : e ≤ eta₃) (hS : S ≤ Sc)
    (hlg : lg ≤ large₂) (hLg : 1 ≤ large₂) (hSc : 0 ≤ Sc) (hLb : 0 ≤ Lb) (hT : 1 / 2 ≤ T) (hTe : 2 * T + 1 ≤ eta₃)
    (hCB : 0 ≤ CB) (hC : 6 * CB + 1 ≤ C)
    (habs : |lr * z - Wb| ≤ CB * (lr * e + lr * S + Wb / lr + z + lr * lg)) :
    |lr * s - Lb| ≤ C * (lr * eta₃ + lr * Sc + Lb / lr + s + lr * large₂) := by
  set E := lr * eta₃ + lr * Sc + Lb / lr + s + lr * large₂ with hE
  have hlr0 : 0 < lr := by linarith
  rw [abs_le] at hzs habs
  have hA : lr * e + lr * S + Wb / lr + z + lr * lg ≤ E + lr * eta₃ := by
    have e1 : lr * e ≤ lr * eta₃ := mul_le_mul_of_nonneg_left he hlr0.le
    have e2 : lr * S ≤ lr * Sc := mul_le_mul_of_nonneg_left hS hlr0.le
    have e3 : Wb / lr ≤ Lb / lr + 1 / lr := by
      rw [← add_div]; exact div_le_div_of_nonneg_right (by linarith) hlr0.le
    have e3' : 1 / lr ≤ 1 := by rw [div_le_one hlr0]; linarith
    have e5 : lr * lg ≤ lr * large₂ := mul_le_mul_of_nonneg_left hlg hlr0.le
    have e6 : eta₃ ≤ lr * eta₃ := by nlinarith
    rw [hE]; linarith
  have hEge : lr * eta₃ ≤ E := by
    have : 0 ≤ Lb / lr := div_nonneg hLb hlr0.le
    have : 0 ≤ lr * Sc := mul_nonneg hlr0.le hSc
    have : 0 ≤ lr * large₂ := mul_nonneg hlr0.le (by linarith)
    rw [hE]; linarith
  have hEt0 : 0 ≤ lr * eta₃ := mul_nonneg hlr0.le (by linarith)
  have hx1 : lr * T + T ≤ lr * eta₃ := by nlinarith
  have hCBA : CB * (lr * e + lr * S + Wb / lr + z + lr * lg) ≤ CB * (E + lr * eta₃) :=
    mul_le_mul_of_nonneg_left hA hCB
  have hCE : (2 * CB + 1) * E ≤ C * E := mul_le_mul_of_nonneg_right (by linarith) (hEt0.trans hEge)
  have hm1 : lr * (s - z) ≤ lr * T := mul_le_mul_of_nonneg_left (by linarith) hlr0.le
  have hm2 : -(lr * T) ≤ lr * (s - z) := by
    rw [← mul_neg]; exact mul_le_mul_of_nonneg_left (by linarith) hlr0.le
  have hCBE : CB * (lr * eta₃) ≤ CB * E := mul_le_mul_of_nonneg_left hEge hCB
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

end GlobalTheory.NBand

theorem GlobalTheory.NBand.bandPlaceWeightApproximation_tabX : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (C : ℝ), KillingConditions.DataAD L HW X R → R.Le C → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → TwistedPlaces.BandPlaceWeightApproximation L (tabX L X) C := by
  intro D L P HW X R C hX hR hpar
  intro i lam hTw hb l hl hlp
  obtain ⟨h11, π, hπ, hw, Cx, hG, Wd, hBase, hBox, hNT, hBand⟩ := (hX.band i lam).1 hb
  have hli : l = D.nd.l i := prime_eq_of_mem hlp (D.nd.lPrime i).out hl hw
  subst hli
  obtain ⟨a, hnt, -, habs⟩ := hBand
  obtain ⟨s, hs1, hs2, hs3⟩ := hBox.nt a hnt
  refine ⟨s, hs1, hs2, ?_⟩
  obtain ⟨-, hCB, -, -, -, -, -, -, -, hC6, -⟩ := hR
  have hl11 : (11 : ℝ) ≤ (D.nd.l i : ℝ) := by exact_mod_cast h11
  have hLg : 1 ≤ TwistedPlaces.large₂ L := by
    unfold TwistedPlaces.large₂ Scale.L
    exact Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have hbexp : L.sc.b = Real.exp (TwistedPlaces.large₂ L) := rfl
  have hpar' : L.Sc + L.etaSz + (D.R.t : ℝ) + 2 ≤ L.sc.b := hpar
  have hSc := L.Sc_pos
  have hEt := L.etaSz_pos
  have ht0 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hetaP : TwistedPlaces.eta₃ L = L.etaSz + D.R.t + 2 := rfl
  have hhB : TwistedPlaces.hB L = L.sc.b + L.Sc + L.etaSz + D.R.t + 2 := rfl
  have hh17n : Formalism.MainNotions.TruncatedSeriesCountingBounds.hB Wd.b Wd.w Wd.S Wd.η Wd.sz ≤ Wd.b + Wd.η + Wd.S := by
    have := hNT.w20
    unfold Formalism.MainNotions.TruncatedSeriesCountingBounds.hB; split_ifs <;> omega
  have hh17 : ((Formalism.MainNotions.TruncatedSeriesCountingBounds.hB Wd.b Wd.w Wd.S Wd.η Wd.sz : ℕ) : ℝ) ≤ (Wd.b : ℝ) + Wd.η + Wd.S := by
    exact_mod_cast hh17n
  have hhle := hBase.h_le
  have hlg : Real.logb (D.nd.l i : ℝ) (2 * ((Formalism.MainNotions.TruncatedSeriesCountingBounds.hB Wd.b Wd.w Wd.S Wd.η Wd.sz : ℕ) : ℝ)) ≤ TwistedPlaces.large₂ L := by
    apply logb_le_of_le_four_exp hl11 hLg (by positivity)
    rw [← hbexp]; linarith
  have hw0 : 0 ≤ L.sc.w'' D.R.n := by
    have hx : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]
    unfold Scale.w'' Scale.b' Scale.a Scale.X' Scale.b
    apply div_nonneg
    · exact div_nonneg (mul_nonneg hx.le (Real.exp_pos _).le) (Real.exp_pos _).le
    · exact mul_nonneg hx.le (Nat.cast_nonneg _)
  exact band_arith hl11 (hw0.trans hs1) hs3 hBox.b_lo hBox.b_hi hBase.η_le hBase.S_le hlg hLg hSc.le
    (by rw [hbexp]; exact (Real.exp_pos _).le) (by linarith) (by rw [hetaP]; linarith) hCB hC6 habs
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.MultiplicityBound

theorem finrank_biSup_indep {K V ι : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [DecidableEq ι] {t : ι → Submodule K V} (ht : iSupIndep t) (A : Finset ι) :
    Module.finrank K ↥(⨆ σ ∈ A, t σ) = ∑ σ ∈ A, Module.finrank K ↥(t σ) := by
  induction A using Finset.induction_on with
  | empty => simp
  | insert a A ha ih =>
    rw [Finset.sum_insert ha, ← ih]
    have hs : (⨆ σ ∈ insert a A, t σ) = t a ⊔ ⨆ σ ∈ A, t σ := by
      rw [Finset.iSup_insert]
    have hd : Disjoint (t a) (⨆ σ ∈ A, t σ) := ht.disjoint_biSup (by simpa using ha)
    rw [hs, ← Submodule.finrank_sup_add_finrank_inf_eq, hd.eq_bot, finrank_bot, add_zero]


open Classical in
noncomputable def goodRows (D : D7) (i : D.nd.Loc) : Finset D.what₂.FT :=
  Finset.univ.filter (fun σ => D.nd.goodRow σ ∧ AtM D.nd D.naut i σ)

theorem dM_eq_sum (D : D7) (hI : Rows.IsotInternal D.what₂) (i : D.nd.Loc) (j : ℕ) (h : D.nd.j i = j) :
    dM D.nd D.naut i = ∑ σ ∈ goodRows D i, Module.finrank ℂ ↥(D.what₂.isot j σ) := by
  classical
  subst h
  have hr := D.nd.j_range i
  have hind : iSupIndep (D.what₂.isot (D.nd.j i)) := (hI _ hr.1 hr.2).submodule_iSupIndep
  have hsup : goodPartM D.nd D.naut i = ⨆ σ ∈ goodRows D i, D.what₂.isot (D.nd.j i) σ := by
    unfold goodPartM goodRows
    apply iSup_congr
    intro σ
    simp
  unfold dM
  rw [hsup]
  exact finrank_biSup_indep hind _

theorem sum_mult_le (D : D7) (hZ : SumRepresentations.ConclusionZ D) (i : D.nd.Loc) :
    (∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℝ)) ≤ (dM D.nd D.naut i : ℝ) := by
  classical
  rcases (D.nd.Zgood i).eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sum_empty]
    exact Nat.cast_nonneg _
  · have hG : HG D.nd D.naut i := by
      obtain ⟨x, hx⟩ := hne
      exact ⟨x, (D.Zgood_tie i x).1 hx⟩
    have h3 := (hZ i hG).2.2
    rw [← h3, ← Nat.cast_sum]
    apply le_of_eq
    congr 1
    rw [← Finset.sum_subset (Finset.subset_univ (D.nd.Zgood i))]
    · apply Finset.sum_congr rfl
      intro x hx
      rw [if_pos ((D.Zgood_tie i x).1 hx)]
    · intro x _ hx
      rw [if_neg (fun h => hx ((D.Zgood_tie i x).2 h))]

end GlobalTheory.MultiplicityBound


open GlobalTheory.MultiplicityBound in
theorem GlobalTheory.NLink.multLe_of_rank : ∀ (D : D7) (L : SizeData₂ D), SumRepresentations.Conclusion42 D → SumRepresentations.ConclusionZ D → Rows.IsotInternal D.what₂ →
    KillingConditions.LocalisationUniqueness D → MultLe L := by
  intro D L h42 hZ hI h2 j hj w hw
  classical
  rcases (D.nd.locs j w).eq_empty_or_nonempty with he | ⟨i0, hi0⟩
  · rw [he, Finset.sum_empty]
    exact Nat.cast_nonneg _
  obtain ⟨hj0, hw0⟩ := (D.nd.locs_mem j w i0).1 hi0
  subst hj0 hw0
  have hr := D.nd.j_range i0
  have hind : iSupIndep (D.what₂.isot (D.nd.j i0)) := (hI _ hr.1 hr.2).submodule_iSupIndep
  have h1 : (∑ i ∈ D.nd.locs (D.nd.j i0) (D.nd.w i0), ∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℝ)) ≤
      ((∑ i ∈ D.nd.locs (D.nd.j i0) (D.nd.w i0), dM D.nd D.naut i : ℕ) : ℝ) := by
    rw [Nat.cast_sum]
    exact Finset.sum_le_sum (fun i _ => sum_mult_le D hZ i)
  refine h1.trans ?_
  apply Nat.cast_le.2
  have hdisj : (↑(D.nd.locs (D.nd.j i0) (D.nd.w i0)) : Set D.nd.Loc).PairwiseDisjoint (goodRows D) := by
    intro i hi i' hi' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro σ hσ hσ'
    have hi := (D.nd.locs_mem _ _ i).1 hi
    have hi' := (D.nd.locs_mem _ _ i').1 hi'
    simp only [goodRows, Finset.mem_filter, Finset.mem_univ, true_and] at hσ hσ'
    have htw : TwistedPlaces.TwLoc D i := by
      unfold TwistedPlaces.TwLoc
      rw [hi.2]
      exact hw
    exact hne (h2 i i' htw (hi.1.trans hi'.1.symm) (hi.2.trans hi'.2.symm) σ hσ.1 hσ.2 hσ'.2)
  calc (∑ i ∈ D.nd.locs (D.nd.j i0) (D.nd.w i0), dM D.nd D.naut i)
      = ∑ i ∈ D.nd.locs (D.nd.j i0) (D.nd.w i0), ∑ σ ∈ goodRows D i,
          Module.finrank ℂ ↥(D.what₂.isot (D.nd.j i0) σ) :=
        Finset.sum_congr rfl (fun i hi => dM_eq_sum D hI i _ ((D.nd.locs_mem _ _ i).1 hi).1)
    _ = ∑ σ ∈ (D.nd.locs (D.nd.j i0) (D.nd.w i0)).biUnion (goodRows D),
          Module.finrank ℂ ↥(D.what₂.isot (D.nd.j i0) σ) :=
        (Finset.sum_biUnion hdisj).symm
    _ = Module.finrank ℂ ↥(⨆ σ ∈ (D.nd.locs (D.nd.j i0) (D.nd.w i0)).biUnion (goodRows D),
          D.what₂.isot (D.nd.j i0) σ) :=
        (finrank_biSup_indep hind _).symm
    _ ≤ Module.finrank ℂ (D.what₂.Mj (D.nd.j i0)) := Submodule.finrank_le _
    _ = L.zeroSpaceRankAtPlace (D.nd.j i0) (D.nd.w i0) := by
        unfold SizeData₂.zeroSpaceRankAtPlace Rows.Data.Zj
        rw [← D.nd.mu_w i0,
          LinearMap.finrank_range_of_inj (Formalism.MainNotions.J.theta_injective_of_scalars D h42 hI i0 hj)]
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per

namespace GlobalTheory.PMon.Ram

theorem senFinite_of_noTower (hNT : NoTower) : SenFinite := by
  intro l _ n _ _ K ρ hc M hM
  obtain ⟨N, hN, hanti, hopen, hpow, hroot, hker⟩ := GlobalTheory.T.exists_congruenceFiltration_galoisRep l n K ρ hc
  have hdet := GlobalTheory.T.exists_detecting_characters_congr_filtration l n K ρ M hM N hN
  obtain ⟨k, hk⟩ := hNT l K N hanti hopen hpow hroot hdet
  refine GlobalTheory.T.finite_image_of_trivial_on_inf_isOpen l K (GL n ℚ_[l]) ρ (IK K) (N k) (hopen k) ?_
  intro g hgI hgN
  exact hker g (fun j => hk j ⟨hgI, hgN⟩)

end GlobalTheory.PMon.Ram
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem ordIs_padic_self (l : ℕ) [Fact l.Prime] : OrdIs ℚ_[l] l 1 := by
  unfold OrdIs
  rw [IsDiscreteValuationRing.addVal_uniformizer (GroundTheory.LocalField.Padic.irreducible_natCast_integer l)]
  rfl

theorem ordIs_eq_card_inertia : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra ℚ_[l] L] [ValuativeExtension ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    [IsGalois ℚ_[l] L] [Algebra L (Om l)] [IsScalarTower ℚ_[l] L (Om l)],
    OrdIs L l (Nat.card ↥(lowerRamificationGroup ℚ_[l] L 0)) := by
  intro l _ L _ _ _ _ _ _ _ _ _ _
  have hlL : (l : L) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[l] L)]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hne : ((l : 𝒪[L])) ≠ 0 := by
    intro h
    apply hlL
    have h2 : ((l : 𝒪[L]) : L) = 0 := by rw [h]; rfl
    simpa using h2
  have htop : IsDiscreteValuationRing.addVal 𝒪[L] (l : 𝒪[L]) ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  obtain ⟨E, hE⟩ := WithTop.ne_top_iff_exists.1 htop
  have hL : OrdIs L l E := by unfold OrdIs; rw [← hE]; rfl
  obtain ⟨e, he, hEe, hram⟩ := GlobalTheory.T.normalizedValuationOfPrime_of_galoisExtension ℚ_[l] L l E hL
  have h1 := ordIs_padic_self l
  unfold OrdIs at he h1
  have he1 : e = 1 := by
    have := he.symm.trans h1
    exact_mod_cast this
  subst he1
  rw [mul_one] at hEe
  unfold OrdIs
  rw [← hram, ← hEe, ← hE]
  rfl

end GlobalTheory.PMon.Ram
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.bcrisPlus_frobeniusStable_subring_in_filZero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI), (∀ b, Plus T b → Plus T (P.φB b)) ∧ (∀ b, Plus T b → ∀ j, ev P j b ∈ Fil P 0) ∧ (∀ a b, Plus T a → Plus T b → Plus T (a + b) ∧ Plus T (a * b)) ∧ (∀ q : ℚ_[l], Plus T (algebraMap ℚ_[l] P.R.B q)) ∧ (∀ x : Formalism.Per.Ainf l, Plus T (T.eB.symm (Formalism.Per.aB l x))) ∧ Plus T P.tB := by
  first | exact @GlobalTheory.PMon.CrisPlus.plus_props | exact GlobalTheory.PMon.CrisPlus.plus_props | (intros; apply GlobalTheory.PMon.CrisPlus.plus_props <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_theta_deRhamFilZero_surjective : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI), ∃ (S : Subring P.R.BdR) (θ : ↥S →+* ℂ_[l]), (∀ x, x ∈ S ↔ x ∈ Fil P 0) ∧ Function.Surjective θ ∧ (∀ x : ↥S, θ x = 0 ↔ (x : P.R.BdR) ∈ Fil P 1) ∧ (∀ y : Om l, ∃ h, θ ⟨algebraMap (Om l) P.R.BdR y, h⟩ = (y : ℂ_[l])) ∧ ∀ (g : GQ l) (x : ↥S), ∃ h, θ ⟨P.actQdR g x, h⟩ = Formalism.Per.σC g (θ x) := by
  first | exact @GlobalTheory.PMon.exists_theta_deRhamFilZero_surjective_alt | exact GlobalTheory.PMon.exists_theta_deRhamFilZero_surjective_alt | (intros; apply GlobalTheory.PMon.exists_theta_deRhamFilZero_surjective_alt <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

theorem _root_.GlobalTheory.T.residual_selmer_determinant_order_bound : TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → FirstHalf i s → Recip bkP i s → EqDim bkP i s → ResBound bkP i s := by
  first | exact @GlobalTheory.ResOrder.resBound | exact GlobalTheory.ResOrder.resBound | (intros; apply GlobalTheory.ResOrder.resBound <;> assumption)
end
