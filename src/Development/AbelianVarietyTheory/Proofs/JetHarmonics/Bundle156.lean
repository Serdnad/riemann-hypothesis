module

public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle021
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle014
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle140
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle153
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle076
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle074
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle060
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle091
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle104
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle132
public import Formalism.HermitianCurvature.StatementQ
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle154
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMeanContinuity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle008
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle034
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle148
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle042
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm

@[expose] public section

section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.TranslNorm

theorem even_of_inOK_half {d : ℕ} (hd : 0 < d) {s : ℕ} (h : InOK d ((s : ℂ) / 2)) : 2 ∣ s := by
  obtain ⟨u, v, h⟩ := h
  have hs : Real.sqrt d ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    exact (Real.sqrt_pos.mpr this).ne'
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp [wK] at him hre
  have hv : v = 0 := by
    rcases him with h | h
    · exact h
    · exfalso
      first | exact hs h | omega
  subst hv
  have h2 : (s : ℝ) = 2 * u := by
    simp at hre
    linarith
  have h3 : (s : ℤ) = 2 * u := by exact_mod_cast h2
  omega

theorem inOK_add {d : ℕ} {x y : ℂ} (hx : InOK d x) (hy : InOK d y) : InOK d (x + y) := by
  obtain ⟨u, v, rfl⟩ := hx
  obtain ⟨u', v', rfl⟩ := hy
  exact ⟨u + u', v + v', by push_cast; ring⟩

theorem inOK_int_mul {d : ℕ} (k : ℤ) {x : ℂ} (hx : InOK d x) : InOK d ((k : ℂ) * x) := by
  obtain ⟨u, v, rfl⟩ := hx
  exact ⟨k * u, k * v, by push_cast; ring⟩

theorem primeTo_add {d q : ℕ} {x y : ℂ} (hx : PrimeTo d q x) (hy : PrimeTo d q y) :
    PrimeTo d q (x + y) := by
  obtain ⟨s, hs, hsq, hx⟩ := hx
  obtain ⟨r, hr, hrq, hy⟩ := hy
  refine ⟨s * r, Nat.mul_pos hs hr, Nat.Coprime.mul_left hsq hrq, ?_⟩
  have := inOK_add (inOK_int_mul (r : ℤ) hx) (inOK_int_mul (s : ℤ) hy)
  convert this using 1
  push_cast
  ring

theorem norm_law : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → ∀ (a m : ℕ) (c : Fin m → ℂ_[q]) (s : Fin m → ℂ) (t : ℂ) (B : ℝ), (∀ j, PrimeTo d q (s j)) → PrimeTo d q t → Bd B (∑ j, C (c j) * hat M.ι (C ω * logS) (U1 d (s j) θ) ^ a) → Bd B (∑ j, C (c j) * hat M.ι (C ω * logS) (U1 d t (U1 d (s j) θ)) ^ a) := by
  intro d q hq M ω θ hd hd16 hsp hL hM hθ a m c s t B hs ht hB
  have law0 := GlobalTheory.T.translate_coprime_order_not_increase_theta_comb_norm d q M ω θ hd hd16 hsp hL hM hθ a m
  by_cases hhalf : InOK d (t - 1 / 2)
  swap
  · exact law0 c s t B hs ht hhalf hB
  have hd0 : 0 < d := hd.pos
  obtain ⟨hUU, -, hdiff, -⟩ := GlobalTheory.T.cmLattice_heisenberg_relations_one_variable d hd0
  obtain ⟨hlaws, hconst, -⟩ := GlobalTheory.MomOne.TaylorRead.hat_laws q M.ι (C ω * logS) hM.2.1
  have hcm : ∀ (r : ℂ) (F : ℂ → ℂ), Differentiable ℂ F →
      hat M.ι (C ω * logS) (fun z => r * F z) = C (M.ι r) * hat M.ι (C ω * logS) F := by
    intro r F hF
    rw [← hconst r]
    exact (hlaws (fun _ => r) F analyticAt_const (hF.analyticAt 0)).2.1
  have hτ : PrimeTo d q (t / 2) := by
    obtain ⟨n, hn, hnq, hnt⟩ := ht
    have h2 : 2 ∣ n := by
      apply even_of_inOK_half hd0
      have := inOK_add hnt (inOK_int_mul (-(n : ℤ)) hhalf)
      convert this using 1
      push_cast
      ring
    refine ⟨n * n, Nat.mul_pos hn hn, Nat.Coprime.mul_left hnq hnq, ?_⟩
    obtain ⟨k, hk⟩ := h2
    have := inOK_int_mul (k : ℤ) hnt
    convert this using 1
    have hk' : (n : ℂ) = 2 * k := by exact_mod_cast hk
    push_cast
    rw [hk']
    ring
  have hτ' : ¬ InOK d (t / 2 - 1 / 2) := by
    intro h
    have h1 : InOK d 1 := ⟨1, 0, by simp⟩
    have h2 : 2 ∣ 1 := by
      apply even_of_inOK_half hd0
      have := inOK_add (inOK_add (inOK_int_mul 2 h) h1) (inOK_int_mul (-1) hhalf)
      convert this using 1
      push_cast
      ring
    omega
  have hdouble : ∀ F : ℂ → ℂ, U1 d (t / 2) (U1 d (t / 2) F) = U1 d t F := by
    intro F
    rw [hUU]
    have him : (h1 d (t / 2) (t / 2)).im = 0 := by
      rw [h1, Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_im]
    funext z
    rw [him, add_halves]
    simp
  set r : Fin m → ℂ := fun j =>
    Complex.exp (-(Real.pi : ℂ) * Complex.I * (((h1 d (t / 2) (s j)).im : ℝ) : ℂ)) with hr
  have hstep : ∀ j, U1 d (t / 2) (U1 d (s j) θ) = fun z => r j * U1 d (t / 2 + s j) θ z :=
    fun j => hUU _ _ _
  have hD : ∀ j, Differentiable ℂ (U1 d (t / 2 + s j) θ) := fun j => (hdiff _ _ hθ.1).1
  have h1 := law0 c s (t / 2) B hs hτ hτ' hB
  have h2 : Bd B (∑ j, C (c j * M.ι (r j) ^ a) *
      hat M.ι (C ω * logS) (U1 d (t / 2 + s j) θ) ^ a) := by
    convert h1 using 2 with j
    rw [hstep j, hcm _ _ (hD j), mul_pow, map_mul, map_pow, mul_assoc]
  have h3 := law0 _ _ (t / 2) B (fun j => primeTo_add hτ (hs j)) hτ hτ' h2
  convert h3 using 2 with j
  have : U1 d t (U1 d (s j) θ) = fun z => r j * U1 d (t / 2) (U1 d (t / 2 + s j) θ) z := by
    rw [← hdouble, hstep j]
    funext z
    simp only [U1]
    ring
  rw [this, hcm _ _ (hdiff _ _ (hD j)).1, mul_pow, map_mul, map_pow, mul_assoc]

end GlobalTheory.MomOne.TranslNorm
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.WedgeKappa

theorem n1_add_eZ_le_add_card {n : ℕ} (ν : Fin n → ℤ) (I : Finset (Fin n)) : n1 (ν + eZ I) ≤ n1 ν + I.card := by
  unfold n1
  have h1 : ∑ i, (eZ I i).natAbs = I.card := by
    have : ∀ i, (eZ I i).natAbs = if i ∈ I then 1 else 0 := by
      intro i; unfold eZ; split_ifs <;> rfl
    simp [this]
  rw [← h1, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => Int.natAbs_add_le _ _

theorem eZ_injective {n : ℕ} : Function.Injective (eZ : Finset (Fin n) → Fin n → ℤ) := by
  intro I J h
  ext i
  have := congrFun h i
  unfold eZ at this
  by_cases hI : i ∈ I <;> by_cases hJ : i ∈ J <;> simp_all

theorem kappa_bound : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → ∀ ν, n1 ν + (r + 1) * (r + 2) ≤ q0 → ∀ io pr ep, TensH (cmp (r + 1)) (cmp (r + 1) (Formalism.QuantumDeterminants.Hpk k r)) (R ν) (fun I : Sub (2 * r + k + 1) (r + 1) => R (ν + eZ I.1)) io pr ep → NzOn (R ν) (l ν) → ∀ (I : Sub (2 * r + k + 1) (r + 1)) (κ₀ : ℂ), NzOn (R (ν + eZ I.1)) (l (ν + eZ I.1)) → (∀ v ∈ (R ν).sm, l (ν + eZ I.1) (∑ c, pr I c (tm (R ν) (wedge (Formalism.QuantumDeterminants.fvec k r z)) v c)) = κ₀ • l ν v) → ‖κ₀‖ ^ 2 * dg ν / dg (ν + eZ I.1) ≤ Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ (r + 1) := by
  intro hyp k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hν io pr ep hT hnz I κ₀ hnzI hκ
  classical
  have hS' := hS
  obtain ⟨hNum, hFam, hG, hSF⟩ := hS'
  have hν0 : n1 ν ≤ q0 := by omega
  have hνJ : ∀ J : Sub (2 * r + k + 1) (r + 1), n1 (ν + eZ J.1) + (r + 1) ^ 2 ≤ q0 := by
    intro J
    have := n1_add_eZ_le_add_card ν J.1
    rw [J.2] at this
    nlinarith
  have hνJ0 : ∀ J : Sub (2 * r + k + 1) (r + 1), n1 (ν + eZ J.1) ≤ q0 := fun J =>
    le_trans (Nat.le_add_right _ _) (hνJ J)
  have hDS := hFam ν hν0
  have hDSJ := fun J : Sub (2 * r + k + 1) (r + 1) => hFam (ν + eZ J.1) (hνJ0 J)
  have hF := GlobalTheory.WedgeFRep.isFRep_cmp k r (r + 1)
  have hdual := fun J : Sub (2 * r + k + 1) (r + 1) =>
    GlobalTheory.T.bessel_tensor_projection_scalar_and_adjoint hyp k r _ _ _ _ _ (R ν) _ io pr ep _ _ _ Wp z π u μW μN μG νq
      (wedge (Formalism.QuantumDeterminants.fvec k r z)) (l ν) hDS hDSJ hF hT hG
      (fun s hs => (GlobalTheory.FlagFix.fixes_wedge_and_form k r z hG.1 s hs).1) (hSF ν hν0).1 hnz J
      (l (ν + eZ J.1)) (hSF _ (hνJ0 J)).1
  have hex : ∀ J : Sub (2 * r + k + 1) (r + 1), ∃ c : ℂ, (J = I → c = κ₀) ∧
      ∀ y ∈ (R (ν + eZ J.1)).sm, l ν (ev (cmp (r + 1) (Formalism.QuantumDeterminants.Hpk k r)) (R ν) (wedge (Formalism.QuantumDeterminants.fvec k r z))
        (fun c => io J c y)) = ((ep J : ℂ) * star c) • l (ν + eZ J.1) y := by
    intro J
    by_cases hJ : J = I
    · subst hJ
      exact ⟨κ₀, fun _ => rfl, (hdual J).2 κ₀ hκ⟩
    · obtain ⟨c, hc⟩ := (hdual J).1
      exact ⟨c, fun h => absurd h hJ, (hdual J).2 c hc⟩
  choose κ hκI hκd using hex
  have hd0 : 0 < dg ν := (hSF ν hν0).2.1
  have hdJ : ∀ J : Sub (2 * r + k + 1) (r + 1), 0 < dg (ν + eZ J.1) := fun J => (hSF _ (hνJ0 J)).2.1
  have hmass := GlobalTheory.T.bessel_functional_l2_bound_and_isometry hyp k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS
  obtain ⟨w, hw, hw1, hint⟩ := GlobalTheory.T.family_exists_unit_product_moment_le_Hsq_pow hyp k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS _ (hνJ I) hnzI
  have hinj : Function.Injective (fun (J : Sub (2 * r + k + 1) (r + 1)) (a : Fin (2 * r + k + 1)) =>
      lam a + (((ν + eZ J.1) a : ℤ) : ℝ)) := by
    intro J J' hJ
    apply Subtype.ext
    apply eZ_injective
    funext a
    have := congrFun hJ a
    simp only [Pi.add_apply, add_right_inj, Int.cast_inj] at this
    exact this
  have h8 := GlobalTheory.T.tensor_moment_weighted hyp k r _ _ _ _ _ (R ν) _ io pr ep _ _ _ Wp z π u μW μN μG νq
    (wedge (Formalism.QuantumDeterminants.fvec k r z)) (fun w => ((Real.sqrt (dg ν) : ℝ) : ℂ) • l ν w)
    (fun J w => ((Real.sqrt (dg (ν + eZ J.1)) : ℝ) : ℂ) • l (ν + eZ J.1) w)
    (fun J => if NzOn (R (ν + eZ J.1)) (l (ν + eZ J.1)) then
      (ep J : ℂ) * star (κ J) * ((Real.sqrt (dg ν) : ℝ) : ℂ) / ((Real.sqrt (dg (ν + eZ J.1)) : ℝ) : ℂ) else 0)
    hDS hDSJ hinj hF hT hG ((hmass ν hν0).2 hnz).1
    (fun J => by
      by_cases hJ : NzOn (R (ν + eZ J.1)) (l (ν + eZ J.1))
      · exact Or.inl ((hmass _ (hνJ0 J)).2 hJ).1
      · exact Or.inr (if_neg hJ))
    (fun J y hy => by
      rw [hκd J y hy]
      by_cases hJ : NzOn (R (ν + eZ J.1)) (l (ν + eZ J.1))
      · rw [if_pos hJ, smul_smul, smul_smul]
        congr 1
        have : ((Real.sqrt (dg (ν + eZ J.1)) : ℝ) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (hdJ J)).ne'
        field_simp
      · have : l (ν + eZ J.1) y = 0 := by
          by_contra hne
          exact hJ ⟨y, hy, hne⟩
        rw [if_neg hJ, this]
        simp)
    I ((hmass _ (hνJ0 I)).2 hnzI).1 w hw
  have hae := (GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hyp.1.2.2.1 k r _ _ (R ν) Wp z π u μW μN μG νq hDS hG).1
  rw [if_pos hnzI, hκI I rfl, hw1] at h8
  have h9 := h8.trans (le_trans (le_of_eq (lintegral_congr_ae ?_)) hint)
  · have hH : 0 ≤ Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ (r + 1) := by
      apply pow_nonneg
      unfold Hsq
      apply mul_nonneg (le_trans zero_le_one (le_max_left _ _))
      rw [show 20 * (r + 1) = 2 * (10 * (r + 1)) by ring, pow_mul]
      positivity
    rw [ENNReal.ofReal_le_ofReal_iff hH] at h9
    refine le_trans (le_of_eq ?_) h9
    have hep : ‖(ep I : ℂ)‖ = 1 := by
      rcases hT.ep_sq I with h | h <;> simp [h]
    rw [norm_div, norm_mul, norm_mul, hep, norm_star, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, div_pow, mul_pow, sq_abs, sq_abs, Real.sq_sqrt hd0.le, Real.sq_sqrt (hdJ I).le]
    ring
  · filter_upwards [hae] with x hx
    rw [(GlobalTheory.TensLen.lengths k r z hG.1 hG.2.1 _ hx).1, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, Real.sq_sqrt (hdJ I).le]

end GlobalTheory.WedgeKappa
end

section

noncomputable section

namespace GlobalTheory.LevelCusp.Transport

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LevelCusp
open ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity
open GlobalTheory.Dict (castFr)
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem integral_eq_zero_cast {α : Type} {Ψ Ψ' : Finset α} (h : Ψ = Ψ') {L : AddSubgroup (Ψ → ℝ)}
    {L' : AddSubgroup (Ψ' → ℝ)} [Countable L] [Countable L'] {D : Set (Ψ → ℝ)} {D' : Set (Ψ' → ℝ)}
    {g : (Ψ → ℝ) → ℂ} {g' : (Ψ' → ℝ) → ℂ} {c : ℂ}
    (hg : ∀ s, g s = c * g' (fun τ => s ⟨τ.1, h ▸ τ.2⟩))
    (hD : IsAddFundamentalDomain L D volume) (hD' : IsAddFundamentalDomain L' D' volume)
    (hf : volume D < ⊤) (hf' : volume D' < ⊤) (hp' : 0 < volume D') (hc : Continuous g)
    (hb : ∃ C : ℝ, ∀ s, ‖g s‖ ≤ C) (hL : ∀ p ∈ L, ∀ s, g (p + s) = g s)
    (hL' : ∀ p ∈ L', ∀ s, g' (p + s) = g' s) (h0 : ∫ s in D', g' s = 0) : ∫ s in D, g s = 0 := by
  subst h
  have hg' : ∀ s, g s = c * g' s := hg
  have key := GlobalTheory.mean_fundamentalDomain_eq_of_periodic Ψ L L' D D' g hD hD' hf hf' hc hb (fun p hp s => by rw [add_comm, hL p hp])
    (fun p hp s => by rw [hg', hg', add_comm, hL' p hp])
  have e : ∫ s in D', g s = 0 := by
    simp only [hg']
    rw [integral_const_mul, h0, mul_zero]
  rw [e, mul_zero] at key
  refine (mul_eq_zero.1 key.symm).resolve_left ?_
  exact_mod_cast (ENNReal.toReal_pos hp'.ne' hf'.ne).ne'

variable {X X' : Data E r} {a : GL (Fin r) E}

theorem nfac_eq (h : IsMatch X X' a) {la : Wt X.Ψ r} {la' : Wt X'.Ψ r}
    (hl : ∀ (τ : X'.Ψ) i, la' τ i = la ⟨τ.1, h.mem τ⟩ i) (x : Frame X.Ψ r) :
    X'.nfac la' (lact a (castFr h.psi x)) = X.nfac la x := by
  unfold Data.nfac
  simp only [h.dmin_eq]
  exact (GlobalTheory.Dict.Pull.cast_wt h.psi rfl hl (castFr h.psi x)).symm

theorem isIso_map (h : IsMatch X X' a) {ξ : Fin r → E} (hξ : X.IsIso ξ) :
    X'.IsIso ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) := by
  refine ⟨(h.lat ξ).1 hξ.1, by rw [h.iso, hξ.2.1], fun e => hξ.2.2 ?_⟩
  rw [← GlobalTheory.Dict.Pull.inv_mulVec a ξ, e, Matrix.mulVec_zero]

theorem map_mul_flowMat (h : IsMatch X X' a) (ξ : Fin r → E) (τ : X'.Ψ) (s : ℂ) :
    (a : Matrix (Fin r) (Fin r) E).map τ.1 * X.flowMat ξ ⟨τ.1, h.mem τ⟩ s =
      X'.flowMat ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) τ s * (a : Matrix (Fin r) (Fin r) E).map τ.1 := by
  have he : Data.emb τ.1 ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) =
      (a : Matrix (Fin r) (Fin r) E).map τ.1 *ᵥ Data.emb τ.1 ξ := by
    funext i
    simp [Data.emb, Matrix.mulVec, dotProduct]
  have hc : X'.c τ = X.c ⟨τ.1, h.mem τ⟩ := by simp only [Data.c, h.xi]
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  simp only [Matrix.toLin'_apply]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, flowMat_mulVec, flowMat_mulVec, he, h.hermC_eq, hc,
    Matrix.mulVec_add, Matrix.mulVec_smul]

theorem lact_flow (h : IsMatch X X' a) (ξ : Fin r → E) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) :
    lact a (castFr h.psi (X.flow ξ s x)) =
      X'.flow ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) (fun τ => s ⟨τ.1, h.mem τ⟩) (lact a (castFr h.psi x)) := by
  funext τ
  show (a : Matrix (Fin r) (Fin r) E).map τ.1 * (X.flowMat ξ ⟨τ.1, h.mem τ⟩ (s ⟨τ.1, h.mem τ⟩) *
      mat x ⟨τ.1, h.mem τ⟩) = X'.flowMat ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) τ (s ⟨τ.1, h.mem τ⟩) *
      ((a : Matrix (Fin r) (Fin r) E).map τ.1 * mat x ⟨τ.1, h.mem τ⟩)
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, map_mul_flowMat h]

theorem freq_zero (X : Data E r) (la : Wt X.Ψ r) :
    ∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, (0 : X.Ψ → ℝ) τ * p τ = k := fun p _ => ⟨0, by simp⟩

theorem fjI_zero (X : Data E r) (ξ : Fin r → E) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) (s : X.Ψ → ℝ) :
    fjI X ξ 0 P x s = P (X.flow ξ (cR X s) x) := by
  simp [fjI]
  rfl

theorem fj_zero_eq (X : Data E r) (la : Wt X.Ψ r) (ξ : Fin r → E) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.fj la ξ 0 P x = ((volume (ExponentialGrowthExclusion.exists_fd X la).choose).toReal : ℂ)⁻¹ *
      ∫ s in (ExponentialGrowthExclusion.exists_fd X la).choose, fjI X ξ 0 P x s := by
  rw [Data.fj, if_pos (freq_zero X la), dite_eq_left (ExponentialGrowthExclusion.exists_fd X la)]
  rfl

end GlobalTheory.LevelCusp.Transport

end

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix


open GlobalTheory.LevelCusp.Transport ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
  ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity in
theorem GlobalTheory.LevelCusp.mem_SS_of_isMatch : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (a : GL (Fin r) E) (h : IsMatch X X' a) (la : Wt X.Ψ r) (la' : Wt X'.Ψ r), (∀ (τ : X'.Ψ) i, la' τ i = la ⟨τ.1, h.mem τ⟩ i) → ∀ (P : Frame X.Ψ r → ℂ) (Q : Frame X'.Ψ r → ℂ) (c : ℂ), X.IsSec la P → Q ∈ X'.SS la' → (∀ x ∈ X.dom, P x = c * Q (lact a (castFr h.psi x))) → P ∈ X.SS la := by
  intro E _ _ _ r X X' a h la la' hl P Q c hP hQ hPQ
  obtain ⟨⟨hQs, C, hC⟩, hQ0⟩ := hQ
  have hb : ∀ x ∈ X.dom, X.pnorm la P x ≤ ‖c‖ * C := fun x hx => by
    have := hC _ (h.mem_dom hx)
    rw [BoundedSectionAlgebra.pnorm_eq, nfac_eq h hl] at this
    rw [BoundedSectionAlgebra.pnorm_eq, hPQ x hx, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
  refine ⟨⟨hP, _, hb⟩, fun ξ hξ x hx => ?_⟩
  have hξ' := isIso_map h hξ
  have hx' := h.mem_dom hx
  have h0 := hQ0 _ hξ' _ hx'
  obtain ⟨-, hD, -, hf⟩ := (ExponentialGrowthExclusion.exists_fd X la).choose_spec
  obtain ⟨-, hD', hp', hf'⟩ := (ExponentialGrowthExclusion.exists_fd X' la').choose_spec
  rw [fj_zero_eq] at h0 ⊢
  have hne : ((MeasureTheory.volume (ExponentialGrowthExclusion.exists_fd X' la').choose).toReal : ℂ)⁻¹ ≠ 0 :=
    inv_ne_zero (by exact_mod_cast (ENNReal.toReal_pos hp'.ne' hf'.ne).ne')
  have : Countable (X.periods la) := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  have : Countable (X'.periods la') := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  rw [integral_eq_zero_cast h.psi (c := c) (fun s => ?_) hD hD' hf hf' hp'
    (fjI_continuous X la P hP hξ.2.1 0 hx) ⟨‖c‖ * C / X.nfac la x, fun s => ?_⟩
    (fjI_periodic X la P hP hξ.1 hξ.2.1 0 (freq_zero X la) hx)
    (fjI_periodic X' la' Q hQs hξ'.1 hξ'.2.1 0 (freq_zero X' la') hx')
    ((mul_eq_zero.1 h0).resolve_left hne), mul_zero]
  · rw [fjI_zero, fjI_zero, hPQ _ (flow_real_mem_dom X hξ.2.1 s x hx), lact_flow h]
    rfl
  · have hT := hb _ (flow_real_mem_dom X hξ.2.1 s x hx)
    rw [BoundedSectionAlgebra.pnorm_eq, BoundedSectionAlgebra.nfac_flow_real X hξ.2.1] at hT
    rw [fjI_zero, le_div_iff₀ (BoundedSectionAlgebra.nfac_pos X hx la)]
    exact hT
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

theorem conj_entry_smul_eigenSum : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (lam : Fin (2 * r + k + 1) → ℝ) (d : ℕ) (A : ℝ) (i j : Fin (2 * r + k + 1)) (F : B.Mat k r → (Wq →L[ℂ] Wp)), (∀ s t, s ≠ t → 2 * ((d : ℕ) : ℝ) < |lam s - lam t|) → (∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * r + k + 1) → ℤ), (∀ i s, |ν i s| ≤ ((d : ℕ) : ℤ)) ∧ (∀ i, (B.CkOn ⊤ (B.GV k r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A) m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ B.GV k r, (F) g = ∑ i, Fi i g) → (∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * r + k + 1) → ℤ), (∀ i s, |ν i s| ≤ ((d + 1 : ℕ) : ℤ)) ∧ (∀ i, (B.CkOn ⊤ (B.GV k r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A - 1) m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ B.GV k r, (fun g => star (g i j) • F g) g = ∑ i, Fi i g) := by
  intro k r Wp Wq _ _ _ _ _ _ lam d A i j F hsep hF
  obtain ⟨N₀, Fi, ν, hν, hcl, heig, hsum⟩ := hF
  obtain ⟨⟨co, hco⟩, -⟩ := GlobalTheory.T.unitary_conj_entry_and_inv_entry_linear k r i j
  refine GlobalTheory.T.capelliEigenSum_linearCombination k r Wp Wq lam (d + 1) (A - 1)
    (Fin N₀ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) Finset.univ
    (fun x => co x.2.1 x.2.2) (fun x g => g⁻¹ x.2.1 x.2.2 • Fi x.1 g)
    (fun g => star (g i j) • F g) ?_ ?_
  · rintro ⟨x, a, b⟩ -
    refine ⟨d + 1, A - 1, le_rfl, le_rfl, ?_⟩
    have hinj : Function.Injective (fun s => lam s + (ν x s : ℝ)) := by
      intro s t hst
      by_contra hne
      have h1 := hsep s t hne
      have h2 : |(ν x s : ℝ)| ≤ (d : ℝ) := by exact_mod_cast hν x s
      have h3 : |(ν x t : ℝ)| ≤ (d : ℝ) := by exact_mod_cast hν x t
      have h4 : lam s - lam t = (ν x t : ℝ) - (ν x s : ℝ) := by
        simp only at hst
        linarith
      rw [h4] at h1
      have h5 := abs_sub (ν x t : ℝ) (ν x s : ℝ)
      linarith
    obtain ⟨G, hG1, hG2, hG3⟩ := GlobalTheory.T.inverseEntry_smul_capelliEigenfunction_sum k r Wp Wq (fun s => lam s + (ν x s : ℝ)) A a b
      (Fi x) hinj (hcl x) (by
        intro Y g hg
        rw [heig x Y g hg]
        simp only [add_assoc])
    refine ⟨2 * r + k + 1, G, fun t s => ν x s - if s = t then 1 else 0, ?_, hG1, ?_, hG3⟩
    · intro t s
      have h := abs_le.mp (hν x s)
      rw [abs_le]
      push_cast
      split_ifs <;> constructor <;> omega
    · intro t Y g hg
      rw [hG2 t Y g hg]
      congr 2
      refine Finset.prod_congr rfl fun s _ => ?_
      push_cast
      split_ifs <;> ring
  · intro g hg
    beta_reduce
    rw [hco g hg, hsum g hg, Fintype.sum_prod_type, Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fintype.sum_prod_type, Finset.sum_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_smul]

end GlobalTheory
end
