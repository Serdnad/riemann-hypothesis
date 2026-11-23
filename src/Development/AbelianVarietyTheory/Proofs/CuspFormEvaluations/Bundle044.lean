module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.SumFinsuppAntidiagProdPowDivMultiFactorial
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsReducedBasisIntegralPartOfLinearIndependen
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortIndependentIntegers
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HarmAMemSpanShort
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle042
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle006
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle007
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.SupDict

theorem finrank_host (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.der.finrank_E]
  simp only [Ranks.f, Ranks.n]
  ring

theorem xiR_pos (D : D7) : 0 < xiR D := by
  unfold xiR
  refine norm_pos_iff.mpr ((map_ne_zero _).mpr ?_)
  have hd : (D.host.d : D.host.E) ≠ 0 := by
    have hlt := D.host.qd_big.2
    exact_mod_cast (Nat.zero_lt_of_lt hlt).ne'
  have hs : D.host.sqd ≠ 0 := by
    intro h0
    have h2 := D.host.sqd_sq
    rw [h0] at h2
    apply hd
    have h3 : -(D.host.d : D.host.E) = 0 := by rw [← h2]; ring
    exact neg_eq_zero.mp h3
  have hn : ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ≠ 0 :=
    Nat.cast_ne_zero.mpr (fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.mp h0))
  simp only [Host.xi0, Host.sqrtMinusD]
  exact div_ne_zero (neg_ne_zero.mpr one_ne_zero) (mul_ne_zero hn hs)

theorem one_le_dE (E : Type) [Field E] [NumberField E] : 1 ≤ dE E := by
  unfold dE
  rw [← Int.cast_abs]
  exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero E)

private lemma sum_ext0_le_sum {l : ℕ} (a : Fin l → ℕ) (M : ℕ) : ∑ i : Fin M, ext0 a (i : ℕ) ≤ ∑ i, a i := by
  rw [Fin.sum_univ_eq_sum_range (fun i => ext0 a i) M]
  have h1 : ∑ i ∈ Finset.range M, ext0 a i = ∑ i ∈ (Finset.range M).filter (· < l), ext0 a i := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs with hi
    · rfl
    · simp [ext0, hi]
  have h2 : ∑ i ∈ (Finset.range M).filter (· < l), ext0 a i ≤ ∑ i ∈ Finset.range l, ext0 a i :=
    Finset.sum_le_sum_of_subset (fun i hi => by simp at hi ⊢; omega)
  have h3 : ∑ i ∈ Finset.range l, ext0 a i = ∑ i, a i := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => ext0 a i) l]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [ext0, i.isLt]
  omega

theorem record_dictionary : ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), fdeg D.host.E = D.R.f ∧ Real.log (rdE D.host.E) = lrd D ∧ 1 ≤ rdE D.host.E ∧ 1 ≤ D.R.f ∧ 1 ≤ D.R.r ∧ 0 < xiR D ∧ Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) ≤ WeightAlgebra.DF w ∧ absA w = (WeightAlgebra.DF w : ℝ) ∧ (∀ σ, GoodEmb T.Q.c σ → ∀ k τ, ((T.U j σ).X k).c τ = 2 * xiR D) ∧ lieFac (T.Q.Dw j) (xiR D) (wtA w) = Real.exp (-(((Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℕ) : ℝ) / 2) * Real.log (Real.pi * (2 * xiR D))) ∧ T.Q.l.A = 1 ∧ 0 < D.host.pde ∧ 0 < D.host.pde' ∧ ∀ (ι : Type) (σ : T.Q.c.F →+* ℂ) (P : MvPolynomial ι T.Q.c.F), l1At (goodOf T.Q.c σ) P = l1At σ P := by
  intro D T h j hj w
  have hfin := finrank_host D
  have hdpos : 0 < dE D.host.E := lt_of_lt_of_le one_pos (one_le_dE _)
  refine ⟨?_, ?_, ?_, ?_, ?_, xiR_pos D, ?_, ?_, ?_, ?_, ?_, D.host.pde_prime.pos, D.host.pde'_prime.pos, ?_⟩
  · unfold fdeg
    rw [hfin]
    omega
  · rw [rdE, Real.log_rpow hdpos, hfin, lrd, dE]
    push_cast
    ring
  · unfold rdE
    exact Real.one_le_rpow (one_le_dE _) (by positivity)
  · have h1 := D.R.two_le_m
    have h2 := D.R.m_le_f
    simp only [Ranks.f, Ranks.n]
    omega
  · have h1 := D.R.two_le_m
    simp only [Ranks.r]
    omega
  · unfold wtA Formalism.L2.Pj.DF WeightAlgebra.DF WeightAlgebra.degP
    simp only [Finset.sum_add_distrib]
    apply add_le_add
    · rw [Finset.sum_congr rfl (fun τ _ => Finset.sum_comm), Finset.sum_comm]
      refine Finset.sum_le_sum (fun t _ => ?_)
      rw [Finset.sum_eq_single (DV.tauEmb D t)]
      · simp only [↓reduceIte]
        exact sum_ext0_le_sum _ _
      · intro τ _ hτ
        simp [hτ]
      · intro hn
        exact absurd (Finset.mem_univ _) hn
    · rw [Finset.sum_congr rfl (fun τ _ => Finset.sum_comm), Finset.sum_comm]
      refine Finset.sum_le_sum (fun t _ => ?_)
      rw [Finset.sum_eq_single (conjEmb (DV.tauEmb D t))]
      · simp only [↓reduceIte]
        exact sum_ext0_le_sum _ _
      · intro τ _ hτ
        simp [hτ]
      · intro hn
        exact absurd (Finset.mem_univ _) hn
  · unfold absA WeightAlgebra.DF WeightAlgebra.degP
    push_cast
    rfl
  · intro σ hσ k τ
    unfold Data.c
    rw [h.xiAbs j hj σ hσ k τ.1]
  · unfold lieFac Formalism.L2.Pj.DF
    rw [show (2 : ℝ) * Real.pi * xiR D = Real.pi * (2 * xiR D) by ring]
    push_cast
    rfl
  · obtain ⟨-, hl, -, -⟩ := h.pins
    unfold Par.PinLevel at hl
    exact hl.2
  · intro ι σ P
    unfold l1At goodOf
    split_ifs with hg
    · rfl
    · simp only [RingHom.comp_apply, Complex.norm_conj]

end GlobalTheory.SupDict
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.RunIn

namespace GlobalTheory.HarmBasis

open MvPolynomial

theorem mem_HHa_of_mem_span {T : Type} {r : T → ℕ} {n : ℕ} {k : Type} [Field k] {cc : T → T} {isX : T → Prop}
    {a : T → ℕ → ℕ} {S : Set (MvPolynomial (Letter T r n) k)} (hS : S ⊆ HHa r n k cc isX a)
    {P : MvPolynomial (Letter T r n) k} (hP : P ∈ Submodule.span k S) : P ∈ HHa r n k cc isX a := by
  classical
  induction hP using Submodule.span_induction with
  | mem y hy => exact hS hy
  | zero => exact ⟨zero_mem _, fun _ _ _ _ _ => map_zero _, fun m hm => by simp at hm⟩
  | add y z _ _ hy hz =>
    refine ⟨add_mem hy.1 hz.1, fun σ i i' h t => ?_, fun m hm => ?_⟩
    · rw [map_add (f := _), hy.2.1 σ i i' h t, hz.2.1 σ i i' h t]
    · rcases Finset.mem_union.1 (support_add hm) with h | h
      exacts [hy.2.2 m h, hz.2.2 m h]
  | smul q y _ hy =>
    refine ⟨Submodule.smul_mem _ _ hy.1, fun σ i i' h t => ?_, fun m hm => hy.2.2 m (support_smul hm)⟩
    rw [map_smul, hy.2.1 σ i i' h t]

theorem totalDegree_le_of_rowDeg {T : Type} [Fintype T] {r : T → ℕ} {n : ℕ} {k : Type} [Field k]
    {a : T → ℕ → ℕ} {P : MvPolynomial (Letter T r n) k} (hP : RowDeg r n k a P) :
    P.totalDegree ≤ ∑ σ, ∑ i : Fin (r σ), a σ i := by
  classical
  refine Finset.sup_le fun m hm => le_of_eq ?_
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => hP m hm σ i

theorem l1At_eq_l1Norm_map {K ι : Type} [Field K] (σ : K →+* ℂ) (P : MvPolynomial ι K) :
    l1At σ P = MvPoly.l1Norm (map σ P) := by
  rw [MvPoly.l1Norm_eq_sum_of_subset (support_map_subset σ P), l1At]
  simp only [coeff_map]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem mult_add_mult_conjugate (Dw : Datum H) (τ : E →+* ℂ) :
    Dw.mult τ + Dw.mult (ComplexEmbedding.conjugate τ) = Dw.p + Dw.q := by
  have h2 := H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hne : H.rt0 ≠ -H.rt0 := fun h => by
    have h0 : H.rt0 = 0 := by linear_combination h / 2
    rw [h0] at h2
    have : (H.d : ℂ) = 0 := by simpa using h2.symm
    exact H.d_prime.ne_zero (by exact_mod_cast this)
  have hc : starRingEnd ℂ H.rt0 = -H.rt0 := by
    have him := congrArg Complex.im h2
    have hre := congrArg Complex.re h2
    simp [pow_two] at him hre
    have h0 : H.rt0.re = 0 := by
      by_contra hne
      have : H.rt0.im = 0 := by
        have : H.rt0.re * H.rt0.im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hne
      rw [this] at hre
      nlinarith [mul_self_nonneg H.rt0.re]
    apply Complex.ext <;> simp [h0]
  have hs : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
    have h := congrArg (fun a : 𝓞 E => τ (a : E)) H.rt_sq
    rw [H.sqrt_neg_disc_sq]
    simpa using h
  simp only [Datum.mult, ComplexEmbedding.conjugate_coe_eq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hs with h | h
  · rw [if_pos h, if_neg (by rw [h, hc]; exact hne.symm)]
  · rw [if_neg (by rw [h]; exact hne.symm), if_pos (by rw [h, map_neg, hc, neg_neg]), add_comm]

theorem card_LtN (Dw : Datum H) (n : ℕ) :
    Fintype.card (LtN Dw n) = FD.fdeg E * (Dw.p + Dw.q) * n := by
  have h1 := (ComplexEmbedding.involutive_conjugate E).bijective.sum_comp Dw.mult
  have h2 : ∑ τ, (Dw.mult τ + Dw.mult (ComplexEmbedding.conjugate τ)) =
      Module.finrank ℚ E * (Dw.p + Dw.q) := by
    simp only [mult_add_mult_conjugate]
    rw [Finset.sum_const, Finset.card_univ, Embeddings.card E ℂ, smul_eq_mul]
  rw [Finset.sum_add_distrib, h1] at h2
  have h3 : Module.finrank ℚ E = 2 * FD.fdeg E := by
    rw [FD.fdeg, IsTotallyComplex.finrank E]
    omega
  have h4 : ∑ τ, Dw.mult τ = FD.fdeg E * (Dw.p + Dw.q) := by
    rw [h3, mul_assoc] at h2
    omega
  rw [Fintype.card_sigma, ← h4, Finset.sum_mul]
  simp only [Fintype.card_prod, Fintype.card_fin]

theorem bound_le_exp {R d D N : ℕ} {L x Δ : ℝ} (hR : 1 ≤ R) (hd : 1 ≤ d) (hΔ : 0 < Δ)
    (hle : R ≤ d * (1 + D) ^ N) (hL : Real.log (1 + D) ≤ 2 * L) :
    (1 + D : ℝ) ^ ((N : ℝ) / 2) * (√((R + 3) / 4) * √d * ((d : ℝ) ^ 3 * Δ ^ (1 / (d : ℝ))) * Real.exp x) ≤
      Real.exp (x + 2 * N * L + 4 * Real.log d + Real.log Δ / d) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : (1 + D : ℝ) ^ ((N : ℝ) / 2) ≤ Real.exp (N * L) := by
    rw [Real.rpow_def_of_pos (by positivity)]
    refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_right hL (by positivity : (0 : ℝ) ≤ (N : ℝ) / 2)
    linarith
  have h2 : √((R + 3) / 4) ≤ √d * Real.exp (N * L) := by
    have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
    have hle' : (R : ℝ) ≤ d * (1 + D) ^ N := by exact_mod_cast hle
    refine (Real.sqrt_le_sqrt (show ((R : ℝ) + 3) / 4 ≤ d * (1 + D) ^ N by linarith)).trans ?_
    rw [Real.sqrt_mul hd0.le]
    refine mul_le_mul_of_nonneg_left (le_trans (le_of_eq ?_) h1) (Real.sqrt_nonneg _)
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    ring
  have h3 : Real.exp (4 * Real.log d) = √d * √d * (d : ℝ) ^ 3 := by
    rw [Real.mul_self_sqrt hd0.le, show (4 : ℝ) = (4 : ℕ) by norm_num, Real.exp_nat_mul, Real.exp_log hd0]
    ring
  have h4 : Real.exp (Real.log Δ / d) = Δ ^ (1 / (d : ℝ)) := by
    rw [Real.rpow_def_of_pos hΔ, mul_one_div]
  rw [Real.exp_add, Real.exp_add, Real.exp_add, h3, h4,
    show 2 * (N : ℝ) * L = N * L + N * L by ring, Real.exp_add]
  calc _ ≤ Real.exp (N * L) * (√d * Real.exp (N * L) * √d * ((d : ℝ) ^ 3 * Δ ^ (1 / (d : ℝ))) * Real.exp x) := by
        gcongr
    _ = _ := by ring

theorem exists_reduced_basis_harmA : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (n : ℕ), Dw.p + Dw.q ≤ n → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (L : ℝ), 2 ≤ L → Real.log (FD.rdE E) ≤ 2 * L → Real.log (FD.fdeg E) ≤ 2 * L → Real.log (1 + DF Dw a) ≤ 2 * L → Real.log n ≤ L → ∃ (R : ℕ) (b : Fin R → MvPolynomial (LtN Dw n) c.F), (∀ i, b i ∈ harmA (Dw := Dw) c a n) ∧ (∀ P ∈ harmA (Dw := Dw) c a n, ∃ z : Fin R → ℤ, P = ∑ i, (z i : c.F) • b i) ∧ R ≤ Module.finrank ℚ c.F * (1 + DF Dw a) ^ (FD.fdeg E * (Dw.p + Dw.q) * n) ∧ ∀ i (σ : c.F →+* ℂ), l1At σ (b i) ≤ Real.exp (140 * (Dw.p + Dw.q : ℕ) * L * DF Dw a + 2 * FD.fdeg E * (Dw.p + Dw.q : ℕ) * n * L + 4 * Real.log (Module.finrank ℚ c.F) + Real.log |((NumberField.discr c.F : ℤ) : ℝ)| / Module.finrank ℚ c.F) := by
  intro E _ _ _ H Dw l c n hn a L hL h1 h2 h3 h4
  classical
  have hsp := (GlobalTheory.StdHarm.harmA_mem_span_short E H Dw l c n).2 hn a L hL h1 h2 h3 h4
  set x : ℝ := 140 * (Dw.p + Dw.q : ℕ) * L * DF Dw a with hx
  set S : Set (MvPolynomial (LtN Dw n) c.F) := {Q | Q ∈ harmA c a n ∧
    ∀ σ' : c.F →+* ℂ, Real.log (∑ m ∈ Q.support, ‖σ' (Q.coeff m)‖) ≤ x} with hS
  have hW : ∀ P ∈ Submodule.span c.F S, P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H)
      fun τ i => a (τ, i) := fun P hP => mem_HHa_of_mem_span (S := S) (fun Q hQ => hQ.1.1) hP
  have hI : ∀ P, P ∈ MvPoly.integralPart (Submodule.span c.F S) ↔ P ∈ harmA (Dw := Dw) c a n := fun P =>
    ⟨fun h => ⟨hW P h.1, h.2⟩, fun h => ⟨hsp P h, h.2⟩⟩
  obtain ⟨ω, hω, hA⟩ := GlobalTheory.exists_short_independent_integers c.F
  obtain ⟨hR, b, -, hb, -⟩ := MvPoly.exists_reduced_basis_integralPart (Submodule.span c.F S) (D := DF Dw a)
    (fun P hP => totalDegree_le_of_rowDeg (hW P hP).2.2) S (fun P hP => (hI P).2 hP.1) rfl
    (B := Real.exp x) (fun P hP s => by
      rw [← l1At_eq_l1Norm_map]
      exact Real.le_exp_of_log_le (hP.2 s))
    ω (hω.span_eq_top_of_card_eq_finrank' (Fintype.card_fin _)) hA rfl
  rw [card_LtN] at hR hb
  refine ⟨_, fun i => b i, fun i => (hI _).1 (b i).2, fun P hP => ?_, hR, fun i σ => ?_⟩
  · refine ⟨b.repr ⟨P, (hI P).2 hP⟩, ?_⟩
    have h := congrArg Subtype.val (b.sum_repr ⟨P, (hI P).2 hP⟩)
    simp only [Int.cast_smul_eq_zsmul]
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h
    exact h.symm
  · rw [l1At_eq_l1Norm_map]
    refine (hb i σ).trans ((bound_le_exp (L := L) i.pos Module.finrank_pos
      (abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero c.F)) hR h3).trans (le_of_eq ?_))
    congr 1
    push_cast
    ring

end GlobalTheory.HarmBasis
end

section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GalTw

theorem _root_.GlobalTheory.T.level_fourier_transform_aut_and_homogeneous : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ), (∀ ta : c.F ≃+* c.F, (∃ a a' : ℕ, ta (zetaM c) = zetaM c ^ a ∧ a * a' ≡ 1 [MOD l.M]) ∧ ∀ a a' : ℕ, ta (zetaM c) = zetaM c ^ a → a * a' ≡ 1 [MOD l.M] → ∀ (φ : (Fin n → LevQc Dw l) → c.F) (q : Fin n → LevQ Dw l), ta (phiHat c φ q) = phiHat c (fun x => ta (φ (a' • x))) q) ∧ (∀ (u : c.F) (φ : (Fin n → LevQc Dw l) → c.F) q, phiHat c (fun x => u * φ x) q = u * phiHat c φ q) ∧ ∀ (nab : NabV Xo c) (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (b u : c.F) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S), ShortValAt Xo c nab w Λ b N P y v → ShortValAt Xo c nab (fun q => u * w q) Λ b N P y (algebraMap c.F S u * v) := by
  first | exact @GlobalTheory.GalTw.phiHat_aut_and_mul | exact GlobalTheory.GalTw.phiHat_aut_and_mul | (intros; apply GlobalTheory.GalTw.phiHat_aut_and_mul <;> assumption)
end
