import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndFrFix
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet
import ReciprocityTheory.ReductiveGroups.Models.FiniteGeneration.FiniteGenerationProofs.SolveV

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2a

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.FG.SolveVAux Formalism.L2.Pj

open ReciprocityTheory.ChartRestriction.G.TB (dLin)
open ReciprocityTheory.ChartRestriction.G.TB.LogPf (logOf pderiv_logOf cc_om constantCoeff_prim)

variable {S : Type} [CommRing S]

theorem low_smul {τ : Type} {N : ℕ} (a : S) {p : MvPowerSeries τ S} (hp : Low N p) : Low N (a • p) := by
  intro e he
  rw [map_smul, hp e he, smul_zero]

theorem low_sum {τ ι : Type} {N : ℕ} (s : Finset ι) {p : ι → MvPowerSeries τ S} (hp : ∀ i ∈ s, Low N (p i)) :
    Low N (∑ i ∈ s, p i) := by
  exact Finset.sum_induction _ (Low N) (fun _ _ h1 h2 => low_add h1 h2) (fun e _ => by simp) hp

theorem low_subst' {ι τ : Type} [Finite ι] {N : ℕ} {k : ι → MvPowerSeries τ S} (hk : ∀ i, Low 1 (k i))
    {g : MvPowerSeries ι S} (hg : Low N g) : Low N (subst k g) := by
  have hk' : 1 ≤ ⨅ i, (k i).order := le_iInf fun i =>
    one_le_order_iff_constCoeff_eq_zero.2 ((low_one_iff _).1 (hk i))
  have horder : (N : ℕ∞) ≤ (subst k g).order := calc
    (N : ℕ∞) = 1 * N := by simp
    _ ≤ (⨅ i, (k i).order) * g.order := mul_le_mul' hk' (nat_le_order hg)
    _ ≤ (subst k g).order := le_order_subst (hasSubst_of_low hk) g
  intro e he
  exact coeff_of_lt_order ((Nat.cast_lt.mpr he).trans_le horder)

variable [Algebra ℚ S] {d : ℕ}

private lemma low_two_of_lemma {σ : Type} {f : MvPowerSeries σ S} (h0 : constantCoeff f = 0)
    (h1 : ∀ w, coeff (Finsupp.single w 1) f = 0) : Low 2 f := by
  intro e he
  have hd : e.degree = 0 ∨ e.degree = 1 := by omega
  rcases hd with hd | hd
  · have h := (Finsupp.degree_eq_zero_iff e).1 hd
    rw [h, coeff_zero_eq_constantCoeff_apply]
    exact h0
  · obtain ⟨w, rfl⟩ := Formalism.FG.SolveVAux.degree_eq_one e hd
    exact h1 w

theorem dLin_logOf (G : FGLaw S d) : ReciprocityTheory.ChartRestriction.G.TB.dLin (fun i => ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i) = 1 := by
  ext i j
  change coeff (Finsupp.single ((0 : Fin 1), j) 1) (logOf G i) = (1 : Matrix (Fin d) (Fin d) S) i j
  have hom := congrFun (congrFun (cc_om (G := G)) i) j
  rw [Matrix.map_apply] at hom
  calc
    _ = constantCoeff (pderiv S ((0 : Fin 1), j) (logOf G i)) := by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add]
      simp
    _ = _ := congrArg constantCoeff (pderiv_logOf G i j)
    _ = _ := hom

theorem cc_logOf (G : FGLaw S d) (i : Fin d) : constantCoeff (ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i) = 0 := by
  exact constantCoeff_prim _

theorem low_logOf (G : FGLaw S d) (i : Fin d) :
    Low 2 (ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i - X ((0 : Fin 1), i)) := by
  apply low_two_of_lemma
  · rw [map_sub, cc_logOf, constantCoeff_X, sub_zero]
  · intro w
    obtain ⟨a, j⟩ := w
    have ha : a = 0 := Subsingleton.elim a 0
    subst ha
    have h : ReciprocityTheory.ChartRestriction.G.TB.dLin (fun i => ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i) i j =
        (1 : Matrix (Fin d) (Fin d) S) i j := by
      rw [dLin_logOf G]
    change coeff (Finsupp.single ((0 : Fin 1), j) 1) (ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i) =
      (1 : Matrix (Fin d) (Fin d) S) i j at h
    rw [map_sub, coeff_X, h, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij, Finsupp.single_left_inj Nat.one_ne_zero]

theorem low_lg (G : FGLaw S d) (b : Fin 2) (i : Fin d) :
    Low 2 (CIndFrFix.lg G b i - X (b, i)) := by
  have hk : ∀ p : Fin 1 × Fin d, Low 1 (![pt S d b] p.1 p.2) := by
    intro p
    rw [low_one_iff]
    simp [pt]
  have h := low_subst' hk (low_logOf G i)
  rw [subst_sub (hasSubst_of_low hk), subst_X (hasSubst_of_low hk)] at h
  exact h

theorem log_low_order_one (G : FGLaw S d) (b : Fin 2) (i : Fin d) : Low 1 (CIndFrFix.lg G b i) := by
  have h := low_add (low_mono (by norm_num) (low_lg G b i)) ((low_one_iff (X (b, i))).2 (constantCoeff_X _))
  rwa [sub_add_cancel] at h

private lemma exp_split_lemma_4 {σ : Type} {B : MvPowerSeries σ S} (hB2 : Low 2 B) :
    Low 3 (PowerSeries.subst B (PowerSeries.exp S) - 1 - B) := by
  have hB0 : constantCoeff B = 0 := (low_one_iff _).1 (low_mono (by norm_num) hB2)
  have hB : PowerSeries.HasSubst B := PowerSeries.HasSubst.of_constantCoeff_zero hB0
  have hexp : PowerSeries.exp S = 1 + PowerSeries.X + PowerSeries.X ^ 2 *
      PowerSeries.mk (fun n => algebraMap ℚ S (1 / ((n + 2).factorial : ℚ))) := by
    ext n
    rcases n with _ | _ | n <;> simp [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X, PowerSeries.coeff_one]
  rw [hexp, ← PowerSeries.coe_substAlgHom hB, map_add, map_add, map_mul, map_pow, map_one,
    PowerSeries.coe_substAlgHom, PowerSeries.subst_X hB]
  have h4 : Low (2 + 2 + 0) (B ^ 2 * PowerSeries.subst B
      (PowerSeries.mk (fun n => algebraMap ℚ S (1 / ((n + 2).factorial : ℚ))))) := by
    rw [pow_two]
    exact low_mul (low_mul hB2 hB2) (low_zero _)
  have h3 := low_mono (by norm_num : 3 ≤ 2 + 2 + 0) h4
  convert h3 using 1
  ring


theorem psTrunc_two_twist (G : FGLaw S d) (c : Fin d → Fin d → S) :
    psTrunc 2 (CIndFrFix.expP (CIndFrFix.bilL G c)) =
      1 + ∑ i, ∑ l, MvPolynomial.C (c i l) * (MvPolynomial.X ((0 : Fin 2), i) * MvPolynomial.X ((1 : Fin 2), l)) := by
  have hB2 : Low 2 (CIndFrFix.bilL G c) := by
    unfold CIndFrFix.bilL
    exact low_sum _ (fun i _ => low_sum _ (fun l _ => low_smul _ (low_mul (log_low_order_one G 0 i) (log_low_order_one G 1 l))))
  have hBQ : Low 3 (CIndFrFix.bilL G c - ∑ i, ∑ l, c i l • (X ((0 : Fin 2), i) * X ((1 : Fin 2), l))) := by
    unfold CIndFrFix.bilL
    rw [← Finset.sum_sub_distrib]
    apply low_sum
    intro i _
    rw [← Finset.sum_sub_distrib]
    apply low_sum
    intro l _
    rw [← smul_sub]
    apply low_smul
    have key : Low 3 ((CIndFrFix.lg G (0 : Fin 2) i - X ((0 : Fin 2), i)) * CIndFrFix.lg G (1 : Fin 2) l +
        X ((0 : Fin 2), i) * (CIndFrFix.lg G (1 : Fin 2) l - X ((1 : Fin 2), l))) :=
      low_add (low_mul (low_lg G 0 i) (log_low_order_one G 1 l))
        (low_mul ((low_one_iff _).2 (constantCoeff_X _)) (low_lg G 1 l))
    convert key using 1
    ring
  have hcoe : ((1 + ∑ i, ∑ l, MvPolynomial.C (c i l) * (MvPolynomial.X ((0 : Fin 2), i) * MvPolynomial.X ((1 : Fin 2), l)) :
        MvPolynomial (Fin 2 × Fin d) S) : MvPowerSeries (Fin 2 × Fin d) S) =
      1 + ∑ i, ∑ l, c i l • (X ((0 : Fin 2), i) * X ((1 : Fin 2), l)) := by
    rw [← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_add, map_one, map_sum]
    simp only [map_sum, map_mul, MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_C,
      MvPolynomial.coe_X, MvPowerSeries.smul_eq_C_mul]
  have hdiff : Low 3 (CIndFrFix.expP (CIndFrFix.bilL G c) - ((1 + ∑ i, ∑ l, MvPolynomial.C (c i l) * (MvPolynomial.X ((0 : Fin 2), i) * MvPolynomial.X ((1 : Fin 2), l)) :
        MvPolynomial (Fin 2 × Fin d) S) : MvPowerSeries (Fin 2 × Fin d) S)) := by
    rw [hcoe]
    have h1 : Low 3 (CIndFrFix.expP (CIndFrFix.bilL G c) - 1 - CIndFrFix.bilL G c) := exp_split_lemma_4 hB2
    convert low_add h1 hBQ using 1
    ring
  have hmem : ∀ e : Fin 2 × Fin d →₀ ℕ, e ∈ degLE 2 ↔ e.degree ≤ 2 := by
    intro e
    simp only [degLE, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, h⟩
      exact h
    · intro h
      refine ⟨⟨fun i => ⟨e i, ?_⟩, ?_⟩, h⟩
      · have hle : e i ≤ e.degree := by
          show e i ≤ ∑ j ∈ e.support, e j
          by_cases hi : i ∈ e.support
          · exact Finset.single_le_sum (f := fun j => e j) (fun _ _ => Nat.zero_le _) hi
          · have h0 : e i = 0 := by simpa using hi
            rw [h0]
            exact Nat.zero_le _
        omega
      · ext i
        simp
  have hpt : ∀ (g : MvPowerSeries (Fin 2 × Fin d) S) (e : Fin 2 × Fin d →₀ ℕ),
      MvPolynomial.coeff e (psTrunc 2 g) = if e.degree ≤ 2 then coeff e g else 0 := by
    intro g e
    rw [psTrunc, MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq', Finset.sum_ite_eq]
    by_cases h : e.degree ≤ 2
    · rw [if_pos ((hmem e).2 h), if_pos h]
    · rw [if_neg (fun h' => h ((hmem e).1 h')), if_neg h]
  have hXX : ∀ (a b : Fin 2 × Fin d) (e : Fin 2 × Fin d →₀ ℕ), 2 < e.degree →
      coeff e (X a * X b : MvPowerSeries (Fin 2 × Fin d) S) = 0 := by
    intro a b e he
    rw [MvPowerSeries.X, MvPowerSeries.X, monomial_mul_monomial, coeff_monomial, if_neg]
    rintro rfl
    have hdeg : (Finsupp.single a 1 + Finsupp.single b 1 : Fin 2 × Fin d →₀ ℕ).degree = 2 := by
      show (Finsupp.single a 1 + Finsupp.single b 1 : Fin 2 × Fin d →₀ ℕ).sum (fun _ k => k) = 2
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl,
        Finsupp.sum_single_index rfl]
    omega
  ext e
  rw [hpt]
  by_cases hd : e.degree ≤ 2
  · rw [if_pos hd, ← MvPolynomial.coeff_coe]
    have h := hdiff e (by omega)
    rwa [map_sub, sub_eq_zero] at h
  · rw [if_neg hd, ← MvPolynomial.coeff_coe, hcoe, map_add, map_sum]
    have h2 : 2 < e.degree := by omega
    have hz : ∀ a b : Fin 2 × Fin d, coeff e (X a * X b : MvPowerSeries (Fin 2 × Fin d) S) = 0 :=
      fun a b => hXX a b e h2
    simp only [map_sum, map_smul, hz, smul_zero, Finset.sum_const_zero, add_zero]
    rw [coeff_one, if_neg]
    rintro rfl
    simp at hd

end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2a
