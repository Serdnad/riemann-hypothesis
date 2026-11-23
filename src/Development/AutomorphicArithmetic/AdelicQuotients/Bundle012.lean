module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.Bundle001
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.IsNormAlong
public import GroundTheory.AutomorphicForms.AffineBruhat
public import GroundTheory.GlobalFields.SemilocalAlgebras.Galois
public import Development.AutomorphicArithmetic.AdelicQuotients.NormGaloisSmulAdeleComponentAtSmulPlace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing

private lemma nrm_le {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (x : w.adicCompletion E) (h : ValuativeRel.valuation (w.adicCompletion E) x ≤ 1) : ‖x‖ ≤ 1 :=
  norm_le_one_of_mem w ((mem_valuationInteger_iff w x).1 ((Valuation.mem_integer_iff _ _).2 h))

private lemma nrm_eq {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    {x y : w.adicCompletion E}
    (h : ValuativeRel.valuation (w.adicCompletion E) x = ValuativeRel.valuation (w.adicCompletion E) y) :
    ‖x‖ = ‖y‖ := by
  have key : ∀ a b : w.adicCompletion E, b ≠ 0 →
      ValuativeRel.valuation (w.adicCompletion E) a = ValuativeRel.valuation (w.adicCompletion E) b →
      ‖a‖ ≤ ‖b‖ := by
    intro a b hb hab
    have hb' : ValuativeRel.valuation (w.adicCompletion E) b ≠ 0 := (Valuation.ne_zero_iff _).2 hb
    have h1 : ValuativeRel.valuation (w.adicCompletion E) (a / b) ≤ 1 := by
      rw [map_div₀, hab, div_self hb']
    have h2 := nrm_le w _ h1
    rw [norm_div] at h2
    exact (div_le_one (norm_pos_iff.2 hb)).1 h2
  by_cases hy : y = 0
  · subst hy
    have hx : x = 0 := (Valuation.zero_iff _).1 (by rw [h, map_zero])
    rw [hx]
  have hx : x ≠ 0 := by
    intro hx
    exact hy ((Valuation.zero_iff _).1 (by rw [← h, hx, map_zero]))
  exact le_antisymm (key x y hy h) (key y x hx h.symm)

private lemma nrm_unif {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    ‖((GLnLocal.uniformizer (w.adicCompletion E) : _) : w.adicCompletion E)‖ ≤ 1 / 2 := by
  have hlt : ValuativeRel.valuation (w.adicCompletion E)
      ((GLnLocal.uniformizer (w.adicCompletion E) : _) : w.adicCompletion E) < 1 :=
    GLnLocal.valuation_uniformizer_lt_one _
  have hne : ((GLnLocal.uniformizer (w.adicCompletion E) : _) : w.adicCompletion E) ≠ 0 :=
    GLnLocal.uniformizer_ne_zero _
  generalize ((GLnLocal.uniformizer (w.adicCompletion E) : _) : w.adicCompletion E) = x at hlt hne
  have hv : Valued.v x < 1 := by
    by_contra hge
    have hge' : 1 ≤ Valued.v x := not_lt.1 hge
    have hinv : Valued.v x⁻¹ ≤ 1 := by
      rw [map_inv₀]; exact inv_le_one_of_one_le₀ hge'
    have hm : x⁻¹ ∈ HeightOneSpectrum.adicCompletionIntegers E w :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hinv
    have h3 := (Valuation.mem_integer_iff _ _).1 ((mem_valuationInteger_iff w _).2 hm)
    rw [map_inv₀] at h3
    have h0 : ValuativeRel.valuation (w.adicCompletion E) x ≠ 0 := (Valuation.ne_zero_iff _).2 hne
    exact absurd h3 (not_le.2 ((one_lt_inv₀ (zero_lt_iff.2 h0)).2 hlt))
  have hvne : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hne
  have hN : 1 < Ideal.absNorm w.asIdeal := HeightOneSpectrum.one_lt_absNorm w
  have hN2 : (2 : ℝ) ≤ (Ideal.absNorm w.asIdeal : ℝ) := by exact_mod_cast hN
  have h1 : (1 : NNReal) < (Ideal.absNorm w.asIdeal : NNReal) := by exact_mod_cast hN
  have hlt1 : ‖x‖ < 1 := by
    rw [FinitePlace.norm_def]
    exact_mod_cast (WithZeroMulInt.toNNReal_lt_one_iff h1).2 hv
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hvne] at hlt1 ⊢
  generalize (Valued.v x).log = m at hlt1 ⊢
  have hm : m ≤ -1 := by
    by_contra hc
    have hm0 : 0 ≤ m := by omega
    have h5 : (1 : NNReal) ≤ (Ideal.absNorm w.asIdeal : NNReal) ^ m := one_le_zpow₀ h1.le hm0
    have h6 : (1 : ℝ) ≤ (((Ideal.absNorm w.asIdeal : NNReal) ^ m : NNReal) : ℝ) := by exact_mod_cast h5
    exact absurd hlt1 (not_lt.2 h6)
  have h6 : (Ideal.absNorm w.asIdeal : NNReal) ^ m ≤ (Ideal.absNorm w.asIdeal : NNReal) ^ (-1 : ℤ) :=
    zpow_le_zpow_right₀ h1.le hm
  have h7 : (((Ideal.absNorm w.asIdeal : NNReal) ^ m : NNReal) : ℝ) ≤ (Ideal.absNorm w.asIdeal : ℝ)⁻¹ := by
    have := NNReal.coe_le_coe.2 h6
    simpa using this
  refine h7.trans ?_
  rw [one_div]
  exact inv_anti₀ (by norm_num) hN2

private lemma prod_zp {n : ℕ} {K : Type} [Field K] (x : K) (hx : x ≠ 0) (e : Fin n → ℤ) (J : Finset (Fin n)) :
    ∏ i ∈ J, x ^ e i = x ^ ∑ i ∈ J, e i := by
  classical
  induction J using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hx]

private lemma fin_real (r : ℝ) (h0 : 0 < r) (h1 : r ≤ 1 / 2) (j m : ℕ) (hm : 1 ≤ m) :
    r ^ (j * m) * 2 ^ j ≤ 1 := by
  have hr1 : r ≤ 1 := by linarith
  have ha : r ^ (j * m) ≤ r ^ j := pow_le_pow_of_le_one h0.le hr1 (Nat.le_mul_of_pos_right j hm)
  have hb : r ^ j * 2 ^ j ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (by positivity) (by linarith)
  exact (mul_le_mul_of_nonneg_right ha (by positivity)).trans hb

theorem UpperTheory.norm_coeff_zero_factor_charpoly_iwahori_diagPow_le :
    A1 → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ν : Fin n → ℤ), Function.Injective ν → ∑ i, ν i = 0 →
        (∀ J : Finset (Fin n), J.Nonempty → J ≠ Finset.univ → ∑ i ∈ J, ν i ≠ 0) → ∀ j : ℕ, 0 < j →
        ∀ a ∈ GLnLocal.iwahori (w.adicCompletion E) n, ∀ b ∈ GLnLocal.iwahori (w.adicCompletion E) n,
        ∀ p₁ p₂ : (w.adicCompletion E)[X], p₁.Monic → p₂.Monic → 0 < p₁.natDegree → 0 < p₂.natDegree →
        p₁ * p₂ = ((a * Cartan.diagPow (w.adicCompletion E) n (fun i => (j : ℤ) * ν i) * b : GL (Fin n) (w.adicCompletion E)) :
          Matrix (Fin n) (Fin n) (w.adicCompletion E)).charpoly →
        ‖p₁.coeff 0‖ * 2 ^ j ≤ 1 ∨ ‖p₂.coeff 0‖ * 2 ^ j ≤ 1 := by
  intro hA E _ _ w n ν hν hsum hJ j hj a ha b hb p₁ p₂ hm₁ hm₂ hd₁ hd₂ hp
  classical
  have hϖ : ((GLnLocal.uniformizer (w.adicCompletion E) : _) : w.adicCompletion E) ≠ 0 :=
    GLnLocal.uniformizer_ne_zero _
  have hr := nrm_unif w
  have hdiag : ∀ J : Finset (Fin n), ∏ i ∈ J, ((Cartan.diagPow (w.adicCompletion E) n (fun i => (j : ℤ) * ν i) :
      GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i i =
      ((GLnLocal.uniformizer (w.adicCompletion E) : _) : w.adicCompletion E) ^ ((j : ℤ) * ∑ i ∈ J, ν i) := by
    intro J
    rw [Finset.mul_sum, ← prod_zp _ hϖ]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Cartan.coe_diagPow, Matrix.diagonal_apply_eq]
  generalize ((GLnLocal.uniformizer (w.adicCompletion E) : _) : w.adicCompletion E) = ϖ at hϖ hr hdiag
  have hr0 : 0 < ‖ϖ‖ := norm_pos_iff.2 hϖ
  have hinj : Function.Injective (fun i => (j : ℤ) * ν i) := fun x y h =>
    hν (mul_left_cancel₀ (by exact_mod_cast hj.ne') h)
  obtain ⟨J, hJc, hJv⟩ := hA (w.adicCompletion E) n _ hinj a ha b hb p₁ hm₁ ⟨p₂, hp.symm⟩
  have hcp : (p₁ * p₂).natDegree = n := by
    rw [hp, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  obtain ⟨J', hJ'c, hJ'v⟩ := hA (w.adicCompletion E) n _ hinj a ha b hb (p₁ * p₂) (hm₁.mul hm₂) (hp ▸ dvd_rfl)
  have hJ'u : J' = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hJ'c, hcp, Fintype.card_fin]
  have hdeg : p₁.natDegree + p₂.natDegree = n := by
    rw [← hm₁.natDegree_mul hm₂]; exact hcp
  have hne : J.Nonempty := Finset.card_pos.1 (by omega)
  have hnu : J ≠ Finset.univ := by
    intro h
    rw [h, Finset.card_univ, Fintype.card_fin] at hJc
    omega
  have hs := hJ J hne hnu
  have h1 : ‖p₁.coeff 0‖ = ‖ϖ‖ ^ ((j : ℤ) * ∑ i ∈ J, ν i) := by
    rw [nrm_eq w (hJv.trans (by rw [hdiag])), norm_zpow]
  have h2 : ‖p₁.coeff 0‖ * ‖p₂.coeff 0‖ = 1 := by
    rw [← norm_mul, ← mul_coeff_zero, nrm_eq w (hJ'v.trans (congrArg _ (hdiag J'))), hJ'u, hsum]
    simp
  generalize (∑ i ∈ J, ν i) = s at hs h1
  rcases lt_or_gt_of_ne hs with hlt | hgt
  · right
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ -s)
    have hs' : s = -(m : ℤ) := by omega
    have hm1 : 1 ≤ m := by omega
    have h3 : ‖p₂.coeff 0‖ = ‖ϖ‖ ^ (j * m) := by
      have h4 : ‖p₁.coeff 0‖ = (‖ϖ‖ ^ (j * m))⁻¹ := by
        rw [h1, hs', mul_neg, zpow_neg, ← Nat.cast_mul, zpow_natCast]
      rw [h4] at h2
      exact (inv_mul_eq_one₀ (pow_ne_zero _ hr0.ne')).1 h2 |>.symm
    rw [h3]
    exact fin_real _ hr0 hr j m hm1
  · left
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hgt.le
    have hm1 : 1 ≤ m := by omega
    rw [h1, hm, ← Nat.cast_mul, zpow_natCast]
    exact fin_real _ hr0 hr j m hm1
end

section

open PositivityTheory.Rg.Tf.Geo

private def piGL {W : Type} (K : W → Type) [∀ w, CommRing (K w)] (n : ℕ) (g : ∀ w, GL (Fin n) (K w)) :
    GL (Fin n) (∀ w, K w) where
  val := Matrix.of fun i j w => (g w : Matrix (Fin n) (Fin n) (K w)) i j
  inv := Matrix.of fun i j w => ((g w)⁻¹ : GL (Fin n) (K w)).val i j
  val_inv := by
    ext i j w
    have h := congrFun (congrFun (g w).mul_inv i) j
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply] at h ⊢
    rw [h]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  inv_val := by
    ext i j w
    have h := congrFun (congrFun (g w).inv_mul i) j
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply] at h ⊢
    rw [h]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

private def prGL {W : Type} (K : W → Type) [∀ w, CommRing (K w)] (n : ℕ) (w : W) :
    GL (Fin n) (∀ w, K w) →* GL (Fin n) (K w) :=
  Matrix.GeneralLinearGroup.map (Pi.evalRingHom K w)

private theorem prGL_piGL {W : Type} (K : W → Type) [∀ w, CommRing (K w)] (n : ℕ) (g : ∀ w, GL (Fin n) (K w)) (w : W) :
    prGL K n w (piGL K n g) = g w := by
  ext i j
  rfl

private theorem prGL_ext {W : Type} (K : W → Type) [∀ w, CommRing (K w)] (n : ℕ) (a b : GL (Fin n) (∀ w, K w))
    (h : ∀ w, prGL K n w a = prGL K n w b) : a = b := by
  ext i j w
  exact congrArg (fun g : GL (Fin n) (K w) => (g : Matrix (Fin n) (Fin n) (K w)) i j) (h w)

private theorem prGL_cont {W : Type} (K : W → Type) [∀ w, CommRing (K w)] [∀ w, TopologicalSpace (K w)] (n : ℕ) (w : W) :
    Continuous (prGL K n w) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (continuous_apply w).comp ((continuous_apply j).comp ((continuous_apply i).comp
      (Units.continuous_val (M := Matrix (Fin n) (Fin n) (∀ w, K w)))))
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (continuous_apply w).comp ((continuous_apply j).comp ((continuous_apply i).comp
      (Units.continuous_coe_inv (M := Matrix (Fin n) (Fin n) (∀ w, K w)))))

private theorem piGL_cont {W : Type} (K : W → Type) [∀ w, CommRing (K w)] [∀ w, TopologicalSpace (K w)] (n : ℕ) :
    Continuous (piGL K n) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_pi fun i => continuous_pi fun j => continuous_pi fun w => ?_
    exact (continuous_apply j).comp ((continuous_apply i).comp
      ((Units.continuous_val (M := Matrix (Fin n) (Fin n) (K w))).comp (continuous_apply w)))
  · refine continuous_pi fun i => continuous_pi fun j => continuous_pi fun w => ?_
    exact (continuous_apply j).comp ((continuous_apply i).comp
      ((Units.continuous_coe_inv (M := Matrix (Fin n) (Fin n) (K w))).comp (continuous_apply w)))

theorem UpperTheory.exists_compact_conj_mem_centralizer_mul_of_separable_charpoly :
    P1 → ∀ (W : Type) [Finite W] (K : W → Type) [∀ w, NontriviallyNormedField (K w)] [∀ w, LocallyCompactSpace (K w)] [∀ w, CharZero (K w)] (n : ℕ) (γ : GL (Fin n) (∀ w, K w)), (γ : Matrix (Fin n) (Fin n) (∀ w, K w)).charpoly.Separable → ∀ D : Set (GL (Fin n) (∀ w, K w)), IsCompact D → ∃ C : Set (GL (Fin n) (∀ w, K w)), IsCompact C ∧ ∀ x, x⁻¹ * γ * x ∈ D → ∃ t, t * γ = γ * t ∧ ∃ y ∈ C, x = t * y := by
  intro hP W _ K _ _ _ n γ hγ D hD
  have hsep : ∀ w, ((prGL K n w γ : GL (Fin n) (K w)) : Matrix (Fin n) (Fin n) (K w)).charpoly.Separable := by
    intro w
    have h : ((prGL K n w γ : GL (Fin n) (K w)) : Matrix (Fin n) (Fin n) (K w))
        = (γ : Matrix (Fin n) (Fin n) (∀ w, K w)).map (Pi.evalRingHom K w) := rfl
    rw [h, Matrix.charpoly_map]
    exact hγ.map
  choose C hC hCx using fun w => hP (K w) n (prGL K n w γ) (hsep w) (prGL K n w '' D) (hD.image (prGL_cont K n w))
  refine ⟨piGL K n '' Set.pi Set.univ C, (isCompact_univ_pi hC).image (piGL_cont K n), fun x hx => ?_⟩
  choose t ht y hy hxy using fun w => hCx w (prGL K n w x) ⟨_, hx, by simp only [map_mul, map_inv]⟩
  refine ⟨piGL K n t, prGL_ext K n _ _ fun w => ?_, piGL K n y, ⟨y, fun w _ => hy w, rfl⟩, prGL_ext K n _ _ fun w => ?_⟩
  · simp only [map_mul, prGL_piGL, ht w]
  · simp only [map_mul, prGL_piGL, hxy w]
end

section

open MeasureTheory NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Global GroundTheory.Global.SemiLocal
open GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped ENNReal NumberField.AdeleRing TensorProduct

private theorem finsum_norm_ne_zero {X : Type*} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X]
    (Γ : Subgroup X) [DiscreteTopology Γ] (f : X → ℂ) (hf : HasCompactSupport f) (a b δ : X) (hδ : δ ∈ Γ)
    (h : f (a * δ * b) ≠ 0) : ∑ᶠ γ : Γ, ((‖f (a * γ * b)‖ : ℝ) : ℂ) ≠ 0 := by
  have hc : IsCompact ((fun y => a⁻¹ * y * b⁻¹) '' tsupport f) := hf.isCompact.image (by fun_prop)
  have hfin : ((fun γ : Γ => (γ : X)) ⁻¹' ((fun y => a⁻¹ * y * b⁻¹) '' tsupport f)).Finite := by
    have := Γ.tendsto_coe_cofinite_of_discrete ⟨inferInstance⟩ hc.compl_mem_cocompact
    simpa [Filter.mem_map, Filter.mem_cofinite] using this
  have hs : (Function.support fun γ : Γ => ‖f (a * γ * b)‖).Finite := by
    refine hfin.subset fun γ hγ => ⟨a * γ * b, subset_tsupport _ ?_, by group⟩
    simpa using hγ
  have h1 : ∑ᶠ γ : Γ, ((‖f (a * γ * b)‖ : ℝ) : ℂ) = ((∑ᶠ γ : Γ, ‖f (a * γ * b)‖ : ℝ) : ℂ) :=
    (Complex.ofRealHom.toAddMonoidHom.map_finsum hs).symm
  rw [h1, Complex.ofReal_ne_zero]
  exact (finsum_pos (f := fun γ : Γ => ‖f (a * γ * b)‖) (fun _ => norm_nonneg _) ⟨⟨δ, hδ⟩, norm_pos_iff.2 h⟩ hs).ne'

theorem UpperTheory.exists_height_bound_of_twistedElliptic_support :
    G2 → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
        (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n → ∀ (μ : Measure (G1 E n)) [μ.IsHaarMeasure] (θ : Twist μ), IsGalTwist σ θ →
        ∀ f : CC E n, Ell σ f → ∃ R : ℝ, ∀ x : G1 E n, ∀ δ ∈ Gam E n, f (x⁻¹ * δ * θ.e x) ≠ 0 → qht x ≤ R := by
  intro h2 F E _ _ _ _ _ _ σ hσ n hn μ _ θ hθ f hf
  obtain ⟨C, c, hC⟩ := h2 F E σ hσ n hn
  have hcs : HasCompactSupport (f : G1 E n → ℂ) := f.hasCompactSupport
  obtain ⟨M, hM⟩ := GroundTheory.Automorphic.CuspidalSpectrum.exists_height_le_of_isCompact
    (hcs.isCompact.image (continuous_subtype_val (p := fun g => g ∈ normOneGL (K := E) (n := n))))
  let f' : PositivityTheory.Rg.Tf.Core.CC E n :=
    { toFun := fun g => ((‖f g‖ : ℝ) : ℂ)
      continuous_toFun := Complex.continuous_ofReal.comp (map_continuous f).norm
      hasCompactSupport' := hcs.comp_left (g := fun z : ℂ => ((‖z‖ : ℝ) : ℂ)) (by simp) }
  have hne : ∀ g, f' g ≠ 0 → f g ≠ 0 := fun g hg h0 => hg (by
    show ((‖f g‖ : ℝ) : ℂ) = 0
    simp [h0])
  refine ⟨C * (max 1 M) ^ c, fun x δ hδ hx => ?_⟩
  refine hC μ θ hθ f' (max 1 M) (le_max_left _ _) (fun g hg => ?_) (fun δ x y hy hg => hf δ x y hy (hne y hg)) x ?_
  · exact (hM _ ⟨g, subset_tsupport _ (hne g hg), rfl⟩).trans (le_max_right _ _)
  · exact finsum_norm_ne_zero (Gam E n) f hcs x⁻¹ (θ.e x) δ hδ hx
end

section

open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing

private theorem locHeight_congr {A B : Type*} [NormedField A] [NormedField B] {n : ℕ}
    (g : GL (Fin n) A) (h : GL (Fin n) B)
    (h₁ : ∀ i j, ‖(g : Matrix (Fin n) (Fin n) A) i j‖ = ‖(h : Matrix (Fin n) (Fin n) B) i j‖)
    (h₂ : ∀ i j, ‖((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) i j‖ =
      ‖((h⁻¹ : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) i j‖) :
    AutomorphicForm.locHeight g = AutomorphicForm.locHeight h :=
  le_antisymm
    (AutomorphicForm.locHeight_le (AutomorphicForm.one_le_locHeight h)
      (fun i j => (h₁ i j).le.trans (AutomorphicForm.norm_apply_le_locHeight h i j))
      (fun i j => (h₂ i j).le.trans (AutomorphicForm.norm_inv_apply_le_locHeight h i j)))
    (AutomorphicForm.locHeight_le (AutomorphicForm.one_le_locHeight g)
      (fun i j => (h₁ i j).ge.trans (AutomorphicForm.norm_apply_le_locHeight g i j))
      (fun i j => (h₂ i j).ge.trans (AutomorphicForm.norm_inv_apply_le_locHeight g i j)))

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem fin_norm (σ : E ≃ₐ[F] E) {n : ℕ} (w : HeightOneSpectrum (𝓞 E))
    (g : AdelicGLn.AdelicGL E n) (i j : Fin n) :
    ‖(finAt (σ • w) (mapGL n (galAd σ) g)).val i j‖ = ‖(finAt w g).val i j‖ :=
  (UpperTheory.norm_galois_smul_adele_component_at_smul_place F E σ ((g : Matrix (Fin n) (Fin n) 𝔸[E]) i j)).1 w

private theorem inf_norm (σ : E ≃ₐ[F] E) {n : ℕ} (w : InfinitePlace E)
    (g : AdelicGLn.AdelicGL E n) (i j : Fin n) :
    ‖(infAt (σ • w) (mapGL n (galAd σ) g)).val i j‖ = ‖(infAt w g).val i j‖ :=
  (UpperTheory.norm_galois_smul_adele_component_at_smul_place F E σ ((g : Matrix (Fin n) (Fin n) 𝔸[E]) i j)).2 w

private theorem locHeight_fin (σ : E ≃ₐ[F] E) {n : ℕ} (w : HeightOneSpectrum (𝓞 E))
    (g : AdelicGLn.AdelicGL E n) :
    AutomorphicForm.locHeight (finAt (σ • w) (mapGL n (galAd σ) g)) =
      AutomorphicForm.locHeight (finAt w g) := by
  refine locHeight_congr _ _ (fin_norm σ w g) fun i j => ?_
  rw [← finAt_inv, ← finAt_inv, ← map_inv]
  exact fin_norm σ w g⁻¹ i j

private theorem locHeight_inf (σ : E ≃ₐ[F] E) {n : ℕ} (w : InfinitePlace E)
    (g : AdelicGLn.AdelicGL E n) :
    AutomorphicForm.locHeight (infAt (σ • w) (mapGL n (galAd σ) g)) =
      AutomorphicForm.locHeight (infAt w g) := by
  refine locHeight_congr _ _ (inf_norm σ w g) fun i j => ?_
  rw [← infAt_inv, ← infAt_inv, ← map_inv]
  exact inf_norm σ w g⁻¹ i j

private theorem mult_smul (σ : E ≃ₐ[F] E) (w : InfinitePlace E) : (σ • w).mult = w.mult := by
  have h : (σ • w).IsReal ↔ w.IsReal := InfinitePlace.isReal_smul_iff
  unfold InfinitePlace.mult
  by_cases hw : w.IsReal
  · rw [if_pos (h.2 hw), if_pos hw]
  · rw [if_neg (fun h' => hw (h.1 h')), if_neg hw]

private theorem inf_prod (σ : E ≃ₐ[F] E) {n : ℕ} (g : AdelicGLn.AdelicGL E n) :
    (∏ w : InfinitePlace E, AutomorphicForm.locHeight (infAt w (mapGL n (galAd σ) g)) ^ w.mult) =
      ∏ w : InfinitePlace E, AutomorphicForm.locHeight (infAt w g) ^ w.mult := by
  refine (Equiv.prod_comp (MulAction.toPerm σ) (fun w : InfinitePlace E =>
    AutomorphicForm.locHeight (infAt w (mapGL n (galAd σ) g)) ^ w.mult)).symm.trans
    (Finset.prod_congr rfl fun w _ => ?_)
  change AutomorphicForm.locHeight (infAt (σ • w) (mapGL n (galAd σ) g)) ^ (σ • w).mult = _
  rw [locHeight_inf, mult_smul]

private theorem fin_prod (σ : E ≃ₐ[F] E) {n : ℕ} (q : HeightOneSpectrum (𝓞 F))
    (g : AdelicGLn.AdelicGL E n) :
    (∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : below F w ≠ q),
      AutomorphicForm.locHeight (finAt w (mapGL n (galAd σ) g))) =
      ∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : below F w ≠ q),
        AutomorphicForm.locHeight (finAt w g) := by
  refine (finprod_comp_equiv (MulAction.toPerm σ : Equiv.Perm (HeightOneSpectrum (𝓞 E)))
    (f := fun w : HeightOneSpectrum (𝓞 E) => ∏ᶠ (_ : below F w ≠ q),
      AutomorphicForm.locHeight (finAt w (mapGL n (galAd σ) g)))).symm.trans
    (finprod_congr fun w => ?_)
  change (∏ᶠ (_ : below F (σ • w) ≠ q),
    AutomorphicForm.locHeight (finAt (σ • w) (mapGL n (galAd σ) g))) = _
  have hb : below F (σ • w) = below F w :=
    HeightOneSpectrum.ext (Ideal.under_smul (𝓞 F) w.asIdeal σ)
  rw [locHeight_fin, hb]

end

theorem UpperTheory.heightOff_mapGL_galAd :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : ℕ) (q : HeightOneSpectrum (𝓞 F)) (g : AdelicGLn.AdelicGL E n),
        heightOff q (mapGL n (galAd σ) g : AdelicGLn.AdelicGL E n) = heightOff q g := by
  intro F E _ _ _ _ _ σ n q g
  unfold heightOff
  rw [inf_prod, fin_prod]
end

section

open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing

private theorem val_lt_iff' {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (y : w.adicCompletion E) : ValuativeRel.valuation (w.adicCompletion E) y < 1 ↔ ‖y‖ < 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [(ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))).lt_one_iff_lt_one,
    Valued.toNormedField.norm_lt_one_iff]

private theorem val_le_iff' {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (y : w.adicCompletion E) : ValuativeRel.valuation (w.adicCompletion E) y ≤ 1 ↔ ‖y‖ ≤ 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [(ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one,
    Valued.toNormedField.norm_le_one_iff]

private theorem val_eq_iff' {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (y : w.adicCompletion E) : ValuativeRel.valuation (w.adicCompletion E) y = 1 ↔ ‖y‖ = 1 := by
  rw [le_antisymm_iff, le_antisymm_iff, val_le_iff', not_iff_not.1 (by
    rw [not_le, not_le]; exact val_lt_iff' w y : ¬ (1 ≤ ValuativeRel.valuation (w.adicCompletion E) y) ↔ ¬ (1 ≤ ‖y‖))]

theorem UpperTheory.finAt_mapGL_galAd_mem_iwahori :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : ℕ) (w : HeightOneSpectrum (𝓞 E)) (g : AdelicGLn.AdelicGL E n),
        finAt w g ∈ GLnLocal.iwahori (w.adicCompletion E) n →
        finAt (σ • w) (mapGL n (galAd σ) g : AdelicGLn.AdelicGL E n) ∈ GLnLocal.iwahori ((σ • w).adicCompletion E) n := by
  intro F E _ _ _ _ _ σ n w g hg
  have key : ∀ i j, ‖finAt (σ • w) (mapGL n (galAd σ) g : AdelicGLn.AdelicGL E n) i j‖ = ‖finAt w g i j‖ :=
    fun i j => (UpperTheory.norm_galois_smul_adele_component_at_smul_place F E σ (g i j)).1 w
  obtain ⟨h1, h2, h3⟩ := (GLnLocal.mem_iwahori_iff _ n).1 hg
  refine (GLnLocal.mem_iwahori_iff _ n).2 ⟨fun i j => ?_, fun i j hij => ?_, fun i => ?_⟩
  · rw [val_le_iff', key]; exact (val_le_iff' w _).1 (h1 i j)
  · rw [val_lt_iff', key]; exact (val_lt_iff' w _).1 (h2 i j hij)
  · rw [val_eq_iff', key]; exact (val_eq_iff' w _).1 (h3 i)
end
