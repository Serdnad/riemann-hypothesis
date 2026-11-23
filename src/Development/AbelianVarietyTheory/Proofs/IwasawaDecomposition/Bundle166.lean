module

public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle004
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsGoodFamily
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle040
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Taylor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle158
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2.JetEx
open scoped ContDiff

namespace GlobalTheory.Mem.JetChain

variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem eq_sum_coordX (z : VCx ι a b) : z = ∑ k : DVar ι a b, z k.1 k.2.1 k.2.2 • coordX k := by
  classical
  funext τ i j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (τ, i, j)]
  · simp [coordX]
  · rintro ⟨τ', i', j'⟩ _ h
    have : ¬ (τ = τ' ∧ i = i' ∧ j = j') := by
      rintro ⟨rfl, rfl, rfl⟩
      exact h rfl
    simp [coordX, this]
  · simp

theorem exists_derivAt0 (G : VCx ι a b → ℂ) (hG : ∀ k : ℕ, ContDiff ℂ k G) {n : ℕ} (f : Fin n → DVar ι a b) :
    ∃ e : DVar ι a b →₀ ℕ, e.degree = n ∧ iteratedFDeriv ℂ n G 0 (fun i => coordX (f i)) = derivAt0 G e := by
  classical
  have hG' : ContDiff ℂ ∞ G := contDiff_infty.2 hG
  set e : DVar ι a b →₀ ℕ := Multiset.toFinsupp (↑(List.ofFn f) : Multiset (DVar ι a b)) with he
  have hm : Finsupp.toMultiset e = (↑(List.ofFn f) : Multiset (DVar ι a b)) := by
    rw [he, Multiset.toFinsupp_toMultiset]
  have hc : (Finsupp.toMultiset e).card = n := by rw [hm]; simp
  refine ⟨e, ?_, ?_⟩
  · rw [← hc, Finsupp.card_toMultiset]; rfl
  have p : ((List.ofFn f).map coordX).Perm ((Finsupp.toMultiset e).toList.map coordX) := by
    refine List.Perm.map _ ?_
    rw [← Multiset.coe_eq_coe, Multiset.coe_toList, hm]
  have h2 := ReciprocityTheory.ChartRestriction.G.PullbackSections.cml_perm p n (iteratedFDeriv ℂ _ G 0)
    (fun v σ => ReciprocityTheory.L2DbarEstimates.Y.zd_iteratedFDeriv_comp_perm isOpen_univ hG'.contDiffOn _ 0 trivial σ v)
    (by simp) (by simp [hc])
  have h3 : ∀ (n n' : ℕ) (h : n = n') (v : Fin n → VCx ι a b) (w : Fin n' → VCx ι a b), (∀ i, v i = w (i.cast h)) →
      iteratedFDeriv ℂ n G 0 v = iteratedFDeriv ℂ n' G 0 w := by
    intro n n' h v w hvw
    subst h
    exact congrArg _ (funext hvw)
  unfold derivAt0
  refine Eq.trans (congrArg _ (funext fun i => ?_)) (h2.trans (h3 _ _ hc.symm _ _ fun i => ?_))
  · simp
  · simp

theorem derivAt0_comp_mem : ∀ (ι : Type) [Fintype ι] (a b n : ℕ) (K₀ : Subfield ℂ) (G : VCx ι a b → ℂ) (L : VCx ι a b →ₗ[ℂ] VCx ι a b) (κ : ℂ), (∀ k : ℕ, ContDiff ℂ k G) → (∀ k τ i j, L (coordX k) τ i j ∈ K₀) → (∀ e : DVar ι a b →₀ ℕ, e.degree = n → κ * derivAt0 G e ∈ K₀) → ∀ e : DVar ι a b →₀ ℕ, e.degree = n → κ * derivAt0 (fun z => G (L z)) e ∈ K₀ := by
  intro ι _ a b n K₀ G L κ hG hL hK e he
  classical
  have hc : (Finsupp.toMultiset e).card = n := by
    rw [← he, Finsupp.card_toMultiset]; rfl
  subst hc
  let T : VCx ι a b →L[ℂ] VCx ι a b := LinearMap.toContinuousLinearMap L
  have h1 : (fun z => G (L z)) = G ∘ T := rfl
  have key : ∀ g : Fin (Finsupp.toMultiset e).card → DVar ι a b,
      κ * iteratedFDeriv ℂ _ G 0 (fun i => L (coordX (g i))) ∈ K₀ := by
    intro g
    have h2 : (fun i => L (coordX (g i))) =
        fun i => ∑ k : DVar ι a b, L (coordX (g i)) k.1 k.2.1 k.2.2 • coordX k :=
      funext fun i => eq_sum_coordX _

    rw [h2, ContinuousMultilinearMap.map_sum, Finset.mul_sum]
    refine sum_mem fun f _ => ?_
    rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul, mul_left_comm]
    refine mul_mem (prod_mem fun i _ => hL _ _ _ _) ?_
    obtain ⟨e', he', h⟩ := exists_derivAt0 G hG f
    rw [h]
    exact hK e' he'
  unfold derivAt0
  rw [h1, T.iteratedFDeriv_comp_right (hG _) 0 le_rfl, map_zero, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  exact key _

end GlobalTheory.Mem.JetChain
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Filter Topology

namespace GlobalTheory.HalfIntChars

theorem emb_mul_indep {L I : Type} [Field L] [CharZero L] [Fintype I] (σ : I → L →+* ℂ) (hσ : Function.Injective σ)
    (m : I → ℤ) (h : ∀ k : L, k ≠ 0 → ∏ i, σ i k ^ m i = 1) : m = 0 := by
  classical
  have key : ∀ x : L, ∑ i, (m i : ℂ) * σ i x = 0 := by
    intro x
    let f : ℂ → ℂ := fun t => ∏ i, (1 + t * σ i x) ^ m i
    have hd : ∀ i ∈ (Finset.univ : Finset I),
        HasDerivAt (fun t : ℂ => (1 + t * σ i x) ^ m i) ((m i : ℂ) * σ i x) 0 := by
      intro i _
      have h1 : HasDerivAt (fun t : ℂ => 1 + t * σ i x) (σ i x) 0 := by
        simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (σ i x)).const_add 1
      have h2 := (hasDerivAt_zpow (m i) ((fun t : ℂ => 1 + t * σ i x) 0) (Or.inl (by simp))).comp (0 : ℂ) h1
      simpa [Function.comp_def] using h2
    have hf : HasDerivAt f (∑ i, (m i : ℂ) * σ i x) 0 := by
      have := HasDerivAt.fun_finsetProd hd
      simpa [f] using this
    have hs := hasDerivAt_iff_tendsto_slope.1 hf
    have hu : Tendsto (fun n : ℕ => ((1 : ℂ) / ((n : ℂ) + 1))) atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ), Eventually.of_forall fun n => ?_⟩
      exact one_div_ne_zero (Nat.cast_add_one_ne_zero n)
    have hfin : ∀ᶠ n : ℕ in atTop, (1 + (1 / ((n : L) + 1)) * x) ≠ 0 := by
      rw [← Nat.cofinite_eq_atTop]
      refine Set.Subsingleton.finite ?_
      intro a ha b hb
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at ha hb
      have ha1 : ((a : L) + 1) ≠ 0 := Nat.cast_add_one_ne_zero a
      have hb1 : ((b : L) + 1) ≠ 0 := Nat.cast_add_one_ne_zero b
      field_simp at ha hb
      have : (a : L) = b := by linear_combination ha - hb
      exact_mod_cast this
    have h0 : Tendsto (fun n : ℕ => slope f 0 ((1 : ℂ) / ((n : ℂ) + 1))) atTop (𝓝 0) := by
      refine tendsto_const_nhds.congr' (hfin.mono fun n hn => ?_)
      have h1 := h _ hn
      have h2 : f ((1 : ℂ) / ((n : ℂ) + 1)) = 1 := by
        refine Eq.trans ?_ h1; simp [f]
      have h3 : f 0 = 1 := by simp [f]
      simp only [slope, h2, h3, vsub_self, smul_zero]
    exact tendsto_nhds_unique (hs.comp hu) h0
  have li := (linearIndependent_monoidHom L ℂ).comp (fun i => (σ i : L →* ℂ))
    (fun i j hij => hσ (RingHom.coe_monoidHom_injective hij))
  have := Fintype.linearIndependent_iff.1 li (fun i => (m i : ℂ)) (by
    funext x
    simpa [Finset.sum_apply] using key x)
  funext i
  exact_mod_cast this i

theorem unit_sq (z : ℂ) (hz : z ≠ 0) : (z / ((‖z‖ : ℝ) : ℂ)) ^ 2 = z / starRingEnd ℂ z := by
  have h1 : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz
  have h2 : starRingEnd ℂ z ≠ 0 := by simpa using hz
  have h3 : z * starRingEnd ℂ z = ((‖z‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  field_simp
  rw [← h3]

theorem hasInf_unique {L I : Type} [Field L] [NumberField L] [Fintype I] (φ : I → L →+* ℂ) (h1 : Function.Injective φ)
    (h2 : ∀ i j, φ i ≠ (starRingEnd ℂ).comp (φ j)) {χ : HChar L} {n n' : I → ℤ} (h : χ.HasInf φ n) (h' : χ.HasInf φ n') :
    n = n' := by
  let σ : I ⊕ I → L →+* ℂ := Sum.elim φ fun i => (starRingEnd ℂ).comp (φ i)
  have hσ : Function.Injective σ := by
    rintro (i | i) (j | j) hij
    · exact congrArg _ (h1 hij)
    · exact absurd hij (h2 i j)
    · exact absurd hij.symm (h2 j i)
    · refine congrArg _ (h1 (RingHom.ext fun x => ?_))
      have := congrArg (fun f : L →+* ℂ => starRingEnd ℂ (f x)) hij
      simpa [σ] using this
  have := emb_mul_indep σ hσ (Sum.elim (n - n') (n' - n)) (fun k hk => by
    have e := (h (Units.mk0 k hk)).symm.trans (h' (Units.mk0 k hk))
    simp only [Units.val_mk0] at e
    have hne : ∀ i, φ i k ≠ 0 := fun i => by simpa using hk
    have hu : ∀ i, φ i k / ((‖φ i k‖ : ℝ) : ℂ) ≠ 0 := fun i =>
      div_ne_zero (hne i) (by exact_mod_cast norm_ne_zero_iff.2 (hne i))
    have e2 : ∏ i, (φ i k / ((‖φ i k‖ : ℝ) : ℂ)) ^ (n i - n' i) = 1 := by
      simp_rw [zpow_sub₀ (hu _)]
      rw [Finset.prod_div_distrib, e, div_self]
      exact Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (hu i)
    have e3 := congrArg (· ^ 2) e2
    simp only [← Finset.prod_pow, one_pow] at e3
    rw [Fintype.prod_sum_type, ← Finset.prod_mul_distrib, ← e3]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm (n i - n' i), zpow_mul, zpow_natCast, unit_sq _ (hne i), div_zpow]
    simp only [σ, Sum.elim_inl, Sum.elim_inr, Pi.sub_apply, RingHom.comp_apply]
    rw [div_eq_mul_inv, ← zpow_neg, neg_sub])
  funext i
  have := congrFun this (Sum.inl i)
  simpa [sub_eq_zero] using this

theorem hasInfQ_inv {L I : Type} [Field L] [NumberField L] [Fintype I] {φ : I → L →+* ℂ} {χ : HChar L} {a : I → ℚ}
    (h : χ.HasInfQ φ a) : (χ⁻¹).HasInfQ φ (-a) := by
  obtain ⟨n, hn, h⟩ := h
  refine ⟨-n, fun i => by simp [hn], fun k => ?_⟩
  rw [_root_.Formalism.L2.Host.HChar.inf_inv, Units.val_inv_eq_inv_val, h k, ← Finset.prod_inv_distrib]
  simp

theorem embPsi_inj {R : Ranks} (H : Formalism.BasicNotions.Host R) : Function.Injective (_root_.Formalism.L2.Host.embPsi H) := fun _ _ h =>
  Subtype.ext ((factEmb R H).1.1 h)

theorem embPsi_ne_conj {R : Ranks} (H : Formalism.BasicNotions.Host R) (i j : R.Psi) :
    _root_.Formalism.L2.Host.embPsi H i ≠ (starRingEnd ℂ).comp (_root_.Formalism.L2.Host.embPsi H j) := by
  intro h
  have hi : _root_.Formalism.L2.Host.embPsi H i (H.sqd) = Complex.I * ((Real.sqrt H.d : ℝ) : ℂ) :=
    ((factEmb R H).2 _).2 i.2
  have hj : _root_.Formalism.L2.Host.embPsi H j (H.sqd) = Complex.I * ((Real.sqrt H.d : ℝ) : ℂ) :=
    ((factEmb R H).2 _).2 j.2
  rw [h, RingHom.comp_apply, hj, map_mul, Complex.conj_I, Complex.conj_ofReal] at hi
  have h0 : ((Real.sqrt H.d : ℝ) : ℂ) = 0 := by
    have : (2 * Complex.I) * ((Real.sqrt H.d : ℝ) : ℂ) = 0 := by linear_combination -hi
    exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero two_ne_zero Complex.I_ne_zero)
  have hd : 0 < H.d := H.hyp.2.1.pos
  have : (0 : ℝ) < Real.sqrt H.d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  exact this.ne' (by exact_mod_cast h0)


end GlobalTheory.HalfIntChars
end
end

section

noncomputable section

open Matrix Formalism.MainNotions.S

namespace GlobalTheory.CoefSpace.Conj

variable {k : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)}

theorem ujset_eq (k : ℕ) : UJset (allPos k) = (Matrix.unitaryGroup (Fin k) ℂ : Set _) :=
  GlobalTheory.RealPar.ujset_const true

theorem kset_eq (k : ℕ) : Formalism.REAL.Kset (allPos k) = (Matrix.unitaryGroup (Fin k) ℂ : Set _) :=
  (GlobalTheory.DefiniteCheck.kset_const k true).trans (ujset_eq k)

theorem conj_mem {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ Matrix.unitaryGroup (Fin k) ℂ) :
    g.map star ∈ Matrix.unitaryGroup (Fin k) ℂ :=
  Matrix.transpose_mem_unitaryGroup_iff.2 (Unitary.star_mem hg)

def tor (θ : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℂ := Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)

theorem tor_conj (θ : Fin k → ℝ) : (tor θ).map star = tor (-θ) := by
  rw [tor, Matrix.diagonal_map (star_zero ℂ)]
  congr 1
  funext a
  simp [← Complex.exp_conj]

theorem tor_mem (θ : Fin k → ℝ) : tor θ ∈ Matrix.unitaryGroup (Fin k) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, tor, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  simp [← Complex.exp_conj, ← Complex.exp_add]

theorem wt_iff (μ : Fin k → ℝ) (v : H) : IsWtOn (Formalism.REAL.Kset (allPos k)) π μ v ↔
    ∀ θ, π (tor θ) v = Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • v :=
  ⟨fun h θ => h θ (by rw [kset_eq]; exact tor_mem θ), fun h θ _ => h θ⟩

theorem wt_conj {μ : Fin k → ℝ} {v : H} :
    IsWtOn (Formalism.REAL.Kset (allPos k)) (fun g => π (g.map star)) μ v ↔ IsWtOn (Formalism.REAL.Kset (allPos k)) π (-μ) v := by
  simp only [wt_iff, tor_conj]
  refine ⟨fun h θ => ?_, fun h θ => ?_⟩
  · simpa using h (-θ)
  · simpa using h (-θ)

def revM (k : ℕ) : Matrix (Fin k) (Fin k) ℂ := (1 : Matrix (Fin k) (Fin k) ℂ).submatrix Fin.revPerm id

theorem revM_mem : revM k ∈ Matrix.unitaryGroup (Fin k) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, revM, Matrix.conjTranspose_submatrix,
    Matrix.conjTranspose_one, Matrix.submatrix_mul_equiv, Matrix.mul_one, Matrix.submatrix_id_id]

theorem tor_revM (θ : Fin k → ℝ) : tor θ * revM k = revM k * tor fun a => θ (Fin.rev a) := by
  ext a b
  simp only [tor, revM, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.submatrix_apply, Fin.revPerm_apply, id,
    Matrix.one_apply]
  split_ifs with h
  · subst h
    simp
  · simp

theorem wt_rev (hπ : IsURepOn (UJset (allPos k)) π) {μ : Fin k → ℝ} {v : H} (hv0 : v ≠ 0)
    (hv : IsWtOn (Formalism.REAL.Kset (allPos k)) π μ v) :
    π (revM k) v ≠ 0 ∧ IsWtOn (Formalism.REAL.Kset (allPos k)) π (fun a => μ (Fin.rev a)) (π (revM k) v) := by
  rw [ujset_eq] at hπ
  refine ⟨fun h => hv0 ?_, (wt_iff _ _).2 fun θ => ?_⟩
  · rw [← norm_eq_zero, ← hπ.2.1 _ revM_mem v, h, norm_zero]
  · have e : ∑ a, μ a * θ (Fin.rev a) = ∑ a, μ (Fin.rev a) * θ a := by
      rw [← Equiv.sum_comp Fin.revPerm]
      simp
    rw [← ContinuousLinearMap.comp_apply, ← hπ.1.2 _ (tor_mem θ) _ revM_mem, tor_revM,
      hπ.1.2 _ revM_mem _ (tor_mem _), ContinuousLinearMap.comp_apply, (wt_iff _ _).1 hv, map_smul, e]

theorem cdom_neg_rev {μ Λ : Fin k → ℝ} (h : CDom (allPos k) μ Λ) :
    CDom (allPos k) (fun a => -μ (Fin.rev a)) fun a => -Λ (Fin.rev a) := by
  obtain ⟨c, hc, e⟩ := h
  refine ⟨fun a b => c (Fin.rev b) (Fin.rev a), fun a b h => ⟨Fin.rev_lt_rev.1 (hc _ _ h).1, rfl⟩, ?_⟩
  funext x
  have h1 := congrFun e (Fin.rev x)
  rw [← Equiv.sum_comp Fin.revPerm] at h1
  simp only [← Equiv.sum_comp Fin.revPerm (fun b => (c _ b : ℝ) • Formalism.REAL.root _ b)] at h1
  rw [Finset.sum_comm] at h1
  simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, Formalism.REAL.root, Pi.single_apply, Fin.revPerm_apply,
    Fin.rev_inj, smul_eq_mul] at h1 ⊢
  rw [show -Λ x.rev - -μ x.rev = -(Λ x.rev - μ x.rev) by ring, h1, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun b _ => by ring

theorem isHCTypeU_conj {u : Fin k → ℝ} (h : IsHCTypeU k u π) :
    IsHCTypeU k (fun i => -u (Fin.rev i)) (fun g => π (g.map star)) := by
  obtain ⟨h1, h2, h3, h4, -, h5, ⟨v, -, hv0, hv⟩, h6⟩ := h
  have hl : Formalism.QuantumDeterminants.lowK (allPos k) (fun i => -u (Fin.rev i)) =
      fun a => -Formalism.QuantumDeterminants.lowK (allPos k) u (Fin.rev a) := by
    funext a
    unfold allPos
    rw [GlobalTheory.DefiniteCheck.lowK_const, GlobalTheory.DefiniteCheck.lowK_const, Fin.val_rev, Nat.cast_sub a.2]
    push_cast
    ring
  have h3' := h3
  rw [ujset_eq] at h3'
  refine ⟨h1, h2, ?_, h4, fun _ _ _ _ => trivial, fun S hS hst => h5 S hS fun g hg x hx => ?_,
    ⟨_, trivial, (wt_rev h3 hv0 hv).1, ?_⟩, fun μ x _ hx0 hx => ?_⟩
  · rw [ujset_eq]
    refine ⟨⟨?_, fun a ha b hb => ?_⟩, fun g hg => h3'.2.1 _ (conj_mem hg), fun x => ?_⟩
    · beta_reduce
      rw [Matrix.map_one _ (star_zero ℂ) (star_one ℂ)]
      exact h3'.1.1
    · have : (a * b).map star = a.map star * b.map star := Matrix.map_mul (f := starRingEnd ℂ)
      beta_reduce
      rw [this]
      exact h3'.1.2 _ (conj_mem ha) _ (conj_mem hb)
    · exact (h3'.2.2 x).comp (continuous_id.matrix_map continuous_star).continuousOn fun g hg => conj_mem hg
  · rw [kset_eq] at hg
    have := hst (g.map star) (by rw [kset_eq]; exact conj_mem hg) x hx
    have e : (g.map star).map star = g := by
      ext a b
      simp
    simpa only [e] using this
  · rw [hl, wt_conj]
    convert (wt_rev h3 hv0 hv).2 using 1
    funext a
    simp
  · obtain ⟨a1, a2⟩ := wt_rev h3 hx0 (wt_conj.1 hx)
    rw [hl]
    convert cdom_neg_rev (h6 _ _ trivial a1 a2) using 1
    funext a
    simp

end GlobalTheory.CoefSpace.Conj
end
end

section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GraphClosure

theorem exists_normalisation_of_locallyClosed : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] (P U : Scheme.{0}) (s : P ⟶ Sp O) (Ω : P.Opens) (j : U ⟶ Ω.toScheme), IsProjOver s → IsClosedImmersion j → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme U → Flat (j ≫ Ω.ι ≫ s) → ∃ (Z' : Scheme.{0}) (ν : Z' ⟶ P) (e : U ⟶ Z'), IsFinite ν ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z' ∧ IsProjOver (ν ≫ s) ∧ Flat (ν ≫ s) ∧ IsPullback e j ν Ω.ι ∧ Dense (Set.range e) := by
  intro O _ _ _ P U s Ω j hs _ hn hfl
  have : IsProper s := ((isProjOver_iff_isProper_and_exists_isAmpleLB s).mp hs).1
  have := GlobalTheory.IsNormalScheme.of_pred hn
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian s
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian (j ≫ Ω.ι)
  obtain ⟨h, eh⟩ : ∃ h : U ⟶ P, h = j ≫ Ω.ι := ⟨_, rfl⟩
  have : QuasiCompact h := eh ▸ inferInstance
  have : IsSeparated h := eh ▸ inferInstance
  have : LocallyOfFiniteType h := eh ▸ inferInstance
  have : Flat (h ≫ s) := by rw [eh, Category.assoc]; exact hfl
  have : IsFinite h.fromNormalization :=
    isFinite_fromNormalization_of_locallyOfFiniteType (o := CommRingCat.of O) h s
      fun x hx => charZero_residueField_of_flat (h ≫ s) hx
  have : Flat (h.toNormalization ≫ h.fromNormalization ≫ s) := by
    rw [Scheme.Hom.toNormalization_fromNormalization_assoc]
    infer_instance
  exact ⟨h.normalization, h.fromNormalization, h.toNormalization, inferInstance,
    IsNormalScheme.pred _, isProjOver_comp_of_isFinite _ hs, flat_normalization h _,
    isPullback_toNormalization_of_mono j Ω.ι h eh, h.toNormalization.denseRange⟩

end GlobalTheory.GraphClosure
end
