module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsBlockProductMemIntegralHarmonic
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle002
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle007
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle003
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle008
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle060
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsMemRowHighestTotalDegreeEqTwo
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FirstMinimumEqZeroOfRankZero
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FirstMinimumPrincipalTorusAtOrthonormalFrame
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsHarmonicAndMemMinorSpan
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle006
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle065
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle006
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle061
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RowHighestLeSpanColWordComplex
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetOfTriangular
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetA
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.UniformSpace.Uniformizable
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle014

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_blockProduct_mem_integralHarmonic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ τ i k, i ≤ k → a (τ, k) ≤ a (τ, i)) → I2.PT.f E * (Dw.p + Dw.q) * (Dw.p + Dw.q + 1) ≤ 2 * n → ∃ P : MvPolynomial (LtN Dw n) c.F, P ∈ harmA c a n ∧ _root_.GlobalTheory.BlockTh.IsBlockProd P ∧ P.totalDegree = Formalism.L2.Pj.DF Dw a ∧ ∀ σ : c.F →+* ℂ, ∑ m ∈ P.support, ‖σ (P.coeff m)‖ ≤ ((Dw.p + Dw.q : ℕ) : ℝ) ^ Formalism.L2.Pj.DF Dw a := by
  first | exact @GlobalTheory.BlockProdEx.exists_blockProd_mem_harmA | exact GlobalTheory.BlockProdEx.exists_blockProd_mem_harmA | (intros; apply GlobalTheory.BlockProdEx.exists_blockProd_mem_harmA <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares
open MeasureTheory

namespace GlobalTheory.GenericFlat

theorem ae_cast {a b n m : ℕ} (hab : a = b) (hnm : n = m) (P : (Fin (a + 1) × Fin n → ℂ) → Prop)
    (hP : ∀ᵐ t : Fin (a + 1) × Fin n → ℂ, P t) :
    ∀ᵐ t : Fin (b + 1) × Fin m → ℂ,
      P fun p => t (Fin.cast (congrArg (· + 1) hab) p.1, Fin.cast hnm p.2) := by
  subst hab hnm
  simpa using hP

theorem exists_generic_flatAt : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1), ∃ t : Idx D j N → ℂ, (∀ Q : MvPolynomial (Idx D j N) T.Q.c.F, Q ≠ 0 → MvPolynomial.eval₂ T.σ₀ t Q ≠ 0) ∧ Nonempty (FlatAt h j A t) := by
  intro D T h j _hj N wL wF w Tn c1 A
  have hC : Countable T.Q.c.F := (Module.finBasis ℚ T.Q.c.F).equivFun.injective.countable

  have hk : ∀ k : (T.U j T.σ₀).Comp, ∀ᵐ t : Fin (WeightFamilies.dimY D j + 1) × Fin N → ℂ,
      ∃ Fl : FlatM ((T.U j T.σ₀).X k) (A.Xa k),
        (∀ x, Fl.w0 x = ∑ i, t (0, i) * rdR h j (w i) k x) ∧
        ∀ a x, Fl.s a x = ∑ i, t ((Fin.cast (A.dim k) a).succ, i) * rdR h j (w i) k x := by
    intro k
    have H := GlobalTheory.T.ae_exists_flat_datum_linearCombination _ _ ((T.U j T.σ₀).X k) (A.Xa k) T.Q.c.F T.σ₀ (A.rel k)
    refine (ae_cast (A.dim k) (A.hN k) _ H).mono ?_
    rintro t ⟨Fl, h0, hs⟩
    refine ⟨Fl, fun x => ?_, fun a x => ?_⟩
    · rw [h0]
      refine Fintype.sum_equiv (finCongr (A.hN k)) _ _ fun i => ?_
      simp only [A.hw k i, finCongr_apply]
      congr 2
    · rw [hs]
      refine Fintype.sum_equiv (finCongr (A.hN k)) _ _ fun i => ?_
      simp only [A.hw k i, finCongr_apply]
      congr 2

  have hall := (ae_all_iff.2 hk).and
    (GlobalTheory.ae_eval₂_ne_zero_of_countable T.Q.c.F T.σ₀ (Fin (WeightFamilies.dimY D j + 1) × Fin N))
  obtain ⟨t, ht, hg⟩ := hall.exists
  choose Fl h0 hs using ht
  exact ⟨t, hg, ⟨⟨Fl, h0, hs⟩⟩⟩

end GlobalTheory.GenericFlat
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps GlobalTheory.Shares

namespace GlobalTheory.Shares

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j}

theorem addL_zero_wt (u wL : WeightFamilies.Wt D j) : addL u wL 0 = u := by
  cases u
  simp [addL, wadd, wsmul]

theorem rk_Mlat_eq_finrank (X : PJ D B P j) (ka : WeightFamilies.Wt D j) (h : LatAt B j ka) :
    X.rk ka (B.Mlat j ka) = Module.finrank B.KO (⊤ : Submodule B.KO (B.Cusp j ka)) := by
  letI : Submodule.IsFullLattice B.KO (B.Mlat j ka) := h
  unfold PJ.rk
  rw [Submodule.IsFullLattice.span_eq_top]

private lemma s_mem_sp_univ (R : Rdg X) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)
    (t : Idx D j N → ℂ) (i : Fin (WeightFamilies.dimY D j + 1)) : R.s w t i ∈ R.sp wL Set.univ := by
  unfold Rdg.s Rdg.sp
  refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨w k, Set.mem_univ _, rfl⟩

theorem Rdg.s_pow_mul_mem (R : Rdg X) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL) (t : Idx D j N → ℂ)
    (hmul : ∀ u u', ∀ f ∈ R.sp u Set.univ, ∀ g ∈ R.sp u' Set.univ, f * g ∈ R.sp (wadd u u') Set.univ)
    (i : Fin (WeightFamilies.dimY D j + 1)) (u : WeightFamilies.Wt D j) (n m : ℕ) {v : R.Y → ℂ}
    (hv : v ∈ R.sp (addL u wL n) Set.univ) : R.s w t i ^ m * v ∈ R.sp (addL u wL (n + m)) Set.univ := by
  induction m with
  | zero => simpa using hv
  | succ m ih =>

    rw [pow_succ', mul_assoc, ← Nat.add_assoc, ← wadd_addL]
    exact hmul _ _ _ (s_mem_sp_univ R w t i) _ ih

theorem Rdg.prod_pow_mul_mem (R : Rdg X) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL) (t : Idx D j N → ℂ)
    (hmul : ∀ u u', ∀ f ∈ R.sp u Set.univ, ∀ g ∈ R.sp u' Set.univ, f * g ∈ R.sp (wadd u u') Set.univ)
    (α : Fin (WeightFamilies.dimY D j) → ℕ) (s : Finset (Fin (WeightFamilies.dimY D j))) (u : WeightFamilies.Wt D j) (n : ℕ) {v : R.Y → ℂ}
    (hv : v ∈ R.sp (addL u wL n) Set.univ) :
    (∏ i ∈ s, R.s w t i.succ ^ α i) * v ∈ R.sp (addL u wL (n + ∑ i ∈ s, α i)) Set.univ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hv
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, mul_assoc]
    have h := R.s_pow_mul_mem w t hmul a.succ u (n + ∑ i ∈ s, α i) (α a) ih
    have e : n + (α a + ∑ i ∈ s, α i) = n + ∑ i ∈ s, α i + α a := by ring
    rw [e]
    exact h

theorem shareRd_of_inBasis : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData X ka wL wF) (R : Rdg X) (t : Idx D j G.N → ℂ) (T : ℕ) (Mg : Submodule B.KO (B.Cusp j ka)) (δ : ℕ) (xs : Fin δ → R.Y), R.Generic t → AnFacts R G.w t ka wF T Mg xs → addL wF wL T = ka → WeightFamilies.dimY D j < T → 0 < WeightFamilies.dimY D j → LatAt B j ka → (∃ la, InBasis G la) → ShareRd (D := D) (j := j) T G.del (X.rk ka (B.Mlat j ka)) := by
  intro D B P j X ka wL wF G R t T Mg δ xs hgen hfac hka hDT _ hlat hex
  obtain ⟨la, hla⟩ := hex

  have hI := (GlobalTheory.T.inBasis_iff_pointValues_linearIndependent_span D B P j X ka wL wF G R t T Mg δ xs hgen hfac hka la).1 hla
  obtain ⟨-, -, -, -, -, hmul, -, hfin⟩ := GlobalTheory.T.genericSections_polynomial_dictionary D B P j X R la G.N wL G.w t
  have hθ : ∀ i, R.ev (X.inc wF (G.th' i)) ∈ R.sp wF Set.univ := fun i =>
    Submodule.subset_span ⟨G.th' i, Set.mem_univ _, rfl⟩

  have hLI := (hfac.indep G.del (fun i => R.ev (X.inc wF (G.th' i))) hθ hI.1).1

  have hmem : ∀ p, R.lead G.w t T (a0 D j T) (fun i => R.ev (X.inc wF (G.th' i))) p ∈
      R.sp ka Set.univ := by
    rintro ⟨⟨α, hα⟩, i⟩
    have h0 : R.ev (X.inc wF (G.th' i)) ∈ R.sp (addL wF wL 0) Set.univ := by
      rw [addL_zero_wt]
      exact hθ i
    have h1 := R.s_pow_mul_mem G.w t hmul 0 wF 0 (T - ∑ k, α k) h0
    have h2 := R.prod_pow_mul_mem G.w t hmul α Finset.univ wF (0 + (T - ∑ k, α k)) h1
    have hle : ∑ k, α k ≤ T := by
      unfold a0 at hα
      omega
    have e : 0 + (T - ∑ k, α k) + ∑ k ∈ Finset.univ, α k = T := by omega
    rw [e, hka] at h2
    show R.mon G.w t α * R.s G.w t 0 ^ (T - ∑ k, α k) * R.ev (X.inc wF (G.th' i)) ∈ R.sp ka Set.univ
    rw [mul_assoc]
    exact h2

  obtain ⟨hfd, hfr⟩ := hfin ka ⊤
  rw [Submodule.top_coe] at hfd hfr
  have hcard : Nat.card ({α : Fin (WeightFamilies.dimY D j) → ℕ // ∑ i, α i < a0 D j T} × Fin G.del) ≤
      Module.finrank B.KO (⊤ : Submodule B.KO (B.Cusp j ka)) := by
    rw [← hfr]
    haveI : FiniteDimensional ℂ (R.sp ka Set.univ) := hfd
    have hLI' : LinearIndependent ℂ (fun p =>
        (⟨R.lead G.w t T (a0 D j T) (fun i => R.ev (X.inc wF (G.th' i))) p, hmem p⟩ :
          R.sp ka Set.univ)) :=
      LinearIndependent.of_comp (R.sp ka Set.univ).subtype hLI
    haveI := hLI'.finite
    haveI := Fintype.ofFinite ({α : Fin (WeightFamilies.dimY D j) → ℕ // ∑ i, α i < a0 D j T} × Fin G.del)
    rw [Nat.card_eq_fintype_card]
    exact hLI'.fintype_card_le_finrank
  have hcnt : Nat.card {α : Fin (WeightFamilies.dimY D j) → ℕ // ∑ i, α i < a0 D j T} =
      (T - 1).choose (WeightFamilies.dimY D j) :=
    GlobalTheory.card_exponents_sum_lt_sub _ _ hDT
  rw [Nat.card_prod, Nat.card_fin, hcnt] at hcard
  unfold ShareRd
  rw [rk_Mlat_eq_finrank X ka hlat]
  exact_mod_cast hcard

end GlobalTheory.Shares
end

section

noncomputable section

namespace GlobalTheory.Shares.Contain

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps GlobalTheory.Shares

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem addL_zero (u wL : WeightFamilies.Wt D j) : addL u wL 0 = u := by
  unfold addL wadd wsmul
  cases u
  simp only [WeightFamilies.Wt.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext τ i; simp
  · funext τ i; simp
  · simp

def secP (X : PJ D B P j) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL) (i : Fin (WeightFamilies.dimY D j + 1)) :
    MvPolynomial (Idx D j N) X.Forms :=
  ∑ k, MvPolynomial.X (i, k) * MvPolynomial.C (X.inc wL (w k))

section Weights

variable {X : PJ D B P j} {N : ℕ} {wL : WeightFamilies.Wt D j} {w : Fin N → B.Cusp j wL}

theorem ofWt_pow_mul (hs : ∀ i, OfWt X wL (secP X w i))
    (hm : ∀ u u' (p q : MvPolynomial (Idx D j N) X.Forms), OfWt X u p → OfWt X u' q → OfWt X (wadd u u') (p * q))
    (i : Fin (WeightFamilies.dimY D j + 1)) (u : WeightFamilies.Wt D j) (n m : ℕ) {p : MvPolynomial (Idx D j N) X.Forms}
    (hp : OfWt X (addL u wL n) p) : OfWt X (addL u wL (n + m)) (secP X w i ^ m * p) := by
  induction m with
  | zero => simpa using hp
  | succ m ih =>
    rw [pow_succ', mul_assoc, ← add_assoc, ← wadd_addL]
    exact hm _ _ _ _ (hs i) ih

theorem ofWt_prod_mul (hs : ∀ i, OfWt X wL (secP X w i))
    (hm : ∀ u u' (p q : MvPolynomial (Idx D j N) X.Forms), OfWt X u p → OfWt X u' q → OfWt X (wadd u u') (p * q))
    (α : Fin (WeightFamilies.dimY D j) → ℕ) (u : WeightFamilies.Wt D j) (n : ℕ) {p : MvPolynomial (Idx D j N) X.Forms}
    (hp : OfWt X (addL u wL n) p) (s : Finset (Fin (WeightFamilies.dimY D j))) :
    OfWt X (addL u wL (n + ∑ i ∈ s, α i)) ((∏ i ∈ s, secP X w i.succ ^ α i) * p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, mul_assoc, add_comm (α a), ← add_assoc]
    exact ofWt_pow_mul hs hm _ u _ _ ih

end Weights

theorem inContainMR_of_anFacts : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData X ka wL wF) (R : Rdg X) (t : Idx D j G.N → ℂ) (T : ℕ) (CR c : ℝ) (δ : ℕ) (xs : Fin δ → R.Y), R.Generic t → AnFacts R G.w t ka wF T (WeightFamilies.MggK B CR T c j ka) xs → addL wF wL T = ka → WeightFamilies.dimY D j ≤ T → ∀ S : Scal B, Submodule.span B.KO ((X.Thc S.s0 (X.wF0 wL wF) : Submodule (𝓞 B.KO) _) : Set (B.Cusp j (X.wF0 wL wF))) = ⊤ → ∀ la, InBasis G la → InContainMR G la S CR T c := by
  intro D B P j X ka wL wF G R t T CR c δ xs hgen hA hka hDT S hTh la hB
  obtain ⟨hsec, hC, hCw, hmul, -, -, hsp, -⟩ := GlobalTheory.T.genericSections_polynomial_dictionary D B P j X R la G.N wL G.w t
  obtain ⟨hli, hdel⟩ := (GlobalTheory.T.inBasis_iff_pointValues_linearIndependent_span D B P j X ka wL wF G R t T _ δ xs hgen hA hka la).1 hB
  have hs1 : ∀ i, toRp X la G.N (secP X G.w i) = sec X la G.w i := fun i => (hsec i).1
  have hs2 : ∀ i, R.toFn t (secP X G.w i) = R.s G.w t i := fun i => (hsec i).2.1
  have hs3 : ∀ i, OfWt X wL (secP X G.w i) := fun i => (hsec i).2.2
  have hspan : Submodule.span ℂ (Set.range (vals xs fun i => R.ev (X.inc wF (G.th' i)))) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp [hdel])
  have hcon := hA.contain G.del (fun i => R.ev (X.inc wF (G.th' i)))
    (fun i => Submodule.subset_span ⟨G.th' i, Set.mem_univ _, rfl⟩) hspan

  set Gen : Set (Rp X la G.N) := ({v | ∃ (al : Fin (WeightFamilies.dimY D j) → ℕ) (i : Fin G.del), ∑ i, al i < a0 D j T ∧
          v = _root_.Formalism.MainNotions.Gaps.EtaleWeightGaps.secPow X la G.w al * sec X la G.w 0 ^ (T - ∑ i, al i) * emb X la G.N (X.inc wF (G.th' i))} ∪
       zAll G la S T) with hGen
  let Sp : Set (MvPolynomial (Idx D j G.N) X.Forms) := {p | OfWt X ka p ∧ toRp X la G.N p ∈ Gen}
  have hle : Submodule.span ℂ (Set.range (R.lead G.w t T (a0 D j T) fun i => R.ev (X.inc wF (G.th' i)))) ⊔
      R.deep G.w t (X.wF0 wL wF) (a0 D j T) ≤ Submodule.span ℂ (R.toFn t '' Sp) := by
    refine sup_le (Submodule.span_mono ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨⟨⟨al, hal⟩, i⟩, rfl⟩
      refine ⟨(∏ k, secP X G.w k.succ ^ al k) * (secP X G.w 0 ^ (T - ∑ k, al k) *
        MvPolynomial.C (X.inc wF (G.th' i))), ⟨?_, Or.inl ⟨al, i, hal, ?_⟩⟩, ?_⟩
      · have h0 : OfWt X (addL wF wL 0) (MvPolynomial.C (X.inc wF (G.th' i)) : MvPolynomial (Idx D j G.N) X.Forms) := by
          rw [addL_zero]; exact hCw _ _
        have h1 := ofWt_prod_mul hs3 hmul al wF _ (ofWt_pow_mul hs3 hmul 0 wF 0 (T - ∑ k, al k) h0) Finset.univ
        have he : 0 + (T - ∑ k, al k) + ∑ k, al k = T := by
          unfold a0 at hal; omega
        rwa [he, hka] at h1
      · simp only [map_mul, map_prod, map_pow, hs1, (hC _).1, _root_.Formalism.MainNotions.Gaps.EtaleWeightGaps.secPow, mul_assoc]
      · simp only [map_mul, map_prod, map_pow, hs2, (hC _).2, Rdg.lead, Rdg.mon, mul_assoc]
    · rintro _ ⟨al, f, hal, hf, rfl⟩
      have hf' : f ∈ R.sp (X.wF0 wL wF)
          ((X.Thc S.s0 (X.wF0 wL wF) : Submodule (𝓞 B.KO) _) : Set (B.Cusp j (X.wF0 wL wF))) := by
        rw [← hsp, hTh]; exact hf
      clear hf
      unfold Rdg.sp at hf'
      induction hf' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨θ, hθ, rfl⟩ := hx
        refine Submodule.subset_span ⟨(∏ k, secP X G.w k.succ ^ al k) * MvPolynomial.C (X.inc _ θ),
          ⟨?_, Or.inr ⟨al, θ, hal, hθ, ?_⟩⟩, ?_⟩
        · have h0 : OfWt X (addL wF wL (WeightFamilies.dimY D j))
              (MvPolynomial.C (X.inc _ θ) : MvPolynomial (Idx D j G.N) X.Forms) := hCw _ θ
          have h1 := ofWt_prod_mul hs3 hmul al wF _ h0 Finset.univ
          have he : WeightFamilies.dimY D j + ∑ k, al k = T := by
            unfold a0 at hal; omega
          rwa [he, hka] at h1
        · simp only [map_mul, map_prod, map_pow, hs1, (hC _).1, _root_.Formalism.MainNotions.Gaps.EtaleWeightGaps.secPow]
        · simp only [map_mul, map_prod, map_pow, hs2, (hC _).2, Rdg.mon]
      | zero => rw [mul_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
      | smul a x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx
  refine Submodule.span_le.2 ?_
  rintro _ ⟨F, hF, rfl⟩
  have hmem : R.ev (X.inc ka F) ∈ Submodule.span ℂ (R.toFn t '' Sp) :=
    hle (hcon (Submodule.subset_span ⟨F, hF, rfl⟩))
  obtain ⟨n, a, g, hsum⟩ := Submodule.mem_span_set'.1 hmem
  choose p hp hpg using fun i => (g i).2
  have htr := (GlobalTheory.T.indep_span_rank_transfer_largeField_complex D B P j X R la G.N t hgen ka (Fin n) p (fun i => (hp i).1)).2.1
    (MvPolynomial.C (X.inc ka F)) (hCw _ _)
  rw [(hC _).1, (hC _).2] at htr
  have h2 : R.ev (X.inc ka F) ∈ Submodule.span ℂ (Set.range fun i => R.toFn t (p i)) := by
    rw [← hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hpg i⟩)
  refine Submodule.span_mono ?_ (htr.2 h2)
  rintro _ ⟨i, rfl⟩
  exact (hp i).2

end GlobalTheory.Shares.Contain
end
end

section

open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.ThFr

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {g : ℕ}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)
  {q0 : ℕ} (hr : X.p0 + q0 = r) {n : ℕ} {c : X.Ψ → Fin q0 → ℕ} {c' : X.Ψ → Fin X.p0 → ℕ}

theorem hasSum_prod_of_fintype {J ι : Type*} [Fintype J] {f : J → ι → ℂ} {y : J → ℂ}
    (hf : ∀ j, Summable fun m => ‖f j m‖) (h : ∀ j, HasSum (f j) (y j)) :
    (Summable fun p : J × ι => ‖f p.1 p.2‖) ∧ HasSum (fun p : J × ι => f p.1 p.2) (∑ j, y j) := by
  have h1 : Summable fun p : J × ι => ‖f p.1 p.2‖ :=
    (summable_prod_of_nonneg fun _ => norm_nonneg _).2 ⟨hf, Summable.of_finite⟩
  have h2 := h1.of_norm.hasSum
  exact ⟨h1, (h2.prod_fiberwise h).unique (hasSum_fintype y) ▸ h2⟩

theorem exists_expansion_of_rowHighest (hs : IsSympl X bas) (hn : Even n) (hpq : X.p0 + q0 ≤ n)
    (hc : ∃ τ, (∃ i : Fin q0, i.val + 1 = q0 ∧ 1 ≤ c τ i) ∨
      ∃ i : Fin X.p0, i.val + 1 = X.p0 ∧ 1 ≤ c' τ i)
    (a b : Fin n → Fin g → ℝ) {P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)}
    (hP : P ∈ Harm.rowHighest ℂ c c') {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) :
    ∃ (A : (Fin n → Fin g → ℤ) → ℂ) (ν : (Fin n → Fin g → ℤ) → X.Ψ → ℝ),
      (Summable fun m => ‖A m‖) ∧
      (∀ s : X.Ψ → ℝ, HasSum (fun m => A m * cexp (4 * Real.pi * I * ∑ τ, (ν m τ : ℂ) * s τ))
        (thFr X hr bas idx n a b P (X.flow ξ (fun τ => (s τ : ℂ)) x))) ∧
      ∀ m, A m ≠ 0 → ν m ≠ 0 := by
  obtain ⟨bas', S, hs', hA⟩ := exists_isAdapted hs hξ.2.1
  obtain ⟨a', b', κ, -, -, hκ⟩ := exists_thFr_eq_mul idx hr hs hs' hn a b
  have hm : P ∈ GaussGauge.minorSpan (Fin n) c c' :=
    GaussGauge.orbitSpan_le_minorSpan (add_comm X.p0 q0 ▸ hpq) c c'
      (Harm.rowHighest_eq_orbitSpan (add_comm X.p0 q0 ▸ hpq) c c' ℂ ▸ hP)
  obtain ⟨A, hA1, hA2, hA3⟩ := hA.exists_expansion hr idx hs' hξ n a' b'
    (Harm.isHarmonic_of_mem_rowHighest hP) hm hc hx
  refine ⟨fun m => κ * A m, _, ?_, fun s => ?_,
    fun m hm h0 => hm (mul_eq_zero_of_right κ (hA3 m h0))⟩
  · simpa only [norm_mul] using hA1.mul_left ‖κ‖
  · have hxs := (FlowCoefficientBounds.flow_real X hξ hx s 0).1
    rw [hκ P _ hxs]
    simpa only [mul_assoc] using (hA2 _ hxs).mul_left κ

variable {J : Type*} (s : Finset J) (t : J → ℂ) (a b : J → Fin n → Fin g → ℝ)
  {P : J → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)} {Q : Frame X.Ψ r → ℂ}

theorem isSec_of_eq_sum_thFr (hs : IsSympl X bas) (hP : ∀ j ∈ s, P j ∈ Harm.rowHighest ℂ c c')
    (hQ : ∀ x ∈ X.dom, Q x = ∑ j ∈ s, t j * thFr X hr bas idx n (a j) (b j) (P j) x)
    (hΓ : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, Q (lact γ x) = X.χ (wtOf X hr c c' n) γ * Q x) :
    X.IsSec (wtOf X hr c c' n) Q := by
  refine ⟨DifferentiableOn.congr (DifferentiableOn.fun_sum fun j hj => ?_) hQ,
    fun x hx u hu => ?_, hΓ⟩
  · exact (differentiableOn_thFr idx hs hr n _ _
      (Harm.isHarmonic_of_mem_rowHighest (hP j hj))).const_mul _
  · rw [hQ _ (PerMove.rmul_mem_GG hx hu), hQ x hx, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j hj => by
      rw [thFr_rmul idx hr _ _ hs (hP j hj) hx hu, mul_left_comm]

theorem isModerate_of_eq_sum_thFr (hs : IsSympl X bas) (hn : Even n)
    (hP : ∀ j ∈ s, P j ∈ Harm.rowHighest ℂ c c')
    (hQ : ∀ x ∈ X.dom, Q x = ∑ j ∈ s, t j * thFr X hr bas idx n (a j) (b j) (P j) x) :
    X.IsModerate (wtOf X hr c c' n) Q := by
  obtain ⟨C, A, h⟩ := isModerate_sum_thFr idx hr hs hn s t a b hP
  exact ⟨C, A, fun x hx => by simpa only [Data.pnorm, hQ x hx] using h x hx⟩

theorem exists_expansion_of_eq_sum_thFr (hs : IsSympl X bas) (hn : Even n) (hpq : X.p0 + q0 ≤ n)
    (hc : ∃ τ, (∃ i : Fin q0, i.val + 1 = q0 ∧ 1 ≤ c τ i) ∨
      ∃ i : Fin X.p0, i.val + 1 = X.p0 ∧ 1 ≤ c' τ i)
    (hP : ∀ j ∈ s, P j ∈ Harm.rowHighest ℂ c c')
    (hQ : ∀ x ∈ X.dom, Q x = ∑ j ∈ s, t j * thFr X hr bas idx n (a j) (b j) (P j) x)
    {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    ∃ (A : s × (Fin n → Fin g → ℤ) → ℂ) (ν : s × (Fin n → Fin g → ℤ) → X.Ψ → ℝ),
      (Summable fun m => ‖A m‖) ∧
      (∀ u : X.Ψ → ℝ, HasSum (fun m => A m * cexp (4 * Real.pi * I * ∑ τ, (ν m τ : ℂ) * u τ))
        (Q (X.flow ξ (fun τ => (u τ : ℂ)) x))) ∧
      ∀ m, A m ≠ 0 → ν m ≠ 0 := by
  choose A ν h1 h2 h3 using fun j : s =>
    exists_expansion_of_rowHighest idx hr hs hn hpq hc (a j) (b j) (hP j j.2) hξ hx
  have h4 (j : s) : Summable fun m => ‖t j * A j m‖ := by
    simpa only [norm_mul] using (h1 j).mul_left ‖t j‖
  refine ⟨fun p => t p.1 * A p.1 p.2, fun p => ν p.1 p.2,
    (hasSum_prod_of_fintype h4 fun j => (h4 j).of_norm.hasSum).1, fun u => ?_,
    fun p hp => h3 _ _ (right_ne_zero_of_mul hp)⟩
  rw [hQ _ (FlowCoefficientBounds.flow_real X hξ hx u 0).1, ← Finset.sum_coe_sort]
  refine (hasSum_prod_of_fintype
    (f := fun (j : s) m => t j * A j m * cexp (4 * Real.pi * I * ∑ τ, (ν j m τ : ℂ) * u τ))
    (fun j => ?_) fun j => ?_).2
  · refine (h4 j).congr fun m => ?_
    have h := FJZero.norm_expo (ν j m) u
    rw [FJZero.expo] at h
    rw [norm_mul (t j * A j m), h, mul_one]
  · simpa only [mul_assoc] using (h2 j u).mul_left (t j)

theorem mem_SS_of_eq_sum_thFr (hs : IsSympl X bas) (hn : Even n)
    (hc : (X.p0 + q0 ≤ n ∧ ∃ τ, (∃ i : Fin q0, i.val + 1 = q0 ∧ 1 ≤ c τ i) ∨
      ∃ i : Fin X.p0, i.val + 1 = X.p0 ∧ 1 ≤ c' τ i) ∨ ∀ ξ, ¬ X.IsIso ξ)
    (hP : ∀ j ∈ s, P j ∈ Harm.rowHighest ℂ c c')
    (hQ : ∀ x ∈ X.dom, Q x = ∑ j ∈ s, t j * thFr X hr bas idx n (a j) (b j) (P j) x)
    (hΓ : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, Q (lact γ x) = X.χ (wtOf X hr c c' n) γ * Q x) :
    Q ∈ X.SS (wtOf X hr c c' n) := by
  have hsec := isSec_of_eq_sum_thFr idx hr s t a b hs hP hQ hΓ
  refine FJZero.mem_SS_of_isModerate X _ Q hsec
    (isModerate_of_eq_sum_thFr idx hr s t a b hs hn hP hQ) fun ξ hξ x hx => ?_
  obtain ⟨hpq, hc⟩ := hc.resolve_right fun h => h ξ hξ
  obtain ⟨A, ν, h1, h2, h3⟩ := exists_expansion_of_eq_sum_thFr idx hr s t a b hs hn hpq hc hP hQ hξ hx
  exact FJZero.fj_eq_zero_of_isSec X _ Q hsec hξ hx A h1 ν h2 0 h3

end

end GlobalTheory.ThFr
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

theorem _root_.GlobalTheory.T.cuspForm_halfSup_at_orthonormalFrame_firstMin : ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → LastPos (T.Q.Dw j) (wtA w) → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ f ∈ T.C j w, 0 < supN (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f) → ∃ (k : (T.U j σ).Comp) (xf : ((T.U j σ).X k).dom), (∀ τ' i', ‖dmin ((T.U j σ).X k).Gm xf.1 τ' i'‖ = 1) ∧ ((T.U j σ).X k).IsOrtho xf.1 ∧ supN (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f) ≤ 2 * ‖toC (evR (T.Q.Xo j) T.Q.c f ((T.U j σ).un k xf))‖ ∧ 0 < ((T.U j σ).X k).firstMinimumSq xf.1 ∧ Real.log (1 / ((T.U j σ).X k).firstMinimumSq xf.1) ≤ 80 * large₂.sc.L := by
  first | exact @GlobalTheory.RunIn.half_sup_at_ortho_frame | exact GlobalTheory.RunIn.half_sup_at_ortho_frame | (intros; apply GlobalTheory.RunIn.half_sup_at_ortho_frame <;> assumption)
end
