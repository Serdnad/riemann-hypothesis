module

public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsMulEqPolynomialWeierstrassP
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassCurvePointOfLatticeAddOfGeneric
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassPAddOfNeOfDerivNeZero
public import Formalism.LocalToGlobal.ProjectiveLattices.CrudeMin
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle011
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle001

@[expose] public section

section

open Filter PeriodPair
open scoped Topology

noncomputable section

namespace GlobalTheory.EllipticPoles

variable (L : PeriodPair)

lemma tendsto_neg_ne (a : ℂ) : Tendsto (fun z : ℂ ↦ -z) (𝓝[≠] a) (𝓝[≠] (-a)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (continuous_neg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (by filter_upwards [self_mem_nhdsWithin] with z hz using by simpa using hz)

lemma tendsto_add_ne (a l : ℂ) : Tendsto (fun z : ℂ ↦ z + l) (𝓝[≠] a) (𝓝[≠] (a + l)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    ((continuous_add_const l).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (by filter_upwards [self_mem_nhdsWithin] with z hz using by simpa using hz)

lemma tendsto_two_ne (a : ℂ) : Tendsto (fun z : ℂ ↦ z + z) (𝓝[≠] a) (𝓝[≠] (a + a)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    ((by fun_prop : Continuous fun z : ℂ ↦ z + z).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (by
      filter_upwards [self_mem_nhdsWithin] with z hz h
      apply hz
      simp only [Set.mem_singleton_iff] at h ⊢
      linear_combination h / 2)

lemma exists_analytic_of_tendsto {f : ℂ → ℂ} {a c : ℂ} (hf : MeromorphicAt f a)
    (h : Tendsto f (𝓝[≠] a) (𝓝 c)) : ∃ g, AnalyticAt ℂ g a ∧ f =ᶠ[𝓝[≠] a] g :=
  hf.meromorphicOrderAt_nonneg_iff.1 ((tendsto_nhds_iff_meromorphicOrderAt_nonneg hf).1 ⟨c, h⟩)

lemma even_case {g : ℂ → ℂ} (hg : Meromorphic g)
    (hd : ∀ a ∉ L.lattice, ∃ c, Tendsto g (𝓝[≠] a) (𝓝 c))
    (hp : ∀ z, ∀ l ∈ L.lattice, g (z + l) = g z) (hev : ∀ z, g (-z) = g z) :
    ∃ A : Polynomial ℂ, ∀ z₀ : ℂ, ∀ᶠ z in 𝓝[≠] z₀, g z = A.eval (℘[L] z) := by
  classical
  let G : ℂ → ℂ := fun z ↦ if z ∈ L.lattice then 0 else limUnder (𝓝[≠] z) g
  have hG : ∀ a ∉ L.lattice, ∀ c, Tendsto g (𝓝[≠] a) (𝓝 c) → G a = c := fun a ha c h ↦ by
    simp only [G, if_neg ha]
    exact h.limUnder_eq
  have hGg : ∀ z₀, G =ᶠ[𝓝[≠] z₀] g := fun z₀ ↦ by
    filter_upwards [(hg z₀).eventually_analyticAt, eventually_ne_notMem_periodLattice L z₀]
      with z h1 h2
    exact hG z h2 _ (h1.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  obtain ⟨A, hA⟩ := exists_eq_polynomial_weierstrassP L (g := G) ((hg 0).congr (hGg 0).symm)
    (fun a ha ↦ by
      obtain ⟨c, hc⟩ := hd a ha
      obtain ⟨h, hh, hgh⟩ := exists_analytic_of_tendsto (hg a) hc
      refine hh.differentiableAt.congr_of_eventuallyEq ?_
      rw [← nhdsNE_sup_pure, EventuallyEq, eventually_sup]
      refine ⟨(hGg a).trans hgh, ?_⟩
      simp only [eventually_pure]
      exact hG a ha _ ((hh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hgh.symm))
    (fun z l hl ↦ by
      by_cases hz : z ∈ L.lattice
      · simp [G, hz, add_mem hz hl]
      · have hz' : z + l ∉ L.lattice := by rwa [L.lattice.add_mem_iff_left hl]
        obtain ⟨c, hc⟩ := hd _ hz'
        rw [hG _ hz' c hc, hG z hz c
          ((hc.comp (tendsto_add_ne z l)).congr fun w ↦ hp w l hl)])
    (fun z ↦ by
      by_cases hz : z ∈ L.lattice
      · simp [G, hz]
      · have hz' : -z ∉ L.lattice := by simpa using hz
        obtain ⟨c, hc⟩ := hd _ hz'
        rw [hG _ hz' c hc, hG z hz c ((hc.comp (tendsto_neg_ne z)).congr fun w ↦ hev w)])
  refine ⟨A, fun z₀ ↦ ?_⟩
  filter_upwards [hGg z₀, eventually_ne_notMem_periodLattice L z₀] with z h1 h2
  rw [← h1, hA z h2]

lemma no_pole_case {g : ℂ → ℂ} (hg : Meromorphic g)
    (hd : ∀ a ∉ L.lattice, ∃ c, Tendsto g (𝓝[≠] a) (𝓝 c))
    (hp : ∀ z, ∀ l ∈ L.lattice, g (z + l) = g z) :
    ∃ A B : Polynomial ℂ, ∀ z₀ : ℂ, ∀ᶠ z in 𝓝[≠] z₀,
      g z = A.eval (℘[L] z) + B.eval (℘[L] z) * ℘'[L] z := by
  have hgn : Meromorphic fun z ↦ g (-z) := fun a ↦
    MeromorphicAt.comp_analyticAt (f := g) (g := fun z ↦ -z) (hg (-a)) (by fun_prop)
  have hdn : ∀ a ∉ L.lattice, ∃ c, Tendsto (fun z ↦ g (-z)) (𝓝[≠] a) (𝓝 c) := fun a ha ↦ by
    obtain ⟨c, hc⟩ := hd (-a) (by simpa using ha)
    exact ⟨c, hc.comp (tendsto_neg_ne a)⟩
  have hpn : ∀ z, ∀ l ∈ L.lattice, g (-(z + l)) = g (-z) := fun z l hl ↦ by
    rw [neg_add, hp _ _ (neg_mem hl)]
  obtain ⟨A, hA⟩ := even_case L (g := fun z ↦ (g z + g (-z)) / 2)
    (fun a ↦ by have := hg a; have := hgn a; fun_prop)
    (fun a ha ↦ by
      obtain ⟨c, hc⟩ := hd a ha
      obtain ⟨c', hc'⟩ := hdn a ha
      exact ⟨_, (hc.add hc').div_const 2⟩)
    (fun z l hl ↦ by simp only [hp z l hl, hpn z l hl])
    (fun z ↦ by simp only [neg_neg, add_comm])
  let o : ℂ → ℂ := fun z ↦ (g z - g (-z)) / 2
  have ho : Meromorphic o := fun a ↦ by have := hg a; have := hgn a; fun_prop
  have hop : ∀ z, ∀ l ∈ L.lattice, o (z + l) = o z := fun z l hl ↦ by
    simp only [o, hp z l hl, hpn z l hl]
  have hon : ∀ z, o (-z) = -o z := fun z ↦ by simp only [o, neg_neg]; ring
  obtain ⟨B, hB⟩ := even_case L (g := fun z ↦ o z / ℘'[L] z)
    (fun a ↦ (ho a).div (L.meromorphic_derivWeierstrassP a))
    (fun a ha ↦ by
      obtain ⟨c, hc⟩ := hd a ha
      obtain ⟨c', hc'⟩ := hdn a ha
      have h1 : Tendsto o (𝓝[≠] a) (𝓝 ((c - c') / 2)) := (hc.sub hc').div_const 2
      have hP := hasDerivAt_derivWeierstrassP L ha
      by_cases h0 : ℘'[L] a = 0
      · have h2 := (derivWeierstrassP_eq_zero_iff L ha).1 h0
        obtain ⟨h, hh, hoh⟩ := exists_analytic_of_tendsto (ho a) h1
        have h3 : Tendsto o (𝓝[≠] a) (𝓝 (h a)) :=
          (hh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hoh.symm
        have h4 : Tendsto (fun z : ℂ ↦ -z + (a + a)) (𝓝[≠] a) (𝓝[≠] a) := by
          have := (tendsto_add_ne (-a) (a + a)).comp (tendsto_neg_ne a)
          simpa [Function.comp_def] using this
        have h5 : Tendsto o (𝓝[≠] a) (𝓝 (-h a)) :=
          (h3.comp h4).neg.congr fun z ↦ by simp [hop _ _ h2, hon]
        have h6 : h a = 0 := CharZero.eq_neg_self_iff.1 (tendsto_nhds_unique h3 h5)
        refine ⟨_, ((hasDerivAt_iff_tendsto_slope.1 hh.differentiableAt.hasDerivAt).div
          (hasDerivAt_iff_tendsto_slope.1 hP) (weierstrassP_second_ne_zero L ha h0)).congr' ?_⟩
        filter_upwards [hoh, self_mem_nhdsWithin] with z hz hza
        have : z - a ≠ 0 := sub_ne_zero.2 hza
        simp only [Pi.div_apply, slope_def_field, h6, h0, sub_zero, hz]
        rw [div_div_div_cancel_right₀ this]
      · exact ⟨_, h1.div (hP.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) h0⟩)
    (fun z l hl ↦ by simp only [hop z l hl, L.derivWeierstrassP_add_coe z ⟨l, hl⟩])
    (fun z ↦ by simp only [hon, derivWeierstrassP_neg, neg_div_neg_eq])
  refine ⟨A, B, fun z₀ ↦ ?_⟩
  filter_upwards [hA z₀, hB z₀,
    (tendsto_two_ne z₀).eventually (eventually_ne_notMem_periodLattice L (z₀ + z₀))]
    with z h1 h2 h3
  have h4 : ℘'[L] z ≠ 0 := fun h ↦
    h3 ((derivWeierstrassP_eq_zero_iff L fun hz ↦ h3 (add_mem hz hz)).1 h)
  rw [← h1, ← h2, div_mul_cancel₀ _ h4]
  simp only [o]
  ring

theorem exists_mul_prod_eq (L : PeriodPair) (φ : ℂ → ℂ) (hφ : GlobalTheory.MomOne.Ell L φ) :
    ∃ (m : ℕ) (P : Fin m → ℂ) (A B : Polynomial ℂ),
      (∀ i, P i ∉ L.lattice ∧ meromorphicOrderAt φ (P i) < 0) ∧
      ∀ z₀ : ℂ, ∀ᶠ z in 𝓝[≠] z₀, φ z * ∏ i, (L.weierstrassP z - L.weierstrassP (P i)) =
        A.eval (L.weierstrassP z) + B.eval (L.weierstrassP z) * L.derivWeierstrassP z := by
  classical
  obtain ⟨hf, hp⟩ := hφ
  have hK := (ZSpan.fundamentalDomain_isBounded L.basis).isCompact_closure
  set K := closure (ZSpan.fundamentalDomain L.basis)
  have hS := hK.finite_sdiff_of_mem_codiscreteWithin
    (hf.meromorphicOn (s := K)).analyticAt_mem_codiscreteWithin
  let S : Finset ℂ := hS.toFinset.filter fun a ↦ a ∉ L.lattice ∧ meromorphicOrderAt φ a < 0
  choose n hn using id hf
  let e := Fintype.equivFin (Σ a : S, Fin (n a))
  let D : ℂ → ℂ := fun z ↦ ∏ a ∈ S, (℘[L] z - ℘[L] a) ^ n a
  have hD : ∀ z, ∏ i, (℘[L] z - ℘[L] (e.symm i).1) = D z := fun z ↦ by
    rw [e.symm.prod_comp (fun x : (Σ a : S, Fin (n a)) ↦ ℘[L] z - ℘[L] x.1), Fintype.prod_sigma]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact Finset.prod_coe_sort S fun a ↦ (℘[L] z - ℘[L] a) ^ n a
  have hK' : ∀ a ∈ K, a ∉ L.lattice → ∃ c, Tendsto (fun z ↦ φ z * D z) (𝓝[≠] a) (𝓝 c) := by
    intro a haK ha
    have hP := L.analyticOnNhd_weierstrassP a ha
    have hP' := hP.continuousAt
    by_cases haS : a ∈ S
    · obtain ⟨u, hu, hu'⟩ := (natCast_le_analyticOrderAt (f := fun z ↦ ℘[L] z - ℘[L] a)
        (z₀ := a) (by fun_prop) (n := 1)).mp
        ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (by fun_prop)).mpr fun i hi ↦ by
          interval_cases i; simp)
      have h1 := (hn a).continuousAt
      have h2 := hu.continuousAt
      have h3 : ContinuousAt (fun z ↦ ((z - a) ^ n a • φ z) * u z ^ n a *
          ∏ b ∈ S.erase a, (℘[L] z - ℘[L] b) ^ n b) a := by fun_prop
      refine ⟨_, (h3.tendsto.congr' ?_).mono_left nhdsWithin_le_nhds⟩
      filter_upwards [hu'] with z hz
      simp only [D]
      rw [← Finset.mul_prod_erase _ _ haS, hz]
      simp only [smul_eq_mul, mul_pow]
      ring
    · have h1 : 0 ≤ meromorphicOrderAt φ a := by
        by_contra h
        refine haS (Finset.mem_filter.2 ⟨?_, ha, not_le.1 h⟩)
        simp only [Set.Finite.mem_toFinset]
        exact ⟨haK, fun h' ↦ h (AnalyticAt.meromorphicOrderAt_nonneg h')⟩
      obtain ⟨c, hc⟩ := (tendsto_nhds_iff_meromorphicOrderAt_nonneg (hf a)).2 h1
      have h2 : ContinuousAt D a := by simp only [D]; fun_prop
      exact ⟨_, hc.mul (h2.tendsto.mono_left nhdsWithin_le_nhds)⟩
  have hper : ∀ z, ∀ l ∈ L.lattice, φ (z + l) * D (z + l) = φ z * D z := fun z l hl ↦ by
    simp only [D, hp l hl z, L.weierstrassP_add_coe z ⟨l, hl⟩]
  obtain ⟨A, B, hAB⟩ := no_pole_case L (g := fun z ↦ φ z * D z)
    (fun a ↦ by
      have h1 := hf a
      have h2 := L.meromorphic_weierstrassP a
      simp only [D]
      fun_prop)
    (fun z hz ↦ by
      have hl : -(ZSpan.floor L.basis z : ℂ) ∈ L.lattice := by
        rw [L.lattice_eq_span_range_basis]; exact neg_mem (ZSpan.floor L.basis z).2
      obtain ⟨c, hc⟩ := hK' (z + -ZSpan.floor L.basis z)
        (by rw [← sub_eq_add_neg]; exact subset_closure (ZSpan.fract_mem_fundamentalDomain L.basis z))
        (by rwa [L.lattice.add_mem_iff_left hl])
      exact ⟨c, (hc.comp (tendsto_add_ne z _)).congr fun w ↦ hper w _ hl⟩)
    hper
  refine ⟨_, fun i ↦ (e.symm i).1, A, B, fun i ↦ (Finset.mem_filter.1 (e.symm i).1.2).2, fun z₀ ↦ ?_⟩
  simpa only [hD] using hAB z₀

end GlobalTheory.EllipticPoles
end
end

section

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical MvPolynomial Formalism.L2.Pj Formalism.L2.Pj.Crude

namespace GlobalTheory.CombMinor

variable {Ty : Type} {r : Ty → ℕ} {n : ℕ} {k : Type} [Field k]

def cMat (τ : Ty) (s : ℕ) (hs : s ≤ r τ) (B : Fin s → Fin n → k) :
    Matrix (Fin s) (Fin s) (MvPolynomial (Letter Ty r n) k) :=
  Matrix.of fun ρ i : Fin s => ∑ b, C (B ρ b) * (X ⟨τ, Fin.castLE hs i, b⟩ : MvPolynomial (Letter Ty r n) k)

theorem det_mem {R : Type} [CommRing R] (S : Subring R) {s : ℕ} (M : Matrix (Fin s) (Fin s) R)
    (h : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply]
  refine S.sum_mem fun π _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (S.prod_mem fun i _ => h _ _) _

theorem cMat_supported (τ : Ty) (s : ℕ) (hs : s ≤ r τ) (B : Fin s → Fin n → k) (S : Set (Letter Ty r n))
    (h : ∀ ρ i b, B ρ b ≠ 0 → (⟨τ, i, b⟩ : Letter Ty r n) ∈ S) :
    (cMat τ s hs B).det ∈ supported k S := by
  refine det_mem (supported k S).toSubring _ fun ρ i => ?_
  change _ ∈ supported k S
  simp only [cMat, Matrix.of_apply]
  refine Subalgebra.sum_mem _ fun b _ => ?_
  by_cases hb : B ρ b = 0
  · rw [hb, C_0, zero_mul]; exact Subalgebra.zero_mem _
  · refine Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) ?_
    rw [supported_eq_adjoin_X]; exact Algebra.subset_adjoin ⟨_, h ρ _ b hb, rfl⟩

theorem cMat_range (O : Subring k) (τ : Ty) (s : ℕ) (hs : s ≤ r τ) (B : Fin s → Fin n → k)
    (h : ∀ ρ b, B ρ b ∈ O) :
    (cMat τ s hs B).det ∈ (MvPolynomial.map (σ := Letter Ty r n) O.subtype).range := by
  refine det_mem _ _ fun ρ i => ?_
  simp only [cMat, Matrix.of_apply]
  refine Subring.sum_mem _ fun b _ => Subring.mul_mem _ ⟨C ⟨B ρ b, h ρ b⟩, by simp⟩ ⟨X _, map_X _ _⟩

theorem cMat_rowShift [Fintype Ty] (τ : Ty) (s : ℕ) (hs : s ≤ r τ) (B : Fin s → Fin n → k)
    (σ : Ty) (i i' : Fin (r σ)) (hii : i' < i) (t : k) :
    rowShift r n k σ i i' t (cMat τ s hs B).det = (cMat τ s hs B).det := by
  rw [AlgHom.map_det]
  by_cases hτ : τ = σ
  · subst hτ
    by_cases hin : i.val < s
    · have hin' : i'.val < s := lt_trans hii hin
      let i0 : Fin s := ⟨i.val, hin⟩
      let i1 : Fin s := ⟨i'.val, hin'⟩
      have hne : i0 ≠ i1 := by
        intro h
        have := congrArg Fin.val h
        simp only [i0, i1] at this
        exact (ne_of_gt hii) (Fin.ext this)
      have hmat : (rowShift r n k τ i i' t).mapMatrix (cMat τ s hs B) =
          (cMat τ s hs B).updateCol i0 (fun p => cMat τ s hs B p i0 +
            (C t : MvPolynomial (Letter Ty r n) k) • cMat τ s hs B p i1) := by
        refine Matrix.ext fun p q => ?_

        simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, cMat, Matrix.of_apply, map_sum, map_mul,
        algHom_C, algebraMap_eq, rowShift, aeval_X, Matrix.updateCol_apply, crSig_iff]
        by_cases hp : q = i0
        · subst hp
          have hc : Fin.castLE hs i0 = i := Fin.ext rfl
          have hc1 : Fin.castLE hs i1 = i' := Fin.ext rfl
          simp only [hc, hc1, if_true, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun b _ => by ring
        · rw [if_neg hp]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [if_neg]
          intro h
          apply hp
          apply Fin.ext
          have := congrArg Fin.val h
          simp only [Fin.val_castLE] at this
          exact this
      rw [hmat]
      exact Matrix.det_updateCol_add_smul_self _ hne (C t)
    · have hmat : (rowShift r n k τ i i' t).mapMatrix (cMat τ s hs B) = cMat τ s hs B := by
        refine Matrix.ext fun p q => ?_

        simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, cMat, Matrix.of_apply, map_sum, map_mul,
        algHom_C, algebraMap_eq, rowShift, aeval_X, crSig_iff]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [if_neg]
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_castLE] at this
        omega
      rw [hmat]
  · have hmat : (rowShift r n k σ i i' t).mapMatrix (cMat τ s hs B) = cMat τ s hs B := by
      refine Matrix.ext fun p q => ?_

      simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, cMat, Matrix.of_apply, map_sum, map_mul,
      algHom_C, algebraMap_eq, rowShift, aeval_X]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [if_neg (crSig_ne hτ)]
    rw [hmat]

theorem cMat_hom [Fintype Ty] (τ : Ty) (s : ℕ) (hs : s ≤ r τ) (B : Fin s → Fin n → k) (σ : Ty) (i0 : ℕ) :
    IsWeightedHomogeneous (crW (r := r) (n := n) σ i0) (cMat τ s hs B).det
      (if τ = σ ∧ i0 < s then 1 else 0) := by
  rw [← mem_weightedHomogeneousSubmodule, Matrix.det_apply]
  refine Submodule.sum_mem _ fun π _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem ?_ _
  rw [mem_weightedHomogeneousSubmodule, ← crRowSum τ σ s i0]
  refine IsWeightedHomogeneous.prod _ _ _ fun j _ => ?_
  rw [← mem_weightedHomogeneousSubmodule]
  simp only [cMat, Matrix.of_apply]
  refine Submodule.sum_mem _ fun b _ => ?_
  rw [C_mul']
  refine Submodule.smul_mem _ _ ?_
  rw [mem_weightedHomogeneousSubmodule]
  exact isWeightedHomogeneous_X k (crW (r := r) (n := n) σ i0) ⟨τ, Fin.castLE hs j, b⟩

theorem prod_det_mem_HaO : ∀ (Ty : Type) [Fintype Ty] (r : Ty → ℕ) (n : ℕ) (k : Type) [Field k] (O : Subring k) (cc : Ty → Ty) (isX : Ty → Prop) (a : Ty → ℕ → ℕ) (A : Type) [Fintype A] (σ : A → Ty) (s : A → ℕ) (hs : ∀ α, s α ≤ r (σ α)) (B : ∀ α, Fin (s α) → Fin n → k) (e : A → ℕ), (∀ α ρ b, B α ρ b ∈ O) → (∀ τ, cc τ ≠ τ) → (∀ α α', e α ≠ 0 → e α' ≠ 0 → σ α' = cc (σ α) → ∀ ρ ρ' b, B α ρ b = 0 ∨ B α' ρ' b = 0) → (∀ (τ : Ty) (i : Fin (r τ)), ∑ α ∈ Finset.univ.filter (fun α => σ α = τ ∧ i.val < s α), e α = a τ i) → (∏ α, (Matrix.of fun ρ i : Fin (s α) => ∑ b, MvPolynomial.C (B α ρ b) * (MvPolynomial.X ⟨σ α, Fin.castLE (hs α) i, b⟩ : MvPolynomial (Letter Ty r n) k)).det ^ e α) ∈ HaO r n k O cc isX a := by
  intro Ty _ r n k _ O cc isX a A _ σ s hs B e hO _ hdis hdeg
  change (∏ α, (cMat (σ α) (s α) (hs α) (B α)).det ^ e α) ∈ _
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · let S : Set (Letter Ty r n) := {ℓ | ∃ α, e α ≠ 0 ∧ σ α = ℓ.1 ∧ ∃ ρ, B α ρ ℓ.2.2 ≠ 0}
    have hS : (∏ α, (cMat (σ α) (s α) (hs α) (B α)).det ^ e α) ∈ supported k S := by
      refine Subalgebra.prod_mem _ fun α _ => ?_
      by_cases he : e α = 0
      · rw [he, pow_zero]; exact Subalgebra.one_mem _
      · exact Subalgebra.pow_mem _ (cMat_supported _ _ _ _ S fun ρ i b hb =>
          (show _ ∈ S from ⟨α, he, rfl, ρ, hb⟩)) _
    generalize (∏ α, (cMat (σ α) (s α) (hs α) (B α)).det ^ e α) = P at hS
    simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker]
    intro τ _ i i'
    simp only [lap, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun b' _ => ?_
    by_cases hb : b = b'
    · subst hb
      have key : pderiv (⟨τ, i, b⟩ : Letter Ty r n) (pderiv (⟨cc τ, i', b⟩ : Letter Ty r n) P) = 0 := by
        by_cases hg : (⟨cc τ, i', b⟩ : Letter Ty r n) ∈ S
        · have hg' : (⟨τ, i, b⟩ : Letter Ty r n) ∉ S := by
            rintro ⟨α, he, hσ, ρ, hρ⟩
            obtain ⟨α', he', hσ', ρ', hρ'⟩ := hg
            rcases hdis α α' he he' (by rw [hσ', hσ]) ρ ρ' b with h | h
            · exact hρ h
            · exact hρ' h
          exact pderiv_eq_zero_of_notMem_vars
            (fun hv => hg' (mem_supported.1 (crPderiv_supported _ hS) hv))
        · rw [pderiv_eq_zero_of_notMem_vars (fun hv => hg (mem_supported.1 hS hv)), map_zero]
      simpa using congrArg (fun x => (1 : k) • x) key
    · simp [Matrix.one_apply_ne hb]
  · intro τ i i' hii t
    rw [map_prod]
    refine Finset.prod_congr rfl fun α _ => ?_
    rw [map_pow, cMat_rowShift _ _ _ _ _ _ _ hii]
  · intro m hm τ i
    rw [← crW_weight]
    have h := IsWeightedHomogeneous.prod Finset.univ (fun α => (cMat (σ α) (s α) (hs α) (B α)).det ^ e α)
      (fun α => e α • (if σ α = τ ∧ i.val < s α then 1 else 0))
      (fun α _ => (cMat_hom (σ α) (s α) (hs α) (B α) τ i.val).pow (e α))
    rw [h (Finsupp.mem_support_iff.1 hm), ← hdeg τ i, Finset.sum_filter]
    refine Finset.sum_congr rfl fun α _ => ?_
    split_ifs <;> simp
  · intro m
    obtain ⟨Q, hQ⟩ : (∏ α, (cMat (σ α) (s α) (hs α) (B α)).det ^ e α) ∈
        (MvPolynomial.map (σ := Letter Ty r n) O.subtype).range :=
      Subring.prod_mem _ fun α _ => Subring.pow_mem _ (cMat_range O _ _ _ _ (hO α)) _
    rw [← hQ, coeff_map]
    exact (Q.coeff m).2

end GlobalTheory.CombMinor
end
end

section

open GlobalTheory.ConvSer

theorem _root_.GlobalTheory.T.exists_integral_poly_of_character' : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (G : Type) [AddCommGroup G] [Fintype G] (x χ : G → K), Function.Injective x → (∀ i j, χ (i + j) = χ i * χ j) → (∀ k : Fin (Fintype.card G), ∃ c : Fin (Fintype.card G) → Fin (Fintype.card G) → K, (∀ a b, ‖c a b‖ ≤ 1) ∧ ∀ i j, x (i + j) ^ (k : ℕ) = ∑ a, ∑ b, c a b * x i ^ (a : ℕ) * x j ^ (b : ℕ)) → ∃ g : Polynomial K, (∀ k, ‖g.coeff k‖ ≤ 1) ∧ ∀ i, g.eval (x i) = χ i := by
  first | exact @GlobalTheory.ConvSer.exists_integral_poly_of_character | exact GlobalTheory.ConvSer.exists_integral_poly_of_character | (intros; apply GlobalTheory.ConvSer.exists_integral_poly_of_character <;> assumption)
end
