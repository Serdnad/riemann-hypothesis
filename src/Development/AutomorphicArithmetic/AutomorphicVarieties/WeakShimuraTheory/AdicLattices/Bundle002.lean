module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicLattices.CompanionTheory
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle004
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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

@[expose] public section

section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Lat

namespace UpperTheory.V.Ws.Lat

private theorem col0 {R : Type} [CommRing R] (n X : M4 R) (hn : IsLow n) (hu : IsUp (adj n * X * n)) (i : Fin 4) :
    X i 0 + X i 1 * n 1 0 + X i 2 * n 2 0 + X i 3 * n 3 0 = n i 0 * (adj n * X * n) 0 0 := by
  have h1 : adj n * n = 1 := by
    have := hn.1
    unfold IsGSp at this
    rwa [one_smul] at this
  have h2 : n * adj n = 1 := mul_eq_one_comm.1 h1
  have h3 : X * n = n * (adj n * X * n) := by
    rw [← mul_assoc, ← mul_assoc, h2, one_mul]
  have h4 := congrFun (congrFun h3 i) 0
  rw [Matrix.mul_apply, Matrix.mul_apply (M := n), Fin.sum_univ_four, Fin.sum_univ_four, hu 1 0 (by decide),
    hu 2 0 (by decide), hu 3 0 (by decide), hn.2.1 0] at h4
  linear_combination h4

private theorem notTight {ι Γ R : Type} [Group Γ] [CommRing R] {P : PD ι Γ R} {w : ℤ × ℤ} (hw : w ∈ roots)
    (h : w ∉ Tight P) : (∀ g i j, wt i j = w → P.r g i j = 0) ∧ ∀ v, nCo (P.n v) w = 0 := by
  simp only [Tight, Set.mem_setOf_eq, not_and, Ent, not_or, not_exists, not_not] at h
  obtain ⟨h1, h2⟩ := h hw
  refine ⟨fun g i j hij => ?_, h2⟩
  by_contra hne
  simp_all

private theorem nCo_al {R : Type} [CommRing R] (X : M4 R) : nCo X (-wAl) = X 1 0 := by
  simp [nCo]

private theorem nCo_th {R : Type} [CommRing R] (X : M4 R) : nCo X (-wTh) = X 3 0 := by
  simp [nCo, wAl, wBe, wPs, wTh]

private theorem wt_th : ∀ i j : Fin 4, wt i j = -wTh → i = 3 ∧ j = 0 := by decide

private theorem wt_al : ∀ i j : Fin 4, wt i j = -wAl → (i = 1 ∧ j = 0) ∨ (i = 3 ∧ j = 2) := by decide

end UpperTheory.V.Ws.Lat

private theorem entry_one_zero_eq_zero_of_nCo_neg_wAl_eq_zero {R : Type} [CommRing R] {X : M4 R} (h : nCo X (-wAl) = 0) : X 1 0 = 0 := by
  rwa [nCo_al] at h

theorem UpperTheory.V.Ws.Lat.noNeg :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Φ : Fr O Γ) {k : Type} [Field k] (a : O →+* k) (P : PD Φ.ι Γ k), PreRes Φ a P → EntVan Φ a P →
      (-wAl ∉ Tight P → -wTh ∉ Tight P) ∧ (wBe ∉ Tight P → wPs ∉ Tight P → -wAl ∉ Tight P) := by
  intro O Γ _ _ _ Φ k _ a P hP hE
  have col : ∀ v, ∀ s ∈ Φ.Gv v, ∀ i, P.r s i 0 + P.r s i 1 * P.n v 1 0 + P.r s i 2 * P.n v 2 0
      + P.r s i 3 * P.n v 3 0 = P.n v i 0 * a ↑((Φ.χ 0) s) := by
    intro v s hs i
    rw [col0 (P.n v) (P.r s) (hP.pair.low v) (hP.pair.flag v s hs) i]
    congr 1
    exact hP.char v s hs 0
  constructor
  · intro hA
    obtain ⟨hAr, hAn⟩ := notTight (by decide) hA
    have r10 : ∀ g, P.r g 1 0 = 0 := fun g => hAr g 1 0 (by decide)
    have r32 : ∀ g, P.r g 3 2 = 0 := fun g => hAr g 3 2 (by decide)
    have n10 : ∀ v, P.n v 1 0 = 0 := fun v => entry_one_zero_eq_zero_of_nCo_neg_wAl_eq_zero (hAn v)
    obtain ⟨hr30, hm⟩ := hE 3 0 (by decide) (by
        intro g h x hx3 hx0
        fin_cases x <;> simp [r10, r32] at hx0 hx3 ⊢) (fun v => P.n v 3 0) (by
        intro v s hs
        have c := col v s hs 3
        rw [n10 v, r32 s, hP.diag s 3] at c
        linear_combination c)
    intro hmem
    obtain ⟨-, hEnt | ⟨v, hv⟩⟩ := hmem
    · obtain ⟨g, i, j, hij, hne⟩ := hEnt
      obtain ⟨rfl, rfl⟩ := wt_th i j hij
      exact hne (hr30 g)
    · rw [nCo_th] at hv
      exact hv (congrFun hm v)
  · intro hB hPs
    obtain ⟨hBr, -⟩ := notTight (by decide) hB
    obtain ⟨hPr, -⟩ := notTight (by decide) hPs
    have r12 : ∀ g, P.r g 1 2 = 0 := fun g => hBr g 1 2 (by decide)
    have r13 : ∀ g, P.r g 1 3 = 0 := fun g => hPr g 1 3 (by decide)
    obtain ⟨hr10, hm⟩ := hE 1 0 (by decide) (by
        intro g h x hx1 hx0
        fin_cases x <;> simp [r12, r13] at hx0 hx1 ⊢) (fun v => P.n v 1 0) (by
        intro v s hs
        have c := col v s hs 1
        rw [r12 s, r13 s, hP.diag s 1] at c
        linear_combination c)
    have hr32 : ∀ g, P.r g 3 2 = 0 := by
      intro g
      obtain ⟨-, -, -, -, -, -, hinv, -⟩ := grp k
      have e := hinv _ (P.r g) (P.r g⁻¹) (hP.pair.mult g) (by rw [← map_mul, mul_inv_cancel, map_one])
      have e' := congrFun (congrFun e 1) 0
      rw [adj_apply] at e'
      simpa [sgn, Fin.rev, hr10] using e'
    intro hmem
    obtain ⟨-, hEnt | ⟨v, hv⟩⟩ := hmem
    · obtain ⟨g, i, j, hij, hne⟩ := hEnt
      rcases wt_al i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hne (hr10 g)
      · exact hne (hr32 g)
    · rw [nCo_al] at hv
      exact hv (congrFun hm v)
end

section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Lat

namespace UpperTheory.V.Ws.Lat

section
variable {R K : Type} [CommRing R] [CommRing K] {f : R →+* K} {t : Kˣ × Kˣ}

private theorem wt_self (i : Fin 4) : wt i i = 0 := by revert i; decide

private theorem tc_entry {X X' : M4 R} (h : X'.map f = tconj t (X.map f)) (i j : Fin 4) :
    f (X' i j) = (wv t (wt i j) : K) * f (X i j) := congrFun (congrFun h i) j

private theorem tc_diag (hf : Function.Injective f) {X X' : M4 R} (h : X'.map f = tconj t (X.map f)) (i : Fin 4) :
    X' i i = X i i := by
  apply hf
  rw [tc_entry h, wt_self]
  simp [wv]

private theorem tc_zero (hf : Function.Injective f) {X X' : M4 R} (h : X'.map f = tconj t (X.map f)) {i j : Fin 4}
    (h0 : X i j = 0) : X' i j = 0 := by
  apply hf
  rw [tc_entry h, h0]
  simp

private theorem tc_mul {X X' Y Y' : M4 R} (h : X'.map f = tconj t (X.map f)) (h' : Y'.map f = tconj t (Y.map f)) :
    (X' * Y').map f = tconj t ((X * Y).map f) := by
  obtain ⟨-, -, -, -, -, -, -, -, hmul, -⟩ := grp K
  rw [Matrix.map_mul, Matrix.map_mul, h, h', hmul]

private theorem tc_adj {X X' : M4 R} (h : X'.map f = tconj t (X.map f)) :
    (adj X').map f = tconj t ((adj X).map f) := by
  obtain ⟨-, -, -, -, -, hmap, -⟩ := grp R
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hadj, -⟩ := grp K
  rw [← hmap, ← hmap, h, hadj]

private theorem tc_scalar (hf : Function.Injective f) {X X' : M4 R} (h : X'.map f = tconj t (X.map f)) {c : R}
    (hX : X = c • (1 : M4 R)) : X' = c • (1 : M4 R) := by
  subst hX
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [tc_diag hf h]
  · rw [tc_zero hf h (by simp [Matrix.one_apply_ne hij])]
    simp [Matrix.one_apply_ne hij]

private theorem tc_gsp (hf : Function.Injective f) {X X' : M4 R} (h : X'.map f = tconj t (X.map f)) {c : R}
    (hX : IsGSp c X) : IsGSp c X' := tc_scalar hf (tc_mul (tc_adj h) h) hX

end

end UpperTheory.V.Ws.Lat

theorem UpperTheory.V.Ws.Lat.tcPair :
    ∀ {O Γ R K : Type} [CommRing O] [Group Γ] [CommRing R] [CommRing K] (Φ : Fr O Γ) (a : O →+* R) (f : R →+* K), Function.Injective f →
      ∀ (t : Kˣ × Kˣ) (P P' : PD Φ.ι Γ R), TConj f t P P' → Φ.IsPair a P →
      Φ.IsPair a P' ∧ (∀ g i, P'.r g i i = P.r g i i) ∧ (∀ v i s, P'.ψ v i s = P.ψ v i s) ∧ IsConj4 (mapRep f P.r) (mapRep f P'.r) := by
  intro O Γ R K _ _ _ _ Φ a f hf t P P' hT hP
  obtain ⟨hr, hn⟩ := hT
  have hY : ∀ v s, (adj (P'.n v) * P'.r s * P'.n v).map f
      = tconj t ((adj (P.n v) * P.r s * P.n v).map f) := fun v s =>
    tc_mul (tc_mul (tc_adj (hn v)) (hr s)) (hn v)
  have hpsi : ∀ v i s, P'.ψ v i s = P.ψ v i s := fun v i s => tc_diag hf (hY v s) i
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun g i => tc_diag hf (hr g) i, hpsi, ?_⟩
  · intro g
    exact tc_gsp hf (hr g) (hP.mult g)
  · intro g hg
    have := tc_scalar hf (hr g) (c := 1) (by rw [one_smul]; exact hP.kill g hg)
    rwa [one_smul] at this
  · intro i j hij
    exact tc_zero hf (hr Φ.g0) (hP.nrm hij)
  · intro v
    obtain ⟨h1, h2, h3⟩ := hP.low v
    refine ⟨tc_gsp hf (hn v) h1, fun i => ?_, fun i j hij => tc_zero hf (hn v) (h3 i j hij)⟩
    rw [tc_diag hf (hn v), h2]
  · intro v s hs i j hij
    exact tc_zero hf (hY v s) (hP.flag v s hs i j hij)
  · intro v s hs i
    rw [hpsi]
    exact hP.mu v s hs i
  · obtain ⟨u, hu⟩ := (grp K).2.2.2.2.2.2.2.2.2.2.2.2 t
    refine ⟨u, fun g => ?_⟩
    change (P'.r g).map f = _
    rw [hr g, hu]
    rfl
end

section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Lat

namespace UpperTheory.V.Ws.Lat

private theorem lower_symplectic_entries_eq {R : Type} [CommRing R] {X : M4 R} (h : IsLow X) : X 3 2 = -X 1 0 ∧ X 3 1 = X 2 0 - X 1 0 * X 2 1 := by
  obtain ⟨hg, hd, hu⟩ := h
  have e32 := congrFun (congrFun hg 3) 2
  have e31 := congrFun (congrFun hg 3) 1
  simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, hd, Fin.rev] at e32 e31
  have a := hu 1 2 (by decide)
  have b := hu 0 1 (by decide)
  have c := hu 0 2 (by decide)
  rw [a, c] at e32
  rw [b] at e31
  constructor
  · linear_combination e32
  · linear_combination e31

private theorem lowMem {K : Type} [Field K] (V : ValuationSubring K) (t : Kˣ × Kˣ) {X : M4 V} (h : IsLow X)
    (hw : ∀ w ∈ nM, (wv t w : K) * ((nCo X w : V) : K) ∈ V) (i j : Fin 4) : (wv t (wt i j) : K) * (X i j : K) ∈ V := by
  have hA := hw (-wAl) (by simp [nM])
  have hB := hw (-wBe) (by simp [nM])
  have hP := hw (-wPs) (by simp [nM])
  have hT := hw (-wTh) (by simp [nM])
  simp [nCo, wAl, wBe, wPs, wTh, wv] at hA hB hP hT
  obtain ⟨l1, l2⟩ := lower_symplectic_entries_eq h
  obtain ⟨_, hd, hu⟩ := h
  fin_cases i <;> fin_cases j <;> simp [wt, lamW, muW, wv, hd, hu]
  · exact hA
  · exact hP
  · exact hB
  · exact hT
  · rw [l2]
    have h1 : (t.1 : K) ≠ 0 := t.1.ne_zero
    have e : (↑t.2)⁻¹ * ((↑(X 2 0 - X 1 0 * X 2 1 : V) : K))
        = (↑t.2)⁻¹ * ↑(X 2 0) - ((↑t.1)⁻¹ * ↑(X 1 0)) * (↑t.1 * (↑t.2)⁻¹ * ↑(X 2 1)) := by
      push_cast
      field_simp
    rw [e]
    exact sub_mem hP (mul_mem hA hB)
  · rw [l1]
    push_cast
    rw [mul_neg]
    exact neg_mem hA

end UpperTheory.V.Ws.Lat

theorem UpperTheory.V.Ws.Lat.tcEx :
    ∀ {ι Γ K : Type} [Group Γ] [Field K] (V : ValuationSubring K) (t : Kˣ × Kˣ) (P : PD ι Γ V), (∀ v, IsLow (P.n v)) →
      (∀ g i j, V.valuation ((wv t (wt i j) : K) * (P.r g i j : K)) ≤ 1) →
      (∀ v, ∀ w ∈ nM, V.valuation ((wv t w : K) * ((nCo (P.n v) w : V) : K)) ≤ 1) → ∃ P' : PD ι Γ V, TConj V.subtype t P P' := by
  intro ι Γ K _ _ V t P hl hr hn
  simp only [ValuationSubring.valuation_le_one_iff] at hr hn
  obtain ⟨-, -, -, -, -, -, -, -, hmul, hone, -⟩ := grp K
  let r : Γ → M4 V := fun g => Matrix.of fun i j => ⟨_, hr g i j⟩
  have hrm : ∀ g, (r g).map V.subtype = tconj t ((P.r g).map V.subtype) := fun g => rfl
  have inj : Function.Injective fun X : M4 V => X.map V.subtype := Matrix.map_injective V.subtype_injective
  have h1 : (1 : M4 V).map V.subtype = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  refine ⟨⟨⟨⟨r, inj ?_⟩, fun g h => inj ?_⟩, fun v => Matrix.of fun i j => ⟨_, lowMem V t (hl v) (hn v) i j⟩⟩,
    fun g => rfl, fun v => rfl⟩
  · show (r 1).map V.subtype = (1 : M4 V).map V.subtype
    rw [hrm, map_one, h1, hone]
  · show (r (g * h)).map V.subtype = (r g * r h).map V.subtype
    rw [Matrix.map_mul, hrm, hrm, hrm, map_mul, Matrix.map_mul, hmul]
end
