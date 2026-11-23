module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicLattices.CompanionTheory
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
import Mathlib.RingTheory.SimpleRing.Principal
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

private theorem adic_bot {X R : Type} [CommRing R] [TopologicalSpace X] (f : X → R) (h : AdicCont ⊥ f) : IsLocallyConstant f := by
  refine IsLocallyConstant.desc f (Ideal.Quotient.mk ((⊥ : Ideal R) ^ 1)) (h 1) ?_
  rw [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker, pow_one]

private theorem rt_wt {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) (h : ∀ i g, Φ.χ i g * Φ.χ i.rev g = Φ.ν g)
    (i j : Fin 4) (g : Γ) : Φ.rt (wt i j) g * Φ.χ j g = Φ.χ i g := by
  have h3 : Φ.χ 3 g = Φ.χ 1 g * Φ.χ 2 g * (Φ.χ 0 g)⁻¹ := by
    have a0 : Φ.χ 0 g * Φ.χ 3 g = Φ.ν g := h 0 g
    have a1 : Φ.χ 1 g * Φ.χ 2 g = Φ.ν g := h 1 g
    rw [a1, ← a0, mul_comm, inv_mul_cancel_left]
  have key : ∀ i : Fin 4, Φ.χ i g = (Φ.χ 0 g * (Φ.χ 1 g)⁻¹) ^ (lamW i) * (Φ.χ 0 g * (Φ.χ 2 g)⁻¹) ^ (muW i) *
      (Φ.χ 0 g * ((Φ.χ 0 g * (Φ.χ 1 g)⁻¹) ^ (lamW 0) * (Φ.χ 0 g * (Φ.χ 2 g)⁻¹) ^ (muW 0))⁻¹) := by
    intro i
    apply Additive.ofMul.injective
    fin_cases i <;> simp [lamW, muW, h3] <;> abel
  show (Φ.χ 0 g * (Φ.χ 1 g)⁻¹) ^ (lamW i - lamW j) * (Φ.χ 0 g * (Φ.χ 2 g)⁻¹) ^ (muW i - muW j) * Φ.χ j g = _
  have ki := key i
  have kj := key j
  generalize Φ.χ 0 g * ((Φ.χ 0 g * (Φ.χ 1 g)⁻¹) ^ (lamW 0) * (Φ.χ 0 g * (Φ.χ 2 g)⁻¹) ^ (muW 0))⁻¹ = c at ki kj
  generalize Φ.χ 0 g * (Φ.χ 1 g)⁻¹ = A at *
  generalize Φ.χ 0 g * (Φ.χ 2 g)⁻¹ = B at *
  rw [ki, kj, zpow_sub, zpow_sub]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem UpperTheory.V.Ws.Lat.entVan :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Φ : Fr O Γ) {k : Type} [Field k] (a : O →+* k) (P : PD Φ.ι Γ k), PreRes Φ a P →
      (∀ i g, Φ.χ i g * Φ.χ i.rev g = Φ.ν g) → OddVan Φ a → EntVan Φ a P := by
  intro O Γ _ _ _ Φ k _ a P hP hm hO i j hw hx m hl
  have hij : i ≠ j := by
    rintro rfl
    revert hw
    simp only [wt, sub_self]
    decide
  have hne : ∀ g, a (Φ.χ j g) ≠ 0 := fun g => ((Φ.χ j g).isUnit.map a).ne_zero
  have hrt : ∀ g, a (Φ.rt (wt i j) g) = a (Φ.χ i g) * (a (Φ.χ j g))⁻¹ := fun g => by
    rw [← rt_wt Φ hm i j g, Units.val_mul, map_mul, mul_assoc, mul_inv_cancel₀ (hne g), mul_one]
  have hmul : ∀ g h, P.r (g * h) i j = a (Φ.χ i g) * P.r h i j + P.r g i j * a (Φ.χ j h) := fun g h => by
    rw [map_mul, Matrix.mul_apply, Finset.sum_eq_add i j hij, hP.diag, hP.diag]
    · exact fun x _ hx' => hx g h x hx'.1 hx'.2
    · simp
    · simp
  have hz : (fun g => P.r g i j * (P.r g j j)⁻¹) ∈ Φ.Zgl a (wt i j) := by
    refine ⟨(adic_bot _ (hP.cont i j)).mul ((adic_bot _ (hP.cont j j)).comp (·⁻¹)), fun g h => ?_, fun g hg => ?_, fun _ => ?_⟩
    · have := hne g
      have := hne h
      simp only [hP.diag, hmul, hrt, map_mul, Units.val_mul]
      field_simp
      ring
    · simp only [hP.pair.kill g hg, Matrix.one_apply_ne hij, zero_mul]
    · simp only [hP.pair.nrm hij, zero_mul]
  obtain ⟨h1, h2⟩ := hO _ hw _ hz m fun v s hs => by
    have := hne s
    simp only [hP.diag, hl v s hs, hrt]
    field_simp
  refine ⟨fun g => ?_, h2⟩
  have := congrFun h1 g
  simp only [hP.diag, Pi.zero_apply, mul_eq_zero, inv_eq_zero, hne g, or_false] at this
  exact this
end

section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Lat

private theorem wt_root : ∀ i j : Fin 4, i ≠ j → wt i j ∈ roots := by decide

private theorem low_case : ∀ i j : Fin 4, i ≠ j → wt i j ∉ qQ → i < j ∨ (i = 2 ∧ j = 1) := by decide

private theorem be_case : ∀ i j : Fin 4, wt i j = wBe → i = 1 ∧ j = 2 := by decide

private theorem vV_case : ∀ i j : Fin 4, wt i j ∉ vV → wt i j ∉ nP ∨ wt i j = -wPs := by decide

private theorem nCo_be {R : Type} [CommRing R] (X : M4 R) : nCo X wBe = 0 := by
  simp [nCo, wBe, UpperTheory.V.GradeZeroInterpolatingElement.wAl, UpperTheory.V.GradeZeroInterpolatingElement.wPs, UpperTheory.V.GradeZeroInterpolatingElement.wTh]

private theorem nCo_nbe {R : Type} [CommRing R] (X : M4 R) : nCo X (-wBe) = X 2 1 := by
  simp [nCo, wBe, UpperTheory.V.GradeZeroInterpolatingElement.wAl, UpperTheory.V.GradeZeroInterpolatingElement.wPs, UpperTheory.V.GradeZeroInterpolatingElement.wTh]

private theorem nCo_nps {R : Type} [CommRing R] (X : M4 R) : nCo X (-wPs) = X 2 0 := by
  simp [nCo, wBe, UpperTheory.V.GradeZeroInterpolatingElement.wAl, UpperTheory.V.GradeZeroInterpolatingElement.wPs, UpperTheory.V.GradeZeroInterpolatingElement.wTh]

private theorem entry_zero_zero_eq_two_two_of_isUp_conj {k : Type} [Field k] (N X : M4 k) (hN : IsLow N) (hN21 : N 2 1 = 0)
    (hX0 : ∀ j, j ≠ 0 → X 0 j = 0) (hX2 : ∀ j, j ≠ 2 → X 2 j = 0)
    (hup : IsUp (adj N * X * N)) (hc : N 2 0 ≠ 0) : X 0 0 = X 2 2 := by
  obtain ⟨hg, hd, hu⟩ := hN
  unfold IsGSp at hg
  have e1 := congrFun (congrFun hg 2) 0
  have e2 := hup 2 0 (by decide)
  simp [Matrix.mul_apply, Fin.sum_univ_four, adj, sgn] at e1 e2
  rw [hu 0 1 (by decide), hd 0, hd 1, hN21, hX0 1 (by decide), hX0 2 (by decide), hX0 3 (by decide),
    hX2 0 (by decide), hX2 1 (by decide), hX2 3 (by decide)] at e2
  rw [hu 0 1 (by decide), hd 0, hd 1, hN21] at e1
  have h : (X 2 2 - X 0 0) * N 2 0 = 0 := by linear_combination e2 - X 0 0 * e1
  rcases mul_eq_zero.mp h with h | h
  · linear_combination -h
  · exact absurd h hc

theorem UpperTheory.V.Ws.Lat.shape :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Φ : Fr O Γ) {k : Type} [Field k] (a : O →+* k) (P : PD Φ.ι Γ k), PreRes Φ a P → EntVan Φ a P →
      wBe ∈ Tight P → -wPs ∈ Tight P → Tight P ⊆ nP →
      Supp nP P.r ∧ (∀ v, SuppM qQ (P.n v)) ∧ Ent P.r wBe ∧
        (Ent P.r (-wPs) ∨ (Supp vV P.r ∧ (∃ v, P.n v 2 0 ≠ 0 ∧ ∀ s ∈ Φ.Gv v, a (Φ.χ 0 s) = a (Φ.χ 2 s)) ∧
          ¬ ∃ m : Φ.ι → k, ∀ v, ∀ s ∈ Φ.Gv v, P.r s 1 2 = m v * (a (Φ.χ 2 s) - a (Φ.χ 1 s)))) := by
  intro O Γ _ _ _ Φ k _ a P hP hE hbe hps hsub
  have hS : Supp nP P.r := by
    intro g i j hij hw
    by_contra h
    exact hw (hsub ⟨wt_root i j hij, Or.inl ⟨g, i, j, rfl, h⟩⟩)
  have hN : ∀ v, SuppM qQ (P.n v) := by
    intro v i j hij hw
    rcases low_case i j hij hw with h | ⟨rfl, rfl⟩
    · exact (hP.pair.low v).2.2 i j h
    · by_contra h
      have hT : -wBe ∈ Tight P := ⟨by decide, Or.inr ⟨v, by rw [nCo_nbe]; exact h⟩⟩
      exact absurd (hsub hT) (by decide)
  have hEbe : Ent P.r wBe := by
    rcases hbe.2 with h | ⟨v, hv⟩
    · exact h
    · exact absurd (nCo_be _) hv
  refine ⟨hS, hN, hEbe, ?_⟩
  by_cases hp : Ent P.r (-wPs)
  · exact Or.inl hp
  right
  obtain ⟨v, hv⟩ := hps.2.resolve_left hp
  rw [nCo_nps] at hv
  have h0 : ∀ g i j, wt i j = -wPs → P.r g i j = 0 := fun g i j hw => by
    by_contra h
    exact hp ⟨g, i, j, hw, h⟩
  refine ⟨?_, ⟨v, hv, ?_⟩, ?_⟩
  · intro g i j hij hw
    rcases vV_case i j hw with h | h
    · exact hS g i j hij h
    · exact h0 g i j h
  · intro s hs
    have key := entry_zero_zero_eq_two_two_of_isUp_conj (P.n v) (P.r s) (hP.pair.low v) (hN v 2 1 (by decide) (by decide)) ?_ ?_
      (hP.pair.flag v s hs) hv
    · rw [hP.diag s 0, hP.diag s 2] at key
      exact key
    · intro j hj
      apply hS s 0 j (Ne.symm hj)
      revert hj
      revert j
      decide
    · intro j hj
      by_cases hw : wt 2 j = -wPs
      · exact h0 s 2 j hw
      · apply hS s 2 j (Ne.symm hj)
        revert hw hj
        revert j
        decide
  · rintro ⟨m, hm⟩
    have hz := (hE 1 2 (by decide) ?_ m hm).1
    · obtain ⟨g, i, j, hw, hne⟩ := hEbe
      obtain ⟨rfl, rfl⟩ := be_case i j hw
      exact hne (hz g)
    · intro g h x hx1 hx2
      have a1 : P.r h 0 2 = 0 := hS h 0 2 (by decide) (by decide)
      have a2 : P.r g 1 3 = 0 := hS g 1 3 (by decide) (by decide)
      fin_cases x
      · simp [a1]
      · exact absurd rfl hx1
      · exact absurd rfl hx2
      · simp [a2]
end
