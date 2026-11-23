module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.Bundle002
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerAdditivityExactSequence
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerIndependenceOfOrder
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.Bundle003
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleFin
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleGr
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.Bundle002
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleNzd
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RulePos
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleSmall
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem UpperTheory.V.Alg.M.kill_pow {O B A κ : Type} [CommRing O] [CommRing B] [CommRing A] [Algebra O A]
    [Algebra B A] [Field κ] [Algebra O κ] (ξ : A →ₐ[O] κ) (N : Submodule B A) (hN : ∀ f ∈ N, ξ f = 0)
    (n : ℕ) (hn : n ≠ 0) : ∀ f ∈ N ^ n, ξ f = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  intro f hf
  rw [pow_succ] at hf
  refine Submodule.mul_induction_on hf (fun a _ b hb => ?_) (fun a b ha hb => ?_)
  · rw [map_mul, hN b hb, mul_zero]
  · rw [map_add (f := _), ha, hb, add_zero]

theorem UpperTheory.V.Alg.M.sign_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (κ : Type) [Field κ] [Algebra O κ] (ξ : A →ₐ[O] κ),
      (¬ NegZero 𝒜 ξ ↔ ∃ f ∈ 𝒜 (-2), ξ f ≠ 0) ∧ (¬ PosZero 𝒜 ξ ↔ ∃ g ∈ 𝒜 2, ξ g ≠ 0) := by
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x hx κ _ _ ξ
  have hp := UpperTheory.V.Alg.M.oz_two_mul_eq_pow O A 𝒜 x hx
  refine ⟨⟨fun h => ?_, ?_⟩, ⟨fun h => ?_, ?_⟩⟩
  · by_contra hc
    push Not at hc
    refine h fun j hj f hf => ?_
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -j by omega)
    have h2 : f * f ∈ oz 𝒜 (-(2 * (n : ℤ))) := by
      have := SetLike.GradedMul.mul_mem hf hf
      rwa [show j + j = -(2 * (n : ℤ)) by omega] at this
    rw [(hp n).1] at h2
    have h3 := UpperTheory.V.Alg.M.kill_pow ξ (oz 𝒜 (-2)) hc n (by omega) _ h2
    rw [map_mul] at h3
    exact mul_self_eq_zero.1 h3
  · rintro ⟨f, hf, h0⟩ h
    exact h0 (h (-2) (by norm_num) f hf)
  · by_contra hc
    push Not at hc
    refine h fun j hj f hf => ?_
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ j by omega)
    have h2 : f * f ∈ oz 𝒜 (2 * (n : ℤ)) := by
      have := SetLike.GradedMul.mul_mem hf hf
      rwa [show j + j = 2 * (n : ℤ) by omega] at this
    rw [(hp n).2] at h2
    have h3 := UpperTheory.V.Alg.M.kill_pow ξ (oz 𝒜 2) hc n (by omega) _ h2
    rw [map_mul] at h3
    exact mul_self_eq_zero.1 h3
  · rintro ⟨f, hf, h0⟩ h
    exact h0 (h 2 (by norm_num) f hf)
end

section

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

section SlopeTestRemainingChoices

variable {O A E τ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing E] [Algebra O E]
  (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] (wt : τ → ℤ) (φ : A →ₐ[O] MvPowerSeries τ E)

private theorem mem_fil_zero (g : MvPowerSeries τ E) : g ∈ fil E wt 0 :=
  fun _ h => absurd h (Nat.not_lt_zero _)

private theorem fil_mul {a b : ℕ} {g h : MvPowerSeries τ E} (hg : g ∈ fil E wt a) (hh : h ∈ fil E wt b) :
    g * h ∈ fil E wt (a + b) := (fil_holds E τ wt a b g h hg hh).1

private theorem fil_of_wt {j : ℤ} {g : MvPowerSeries τ E} (hg : g ∈ wtPart E wt j) : g ∈ fil E wt (-j).toNat :=
  (fil_holds E τ wt 0 0 g g (mem_fil_zero wt g) (mem_fil_zero wt g)).2 j hg

private def sf (j : ℤ) (n : ℕ) : Submodule (𝒜 0) A where
  carrier := {f | f ∈ 𝒜 j ∧ φ f ∈ fil E wt n}
  add_mem' hf hg := ⟨add_mem hf.1 hg.1, by
    rw [map_add φ]
    exact add_mem hf.2 hg.2⟩
  zero_mem' := ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩
  smul_mem' c f hf := by
    refine ⟨(oz 𝒜 j).smul_mem c hf.1, ?_⟩
    show φ ((c : A) * f) ∈ fil E wt n
    have := fil_mul wt (mem_fil_zero wt (φ (c : A))) hf.2
    rwa [zero_add, ← map_mul] at this

private theorem sf_mul {j j' : ℤ} {n n' : ℕ} {M M' : Submodule (𝒜 0) A} (h : M ≤ sf 𝒜 wt φ j n)
    (h' : M' ≤ sf 𝒜 wt φ j' n') : M * M' ≤ sf 𝒜 wt φ (j + j') (n + n') := by
  rw [Submodule.mul_le]
  intro a ha b hb
  obtain ⟨ha1, ha2⟩ := h ha
  obtain ⟨hb1, hb2⟩ := h' hb
  refine ⟨SetLike.GradedMul.mul_mem ha1 hb1, ?_⟩
  rw [map_mul]
  exact fil_mul wt ha2 hb2

private theorem sf_pow {j : ℤ} {n : ℕ} {M : Submodule (𝒜 0) A} (h : M ≤ sf 𝒜 wt φ j n) (k : ℕ) :
    M ^ k ≤ sf 𝒜 wt φ (k * j) (k * n) := by
  induction k with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    rw [Submodule.one_le]
    refine ⟨SetLike.GradedOne.one_mem, ?_⟩
    exact mem_fil_zero wt _
  | succ k ih =>
    have := sf_mul 𝒜 wt φ ih h
    rw [pow_succ]
    convert this using 2 <;> push_cast <;> ring

end SlopeTestRemainingChoices

theorem UpperTheory.V.Alg.M.latfil_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (τ : Type) [Fintype τ] (wt : τ → ℤ) (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)), IsChart0 𝒜 x wt φ →
    ∀ F ∈ 𝒜 (-1), F ∈ satSq x → ∀ (μ : Fin 3 →₀ ℕ) (f : A), f ∈ lat (mN 𝒜 F) μ →
      f ∈ 𝒜 (2 * ((μ 1 : ℤ) - μ 0 - μ 2)) ∧ φ f ∈ fil (FractionRing O) wt (2 * μ 0 + 4 * μ 2) := by
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x hW τ _ wt φ hφ F hF hFs μ f hf
  have h0 : oz 𝒜 (-2) ≤ sf 𝒜 wt φ (-2) 2 := fun g hg => ⟨hg, fil_of_wt wt (hφ.graded (-2) g hg)⟩
  have h1 : oz 𝒜 2 ≤ sf 𝒜 wt φ 2 0 := fun g hg => ⟨hg, mem_fil_zero wt _⟩
  have hF2 : φ F ∈ fil (FractionRing O) wt 2 := (satfil_holds O A 𝒜 x hW τ wt φ hφ).1 F hF hFs
  have h2 : Submodule.span (𝒜 0) {F ^ 2} ⊔ oz 𝒜 (-2) * oz 𝒜 (-2) * oz 𝒜 2 ≤ sf 𝒜 wt φ (-2) 4 := by
    refine sup_le ?_ (sf_mul 𝒜 wt φ (sf_mul 𝒜 wt φ h0 h0) h1)
    rw [Submodule.span_singleton_le_iff_mem]
    refine ⟨sq_mem_neg 𝒜 hF, ?_⟩
    rw [sq, map_mul]
    exact fil_mul wt hF2 hF2
  rw [lat, Fin.prod_univ_three] at hf
  have key := sf_mul 𝒜 wt φ (sf_mul 𝒜 wt φ (sf_pow 𝒜 wt φ h0 (μ 0)) (sf_pow 𝒜 wt φ h1 (μ 1)))
    (sf_pow 𝒜 wt φ h2 (μ 2)) hf
  have e1 : 2 * ((μ 1 : ℤ) - μ 0 - μ 2) = μ 0 * (-2) + μ 1 * 2 + μ 2 * (-2) := by ring
  have e2 : 2 * μ 0 + 4 * μ 2 = μ 0 * 2 + μ 1 * 0 + μ 2 * 4 := by ring
  rw [e1, e2]
  exact key
end

section

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem la_dif_perm {k : ℕ} {l l' : List (Deg k)} (h : l.Perm l') (f : Deg k → ℤ) :
    ∀ m, dif l f m = dif l' f m := by
  induction h with
  | nil => intro m; rfl
  | cons a _ ih => intro m; simp only [dif, ih]
  | swap a b l =>
    intro m
    simp only [dif]
    rw [sub_right_comm m a b]
    ring
  | trans _ _ ih1 ih2 => intro m; rw [ih1, ih2]

private theorem la_hdiff {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]
    (ts : List (Deg k × R)) (G : GMod B R k) :
    ∀ m, Sm.hdiff ts G m = dif (ts.map Prod.fst) (hilb G) m := by
  induction ts with
  | nil => intro m; rw [Sm.hdiff_nil]; rfl
  | cons p ts ih =>
    obtain ⟨d, s⟩ := p
    intro m
    rw [Sm.hdiff_cons, ih, ih]
    rfl

private theorem la_adm {k : ℕ} (X : HidaSetting k) (J : Ideal X.R) (d : Deg k) (a y : X.R)
    (ts : List (Deg k × X.R)) (h : admitted X.𝒜 ((d, a * y) :: ts) J) : admitted X.𝒜 ((d, y) :: ts) J := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, hN.trans (sup_le_sup_left ?_ _)⟩
  rw [secs, Ideal.span_le]
  rintro x ⟨e, he⟩
  rcases List.mem_cons.1 he with h | h
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, List.mem_cons_self⟩)
  · exact Ideal.subset_span ⟨e, List.mem_cons_of_mem _ h⟩

private theorem la_mem {k : ℕ} (X : HidaSetting k) (β : X.B) (c : ℕ) {d : Deg k} {y : X.R} (hy : y ∈ X.𝒜 d) :
    algebraMap X.B X.R β ^ c * y ∈ X.𝒜 d := by
  rw [← map_pow, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ hy

private theorem la_peel {k : ℕ} (X : HidaSetting k) (F : X.Mod) (hF : F.IsGr X.𝒜) (β : X.B)
    (hβ : ∀ y : F.M, algebraMap X.B X.R β • y = 0 → y = 0)
    (hA : admitted X.𝒜 [] (F.quot (algebraMap X.B X.R β)).Ann) (d : Deg k) (hd : 0 ≤ d) (y : X.R)
    (hy : y ∈ X.𝒜 d) (ts : List (Deg k × X.R)) (hV : Valid X.𝒜 ts) (c : ℕ) :
    admitted X.𝒜 ((d, algebraMap X.B X.R β ^ c * y) :: ts) F.Ann →
    ∀ᶠ m in atTop, chi ((d, algebraMap X.B X.R β ^ c * y) :: ts) F m =
      (c : ℤ) * dif (ts.map Prod.fst) (hilb (F.quot (algebraMap X.B X.R β))) m + chi ((d, y) :: ts) F m := by
  have hb : algebraMap X.B X.R β ∈ X.𝒜 0 := by
    rw [X.std.zero]; exact ⟨β, rfl⟩
  have hs := ruleSmall k X ts _ hV ((ruleGr k X F hF).2.2 0 _ hb).1 hA
  induction c with
  | zero => intro _; simp
  | succ c ih =>
    intro h
    rw [pow_succ', mul_assoc] at h ⊢
    have hV' : Valid X.𝒜 ((0, algebraMap X.B X.R β) :: (d, algebraMap X.B X.R β ^ c * y) :: ts) := by
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨le_rfl, hb⟩
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨hd, la_mem X β c hy⟩
      · exact hV p hp
    filter_upwards [euler_rule_product_zero k X ts F d _ _ hV' hF h, ih (la_adm X _ d _ _ ts h), hs] with m h1 h2 h3
    have h4 : chi ts (F.quot (algebraMap X.B X.R β)) m = _ := h3.trans (la_hdiff ts _ m)
    rw [h1, h2, ruleNzd k X ts F 0 _ hβ m, h4]
    push_cast
    ring

theorem UpperTheory.V.Alg.M.la_holds :
    ∀ (k : ℕ) (X : HidaSetting k) (F : X.Mod), F.IsGr X.𝒜 → ∀ β : X.B, (∀ y : F.M, algebraMap X.B X.R β • y = 0 → y = 0) →
      admitted X.𝒜 [] (F.quot (algebraMap X.B X.R β)).Ann → ∀ (d : Deg k), 0 ≤ d → ∀ (n : ℕ) (y : Fin n → X.R) (c : Fin n → ℕ),
      (∀ i, y i ∈ X.𝒜 d) → ∀ us : List (Deg k × X.R), Valid X.𝒜 us →
      admitted X.𝒜 ((List.ofFn fun i => (d, algebraMap X.B X.R β ^ c i * y i)) ++ us) F.Ann →
      ∀ᶠ m in atTop, ((∑ i, c i : ℕ) : ℤ) * dif (List.replicate (n - 1) d ++ us.map Prod.fst) (hilb (F.quot (algebraMap X.B X.R β))) m ≤
        chi ((List.ofFn fun i => (d, algebraMap X.B X.R β ^ c i * y i)) ++ us) F m := by
  intro k X F hF β hβ hA d hd n
  induction n with
  | zero =>
    intro y c _ us hV h
    simpa using rulePos k X us F hV hF (by simpa using h)
  | succ n ih =>
    intro y c hy us hV h
    rw [List.ofFn_succ, List.cons_append] at h ⊢
    set L := (List.ofFn fun i : Fin n => (d, algebraMap X.B X.R β ^ c i.succ * y i.succ)) with hL
    have hVL : Valid X.𝒜 (L ++ us) := by
      intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hp
        exact ⟨hd, la_mem X β _ (hy _)⟩
      · exact hV p hp
    have hc : ∀ l, Valid X.𝒜 l → Valid X.𝒜 ((d, y 0) :: l) := by
      intro l hl p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨hd, hy 0⟩
      · exact hl p hp
    have hP : ((d, y 0) :: (L ++ us)).Perm (L ++ (d, y 0) :: us) := List.perm_middle.symm
    have h' := la_adm X _ d _ _ _ h
    have h'' : admitted X.𝒜 (L ++ (d, y 0) :: us) F.Ann := by
      unfold admitted at h' ⊢
      rwa [← E2.secs_perm hP]
    have hfst : (L ++ us).map Prod.fst = List.replicate n d ++ us.map Prod.fst := by
      rw [List.map_append, hL, List.map_ofFn]
      congr 1
      exact List.ofFn_const n d
    filter_upwards [la_peel X F hF β hβ hA d hd (y 0) (hy 0) _ hVL (c 0) h,
      euler_rule_two_of_graded_finite_iso ruleGr ruleFin ruleIso (euler_additivity_of_rules ruleGr ruleFin ruleIso) k X _ _ F (hc _ hVL) hP hF h',
      ih (fun i => y i.succ) (fun i => c i.succ) (fun i => hy _) _ (hc _ hV) h''] with m h1 h2 h3
    rw [h1, h2, hfst, Fin.sum_univ_succ, Nat.add_sub_cancel, Nat.cast_add, add_mul]
    refine add_le_add le_rfl (le_trans (le_of_eq ?_) h3)
    cases n with
    | zero => simp
    | succ n =>
      congr 1
      refine la_dif_perm ?_ _ m
      rw [Nat.add_sub_cancel, List.replicate_succ, List.map_cons, List.cons_append]
      exact List.perm_middle.symm
end
