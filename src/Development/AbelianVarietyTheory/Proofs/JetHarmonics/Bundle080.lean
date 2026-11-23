module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle072
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle073
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsAreEigenvectors
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UniversalStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle036
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle052
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle074
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle007
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle069
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.Integral
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
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowAt

private theorem gap_step (r : ℕ) (a : ℕ → ℕ) (h : ∀ i j, i ≤ j → j < r → a j ≤ a i) (k : ℕ) :
    gap r a (k + 1) + (if k + 1 < r then a (k + 1) else 0) = (if k < r then a k else 0) := by
  unfold gap
  by_cases h1 : k + 1 < r
  · have := h k (k + 1) (by omega) h1
    rw [if_pos (show 1 ≤ k + 1 ∧ k + 1 ≤ r by omega), if_pos h1, if_pos (show k < r by omega),
      Nat.add_sub_cancel]
    omega
  · by_cases h2 : k < r
    · rw [if_pos (show 1 ≤ k + 1 ∧ k + 1 ≤ r by omega), if_neg h1, if_pos h2, Nat.add_sub_cancel]
      omega
    · rw [if_neg (show ¬ (1 ≤ k + 1 ∧ k + 1 ≤ r) by omega), if_neg h1, if_neg h2]

private theorem gap_tele (r : ℕ) (a : ℕ → ℕ) (h : ∀ i j, i ≤ j → j < r → a j ≤ a i) (i K : ℕ)
    (hK : i ≤ K) :
    ∑ k ∈ Finset.Icc (i + 1) K, gap r a k + (if K < r then a K else 0)
      = (if i < r then a i else 0) := by
  induction K, hK using Nat.le_induction with
  | base => simp
  | succ K hK ih =>
    rw [Finset.sum_Icc_succ_top (by omega), add_assoc, gap_step r a h K, ih]

private theorem gap_parts (r : ℕ) (a : ℕ → ℕ) (h : ∀ i j, i ≤ j → j < r → a j ≤ a i) (K : ℕ) :
    ∑ k ∈ Finset.Icc 1 K, k * gap r a k + K * (if K < r then a K else 0)
      = ∑ i ∈ Finset.range K, (if i < r then a i else 0) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega), add_assoc, ← mul_add, gap_step r a h K,
      Finset.sum_range_succ, ← ih]
    ring

theorem gap_sums : ∀ (r : ℕ) (a : ℕ → ℕ), (∀ i j, i ≤ j → j < r → a j ≤ a i) → (∀ k, gap r a k ≠ 0 → 1 ≤ k ∧ k ≤ r) ∧ ∀ K, r ≤ K → (∀ i, i < r → ∑ k ∈ Finset.Icc (i + 1) K, gap r a k = a i) ∧ ∑ k ∈ Finset.Icc 1 K, k * gap r a k = ∑ i : Fin r, a i := by
  intro r a h
  refine ⟨fun k hk => ?_, fun K hK => ⟨fun i hi => ?_, ?_⟩⟩
  · by_contra hc
    exact hk (by unfold gap; rw [if_neg hc])
  · have := gap_tele r a h i K (by omega)
    rw [if_neg (show ¬ K < r by omega), if_pos hi, add_zero] at this
    exact this
  · have := gap_parts r a h K
    rw [if_neg (show ¬ K < r by omega), mul_zero, add_zero] at this
    rw [this, Fin.sum_univ_eq_sum_range a r, ← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega

end GlobalTheory.RowAt
end

section

set_option autoImplicit false

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowAt

theorem supply_extend :
    ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (Pl : Type) [Fintype Pl] (Z : Finset Pl) (n m : ℕ) (big : Pl → Fin 2 → ZMod d → Prop) (rk : Pl → Fin 2 → ZMod d → ℕ) (ga : Pl → Fin 2 → ZMod d → ℕ → ℕ) (nW : ℕ) (ν : ℝ), Z.Nonempty → Supply V d Z Finset.univ n m (fun o => big o.1) (fun o => rk o.1) (fun o => ga o.1) nW ν → Supply V d Pl Z n m big rk ga nW ν := by
  intro C _ V d _ Pl _ Z n m big rk ga nW ν hZ h
  obtain ⟨I, J, fI, fJ, X, F, h1, h2, h3⟩ := h
  obtain ⟨z0, hz0⟩ := hZ
  obtain ⟨q, hq⟩ : ∃ q : Pl → Z, ∀ o : Z, q o.1 = o :=
    ⟨fun o => if h : o ∈ Z then ⟨o, h⟩ else ⟨z0, hz0⟩, fun o => by simp [o.2]⟩
  refine ⟨fun o => I (q o), fun o => J (q o), fun o => fI (q o), fun o => fJ (q o), fun o => X (q o),
    fun o => F (q o), fun o => h1 (q o), ?_, ?_⟩
  · intro o ho g s
    have e := h2 (q o) (Finset.mem_univ _) g s
    have e' : (q o).1 = o := congrArg Subtype.val (hq ⟨o, ho⟩)
    simp only [e'] at e
    exact e
  · intro L hA hR hW
    have key := h3 (fun o => L o.1) ?_ ?_ ?_
    · rw [← Finset.sum_coe_sort Z]
      exact key
    · intro o _ p hp
      have e := hA o.1 o.2 p hp
      have gen : ∀ o' : Z, o' = o → p.1.Attains (X o') (F o') p.2 → p.1.Attains (X o) (F o) p.2 := by
        intro o' ho' h'
        subst ho'
        exact h'
      exact gen _ (hq o) e
    · rw [← Finset.sum_coe_sort Z] at hR
      refine le_trans (le_of_eq ?_) hR
      refine Finset.sum_congr rfl fun o _ => ?_
      simp only [(h1 _).1]
    · intro o _ g a k
      have e := hW o.1 o.2 g a k
      have gen : ∀ o' : Z, o' = o → ((L o.1).map fun p => p.1.wt (X o') g a k).sum = ga o.1 g a k →
          ((L o.1).map fun p => p.1.wt (X o) g a k).sum = ga o.1 g a k := by
        intro o' ho' h'
        subst ho'
        exact h'
      exact gen _ (hq o) e

end GlobalTheory.RowAt
end

section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.UnrIdem

theorem exists_idem (E : Type) [Field E] [NumberField E] (l : ℕ) (hl : l.Prime)
    (hd : ¬ (l : ℤ) ∣ NumberField.discr E) (P : Ideal (𝓞 E)) [hP : P.IsPrime] (hlP : (l : 𝓞 E) ∈ P) :
    ∃ ε : 𝓞 E, (∃ y, ε * ε - ε = (l : 𝓞 E) * y) ∧ ε - 1 ∈ P ∧ ∀ x ∈ P, ∃ y, ε * x = (l : 𝓞 E) * y := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hun : Algebra.IsUnramifiedAt ℤ P :=
    (NumberField.not_dvd_discr_iff_forall_mem E (𝓞 E) hp).mp hd P hP (by simpa using hlP)
  have hov : P.LiesOver (Ideal.span {(l : ℤ)}) :=
    (Ideal.liesOver_span_iff hP.ne_top hp).mpr (by simpa using hlP)
  have hmap : (Ideal.span {(l : ℤ)}).map (algebraMap ℤ (𝓞 E)) = Ideal.span {(l : 𝓞 E)} := by
    rw [Ideal.map_span]; simp
  have hl0 : (l : 𝓞 E) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hne : (Ideal.span {(l : ℤ)}).map (algebraMap ℤ (𝓞 E)) ≠ ⊥ := by
    rw [hmap]; simpa using hl.ne_zero
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    exact hl0 (by simpa using hlP)
  have := hP.isMaximal hP0
  obtain ⟨Q, h₁, h₂⟩ := Ideal.eq_prime_pow_mul_coprime hne P
  rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count _ _ hne,
    Ideal.ramificationIdx_eq_one P ℤ, pow_one, hmap] at h₂
  obtain ⟨p, hpP, q, hqQ, hpq⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp h₁)
  have key : ∀ x ∈ P, ∃ y, q * x = (l : 𝓞 E) * y := by
    intro x hx
    have : x * q ∈ Ideal.span {(l : 𝓞 E)} := h₂ ▸ Ideal.mul_mem_mul hx hqQ
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp this
    exact ⟨y, by rw [mul_comm, hy]⟩
  have hq1 : q - 1 ∈ P := by
    have : q - 1 = -p := by rw [← hpq]; ring
    rw [this]; exact P.neg_mem hpP
  refine ⟨q, ?_, hq1, key⟩
  obtain ⟨y, hy⟩ := key _ hq1
  exact ⟨y, by rw [← hy]; ring⟩

variable {C : Type} [Field C] {V : VF C}

theorem ge_int {x : C} (hx : IsIntegral ℤ x) : V.Ge 0 x := by
  have h1 : IsIntegral (Valuation.integer (V.v : Valuation C (Multiplicative (WithTop ℝ)ᵒᵈ))) x := hx.tower_top
  exact (Valuation.integer.integers (V.v : Valuation C (Multiplicative (WithTop ℝ)ᵒᵈ))).mem_of_integral h1

theorem mm_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) := V.v.map_lt_add ha hb

theorem mm_mul {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by
  unfold VF.MM at *
  unfold VF.Ge at ha
  rw [V.v.map_mul]
  exact lt_of_lt_of_le hb (le_add_of_nonneg_left (by simpa using ha))

def ker (V : VF C) {R : Type} [CommRing R] (f : R →+* C) (hf : ∀ x, V.Ge 0 (f x)) : Ideal R where
  carrier := {x | V.MM (f x)}
  add_mem' := fun {a b} ha hb => by
    show V.MM (f (a + b))
    rw [map_add (f := _)]; exact mm_add ha hb
  zero_mem' := by
    show V.MM (f 0)
    simp [VF.MM]
  smul_mem' := fun c x hx => by
    show V.MM (f (c * x))
    rw [map_mul]; exact mm_mul (hf c) hx

theorem ker_isPrime {R : Type} [CommRing R] (f : R →+* C) (hf : ∀ x, V.Ge 0 (f x)) : (ker V f hf).IsPrime := by
  refine ⟨(Ideal.ne_top_iff_one _).mpr ?_, fun {a b} hab => ?_⟩
  · show ¬ V.MM (f 1)
    simp [VF.MM]
  · change V.MM (f (a * b)) at hab
    show V.MM (f a) ∨ V.MM (f b)
    have ha := hf a
    have hb := hf b
    unfold VF.MM VF.Ge at *
    rw [map_mul, V.v.map_mul] at hab
    by_contra hc
    push Not at hc
    exact absurd hab (not_lt.mpr (add_nonpos hc.1 hc.2))

end GlobalTheory.UnrIdem

open GlobalTheory.UnrIdem in
theorem GlobalTheory.exists_idempotent_of_unramified_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (c : Coeff lv) (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ¬ (V.l : ℤ) ∣ NumberField.discr E → ∀ (d : ℕ) [NeZero d] (tau : ZMod d → (E →+* ℂ)), FrobOrd V io ι tau → ∃ ε : 𝓞 E, (∃ y, ε * ε - ε = (V.l : 𝓞 E) * y) ∧ (∀ a, V.MM (emA3 io ι (tau a) ε - 1)) ∧ ∀ x : 𝓞 E, (∀ a, V.MM (emA3 io ι (tau a) x)) → ∃ y, ε * x = (V.l : 𝓞 E) * y := by
  intro E _ _ _ H lv c T io C _ _ V ι _ hd d _ tau hF
  have hint : ∀ τ x, V.Ge 0 (emA3 io ι τ x) := fun τ x =>
    ge_int ((RingOfIntegers.isIntegral x).map (emA3 io ι τ).toIntAlgHom)
  have hstep : ∀ x s, V.MM (emA3 io ι (tau s) x) → V.MM (emA3 io ι (tau (s + 1)) x) := by
    intro x s hs
    have h1 := hF s x
    have h2 : V.MM (emA3 io ι (tau s) x ^ V.l) := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero V.l_prime.ne_zero
      rw [hk, pow_succ]
      exact mm_mul ((hint _ _).pow k) hs
    simpa using mm_add h1 h2
  have hall : ∀ x, V.MM (emA3 io ι (tau 0) x) → ∀ a, V.MM (emA3 io ι (tau a) x) := by
    intro x h0 a
    have : ∀ n : ℕ, V.MM (emA3 io ι (tau (n : ZMod d)) x) := by
      intro n
      induction n with
      | zero => simpa using h0
      | succ n ih => push_cast; exact hstep x _ ih
    simpa using this a.val
  have hP := ker_isPrime (V := V) (emA3 io ι (tau 0)) (hint _)
  obtain ⟨ε, h1, h2, h3⟩ := exists_idem E V.l V.l_prime hd (ker V (emA3 io ι (tau 0)) (hint _)) (by
    show V.MM (emA3 io ι (tau 0) (V.l : 𝓞 E))
    rw [map_natCast]
    unfold VF.MM
    rw [V.v_l]
    exact zero_lt_one)
  refine ⟨ε, h1, fun a => ?_, fun x hx => h3 x (hx 0)⟩
  have := hall _ h2 a
  rwa [map_sub, map_one] at this
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

theorem _root_.GlobalTheory.T.truncation_frames_local_series : LinkEpsSt := by
  first | exact @GlobalTheory.LinkEps.linkEps | exact GlobalTheory.LinkEps.linkEps | (intros; apply GlobalTheory.LinkEps.linkEps <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

theorem _root_.GlobalTheory.T.universalJets_reindex_fin : UnivConvSt := by
  first | exact @GlobalTheory.PowGerm.univConv | exact GlobalTheory.PowGerm.univConv | (intros; apply GlobalTheory.PowGerm.univConv <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

theorem _root_.GlobalTheory.T.exists_universalJetCoordinates_pullback : ∀ (V V' : Type) [CommRing V] [IsLocalRing V] [CommRing V'] (φ : V →+* V') (G : Over (Sp V)) [GrpObj G] (G' : Over (Sp V')) [GrpObj G'] (F : G'.left ⟶ G.left), IsGrpPullback G' G (spMap φ) F → ∀ (κ : Type) (z : GlobalTheory.PowGerm.JetPts G κ), GlobalTheory.PowGerm.IsUnivJ G κ z → ∃ z' : GlobalTheory.PowGerm.JetPts G' κ, GlobalTheory.PowGerm.IsUnivJ G' κ z' ∧ ∀ m, (z' m).left ≫ F = spMap (jetCoef φ κ m) ≫ (z m).left := by
  first | exact @GlobalTheory.UnivJetBaseChange.exists_univ_pullback | exact GlobalTheory.UnivJetBaseChange.exists_univ_pullback | (intros; apply GlobalTheory.UnivJetBaseChange.exists_univ_pullback <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

theorem _root_.GlobalTheory.T.germ_existsUnique_linear : AGermSt := by
  first | exact @GlobalTheory.GermBasic.main | exact GlobalTheory.GermBasic.main | (intros; apply GlobalTheory.GermBasic.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

theorem _root_.GlobalTheory.T.integral_chart_directions_are_eigenvectors : EigDirSt := by
  first | exact @GlobalTheory.PowGerm.eigDirSt | exact GlobalTheory.PowGerm.eigDirSt | (intros; apply GlobalTheory.PowGerm.eigDirSt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

theorem _root_.GlobalTheory.T.universal_statement : UnivSt := by
  first | exact @GlobalTheory.PowGerm.univSt_holds | exact GlobalTheory.PowGerm.univSt_holds | (intros; apply GlobalTheory.PowGerm.univSt_holds <;> assumption)
end

section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PairingLinear

def linOfComb {F M N : Type} [Field F] [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N] (f : M → N)
    (h : ∀ (l : ℕ) (c : Fin l → F) (s : Fin l → M), f (∑ i, c i • s i) = ∑ i, c i • f (s i)) : M →ₗ[F] N where
  toFun := f
  map_add' a b := by simpa using h 2 ![1, 1] ![a, b]
  map_smul' c a := by simpa using h 1 ![c] ![a]

theorem exists_germ_linearMap (hL : Laws) (hL2 : Laws2) (hL4 : Laws4) (hT : TwistBaseChangeStatement)
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V]
    (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Sp V))
    [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (κ : Type) [Fintype κ] [DecidableEq κ]
    (z : JetPts G κ) (hz : IsUnivJ G κ z) (τ : Frames U.LG.L z) (hτ : τ.Gen) (hτT : τ.Trunc)
    (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F]
    (q : ℕ) (hq : 1 ≤ q) :
    ∃ gm : Fam D.toPre F q →ₗ[F] MvPowerSeries κ F,
      (∀ t σ' h, U.ExpandsG F q σ' t → GermA U.toUnifPre z τ F q σ' h → h = gm t) ∧
      ∀ t, ∃ σ', U.ExpandsG F q σ' t ∧ GermA U.toUnifPre z τ F q σ' (gm t) := by
  obtain ⟨huniq, hlin, hex⟩ := GlobalTheory.GermBasic.main V D A G U κ z hz τ hτ F q
  have hbij := (GlobalTheory.expandsG_bijective_of_dvr hL hL2 hL4 hT V D A G U F q hq).2
  choose S hS hSu using hbij
  choose Γg hΓ using hex hτT
  have key : ∀ t σ' h, U.ExpandsG F q σ' t → GermA U.toUnifPre z τ F q σ' h → h = Γg (S t) := by
    intro t σ' h he hg
    obtain rfl := hSu t σ' he
    exact huniq _ _ _ hg (hΓ _)
  refine ⟨linOfComb (fun t => Γg (S t)) fun l c s => ?_, key, fun t => ⟨S t, hS t, hΓ _⟩⟩
  let σ' : U.SecGF F q := GlobalTheory.ExpansionLinear.secComb
    (fun i => scal (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left (c i)) (fun i => S (s i))
  exact (key _ σ' _
    (GlobalTheory.GroupExpansionLinear.expandsG_sum V D A G U F q l c (fun i => S (s i)) s σ' (fun i => hS _) (fun _ => rfl))
    (hlin l c (fun i => S (s i)) _ σ' (fun i => hΓ _) (fun _ => rfl))).symm

end GlobalTheory.PairingLinear
end
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.numericalFamily_shape_gaps : ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ), Num k r lam u b bv ga h q0 → (bv ≤ b ∧ (1000000 : ℝ) ≤ bv ∧ ((2 * r + k + 1) : ℝ) ≤ b ∧ 100 * (q0 : ℝ) ≤ bv ∧ GapOK k r (h / 2)) ∧ ∀ ν : Fin (2 * r + k + 1) → ℤ, n1 ν ≤ q0 → Formalism.QuantumDeterminants.IsHCParam (fun a => lam a + (ν a : ℝ)) ∧ Shape (PI.BesselPeriodGGP.eps48 k r) k (fun a => lam a + (ν a : ℝ)) bv ∧ Formalism.QuantumDeterminants.GapAtLeast (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (h / 2) ∧ ∀ a c, a < c → 2 ≤ (lam a + (ν a : ℝ)) - (lam c + (ν c : ℝ)) := by
  first | exact @GlobalTheory.NumFam.num_fam | exact GlobalTheory.NumFam.num_fam | (intros; apply GlobalTheory.NumFam.num_fam <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.numericalFamily_productBound_constant_le : ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (T : ℝ), Num k r lam u b bv ga h q0 → 0 < T → (((2 * r + k + 1) : ℝ) ^ 2 * (T * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) * (b ^ 2) ^ (2 * r) ≤ Hsq r T b := by
  first | exact @GlobalTheory.MomNum.mom_num | exact GlobalTheory.MomNum.mom_num | (intros; apply GlobalTheory.MomNum.mom_num <;> assumption)
end
