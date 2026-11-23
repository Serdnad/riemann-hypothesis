module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ChainLemmaMultivariatePowerSeriesCoordinateForm
public import ReciprocityTheory.DualLattices.Bundle001
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle030
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ZetaSeriesCoeffMulLe
import Formalism.LocalToGlobal.CharacterGerms.Bundle006
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.DualLattices.FormalChartAtZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
open Formalism.BaseCaseIdentities (Data Kn s0)
open ReciprocityTheory.PGsh (OrdGe lgSum)

namespace GlobalTheory.LeafCoordWeight

theorem chain_data {C : Type} [Field C] [CharZero C] {Z I : Type} [Fintype I] (D : Data C Z I)
    {N : ℕ} (em : Fin N → I) (hem : ∀ δ, D.lev (em δ) = 0) (t : I → MvPowerSeries (Fin N) C)
    (ht : ∀ c, MvPowerSeries.constantCoeff (t c) = 0)
    (hz : ∀ (b : I) (μ : Fin N →₀ ℕ), ∑ s ∈ Finset.range (μ.degree + 1), ∑ c,
      (if s = 0 then (if c = b then 1 else 0) else D.al c s b) *
        MvPowerSeries.coeff μ (t c ^ (D.l ^ s)) =
      MvPowerSeries.coeff μ (∑ j, MvPowerSeries.C (R := C) (if b = em j then 1 else 0) *
        (MvPowerSeries.X j : MvPowerSeries (Fin N) C))) :
    (∀ c, D.lev c < Kn D.i →
      OrdGe D.v (fun _ => 1 / ((D.l : ℝ) ^ 2 - 1) + 3 / (8 * (D.l : ℝ) ^ D.i))
        (t c - ∑ j, MvPowerSeries.C (R := C)
          (GlobalTheory.ChainCoord.kap C D.l (D.lev c) * chainMat D (D.lev c) c (em j)) *
          (MvPowerSeries.X j : MvPowerSeries (Fin N) C) ^ ((D.l ^ 2) ^ D.lev c))
        (1 + 1 / ((D.l : ℝ) ^ 2 - 1))) ∧
    ∀ c, ¬ D.lev c < Kn D.i →
      OrdGe D.v (fun _ => 1 / ((D.l : ℝ) ^ 2 - 1) + 3 / (8 * (D.l : ℝ) ^ D.i)) (t c)
        (1 + 1 / ((D.l : ℝ) ^ 2 - 1)) := by
  obtain ⟨ε⟩ : Nonempty (Fin (Fintype.card I) ≃ I) := ⟨(Fintype.equivFin I).symm⟩
  have hK := Kn_eq D.i_odd
  have hl0 : (D.l : C) ≠ 0 := by exact_mod_cast D.l_prime.ne_zero
  have key := GlobalTheory.ChainCoord.chain C D.v D.l D.l_prime D.v_l D.l_ge (Fintype.card I) N (s0 D.i)
    {c | D.good (ε c)}
    (fun s => Finset.univ.filter fun c => D.lev (ε c) = s ∧ s < Kn D.i)
    (fun c s b => if s = 0 then (if ε c = ε b then 1 else 0) else D.al (ε c) s (ε b))
    (fun s e j => chainMat D s (ε e) (em j)) (fun c => t (ε c))
    (fun s c hc => by
      obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hc).2
      exact D.pure_good _ (h1 ▸ h2))
    (fun s s' c _ _ hc hc' =>
      (Finset.mem_filter.1 hc).2.1.symm.trans (Finset.mem_filter.1 hc').2.1)
    (fun c e => by simp)
    (fun c n e => by
      by_cases hn : n = 0
      · subst hn
        by_cases h : ε c = ε e <;> simp [h]
      · simp only [if_neg hn]
        exact D.al_all _ _ _)
    (fun c hc => ⟨by
      funext e
      simpa using D.al_one _ hc (ε e), fun n e hn => by
      simp only [if_neg (show n ≠ 0 by omega)]
      have := D.al_good _ hc n (ε e) hn
      rwa [neg_sub] at this⟩)
    (fun s hs c hc e he => by
      obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hc).2
      have h3 : D.lev (ε e) ≠ D.lev (ε c) + 1 := fun h =>
        he (Finset.mem_filter.2 ⟨Finset.mem_univ _, by omega, by omega⟩)
      simp only [if_neg (show (2 : ℕ) ≠ 0 by omega)]
      rw [D.al_two _ (by omega), D.g_supp _ (by omega) _ h3, zero_add, inv_mul_cancel_left₀ hl0]
      exact D.lam_int _ _)
    (fun c j => by
      simp only [chainMat_zero]
      split_ifs <;> simp)
    (fun c hc => by
      funext j
      simp only [chainMat_zero, Pi.zero_apply]
      refine if_neg fun h => hc (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, by omega⟩)
      rw [h, hem])
    (fun s e j => by
      simp only [chainMat_succ, if_neg (show (2 : ℕ) ≠ 0 by omega)]
      rw [Finset.sum_filter, Finset.sum_filter, ← ε.sum_comp])
    (fun c => ht _)
    (fun e => by
      ext μ
      refine Eq.trans ?_ (hz (ε e) μ)
      change ∑ n ∈ Finset.range (Finsupp.degree μ + 1), ∑ a, _ = _
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [← ε.sum_comp])
  rw [two_mul_chainStartIndex_add_one_of_odd D.i_odd] at key
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · obtain ⟨c, rfl⟩ := ε.surjective c
    exact key.1 _ (by omega) c (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl, hc⟩)
  · obtain ⟨c, rfl⟩ := ε.surjective c
    refine key.2 c fun s _ h => hc ?_
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 h).2
    omega

theorem wtGe1_of_ordGe {C : Type} [Field C] {V : VF C} {i N : ℕ} {w : ℝ}
    {f : MvPowerSeries (Fin N) C}
    (h : OrdGe V.v (fun _ => 1 / ((V.l : ℝ) ^ 2 - 1) + 3 / (8 * (V.l : ℝ) ^ i)) f w) :
    WtGe1 V i w f := by
  intro μ
  have h1 : r1 V.l i - del V.l i = 1 / ((V.l : ℝ) ^ 2 - 1) + 3 / (8 * (V.l : ℝ) ^ i) := by
    have : (V.l : ℝ) ≠ 0 := by exact_mod_cast V.l_prime.ne_zero
    have h3 : 1 / (2 * (V.l : ℝ) ^ i) - 1 / (8 * (V.l : ℝ) ^ i) = 3 / (8 * (V.l : ℝ) ^ i) := by
      field_simp
      ring
    rw [← h3]
    unfold r1 del rho
    ring
  have h2 : (μ.degree : ℝ) = ∑ m, (μ m : ℝ) := by
    rw [Finsupp.degree_eq_sum]
    push_cast
    rfl
  refine le_trans ?_ (add_le_add (h μ) le_rfl)
  rw [← WithTop.coe_add, h1, h2, ← Finset.mul_sum]
  exact WithTop.coe_le_coe.2 (le_of_eq (by ring))

theorem weight_nonneg : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) [NeZero d] (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (Z : Type) (D : Formalism.BaseCaseIdentities.Data C Z I) (a : ZMod d) (i : ℕ), Adapted S D a i → ∀ t : I → MvPowerSeries I C, S.IsT t → ∀ (N : ℕ) (em : Fin N → I), (∀ δ, D.lev (em δ) = 0) → ∀ c, WtGe1 V i 0 (linPull (fun δ => S.tan (em δ)) (t c)) := by
  intro C _ _ V d _ I J _ _ G S Z D a i h t ht N em hem c
  obtain ⟨h1, h2, -⟩ := GlobalTheory.MainTerm.linPull_coords C V d I J G S t ht (Fin N) (fun δ => S.tan (em δ))
    (fun b j => if b = em j then 1 else 0)
    (fun c s b => if s = 0 then (if c = b then 1 else 0) else D.al c s b)
    (fun j x => by simp) (fun c b => by simp)
    (fun c k x hk => by
      simp only [if_neg (show k ≠ 0 by omega)]
      exact h.2.2.2.1 c k x hk)
  rw [← h.2.1] at h2
  obtain ⟨k1, k2⟩ := chain_data D em hem _ h1 h2
  have h3 : (3 : ℝ) ≤ D.l := by exact_mod_cast D.l_ge
  have hq : 0 < (D.l : ℝ) ^ 2 - 1 := by nlinarith
  have hρ : 0 < 1 / ((D.l : ℝ) ^ 2 - 1) := by positivity
  apply wtGe1_of_ordGe
  rw [← h.1, ← h.2.1, ← h.2.2.1]
  by_cases hc : D.lev c < Kn D.i
  · have hint : ∀ j, ((0 : ℝ) : WithTop ℝ) ≤ D.v (chainMat D (D.lev c) c (em j)) := fun j => by
      rw [h.1]
      exact h.chainMat_int _ _ _
    have hP := GlobalTheory.ChainCoord.ord_pure (v := D.v) fun j =>
      GlobalTheory.ChainCoord.ord_pure_level (σ := 3 / (8 * (D.l : ℝ) ^ D.i)) (s := D.lev c) (c := (0 : Fin 1))
        (π := fun s _ j => chainMat D s c (em j)) D.l_ge D.v_l hint j
    have := GlobalTheory.ChainCoord.ord_add (GlobalTheory.ChainCoord.ord_mono (k1 c hc) (w' := 0) (by linarith))
      (GlobalTheory.ChainCoord.ord_mono hP (w' := 0) (by positivity))
    rwa [sub_add_cancel] at this
  · exact GlobalTheory.ChainCoord.ord_mono (k2 c hc) (by linarith)

end GlobalTheory.LeafCoordWeight
end

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

noncomputable section

namespace GlobalTheory.MainTerm

open Formalism.BaseCaseIdentities (Data Kn s0)

theorem zetaSeries_main_term_fintype (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ))
    (l : ℕ) (hl : l.Prime) (hv : v (l : C) = 1) (h3 : 3 ≤ l) (I : Type) [Fintype I] (M s₀ : ℕ)
    (good : I → Prop) (Gs : ℕ → Finset I) (al : I → ℕ → I → C) (π : ℕ → I → Fin M → C)
    (t : I → MvPowerSeries (Fin M) C) (h1 : ∀ s c, c ∈ Gs s → good c)
    (h2 : ∀ s s' c, c ∈ Gs s → c ∈ Gs s' → s = s')
    (h4 : ∀ c e, al c 0 e = if c = e then 1 else 0)
    (h5 : ∀ c (n : ℕ) e, ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (al c n e))
    (h6 : ∀ c, good c → ∀ e, al c 1 e = 0)
    (h6' : ∀ c, good c → ∀ (n : ℕ) e, 1 ≤ n → ((1 - (n : ℝ) : ℝ) : WithTop ℝ) ≤ v (al c n e))
    (h7 : ∀ s < s₀, ∀ c ∈ Gs s, ∀ e, e ∉ Gs (s + 1) → 0 ≤ v (al c 2 e))
    (h8 : ∀ c j, 0 ≤ v (π 0 c j)) (h9 : ∀ c, c ∉ Gs 0 → ∀ j, π 0 c j = 0)
    (h10 : ∀ s e j, π (s + 1) e j = ∑ c ∈ Gs s, (l : C) * al c 2 e * π s c j ^ (l ^ 2))
    (h11 : ∀ c, MvPowerSeries.constantCoeff (t c) = 0)
    (h12 : ∀ (e : I) (μ : Fin M →₀ ℕ), ∑ s ∈ Finset.range (μ.degree + 1), ∑ c,
      al c s e * MvPowerSeries.coeff μ (t c ^ (l ^ s)) =
        MvPowerSeries.coeff μ (∑ j, MvPowerSeries.C (R := C) (π 0 e j) *
          (MvPowerSeries.X j : MvPowerSeries (Fin M) C)))
    (be : I → ℕ → C) (h13 : ∀ c, be c 0 = 0)
    (h14 : ∀ c (n : ℕ), ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (be c n))
    (h15 : ∀ c, good c → ∀ n : ℕ, 2 ≤ n → ((1 - (n : ℝ) : ℝ) : WithTop ℝ) ≤ v (be c n))
    (h16 : ∀ s < s₀, ∀ c ∈ Gs s, be c 1 = 0) (ζ : MvPowerSeries (Fin M) C)
    (h17 : ∀ α, MvPowerSeries.coeff α ζ = -∑ n ∈ Finset.range (Finsupp.degree α + 1), ∑ c,
      be c n * MvPowerSeries.coeff α (t c ^ (l ^ n))) :
    ReciprocityTheory.PGsh.OrdGe v (fun _ => 1 / ((l : ℝ) ^ 2 - 1) + 3 / (8 * (l : ℝ) ^ (2 * s₀ + 1)))
      (ζ - ∑ j, MvPowerSeries.C (R := C)
        (((l : C) ^ (1 + l * (∑ u ∈ Finset.range s₀, (l ^ 2) ^ u)))⁻¹ *
          ((-1) ^ (s₀ + 1) * ∑ c ∈ Gs s₀, π s₀ c j ^ l * ((l : C) * be c 1))) *
        (MvPowerSeries.X j : MvPowerSeries (Fin M) C) ^ (l ^ (2 * s₀ + 1))) 0 := by
  let φ : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  have hmem : ∀ s c, c ∈ (Gs s).map φ.toEmbedding ↔ φ.symm c ∈ Gs s := fun s c =>
    Finset.mem_map_equiv
  have key := GlobalTheory.zetaSeries_main_term C v l hl hv h3 (Fintype.card I) M s₀ {c | good (φ.symm c)}
    (fun s => (Gs s).map φ.toEmbedding) (fun c n e => al (φ.symm c) n (φ.symm e))
    (fun s e j => π s (φ.symm e) j) (fun c => t (φ.symm c))
    (fun s c hc => h1 s _ ((hmem s c).1 hc))
    (fun s s' c _ _ hc hc' => h2 s s' _ ((hmem s c).1 hc) ((hmem s' c).1 hc'))
    (fun c e => by simp [h4])
    (fun c n e => h5 _ n _)
    (fun c hc => ⟨funext fun e => h6 _ hc _, fun n e hn => h6' _ hc n _ hn⟩)
    (fun s hs c hc e he => h7 s hs _ ((hmem s c).1 hc) _ (fun h => he ((hmem _ e).2 h)))
    (fun c j => h8 _ j)
    (fun c hc => funext fun j => h9 _ (fun h => hc ((hmem _ c).2 h)) j)
    (fun s e j => by simp [h10, Finset.sum_map])
    (fun c => h11 _)
    (fun e => by
      ext μ
      rw [← h12 (φ.symm e) μ]
      change ∑ n ∈ Finset.range (μ.degree + 1), ∑ a, al (φ.symm a) n (φ.symm e) *
        MvPowerSeries.coeff μ (t (φ.symm a) ^ (l ^ n)) = _
      refine Finset.sum_congr rfl fun n _ => ?_
      exact Equiv.sum_comp φ.symm (fun c => al c n (φ.symm e) * MvPowerSeries.coeff μ (t c ^ (l ^ n))))
    1 (fun c n _ => be (φ.symm c) n) 0
    (fun c => h13 _) (fun c n => h14 _ n) (fun c hc n hn => h15 _ hc n hn)
    (fun s hs c hc => h16 s hs _ ((hmem s c).1 hc)) ζ
    (fun α => by
      rw [h17 α]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      exact (Equiv.sum_comp φ.symm (fun c => be c n * MvPowerSeries.coeff α (t c ^ (l ^ n)))).symm)
  simpa only [Finset.sum_map, Equiv.coe_toEmbedding, Equiv.symm_apply_apply] using key

theorem zeta_leaf_main_term : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) [NeZero d] (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (Z : Type) (D : Formalism.BaseCaseIdentities.Data C Z I) (a : ZMod d) (i : ℕ), Adapted S D a i → i < d → ∀ t : I → MvPowerSeries I C, S.IsT t → ∀ (N : ℕ) (em : Fin N → I), (∀ δ, D.lev (em δ) = 0) → ∀ κ : J, G.ty (Sum.inr κ) = a + (i : ZMod d) → WtGe1 V i 0 (linPull (fun δ => S.tan (em δ)) (S.ze t κ) - ((V.l : C) ^ expE V.l i)⁻¹ • ∑ δ : Fin N, mainVec S D (em δ) κ • (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) ^ (V.l ^ i)) := by
  intro C _ _ V d _ I J _ _ G S Z D a i h hid t ht N em hem κ hκ
  have hDv : D.v = V.v := h.1
  have hDl : D.l = V.l := h.2.1
  have hDi : D.i = i := h.2.2.1
  have hi : Odd i := hDi ▸ D.i_odd
  have h3 : 3 ≤ V.l := hDl ▸ D.l_ge
  have hK : Kn i = s0 i + 1 := Kn_eq hi
  have hs : 2 * s0 i + 1 = i := two_mul_chainStartIndex_add_one_of_odd hi
  let al : I → ℕ → I → C := fun c k b => if k = 0 then (if c = b then 1 else 0) else D.al c k b
  have hal0 : ∀ c b, al c 0 b = if c = b then 1 else 0 := fun c b => by simp [al]
  have halk : ∀ c k b, 1 ≤ k → al c k b = D.al c k b := fun c k b hk => by
    have : k ≠ 0 := by omega
    simp [al, this]
  obtain ⟨hc1, hc2, hc3⟩ := GlobalTheory.MainTerm.linPull_coords C V d I J G S t ht (Fin N) (fun δ => S.tan (em δ))
    (fun b j => chainMat D 0 b (em j)) al
    (fun j x => by simp [chainMat_zero])
    (fun c b => by rw [hal0])
    (fun c k x hk => by
      rw [h.2.2.2.1 c k x hk]
      exact Finset.sum_congr rfl fun b _ => by rw [halk c k b hk])
  have hGs : ∀ s c, c ∈ Finset.univ.filter (fun c => D.lev c = s ∧ s < Kn D.i) ↔
      D.lev c = s ∧ s < Kn D.i := fun s c => by simp
  have hl0 : (D.l : C) ≠ 0 := by exact_mod_cast D.l_prime.ne_zero
  have key := zetaSeries_main_term_fintype C V.v V.l V.l_prime V.v_l h3 I N (s0 i) D.good
    (fun s => Finset.univ.filter (fun c => D.lev c = s ∧ s < Kn D.i)) al
    (fun s e j => chainMat D s e (em j)) (fun c => linPull (fun δ => S.tan (em δ)) (t c))
    (fun s c hc => by
      obtain ⟨h1, h2⟩ := (hGs s c).1 hc
      exact D.pure_good c (h1 ▸ h2))
    (fun s s' c hc hc' => ((hGs s c).1 hc).1.symm.trans ((hGs s' c).1 hc').1)
    hal0
    (fun c n e => by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [hal0]
        split_ifs <;> simp
      · rw [halk c n e hn, ← hDv]
        exact D.al_all c n e)
    (fun c hc e => by rw [halk c 1 e le_rfl, D.al_one c hc])
    (fun c hc n e hn => by
      rw [halk c n e hn, ← hDv]
      have := D.al_good c hc n e hn
      rwa [neg_sub] at this)
    (fun s hs' c hc e he => by
      obtain ⟨h1, h2⟩ := (hGs s c).1 hc
      have h4 : s + 1 < Kn D.i := by rw [hDi, hK]; omega
      have h5 : D.lev e ≠ D.lev c + 1 := fun h6 => he ((hGs _ e).2 ⟨by rw [h6, h1], h4⟩)
      rw [halk c 2 e (by norm_num), D.al_two c (h1 ▸ h2), D.g_supp c (h1 ▸ h4) e h5, zero_add,
        inv_mul_cancel_left₀ hl0, ← hDv]
      exact D.lam_int c e)
    (fun c j => by simpa [VF.Ge] using h.chainMat_int 0 c (em j))
    (fun c hc j => by
      rw [chainMat_zero, if_neg]
      rintro rfl
      exact hc ((hGs _ _).2 ⟨hem j, by rw [hDi, hK]; omega⟩))
    (fun s e j => by
      rw [chainMat_succ, hDl]
      exact Finset.sum_congr rfl fun c _ => by rw [halk c 2 e (by norm_num)])
    hc1 hc2 (fun c n => S.be c n κ) (fun c => S.be_zero c κ)
    (fun c n => G.bound0 n _ (S.mem c) (Sum.inr κ))
    (fun c hc n hn => by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
      have := (h.good hc).bound m (Sum.inr κ)
      have e : (1 - ((m + 2 : ℕ) : ℝ)) = -((m : ℝ) + 1) := by push_cast; ring
      rw [e]
      exact this)
    (fun s hs' c hc => by
      obtain ⟨h1, h2⟩ := (hGs s c).1 hc
      apply S.pure c 1
      rw [hκ, h.2.2.2.2 c (by rw [h1, ← hDi]; exact h2), h1, add_assoc, ← Nat.cast_add]
      intro h5
      have h6 := (ZMod.natCast_eq_natCast_iff' _ _ _).1 (add_left_cancel h5)
      rw [Nat.mod_eq_of_lt hid, Nat.mod_eq_of_lt (by omega)] at h6
      omega)
    (linPull (fun δ => S.tan (em δ)) (S.ze t κ)) (hc3 κ)
  have hE : expE V.l i = 1 + V.l * (∑ u ∈ Finset.range (s0 i), (V.l ^ 2) ^ u) := rfl
  have hmain : ((V.l : C) ^ expE V.l i)⁻¹ • ∑ δ : Fin N, mainVec S D (em δ) κ •
      (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) ^ (V.l ^ i) =
      ∑ j, MvPowerSeries.C (R := C)
        (((V.l : C) ^ (1 + V.l * (∑ u ∈ Finset.range (s0 i), (V.l ^ 2) ^ u)))⁻¹ *
          ((-1) ^ (s0 i + 1) * ∑ c ∈ Finset.univ.filter (fun c => D.lev c = s0 i ∧ s0 i < Kn D.i),
            chainMat D (s0 i) c (em j) ^ V.l * ((V.l : C) * S.be c 1 κ))) *
        (MvPowerSeries.X j : MvPowerSeries (Fin N) C) ^ (V.l ^ (2 * s0 i + 1)) := by
    rw [Finset.smul_sum, hs, hE]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, MvPowerSeries.smul_eq_C_mul, mainVec, hDl, hDi]
  rw [hmain]
  intro μ
  have hk := key μ
  rw [hs] at hk
  have hr : ∑ m, (1 / ((V.l : ℝ) ^ 2 - 1) + 3 / (8 * (V.l : ℝ) ^ i)) * (μ m : ℝ) =
      (μ.degree : ℝ) * (r1 V.l i - del V.l i) := by
    rw [← Finset.mul_sum, Finsupp.degree_eq_sum, Nat.cast_sum, mul_comm]
    congr 1
    unfold r1 del rho
    have : (V.l : ℝ) ≠ 0 := by exact_mod_cast V.l_prime.ne_zero
    rw [add_sub_assoc]
    congr 1
    field_simp
    ring
  simp only [hr] at hk
  rw [hs]
  calc (((0 : ℝ) : ℝ) : WithTop ℝ)
      = ((0 - (μ.degree : ℝ) * (r1 V.l i - del V.l i) : ℝ) : WithTop ℝ) +
        (((μ.degree : ℝ) * (r1 V.l i - del V.l i) : ℝ) : WithTop ℝ) := by
        rw [← WithTop.coe_add, sub_add_cancel]
    _ ≤ _ := add_le_add_left hk _

end GlobalTheory.MainTerm
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharExt

private theorem isAddUnit_of_pow {M : Type} [AddCommMonoid M] {p : ℕ} (hp : p ≠ 0) {a : M}
    (h : ∃ k, p ^ k • a = 0) : IsAddUnit a := by
  obtain ⟨k, hk⟩ := h
  have h1 : p ^ k = (p ^ k - 1) + 1 := by
    have : 0 < p ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ hp)
    omega
  rw [h1, add_nsmul, one_nsmul, add_comm] at hk
  exact ⟨⟨a, (p ^ k - 1) • a, hk, by rw [add_comm]; exact hk⟩, rfl⟩

private theorem extend_group {A B : Type} [AddCommGroup A] [AddCommGroup B] (j : A →+ B)
    (hj : Function.Injective j) (C : Type) [Field C] [IsAlgClosed C]
    (χ : A →+ Additive Cˣ) : ∃ κ : B →+ Additive Cˣ, ∀ a, κ (j a) = χ a := by
  classical
  have hsurj : ∀ n : ℕ, n ≠ 0 → ∀ x : Additive Cˣ, ∃ y : Additive Cˣ, n • y = x := by
    intro n hn x
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((Additive.toMul x : Cˣ) : C)
      (Nat.pos_of_ne_zero hn)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hn] at hz
      exact (Additive.toMul x : Cˣ).ne_zero hz.symm
    refine ⟨Additive.ofMul (Units.mk0 z hz0), ?_⟩
    apply Additive.toMul.injective
    ext
    simpa using hz
  letI : DivisibleBy (Additive Cˣ) ℕ :=
    divisibleByOfSMulRightSurj (Additive Cˣ) ℕ (fun {n} hn x => hsurj n hn x)
  letI : DivisibleBy (Additive Cˣ) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  obtain ⟨κ, hκ⟩ := (Module.Baer.of_divisible (Additive Cˣ)).extension_property_addMonoidHom
    j hj χ
  exact ⟨κ, fun a => DFunLike.congr_fun hκ a⟩

theorem exists_extension : ∀ (M M' : Type) [AddCommMonoid M] [AddCommMonoid M'] (j : M' →+ M), Function.Injective j → ∀ (C : Type) [Field C] [IsAlgClosed C] (p : ℕ), p ≠ 0 → ∀ χ : M' → Cˣ, (∀ a b, χ (a + b) = χ a * χ b) → ∃ κ : M → Cˣ, (∀ a b, (∃ k, p ^ k • a = 0) → (∃ k, p ^ k • b = 0) → κ (a + b) = κ a * κ b) ∧ κ 0 = 1 ∧ ∀ a, (∃ k, p ^ k • a = 0) → κ (j a) = χ a := by
  intro M M' _ _ j hj C _ _ p hp χ hχ
  classical
  let χ' : AddUnits M' →+ Additive Cˣ := AddMonoidHom.mk' (fun u => Additive.ofMul (χ u.val))
    (fun a b => by rw [AddUnits.val_add, hχ]; rfl)
  have hj' : Function.Injective (AddUnits.map j) := by
    intro a b hab
    ext
    exact hj (congrArg AddUnits.val hab)
  obtain ⟨κ, hκ⟩ := extend_group (AddUnits.map j) hj' C χ'
  have key : ∀ u : AddUnits M,
      (if h : IsAddUnit u.val then Additive.toMul (κ h.addUnit) else 1) = Additive.toMul (κ u) := by
    intro u
    rw [dite_eq_left u.isAddUnit]
    congr 2
    ext
    exact IsAddUnit.addUnit_spec _
  refine ⟨fun a => if h : IsAddUnit a then Additive.toMul (κ h.addUnit) else 1, ?_, ?_, ?_⟩
  · intro a b ha hb
    obtain ⟨u, rfl⟩ := isAddUnit_of_pow hp ha
    obtain ⟨v, rfl⟩ := isAddUnit_of_pow hp hb
    have h3 := key (u + v)
    have h1 := key u
    have h2 := key v
    beta_reduce
    rw [h1, h2]
    refine Eq.trans h3 ?_
    rw [map_add (f := _)]; rfl
  · have := key 0
    refine Eq.trans this ?_
    rw [map_zero]; rfl
  · intro a ha
    obtain ⟨u, rfl⟩ := isAddUnit_of_pow hp ha
    have h1 := key (AddUnits.map j u)
    refine Eq.trans h1 ?_
    rw [hκ]; rfl

end GlobalTheory.CharExt
end
