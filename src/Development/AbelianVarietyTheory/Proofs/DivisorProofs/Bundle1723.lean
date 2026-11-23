module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFactorDepthInChartChartIndependent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1687
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1688
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
import Mathlib.RingTheory.Radical.NatInt
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtCoeffSingleSubst
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtOrderProdSub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TangentEqLcZero
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv

open MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dAct)

theorem subst_comb_expPt {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d n : ℕ} {σ κ : Type} [Fintype κ]
    (G : LogFGL v d) (w : κ → Fin d → MvPowerSeries σ C) (hw : ∀ b i, constantCoeff (w b i) = 0)
    (F : MvPowerSeries (Fin n × Fin d) C) (M : κ → Fin n → Matrix (Fin d) (Fin d) C) :
    (subst (fun q : Fin n × Fin d => ∑ i : κ × Fin d, M i.1 q.1 q.2 i.2 • w i.1 i.2)
      (subst (fun q : Fin n × Fin d => expPt G (fun e => (X (q.1, e) : MvPowerSeries (Fin n × Fin d) C)) q.2) F :
        MvPowerSeries (Fin n × Fin d) C) : MvPowerSeries σ C) =
      subst (fun q : Fin n × Fin d => expPt G (∑ b, mv (M b q.1) (w b)) q.2) F := by
  have ht : HasSubst (fun q : Fin n × Fin d => ∑ i : κ × Fin d, M i.1 q.1 q.2 i.2 • w i.1 i.2) :=
    hasSubst_of_constantCoeff_zero (by intro q; simp [hw])
  have hs : HasSubst (fun q : Fin n × Fin d =>
      expPt G (fun e => (X (q.1, e) : MvPowerSeries (Fin n × Fin d) C)) q.2) :=
    hasSubst_of_constantCoeff_zero (fun q => cc_expPt G (by simp) q.2)
  refine (subst_comp_subst_apply hs ht F).trans ?_
  congr 1
  funext q
  refine (subst_expPt G ht (by simp) q.2).trans ?_
  congr 1
  funext e
  refine (subst_X ht _).trans ?_
  simp [mv, Fintype.sum_prod_type, Finset.sum_apply]

theorem le_v_pow_mul_int {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {p : ℕ} (hp : v (p : C) = 1)
    (N : ℕ) (z : ℤ) : ((N : ℝ) : WithTop ℝ) ≤ v ((((p : ℤ) ^ N * z : ℤ)) : C) := by
  have hz : 0 ≤ v (z : C) := intCast_mem (ReciprocityTheory.ChartRestriction.G.Sh.ptIntSub v) z
  push_cast
  rw [v.map_mul, v.map_pow, hp]
  calc ((N : ℕ) : WithTop ℝ) = N • (1 : WithTop ℝ) := by simp
    _ ≤ _ := le_add_of_nonneg_right hz

theorem limFrame : AddSt → ActSt → UnitSt → BiaddSt → FrameSt → FinSt → ContSt → LimFrameSt := by
  classical
  intro _ hAct hUnit hBi hFr hFin hCont C _ _ v p hp d R _ _ O _ _ _ B hB h hh σ _ κ _ w hw w0 n A a hA hiso α
  have hw0 : ∀ b i, constantCoeff (w b i) = 0 := fun b => (hw b).1
  have mono : ∀ {M N : ℕ} {x : WithTop ℝ}, M ≤ N → ((N : ℝ) : WithTop ℝ) ≤ x → ((M : ℝ) : WithTop ℝ) ≤ x :=
    fun hMN hx => le_trans (WithTop.coe_le_coe.2 (Nat.cast_le.2 hMN)) hx
  have zle : ∀ {N : ℕ} {x : C}, ((N : ℝ) : WithTop ℝ) ≤ v x → IsIntV v x := fun hx => by
    have := mono (Nat.zero_le _) hx
    simpa [IsIntV] using this
  have hD : ∀ (x : O) i j, IsIntV v (dAct C B x i j) := fun x i j => hB.2.1 x i _
  have hAi : ∀ b j e e', IsIntV v (A b j e e') := fun b j e e' => by
    have := (ReciprocityTheory.ChartRestriction.G.Sh.ptIntSub v).add_mem (zle (hA 0 b j e e')) (hD (a 0 b j) e e')
    rw [sub_add_cancel] at this
    exact this
  obtain ⟨m, e, he⟩ := Module.Finite.exists_fin (R := ℤ) (M := O)
  let g : κ × κ × Fin m → MvPowerSeries σ C := fun i =>
    pairSer (fglOf hB) h (w i.1) (mv (dAct C B (e i.2.2)) (w i.2.1))
  have hg0 : ∀ i, constantCoeff (g i) = 0 := fun i =>
    (hBi C v d R O B hB h hh σ (w i.1) (w i.1) _ (hw _) (hw _)
      ((hAct C v d R O B hB σ (e i.2.2)).2 _ (hw i.2.1))).1
  obtain ⟨N₀, hN₀⟩ := hCont C v (Fin n × Fin d) σ (κ × Fin d)
    (subst (fun q : Fin n × Fin d => expPt (fglOf hB) (fun e => (X (q.1, e) : MvPowerSeries (Fin n × Fin d) C)) q.2)
      (frameSer B h w0 n)) (fun i => w i.1 i.2) (fun i => hw0 _ _) α
  choose N₁ hN₁ using fun γ => hCont C v Unit σ (κ × κ × Fin m) (PowerSeries.exp C) g hg0 γ
  obtain ⟨N, hN0, hN1⟩ : ∃ N : ℕ, N₀ ≤ N ∧ ∀ x ∈ Finset.HasAntidiagonal.antidiagonal α, N₁ x.2 ≤ N :=
    ⟨max N₀ ((Finset.HasAntidiagonal.antidiagonal α).sup fun x => N₁ x.2), le_max_left _ _,
      fun x hx => le_trans (Finset.le_sup (f := fun x => N₁ x.2) hx) (le_max_right _ _)⟩
  have hdec : ∀ b b', ∃ nn : Fin m → ℤ,
      (∑ j, star (a N b j) * a N b' j) * w0 = ∑ i, ((p : ℤ) ^ N * nn i) • e i := fun b b' => by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (hiso N b b')
    obtain ⟨nn, hnn⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ (v := e) (x := c * w0)).1
      (by rw [he]; exact Submodule.mem_top)
    refine ⟨nn, ?_⟩
    rw [hc, mul_assoc, ← hnn, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [zsmul_eq_mul, mul_assoc]
  choose nn hnn using hdec
  have hU := hFin C v d R O B hB h hh σ κ w hw w0 n (a N) (Fin m) e (fun b b' i => (p : ℤ) ^ N * nn b b' i) hnn
  have hF := (hFr C v d R O B hB h hh w0 n).2.2 σ (fun j => ∑ b, mv (dAct C B (a N b j)) (w b))
    (fun j i => by simp [Finset.sum_apply, mv, hw0])
  let s : κ × κ × Fin m → C := fun i => (((p : ℤ) ^ N * nn i.1 i.2.1 i.2.2 : ℤ) : C)
  have hT : ∑ b, ∑ b', ∑ i, (((p : ℤ) ^ N * nn b b' i : ℤ) : C) •
      pairSer (fglOf hB) h (w b) (mv (dAct C B (e i)) (w b')) = ∑ i, s i • g i := by
    simp only [Fintype.sum_prod_type, s, g]
  rw [hT] at hU
  have hT0 : constantCoeff (∑ i, s i • g i) = 0 := by simp [hg0]
  obtain ⟨hz, -, -, hmul, -⟩ := hUnit C v σ
  have hprod := hmul _ _ hU.1 hT0
  rw [sub_add_cancel, ← hF] at hprod
  have h1 := hN₀ (fun q i => A i.1 q.1 q.2 i.2) (fun q i => dAct C B (a N i.1 q.1) q.2 i.2)
    (fun q i => hAi _ _ _ _) (fun q i => hD _ _ _) (fun q i => mono hN0 (hA N _ _ _ _))
  rw [subst_comb_expPt (fglOf hB) w hw0 _ A,
    subst_comb_expPt (fglOf hB) w hw0 _ (fun b j => dAct C B (a N b j)), hprod] at h1
  have h2 : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal α,
      IsIntV v (coeff x.2 (PowerSeries.subst (∑ i, s i • g i) (PowerSeries.exp C))) := fun x hx => by
    have h3 := hN₁ x.2 (fun _ => s) (fun _ _ => 0) (fun _ i => zle (le_v_pow_mul_int hp N _))
      (fun _ _ => by simp [IsIntV]) (fun _ i => by
        rw [sub_zero]; exact mono (hN1 x hx) (le_v_pow_mul_int hp N _))
    simp only [zero_smul, Finset.sum_const_zero] at h3
    have h4 := (ReciprocityTheory.ChartRestriction.G.Sh.ptIntSub v).add_mem h3 (hz.2 x.2)
    have h5 : ∀ y z : C, y - z + z ∈ ReciprocityTheory.ChartRestriction.G.Sh.ptIntSub v → IsIntV v y := fun y z hyz => by
      rw [sub_add_cancel] at hyz
      exact hyz
    exact h5 _ _ h4
  rw [coeff_mul] at h1
  have h6 := (ReciprocityTheory.ChartRestriction.G.Sh.ptIntSub v).add_mem h1
    ((ReciprocityTheory.ChartRestriction.G.Sh.ptIntSub v).sum_mem fun x hx =>
      (ReciprocityTheory.ChartRestriction.G.Sh.ptIntSub v).mul_mem (hU.2 x.1) (h2 x hx))
  rw [sub_add_cancel] at h6
  exact h6

end GlobalTheory.IsoTriv
end
end

section

open GlobalTheory.IsoTriv

namespace GlobalTheory.IsoTriv.PrimeIdempotent

theorem mem_pow_of_map_dvd {R V : Type} [CommRing R] [IsDedekindDomain R] [CommRing V]
    [IsDomain V] [IsDiscreteValuationRing V] (φ : R →+* V) (b a : R) (hb : φ b ≠ 0) (n : ℕ)
    (hw : (Ideal.comap φ (IsLocalRing.maximalIdeal V)).IsMaximal)
    (hbn : b ∈ Ideal.comap φ (IsLocalRing.maximalIdeal V) ^ n) (z : V) (hz : φ a = φ b * z) :
    a ∈ Ideal.comap φ (IsLocalRing.maximalIdeal V) ^ n := by
  set w := Ideal.comap φ (IsLocalRing.maximalIdeal V) with hwdef
  by_cases ha : a = 0
  · rw [ha]; exact Ideal.zero_mem _
  have hspan : Ideal.span {a} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨J, hJ, hfac⟩ := Ideal.eq_prime_pow_mul_coprime hspan w
  generalize Multiset.count w (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})) = i
    at hfac
  by_cases hi : n ≤ i
  · have h1 : a ∈ w ^ i * J := hfac ▸ Ideal.mem_span_singleton_self a
    exact Ideal.pow_le_pow_right hi (Ideal.mul_le_inf h1).1
  exfalso
  have hJw : ¬ J ≤ w := fun h => hw.ne_top (by rw [← hJ, sup_eq_left.mpr h])
  obtain ⟨s, hsJ, hsw⟩ := Set.not_subset.mp hJw
  have hb1 : b ∈ w ^ (i + 1) := Ideal.pow_le_pow_right (by omega) hbn
  have h2 : b * s ∈ Ideal.span {a} * w := by
    rw [hfac, mul_right_comm, ← pow_succ]
    exact Ideal.mul_mem_mul hb1 hsJ
  obtain ⟨m, hm, hm'⟩ := Ideal.mem_span_singleton_mul.mp h2
  apply hsw
  have h3 : φ s = z * φ m := by
    apply mul_left_cancel₀ hb
    rw [← map_mul, ← hm', map_mul, hz, mul_assoc]
  change φ s ∈ IsLocalRing.maximalIdeal V
  rw [h3]
  exact Ideal.mul_mem_left _ _ hm

theorem epsSt : EpsSt := by
  intro R V _ _ _ _ _ φ q hq hu
  set w := Ideal.comap φ (IsLocalRing.maximalIdeal V) with hwdef
  have hq0 : q ≠ 0 := fun h => hq (by rw [h, map_zero])
  have hqw : q ∈ w := (IsLocalRing.mem_maximalIdeal _).mpr hu
  have hwp : w.IsPrime := Ideal.comap_isPrime φ _
  have hw0 : w ≠ ⊥ := fun h => hq0 (by rw [h] at hqw; exact hqw)
  have hw : w.IsMaximal := hwp.isMaximal hw0
  have hspan : Ideal.span {q} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨J, hJ, hfac⟩ := Ideal.eq_prime_pow_mul_coprime hspan w
  generalize Multiset.count w (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {q})) = e
    at hfac
  have hpow : ∀ M : ℕ, Ideal.span {q ^ M} = w ^ (e * M) * J ^ M := fun M => by
    rw [← Ideal.span_singleton_pow, hfac, mul_pow, pow_mul]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have key : ∀ N : ℕ, ∃ y ∈ J ^ N, ∃ z, φ y = 1 + φ q ^ N * z := by
    intro N
    obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible (pow_ne_zero N hq) hϖ
    have hco : w ^ k ⊔ J ^ N = ⊤ := Ideal.pow_sup_pow_eq_top hJ
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp hco)
    have h1 : φ x ∈ Ideal.span {φ q ^ N} := by
      have h2 : φ x ∈ (Ideal.map φ w) ^ k := by
        rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem φ hx
      have h3 : φ x ∈ IsLocalRing.maximalIdeal V ^ k :=
        Ideal.pow_right_mono Ideal.map_comap_le k h2
      rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow] at h3
      rwa [Ideal.span_singleton_eq_span_singleton.mpr hk]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp h1
    refine ⟨y, hy, -c, ?_⟩
    have h4 : φ x + φ y = 1 := by rw [← map_add (f := _), hxy, map_one]
    rw [← h4, hc]; ring
  choose ε hεJ hε using key
  refine ⟨ε, fun N => ⟨hε N, fun M hM a ⟨z, hz⟩ => ?_⟩⟩
  have hqM : q ^ M ∈ w ^ (e * M) := by
    have h1 : q ^ M ∈ w ^ (e * M) * J ^ M := hpow M ▸ Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_inf h1).1
  have ha : a ∈ w ^ (e * M) :=
    mem_pow_of_map_dvd φ (q ^ M) a (by rw [map_pow]; exact pow_ne_zero M hq) _ hw hqM z
      (by rw [map_pow]; exact hz)
  rw [hpow M, mul_comm (ε N)]
  exact Ideal.mul_mem_mul ha (Ideal.pow_le_pow_right hM (hεJ N))

end GlobalTheory.IsoTriv.PrimeIdempotent
end

section

open GlobalTheory.IsoTriv

namespace GlobalTheory.LimInv

variable {R V : Type} [CommRing R] [CommRing V]

def limSub (φ : R →+* V) (q : R) : Subring V where
  carrier := {t | ∀ N : ℕ, ∃ a z, φ a = t + φ q ^ N * z}
  mul_mem' := by
    intro s t hs ht N
    obtain ⟨a, z, ha⟩ := hs N
    obtain ⟨b, w, hb⟩ := ht N
    refine ⟨a * b, z * t + s * w + φ q ^ N * z * w, ?_⟩
    rw [map_mul, ha, hb]; ring
  one_mem' := fun N => ⟨1, 0, by simp⟩
  add_mem' := by
    intro s t hs ht N
    obtain ⟨a, z, ha⟩ := hs N
    obtain ⟨b, w, hb⟩ := ht N
    exact ⟨a + b, z + w, by rw [map_add (f := _), ha, hb]; ring⟩
  zero_mem' := fun N => ⟨0, 0, by simp⟩
  neg_mem' := by
    intro s hs N
    obtain ⟨a, z, ha⟩ := hs N
    exact ⟨-a, -z, by rw [map_neg, ha]; ring⟩

theorem inv_mem_limSub [IsDedekindDomain R] [IsDomain V] [IsDiscreteValuationRing V]
    (φ : R →+* V) (q : R) (hq0 : φ q ≠ 0) (hqu : ¬ IsUnit (φ q)) (u : Vˣ)
    (hu : (u : V) ∈ limSub φ q) : ((u⁻¹ : Vˣ) : V) ∈ limSub φ q := by
  intro N
  obtain ⟨a, z, ha⟩ := hu (N + 1)
  have hqm : φ q ∈ IsLocalRing.maximalIdeal V := (IsLocalRing.mem_maximalIdeal _).2 hqu
  have haU : IsUnit (φ a) := by
    by_contra h
    have h1 : φ a ∈ IsLocalRing.maximalIdeal V := (IsLocalRing.mem_maximalIdeal _).2 h
    have h2 : φ q ^ (N + 1) * z ∈ IsLocalRing.maximalIdeal V :=
      Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hqm _ (Nat.succ_pos N))
    have h3 : (u : V) ∈ IsLocalRing.maximalIdeal V := by
      have : (u : V) = φ a - φ q ^ (N + 1) * z := by rw [ha]; ring
      rw [this]; exact Ideal.sub_mem _ h1 h2
    exact ((IsLocalRing.mem_maximalIdeal _).1 h3) u.isUnit
  set w : Ideal R := (IsLocalRing.maximalIdeal V).comap φ with hw
  have hwp : w.IsPrime := Ideal.comap_isPrime φ _
  have hqw : q ∈ w := hqm
  have hwne : w ≠ ⊥ := by
    intro h
    have : q = 0 := by rw [h] at hqw; exact (Submodule.mem_bot R).1 hqw
    exact hq0 (by rw [this, map_zero])
  have hwm : w.IsMaximal := hwp.isMaximal hwne
  have haw : a ∉ w := fun h => ((IsLocalRing.mem_maximalIdeal _).1 h) haU
  obtain ⟨y, i, hiw, hyi⟩ := hwm.exists_inv haw
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨n, e, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (pow_ne_zero N hq0) hϖ
  have hiV : φ i ∈ Ideal.span {ϖ} := by rw [← hϖ.maximalIdeal_eq]; exact hiw
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hiV
  let b : R := y * ∑ j ∈ Finset.range n, i ^ j
  have hab : φ a * φ b = 1 - φ q ^ N * ((e⁻¹ : Vˣ) * c ^ n) := by
    have h1 : a * b = 1 - i ^ n := by
      have : a * y = 1 - i := by linear_combination hyi
      calc a * b = (a * y) * ∑ j ∈ Finset.range n, i ^ j := by ring
        _ = 1 - i ^ n := by rw [this, mul_neg_geom_sum]
    have h2 : φ a * φ b = 1 - φ i ^ n := by rw [← map_mul, h1, map_sub, map_one, map_pow]
    rw [h2, he, ← hc, mul_pow]
    have : ((e : V) * (e⁻¹ : Vˣ)) = 1 := Units.mul_inv e
    linear_combination (c ^ n * ϖ ^ n) * this
  refine ⟨b, -((u⁻¹ : Vˣ) : V) * ((e⁻¹ : Vˣ) * c ^ n) - ((u⁻¹ : Vˣ) : V) * φ q * z * φ b, ?_⟩
  have hu1 : (u : V) * ((u⁻¹ : Vˣ) : V) = 1 := Units.mul_inv u
  linear_combination ((u⁻¹ : Vˣ) : V) * hab - (((u⁻¹ : Vˣ) : V) * φ b) * ha - φ b * hu1

end GlobalTheory.LimInv

open GlobalTheory.LimInv in
theorem GlobalTheory.IsoTriv.limitEntriesMatrixInverseClosed_proof : InvSt := by
  intro R V _ _ _ _ _ φ q hq0 hqu n M hdet hM
  classical
  let S := limSub φ q
  let M₀ : Matrix (Fin n) (Fin n) S := fun b b' => ⟨M b b', fun N => hM b b' N⟩
  have hMM : S.subtype.mapMatrix M₀ = M := by ext b b'; rfl
  have hadj : ∀ b b', M.adjugate b b' ∈ S := by
    intro b b'
    rw [← hMM, ← RingHom.map_adjugate]
    exact (M₀.adjugate b b').2
  have hdetS : M.det ∈ S := by
    rw [← hMM, ← RingHom.map_det]; exact (M₀.det).2
  set u := hdet.unit with hu
  have huS : (u : V) ∈ S := by rw [hu, IsUnit.unit_spec]; exact hdetS
  have hinv := inv_mem_limSub φ q hq0 hqu u huS
  refine ⟨((u⁻¹ : Vˣ) : V) • M.adjugate, ?_, ?_⟩
  · rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul]
    have : ((u⁻¹ : Vˣ) : V) * M.det = 1 := by
      rw [show M.det = (u : V) by rw [hu, IsUnit.unit_spec]]; exact Units.inv_mul u
    rw [this, one_smul]
  · intro b b' N
    have : (((u⁻¹ : Vˣ) : V) • M.adjugate) b b' ∈ S := by
      rw [Matrix.smul_apply, smul_eq_mul]; exact S.mul_mem hinv (hadj b b')
    exact this N
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.Sh
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.LawLog

theorem limPt_of_steps : AddSt → ActSt → ContSt → LimPtSt := by
  intro hAdd hAct hCont
  intro C _ _ v d R _ _ O _ _ B hB σ _ κ _ w hw A a hA
  have hdI : ∀ c e e', IsIntV v (dAct C B c e e') := fun c e _ => hB.2.1 c e _
  have hAI : ∀ b e e', IsIntV v (A b e e') := by
    intro b e e'
    have h0 : IsIntV v (A b e e' - dAct C B (a 0 b) e e') := by
      have := hA 0 b e e'
      simpa [IsIntV] using this
    have : A b e e' = (A b e e' - dAct C B (a 0 b) e e') + dAct C B (a 0 b) e e' := by ring
    rw [this]
    exact (ptIsIntV_iff _).2 (Subring.add_mem _ ((ptIsIntV_iff _).1 h0) ((ptIsIntV_iff _).1 (hdI _ _ _)))
  have hN : ∀ N, IntLog (fglOf hB) (∑ b, mv (dAct C B (a N b)) (w b)) := fun N =>
    Finset.sum_induction _ (IntLog (fglOf hB)) (fun x y hx hy => (hAdd C v d (fglOf hB) σ).2.2 x y hx hy)
      (hAdd C v d (fglOf hB) σ).1 (fun b _ => (hAct C v d R O B hB σ (a N b)).2 _ (hw b))
  have hw0 : ∀ b i, constantCoeff (w b i) = 0 := fun b => (hw b).1
  have key : ∀ (M : κ → Matrix (Fin d) (Fin d) C) (i : Fin d),
      expPt (fglOf hB) (∑ b, mv (M b) (w b)) i =
        subst (fun q => ∑ x : κ × Fin d, M x.1 q x.2 • w x.1 x.2) (expOf (fglOf hB) i) := by
    intro M i
    unfold expPt
    congr 1
    funext q
    rw [Finset.sum_apply, Fintype.sum_prod_type]
    rfl
  refine ⟨fun i => ?_, fun i α => ?_⟩

  · rw [Finset.sum_apply, map_sum]
    exact Finset.sum_eq_zero fun b _ => cc_mv (A b) (hw0 b) i
  · obtain ⟨N₀, hN₀⟩ := hCont C v (Fin d) σ (κ × Fin d) (expOf (fglOf hB) i) (fun x => w x.1 x.2)
      (fun x => hw0 x.1 x.2) α
    have h1 := hN₀ (fun q x => A x.1 q x.2) (fun q x => dAct C B (a N₀ x.1) q x.2) (fun q x => hAI _ _ _)
      (fun q x => hdI _ _ _) (fun q x => hA N₀ x.1 q x.2)
    have h2 := (hN N₀).2 i α
    rw [key] at h2
    rw [key]
    rw [← sub_add_cancel (coeff α (subst (fun q => ∑ x : κ × Fin d, A x.1 q x.2 • w x.1 x.2)
      (expOf (fglOf hB) i) : MvPowerSeries σ C))
      (coeff α (subst (fun q => ∑ x : κ × Fin d, dAct C B (a N₀ x.1) q x.2 • w x.1 x.2)
      (expOf (fglOf hB) i) : MvPowerSeries σ C))]
    exact (ptIsIntV_iff _).2 (Subring.add_mem _ ((ptIsIntV_iff _).1 h1) ((ptIsIntV_iff _).1 h2))

end GlobalTheory.IsoTriv
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory.LawLog ReciprocityTheory.ChartRestriction.G.TB

theorem actSt : ActSt := by
  intro C _ _ v d R _ _ O _ _ B hB σ _ a

  have hφ0 : ∀ i, constantCoeff (B.actK C a i) = 0 := by
    intro i
    show constantCoeff (MvPowerSeries.map (algebraMap R C) (B.A.act a i)) = 0
    rw [MvPowerSeries.constantCoeff_map, GlobalTheory.FBMap.nc_act B.A a i, map_zero]

  have hhom : comp1 (B.actK C a) (GlobalTheory.FBMap.mapLaw (algebraMap R C) B.G).F =
      addOf (GlobalTheory.FBMap.mapLaw (algebraMap R C) B.G).F (comp1 (B.actK C a) (pt C (n := 2) d 0))
        (comp1 (B.actK C a) (pt C (n := 2) d 1)) := by
    have h := (GlobalTheory.FBMap.mapAct (algebraMap R C) B.A).hom a
    rw [GlobalTheory.LawLog.add_pt] at h
    exact h

  have hcomp := GlobalTheory.FactorDepth.logOf_comp_hom _ _ (B.actK C a) hφ0 hhom
  have h0 : ∀ e, constantCoeff (subst (oneVar C d) (B.actK C a e)) = 0 := fun e =>
    constantCoeff_subst_eq_zero hs_oneVar cc_oneVar (hφ0 e)
  have hl : ∀ e, subst (fun f => subst (oneVar C d) (B.actK C a f)) ((fglOf hB).lg e) =
      ∑ f, dAct C B a e f • (fglOf hB).lg f := by
    intro e
    calc subst (fun f => subst (oneVar C d) (B.actK C a f)) ((fglOf hB).lg e)
        = subst (oneVar C d)
            (comp1 (GlobalTheory.FormalLog.logOf (GlobalTheory.FBMap.mapLaw (algebraMap R C) B.G)) (B.actK C a) e) :=
          GlobalTheory.LawLog.subst_oneVar (oneVar C d) cc_oneVar (B.actK C a) hφ0
            (GlobalTheory.FormalLog.logOf (GlobalTheory.FBMap.mapLaw (algebraMap R C) B.G) e)
      _ = ∑ f, dAct C B a e f • (fglOf hB).lg f := by
          rw [hcomp]
          dsimp only

          rw [← coe_substAlgHom hs_oneVar, map_sum]
          simp only [map_smul, coe_substAlgHom]
          exact Finset.sum_congr rfl fun f _ => rfl

  have hexp : ∀ w : Fin d → MvPowerSeries σ C, (∀ i, constantCoeff (w i) = 0) →
      expPt (fglOf hB) (mv (dAct C B a) w) =
        fun i => subst (fun q : Fin 1 × Fin d => expPt (fglOf hB) w q.2) (B.actK C a i) := by
    intro w hw
    have hsE : HasSubst (fun f => subst w (GlobalTheory.FGDepth.expOf (fglOf hB) f)) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero fun f => cc_expPt (fglOf hB) hw f
    funext i
    have key := GlobalTheory.FactorDepth.exp_eq_of_log_hom (fglOf hB) (fglOf hB) _ h0 (dAct C B a) hl
      (mv (dAct C B a) w) w hw (fun e => rfl) i
    show subst (mv (dAct C B a) w) (GlobalTheory.FGDepth.expOf (fglOf hB) i) = _
    rw [key, subst_comp_subst_apply hs_oneVar hsE]
    congr 1
    funext q
    exact subst_X hsE q.2
  refine ⟨hexp, fun w hw => ⟨cc_mv (dAct C B a) hw.1, fun i => ?_⟩⟩

  rw [hexp w hw.1]
  exact ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v (hB.2.1 a i) (fun q => hw.2 q.2)
    (fun q => cc_expPt (fglOf hB) hw.1 q.2)

end GlobalTheory.IsoTriv
end
end

section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

theorem _root_.GlobalTheory.T.frobeniusMatrix_cofactor_eq_q_pow_frame : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ) (n h : ℕ) (γ : ((HW l).W K 1 LL hA.2.2).Gam) (b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(((HW l).W K 1 LL hA.2.2).N T)) (N : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n ↥(OL LL)), GlobalTheory.AdmLoc.CrysWith ((D.loc l).PD K) ((HW l).W K 1 LL hA.2.2).emb T.ρ U → (∀ i, ∀ u ∈ U i, 0 ≤ u ∧ u ≤ (h : ℤ)) → IsFrame ((HW l).W K 1 LL hA.2.2) T γ b N → ∀ i, ∃ Q : Mx (PowerSeries ↥(OL LL)) n n, (N.P i).map (inc l ↥(OL LL)) * Q = (q l ↥(OL LL) ^ h) • (1 : Mx (PowerSeries ↥(OL LL)) n n) := by
  first | exact @GlobalTheory.WachPlace.FrameHeight.frame_height | exact GlobalTheory.WachPlace.FrameHeight.frame_height | (intros; apply GlobalTheory.WachPlace.FrameHeight.frame_height <;> assumption)
end

section


theorem _root_.GlobalTheory.T.mass_bound_of_tamagawa_unitary : GlobalTheory.Published.TamagawaSpecialUnitary → GlobalTheory.UCls.MassBound := by
  first | exact @GlobalTheory.UCls.massBound_of_tamagawa | exact GlobalTheory.UCls.massBound_of_tamagawa | (intros; apply GlobalTheory.UCls.massBound_of_tamagawa <;> assumption)
end

end

section

@[expose] public section

open GlobalTheory.IsoTriv

theorem _root_.GlobalTheory.T.action_linear_logCoordinates_integral : ActSt := by
  first | exact @GlobalTheory.IsoTriv.actSt | exact GlobalTheory.IsoTriv.actSt | (intros; apply GlobalTheory.IsoTriv.actSt <;> assumption)

end
end

section

@[expose] public section

open GlobalTheory.IsoTriv

theorem _root_.GlobalTheory.T.limitActionIntegralPoint_of_steps : AddSt → ActSt → ContSt → LimPtSt := by
  first | exact @GlobalTheory.IsoTriv.limPt_of_steps | exact GlobalTheory.IsoTriv.limPt_of_steps | (intros; apply GlobalTheory.IsoTriv.limPt_of_steps <;> assumption)

end
end

section

@[expose] public section

open GlobalTheory.IsoTriv

theorem _root_.GlobalTheory.T.limitIsotropicFrameIntegral_of_steps : AddSt → ActSt → UnitSt → BiaddSt → FrameSt → FinSt → ContSt → LimFrameSt := by
  first | exact @GlobalTheory.IsoTriv.limFrame | exact GlobalTheory.IsoTriv.limFrame | (intros; apply GlobalTheory.IsoTriv.limFrame <;> assumption)

end
end

section

@[expose] public section

open GlobalTheory.IsoTriv

theorem _root_.GlobalTheory.T.primeIdempotentApproximationsDVR_proof : EpsSt := by
  first | exact @GlobalTheory.IsoTriv.PrimeIdempotent.epsSt | exact GlobalTheory.IsoTriv.PrimeIdempotent.epsSt | (intros; apply GlobalTheory.IsoTriv.PrimeIdempotent.epsSt <;> assumption)

end
end
