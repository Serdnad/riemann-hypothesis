module

import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle041
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle001
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle004
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.BlockHarmLevOfBlockHarm
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle044
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle013
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle015
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle039
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Data.ZMod.Basic
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.HermitianCurvature.Bundle001

@[expose] public section

section

open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer

theorem intg_nMul_of_intg (K : Type) [NormedField K] [IsUltrametricDist K] (F : FormalGroup K)
    (hF : Intg F.toPowerSeries) (n : ℕ) : Intg (nMul F n) := by
  apply GlobalTheory.ConvSer.intg_nMul_for_point <;> assumption

theorem exists_torsion_tower (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsAlgClosed K] [CharZero K] (p : ℕ) [Fact p.Prime] (F : FormalGroup K)
    (hF : Intg F.toPowerSeries) (hp : ‖PowerSeries.coeff p (nMul F p)‖ = 1)
    (hlt : ∀ k < p, ‖PowerSeries.coeff k (nMul F p)‖ < 1) :
    ∃ t : ℕ → K, (∀ n, ‖t n‖ < 1) ∧ t 0 = 0 ∧ t 1 ≠ 0 ∧
      ∀ n, ev1 (nMul F p) (t (n + 1)) = t n := by
  classical
  have hpr : p.Prime := Fact.out
  have hI := intg_nMul_of_intg K F hF p
  set h := nMul F p with hh
  obtain ⟨-, -, hpow, -, -, -, -, -, -, hiff⟩ := GlobalTheory.T.mvPowerSeries_integral_bounded_closure K Unit
  have hev := fun (x : K) (hx : ‖x‖ < 1) => GlobalTheory.T.powerSeriesEvalTsum_unitDisc_properties_alt K x hx
  have hbdd : ∀ f : PowerSeries K, Intg f → Bdd f := fun f hf => (hpow f 0).2.2 hf
  have hcoef : ∀ n, ‖PowerSeries.coeff n h‖ ≤ 1 := (hiff h).1.1 hI
  have h0 : PowerSeries.coeff 0 h = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact ((GlobalTheory.T.formalGroupNatMulSeries_properties K F).1 p).1
  have h0c : PowerSeries.constantCoeff h = 0 := ((GlobalTheory.T.formalGroupNatMulSeries_properties K F).1 p).1
  have h1 : PowerSeries.coeff 1 h = (p : K) := ((GlobalTheory.T.formalGroupNatMulSeries_properties K F).1 p).2
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hpr.ne_zero
  have hz : ‖(0 : K)‖ < 1 := by simp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hzero⟩ := hev 0 hz

  have hstep : ∀ c : {c : K // ‖c‖ < 1}, ∃ y : {y : K // ‖y‖ < 1}, ev1 h y = c := by
    rintro ⟨c, hc⟩
    have hIc : Intg (h - PowerSeries.C c) := by
      rw [(hiff _).1]
      intro n
      rcases n with _ | n
      · simp [h0c, hc.le]
      · rw [map_sub, PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero n), sub_zero]
        exact hcoef _
    obtain ⟨y, hy, hy0⟩ := GlobalTheory.T.exists_root_openDisc_of_weierstrassDegree K (h - PowerSeries.C c) p hpr.pos hIc (by
        rw [map_sub, PowerSeries.coeff_C, if_neg hpr.ne_zero, sub_zero]
        exact hp) (by
        intro k hk
        rcases k with _ | k
        · simpa [h0, h0c] using hc
        · rw [map_sub, PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero k), sub_zero]
          exact hlt _ hk)
    refine ⟨⟨y, hy⟩, ?_⟩
    obtain ⟨-, hops, hCe, -⟩ := hev y hy
    have hCI : Intg (PowerSeries.C c) := by
      rw [(hiff _).1]
      intro n
      rw [PowerSeries.coeff_C]
      split_ifs
      · exact hc.le
      · simp
    have e := (hops h (PowerSeries.C c) (hbdd h hI) (hbdd _ hCI)).2.1
    rw [hy0, hCe] at e
    simp only
    linear_combination -e

  set g : PowerSeries K := PowerSeries.mk fun k => PowerSeries.coeff (k + 1) h with hg
  have hgI : Intg g := by
    rw [(hiff _).1]
    intro n
    rw [hg, PowerSeries.coeff_mk]
    exact hcoef _
  have hp1 : 0 < p - 1 := by have := hpr.two_le; omega
  obtain ⟨x, hx, hx0⟩ := GlobalTheory.T.exists_root_openDisc_of_weierstrassDegree K g (p - 1) hp1 hgI (by
      rw [hg, PowerSeries.coeff_mk, Nat.sub_add_cancel hpr.one_lt.le]
      exact hp) (by
      intro k hk
      rw [hg, PowerSeries.coeff_mk]
      exact hlt _ (by omega))
  have hxne : x ≠ 0 := by
    rintro rfl
    rw [hzero, hg, PowerSeries.coeff_mk, h1] at hx0
    exact hp0 hx0
  have hXI : Intg (PowerSeries.X : PowerSeries K) := by
    rw [(hiff _).1]
    intro n
    rw [PowerSeries.coeff_X]
    split_ifs <;> simp
  have hXg : h = PowerSeries.X * g := by
    ext n
    rcases n with _ | n
    · simp [h0]
    · rw [PowerSeries.coeff_succ_X_mul, hg, PowerSeries.coeff_mk]
  have hxroot : ev1 h x = 0 := by
    obtain ⟨-, hops, -, hXe, -⟩ := hev x hx
    rw [hXg, ((hops _ _ (hbdd _ hXI) (hbdd _ hgI)).2.2), hXe, hx0, mul_zero]
  choose f hf using hstep
  let x0 : {y : K // ‖y‖ < 1} := ⟨x, hx⟩
  refine ⟨fun n => if n = 0 then 0 else ((f^[n - 1] x0 : {y : K // ‖y‖ < 1}) : K), ?_, ?_, ?_, ?_⟩
  · intro n
    dsimp only
    split_ifs
    · exact hz
    · exact (f^[n - 1] x0).2
  · simp
  · simpa [x0] using hxne
  · intro n
    rcases n with _ | m
    · simpa [x0] using hxroot
    · simp only [Nat.add_sub_cancel, if_neg (Nat.succ_ne_zero _), Function.iterate_succ_apply']
      exact hf _

end GlobalTheory.ConvSer
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BetaOfSum

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BetaEx GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility GlobalTheory.ShortLawsCompare

section Lattice

variable {E : Type} [Field E] [NumberField E] {n₁ n₂ : ℕ}

theorem mem_block (M₁ : Submodule (𝓞 E) (Fin n₁ → E)) (M₂ : Submodule (𝓞 E) (Fin n₂ → E))
    (v : Fin (n₁ + n₂) → E) : v ∈ (blockLat ⟨M₁⟩ ⟨M₂⟩).La ↔
      (fun i => v (Fin.castAdd n₂ i)) ∈ M₁ ∧ (fun j => v (Fin.natAdd n₁ j)) ∈ M₂ := Iff.rfl


omit [NumberField E] in
theorem det_block (u : Matrix (Fin (n₁ + n₂)) (Fin (n₁ + n₂)) E)
    (h : ∀ i j, u (Fin.castAdd n₂ i) (Fin.natAdd n₁ j) = 0) :
    u.det = (Matrix.of fun i j => u (Fin.castAdd n₂ i) (Fin.castAdd n₂ j)).det *
      (Matrix.of fun i j => u (Fin.natAdd n₁ i) (Fin.natAdd n₁ j)).det := by
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv, ← Matrix.det_fromBlocks_zero₁₂ _
    (Matrix.of fun i j => u (Fin.natAdd n₁ i) (Fin.castAdd n₂ j))]
  congr 1
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [h]


omit [NumberField E] in
theorem det_pure_mem (M₁ : Submodule (𝓞 E) (Fin n₁ → E)) (M₂ : Submodule (𝓞 E) (Fin n₂ → E))
    (w : Matrix (Fin (n₁ + n₂)) (Fin (n₁ + n₂)) E)
    (h₁ : ∀ i, (fun j => w i (Fin.castAdd n₂ j)) ∈ M₁) (h₂ : ∀ i, (fun j => w i (Fin.natAdd n₁ j)) ∈ M₂)
    (h : ∀ i, (∀ j, w i (Fin.castAdd n₂ j) = 0) ∨ ∀ j, w i (Fin.natAdd n₁ j) = 0) :
    w.det ∈ detSpan M₁ * detSpan M₂ := by
  by_cases h0 : w.det = 0
  · rw [h0]; exact zero_mem _
  have h0' := h0
  rw [Matrix.det_apply] at h0'
  obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h0'
  have hd : ∀ i, w (σ i) i ≠ 0 := fun i hi => hσ (by
    rw [Finset.prod_eq_zero (f := fun k => w (σ k) k) (Finset.mem_univ i) hi, smul_zero])
  have hm : (w.submatrix σ id).det ∈ detSpan M₁ * detSpan M₂ := by
    rw [det_block _ (fun i j => ((h (σ (Fin.castAdd n₂ i))).resolve_left fun g => hd _ (g i)) j)]
    exact Submodule.mul_mem_mul (det_mem _ fun i => h₁ _) (det_mem _ fun i => h₂ _)
  rw [Matrix.det_permute] at hm
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> rw [e] at hm
  · simpa using hm
  · simpa using hm

theorem detSpan_block (M₁ : Submodule (𝓞 E) (Fin n₁ → E)) (M₂ : Submodule (𝓞 E) (Fin n₂ → E)) :
    detSpan (blockLat ⟨M₁⟩ ⟨M₂⟩).La = detSpan M₁ * detSpan M₂ := by
  classical
  have z₁ : (fun _ => 0) ∈ M₁ := M₁.zero_mem
  have z₂ : (fun _ => 0) ∈ M₂ := M₂.zero_mem
  apply le_antisymm
  · refine Submodule.span_le.2 fun d hd => ?_
    obtain ⟨v, hv, rfl⟩ := (mem_detSet _ d).1 hd
    let a : Fin (n₁ + n₂) → Fin (n₁ + n₂) → E := fun i => Fin.append (fun j => v i (Fin.castAdd n₂ j)) 0
    let b : Fin (n₁ + n₂) → Fin (n₁ + n₂) → E := fun i => Fin.append 0 (fun j => v i (Fin.natAdd n₁ j))
    have e : (v : Fin (n₁ + n₂) → Fin (n₁ + n₂) → E) = a + b := by
      funext i j
      induction j using Fin.addCases <;> simp [a, b]
    have e2 : v.det = ∑ s : Finset (Fin (n₁ + n₂)), (Matrix.of (s.piecewise a b)).det := by
      have := (Matrix.detRowAlternating (n := Fin (n₁ + n₂)) (R := E)).toMultilinearMap.map_add_univ a b
      rw [← e] at this
      exact this
    rw [SetLike.mem_coe, e2]
    refine Submodule.sum_mem _ fun s _ => det_pure_mem M₁ M₂ _ (fun i => ?_) (fun i => ?_) (fun i => ?_)
    · by_cases hi : i ∈ s
      · simpa [hi, a] using ((mem_block _ _ _).1 (hv i)).1
      · simpa [hi, b] using z₁
    · by_cases hi : i ∈ s
      · simpa [hi, a] using z₂
      · simpa [hi, b] using ((mem_block _ _ _).1 (hv i)).2
    · by_cases hi : i ∈ s
      · exact Or.inr fun j => by simp [hi, a]
      · exact Or.inl fun j => by simp [hi, b]
  · rw [detSpan, detSpan, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨v, hv, rfl⟩ := (mem_detSet _ _).1 hx
    obtain ⟨w, hw, rfl⟩ := (mem_detSet _ _).1 hy
    let u : Matrix (Fin (n₁ + n₂)) (Fin (n₁ + n₂)) E :=
      Matrix.of (Fin.append (fun i => Fin.append (v i) 0) (fun i => Fin.append 0 (w i)))
    have e : u.det = v.det * w.det := by
      rw [det_block u (fun i j => by simp [u])]
      congr 2 <;> ext i j <;> simp [u]
    change v.det * w.det ∈ detSpan _
    rw [← e]
    refine det_mem _ fun i => (mem_block _ _ _).2 ?_
    induction i using Fin.addCases with
    | left i => exact ⟨by simpa [u] using hv i, by simpa [u] using z₂⟩
    | right i => exact ⟨by simpa [u] using z₁, by simpa [u] using hw i⟩

theorem block_Ln (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂) :
    (blockLat Λ₁ Λ₂).Ln = (blockLat ⟨Λ₁.Ln⟩ ⟨Λ₂.Ln⟩).La := by
  ext v
  change (v ∈ (blockLat Λ₁ Λ₂).La ∧ v ∈ stdLat E _) ↔ _
  rw [mem_std_block, mem_block, mem_block]
  exact and_and_and_comm

theorem index_block (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂) :
    ((blockLat Λ₁ Λ₂).Ln.toAddSubgroup.addSubgroupOf (blockLat Λ₁ Λ₂).La.toAddSubgroup).index =
      (Λ₁.Ln.toAddSubgroup.addSubgroupOf Λ₁.La.toAddSubgroup).index *
        (Λ₂.Ln.toAddSubgroup.addSubgroupOf Λ₂.La.toAddSubgroup).index := by
  let φ : (blockLat Λ₁ Λ₂).La.toAddSubgroup →+ Λ₁.La.toAddSubgroup × Λ₂.La.toAddSubgroup :=
    { toFun := fun v => (⟨fun i => v.1 (Fin.castAdd n₂ i), v.2.1⟩, ⟨fun j => v.1 (Fin.natAdd n₁ j), v.2.2⟩)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hφ : Function.Surjective φ := by
    rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    refine ⟨⟨Fin.append x y, (mem_block _ _ _).2 ⟨by simpa using hx, by simpa using hy⟩⟩, ?_⟩
    ext j <;> simp [φ]
  rw [← AddSubgroup.index_prod, ← AddSubgroup.index_comap_of_surjective _ hφ, block_Ln]
  rfl

end Lattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (c : Coeff l) {n₁ n₂ : ℕ}

theorem idealAt_block (M₁ : Submodule (𝓞 E) (Fin n₁ → E)) (M₂ : Submodule (𝓞 E) (Fin n₂ → E)) (τ : E →+* ℂ) :
    idealAt c (blockLat ⟨M₁⟩ ⟨M₂⟩).La τ = idealAt c M₁ τ * idealAt c M₂ τ := by
  have e := detSpan_block M₁ M₂
  unfold detSpan at e
  unfold idealAt
  rw [← span_image_span, e, Submodule.span_mul_span, span_image_span, Submodule.span_mul_span, Set.image_mul]

theorem isBeta_block {Λ₁ : GenLat E n₁} {Λ₂ : GenLat E n₂} {β₁ β₂ : c.F} (b₁ : IsBeta Dw c Λ₁ β₁)
    (b₂ : IsBeta Dw c Λ₂ β₂) : IsBeta Dw c (blockLat Λ₁ Λ₂) (β₁ * β₂) := by
  refine ⟨mul_ne_zero b₁.1 b₂.1, ?_, fun σ => ?_⟩
  · have e₁ := b₁.2.1
    have e₂ := b₂.2.1
    unfold BetaIs at e₁ e₂ ⊢
    rw [block_Ln]
    simp only [idealAt_block c Λ₁.La Λ₂.La, idealAt_block c Λ₁.Ln Λ₂.Ln, mul_pow, Finset.prod_mul_distrib]
    rw [← e₁, ← e₂, ← Set.singleton_mul_singleton, ← Submodule.span_mul_span, mul_mul_mul_comm]
  · rw [index_block, map_mul, norm_mul, mul_pow, b₁.2.2 σ, b₂.2.2 σ, Nat.cast_mul, mul_pow]

theorem isBeta_unit_block (n₁ : ℕ) (Λ₂ : GenLat E n₂) (β : c.F) :
    IsBeta Dw c (blockLat (unitLat E n₁) Λ₂) β ↔ IsBeta Dw c Λ₂ β := by
  have e : (unitLat E n₁).Ln = (unitLat E n₁).La := inf_idem _
  have hu : IsUnit (∏ τ : E →+* ℂ, idealAt c (unitLat E n₁).La τ ^ Dw.mult τ) :=
    IsUnit.prod_univ_iff.2 fun τ =>
      (isUnit_idealAt c (trivAt_std n₁ 0) (unimod_std n₁) zero_ne_one τ).pow _
  refine and_congr_right fun _ => and_congr ?_ (forall_congr' fun σ => ?_)
  · unfold BetaIs
    rw [block_Ln, e]
    simp only [idealAt_block c (unitLat E n₁).La Λ₂.La, idealAt_block c (unitLat E n₁).La Λ₂.Ln, mul_pow,
      Finset.prod_mul_distrib]
    rw [mul_left_comm, hu.mul_right_inj]
  · rw [index_block, e]
    simp

theorem blockBeta : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (c : Coeff l) (bad : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility.BlockBeta Dw c bad := by
  intro E _ _ _ H Dw l c bad
  refine ⟨fun n₁ n₂ Λ₁ Λ₂ h₁ h₂ β₁ β₂ β b₁ b₂ => ⟨fun b => ?_, ?_⟩,
    fun n₁ n₂ Λ₂ _ => ⟨GlobalTheory.Survey.BaseClassMove.isBeta_unit c n₁, isBeta_unit_block c n₁ Λ₂⟩⟩
  · have hB := latOK_block h₁ h₂
    exact isBeta_ratio c hB.1 hB.2.2 (isBeta_block c b₁ b₂) b
  · rintro ⟨ζ, hζ, rfl⟩
    exact isBeta_mul c (isBeta_block c b₁ b₂) hζ

end GlobalTheory.BetaOfSum
end
end

section

open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer

theorem seq_eq_iff_modEq_of_op {K : Type*} (G : K → K → K) (τ : ℕ → K)
    (hG : ∀ i j, G (τ i) (τ j) = τ (i + j)) (q : ℕ) (hq : 0 < q) (h0 : τ q = τ 0)
    (hord : ∀ {M : Type} [AddMonoid M] (x : M), (∀ d : ℕ, d • x = 0 ↔ τ d = τ 0) →
      addOrderOf x = q) (i j : ℕ) :
    τ i = τ j ↔ i ≡ j [MOD q] := by
  have shift : ∀ a m, τ m = τ 0 → τ (a + m) = τ a := by
    intro a m hm
    rw [← hG a m, hm, hG a 0, Nat.add_zero]
  have mulS : ∀ s, τ s = τ 0 → ∀ n, τ (s * n) = τ 0 := by
    intro s hs n
    induction n with
    | zero => rw [Nat.mul_zero]
    | succ n ih => rw [Nat.mul_succ, shift _ _ hs, ih]
  have cancel : ∀ a k, τ (a + k) = τ a → τ k = τ 0 := by
    intro a k hak
    have e : (q - 1) * a + a = q * a := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (Nat.succ_le_of_lt hq)]
    calc τ k = τ (k + q * a) := (shift k _ (mulS q h0 a)).symm
      _ = G (τ (a + k)) (τ ((q - 1) * a)) := by rw [hG, ← e]; congr 1; ac_rfl
      _ = G (τ a) (τ ((q - 1) * a)) := by rw [hak]
      _ = τ (q * a) := by rw [hG, Nat.add_comm, e]
      _ = τ 0 := mulS q h0 a
  classical
  have hex : ∃ r, 0 < r ∧ τ r = τ 0 := ⟨q, hq, h0⟩
  obtain ⟨r, hr, hmin⟩ : ∃ r, (0 < r ∧ τ r = τ 0) ∧ ∀ m < r, ¬ (0 < m ∧ τ m = τ 0) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  have hdvd : ∀ d, τ d = τ 0 ↔ r ∣ d := by
    intro d
    constructor
    · intro hd
      have hmod : τ (d % r) = τ 0 := by
        have h := shift (d % r) (r * (d / r)) (mulS r hr.2 _)
        rw [Nat.mod_add_div] at h
        rw [← h, hd]
      by_contra hnd
      have hpos : 0 < d % r := Nat.pos_of_ne_zero (fun h => hnd (Nat.dvd_of_mod_eq_zero h))
      exact hmin _ (Nat.mod_lt d hr.1) ⟨hpos, hmod⟩
    · rintro ⟨c, rfl⟩
      exact mulS r hr.2 c
  have hrq : r = q := by
    have h := hord (M := ZMod r) (1 : ZMod r) (fun d => by
      rw [nsmul_eq_mul, mul_one, CharP.cast_eq_zero_iff (ZMod r) r, hdvd])
    rwa [ZMod.addOrderOf_one] at h
  have key : ∀ d, τ d = τ 0 ↔ q ∣ d := by
    intro d; rw [hdvd, hrq]
  wlog hij : i ≤ j generalizing i j with H
  · rw [eq_comm, Nat.ModEq.comm]; exact H j i (by omega)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [Nat.modEq_iff_dvd' hij, Nat.add_sub_cancel_left, ← key, eq_comm]
  exact ⟨cancel i k, fun h => shift i k h⟩

theorem tower_exact_order : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (p : ℕ) [Fact p.Prime] (F : FormalGroup K), Intg F.toPowerSeries → ∀ t : ℕ → K, (∀ n, ‖t n‖ < 1) → t 0 = 0 → t 1 ≠ 0 → (∀ n, ev1 (nMul F p) (t (n + 1)) = t n) → (∀ n j, ev1 (nMul F (p * j)) (t (n + 1)) = ev1 (nMul F j) (t n)) ∧ (∀ n m j, ev1 (nMul F (p ^ m * j)) (t (n + m)) = ev1 (nMul F j) (t n)) ∧ ∀ n i j, ev1 (nMul F i) (t n) = ev1 (nMul F j) (t n) ↔ i ≡ j [MOD p ^ n] := by
  intro K _ _ _ p _ F hF t ht ht0 ht1 htp
  have base := (GlobalTheory.T.formalGroupNatMulSeries_eval_openDisc_properties K F hF).2
  have hA : ∀ n j, ev1 (nMul F (p * j)) (t (n + 1)) = ev1 (nMul F j) (t n) := by
    intro n j
    rw [← htp n, (base (t (n + 1)) (ht _)).2.2.2.2.1 j p, Nat.mul_comm p j]
  have hB : ∀ n m j, ev1 (nMul F (p ^ m * j)) (t (n + m)) = ev1 (nMul F j) (t n) := by
    intro n m
    induction m with
    | zero => intro j; simp
    | succ m ih =>
      intro j
      rw [← Nat.add_assoc, pow_succ', Nat.mul_assoc, hA, ih]
  refine ⟨hA, hB, fun n i j => ?_⟩
  have hτ0 : ev1 (nMul F 0) (t n) = 0 := (base (t n) (ht n)).1
  have hpn : ev1 (nMul F (p ^ n)) (t n) = 0 := by
    have h := hB 0 n 1
    rw [Nat.mul_one, Nat.zero_add, (base (t 0) (ht 0)).2.1, ht0] at h
    exact h
  refine seq_eq_iff_modEq_of_op (fun a b => ev F.toPowerSeries ![a, b])
    (fun d => ev1 (nMul F d) (t n)) (base (t n) (ht n)).2.2.2.1 (p ^ n)
    (pow_pos (Fact.out : p.Prime).pos n) (by simp only [hpn, hτ0]) ?_ i j
  intro M _ x hx
  have hx' : ∀ d : ℕ, d • x = 0 ↔ ev1 (nMul F d) (t n) = 0 := by
    intro d; rw [hx d]; simp only [hτ0]
  rcases n with _ | k
  · have h := (hx' 1).2 (by rw [(base (t 0) (ht 0)).2.1, ht0])
    rw [one_nsmul] at h
    subst h
    simp
  · have h1k : ev1 (nMul F (p ^ k)) (t (k + 1)) = t 1 := by
      have h := hB 1 k 1
      rw [Nat.mul_one, Nat.add_comm 1 k, (base (t 1) (ht 1)).2.1] at h
      exact h
    exact addOrderOf_eq_prime_pow (fun h => ht1 (by rw [← h1k]; exact (hx' _).1 h)) ((hx' _).2 hpn)

end GlobalTheory.ConvSer
end

section

set_option autoImplicit false

namespace GlobalTheory.CharDepth

open IsLocalRing Formalism.L2.Pj

theorem exists_local_extension_of_integral {A B O C : Type} [CommRing A] [IsDomain A] [IsLocalRing A]
    [CommRing B] [IsDomain B] [IsLocalRing B] [CommRing O] [IsLocalRing O] [Field C] [IsAlgClosed C]
    [Algebra O C] (v : Valuation C NNReal) (hv : v.Integers O) (φ : A →+* B) (hφ : Function.Injective φ)
    (hint : φ.IsIntegral) (ι : A →+* O) [IsLocalHom ι]
    (hι : Function.Injective ((algebraMap O C).comp ι)) :
    ∃ ι' : B →+* O, IsLocalHom ι' ∧ ι'.comp φ = ι := by
  first
  | (rename_i h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 h_12 h_13 h_14 h_21; revert A B O C h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 h_12 h_13 h_14 v hv φ hφ hint ι h_21 hι; exact @_root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension)
  | exact @_root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension
  | exact _root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension
  | (apply _root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension <;> assumption)
  | (intros; apply _root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension ..)

theorem ValExt.exists_local_extension :
    ∀ (T T' : CDVR) (φ : T.V →+* T'.V), Function.Injective φ → φ.Finite → ∀ (p : ℕ) [Fact p.Prime]
      (X : ValExt T p), ∃ ι' : T'.V →+* X.O, IsLocalHom ι' ∧ ι'.comp φ = X.ι := by
  intro T T' φ hφ hfin p _ X
  haveI := X.ι_local
  refine exists_local_extension_of_integral X.v X.ints φ hφ hfin.to_isIntegral X.ι ?_
  have h : (algebraMap X.O X.C).comp X.ι = X.ιF.comp (algebraMap T.V T.Fr) := by
    ext x; exact (X.comp x).symm
  rw [h, RingHom.coe_comp]
  exact X.ιF.injective.comp (IsFractionRing.injective T.V T.Fr)

end GlobalTheory.CharDepth
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.splitCasimir_eigenvalue_on_dualTensor_summand : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (Ns : Type) [AddCommGroup Ns] [Module ℂ Ns] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ M) (F : Fin n → Fin n → Module.End ℂ Ns) (io : Ns →ₗ[ℂ] (Fin n → M)) (mu : Fin n → ℝ) (s : Fin n), (∀ w, Formalism.REAL.Cas E w = (casG mu : ℂ) • w) → (∀ y, Formalism.REAL.Cas F y = (casG (mu - Pi.single s 1) : ℂ) • y) → (∀ a b y, io (F a b y) = dualTens E a b (io y)) → ∀ y, splitCas E (io y) = ((-mu s + (1 - (n : ℝ)) / 2 : ℝ) : ℂ) • io y := by
  first | exact @GlobalTheory.splitCas_on_summand | exact GlobalTheory.splitCas_on_summand | (intros; apply GlobalTheory.splitCas_on_summand <;> assumption)
end
