module

public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Order.Real
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

section

open scoped ENNReal

namespace GlobalTheory

open MulAction

theorem encard_fiber_orbit_mul_stabilizer {Γ L Y : Type} [Group Γ] [MulAction Γ L] [MulAction Γ Y]
    (π : L → Y) (hπ : ∀ (g : Γ) (x : L), π (g • x) = g • π x) (x : L) (y : Y) (g : Γ)
    (hg : g • π x = y) :
    ({z : L | π z = y ∧ z ∈ orbit Γ x}).encard * (stabilizer Γ x : Set Γ).encard
      = (stabilizer Γ y : Set Γ).encard := by
  classical
  have hx0 : π (g • x) = y := by rw [hπ, hg]
  have hset : (orbit (stabilizer Γ y) (g • x) : Set L) = {z : L | π z = y ∧ z ∈ orbit Γ x} := by
    ext z
    constructor
    · rintro ⟨h, rfl⟩
      have hh : (h : Γ) • y = y := mem_stabilizer_iff.mp h.2
      refine ⟨?_, (h : Γ) * g, ?_⟩
      · show π ((h : Γ) • g • x) = y
        rw [hπ, hx0, hh]
      · show ((h : Γ) * g) • x = (h : Γ) • g • x
        rw [mul_smul]
    · rintro ⟨hz, k, rfl⟩
      have hk : k * g⁻¹ ∈ stabilizer Γ y := by
        rw [mem_stabilizer_iff]
        calc (k * g⁻¹) • y = (k * g⁻¹) • g • π x := by rw [hg]
          _ = π (k • x) := by rw [mul_smul, inv_smul_smul, hπ]
          _ = y := hz
      exact ⟨⟨k * g⁻¹, hk⟩, show (k * g⁻¹) • g • x = k • x by rw [mul_smul, inv_smul_smul]⟩
  have e : stabilizer (stabilizer Γ y) (g • x) ≃ stabilizer Γ x :=
    { toFun := fun s => ⟨g⁻¹ * ((s : stabilizer Γ y) : Γ) * g, by
        have hs : ((s : stabilizer Γ y) : Γ) • g • x = g • x := mem_stabilizer_iff.mp s.2
        rw [mem_stabilizer_iff, mul_smul, mul_smul, hs, inv_smul_smul]⟩
      invFun := fun t => ⟨⟨g * (t : Γ) * g⁻¹, by
          have ht : (t : Γ) • x = x := mem_stabilizer_iff.mp t.2
          rw [mem_stabilizer_iff, ← hg, mul_smul, mul_smul, inv_smul_smul, ← hπ, ht]⟩, by
          have ht : (t : Γ) • x = x := mem_stabilizer_iff.mp t.2
          show (g * (t : Γ) * g⁻¹) • g • x = g • x
          rw [mul_smul, mul_smul, inv_smul_smul, ht]⟩
      left_inv := fun s => by
        apply Subtype.ext; apply Subtype.ext
        show g * (g⁻¹ * ((s : stabilizer Γ y) : Γ) * g) * g⁻¹ = ((s : stabilizer Γ y) : Γ)
        group
      right_inv := fun t => by
        apply Subtype.ext
        show g⁻¹ * (g * (t : Γ) * g⁻¹) * g = (t : Γ)
        group }
  have key := ENat.card_congr
    (Subgroup.groupEquivQuotientProdSubgroup (s := stabilizer (stabilizer Γ y) (g • x)))
  rw [ENat.card_prod, ← ENat.card_congr (orbitEquivQuotientStabilizer (stabilizer Γ y) (g • x)),
    ENat.card_congr e] at key
  rw [← hset]
  exact key.symm

theorem encard_eq_tsum_fibers {L Q : Type} (F : Set L) (q : L → Q) :
    (F.encard : ℝ≥0∞) = ∑' o : Q, (({z | z ∈ F ∧ q z = o}).encard : ℝ≥0∞) := by
  classical
  have h1 : ∑' _ : F, (1 : ℝ≥0∞) = ∑' _ : (Σ o : Q, {z : F // q z = o}), (1 : ℝ≥0∞) :=
    ((Equiv.sigmaFiberEquiv (fun z : F => q z)).tsum_eq (fun _ => (1 : ℝ≥0∞))).symm
  rw [← ENNReal.tsum_set_one F, h1, ENNReal.tsum_sigma']
  refine tsum_congr fun o => ?_
  simp only [ENNReal.tsum_one]
  congr 1
  exact ENat.card_congr
    { toFun := fun z => ⟨z.1.1, z.1.2, z.2⟩
      invFun := fun z => ⟨⟨z.1, z.2.1⟩, z.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

private lemma inv_coe_mul_mul_coe_eq_inv_coe (a b : ℕ∞) (h0 : a * b ≠ 0) (ht : a * b ≠ ⊤) :
    (((a * b : ℕ∞) : ℝ≥0∞))⁻¹ * (a : ℝ≥0∞) = (b : ℝ≥0∞)⁻¹ := by
  have ha0 : a ≠ 0 := left_ne_zero_of_mul h0
  have hb0 : b ≠ 0 := right_ne_zero_of_mul h0
  induction a using ENat.recTopCoe with
  | top => exact absurd (ENat.top_mul hb0) ht
  | coe m =>
    induction b using ENat.recTopCoe with
    | top => exact absurd (by rw [mul_comm]; exact ENat.top_mul ha0) ht
    | coe k =>
      have hm : (m : ℝ≥0∞) ≠ 0 := by exact_mod_cast ha0
      have hk : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast hb0
      rw [ENat.toENNReal_mul, ENat.toENNReal_coe, ENat.toENNReal_coe,
        ENNReal.mul_inv (Or.inl hm) (Or.inr hk), mul_comm (m : ℝ≥0∞)⁻¹, mul_assoc,
        ENNReal.inv_mul_cancel hm (ENNReal.natCast_ne_top m), mul_one]

private lemma quotient_mk_map_eq_of_mem_orbit {Γ L Y : Type} [Group Γ] [MulAction Γ L] [MulAction Γ Y]
    (π : L → Y) (hπ : ∀ (g : Γ) (x : L), π (g • x) = g • π x) {a b : L} (h : a ∈ orbit Γ b) :
    Quotient.mk (orbitRel Γ Y) (π a) = Quotient.mk (orbitRel Γ Y) (π b) := by
  obtain ⟨g, rfl⟩ := h
  apply Quotient.sound
  show π (g • b) ∈ orbit Γ (π b)
  rw [hπ]
  exact mem_orbit _ g

theorem tsum_inv_stabilizer_eq_tsum_mul_fiber {Γ L Y : Type} [Group Γ] [MulAction Γ L]
    [MulAction Γ Y] (π : L → Y) (hπ : ∀ (g : Γ) (x : L), π (g • x) = g • π x)
    (hfin : ∀ y : Y, (∃ x, π x = y) → Finite (MulAction.stabilizer Γ y)) :
    (∑' o : MulAction.orbitRel.Quotient Γ L,
        (((MulAction.stabilizer Γ o.out : Set Γ).encard : ℝ≥0∞))⁻¹)
      = ∑' o : MulAction.orbitRel.Quotient Γ Y,
        (((MulAction.stabilizer Γ o.out : Set Γ).encard : ℝ≥0∞))⁻¹
          * (((π ⁻¹' {o.out}).encard : ℝ≥0∞)) := by
  classical
  set φ : orbitRel.Quotient Γ L → orbitRel.Quotient Γ Y :=
    fun o => Quotient.mk (orbitRel Γ Y) (π o.out) with hφ
  have hsplit := ((Equiv.sigmaFiberEquiv φ).tsum_eq
      (fun o : orbitRel.Quotient Γ L => (((stabilizer Γ o.out : Set Γ).encard : ℝ≥0∞))⁻¹)).symm.trans
    (ENNReal.tsum_sigma' _)
  refine hsplit.trans (tsum_congr fun O => ?_)
  change ∑' o : {o // φ o = O}, (((stabilizer Γ o.1.out : Set Γ).encard : ℝ≥0∞))⁻¹ = _
  have hsupp : Function.support (fun o : orbitRel.Quotient Γ L =>
      ((({z | z ∈ π ⁻¹' {O.out} ∧ Quotient.mk (orbitRel Γ L) z = o}).encard : ℕ∞) : ℝ≥0∞))
      ⊆ {o | φ o = O} := by
    intro o ho
    obtain ⟨z, hz, hzo⟩ : ({z | z ∈ π ⁻¹' {O.out} ∧ Quotient.mk (orbitRel Γ L) z = o}).Nonempty := by
      rw [← Set.encard_pos, pos_iff_ne_zero]
      intro h0
      exact ho (by simp only [h0, ENat.toENNReal_zero])
    have hzo' : o.out ∈ orbit Γ z := by
      apply orbitRel_apply.mp
      apply Quotient.exact
      rw [Quotient.out_eq]
      exact hzo.symm
    show Quotient.mk (orbitRel Γ Y) (π o.out) = O
    rw [quotient_mk_map_eq_of_mem_orbit π hπ hzo', show π z = O.out from hz]
    exact Quotient.out_eq O
  rw [encard_eq_tsum_fibers (π ⁻¹' {O.out}) (Quotient.mk (orbitRel Γ L)),
    ← tsum_subtype_eq_of_support_subset hsupp, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun o => ?_
  have hx : Quotient.mk (orbitRel Γ Y) (π o.1.out) = Quotient.mk (orbitRel Γ Y) O.out := by
    rw [Quotient.out_eq O]
    exact o.2
  obtain ⟨h, hh⟩ : π o.1.out ∈ orbit Γ O.out := orbitRel_apply.mp (Quotient.exact hx)
  have hg : h⁻¹ • π o.1.out = O.out := by rw [← hh, inv_smul_smul]
  have hF : {z | z ∈ π ⁻¹' {O.out} ∧ Quotient.mk (orbitRel Γ L) z = o.1}
      = {z : L | π z = O.out ∧ z ∈ orbit Γ o.1.out} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
    refine and_congr Iff.rfl ⟨fun hz => ?_, fun hz => ?_⟩
    · apply orbitRel_apply.mp
      apply Quotient.exact
      rw [Quotient.out_eq]
      exact hz
    · rw [← Quotient.out_eq o.1]
      exact Quotient.sound (orbitRel_apply.mpr hz)
  have hmul := encard_fiber_orbit_mul_stabilizer π hπ o.1.out O.out h⁻¹ hg
  have hfinY : Finite (stabilizer Γ O.out) := hfin O.out ⟨h⁻¹ • o.1.out, by rw [hπ, hg]⟩
  have hY0 : (stabilizer Γ O.out : Set Γ).encard ≠ 0 := by
    rw [Ne, Set.encard_eq_zero]
    exact Set.nonempty_iff_ne_empty.mp ⟨1, (stabilizer Γ O.out).one_mem⟩
  have hYt : (stabilizer Γ O.out : Set Γ).encard ≠ ⊤ := by
    rw [Ne, Set.encard_eq_top_iff, Set.not_infinite]
    exact Set.toFinite _
  rw [hF, ← hmul]
  rw [← hmul] at hY0 hYt
  exact (inv_coe_mul_mul_coe_eq_inv_coe _ _ hY0 hYt).symm

end GlobalTheory
end

section

namespace GlobalTheory.CoordScale
open MeasureTheory

theorem sigmaFinite_smul {α : Type} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] {c : ENNReal}
    (hc : c ≠ ⊤) : SigmaFinite (c • μ) := by
  have h : c • μ = c.toNNReal • μ := by
    rw [ENNReal.smul_def, ENNReal.coe_toNNReal hc]
  rw [h]
  infer_instance

theorem pi_smul_ne_top {ι : Type} [Fintype ι] {α : ι → Type} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (c : ι → ENNReal) (hc : ∀ i, c i ≠ ⊤) :
    Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  have : ∀ i, SigmaFinite (c i • μ i) := fun i => sigmaFinite_smul (μ i) (hc i)
  refine Measure.pi_eq (fun s hs => ?_)
  simp only [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, Finset.prod_mul_distrib]

theorem measurePreserving_inv_mul (r : ℝ) (hr : 0 < r) :
    MeasurePreserving (fun z : ℂ => ((r : ℂ))⁻¹ * z) volume
      (ENNReal.ofReal (r ^ 2) • (volume : Measure ℂ)) := by
  refine ⟨measurable_id.const_mul _, ?_⟩
  have hfun : (fun z : ℂ => ((r : ℂ))⁻¹ * z) = fun z => (r⁻¹ : ℝ) • z := by
    funext z
    rw [Complex.real_smul, Complex.ofReal_inv]
  rw [hfun, Measure.map_addHaar_smul volume (inv_ne_zero hr.ne'), Complex.finrank_real_complex,
    inv_pow, inv_inv, abs_of_pos (by positivity)]

private theorem map_pi_reindex_eq_pi_of_map_eq {ι ι' β γ : Type} [Fintype ι] [Fintype ι'] [MeasurableSpace β]
    [MeasurableSpace γ] (e : ι ≃ ι') (μ : Measure β) [SigmaFinite μ] (ν : ι → Measure γ)
    [∀ i, SigmaFinite (ν i)] (h : ι → β → γ) (hh : ∀ i, Measurable (h i))
    (hmap : ∀ i, Measure.map (h i) μ = ν i) :
    Measure.map (fun (x : ι' → β) (i : ι) => h i (x (e i))) (Measure.pi fun _ => μ) =
      Measure.pi ν := by
  have hm : Measurable (fun (x : ι' → β) (i : ι) => h i (x (e i))) :=
    Measurable.of_eval (fun i => (hh i).comp (measurable_pi_apply (e i)))
  symm
  refine Measure.pi_eq (fun s hs => ?_)
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun (x : ι' → β) (i : ι) => h i (x (e i))) ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun i' => h (e.symm i') ⁻¹' s (e.symm i')) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    constructor
    · intro hx i'
      have := hx (e.symm i')
      rwa [Equiv.apply_symm_apply] at this
    · intro hx i
      have := hx (e i)
      rwa [Equiv.symm_apply_apply] at this
  rw [hpre, Measure.pi_pi]
  refine (Finset.prod_congr rfl (fun i' _ => ?_)).trans (Equiv.prod_comp e.symm (fun i => ν i (s i)))
  rw [← hmap (e.symm i'), Measure.map_apply (hh _) (hs _)]

theorem measure_preimage_reindex_scale_le : ∀ (ι ι' κ κ' : Type) [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype κ'] (e : ι ≃ ι') (f : κ ≃ κ') (ρ c : ℝ) (d : κ → ℕ), 1 ≤ ρ → c ≤ 1 → ∀ A : Set (ι → κ → ℂ), MeasurableSet A → (MeasureTheory.Measure.pi fun _ : ι' => MeasureTheory.Measure.pi fun _ : κ' => ENNReal.ofReal c • (MeasureTheory.volume : MeasureTheory.Measure ℂ)) ((fun (x : ι' → κ' → ℂ) (i : ι) (q : κ) => ((ρ : ℂ) ^ d q)⁻¹ * x (e i) (f q)) ⁻¹' A) ≤ MeasureTheory.volume A * ENNReal.ofReal (ρ ^ (2 * Fintype.card ι * ∑ q, d q)) := by
  intro ι ι' κ κ' _ _ _ _ e f ρ c d hρ hc A hA
  have hρ0 : 0 < ρ := lt_of_lt_of_le one_pos hρ
  set C : ENNReal := ENNReal.ofReal c with hCdef
  have hCt : C ≠ ⊤ := ENNReal.ofReal_ne_top
  have : SigmaFinite (C • (volume : Measure ℂ)) := sigmaFinite_smul _ hCt
  set w : κ → ENNReal := fun q => C * ENNReal.ofReal ((ρ ^ d q) ^ 2) with hwdef
  have hwt : ∀ q, w q ≠ ⊤ := fun q => ENNReal.mul_ne_top hCt ENNReal.ofReal_ne_top
  have : ∀ q, SigmaFinite (w q • (volume : Measure ℂ)) := fun q => sigmaFinite_smul _ (hwt q)
  have hin : Measure.map (fun (y : κ' → ℂ) (q : κ) => ((ρ : ℂ) ^ d q)⁻¹ * y (f q))
      (Measure.pi fun _ : κ' => C • (volume : Measure ℂ)) =
      Measure.pi fun q : κ => w q • (volume : Measure ℂ) := by
    refine map_pi_reindex_eq_pi_of_map_eq f (C • (volume : Measure ℂ)) (fun q => w q • (volume : Measure ℂ))
      (fun q z => ((ρ : ℂ) ^ d q)⁻¹ * z) (fun q => measurable_const.mul measurable_id) (fun q => ?_)
    show Measure.map (fun z : ℂ => ((ρ : ℂ) ^ d q)⁻¹ * z) (C • volume) = w q • volume
    have hfun : (fun z : ℂ => ((ρ : ℂ) ^ d q)⁻¹ * z) = fun z => (((ρ ^ d q : ℝ) : ℂ))⁻¹ * z := by
      funext z
      rw [Complex.ofReal_pow]
    rw [hfun, Measure.map_smul (R := ENNReal) C
      (hf := (measurable_const_mul _).aemeasurable),
      (measurePreserving_inv_mul (ρ ^ d q) (pow_pos hρ0 _)).map_eq,
      smul_smul]
  set K : ENNReal := ∏ q, w q with hKdef
  have hKt : K ≠ ⊤ := ENNReal.prod_ne_top (fun q _ => hwt q)
  have hin' : Measure.map (fun (y : κ' → ℂ) (q : κ) => ((ρ : ℂ) ^ d q)⁻¹ * y (f q))
      (Measure.pi fun _ : κ' => C • (volume : Measure ℂ)) = K • (volume : Measure (κ → ℂ)) := by
    rw [hin, pi_smul_ne_top (fun _ => (volume : Measure ℂ)) w hwt]
    rfl
  have : SigmaFinite (K • (volume : Measure (κ → ℂ))) := sigmaFinite_smul _ hKt
  have hinm : Measurable (fun (y : κ' → ℂ) (q : κ) => ((ρ : ℂ) ^ d q)⁻¹ * y (f q)) :=
    Measurable.of_eval (fun q => (measurable_pi_apply (f q)).const_mul _)
  have hout : Measure.map (fun (x : ι' → κ' → ℂ) (i : ι) (q : κ) => ((ρ : ℂ) ^ d q)⁻¹ * x (e i) (f q))
      (MeasureTheory.Measure.pi fun _ : ι' =>
        MeasureTheory.Measure.pi fun _ : κ' => ENNReal.ofReal c • (MeasureTheory.volume : MeasureTheory.Measure ℂ)) =
      (K ^ Fintype.card ι) • (volume : Measure (ι → κ → ℂ)) := by
    have h1 := map_pi_reindex_eq_pi_of_map_eq e (Measure.pi fun _ : κ' => C • (volume : Measure ℂ))
      (fun _ : ι => K • (volume : Measure (κ → ℂ)))
      (fun _ (y : κ' → ℂ) (q : κ) => ((ρ : ℂ) ^ d q)⁻¹ * y (f q)) (fun _ => hinm) (fun _ => hin')
    refine h1.trans ?_
    rw [pi_smul_ne_top (fun _ : ι => (volume : Measure (κ → ℂ))) (fun _ => K) (fun _ => hKt),
      Finset.prod_const, Finset.card_univ]
    rfl
  have hgm : Measurable (fun (x : ι' → κ' → ℂ) (i : ι) (q : κ) => ((ρ : ℂ) ^ d q)⁻¹ * x (e i) (f q)) :=
    Measurable.of_eval (fun i => hinm.comp (measurable_pi_apply (e i)))
  rw [← Measure.map_apply hgm hA, hout, Measure.smul_apply, smul_eq_mul, mul_comm]
  have hC1 : C ≤ 1 := ENNReal.ofReal_le_one.mpr hc
  have hK1 : K ≤ ∏ q, ENNReal.ofReal ((ρ ^ d q) ^ 2) := by
    refine Finset.prod_le_prod' (fun q _ => ?_)
    calc w q = C * ENNReal.ofReal ((ρ ^ d q) ^ 2) := rfl
      _ ≤ 1 * ENNReal.ofReal ((ρ ^ d q) ^ 2) := by gcongr
      _ = ENNReal.ofReal ((ρ ^ d q) ^ 2) := one_mul _
  have hprod : ∏ q, ENNReal.ofReal ((ρ ^ d q) ^ 2) = ENNReal.ofReal (∏ q, (ρ ^ d q) ^ 2) :=
    (ENNReal.ofReal_prod_of_nonneg (fun q _ => by positivity)).symm
  have hreal : (∏ q, (ρ ^ d q) ^ 2) ^ Fintype.card ι = ρ ^ (2 * Fintype.card ι * ∑ q, d q) := by
    rw [Finset.prod_pow, Finset.prod_pow_eq_pow_sum, ← pow_mul, ← pow_mul]
    congr 1
    ring
  have hK2 : K ^ Fintype.card ι ≤ ENNReal.ofReal (ρ ^ (2 * Fintype.card ι * ∑ q, d q)) := by
    rw [← hreal, ENNReal.ofReal_pow (by positivity), ← hprod]
    exact pow_le_pow_left' hK1 _
  gcongr

end GlobalTheory.CoordScale
end

section

namespace GlobalTheory.CardQuotientPow

open Module Submodule

theorem card_quot_pow {R : Type} [CommRing R] [IsDomain R] {p : R} (hp : Irreducible p) (k : ℕ) :
    Nat.card (R ⧸ Ideal.span {p ^ k}) = Nat.card (R ⧸ Ideal.span {p}) ^ k := by
  have key : ∀ I : Ideal R, Nat.card (R ⧸ I) = I.toAddSubgroup.index := fun I => rfl
  induction k with
  | zero => rw [key]; simp
  | succ k ih =>
    rw [pow_succ (Nat.card (R ⧸ Ideal.span {p})) k, ← ih, key, key, key]
    have hle : (Ideal.span {p ^ (k+1)}).toAddSubgroup ≤ (Ideal.span {p ^ k}).toAddSubgroup := by
      intro x hx
      exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow p (Nat.le_succ k)) hx
    rw [← AddSubgroup.relIndex_mul_index hle, mul_comm]
    congr 1
    let f : R →+ R := AddMonoidHom.mulLeft (p ^ k)
    have hr : f.range = (Ideal.span {p ^ k}).toAddSubgroup := by
      ext x
      simp only [AddMonoidHom.mem_range, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton', f,
        AddMonoidHom.coe_mulLeft]
      constructor
      · rintro ⟨y, rfl⟩; exact ⟨y, mul_comm _ _⟩
      · rintro ⟨y, rfl⟩; exact ⟨y, mul_comm _ _⟩
    have hc : (Ideal.span {p ^ (k+1)}).toAddSubgroup.comap f = (Ideal.span {p}).toAddSubgroup := by
      ext x
      simp only [AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton, f,
        AddMonoidHom.coe_mulLeft]
      rw [pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ hp.ne_zero)]
    rw [← hr, ← AddSubgroup.index_comap, hc]

theorem main {R M ι : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup M] [Module R M] [Fintype ι] (b : Module.Basis ι R M) {p : R}
    (hp : Irreducible p) (φ : M →ₗ[R] M) (hφ : Function.Injective φ) :
    ∃ m : ℕ, Associated (LinearMap.det φ) (p ^ m) ∧
      Nat.card (M ⧸ LinearMap.range φ) = Nat.card (R ⧸ Ideal.span {p}) ^ m := by
  classical
  set N := LinearMap.range φ with hN
  let e : M ≃ₗ[R] N := LinearEquiv.ofInjective φ hφ
  have h : finrank R N = finrank R M := e.finrank_eq.symm
  let a := smithNormalFormCoeffs b h
  let b' := smithNormalFormTopBasis b h
  let ab := smithNormalFormBotBasis b h
  have ab_eq := smithNormalFormBotBasis_def b h
  let f : M →ₗ[R] M := N.subtype ∘ₗ (b'.equiv ab (Equiv.refl _) : M →ₗ[R] N)
  have ha : ∀ i, f (b' i) = a i • b' i := by
    intro i
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe, b'.equiv_apply, Equiv.refl_apply,
      Submodule.subtype_apply]
    exact ab_eq i
  have hdetf : LinearMap.det f = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b', ← Matrix.det_diagonal]
    congr 1; ext i j
    rw [LinearMap.toMatrix_apply, ha, map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul,
      mul_one]
    by_cases hij : i = j
    · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  have hφf : Associated (LinearMap.det φ) (LinearMap.det f) := by
    have : φ = N.subtype ∘ₗ (e : M →ₗ[R] N) := by ext x; rfl
    rw [this]
    exact LinearMap.associated_det_comp_equiv _ _ _
  choose k hk using fun i =>
    IsDiscreteValuationRing.associated_pow_irreducible (smithNormalFormCoeffs_ne_zero b h i) hp
  refine ⟨∑ i, k i, ?_, ?_⟩
  · rw [← Finset.prod_pow_eq_pow_sum]
    refine hφf.trans ?_
    rw [hdetf]
    exact Associated.prod _ _ _ fun i _ => hk i
  · rw [Nat.card_congr (quotientEquivPiSpan N b h).toEquiv, Nat.card_pi,
      ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← card_quot_pow hp, Ideal.span_singleton_eq_span_singleton.mpr (hk i)]

end GlobalTheory.CardQuotientPow
end

section

namespace GlobalTheory.IntegrableExpNegAbs

open MeasureTheory Set

theorem integrable_exp_neg_mul_abs {c : ℝ} (hc : (0 : ℝ) < c) :
    MeasureTheory.Integrable (fun (s : ℝ) ↦ Real.exp (-(c * |s|))) MeasureTheory.MeasureSpace.volume := by
  have h1 : IntegrableOn (fun s : ℝ ↦ Real.exp (-(c * |s|))) (Ioi 0) volume := by
    refine (integrableOn_exp_mul_Ioi (a := -c) (by linarith) 0).congr_fun ?_ measurableSet_Ioi
    intro x hx
    have hx' : 0 < x := hx
    simp only [abs_of_pos hx', neg_mul]
  have h2 : IntegrableOn (fun s : ℝ ↦ Real.exp (-(c * |s|))) (Iic 0) volume := by
    refine (integrableOn_exp_mul_Iic (a := c) hc 0).congr_fun ?_ measurableSet_Iic
    intro x hx
    have hx' : x ≤ 0 := hx
    simp only [abs_of_nonpos hx', mul_neg, neg_neg]
  have h := h2.union h1
  rwa [Iic_union_Ioi, integrableOn_univ] at h

end GlobalTheory.IntegrableExpNegAbs
end

section

open MeasureTheory Measure
open scoped NNReal ENNReal

namespace GlobalTheory.St.HaarSplit

theorem exists_haar_map_prod_eq {A B C : Type*} [Group A] [Group B] [Group C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    [IsTopologicalGroup A] [IsTopologicalGroup B] [IsTopologicalGroup C]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [BorelSpace A] [BorelSpace B] [BorelSpace C]
    [LocallyCompactSpace A] [LocallyCompactSpace B] [LocallyCompactSpace C]
    [SecondCountableTopology A] [SecondCountableTopology B] [SecondCountableTopology C]
    (e : (A × B) ≃ₜ* C) (μA : Measure A) [μA.IsHaarMeasure] (μC : Measure C) [μC.IsHaarMeasure] :
    ∃ μB : Measure B, μB.IsHaarMeasure ∧ (μA.prod μB).map e = μC := by
  let ν : Measure B := Measure.haar
  have : ((μA.prod ν).map e).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map (μA.prod ν) e
  have h := isMulLeftInvariant_eq_smul μC ((μA.prod ν).map e)
  have hc : 0 < haarScalarFactor μC ((μA.prod ν).map e) := haarScalarFactor_pos_of_isHaarMeasure _ _
  refine ⟨haarScalarFactor μC ((μA.prod ν).map e) • ν, IsHaarMeasure.nnreal_smul _ hc.ne', ?_⟩
  conv_rhs => rw [h]
  generalize haarScalarFactor μC ((μA.prod ν).map e) = c
  have he : AEMeasurable (e : A × B → C) (μA.prod ν) :=
    e.continuous.measurable.aemeasurable
  rw [← Measure.map_smul c he]
  congr 1
  rw [ENNReal.smul_def, ENNReal.smul_def, Measure.prod_smul_right]

end GlobalTheory.St.HaarSplit
end
