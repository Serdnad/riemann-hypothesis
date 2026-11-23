module

public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Order.Fin.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Topology.Algebra.Group.Defs
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Topology.Compactness.Compact

@[expose] public section

section

open ValuativeRel Filter Topology Matrix

namespace GlobalTheory.CompanionTheory.CongruenceBasis

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_pow_succ_lt {a γ : ValueGroupWithZero k} (ha0 : a ≠ 0) (ha : a < 1) (hγ : γ ≠ 0) :
    ∃ m : ℕ, a ^ (m + 1) < γ := by
  haveI : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.1 inferInstance
  have h1 : 1 < a⁻¹ := (one_lt_inv₀ (zero_lt_iff.2 ha0)).2 ha
  obtain ⟨n, hn⟩ := MulArchimedean.arch γ⁻¹ h1
  refine ⟨n, ?_⟩
  have h2 : a ^ n ≤ γ := by
    rw [inv_pow] at hn
    exact (inv_le_inv₀ (zero_lt_iff.2 hγ) (zero_lt_iff.2 (pow_ne_zero n ha0))).1 hn
  exact lt_of_lt_of_le (pow_lt_pow_right_of_lt_one₀ (zero_lt_iff.2 ha0) ha n.lt_succ_self) h2

theorem inv_mem_of_mem {N : ℕ} {t : ValueGroupWithZero k} (ht : t < 1) (g : GL (Fin N) k)
    (hg : ∀ i j, valuation k ((g : Matrix (Fin N) (Fin N) k) i j -
      (1 : Matrix (Fin N) (Fin N) k) i j) ≤ t) (i j : Fin N) :
    valuation k (((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j -
      (1 : Matrix (Fin N) (Fin N) k) i j) ≤ t := by
  set A : Matrix (Fin N) (Fin N) k := (g : Matrix (Fin N) (Fin N) k) - 1 with hA
  set B : Matrix (Fin N) (Fin N) k := ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) - 1 with hB
  have hAle : ∀ i j, valuation k (A i j) ≤ t := fun i j => by simpa [hA] using hg i j
  have hrel : B = -A - A * B := by
    have hgh : (g : Matrix (Fin N) (Fin N) k) * ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hg' : (g : Matrix (Fin N) (Fin N) k) = A + 1 := by simp [hA]
    have hh' : ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = B + 1 := by simp [hB]
    rw [hg', hh'] at hgh
    have : (A + 1) * (B + 1) = A * B + A + B + 1 := by noncomm_ring
    rw [this] at hgh
    have h3 : A * B + A + B = 0 := by simpa using hgh
    rw [eq_sub_iff_add_eq, eq_neg_iff_add_eq_zero, ← h3]
    abel
  show valuation k (B i j) ≤ t
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨⟨i₀, j₀⟩, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin N × Fin N))
    (fun p => valuation k (B p.1 p.2)) ⟨(i, j), Finset.mem_univ _⟩
  set M := valuation k (B i₀ j₀) with hM
  have hMt : t < M := lt_of_lt_of_le hcon (hmax (i, j) (Finset.mem_univ _))
  have hM0 : 0 < M := lt_of_le_of_lt zero_le' hMt
  have hprod : valuation k ((A * B) i₀ j₀) ≤ t * M := by
    rw [Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [map_mul]
    exact mul_le_mul' (hAle _ _) (hmax (l, j₀) (Finset.mem_univ _))
  have htM : t * M < M := by
    simpa using mul_lt_mul_of_pos_right ht hM0
  have hent : B i₀ j₀ = -A i₀ j₀ - (A * B) i₀ j₀ := by
    conv_lhs => rw [hrel]
    simp
  have : M < M := by
    calc M = valuation k (-A i₀ j₀ - (A * B) i₀ j₀) := by rw [hM, ← hent]
      _ ≤ max (valuation k (-A i₀ j₀)) (valuation k ((A * B) i₀ j₀)) := Valuation.map_sub _ _ _
      _ < M := by
        refine max_lt ?_ (lt_of_le_of_lt hprod htM)
        rw [Valuation.map_neg]
        exact lt_of_le_of_lt (hAle _ _) hMt
  exact lt_irrefl _ this

theorem exists_congruence_subset : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : k), ϖ ≠ 0 →
    ValuativeRel.valuation k (ϖ) < 1 →
    (∀ x : k, ValuativeRel.valuation k (x) < 1 →
      ValuativeRel.valuation k (x) ≤ ValuativeRel.valuation k (ϖ)) →
    ∀ U : Set (GL (Fin N) k), U ∈ nhds (1 : GL (Fin N) k) →
    ∃ m : ℕ, 1 ≤ m ∧ {g : GL (Fin N) k | ∀ i j,
      ValuativeRel.valuation k ((g : Matrix (Fin N) (Fin N) k) i j -
        (1 : Matrix (Fin N) (Fin N) k) i j) ≤ ValuativeRel.valuation k (ϖ ^ m)} ⊆ U := by
  intro k _ _ _ _ N ϖ hϖ0 hϖ1 _ U hU
  set a := valuation k ϖ with ha
  have ha0 : a ≠ 0 := (Valuation.ne_zero_iff _).2 hϖ0
  let K : ℕ → Set (GL (Fin N) k) := fun m => {g | ∀ i j,
    valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ a ^ (m + 1)}
  have hanti : Antitone K := fun m n hmn g hg i j =>
    (hg i j).trans (pow_le_pow_of_le_one zero_le' hϖ1.le (by omega))
  have hbasis : (⨅ m, 𝓟 (K m)).HasBasis (fun _ => True) K :=
    hasBasis_iInf_principal hanti.directed_ge
  have hent : ∀ (i j : Fin N) (c : GL (Fin N) k → k), (∀ m, ∀ g ∈ K m, valuation k (c g - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ a ^ (m + 1)) →
      Tendsto c (⨅ m, 𝓟 (K m)) (𝓝 ((1 : Matrix (Fin N) (Fin N) k) i j)) := by
    intro i j c hc
    rw [(IsValuativeTopology.hasBasis_nhds' _).tendsto_right_iff]
    intro γ hγ
    obtain ⟨m, hm⟩ := exists_pow_succ_lt ha0 hϖ1 hγ
    exact hbasis.eventually_iff.2 ⟨m, trivial, fun g hg => lt_of_le_of_lt (hc m g hg) hm⟩
  have hlim : Tendsto (id : GL (Fin N) k → GL (Fin N) k) (⨅ m, 𝓟 (K m)) (𝓝 1) := by
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    refine Tendsto.prodMk_nhds ?_ ?_
    · refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
      exact hent i j _ fun m g hg => hg i j
    · refine (MulOpposite.continuous_op.tendsto _).comp ?_
      refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
      exact hent i j (fun g => ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j) fun m g hg =>
        inv_mem_of_mem (pow_lt_one₀ zero_le' hϖ1 (by omega)) g hg i j
  obtain ⟨m, -, hm⟩ := hbasis.mem_iff.1 (hlim hU)
  refine ⟨m + 1, by omega, fun g hg => hm fun i j => ?_⟩
  simpa [ha, map_pow] using hg i j

end GlobalTheory.CompanionTheory.CongruenceBasis
end

section

open Matrix
open scoped Topology

namespace GlobalTheory.CompanionTheory.OrbitSection

section Shear

variable {k : Type} [Field k] {n : ℕ}

noncomputable def shear (j : Fin n) (c : k) (ζ ξ : Fin n → k) : Matrix (Fin n) (Fin n) k :=
  1 + c • vecMulVec (Pi.single j 1) (ξ - ζ)

theorem shear_mul_shear (j : Fin n) (ζ ξ : Fin n → k) (h0 : ζ j ≠ 0) (h1 : ξ j ≠ 0) :
    shear j (ζ j)⁻¹ ζ ξ * shear j (-(ξ j)⁻¹) ζ ξ = 1 := by
  have hE : vecMulVec (Pi.single j (1 : k)) (ξ - ζ) * vecMulVec (Pi.single j 1) (ξ - ζ)
      = (ξ j - ζ j) • vecMulVec (Pi.single j (1 : k)) (ξ - ζ) := by
    rw [vecMulVec_mul_vecMulVec, vecMulVec_smul]
    simp
  have hc : (ζ j)⁻¹ + -(ξ j)⁻¹ + (ζ j)⁻¹ * -(ξ j)⁻¹ * (ξ j - ζ j) = 0 := by
    field_simp
    ring
  have key : ∀ E : Matrix (Fin n) (Fin n) k, E * E = (ξ j - ζ j) • E →
      (1 + (ζ j)⁻¹ • E) * (1 + (-(ξ j)⁻¹) • E) = 1 := by
    intro E hEE
    have : (1 + (ζ j)⁻¹ • E) * (1 + (-(ξ j)⁻¹) • E)
        = 1 + ((ζ j)⁻¹ + -(ξ j)⁻¹ + (ζ j)⁻¹ * -(ξ j)⁻¹ * (ξ j - ζ j)) • E := by
      simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hEE]
      module
    rw [this, hc, zero_smul, add_zero]
  exact key _ hE

theorem vecMul_shear (j : Fin n) (ζ ξ : Fin n → k) (h0 : ζ j ≠ 0) :
    ζ ᵥ* shear j (ζ j)⁻¹ ζ ξ = ξ := by
  have : ζ ᵥ* vecMulVec (Pi.single j (1 : k)) (ξ - ζ) = (ζ j) • (ξ - ζ) := by
    rw [vecMul_vecMulVec]
    simp
  rw [shear, vecMul_add, vecMul_one, vecMul_smul, this, smul_smul, inv_mul_cancel₀ h0, one_smul]
  abel

theorem shear_self (j : Fin n) (c : k) (ζ : Fin n → k) : shear j c ζ ζ = 1 := by
  simp [shear]


open scoped Classical in
open Classical in
noncomputable def orbitSection (j : Fin n) (ζ ξ : Fin n → k) : GL (Fin n) k :=
  if h : ζ j ≠ 0 ∧ ξ j ≠ 0 then
    ⟨shear j (ζ j)⁻¹ ζ ξ, shear j (-(ξ j)⁻¹) ζ ξ, shear_mul_shear j ζ ξ h.1 h.2,
      mul_eq_one_comm.mp (shear_mul_shear j ζ ξ h.1 h.2)⟩
  else 1

theorem coe_orbitSection (j : Fin n) (ζ ξ : Fin n → k) (h0 : ζ j ≠ 0) (h1 : ξ j ≠ 0) :
    (orbitSection j ζ ξ : Matrix (Fin n) (Fin n) k) = shear j (ζ j)⁻¹ ζ ξ := by
  rw [orbitSection, dite_eq_left ⟨h0, h1⟩]

theorem coe_orbitSection_inv (j : Fin n) (ζ ξ : Fin n → k) (h0 : ζ j ≠ 0) (h1 : ξ j ≠ 0) :
    ((orbitSection j ζ ξ)⁻¹ : (Matrix (Fin n) (Fin n) k)ˣ).val = shear j (-(ξ j)⁻¹) ζ ξ := by
  rw [orbitSection, dite_eq_left ⟨h0, h1⟩]
  rfl

end Shear

section Top

variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalDivisionRing k] {n : ℕ}

theorem continuousOn_shear (j : Fin n) (ζ : Fin n → k) {N : Set (Fin n → k)} {c : (Fin n → k) → k}
    (hc : ContinuousOn c N) : ContinuousOn (fun ξ => shear j (c ξ) ζ ξ) N := by
  refine continuousOn_pi.2 fun a => continuousOn_pi.2 fun b => ?_
  simp only [shear, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, Pi.sub_apply, smul_eq_mul]
  refine continuousOn_const.add (hc.mul (continuousOn_const.mul ?_))
  exact ((continuous_apply b).sub continuous_const).continuousOn

theorem continuousOn_orbitSection (j : Fin n) (ζ : Fin n → k) (h0 : ζ j ≠ 0) :
    ContinuousOn (orbitSection j ζ) {ξ | ξ j ≠ 0} := by
  have hinv : ContinuousOn (fun ξ : Fin n → k => -(ξ j)⁻¹) {ξ | ξ j ≠ 0} :=
    (((continuous_apply j).continuousOn).inv₀ fun ξ h => h).neg
  rw [continuousOn_iff_continuous_restrict, Units.continuous_iff]
  refine ⟨(continuousOn_iff_continuous_restrict.1
      (continuousOn_shear j ζ (c := fun _ => (ζ j)⁻¹) continuousOn_const)).congr fun ξ => ?_,
    (continuousOn_iff_continuous_restrict.1 (continuousOn_shear j ζ hinv)).congr fun ξ => ?_⟩
  · exact (coe_orbitSection j ζ ξ.1 h0 ξ.2).symm
  · exact (coe_orbitSection_inv j ζ ξ.1 h0 ξ.2).symm

end Top

theorem exists_local_section : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ζ : Fin n → k), ζ ≠ 0 → ∃ N : Set (Fin n → k), IsOpen N ∧ ζ ∈ N ∧ ∃ f : (Fin n → k) → GL (Fin n) k, ContinuousOn f N ∧ f ζ = 1 ∧ ∀ ξ ∈ N, ζ ᵥ* (f ξ : Matrix (Fin n) (Fin n) k) = ξ := by
  intro k _ _ _ _ n ζ hζ
  haveI : T2Space k := by
    letI := IsTopologicalAddGroup.rightUniformSpace k
    haveI := isUniformAddGroup_of_addCommGroup (G := k)
    infer_instance
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hζ
  have hj' : ζ j ≠ 0 := hj
  refine ⟨{ξ | ξ j ≠ 0}, isOpen_ne.preimage (continuous_apply j), hj', orbitSection j ζ,
    continuousOn_orbitSection j ζ hj', ?_, fun ξ hξ => ?_⟩
  · apply Units.ext
    rw [coe_orbitSection j ζ ζ hj' hj', shear_self]
    rfl
  · rw [coe_orbitSection j ζ ξ hj' hξ, vecMul_shear j ζ ξ hj']

end GlobalTheory.CompanionTheory.OrbitSection
end

section

open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.GLMeasure

open ValuativeRel

theorem secondCountable_t2_local_field (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : SecondCountableTopology k ∧ T2Space k := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  haveI : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k
  exact ⟨secondCountable_of_proper, inferInstance⟩

theorem secondCountable_GL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) : SecondCountableTopology (GL (Fin n) k) := by
  obtain ⟨_, _⟩ := secondCountable_t2_local_field k
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) k) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → k))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) k)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact (Units.isEmbedding_embedProduct (M := Matrix (Fin n) (Fin n) k)).secondCountableTopology

end GlobalTheory.CompanionTheory.GLMeasure
end

section

namespace GlobalTheory.CompanionTheory.Segments

theorem shufcomb (l : ℕ) (hl : 3 ≤ l) (w : Fin l → ℕ) (hw : ∀ a, w a < l) (i j : Fin l)
    (hi : w i = 0) (hj : w j = l - 1)
    (h1 : ∀ a b, a < b → a ≠ i → b ≠ i → w b < w a)
    (h2 : ∀ a b, a < b → a ≠ j → b ≠ j → w b < w a) : StrictAnti w := by
  have hij : i ≠ j := by
    intro h
    rw [h] at hi
    omega
  intro a b hab
  by_cases hbi : b = i
  · by_cases haj : a = j
    · rw [hbi, haj, hi, hj]
      omega
    · exact h2 a b hab haj (by rw [hbi]; exact hij)
  · by_cases hai : a = i
    · by_cases hbj : b = j
      · exfalso
        have hij' : i < j := by
          rw [← hai, ← hbj]
          exact hab
        obtain ⟨c, hci, hcj⟩ : ∃ c : Fin l, c ≠ i ∧ c ≠ j := by
          by_contra hc
          push_neg at hc
          have key : ∀ k : ℕ, ∀ hk : k < l, k = i.val ∨ k = j.val := by
            intro k hk
            by_cases h : (⟨k, hk⟩ : Fin l) = i
            · left
              exact congrArg Fin.val h
            · right
              exact congrArg Fin.val (hc ⟨k, hk⟩ h)
          have k0 := key 0 (by omega)
          have k1 := key 1 (by omega)
          have k2 := key 2 (by omega)
          omega
        rcases lt_or_gt_of_ne hci with hc | hc
        · have h3 := h1 c j (lt_trans hc hij') hci (Ne.symm hij)
          have h4 := hw c
          omega
        · have h3 := h2 i c hc hij hcj
          omega
      · exact h2 a b hab (by rw [hai]; exact hij) hbj
    · exact h1 a b hab hai hbi

end GlobalTheory.CompanionTheory.Segments
end

section

namespace GlobalTheory.CompanionTheory.ComplReg

theorem nonZeroDivisor_of_dense_of_strict {B T : Type} [CommRing B] [CommRing T] (π : B)
    (g : B →+* T) (hH : IsHausdorff (Ideal.span {g π}) T)
    (hd : ∀ (M : ℕ) (y : T), ∃ x, y - g x ∈ Ideal.span {g π ^ M})
    (hk : ∀ (M : ℕ) (x : B), g x ∈ Ideal.span {g π ^ M} → x ∈ Ideal.span {π ^ M})
    (hπ : π ∈ nonZeroDivisors B) : g π ∈ nonZeroDivisors T := by
  have key : ∀ t : T, t * g π = 0 → ∀ M : ℕ, t ∈ Ideal.span {g π ^ M} := by
    intro t ht M
    obtain ⟨x, hx⟩ := hd M t
    rw [Ideal.mem_span_singleton] at hx
    obtain ⟨d, hd'⟩ := hx
    have hxπ : x * π ∈ Ideal.span {π ^ (M + 1)} := by
      apply hk (M + 1) (x * π)
      rw [Ideal.mem_span_singleton]
      exact ⟨-d, by rw [map_mul]; linear_combination ht - g π * hd'⟩
    rw [Ideal.mem_span_singleton] at hxπ
    obtain ⟨c, hc⟩ := hxπ
    have h0 : (x - π ^ M * c) * π = 0 := by
      rw [sub_mul, hc]
      ring
    have hxeq : x = π ^ M * c := sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hπ).2 _ h0)
    have hgx : g x = g π ^ M * g c := by
      rw [hxeq, map_mul, map_pow]
    rw [Ideal.mem_span_singleton]
    exact ⟨d + g c, by linear_combination hd' + hgx⟩
  have main : ∀ t : T, t * g π = 0 → t = 0 := by
    intro t ht
    refine IsHausdorff.haus hH t (fun n => ?_)
    rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
    exact key t ht n
  rw [mem_nonZeroDivisors_iff]
  exact ⟨fun t ht => main t (by rwa [mul_comm] at ht), main⟩

end GlobalTheory.CompanionTheory.ComplReg
end

section

open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.AdicApprox

theorem exists_unit_eq_of_successive_approximation :
    ∀ (O S : Type) [CommRing O] [CommRing S] [Algebra O S] (I : Ideal O) [IsAdicComplete I S] (Q : ℕ → Ideal S) (N₀ : ℕ) (Nm : S → S) (t : S) (P₁ : Sˣ), (∀ m, Q (m + 1) ≤ Q m) → (∀ k, Q (N₀ * k + 1) ≤ Ideal.map (algebraMap O S) (I ^ k)) → Ideal.map (algebraMap O S) I ≤ Q 1 → (∀ x ∈ Q 1, IsUnit (1 + x)) → (∀ (k : ℕ) (x y : S), x - y ∈ Ideal.map (algebraMap O S) (I ^ k) → Nm x - Nm y ∈ Ideal.map (algebraMap O S) (I ^ k)) → t - Nm (P₁ : S) ∈ Q 1 → (∀ m, 1 ≤ m → ∀ P : Sˣ, t - Nm (P : S) ∈ Q m → ∃ P' : Sˣ, (P' : S) - (P : S) ∈ Q m ∧ t - Nm (P' : S) ∈ Q (m + 1)) → ∃ L : Sˣ, Nm (L : S) = t := by
  intro O S _ _ _ I _ Q N₀ Nm t P₁ hQ hN hIQ hU hNm h1 hstep
  have hmono : ∀ {a b : ℕ}, a ≤ b → Q b ≤ Q a := fun h => antitone_nat_of_succ_le hQ h
  have hstep' : ∀ (n : ℕ) (P : {P : Sˣ // t - Nm (P : S) ∈ Q (n + 1)}),
      ∃ P' : {P : Sˣ // t - Nm (P : S) ∈ Q (n + 1 + 1)},
        ((P'.1 : Sˣ) : S) - ((P.1 : Sˣ) : S) ∈ Q (n + 1) := by
    intro n P
    obtain ⟨P', h, h'⟩ := hstep (n + 1) (by omega) P.1 P.2
    exact ⟨⟨P', h'⟩, h⟩
  choose nxt hnxt using hstep'
  let sq : (n : ℕ) → {P : Sˣ // t - Nm (P : S) ∈ Q (n + 1)} :=
    fun n => Nat.rec ⟨P₁, h1⟩ (fun n p => nxt n p) n
  have hsq : ∀ n, (((sq (n + 1)).1 : Sˣ) : S) - (((sq n).1 : Sˣ) : S) ∈ Q (n + 1) :=
    fun n => hnxt n (sq n)
  have hdiff : ∀ m n, m ≤ n → (((sq n).1 : Sˣ) : S) - (((sq m).1 : Sˣ) : S) ∈ Q (m + 1) := by
    intro m n h
    induction n, h using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have := (Q (m + 1)).add_mem (hmono (by omega : m + 1 ≤ n + 1) (hsq n)) ih
      simpa using this
  have hmem : ∀ {k : ℕ} {x : S}, x ∈ Ideal.map (algebraMap O S) (I ^ k) ↔
      x ∈ (I ^ k • ⊤ : Submodule O S) := by
    intro k x
    rw [Ideal.smul_top_eq_map]
    rfl
  let f : ℕ → S := fun k => (((sq (N₀ * k)).1 : Sˣ) : S)
  have hf : ∀ {m n : ℕ}, m ≤ n → f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule O S)] := by
    intro m n h
    rw [SModEq.sub_mem, ← hmem]
    have := hN m (hdiff (N₀ * m) (N₀ * n) (Nat.mul_le_mul_left _ h))
    rw [← neg_sub]
    exact Ideal.neg_mem_iff _ |>.2 this
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (IsAdicComplete.toIsPrecomplete (I := I) (M := S)) hf
  have hL' : ∀ n, f n - L ∈ Ideal.map (algebraMap O S) (I ^ n) := fun n => by
    have := hL n
    rw [SModEq.sub_mem] at this
    exact hmem.2 this
  have hNmL : Nm L = t := by
    have hz : t - Nm L = 0 := by
      apply IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := I) (M := S))
      intro n
      rw [SModEq.zero, ← hmem]
      have a1 := hNm n _ _ (hL' n)
      have a2 : t - Nm (f n) ∈ Ideal.map (algebraMap O S) (I ^ n) := hN n (sq (N₀ * n)).2
      have := Ideal.add_mem _ a2 a1
      simpa using this
    exact (sub_eq_zero.1 hz).symm
  have hLQ : L - (P₁ : S) ∈ Q 1 := by
    have b1 : f 1 - L ∈ Q 1 := by
      have := hL' 1
      rw [pow_one] at this
      exact hIQ this
    have b2 : f 1 - (P₁ : S) ∈ Q 1 := hdiff 0 (N₀ * 1) (Nat.zero_le _)
    have := (Q 1).sub_mem b2 b1
    simpa using this
  have hunit : IsUnit L := by
    have hx : ((P₁⁻¹ : Sˣ) : S) * (L - (P₁ : S)) ∈ Q 1 := (Q 1).mul_mem_left _ hLQ
    have hu := (P₁.isUnit).mul (hU _ hx)
    have he : (P₁ : S) * (1 + ((P₁⁻¹ : Sˣ) : S) * (L - (P₁ : S))) = L := by
      rw [mul_add, ← mul_assoc, Units.mul_inv]
      ring
    rwa [he] at hu
  obtain ⟨u, rfl⟩ := hunit
  exact ⟨u, hNmL⟩

end GlobalTheory.CompanionTheory.AdicApprox
end

section

namespace GlobalTheory.CompanionTheory.TopGroup

theorem finite_image_of_right_invariant_near_one :
    ∀ {Γ X : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (K : Set Γ),
      IsCompact K → ∀ Gf : Γ → X, {s : Γ | ∀ x, Gf (x * s) = Gf x} ∈ nhds (1 : Γ) →
        (Gf '' K).Finite := by
  intro Γ X _ _ _ K hK Gf hS
  have hU : ∀ k ∈ K, {y : Γ | k⁻¹ * y ∈ {s : Γ | ∀ x, Gf (x * s) = Gf x}} ∈ nhds k := by
    intro k _
    have hc : Continuous fun y : Γ => k⁻¹ * y := continuous_const.mul continuous_id
    refine hc.continuousAt.preimage_mem_nhds ?_
    show _ ∈ nhds (k⁻¹ * k)
    rw [inv_mul_cancel]
    exact hS
  obtain ⟨t, -, hcover⟩ := hK.elim_nhds_subcover _ hU
  refine (t.finite_toSet.image Gf).subset ?_
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨k, hk, hyk⟩ := Set.mem_iUnion₂.1 (hcover hy)
  refine ⟨k, hk, ?_⟩
  have h := hyk k
  rw [mul_inv_cancel_left] at h
  exact h.symm

end GlobalTheory.CompanionTheory.TopGroup
end
