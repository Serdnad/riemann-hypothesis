module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Group.LIntegral

@[expose] public section

section

open MeasureTheory

private theorem UpperTheory.Reformulated.B.FactorConjugationCancel.smul_cancel {G : Type} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [MeasurableSpace G]
    [BorelSpace G] (ν : Measure G) [ν.IsAddHaarMeasure] {a b : NNReal}
    (h : a • ν = b • ν) : a = b := by
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : G)
  have h0 : ν K ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hK0).ne'
  have h1 : ν K ≠ ⊤ := hK.measure_lt_top.ne
  have h2 : (a : ENNReal) * ν K = (b : ENNReal) * ν K := by
    have := congrArg (fun μ : Measure G => μ K) h
    simpa using this
  exact_mod_cast (ENNReal.mul_left_inj h0 h1).1 h2

private theorem UpperTheory.Reformulated.B.FactorConjugationCancel.exists_factor {G : Type} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (m : G ≃ₜ+ G) (ν : Measure G) [ν.IsAddHaarMeasure] :
    ∃ a : NNReal, Measure.map (⇑m : G → G) ν = a • ν := by
  haveI : (Measure.map (⇑m : G → G) ν).IsAddHaarMeasure := m.isAddHaarMeasure_map ν
  exact ⟨_, Measure.isAddLeftInvariant_eq_smul _ ν⟩

theorem UpperTheory.Reformulated.B.FactorConjugationCancel.map_eq_of_conj :
    ∀ {G : Type} [inst : AddCommGroup G] [inst_1 : TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [inst_5 : MeasurableSpace G]
    [BorelSpace G] (m s : G ≃ₜ+ G) (ν : MeasureTheory.Measure G) [ν.IsAddHaarMeasure] (c : NNReal),
    (∀ (x : G), (s : G → G) ((s : G → G) x) = x) →
      MeasureTheory.Measure.map (fun (x : G) ↦ (s : G → G) ((m : G → G) ((s : G → G) ((m : G → G) x)))) ν = (c * c) • ν →
        MeasureTheory.Measure.map (⇑m : G → G) ν = c • ν := by
  intro G _ _ _ _ _ _ _ m s ν _ c hs h
  obtain ⟨a, ha⟩ := UpperTheory.Reformulated.B.FactorConjugationCancel.exists_factor m ν
  obtain ⟨b, hb⟩ := UpperTheory.Reformulated.B.FactorConjugationCancel.exists_factor s ν
  have mm : Measurable (⇑m : G → G) := m.continuous.measurable
  have ms : Measurable (⇑s : G → G) := s.continuous.measurable
  have hm' : ∀ r : NNReal, Measure.map (⇑m : G → G) (r • ν) = (r * a) • ν := by
    intro r
    rw [Measure.map_smul r mm.aemeasurable, ha, smul_smul]
  have hs' : ∀ r : NNReal, Measure.map (⇑s : G → G) (r • ν) = (r * b) • ν := by
    intro r
    rw [Measure.map_smul r ms.aemeasurable, hb, smul_smul]
  have hbb : b * b = 1 := by
    apply UpperTheory.Reformulated.B.FactorConjugationCancel.smul_cancel ν
    rw [← hs', ← hb, Measure.map_map ms ms, one_smul]
    have : (⇑s ∘ ⇑s : G → G) = id := funext hs
    rw [this, Measure.map_id]
  have hcomp : (fun (x : G) ↦ (s : G → G) ((m : G → G) ((s : G → G) ((m : G → G) x))))
      = (⇑s : G → G) ∘ ((⇑m : G → G) ∘ ((⇑s : G → G) ∘ (⇑m : G → G))) := rfl
  rw [hcomp, ← Measure.map_map ms (mm.comp (ms.comp mm)), ← Measure.map_map mm (ms.comp mm),
    ← Measure.map_map ms mm, ha, hs', hm', hs'] at h
  have h2 := UpperTheory.Reformulated.B.FactorConjugationCancel.smul_cancel ν h
  have h3 : a * a = c * c := by
    rw [← h2]
    calc a * a = a * a * (b * b) := by rw [hbb, mul_one]
      _ = _ := by ring
  have h5 : (a : ℝ) * a = (c : ℝ) * c := by rw [← NNReal.coe_mul, ← NNReal.coe_mul, h3]
  have h4 : a = c := NNReal.eq ((mul_self_inj_of_nonneg a.coe_nonneg c.coe_nonneg).1 h5)
  rw [ha, h4]
end

section

open MeasureTheory in
theorem UpperTheory.Reformulated.B.Qf2.lintegral_swap_norm :
    ∀ {X T : Type} [inst : Group X]
    [inst_1 : TopologicalSpace X] [IsTopologicalGroup X] [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X]
    [inst_6 : MeasurableSpace X] [BorelSpace X] [inst_8 : Group T] [inst_9 : TopologicalSpace T] [IsTopologicalGroup T]
    [LocallyCompactSpace T] [T2Space T] [SecondCountableTopology T] [inst_14 : MeasurableSpace T] [BorelSpace T]
    (μ : MeasureTheory.Measure X) [μ.IsHaarMeasure] (ν : MeasureTheory.Measure T) [ν.IsHaarMeasure] [ν.IsInvInvariant]
    (i : T →* X),
    Continuous (⇑i : T → X) →
      ∀ {a b Ψ : X → ENNReal},
        Measurable a →
          Measurable b →
            Measurable Ψ →
              (∀ (t : T) (x : X), Ψ ((i : T → X) t * x) = Ψ x) →
                (∀ (x : X), ∫⁻ (t : T), a ((i : T → X) t * x) ∂ν = (1 : ENNReal)) →
                  (∀ (x : X), ∫⁻ (t : T), b ((i : T → X) t * x) ∂ν = (1 : ENNReal)) →
                    ∫⁻ (x : X), Ψ x * a x ∂μ = ∫⁻ (x : X), Ψ x * b x ∂μ := by
  intro X T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ ν _ _ i hi a b Ψ ha hb hΨ hinv hA hB
  have him : Measurable (i : T → X) := hi.measurable
  have m1 : Measurable (fun p : X × T => i p.2 * p.1) :=
    (him.comp measurable_snd).mul measurable_fst
  have m2 : Measurable (fun p : X × T => i p.2⁻¹ * p.1) :=
    (him.comp measurable_snd.inv).mul measurable_fst
  have f1 : Measurable (Function.uncurry fun (x : X) (t : T) => Ψ x * a x * b (i t * x)) :=
    ((hΨ.comp measurable_fst).mul (ha.comp measurable_fst)).mul (hb.comp m1)
  have f2 : Measurable (Function.uncurry fun (x : X) (t : T) => Ψ x * b x * a (i t⁻¹ * x)) :=
    ((hΨ.comp measurable_fst).mul (hb.comp measurable_fst)).mul (ha.comp m2)
  have e1 : ∀ x : X, ∫⁻ t, Ψ x * a x * b (i t * x) ∂ν = Ψ x * a x := by
    intro x
    have hm : Measurable (fun t : T => b (i t * x)) := hb.comp (him.mul_const x)
    rw [lintegral_const_mul _ hm, hB x, mul_one]
  have e2 : ∀ x : X, ∫⁻ t, Ψ x * b x * a (i t⁻¹ * x) ∂ν = Ψ x * b x := by
    intro x
    have hm : Measurable (fun t : T => a (i t⁻¹ * x)) :=
      ha.comp ((him.comp measurable_inv).mul_const x)
    rw [lintegral_const_mul _ hm, lintegral_inv_eq_self (fun t : T => a (i t * x)), hA x, mul_one]
  have e3 : ∀ t : T, ∫⁻ x, Ψ x * a x * b (i t * x) ∂μ = ∫⁻ x, Ψ x * b x * a (i t⁻¹ * x) ∂μ := by
    intro t
    rw [← lintegral_mul_left_eq_self (fun x => Ψ x * b x * a (i t⁻¹ * x)) (i t)]
    refine lintegral_congr fun x => ?_
    simp only [hinv, map_inv, inv_mul_cancel_left]
    ring
  calc ∫⁻ x, Ψ x * a x ∂μ = ∫⁻ x, ∫⁻ t, Ψ x * a x * b (i t * x) ∂ν ∂μ :=
        lintegral_congr fun x => (e1 x).symm
    _ = ∫⁻ t, ∫⁻ x, Ψ x * a x * b (i t * x) ∂μ ∂ν := lintegral_lintegral_swap f1.aemeasurable
    _ = ∫⁻ t, ∫⁻ x, Ψ x * b x * a (i t⁻¹ * x) ∂μ ∂ν := lintegral_congr e3
    _ = ∫⁻ x, ∫⁻ t, Ψ x * b x * a (i t⁻¹ * x) ∂ν ∂μ :=
        (lintegral_lintegral_swap f2.aemeasurable).symm
    _ = ∫⁻ x, Ψ x * b x ∂μ := lintegral_congr e2
end

section

theorem UpperTheory.map_involution_eq_self :
    ∀ (X : Type) [MeasurableSpace X] (μ : MeasureTheory.Measure X) [MeasureTheory.SigmaFinite μ] (ι : X → X) (c : NNReal), Measurable ι → (∀ᵐ x ∂μ, ι (ι x) = x) → μ.map ι = c • μ → μ.map ι = μ := by
  intro X _ μ _ ι c hι hinv hc
  by_cases h0 : μ = 0
  · subst h0
    simp
  have h1 : (μ.map ι).map ι = μ := by
    rw [MeasureTheory.Measure.map_map hι hι]
    have h : (ι ∘ ι) =ᵐ[μ] id := hinv
    rw [MeasureTheory.Measure.map_congr h, MeasureTheory.Measure.map_id]
  have h2 : (c * c) • μ = μ := by
    calc (c * c) • μ = c • (c • μ) := mul_smul c c μ
      _ = c • μ.map ι := by rw [hc]
      _ = (c • μ).map ι := (MeasureTheory.Measure.map_smul c hι.aemeasurable).symm
      _ = (μ.map ι).map ι := by rw [hc]
      _ = μ := h1
  obtain ⟨s, -, -, hs0, hs1⟩ :=
    MeasureTheory.Measure.exists_subset_measure_lt_top (μ := μ) (s := Set.univ) (r := 0)
      MeasurableSet.univ (MeasureTheory.Measure.measure_univ_pos.mpr h0)
  have h3 : ((c * c : NNReal) : ENNReal) * μ s = 1 * μ s := by
    have h := congrArg (fun ν : MeasureTheory.Measure X => ν s) h2
    simpa [ENNReal.smul_def] using h
  have h4 : ((c * c : NNReal) : ENNReal) = 1 :=
    (ENNReal.mul_left_inj hs0.ne' hs1.ne).mp h3
  have h5 : c * c = 1 := by exact_mod_cast h4
  have h6 : c = 1 := by
    have h : (c : ℝ) * c = 1 := by exact_mod_cast h5
    have hc0 : (0 : ℝ) ≤ c := c.2
    have h' : (c : ℝ) = 1 := by nlinarith
    exact_mod_cast h'
  rw [hc, h6, one_smul]
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.CyclotomicBarContinuous.G.{u_1, u_2} :
    (F : Type u_1) → (Ω : Type u_2) → [inst : Field F] → [inst_1 : Field Ω] → [Algebra F Ω] → Type u_2 :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] ↦ Gal(Ω/F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.CyclotomicBarContinuous.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

noncomputable def UpperTheory.Reformulated.B.CyclotomicBarContinuous.cycZ.{u_1, u_2} :
    (F : Type u_1) →
      (Ω : Type u_2) →
        [inst : Field F] →
          [inst_1 : Field Ω] →
            [inst_2 : Algebra F Ω] → (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.CyclotomicBarContinuous.G F Ω →* ℤ_[l]ˣ :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (cyclotomicCharacter Ω l).comp (MulSemiringAction.toRingAut (UpperTheory.Reformulated.B.CyclotomicBarContinuous.G F Ω) Ω)

noncomputable def UpperTheory.Reformulated.B.CyclotomicBarContinuous.cycBar :
    (E Ω : Type) →
      [inst : Field E] →
        [inst_1 : Field Ω] →
          [inst_2 : Algebra E Ω] →
            (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.CyclotomicBarContinuous.G E Ω →* (UpperTheory.Reformulated.B.CyclotomicBarContinuous.Qbar l)ˣ :=
    fun (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (Units.map
            (↑((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.CyclotomicBarContinuous.Qbar l)).comp PadicInt.Coe.ringHom) :
              ℤ_[l] →* UpperTheory.Reformulated.B.CyclotomicBarContinuous.Qbar l)).comp
        (UpperTheory.Reformulated.B.CyclotomicBarContinuous.cycZ E Ω l)

theorem UpperTheory.Reformulated.B.CyclotomicBarContinuous.cont_cycBar :
    ∀ (F Ω : Type) [inst : Field F] [NumberField F] [inst_2 : Field Ω] [inst_3 : Algebra F Ω] (l : ℕ)
      [inst_4 : Fact (Nat.Prime l)],
      Continuous (⇑(UpperTheory.Reformulated.B.CyclotomicBarContinuous.cycBar F Ω l) : UpperTheory.Reformulated.B.CyclotomicBarContinuous.G F Ω → (UpperTheory.Reformulated.B.CyclotomicBarContinuous.Qbar l)ˣ) := by
  intro F Ω _ _ _ _ l _
  have hZ : Continuous (UpperTheory.Reformulated.B.CyclotomicBarContinuous.cycZ F Ω l) := cyclotomicCharacter.continuous l F Ω
  have hι : Continuous
      (↑((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.CyclotomicBarContinuous.Qbar l)).comp PadicInt.Coe.ringHom) :
        ℤ_[l] →* UpperTheory.Reformulated.B.CyclotomicBarContinuous.Qbar l) :=
    (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp continuous_subtype_val
  exact (Units.continuous_map hι).comp hZ
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.G.{u_1, u_2} :
    (F : Type u_1) → (Ω : Type u_2) → [inst : Field F] → [inst_1 : Field Ω] → [Algebra F Ω] → Type u_2 :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] ↦ Gal(Ω/F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.cycZ.{u_1, u_2} :
    (F : Type u_1) →
      (Ω : Type u_2) →
        [inst : Field F] →
          [inst_1 : Field Ω] →
            [inst_2 : Algebra F Ω] → (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.G F Ω →* ℤ_[l]ˣ :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (cyclotomicCharacter Ω l).comp (MulSemiringAction.toRingAut (UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.G F Ω) Ω)

noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.cycBar :
    (E Ω : Type) →
      [inst : Field E] →
        [inst_1 : Field Ω] →
          [inst_2 : Algebra E Ω] →
            (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.G E Ω →* (UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.Qbar l)ˣ :=
    fun (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (Units.map
            (↑((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.Qbar l)).comp PadicInt.Coe.ringHom) :
              ℤ_[l] →* UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.Qbar l)).comp
        (UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.cycZ E Ω l)

theorem UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.cont_cyc :
    ∀ (F Ω : Type) [inst : Field F] [NumberField F] [inst_2 : Field Ω] [inst_3 : Algebra F Ω] (l : ℕ)
      [inst_4 : Fact (Nat.Prime l)],
      Continuous (⇑(UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.cycBar F Ω l) : UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.G F Ω → (UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.Qbar l)ˣ) := by
  intro F Ω _ _ _ _ l _
  have h1 : Continuous (UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.cycZ F Ω l) := cyclotomicCharacter.continuous l F Ω
  have h2 : Continuous (fun x : ℤ_[l] ↦ algebraMap ℚ_[l] (PadicAlgCl l) (x : ℚ_[l])) :=
    (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp continuous_subtype_val
  exact (Continuous.units_map _ h2).comp h1
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.G.{u_1, u_2} :
    (F : Type u_1) → (Ω : Type u_2) → [inst : Field F] → [inst_1 : Field Ω] → [Algebra F Ω] → Type u_2 :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] ↦ Gal(Ω/F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

noncomputable def UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.cycZ.{u_1, u_2} :
    (F : Type u_1) →
      (Ω : Type u_2) →
        [inst : Field F] →
          [inst_1 : Field Ω] →
            [inst_2 : Algebra F Ω] → (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.G F Ω →* ℤ_[l]ˣ :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (cyclotomicCharacter Ω l).comp (MulSemiringAction.toRingAut (UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.G F Ω) Ω)

noncomputable def UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.cycBar :
    (E Ω : Type) →
      [inst : Field E] →
        [inst_1 : Field Ω] →
          [inst_2 : Algebra E Ω] →
            (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.G E Ω →* (UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.Qbar l)ˣ :=
    fun (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (Units.map
            (↑((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.Qbar l)).comp PadicInt.Coe.ringHom) :
              ℤ_[l] →* UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.Qbar l)).comp
        (UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.cycZ E Ω l)

theorem UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.cyc_continuous :
    ∀ (F Ω : Type) [inst : Field F] [NumberField F] [inst_2 : Field Ω] [inst_3 : Algebra F Ω] (l : ℕ)
      [inst_4 : Fact (Nat.Prime l)],
      Continuous (⇑(UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.cycBar F Ω l) : UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.G F Ω → (UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.Qbar l)ˣ) := by
  intro F Ω _ _ _ _ l _
  have h1 : Continuous (UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.cycZ F Ω l) := cyclotomicCharacter.continuous l F Ω
  have h2 : Continuous ((algebraMap ℚ_[l] (UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.Qbar l)).comp PadicInt.Coe.ringHom) :=
    (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp continuous_subtype_val
  exact (Continuous.units_map _ h2).comp h1
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.G.{u_1, u_2} :
    (F : Type u_1) → (Ω : Type u_2) → [inst : Field F] → [inst_1 : Field Ω] → [Algebra F Ω] → Type u_2 :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] ↦ Gal(Ω/F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.cycZ.{u_1, u_2} :
    (F : Type u_1) →
      (Ω : Type u_2) →
        [inst : Field F] →
          [inst_1 : Field Ω] →
            [inst_2 : Algebra F Ω] → (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.G F Ω →* ℤ_[l]ˣ :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (cyclotomicCharacter Ω l).comp (MulSemiringAction.toRingAut (UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.G F Ω) Ω)

noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.cycBar :
    (E Ω : Type) →
      [inst : Field E] →
        [inst_1 : Field Ω] →
          [inst_2 : Algebra E Ω] →
            (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.G E Ω →* (UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.Qbar l)ˣ :=
    fun (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (Units.map
            (↑((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.Qbar l)).comp PadicInt.Coe.ringHom) :
              ℤ_[l] →* UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.Qbar l)).comp
        (UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.cycZ E Ω l)

theorem UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.cyc_cont :
    ∀ {E Ω : Type} [inst : Field E] [NumberField E] [inst_2 : Field Ω] [inst_3 : Algebra E Ω] {l : ℕ}
      [inst_4 : Fact (Nat.Prime l)],
      Continuous (⇑(UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.cycBar E Ω l) : UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.G E Ω → (UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.Qbar l)ˣ) := by
  intro E Ω _ _ _ _ l _
  have h1 : Continuous (UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.cycZ E Ω l) := cyclotomicCharacter.continuous l E Ω
  have h2 : Continuous ((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.Qbar l)).comp
      (PadicInt.Coe.ringHom : ℤ_[l] →+* ℚ_[l])) :=
    (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp continuous_subtype_val
  exact (Continuous.units_map _ h2).comp h1
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.G.{u_1, u_2} :
    (F : Type u_1) → (Ω : Type u_2) → [inst : Field F] → [inst_1 : Field Ω] → [Algebra F Ω] → Type u_2 :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] ↦ Gal(Ω/F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

noncomputable def UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.cycZ.{u_1, u_2} :
    (F : Type u_1) →
      (Ω : Type u_2) →
        [inst : Field F] →
          [inst_1 : Field Ω] →
            [inst_2 : Algebra F Ω] → (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.G F Ω →* ℤ_[l]ˣ :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (cyclotomicCharacter Ω l).comp (MulSemiringAction.toRingAut (UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.G F Ω) Ω)

noncomputable def UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.cycBar :
    (E Ω : Type) →
      [inst : Field E] →
        [inst_1 : Field Ω] →
          [inst_2 : Algebra E Ω] →
            (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.G E Ω →* (UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.Qbar l)ˣ :=
    fun (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (Units.map
            (↑((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.Qbar l)).comp PadicInt.Coe.ringHom) :
              ℤ_[l] →* UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.Qbar l)).comp
        (UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.cycZ E Ω l)

theorem UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.cyc_cont :
    ∀ (F Ω : Type) [inst : Field F] [NumberField F] [inst_2 : Field Ω] [inst_3 : Algebra F Ω] (l : ℕ)
      [inst_4 : Fact (Nat.Prime l)],
      Continuous (⇑(UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.cycBar F Ω l) : UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.G F Ω → (UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.Qbar l)ˣ) := by
  intro F Ω _ _ _ _ l _
  have h1 : Continuous (UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.cycZ F Ω l) := cyclotomicCharacter.continuous l F Ω
  have h2 : Continuous
      (((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.Qbar l)).comp PadicInt.Coe.ringHom :
        ℤ_[l] →* UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.Qbar l) : ℤ_[l] → UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.Qbar l) :=
    (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp continuous_subtype_val
  exact (Continuous.units_map _ h2).comp h1
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.G.{u_1, u_2} :
    (F : Type u_1) → (Ω : Type u_2) → [inst : Field F] → [inst_1 : Field Ω] → [Algebra F Ω] → Type u_2 :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] ↦ Gal(Ω/F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.cycZ.{u_1, u_2} :
    (F : Type u_1) →
      (Ω : Type u_2) →
        [inst : Field F] →
          [inst_1 : Field Ω] →
            [inst_2 : Algebra F Ω] → (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.G F Ω →* ℤ_[l]ˣ :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (cyclotomicCharacter Ω l).comp (MulSemiringAction.toRingAut (UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.G F Ω) Ω)

noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.cycBar :
    (E Ω : Type) →
      [inst : Field E] →
        [inst_1 : Field Ω] →
          [inst_2 : Algebra E Ω] →
            (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.G E Ω →* (UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.Qbar l)ˣ :=
    fun (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (Units.map
            (↑((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.Qbar l)).comp PadicInt.Coe.ringHom) :
              ℤ_[l] →* UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.Qbar l)).comp
        (UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.cycZ E Ω l)

theorem UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.cyc_cont :
    ∀ (F Ω : Type) [inst : Field F] [NumberField F] [inst_2 : Field Ω] [inst_3 : Algebra F Ω] (l : ℕ)
      [inst_4 : Fact (Nat.Prime l)],
      Continuous (⇑(UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.cycBar F Ω l) : UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.G F Ω → (UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.Qbar l)ˣ) := by
  intro F Ω _ _ _ _ l _
  have h1 : Continuous (UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.cycZ F Ω l) := cyclotomicCharacter.continuous l F Ω
  have h2 : Continuous (algebraMap ℚ_[l] (PadicAlgCl l)) :=
    (algebraMap_isometry ℚ_[l] (PadicAlgCl l)).continuous
  have h3 : Continuous
      (↑((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.Qbar l)).comp PadicInt.Coe.ringHom) :
        ℤ_[l] →* UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.Qbar l) :=
    h2.comp continuous_subtype_val
  exact (Continuous.units_map _ h3).comp h1
end

section

theorem UpperTheory.Reformulated.B.DYlb5.main :
    ∀ {k : Type} [inst : Field k] [inst_1 : ValuativeRel k] [inst_2 : TopologicalSpace k] [IsNonarchimedeanLocalField k]
      {n : ℕ} (f : Module.Dual k (Matrix (Fin n) (Fin n) k)), Continuous (⇑f : Matrix (Fin n) (Fin n) k → k) := by
  intro k _ _ _ _ n f
  haveI : IsTopologicalRing k := inferInstance
  have key : ∀ M : Matrix (Fin n) (Fin n) k,
      f M = ∑ i, ∑ j, M i j * f (Matrix.single i j 1) := by
    intro M
    conv_lhs => rw [Matrix.matrix_eq_sum_single M]

    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have : Matrix.single i j (M i j) = (M i j) • Matrix.single i j (1 : k) := by
      simp [Matrix.smul_single]
    rw [this, map_smul, smul_eq_mul]
  have : (⇑f : Matrix (Fin n) (Fin n) k → k) =
      fun M => ∑ i, ∑ j, M i j * f (Matrix.single i j 1) := funext key
  rw [this]
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (continuous_id.matrix_elem i j).mul continuous_const
end
