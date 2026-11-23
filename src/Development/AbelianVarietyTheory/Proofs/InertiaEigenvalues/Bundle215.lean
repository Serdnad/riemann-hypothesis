module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle100
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle144
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle148
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle121
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle103
public import Mathlib.Data.Int.Interval
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle171
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle200
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle191
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle169
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle186
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle199
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle166
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle009
public import Formalism.CharacterColumnKernels.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle203
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Monotonicity.Lemmas
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle102
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Hyp

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def ccLin (A : Et F E) (e : A.L) : (A.K × A.K) →ₗ[F] A.L where
  toFun := cc A e
  map_add' p q := by simp only [cc, Prod.fst_add, Prod.snd_add, map_add (f := _)]; ring
  map_smul' c p := by
    simp only [cc, Prod.smul_fst, Prod.smul_snd, RingHom.id_apply]
    simp only [Algebra.smul_def, IsScalarTower.algebraMap_apply F A.K A.L, map_mul]
    ring

def ccEquiv [Unram F E] (A : Et F E) (e : A.L) (h1 : ∀ p, ci A e (cc A e p) = p)
    (h2 : ∀ y, cc A e (ci A e y) = y) : (A.K × A.K) ≃L[F] A.L :=
  haveI := EtMeas.finite_L A
  haveI : IsTopologicalAddGroup A.L := IsModuleTopology.topologicalAddGroup F A.L
  let l : (A.K × A.K) ≃ₗ[F] A.L := { ccLin A e with invFun := ci A e, left_inv := h1, right_inv := h2 }
  { l with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap l.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap l.symm.toLinearMap }

def tt (A : Et F E) (ν : Measure A.K) (ψ : AddChar F ℂ) (x : A.K) (Φ : A.K × A.K → ℂ) : A.K × A.K → ℂ :=
  pt A ν ψ x (fun q => pt A ν ψ x Φ (q.2, q.1))

theorem measure_eq_coords : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.Kˣ) (e : A.L), e * e = e → star e = 1 - e → ∀ (ν : Measure A.K) (μ : Measure A.L), SelfDual ν (Hyp.kx A ψ x) → SelfDual μ (A.kerL ψ x) → ∀ h : A.L → ℂ, IsTest h → ∫ y, h y ∂μ = ∫ a, ∫ b, h (Hyp.cc A e (a, b)) ∂ν ∂ν := by
  intro F E _ _ _ _ _ A ψ hψ x e he hse ν μ hν hμ h hh
  haveI : LocallyCompactSpace F := Unram.lcF E
  haveI : IsUltrametricDist F := Unram.ultraF E
  haveI := EtMeas.finite_L A
  haveI := GlobalTheory.FourKFub.secondCountableK A
  obtain ⟨_, _, _, _, hS⟩ := EtMeas.top_facts F A.L
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.K
  obtain ⟨h1, h2, -, hker, -⟩ := GlobalTheory.T.idempotentCoordinates_structure F E A e he hse
  obtain ⟨htc, htc'⟩ := GlobalTheory.T.isLocallyConstantCompactSupport_idempotentCoordinates_iff F E A e h1 h2
  have hlc := (GlobalTheory.T.isLocallyConstant_etaleTraceAddChar_hermitianKernel F E A ψ hψ).2 (x : A.K)
  haveI : ν.IsAddHaarMeasure := hν.1
  let C := ccEquiv A e h1 h2
  have hC : (C : A.K × A.K → A.L) = cc A e := rfl
  set μ₀ := Measure.map (cc A e) (ν.prod ν) with hμ₀
  haveI : μ₀.IsAddHaarMeasure := by rw [hμ₀, ← hC]; exact C.isAddHaarMeasure_map _
  have hint : ∀ g : A.L → ℂ, IsTest g → ∫ y, g y ∂μ₀ = ∫ a, ∫ b, g (cc A e (a, b)) ∂ν ∂ν := by
    intro g hg
    have e1 : ∫ y, g y ∂μ₀ = ∫ p, g (cc A e p) ∂(ν.prod ν) := C.toHomeomorph.measurableEmbedding.integral_map g
    rw [e1]
    exact integral_prod _ (((htc g hg).1.continuous).integrable_of_hasCompactSupport (htc g hg).2)
  have hsw : ∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (fun q : A.K × A.K => Φ (q.2, q.1)) := fun Φ hΦ =>
    ⟨hΦ.1.comp_continuous continuous_swap, hΦ.2.comp_homeomorph (Homeomorph.prodComm A.K A.K)⟩
  have hpt : ∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (pt A ν ψ x Φ) := fun Φ hΦ =>
    GlobalTheory.T.partialFourier_psiK_preserves_testFunctions F E A ψ hψ x ν hν.1 Φ hΦ
  have hT : ∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (tt A ν ψ x Φ) := fun Φ hΦ =>
    hpt _ (hsw _ (hpt Φ hΦ))
  have hTT : ∀ Φ : A.K × A.K → ℂ, IsTest Φ → tt A ν ψ x (tt A ν ψ x Φ) = fun p => Φ (-p.1, -p.2) := by
    intro Φ hΦ
    have i1 := GlobalTheory.T.hyperbolicPartialFourier_twice_eq_reflection F E A ψ x ν hν _ (hsw _ (hpt Φ hΦ))
    have i2 := GlobalTheory.T.hyperbolicPartialFourier_twice_eq_reflection F E A ψ x ν hν Φ hΦ
    funext p
    show pt A ν ψ x (fun q => pt A ν ψ x (pt A ν ψ x (fun q' => pt A ν ψ x Φ (q'.2, q'.1))) (q.2, q.1)) p = _
    rw [i1]
    show pt A ν ψ x (pt A ν ψ x Φ) (-p.1, p.2) = _
    rw [i2]
  have hA : ∀ f : A.L → ℂ, IsTest f → ∀ p,
      fourB μ₀ (A.kerL ψ x) f (cc A e p) = tt A ν ψ x (fun q => f (cc A e q)) p := by
    intro f hf p
    have ht : IsTest (fun z => f z * A.kerL ψ x z (cc A e p)) := ⟨hf.1.mul (hlc _), hf.2.mul_right⟩
    unfold fourB
    rw [hint _ ht]
    show _ = ∫ a, (∫ b, f (cc A e (a, b)) * kx A ψ x b p.1 ∂ν) * kx A ψ x a p.2 ∂ν
    congr 1; funext a
    rw [← integral_mul_const]
    congr 1; funext b
    rw [hker]; dsimp only; ring
  have hB : ∀ f : A.L → ℂ, IsTest f → IsTest (fourB μ₀ (A.kerL ψ x) f) := by
    intro f hf
    have : fourB μ₀ (A.kerL ψ x) f = fun y => tt A ν ψ x (fun q => f (cc A e q)) (ci A e y) := by
      funext y; have := hA f hf (ci A e y); rwa [h2] at this
    rw [this]; exact htc' _ (hT _ (htc f hf))
  have hsd : SelfDual μ₀ (A.kerL ψ x) := by
    refine ⟨inferInstance, fun f hf y => ?_⟩
    rw [← h2 y, hA _ (hB f hf)]
    have : (fun q => fourB μ₀ (A.kerL ψ x) f (cc A e q)) = tt A ν ψ x (fun q => f (cc A e q)) :=
      funext (hA f hf)
    rw [this, hTT _ (htc f hf)]
    dsimp only
    congr 1
    simp only [cc, map_neg]; ring
  have heq : μ = μ₀ := MeasScale.selfDual_unique hS (A.kerL ψ x) hsd hμ
  rw [heq]; exact hint h hh

end GlobalTheory.JR.Hyp
end
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

namespace GlobalTheory.UnitLemma.Desc


open Classical in
noncomputable def badWinBox {ι : Type} (S I : Finset ι) (L k : ℕ) (i₀ i : ι) : Finset ℤ :=
  if i ∈ S then (if i ∈ I then Finset.Icc (2 * (k : ℤ) - L) (2 * k + L) else Finset.Icc (-(L : ℤ)) L)
  else if i = i₀ then Finset.Ico (-(L : ℤ)) L ∪ Finset.Ioc (2 * (k : ℤ) - L) (2 * k + L)
  else Finset.Icc (-(L : ℤ)) (2 * k + L)

open Classical in
theorem card_badWinBox_le {ι : Type} (S I : Finset ι) (L k : ℕ) (i₀ i : ι) :
    (badWinBox S I L k i₀ i).card ≤
      2 * (2 * L + 1) * (if i ∈ insert i₀ S then 1 else k + 1) := by
  unfold badWinBox
  by_cases hS : i ∈ S
  · have : i ∈ insert i₀ S := Finset.mem_insert_of_mem hS
    rw [if_pos hS, if_pos this]
    split_ifs <;> simp [Int.card_Icc] <;> omega
  · rw [if_neg hS]
    by_cases h0 : i = i₀
    · subst h0
      rw [if_pos rfl, if_pos (Finset.mem_insert_self _ _)]
      refine (Finset.card_union_le _ _).trans ?_
      simp [Int.card_Ico, Int.card_Ioc]; omega
    · rw [if_neg h0, if_neg (by simp [h0, hS])]
      simp [Int.card_Icc]
      nlinarith

open Classical in
theorem card_piFinset_badWinBox_le {ι : Type} [Fintype ι] (S I : Finset ι) (L k : ℕ) (i₀ : ι) (h₀ : i₀ ∉ S) :
    (Fintype.piFinset (badWinBox S I L k i₀)).card ≤
      (2 * (2 * L + 1)) ^ Fintype.card ι * (k + 1) ^ (Fintype.card ι - S.card - 1) := by
  rw [Fintype.card_piFinset]
  refine (Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _) fun i _ => card_badWinBox_le S I L k i₀ i).trans ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.prod_ite, Finset.prod_const_one,
    one_mul, Finset.prod_const]
  have : (Finset.univ.filter fun i => i ∉ insert i₀ S).card = Fintype.card ι - S.card - 1 := by
    have h : (Finset.univ.filter fun i => i ∉ insert i₀ S) = (insert i₀ S)ᶜ := by ext; simp
    rw [h, Finset.card_compl, Finset.card_insert_of_notMem h₀]; omega
  rw [this]

end GlobalTheory.UnitLemma.Desc

namespace GlobalTheory.UnitLemma.Desc

theorem tendsto_badWindow_div_rho : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e π : ι → B.A) (S : Finset ι) (a : K.O), B.P.Separable → K.Small a → IsFrame B e π S → ∀ (I I' : Finset ι), (∀ i ∈ S, i ∈ I ∨ i ∈ I') → ∀ (N L : ℕ) (D : ℚ) (f : ℕ → Submodule K.O B.A → ℚ), (∀ M ∈ B.Lin, ∃ p, Pos B a e N M p) → (∀ k M, |f k M| ≤ D) → (∀ k, L ≤ k → ∀ M ∈ B.Lin, ∀ p, Pos B a e N M p → f k M ≠ 0 → Win I I' L k p ∧ ¬ Mid S L k p) → Tendsto (fun k : ℕ => ((∑ᶠ M ∈ B.Lin, f k M : ℚ) : ℝ) / (B.rho (algebraMap K.O B.A a ^ k) : ℝ)) atTop (𝓝 0) := by
  intro K B ι _ e π S a hsep ha hfr I I' hI N L D f hpos hD hsupp
  classical
  obtain ⟨C, hC⟩ := GlobalTheory.T.card_lattices_idempotent_position_bounded K B ι e π S a hsep ha hfr N
  have hrho := GlobalTheory.T.rho_pow_lower_bound_swappedPairs K B ι e π S a hsep ha hfr
  have hD0 : 0 ≤ D := le_trans (abs_nonneg _) (hD 0 ⊥)
  set n := Fintype.card ι
  set m := n - S.card
  set A : ℕ := 2 * (2 * L + 1)
  have key : ∀ k, L ≤ k → |∑ᶠ M ∈ B.Lin, f k M| ≤ D * ((m * A ^ n * (k + 1) ^ (m - 1) * C : ℕ) : ℚ) := by
    intro k hk
    let W : Finset (ι → ℤ) :=
      (Finset.univ.filter (· ∉ S)).biUnion fun i₀ => Fintype.piFinset (badWinBox S I L k i₀)
    have hWcard : W.card ≤ m * A ^ n * (k + 1) ^ (m - 1) := by
      refine Finset.card_biUnion_le.trans ?_
      have h1 : ∀ i₀ ∈ Finset.univ.filter (· ∉ S),
          (Fintype.piFinset (badWinBox S I L k i₀)).card ≤ A ^ n * (k + 1) ^ (m - 1) := by
        intro i₀ hi₀
        exact card_piFinset_badWinBox_le S I L k i₀ (Finset.mem_filter.1 hi₀).2
      refine (Finset.sum_le_sum h1).trans ?_
      rw [Finset.sum_const, smul_eq_mul]
      have h2 : (Finset.univ.filter (· ∉ S)).card = m := by
        have h : (Finset.univ.filter (· ∉ S)) = Sᶜ := by ext; simp
        rw [h, Finset.card_compl]
      rw [h2, mul_assoc]
    have hmem : ∀ M ∈ B.Lin, f k M ≠ 0 → ∃ p ∈ W, Pos B a e N M p := by
      intro M hM hf
      obtain ⟨p, hp⟩ := hpos M hM
      obtain ⟨hw, hmid⟩ := hsupp k hk M hM p hp hf
      refine ⟨p, ?_, hp⟩
      simp only [W, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
      unfold Mid at hmid
      push_neg at hmid
      obtain ⟨i₀, hi₀, h₀⟩ := hmid
      refine ⟨i₀, hi₀, fun i => ?_⟩
      obtain ⟨h1, h2, h3, h4⟩ := hw i
      unfold badWinBox
      by_cases hS : i ∈ S
      · rw [if_pos hS]
        by_cases hiI : i ∈ I
        · rw [if_pos hiI]; simp only [Finset.mem_Icc]; exact ⟨h3 hiI, h2⟩
        · rw [if_neg hiI]
          have := (hI i hS).resolve_left hiI
          simp only [Finset.mem_Icc]; exact ⟨h1, h4 this⟩
      · rw [if_neg hS]
        by_cases h0 : i = i₀
        · subst h0
          rw [if_pos rfl]
          simp only [Finset.mem_union, Finset.mem_Ico, Finset.mem_Ioc]
          by_cases hl : (L : ℤ) ≤ p i
          · exact Or.inr ⟨h₀ hl, h2⟩
          · exact Or.inl ⟨h1, lt_of_not_ge hl⟩
        · rw [if_neg h0]; simp only [Finset.mem_Icc]; exact ⟨h1, h2⟩
    let T : Finset (Submodule K.O B.A) := W.biUnion fun p => (hC p).1.toFinset
    have hTcard : T.card ≤ W.card * C := by
      refine Finset.card_biUnion_le.trans ?_
      refine (Finset.sum_le_sum fun p _ => ?_).trans (by rw [Finset.sum_const, smul_eq_mul])
      rw [← Set.ncard_eq_toFinset_card _ (hC p).1]
      exact (hC p).2
    have hfs : ∑ᶠ M ∈ B.Lin, f k M = ∑ M ∈ T.filter (· ∈ B.Lin), f k M := by
      apply finsum_mem_eq_sum_of_inter_support_eq
      ext M
      simp only [Set.mem_inter_iff, Function.mem_support, Finset.coe_filter, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hM, hf⟩
        refine ⟨⟨?_, hM⟩, hf⟩
        obtain ⟨p, hpW, hp⟩ := hmem M hM hf
        simp only [T, Finset.mem_biUnion, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
        exact ⟨p, hpW, hp⟩
      · rintro ⟨⟨_, hM⟩, hf⟩
        exact ⟨hM, hf⟩
    rw [hfs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun M _ => hD k M).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ hD0
    have : (T.filter (· ∈ B.Lin)).card ≤ m * A ^ n * (k + 1) ^ (m - 1) * C :=
      (Finset.card_filter_le _ _).trans (hTcard.trans (Nat.mul_le_mul_right _ hWcard))
    exact_mod_cast this
  have hm : ∀ k : ℕ, m * (k + 1) ^ (m - 1) * (k + 1) = m * (k + 1) ^ m := by
    intro k
    rcases Nat.eq_zero_or_pos m with h | h
    · simp [h]
    · rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel h]
  set c : ℝ := (D : ℝ) * (A : ℝ) ^ n * (m : ℝ) * (C : ℝ)
  have hlim : Tendsto (fun k : ℕ => c * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul c
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop L] with k hk
  have hr : ((k + 1 : ℕ) : ℝ) ^ m ≤ (B.rho (algebraMap K.O B.A a ^ k) : ℝ) := by exact_mod_cast hrho k
  have hpos' : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) ^ m := by positivity
  have hk' := key k hk
  have hk'' : |((∑ᶠ M ∈ B.Lin, f k M : ℚ) : ℝ)| ≤ (D : ℝ) * ((m * A ^ n * (k + 1) ^ (m - 1) * C : ℕ) : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).2 hk'
    push_cast at this ⊢
    simpa [Rat.cast_abs] using this
  rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
  rw [div_le_iff₀ (lt_of_lt_of_le hpos' hr)]
  calc |((∑ᶠ M ∈ B.Lin, f k M : ℚ) : ℝ)|
      ≤ (D : ℝ) * ((m * A ^ n * (k + 1) ^ (m - 1) * C : ℕ) : ℝ) := hk''
    _ = c * (1 / ((k : ℝ) + 1)) * ((k + 1 : ℕ) : ℝ) ^ m := by
        have h := congrArg (fun x : ℕ => (x : ℝ)) (hm k)
        push_cast at h ⊢
        field_simp
        simp only [c]
        linear_combination (D : ℝ) * (A : ℝ) ^ n * (C : ℝ) * h
    _ ≤ c * (1 / ((k : ℝ) + 1)) * (B.rho (algebraMap K.O B.A a ^ k) : ℝ) := by
        refine mul_le_mul_of_nonneg_left hr ?_
        simp only [c]; positivity

end GlobalTheory.UnitLemma.Desc
end

section

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilQuad.GaussProd

open GlobalTheory.JR.WeilQuad.FourierTest

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem NL_add [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) (t u : A.L) :
    A.NL (t + u) = A.NL t + A.NL u + Algebra.trace A.K A.L (star t * u) := by
  apply algMap_inj A hK hL
  rw [map_add (f := _), map_add (f := _), (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).1, (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).1, (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).1,
    (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.1, star_add, star_mul, star_star]
  ring

theorem two_trace_NL [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) (x : A.K) (y : A.L) :
    2 * Algebra.trace F A.K (x * A.NL y) = beta A x y y := by
  rw [beta_apply]
  have h : Algebra.trace A.K A.L (star y * y) = A.NL y + A.NL y := by
    apply algMap_inj A hK hL
    rw [(GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.1, map_add (f := _), (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).1, star_mul, star_star]
    ring
  rw [h, mul_add, map_add (f := _), two_mul]

theorem trace_NL_add [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) (x : A.K) (t u : A.L) :
    Algebra.trace F A.K (x * A.NL (t + u)) =
      Algebra.trace F A.K (x * A.NL t) + Algebra.trace F A.K (x * A.NL u) + beta A x t u := by
  rw [NL_add A hK hL, mul_add, mul_add, map_add (f := _), map_add (f := _), beta_apply]

theorem continuous_trace_NL [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) (x : A.K) :
    Continuous fun y : A.L => Algebra.trace F A.K (x * A.NL y) := by
  haveI := finite_F_L A
  haveI : CharZero F := Unram.charZero (F := F) (E := E)
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hβc : Continuous (fun p : A.L × A.L => beta A x p.1 p.2) :=
    IsModuleTopology.continuous_bilinear_of_finite_left (beta A x)
  have hdiag : Continuous (fun y : A.L => (y, y)) := continuous_id.prodMk continuous_id
  have hcomp : Continuous ((fun p : A.L × A.L => beta A x p.1 p.2) ∘ (fun y : A.L => (y, y))) :=
    hβc.comp hdiag
  have hd : Continuous (fun y : A.L => (2 : F)⁻¹ * beta A x y y) := continuous_const.mul hcomp
  refine hd.congr (fun y => ?_)
  show (2 : F)⁻¹ * beta A x y y = Algebra.trace F A.K (x * A.NL y)
  rw [← two_trace_NL A hK hL x y, ← mul_assoc, inv_mul_cancel₀ h2, one_mul]

end GlobalTheory.JR.WeilQuad.GaussProd


open GlobalTheory.JR.WeilQuad.FourierTest GlobalTheory.JR.WeilQuad.GaussProd in
theorem GlobalTheory.JR.WeilQuad.gaussInt_one_mul_neg_one : ∀ (F E : Type) [NontriviallyNormedField F]
    [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ)
    (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ Λ : AddSubgroup A.L, IsOpen (Λ : Set A.L) →
    IsCompact (Λ : Set A.L) → {y : A.L | ∀ w ∈ (Λ : Set A.L), A.kerL ψ x w y = 1} ⊆ Λ →
    (∀ y ∈ {y : A.L | ∀ w ∈ (Λ : Set A.L), A.kerL ψ x w y = 1}, A.psiK ψ ((x : A.K) * A.NL y) = 1) →
    gaussInt A ψ x μ 1 Λ * gaussInt A ψ x μ (-1) Λ = 1 := by
  intro F E _ _ _ _ _ A ψ x μ ω h Λ hΛo hΛc hPS hQ
  obtain ⟨hK, hL, hψ, hsd, -⟩ := h
  haveI := hsd.1
  haveI := finite_F_L A
  obtain ⟨hLC, hSC, hT2, hTG⟩ := GlobalTheory.JR.SelfDualLat.topo F E A.L
  haveI := hLC; haveI := hSC; haveI := hT2; haveI := hTG
  have hψ' := (GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ
  have hψc : Continuous (fun t : F => ψ t) := cont_psi hψ
  set β := beta A (x : A.K) with hβdef
  have hβc : Continuous (fun p : A.L × A.L => β p.1 p.2) :=
    IsModuleTopology.continuous_bilinear_of_finite_left β
  set q : A.L → F := fun y => Algebra.trace F A.K ((x : A.K) * A.NL y) with hqdef
  have hqc : Continuous q := continuous_trace_NL A hK hL (x : A.K)
  have hqa : ∀ t u, q (t + u) = q t + q u + β t u := fun t u => trace_NL_add A hK hL (x : A.K) t u
  set S : Set A.L := (Λ : Set A.L) with hSdef
  set P : Set A.L := {y : A.L | ∀ w ∈ S, ψ (β w y) = 1} with hPdef
  have hSm : MeasurableSet S := hΛo.measurableSet
  have hPc : IsClosed P := by
    have : P = ⋂ w ∈ S, (fun y => ψ (β w y)) ⁻¹' {1} := by ext y; simp [hPdef]
    rw [this]
    exact isClosed_biInter fun w _ =>
      isClosed_singleton.preimage (hψc.comp (hβc.comp (continuous_const.prodMk continuous_id)))
  have hPm : MeasurableSet P := hPc.measurableSet
  have hI := GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt F E ψ hψ A.L β (beta_isSymm A hK hL (x : A.K)) (beta_nondeg A hK hL x) μ hsd.1
  have hvol : μ S * μ P = 1 := ((hI.1 Λ hΛo hΛc).1).1 hsd
  have horth : ∀ u, ∫ t in S, ψ (β t u) ∂μ = P.indicator (fun _ => ((μ S).toReal : ℂ)) u :=
    (hI.1 Λ hΛo hΛc).2
  have hPS' : P ⊆ S := hPS
  have hQ' : ∀ y ∈ P, ψ (q y) = 1 := hQ
  have hG1 : gaussInt A ψ x μ 1 Λ = ∫ y in S, ψ (q y) ∂μ := by
    unfold gaussInt
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show ψ (Algebra.trace F A.K (1 * (x : A.K) * A.NL y)) = ψ (Algebra.trace F A.K ((x : A.K) * A.NL y))
    rw [one_mul]
  have hG2 : gaussInt A ψ x μ (-1) Λ = ∫ y in S, ψ (-q y) ∂μ := by
    unfold gaussInt
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show ψ (Algebra.trace F A.K (-1 * (x : A.K) * A.NL y)) = ψ (-Algebra.trace F A.K ((x : A.K) * A.NL y))
    rw [neg_one_mul, neg_mul, map_neg]
  have hne : ∀ a : F, ψ (-a) * ψ a = 1 := by
    intro a; rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have htr : ∀ t ∈ S, (∫ u in S, ψ (q u) ∂μ) = ψ (q t) * ∫ u in S, ψ (q u) * ψ (β t u) ∂μ := by
    intro t ht
    rw [← integral_indicator hSm, ← integral_add_left_eq_self (S.indicator fun u => ψ (q u)) t,
      ← integral_const_mul, ← integral_indicator hSm]
    congr 1; ext u
    by_cases hu : u ∈ S
    · have htu : t + u ∈ S := Λ.add_mem ht hu
      rw [Set.indicator_of_mem htu, Set.indicator_of_mem hu, hqa, AddChar.map_add_eq_mul,
        AddChar.map_add_eq_mul]
      ring
    · have htu : t + u ∉ S := fun h' => hu (by
        have := Λ.sub_mem h' ht
        rwa [add_sub_cancel_left] at this)
      simp [Set.indicator_of_notMem htu, Set.indicator_of_notMem hu]
  haveI : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.2 hΛc.measure_lt_top.ne
  have hint : Integrable (Function.uncurry fun t u => ψ (q u) * ψ (β t u))
      ((μ.restrict S).prod (μ.restrict S)) := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ ?_
    · exact ((hψc.comp (hqc.comp continuous_snd)).mul (hψc.comp hβc)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun z => ?_)
      simp only [Function.uncurry, norm_mul, hψ'.2.1, mul_one, le_refl]
  rw [hG1, hG2]
  calc (∫ y in S, ψ (q y) ∂μ) * ∫ y in S, ψ (-q y) ∂μ
      = ∫ t in S, (∫ y in S, ψ (q y) ∂μ) * ψ (-q t) ∂μ := (integral_const_mul _ _).symm
    _ = ∫ t in S, ∫ u in S, ψ (q u) * ψ (β t u) ∂μ ∂μ := by
        refine setIntegral_congr_fun hSm (fun t ht => ?_)
        rw [htr t ht, mul_comm, ← mul_assoc, hne, one_mul]
    _ = ∫ u in S, ∫ t in S, ψ (q u) * ψ (β t u) ∂μ ∂μ := integral_integral_swap hint
    _ = ∫ u in S, ψ (q u) * P.indicator (fun _ => ((μ S).toReal : ℂ)) u ∂μ := by
        congr 1; ext u
        rw [integral_const_mul, horth u]
    _ = ∫ u in S, P.indicator (fun _ => ((μ S).toReal : ℂ)) u ∂μ := by
        refine setIntegral_congr_fun hSm (fun u _ => ?_)
        by_cases hp : u ∈ P
        · simp only [Set.indicator_of_mem hp, hQ' u hp, one_mul]
        · simp only [Set.indicator_of_notMem hp, mul_zero]
    _ = (μ P).toReal * (μ S).toReal := by
        rw [setIntegral_indicator hPm, Set.inter_eq_right.2 hPS', setIntegral_const]
        simp [Measure.real]
    _ = 1 := by
        have h1 : (μ S).toReal * (μ P).toReal = 1 := by
          rw [← ENNReal.toReal_mul, hvol, ENNReal.toReal_one]
        rw [mul_comm]; exact_mod_cast h1
end
end

section

open ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.h2_bounded_twist : Formalism.GaloisCohomology.LocalTateDualityK → ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)},
    FiniteDimensional ℚ_[p] K → ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] {ϖ : O}, Irreducible ϖ → (p : O) ∈ Ideal.span {ϖ} →
    ∀ (ε : Formalism.GaloisCohomology.GK p K →* Oˣ), (∀ (g : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 →
      ∃ a : ℕ, g ζ = ζ ^ a ∧ (((ε) g : Oˣ) : O) - (a : O) ∈ Ideal.span {(p : O) ^ n}) → ∀ (e : ℕ) {M : Type} [AddCommGroup M] [Module O M],
    (M ≃ₗ[O] Formalism.NG.KO O) → ∀ (ρ : Representation O (Formalism.GaloisCohomology.GK p K) M),
    (∀ g m, ρ g m = ((((ε g) ^ e)⁻¹ : Oˣ) : O) • m) → ∀ σ₀ : Formalism.GaloisCohomology.GK p K, ε σ₀ ^ (e + 1) ≠ 1 →
    (∀ (n : ℕ) (h : ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n}),
      letI := GlobalTheory.ShapeNeg.levZ (M := M) p n h
      ReciprocityTheory.Gal.ContAction (GlobalTheory.ShapeNeg.levRepZ p n h ρ)) →
    ∃ C : ℕ, ∀ (n : ℕ), 0 < n → ∀ (h : ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n}),
      letI := GlobalTheory.ShapeNeg.levZ (M := M) p n h
      Nat.card (ReciprocityTheory.Gal.H2 (GlobalTheory.ShapeNeg.levRepZ p n h ρ)) ≤ C := by
  first | exact @GlobalTheory.CyclotomicH2Bound.h2_bounded_cyclotomic | exact GlobalTheory.CyclotomicH2Bound.h2_bounded_cyclotomic | (intros; apply GlobalTheory.CyclotomicH2Bound.h2_bounded_cyclotomic <;> assumption)
end
