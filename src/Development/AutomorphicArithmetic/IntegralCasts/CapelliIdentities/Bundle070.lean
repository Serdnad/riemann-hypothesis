module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle021
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle049
public import Mathlib.Topology.Instances.Matrix
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle063
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Formalism.LocalToGlobal.CharacterGerms.GeNatCast
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Formalism.RealPlaceAnalysis.Bundle001
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle022
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle061
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Ideal.BigOperators

@[expose] public section

section

open MvPowerSeries in
private theorem UpperTheory.Reformulated.B.AdicDensityOfPresentationSubalgebra.mem_span_of_coeff {σ O : Type} [CommRing O] (s : Finset σ) :
    ∀ f : MvPowerSeries σ O, (∀ n : σ →₀ ℕ, (∀ i ∈ s, n i = 0) → coeff n f = 0) →
      f ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ O)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro f hf
    have h0 : f = 0 := by
      ext n
      simpa using hf n (by simp)
    simp [h0]
  | insert i s _ ih =>
    intro f hf
    let h : MvPowerSeries σ O := fun n => if n i = 0 then coeff n f else 0
    have hh : ∀ n, coeff n h = if n i = 0 then coeff n f else 0 := fun _ => rfl
    have h1 : h ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ O)) := by
      refine ih h fun n hn => ?_
      rw [hh]
      split_ifs with hi
      · refine hf n fun j hj => ?_
        rcases Finset.mem_insert.1 hj with rfl | hj
        · exact hi
        · exact hn j hj
      · rfl
    have h2 : (X i : MvPowerSeries σ O) ∣ f - h := by
      refine X_dvd_iff.2 fun n hn => ?_
      rw [map_sub, hh, if_pos hn, sub_self]
    have h3 : f - h ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ O)) :=
      Ideal.mem_of_dvd _ h2 (Ideal.subset_span ⟨i, rfl⟩)
    simpa using Ideal.add_mem _ h3 h1

open MvPowerSeries in
private theorem UpperTheory.Reformulated.B.AdicDensityOfPresentationSubalgebra.exists_decomp {σ O : Type} [CommRing O] [Fintype σ]
    (f : MvPowerSeries σ O) :
    ∃ (c : O) (g : σ → MvPowerSeries σ O),
      f = algebraMap O (MvPowerSeries σ O) c + ∑ i, g i * X i := by
  classical
  have h := UpperTheory.Reformulated.B.AdicDensityOfPresentationSubalgebra.mem_span_of_coeff Finset.univ
    (f - algebraMap O (MvPowerSeries σ O) (coeff 0 f)) (by
      intro n hn
      have h0 : n = 0 := by
        ext i
        simpa using hn i (Finset.mem_univ i)
      subst h0
      simp [MvPowerSeries.algebraMap_apply])
  obtain ⟨g, hg⟩ := Ideal.mem_span_range_iff_exists_fun.1 h
  exact ⟨coeff 0 f, g, by rw [hg]; ring⟩

theorem UpperTheory.Reformulated.B.AdicDensityOfPresentationSubalgebra.pi_dense :
    ∀ {O : Type} [inst : CommRing O] [inst_1 : IsLocalRing O] {X : Type} [inst_2 : AddCommGroup X] {R : Type}
      [inst_3 : CommRing R] [inst_4 : Algebra O R] [inst_5 : UpperTheory.V.Alg.IsCO O R] (W : UpperTheory.V.Alg.WPres O X R),
      (∀ (s : W.σ), W.z s ∈ IsLocalRing.maximalIdeal R) →
        ∀ (N : ℕ) (x : R), ∃ a ∈ W.A, x - a ∈ IsLocalRing.maximalIdeal R ^ N := by
  intro O _ _ X _ R _ _ _ W hz N
  induction N with
  | zero => intro x; exact ⟨0, W.A.zero_mem, by simp⟩
  | succ N ih =>
    intro x
    obtain ⟨f, rfl⟩ := W.surj x
    obtain ⟨c, g, rfl⟩ := UpperTheory.Reformulated.B.AdicDensityOfPresentationSubalgebra.exists_decomp f
    choose a ha hm using fun i => ih (W.π (g i))
    refine ⟨algebraMap O R c + ∑ i, a i * W.z i, ?_, ?_⟩
    · exact W.A.add_mem (W.A.algebraMap_mem c)
        (W.A.sum_mem fun i _ => W.A.mul_mem (ha i) (W.part_le_A (W.z_mem i)))
    · have he : W.π (algebraMap O _ c + ∑ i, g i * MvPowerSeries.X i)
          - (algebraMap O R c + ∑ i, a i * W.z i) = ∑ i, (W.π (g i) - a i) * W.z i := by

        rw [map_add (f := _), AlgHom.commutes, map_sum, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, sub_mul]
        rfl
      rw [he, pow_succ]
      exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul (hm i) (hz i)
end

section

theorem UpperTheory.Reformulated.B.IsPFSum.isPF_sum :
    ∀ {A : Type} [inst : Ring A] [inst_1 : Algebra ℂ A] {ι : Type} (s : Finset ι) {f : ι → ℂ → A},
      (∀ i ∈ s, UpperTheory.Reformulated.B.PolynomialFunction₂.IsPF (f i)) → UpperTheory.Reformulated.B.PolynomialFunction₂.IsPF fun (Y : ℂ) ↦ ∑ i ∈ s, f i Y := by
  intro A _ _ ι s f h
  classical
  unfold UpperTheory.Reformulated.B.PolynomialFunction₂.IsPF at h ⊢
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun Y => by simp⟩
  | insert a s ha ih =>
    obtain ⟨p, hp⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨q, hq⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine ⟨p + q, fun Y => ?_⟩
    have h1 : (∑ i ∈ s, f i Y) = Polynomial.eval ((algebraMap ℂ A) Y) q := hq Y
    show (∑ i ∈ insert a s, f i Y) = Polynomial.eval ((algebraMap ℂ A) Y) (p + q)
    rw [Finset.sum_insert ha, hp, h1, Polynomial.eval_add]
end

section

theorem UpperTheory.Reformulated.B.MulLinearAe.mulL_ae.{u_1} :
    ∀ {X : Type u_1} [inst : MeasurableSpace X] {ν : MeasureTheory.Measure X} (c : X → ℝ) (hc : Measurable c)
      (hb : ∀ (x : X), |c x| ≤ (1 : ℝ)) (f : ↥(MeasureTheory.Lp ℂ (2 : ENNReal) ν)),
      (↑(↑((UpperTheory.Reformulated.B.MultiplicationNormBound.mulL c hc hb : ↥(MeasureTheory.Lp ℂ (2 : ENNReal) ν) → ↥(MeasureTheory.Lp ℂ (2 : ENNReal) ν))
                        f) :
              X →ₘ[ν] ℂ) :
          X → ℂ) =ᵐ[ν]
        fun (x : X) ↦ (↑(c x) : ℂ) * (↑(↑f : X →ₘ[ν] ℂ) : X → ℂ) x := by
  intro X _ ν c hc hb f
  have h : MeasureTheory.MemLp (fun x : X => (c x : ℂ) * f x) 2 ν :=
    (MeasureTheory.Lp.memLp f).of_le
      ((Complex.measurable_ofReal.comp hc).aestronglyMeasurable.mul
        (MeasureTheory.Lp.aestronglyMeasurable f))
      (Filter.Eventually.of_forall fun x => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) (hb x))
  exact h.coeFn_toLp
end

section

theorem UpperTheory.Reformulated.B.GLRealOpen.glR_open :
    ∀ {K : Type} [inst : CommRing K] [inst_1 : TopologicalSpace K] [IsTopologicalRing K] (R : Subring K),
      IsOpen (↑R : Set K) → ∀ (n : ℕ), IsOpen (↑(UpperTheory.Reformulated.B.GeneralLinearGroupOverSubring.glR R n) : Set (GL (Fin n) K)) := by
  intro K _ _ _ R hR n
  have hM : IsOpen {M : Matrix (Fin n) (Fin n) K | ∀ i j, M i j ∈ R} := by
    have e : {M : Matrix (Fin n) (Fin n) K | ∀ i j, M i j ∈ R}
        = ⋂ i, ⋂ j, (fun M : Matrix (Fin n) (Fin n) K => M i j) ⁻¹' (R : Set K) := by
      ext M
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    rw [e]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact hR.preimage (continuous_id.matrix_elem i j)
  have h1 : Continuous fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) :=
    Units.continuous_val
  have h2 : Continuous fun g : GL (Fin n) K => ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    Units.continuous_coe_inv
  exact (hM.preimage h1).inter (hM.preimage h2)
end

section

private theorem UpperTheory.Reformulated.B.Gr28.exists_fun
    {G W : Type} [Group G] [AddCommGroup W] [_root_.Module ℂ W]
    (H K : Subgroup G) (σ : Representation ℂ (↥H) W) (w : W)
    (hw : ∀ h : H, (h : G) ∈ K → σ h w = w) :
    ∃ f : G → W, f 1 = w ∧ (∀ (h : H) (g : G), f (h * g) = σ h (f g)) ∧
      ∀ k ∈ K, ∀ g, f (g * k) = f g := by
  classical
  let f : G → W := fun g => if hg : ∃ h : H, (h : G)⁻¹ * g ∈ K then σ hg.choose w else 0
  have pos : ∀ (g : G) (h : H), (h : G)⁻¹ * g ∈ K → f g = σ h w := by
    intro g h hh
    have hg : ∃ h : H, (h : G)⁻¹ * g ∈ K := ⟨h, hh⟩
    have h1 := hg.choose_spec
    have h2 : ((h⁻¹ * hg.choose : H) : G) ∈ K := by
      have := K.mul_mem hh (K.inv_mem h1)
      simpa [mul_assoc] using this
    have h3 := hw _ h2
    have h4 : f g = σ hg.choose w := dif_pos hg
    rw [h4]
    conv_rhs => rw [← h3]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  have neg : ∀ g : G, (¬ ∃ h : H, (h : G)⁻¹ * g ∈ K) → f g = 0 := fun g hg => dif_neg hg
  refine ⟨f, ?_, ?_, ?_⟩
  · rw [pos 1 1 (by simp)]
    simp
  · intro h g
    by_cases hg : ∃ h : H, (h : G)⁻¹ * g ∈ K
    · obtain ⟨a, ha⟩ := hg
      rw [pos g a ha, pos (h * g) (h * a) (by simpa [mul_assoc] using ha), map_mul,
        Module.End.mul_apply]
    · rw [neg g hg, map_zero]
      refine neg _ ?_
      rintro ⟨a, ha⟩
      exact hg ⟨h⁻¹ * a, by simpa [mul_assoc] using ha⟩
  · intro k hk g
    by_cases hg : ∃ h : H, (h : G)⁻¹ * g ∈ K
    · obtain ⟨a, ha⟩ := hg
      rw [pos g a ha, pos (g * k) a (by rw [← mul_assoc]; exact K.mul_mem ha hk)]
    · rw [neg g hg]
      refine neg _ ?_
      rintro ⟨a, ha⟩
      refine hg ⟨a, ?_⟩
      have := K.mul_mem ha (K.inv_mem hk)
      simpa [mul_assoc] using this

theorem UpperTheory.Reformulated.B.Gr28.indVec :
    ∀ {G W : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalGroup G] [inst_3 : AddCommGroup W]
      [inst_4 : _root_.Module ℂ W] (H K : Subgroup G) (σ : Representation ℂ (↥H) W),
      IsOpen (↑K : Set G) →
        ∀ (w : W),
          (∀ (h : ↥H), (↑h : G) ∈ K → ((σ : ↥H → W →ₗ[ℂ] W) h : W → W) w = w) →
            ∃ (f : ↥(GlobalTheory.PRep.smoothPart (GlobalTheory.PRep.ind H σ))),
              (↑(↑f : ↥(GlobalTheory.PRep.indSpace H σ)) : G → W) (1 : G) = w ∧ f ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd (GlobalTheory.PRep.smInd H σ) K := by
  intro G W _ _ _ _ _ H K σ hK w hw
  obtain ⟨f, h1, h2, h3⟩ := UpperTheory.Reformulated.B.Gr28.exists_fun H K σ w hw
  let F : GlobalTheory.PRep.indSpace H σ := ⟨f, h2⟩
  have hF : ∀ k ∈ K, GlobalTheory.PRep.ind H σ k F = F := by
    intro k hk
    apply Subtype.ext
    funext g
    exact h3 k hk g
  have hs : F ∈ GlobalTheory.PRep.smoothPart (GlobalTheory.PRep.ind H σ) := by
    let T : Subgroup G :=
      { carrier := {g | GlobalTheory.PRep.ind H σ g F = F}
        mul_mem' := by
          intro x y hx hy
          simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
          rw [hy, hx]
        one_mem' := by simp
        inv_mem' := by
          intro x hx
          simp only [Set.mem_setOf_eq] at *
          conv_lhs => rw [← hx]
          rw [← Module.End.mul_apply, ← map_mul]
          simp }
    exact Subgroup.isOpen_mono (H₁ := K) (H₂ := T) hF hK
  refine ⟨⟨F, hs⟩, h1, ?_⟩
  intro k hk
  exact Subtype.ext (hF k hk)
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.Gr29.Plc :
    (F : Type) → [Field F] → Type :=
    fun (F : Type) [Field F] ↦ IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.Gr29.GLw :
    {L : Type} → [inst : Field L] → [NumberField L] → ℕ → UpperTheory.Reformulated.B.Gr29.Plc L → Type :=
    fun {L : Type} [Field L] [NumberField L] (n : ℕ) (w : UpperTheory.Reformulated.B.Gr29.Plc L) ↦
      GL (Fin n) (IsDedekindDomain.HeightOneSpectrum.adicCompletion L w)

@[reducible] noncomputable def UpperTheory.Reformulated.B.Gr29.GV :
    {L : Type} → [inst : Field L] → [NumberField L] → ℕ → {V : Type} → (V → UpperTheory.Reformulated.B.Gr29.Plc L) → Type :=
    fun {L : Type} [Field L] [NumberField L] (n : ℕ) {V : Type} (S : V → UpperTheory.Reformulated.B.Gr29.Plc L) ↦
      (v : V) → UpperTheory.Reformulated.B.Gr29.GLw n (S v)

noncomputable def UpperTheory.Reformulated.B.Gr29.atJ :
    {L : Type} →
      [inst : Field L] →
        [inst_1 : NumberField L] →
          (n : ℕ) →
            {q : ℕ} →
              (w : Fin q → UpperTheory.Reformulated.B.Gr29.Plc L) → (j : Fin q) → UpperTheory.Reformulated.B.Gr29.GLw n (w j) →* UpperTheory.Reformulated.B.Gr29.GV n w :=
    fun {L : Type} [Field L] [NumberField L] (n : ℕ) {q : ℕ} (w : Fin q → UpperTheory.Reformulated.B.Gr29.Plc L) (j : Fin q) ↦
      MonoidHom.mulSingle (fun (j : Fin q) ↦ UpperTheory.Reformulated.B.Gr29.GLw n (w j)) j

private def UpperTheory.Reformulated.B.Gr29.stab {A P M : Type} [CommRing A] [Group P] [AddCommGroup M]
    [_root_.Module A M] (ρ : Representation A P M) (m : M) : Subgroup P where
  carrier := {g | ρ g m = m}
  mul_mem' := by
    intro a b ha hb
    have ha' : ρ a m = m := ha
    have hb' : ρ b m = m := hb
    change ρ (a * b) m = m
    rw [map_mul, Module.End.mul_apply, hb', ha']
  one_mem' := by
    change ρ 1 m = m
    rw [map_one, Module.End.one_apply]
  inv_mem' := by
    intro a ha
    have ha' : ρ a m = m := ha
    change ρ a⁻¹ m = m
    have h : ρ a⁻¹ (ρ a m) = m := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rwa [ha'] at h

private theorem UpperTheory.Reformulated.B.Gr29.mem_fixed_pi_iff {q : ℕ} {G : Fin q → Type} [∀ j, Group (G j)]
    {A M : Type} [CommRing A] [AddCommGroup M] [_root_.Module A M]
    (ρ : Representation A ((j : Fin q) → G j) M) (H : (j : Fin q) → Subgroup (G j)) (m : M) :
    m ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd ρ (Subgroup.pi Set.univ H) ↔
      ∀ j : Fin q, m ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd (MonoidHom.comp ρ (MonoidHom.mulSingle G j)) (H j) := by
  have key : m ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd ρ (Subgroup.pi Set.univ H) ↔
      Subgroup.pi Set.univ H ≤ UpperTheory.Reformulated.B.Gr29.stab ρ m := Iff.rfl
  rw [key, Subgroup.pi_le_iff]
  refine forall_congr' fun j => ?_
  constructor
  · intro h k hk
    exact h (Subgroup.mem_map_of_mem _ hk)
  · rintro h _ ⟨k, hk, rfl⟩
    exact h k hk

theorem UpperTheory.Reformulated.B.Gr29.mem_pi :
    ∀ {L : Type} [inst : Field L] [inst_1 : NumberField L] {n q : ℕ} {w : Fin q → UpperTheory.Reformulated.B.Gr29.Plc L} {A M : Type}
      [inst_2 : CommRing A] [inst_3 : AddCommGroup M] [inst_4 : _root_.Module A M]
      (ρ : Representation A (UpperTheory.Reformulated.B.Gr29.GV n w) M) (H : (j : Fin q) → Subgroup (UpperTheory.Reformulated.B.Gr29.GLw n (w j)))
      (m : M),
      m ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd ρ (Subgroup.pi Set.univ H) ↔
        ∀ (j : Fin q), m ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd (MonoidHom.comp ρ (UpperTheory.Reformulated.B.Gr29.atJ n w j)) (H j) := by
  intro L _ _ n q w A M _ _ _ ρ H m
  exact UpperTheory.Reformulated.B.Gr29.mem_fixed_pi_iff (G := fun j : Fin q => UpperTheory.Reformulated.B.Gr29.GLw n (w j)) ρ H m
end

section

noncomputable def UpperTheory.Reformulated.B.BoundedSums.Bdd :
    {C : Type} → [inst : Field C] → Formalism.L2.FormalSeriesBounds.VF C → (ℕ → C) → Prop :=
    fun {C : Type} [Field C] (V : Formalism.L2.FormalSeriesBounds.VF C) (s : ℕ → C) ↦ ∃ (K : ℝ), ∀ (n : ℕ), V.Ge K (s n)

noncomputable def UpperTheory.Reformulated.B.BoundedSums.BddS :
    {C : Type} → [inst : Field C] → {σ : Type} → Formalism.L2.FormalSeriesBounds.VF C → (ℕ → MvPowerSeries σ C) → Prop :=
    fun {C : Type} [Field C] {σ : Type} (V : Formalism.L2.FormalSeriesBounds.VF C) (f : ℕ → MvPowerSeries σ C) ↦
      ∀ (μ : σ →₀ ℕ), UpperTheory.Reformulated.B.BoundedSums.Bdd V fun (n : ℕ) ↦ (MvPowerSeries.coeff μ : MvPowerSeries σ C → C) (f n)

private theorem UpperTheory.Reformulated.B.BoundedSums.bdd_sum {C : Type} [Field C] {V : Formalism.L2.FormalSeriesBounds.VF C} {α : Type}
    (T : Finset α) (s : α → ℕ → C) (h : ∀ a ∈ T, UpperTheory.Reformulated.B.BoundedSums.Bdd V (s a)) :
    UpperTheory.Reformulated.B.BoundedSums.Bdd V fun n ↦ ∑ a ∈ T, s a n := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨0, fun n => by simpa using Formalism.L2.FormalSeriesBounds.VF.Ge.zero (V := V) 0⟩
  | insert a T ha ih =>
    obtain ⟨K, hK⟩ := h a (Finset.mem_insert_self a T)
    obtain ⟨L, hL⟩ := ih fun b hb => h b (Finset.mem_insert_of_mem hb)
    refine ⟨min K L, fun n => ?_⟩
    show V.Ge (min K L) (∑ b ∈ insert a T, s b n)
    rw [Finset.sum_insert ha]
    exact ((hK n).mono (min_le_left _ _)).add ((hL n).mono (min_le_right _ _))

private theorem UpperTheory.Reformulated.B.BoundedSums.bddS_mul {C : Type} [Field C] {V : Formalism.L2.FormalSeriesBounds.VF C} {σ : Type}
    {f g : ℕ → MvPowerSeries σ C} (hf : UpperTheory.Reformulated.B.BoundedSums.BddS V f)
    (hg : UpperTheory.Reformulated.B.BoundedSums.BddS V g) : UpperTheory.Reformulated.B.BoundedSums.BddS V fun n ↦ f n * g n := by
  classical
  intro μ
  have h := UpperTheory.Reformulated.B.BoundedSums.bdd_sum (V := V) (Finset.HasAntidiagonal.antidiagonal μ)
    (fun p n => MvPowerSeries.coeff p.1 (f n) * MvPowerSeries.coeff p.2 (g n)) (fun p _ => by
      obtain ⟨K, hK⟩ := hf p.1
      obtain ⟨L, hL⟩ := hg p.2
      exact ⟨K + L, fun n => (hK n).mul (hL n)⟩)
  obtain ⟨K, hK⟩ := h
  refine ⟨K, fun n => ?_⟩
  show V.Ge K (MvPowerSeries.coeff μ (f n * g n))
  rw [MvPowerSeries.coeff_mul]
  exact hK n

theorem UpperTheory.Reformulated.B.BoundedSums.prod :
    ∀ {C : Type} [inst : Field C] {V : Formalism.L2.FormalSeriesBounds.VF C} {σ ι : Type} (S : Finset ι) {f : ι → ℕ → MvPowerSeries σ C},
      (∀ i ∈ S, UpperTheory.Reformulated.B.BoundedSums.BddS V (f i)) → UpperTheory.Reformulated.B.BoundedSums.BddS V fun (n : ℕ) ↦ ∏ i ∈ S, f i n := by
  intro C _ V σ ι S f h
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro μ
    refine ⟨0, fun n => ?_⟩
    show V.Ge 0 (MvPowerSeries.coeff μ (∏ i ∈ (∅ : Finset ι), f i n))
    rw [Finset.prod_empty, MvPowerSeries.coeff_one]
    split_ifs
    · exact Formalism.L2.FormalSeriesBounds.VF.Ge.one
    · exact Formalism.L2.FormalSeriesBounds.VF.Ge.zero 0
  | insert a S ha ih =>
    have h2 := UpperTheory.Reformulated.B.BoundedSums.bddS_mul (h a (Finset.mem_insert_self a S))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))
    simpa only [Finset.prod_insert ha] using h2
end

section

theorem UpperTheory.Reformulated.B.CasimirCommutation.casComm_casK_comm :
    ∀ {A : Type} [inst : Ring A] {n : ℕ} (ε : Fin n → Bool) (E : Fin n → Fin n → A),
      Formalism.REAL.GlRel E → ∀ (c d : Fin n), ε c = ε d → Formalism.REAL.CasK ε E * E c d = E c d * Formalism.REAL.CasK ε E := by
  intro A _ n ε E h c d hcd
  have key : ∀ a b, E a b * E b a * E c d - E c d * (E a b * E b a) =
      E a b * (if a = c then E b d else 0) - E a b * (if d = b then E c a else 0)
        + (if b = c then E a d else 0) * E b a - (if d = a then E c b else 0) * E b a := by
    intro a b
    have h1 := h b a c d
    have h2 := h a b c d
    have : E a b * (if a = c then E b d else 0) - E a b * (if d = b then E c a else 0)
        + (if b = c then E a d else 0) * E b a - (if d = a then E c b else 0) * E b a
        = E a b * ((if a = c then E b d else 0) - (if d = b then E c a else 0))
          + ((if b = c then E a d else 0) - (if d = a then E c b else 0)) * E b a := by
      noncomm_ring
    rw [this, ← h1, ← h2]
    noncomm_ring
  have S1 : ∑ a, ∑ b, (if ε a = ε b then E a b * (if a = c then E b d else 0) else 0)
      = ∑ b, if ε c = ε b then E c b * E b d else 0 := by
    rw [Finset.sum_eq_single c (fun a _ ha => by simp [ha]) (by simp)]
    simp
  have S4 : ∑ a, ∑ b, (if ε a = ε b then (if d = a then E c b else 0) * E b a else 0)
      = ∑ b, if ε d = ε b then E c b * E b d else 0 := by
    rw [Finset.sum_eq_single d (fun a _ ha => by simp [Ne.symm ha]) (by simp)]
    simp
  have S2 : ∑ a, ∑ b, (if ε a = ε b then E a b * (if d = b then E c a else 0) else 0)
      = ∑ a, if ε a = ε d then E a d * E c a else 0 := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single d (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp
  have S3 : ∑ a, ∑ b, (if ε a = ε b then (if b = c then E a d else 0) * E b a else 0)
      = ∑ a, if ε a = ε c then E a d * E c a else 0 := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single c (fun b _ hb => by simp [hb]) (by simp)]
    simp
  have e : Formalism.REAL.CasK ε E * E c d - E c d * Formalism.REAL.CasK ε E =
      ∑ a, ∑ b, (if ε a = ε b then E a b * E b a * E c d - E c d * (E a b * E b a) else 0) := by
    simp only [Formalism.REAL.CasK, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp
  have e2 : ∑ a, ∑ b, (if ε a = ε b then E a b * E b a * E c d - E c d * (E a b * E b a) else 0)
      = ∑ a, ∑ b, (if ε a = ε b then E a b * (if a = c then E b d else 0) else 0)
        - ∑ a, ∑ b, (if ε a = ε b then E a b * (if d = b then E c a else 0) else 0)
        + ∑ a, ∑ b, (if ε a = ε b then (if b = c then E a d else 0) * E b a else 0)
        - ∑ a, ∑ b, (if ε a = ε b then (if d = a then E c b else 0) * E b a else 0) := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [key]
    split_ifs <;> simp
  rw [← sub_eq_zero, e, e2, S1, S2, S3, S4, hcd]
  abel
end

section

theorem UpperTheory.Reformulated.B.ContDiffOnLocalExtension.abs : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {m : ℕ∞} {U : Set E},
  IsOpen U → ∀ {F : E → V}, ContDiffOn ℝ (m : WithTop ℕ∞) F U → ∀ {x : E}, x ∈ U →
    ∃ G : E → V, ContDiff ℝ (m : WithTop ℕ∞) G ∧ G =ᶠ[nhds x] F :=
  @UpperTheory.exists_smooth_extension_near
end

section

theorem UpperTheory.Reformulated.B.CapelliAbsoluteValue.abs : ∀ {F E : Type} [CommSemiring F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  NumberField.IsTotallyComplex E → (∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) →
    {t : E | t * σ t = 1}.Infinite :=
  UpperTheory.infinite_norm_one_elements
end
