module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle315
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle320
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle294
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle322
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle001
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle321
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
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle314
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle228
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsIsoTermComparisonRestrictScalars
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

theorem integralClosure_height_eq_one_of_liesOver : ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (A : Subalgebra k F) [IsFractionRing A F] (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → ∀ (p : Ideal A), p.IsPrime → p.height = 1 → ∀ Q : Ideal B, Q.IsPrime → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → Q.height = 1 := by
  intro k F K _ _ _ _ _ _ _ _ A _ B hB p hp hp1 Q hQ hlo

  have hmem : ∀ a : A, algebraMap F K (a : F) ∈ B := by
    intro a
    rw [hB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
    exact isIntegral_algebraMap (R := A) (A := K) (x := a)
  let f : A →+* B := ((algebraMap F K).comp A.val.toRingHom).codRestrict B hmem
  letI : Algebra A B := f.toAlgebra
  have hf : ∀ a : A, ((algebraMap A B a : B) : K) = algebraMap F K (a : F) := fun _ => rfl

  let φ : B →ₐ[A] K :=
    { toRingHom := B.val.toRingHom
      commutes' := fun a => rfl }
  have hint : Algebra.IsIntegral A B := by
    refine ⟨fun b => ?_⟩
    have key : ∀ x : K, x ∈ B → x ∈ integralClosure A K := by
      intro x hx
      rw [hB, Subalgebra.mem_restrictScalars] at hx
      exact hx
    have hb : (b : K) ∈ integralClosure A K := key b b.2
    rw [← isIntegral_algHom_iff φ Subtype.val_injective]
    exact hb

  have hcomap : Q.comap (algebraMap A B) = p := by
    ext a
    exact hlo a (algebraMap A B a) (hf a)
  haveI := hp
  haveI := hQ
  have hpne : p ≠ ⊥ := Ideal.ne_bot_of_height_eq_one hp1
  apply le_antisymm
  · rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) by rfl, Ideal.height_le_iff]
    intro Q' hQ' hlt
    haveI := hQ'
    by_contra hge
    have hQ'ne : Q' ≠ ⊥ := by
      intro h
      apply hge
      rw [h, Ideal.height_bot]
      norm_num
    have h1 : Q'.comap (algebraMap A B) ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot A hQ'ne
    have h2 : Q'.comap (algebraMap A B) < p := hcomap ▸ Ideal.IsIntegral.comap_lt_comap hlt
    haveI : (Q'.comap (algebraMap A B)).IsPrime := Ideal.comap_isPrime _ _
    have h3 := Ideal.height_add_one_le_of_lt_of_isPrime h2
    have h4 : 1 ≤ (Q'.comap (algebraMap A B)).height := by
      rw [Order.one_le_iff_pos, pos_iff_ne_zero]
      exact fun h => h1 (Ideal.height_eq_zero_iff_eq_bot.mp h)
    rw [hp1] at h3
    have : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add h4 le_rfl).trans h3
    norm_num at this
  · rw [Order.one_le_iff_pos, pos_iff_ne_zero]
    intro h
    rw [Ideal.height_eq_zero_iff_eq_bot] at h
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hpne
    have : algebraMap A B a ∈ Q := by rw [← Ideal.mem_comap, hcomap]; exact ha
    rw [h, Ideal.mem_bot] at this
    apply ha0
    have := congrArg (fun x : B => (x : K)) this
    simp only [hf, ZeroMemClass.coe_zero] at this
    exact Subtype.ext ((algebraMap F K).injective (this.trans (map_zero _).symm))

end GlobalTheory
end

section

open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend

namespace GlobalTheory

theorem exists_mem_closure_sub_mem_maximalIdeal_pow
    (R A : Type) [CommRing R] [IsLocalRing R] [CommRing A] [IsLocalRing A]
    (inc : R →+* A) (ev : A →+* R) (hev : ∀ r, ev (inc r) = r) (n : ℕ) (z : Fin n → A)
    (hm : maximalIdeal A = (maximalIdeal R).map inc ⊔ Ideal.span (Set.range z))
    (k : ℕ) (f : A) :
    ∃ p ∈ Subring.closure (Set.range inc ∪ Set.range z), f - p ∈ maximalIdeal A ^ k := by
  set P := Subring.closure (Set.range inc ∪ Set.range z) with hP
  set m := maximalIdeal A with hmdef
  have incP : ∀ r, inc r ∈ P := fun r => Subring.subset_closure (Or.inl ⟨r, rfl⟩)
  have zP : ∀ i, z i ∈ P := fun i => Subring.subset_closure (Or.inr ⟨i, rfl⟩)
  have hker : ∀ x : A, x - inc (ev x) ∈ m := by
    intro x
    have h1 : x - inc (ev x) ∈ RingHom.ker ev := by
      simp [RingHom.mem_ker, hev]
    exact le_maximalIdeal (RingHom.ker_ne_top ev) h1
  let C : ℕ → Ideal A := fun j =>
    { carrier := {x | ∃ q ∈ P, q ∈ m ^ j ∧ x - q ∈ m ^ (j + 1)}
      add_mem' := by
        rintro a b ⟨q, hq, hqm, hqe⟩ ⟨q', hq', hqm', hqe'⟩
        refine ⟨q + q', P.add_mem hq hq', Ideal.add_mem _ hqm hqm', ?_⟩
        have : a + b - (q + q') = (a - q) + (b - q') := by ring
        rw [this]; exact Ideal.add_mem _ hqe hqe'
      zero_mem' := ⟨0, P.zero_mem, Ideal.zero_mem _, by simp⟩
      smul_mem' := by
        rintro c x ⟨q, hq, hqm, hqe⟩
        refine ⟨inc (ev c) * q, P.mul_mem (incP _) hq, Ideal.mul_mem_left _ _ hqm, ?_⟩
        have hx : x ∈ m ^ j := by
          have : x = q + (x - q) := by ring
          rw [this]; exact Ideal.add_mem _ hqm (Ideal.pow_le_pow_right (Nat.le_succ j) hqe)
        have : c • x - inc (ev c) * q = inc (ev c) * (x - q) + (c - inc (ev c)) * x := by
          simp only [smul_eq_mul]; ring
        rw [this]
        refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hqe) ?_
        rw [pow_succ']
        exact Ideal.mul_mem_mul (hker c) hx }
  have memC : ∀ j x, x ∈ C j ↔ ∃ q ∈ P, q ∈ m ^ j ∧ x - q ∈ m ^ (j + 1) := fun _ _ => Iff.rfl
  have hC1 : m ≤ C 1 := by
    calc m = _ := hm
      _ ≤ C 1 := by
        refine sup_le ?_ ?_
        · rw [Ideal.map_le_iff_le_comap]
          intro r hr
          refine (memC _ _).2 ⟨inc r, incP r, ?_, by simp⟩
          rw [pow_one, hm]; exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hr)
        · rw [Ideal.span_le]
          rintro _ ⟨i, rfl⟩
          refine (memC _ _).2 ⟨z i, zP i, ?_, by simp⟩
          rw [pow_one, hm]; exact Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)
  have hCj : ∀ j, m ^ j ≤ C j := by
    intro j
    induction j with
    | zero =>
      intro x _
      exact (memC _ _).2 ⟨inc (ev x), incP _, by simp, by simpa using hker x⟩
    | succ j ih =>
      rw [pow_succ]
      refine Ideal.mul_le.2 fun y hy w hw => ?_
      obtain ⟨q, hq, hqm, hqe⟩ := (memC _ _).1 (ih hy)
      obtain ⟨q1, hq1, hq1m, hq1e⟩ := (memC _ _).1 (hC1 hw)
      refine (memC _ _).2 ⟨q * q1, P.mul_mem hq hq1, ?_, ?_⟩
      · rw [pow_succ]; exact Ideal.mul_mem_mul hqm (by simpa using hq1m)
      · have : y * w - q * q1 = q * (w - q1) + (y - q) * w := by ring
        rw [this]
        refine Ideal.add_mem _ ?_ ?_
        · have : m ^ (j + 1 + 1) = m ^ j * m ^ (1 + 1) := by rw [← pow_add]
          rw [this]; exact Ideal.mul_mem_mul hqm hq1e
        · rw [pow_succ]; exact Ideal.mul_mem_mul hqe hw
  induction k with
  | zero => exact ⟨0, P.zero_mem, by simp⟩
  | succ k ih =>
    obtain ⟨p, hp, hfp⟩ := ih
    obtain ⟨q, hq, -, hqe⟩ := (memC _ _).1 (hCj k hfp)
    refine ⟨p + q, P.add_mem hp hq, ?_⟩
    rw [show f - (p + q) = f - p - q by ring]
    exact hqe

end GlobalTheory
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

open KaehlerDifferential in
private theorem projective_of_isScalarTower_projective (R A M : Type) [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] [Module.Projective R A]
    [Module.Projective A M] : Module.Projective R M := by
  classical
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective A M)
  have : Module.Projective R (M →₀ A) :=
    Module.Projective.of_equiv (finsuppLequivDFinsupp R : (M →₀ A) ≃ₗ[R] Π₀ _ : M, A).symm
  exact Module.Projective.of_split ((s.restrictScalars R))
    ((Finsupp.linearCombination A id).restrictScalars R)
    (LinearMap.ext fun m => LinearMap.congr_fun hs m)


open KaehlerDifferential in
theorem _root_.GlobalTheory.finite_projective_span_of_integralClosure :
    ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (A : Subalgebra k F) (B : Subalgebra k K), (∀ y : K, y ∈ B ↔ y ∈ integralClosure A K) → Module.Finite A (integralClosure A K) → Module.Projective A (integralClosure A K) → ∀ (W : Type) [AddCommGroup W] [Module K W] [Module F W] [IsScalarTower F K W] (S : Set W), (∀ c ∈ B, ∀ w ∈ S, (c : K) • w ∈ S) → Module.Finite B (Submodule.span B S) → Module.Projective B (Submodule.span B S) → Module.Finite A (Submodule.span A S) ∧ Module.Projective A (Submodule.span A S) := by
  intro k F K _ _ _ _ _ _ _ A B hB hfin hproj W _ _ _ _ S hS hfinB hprojB
  have hAB : ∀ a : A, algebraMap A K a ∈ B := fun a =>
    (hB _).2 ((integralClosure A K).algebraMap_mem a)
  letI : Algebra A B := ((algebraMap A K).codRestrict B hAB).toAlgebra
  have hcoe : ∀ (a : A) (b : B), ((a • b : B) : K) = algebraMap F K (a : F) * (b : K) := by
    intro a b
    rw [Algebra.smul_def]
    rfl
  haveI : IsScalarTower A B W := ⟨fun a b w => by
    rw [Subalgebra.smul_def, hcoe, mul_smul, algebraMap_smul, Subalgebra.smul_def,
      Subalgebra.smul_def]⟩
  let ψ : B ≃ₗ[A] integralClosure A K :=
    { toFun := fun b => ⟨b, (hB b).1 b.2⟩
      invFun := fun c => ⟨c, (hB c).2 c.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun a b => Subtype.ext <| by
        rw [hcoe, RingHom.id_apply, SetLike.val_smul, Algebra.smul_def]
        rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  haveI : Module.Finite A B := Module.Finite.equiv ψ.symm
  haveI : Module.Projective A B := Module.Projective.of_equiv ψ.symm
  haveI : Module.Finite A (Submodule.span B S) := Module.Finite.trans B _
  haveI : Module.Projective A (Submodule.span B S) := projective_of_isScalarTower_projective A B _
  have hclosed : ∀ c : B, ∀ w ∈ Submodule.span A S, c • w ∈ Submodule.span A S := by
    intro c w hw
    induction hw using Submodule.span_induction with
    | mem s hs =>
      rw [Subalgebra.smul_def]
      exact Submodule.subset_span (hS c c.2 s hs)
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add v w _ _ hv hw => rw [smul_add]; exact Submodule.add_mem _ hv hw
    | smul a v _ hv => rw [smul_comm]; exact Submodule.smul_mem _ a hv
  let SB : Submodule B W :=
    { carrier := Submodule.span A S
      add_mem' := Submodule.add_mem _
      zero_mem' := Submodule.zero_mem _
      smul_mem' := fun c w hw => hclosed c w hw }
  have hsets : ∀ w, w ∈ Submodule.span A S ↔ w ∈ Submodule.span B S := by
    intro w
    constructor
    · intro hw
      have hle : Submodule.span A S ≤ (Submodule.span B S).restrictScalars A :=
        Submodule.span_le.mpr fun s hs => Submodule.subset_span hs
      exact hle hw
    · intro hw
      have hle : Submodule.span B S ≤ SB :=
        Submodule.span_le.mpr fun s hs => (Submodule.subset_span hs : s ∈ Submodule.span A S)
      exact hle hw
  let χ : Submodule.span A S ≃ₗ[A] Submodule.span B S :=
    { toFun := fun w => ⟨w, (hsets w).1 w.2⟩
      invFun := fun w => ⟨w, (hsets w).2 w.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact ⟨Module.Finite.equiv χ.symm, Module.Projective.of_equiv χ.symm⟩

end GlobalTheory
end

section

open GlobalTheory GlobalTheory.DI

theorem _root_.GlobalTheory.T.frobeniusDerivation_factors_through_kaehler : ∀ {K : Type} [CommRing K] {M : Type} [AddCommGroup M] [Module K M] (p : ℕ) [Fact p.Prime] [CharP K p] (φ : K →+ M), (∀ a b : K, φ (a * b) = a ^ p • φ b + b ^ p • φ a) → ∃ f : Ω[K⁄ℤ] →+ M, (∀ (c : K) v, f (c • v) = c ^ p • f v) ∧ ∀ a, f (KaehlerDifferential.D ℤ K a) = φ a := by
  first | exact @GlobalTheory.DI.frobDeriv_factors_kaehler | exact GlobalTheory.DI.frobDeriv_factors_kaehler | (intros; apply GlobalTheory.DI.frobDeriv_factors_kaehler <;> assumption)
end

section


theorem _root_.GlobalTheory.T.bertini_general_members_no_derivative_relation : ∀ (k A : Type) [Field k] [CharZero k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A] (n : ℕ) (δ : Fin n → Derivation k A A) (ω : Fin n → KaehlerDifferential k A), (∀ a : A, KaehlerDifferential.D k A a = ∑ l, δ l a • ω l) → ∀ {ι : Type} [Fintype ι] (f : ι → A) (M : ℕ) (J : Finset (Fin M)) (i₀ : Fin M) (p₀ : ι), i₀ ∈ J → ∃ Q : MvPolynomial (Fin M × ι) k, Q ≠ 0 ∧ ∀ u : Fin M × ι → k, MvPolynomial.eval u Q ≠ 0 → ∀ (K : Type) [Field K] [Algebra k K] (φ : A →ₐ[k] K) (c : Fin M → K), φ (f p₀) ≠ 0 → c i₀ = 1 → (∀ i ∈ J, φ (∑ p, u (i, p) • f p) = 0) → ¬ ∀ l, ∑ i ∈ J, c i * φ (δ l (∑ p, u (i, p) • f p)) = 0 := by
  first | exact @GlobalTheory.BertiniC.no_dependence_of_general | exact GlobalTheory.BertiniC.no_dependence_of_general | (intros; apply GlobalTheory.BertiniC.no_dependence_of_general <;> assumption)
end

section

open IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_isUnit_mul_involution_sub_mem_jacobson : ∀ (O : Type) [CommRing O] [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)] (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] (τ : A →+* A), (∀ a, τ (τ a) = a) → ∀ θ : A, IsUnit (θ - τ θ) → ∀ a : A, IsUnit a → τ a = a → ∃ t : A, IsUnit t ∧ t * τ t - a ∈ (⊥ : Ideal A).jacobson := by
  first | (exact @GlobalTheory.exists_isUnit_mul_sub_mem_jacobson_of_finite_residueField) | (exact GlobalTheory.exists_isUnit_mul_sub_mem_jacobson_of_finite_residueField) | (intros; apply GlobalTheory.exists_isUnit_mul_sub_mem_jacobson_of_finite_residueField  <;> assumption)
end

section

open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend

namespace GlobalTheory

open Matrix

theorem powerSeries_matrix_solve : ∀ (n : ℕ) (R : Type) [CommRing R] (J : Fin n → Fin n → MvPowerSeries (Fin n) R), (∀ i j, MvPowerSeries.constantCoeff (J i j) = if i = j then 1 else 0) → ∀ b : Fin n → MvPowerSeries (Fin n) R, ∃ G : Fin n → MvPowerSeries (Fin n) R, ∀ i, ∑ j, G j * J i j = b i := by
  intro n R _ J hJ b
  let M : Matrix (Fin n) (Fin n) (MvPowerSeries (Fin n) R) := Matrix.of J
  have hM : (MvPowerSeries.constantCoeff (σ := Fin n) (R := R)).mapMatrix M = 1 := by
    ext i j
    simp [M, Matrix.one_apply, hJ]
  have hdet : IsUnit M.det := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, RingHom.map_det, hM, Matrix.det_one]
    exact isUnit_one
  refine ⟨M⁻¹ *ᵥ b, fun i => ?_⟩
  have h := congrFun (Matrix.mulVec_mulVec b M M⁻¹) i
  rw [Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec] at h
  rw [← h]
  simp only [Matrix.mulVec, dotProduct, M, Matrix.of_apply]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

end GlobalTheory
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.flat_of_flat_comp_of_map_maximalIdeal_eq : ∀ (O R' E : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R'] [CommRing E] [IsLocalRing E] [IsNoetherianRing E] (φ' : O →+* R') (b : R' →+* E), φ'.Flat → (maximalIdeal O).map φ' = maximalIdeal R' → IsLocalHom b → (b.comp φ').Flat → b.Flat := by
  first | exact @GlobalTheory.ringHom_flat_of_comp_flat_of_map_maximalIdeal | exact GlobalTheory.ringHom_flat_of_comp_flat_of_map_maximalIdeal | (intros; apply GlobalTheory.ringHom_flat_of_comp_flat_of_map_maximalIdeal <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.flat_of_local_retractions_mod_maximalIdeal_pow : ∀ {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B] (φ : A →+* B) [IsLocalHom φ], (∀ n : ℕ, ∃ ψ : B →+* A ⧸ maximalIdeal A ^ (n + 1), ψ.comp φ = Ideal.Quotient.mk _) → (∀ n : ℕ, ∀ g₁ g₂ : B →+* B ⧸ maximalIdeal B ^ (n + 1), IsLocalHom g₁ → IsLocalHom g₂ → g₁.comp φ = g₂.comp φ → g₁ = g₂) → φ.Flat := by
  first | exact @GlobalTheory.flat_of_retractions_mod_pow | exact GlobalTheory.flat_of_retractions_mod_pow | (intros; apply GlobalTheory.flat_of_retractions_mod_pow <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.exists_local_pushout_unramified_charZero : ∀ (A V V' : Type) [CommRing A] [CommRing V] [IsLocalRing V] [CommRing V'] [IsLocalRing V'] (f : A →+* V) (f' : A →+* V'), f'.Flat → (maximalIdeal V).comap f = (maximalIdeal V').comap f' → ((maximalIdeal V).comap f).map f = maximalIdeal V → ((maximalIdeal V').comap f').map f' = maximalIdeal V' → CharZero (ResidueField V) → ∃ (B : Type) (_ : CommRing B) (_ : IsLocalRing B) (g : V →+* B) (g' : V' →+* B), g.comp f = g'.comp f' ∧ g.Flat ∧ (maximalIdeal V).map g = maximalIdeal B ∧ (maximalIdeal V').map g' = maximalIdeal B := by
  first | exact @GlobalTheory.UnramPushout.exists_local_pushout | exact GlobalTheory.UnramPushout.exists_local_pushout | (intros; apply GlobalTheory.UnramPushout.exists_local_pushout <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory

theorem effCartier_comap_of_isIso_restrict : ∀ {Y Y' : Scheme.{0}} (s : Y' ⟶ Y) (I : Y.IdealSheafData) (U : Y.Opens), IsIso (s ∣_ U) → FinalTheorems.EffCartier (I.comap s) → FinalTheorems.EffCartier (I.comap U.ι) := by
  intro Y Y' s I U hiso hE
  have h1 : FinalTheorems.EffCartier ((I.comap s).comap (s ⁻¹ᵁ U).ι) :=
    effCartier_comap_of_isOpenImmersion' _ _ hE
  have h2 := effCartier_comap_of_isOpenImmersion' _ (inv (s ∣_ U)) h1
  have key : inv (s ∣_ U) ≫ (s ⁻¹ᵁ U).ι ≫ s = U.ι := by
    rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, Category.assoc, key] at h2
  exact h2

end GlobalTheory
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.modDepthGE_quotient_span_of_isSMulRegular : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A] [Module.Finite R A] (f : R), f ∈ maximalIdeal R → ∀ [IsLocalRing (R ⧸ Ideal.span {f})], IsSMulRegular A f → ∀ n : ℕ, ReciprocityTheory.CA.ModDepthGE R A (n + 1) → ReciprocityTheory.CA.ModDepthGE (R ⧸ Ideal.span {f}) (A ⧸ (Ideal.span {f}).map (algebraMap R A)) n := by
  first | exact @GlobalTheory.modDepthGE_quotient_map_span_singleton | exact GlobalTheory.modDepthGE_quotient_map_span_singleton | (intros; apply GlobalTheory.modDepthGE_quotient_map_span_singleton <;> assumption)
end
